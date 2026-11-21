/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Universality.RecursionFree.DecompositionTools

/-!
# One side of the decomposition of a rule (page 85)

Lafont 1997, page 85: the right member of a rule for `α_i`, `α_j` is decomposed into a reduced net
`φ_{i,j}` on the auxiliary ports of `α_i`, a reduced net `ψ_{i,j}` on those of `α_j`, and a
permutation `σ_{i,j}` of the `k` wires between them. This file builds one side, `half X Y k mid`,
from a split of the right member into two nets `X` (the side being built) and `Y` (the other
side), both over the names `Fin a ⊕ Fin b ⊕ Fin n` of a rule. `RecursionFree/Decomposition.lean`
uses it twice: for `φ` with `X` the trees rooted at the ports of the first cell, and for `ψ` with
the names exchanged.

* `IsMiddle X Y`, `middle X Y` — the names that join the two sides: a port of the first cell
  (`.inl i`) that occurs in `Y`, a port of the second cell (`.inr (.inl j)`) that occurs in `X`,
  an internal wire that occurs in both.
* `inner X Y` — the internal wires with both ends in `X`.
* `half X Y k mid : Rule S a k` — the side `X` as a net whose ports are the `a` ports of the first
  cell and the `k` middle wires, numbered by `mid`; its internal wires are `inner X Y`, numbered
  in increasing order. A port `.inl i` that occurs in `Y` becomes an equation `i = mid(.inl i)`.
* `half_linear`, `half_reduced`, `half_cells`, `half_bind` — its properties.

Contents, in the order of the file:

1. Auxiliary lemma: `renameOptEq_mk`, an equation renamed by a partial function.
2. Definitions: equations rooted at a port of the first cell, `leftIdx`, `leftRoot`,
   `isLeftVar`, `LeftRooted`, `leftRootedB`, with `isLeftVar_iff`, `leftRootedB_iff` and the
   decidability of `LeftRooted`.
3. Definitions: an order on the names, `code`, `root`, `key`, with `code_lt`, `code_injective`,
   `key_injective`.
4. Definitions: the middle wires and the inner wires, `IsMiddle`, `middle`, `inner`, `innerIdx`,
   with `mem_middle_inl`, `mem_middle_inr_inl`, `mem_middle_inr_inr`, `mem_inner`.
5. Definitions: the side, `ren`, `leftMid`, `leftsOut`, `extras`, `halfNet`, `half`.
6. Auxiliary lemmas: the renaming, `ren_isSome`, `ren_of_mem`, `ren_eq_mid`, `ren_eq_left`,
   `ren_eq_inner`, `mem_leftsOut`.
7. Auxiliary lemmas: the names of a side, `half_net`, `extras_cells`, `extras_vars`,
   `count_filterMap_of_iff`, `count_filterMap_of_none`, `leftMid_injective`.
8. Main results: the properties of a side, `half_cells`, `half_bind`, `half_linear`,
   `half_reduced`.
-/

@[expose] public section

namespace INet

variable {S : Signature}

open Term

-- ============================================================================================
-- 1. Auxiliary lemma: an equation renamed by a partial function
-- ============================================================================================

/-- An equation `s(u, v)` renamed by a partial function `g` is the equation of the renamed sides,
both of which exist. -/
theorem renameOptEq_mk
    -- the names before and after the renaming, and the partial renaming
    {ν μ : Type}
    {g : ν → Option μ}
    -- the equation, and its renaming `e'`
    {u v : Term S ν}
    {e' : Sym2 (Term S μ)}
    (h : renameOptEq g s(u, v) = some e') :
    -- both sides are renamed, and `e'` is the equation between the renamed sides
    ∃ u' v',
      u.renameOpt g = some u' ∧
      v.renameOpt g = some v' ∧
      e' = s(u', v') := by
  simp only [renameOptEq, Sym2.lift_mk] at h
  cases hu : u.renameOpt g <;> cases hv : v.renameOpt g <;> simp_all

namespace Half

-- the number of ports of the first cell, of the second cell, and of internal wires of the rule
variable {a b n : ℕ}

-- ============================================================================================
-- 2. Definitions: equations rooted at a port of the first cell
-- ============================================================================================

/-- The index `i` of a leaf `.inl i`, and `0` for any other tree. -/
def leftIdx :
    Term S (Fin a ⊕ Fin b ⊕ Fin n) → ℕ
  | var (.inl i) => i
  | _ => 0

/-- The largest index of a port `.inl i` on a side of the equation (`0` if there is none): the
root of a tree rooted at a port of the first cell. -/
def leftRoot :
    Sym2 (Term S (Fin a ⊕ Fin b ⊕ Fin n)) → ℕ :=
  Sym2.lift ⟨fun u v => max (leftIdx u) (leftIdx v), fun _ _ => max_comm _ _⟩

/-- Whether a tree is a leaf `.inl i`. -/
def isLeftVar :
    Term S (Fin a ⊕ Fin b ⊕ Fin n) → Bool
  | var (.inl _) => true
  | _ => false

/-- `isLeftVar t` holds exactly when `t` is a leaf `.inl i`. -/
theorem isLeftVar_iff
    (t : Term S (Fin a ⊕ Fin b ⊕ Fin n)) :
    isLeftVar t = true ↔ ∃ i, t = var (.inl i) := by
  rcases t with (i | j | w) | ⟨α, ts⟩ <;> simp [isLeftVar]

/-- An equation rooted at a port of the first cell: one of its sides is a leaf `.inl i`. -/
def LeftRooted
    -- the equation
    (e : Sym2 (Term S (Fin a ⊕ Fin b ⊕ Fin n))) :
    Prop :=
  ∃ i, (var (.inl i) : Term S _) ∈ e

/-- Whether an equation has a side that is a leaf `.inl i`. -/
def leftRootedB :
    Sym2 (Term S (Fin a ⊕ Fin b ⊕ Fin n)) → Bool :=
  Sym2.lift ⟨fun u v => isLeftVar u || isLeftVar v, fun _ _ => Bool.or_comm _ _⟩

/-- `leftRootedB` decides `LeftRooted`. -/
theorem leftRootedB_iff
    (e : Sym2 (Term S (Fin a ⊕ Fin b ⊕ Fin n))) :
    leftRootedB e = true ↔ LeftRooted e := by
  induction e using Sym2.ind with
  | _ u v =>
    simp only [leftRootedB, Sym2.lift_mk, Bool.or_eq_true, isLeftVar_iff, LeftRooted,
      Sym2.mem_iff]
    constructor
    · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact ⟨i, Or.inl rfl⟩
      · exact ⟨i, Or.inr rfl⟩
    · rintro ⟨i, h | h⟩
      · exact Or.inl ⟨i, h.symm⟩
      · exact Or.inr ⟨i, h.symm⟩

instance : DecidablePred (LeftRooted (S := S) (a := a) (b := b) (n := n)) :=
  fun e => decidable_of_iff _ (leftRootedB_iff e)

-- ============================================================================================
-- 3. Definitions: an order on the names
-- ============================================================================================

/-- A number for each name: the ports of the first cell, then those of the second, then the
internal wires. -/
def code :
    Fin a ⊕ Fin b ⊕ Fin n → ℕ :=
  Sum.elim (fun i => i.val) (Sum.elim (fun j => a + j.val) fun w => a + b + w.val)

/-- The number of a name is below the number of names. -/
theorem code_lt
    (x : Fin a ⊕ Fin b ⊕ Fin n) :
    code x < a + b + n := by
  rcases x with i | j | w <;> simp [code] <;> omega

/-- Distinct names have distinct numbers. -/
theorem code_injective :
    Function.Injective (code : Fin a ⊕ Fin b ⊕ Fin n → ℕ) := by
  intro x y h
  rcases x with i | j | w <;> rcases y with i' | j' | w' <;>
    simp [code, Fin.ext_iff] at h ⊢ <;> omega

-- the split of the right member of the rule: `X` the side being built, `Y` the other side
variable (X Y : Net S (Fin a ⊕ Fin b ⊕ Fin n))

/-- The root of a name in the side `X`: `i` for the port `.inl i`, and for another name the root
of the tree of `X` where it occurs. -/
def root :
    Fin a ⊕ Fin b ⊕ Fin n → ℕ
  | .inl i => i
  | x => ((X.filter fun e => x ∈ eqVars e).map leftRoot).sup

/-- The key that orders the middle wires of the side `X`: first by the port of the first cell at
the root of their tree, then by `code`. -/
def key
    -- the name
    (x : Fin a ⊕ Fin b ⊕ Fin n) :
    ℕ :=
  code x + root X x * (a + b + n)

/-- Distinct names have distinct keys. -/
theorem key_injective :
    Function.Injective (key X) := by
  intro x y h
  have hx := congrArg (· % (a + b + n)) h
  simp only [key, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (code_lt _)] at hx
  exact code_injective hx

-- ============================================================================================
-- 4. Definitions: the middle wires and the inner wires
-- ============================================================================================

/-- The names that join the side `X` to the side `Y`. -/
def IsMiddle :
    Fin a ⊕ Fin b ⊕ Fin n → Prop
  | .inl i => .inl i ∈ Y.vars
  | .inr (.inl j) => .inr (.inl j) ∈ X.vars
  | .inr (.inr w) => .inr (.inr w) ∈ X.vars ∧ .inr (.inr w) ∈ Y.vars

instance : DecidablePred (IsMiddle X Y)
  | .inl i => inferInstanceAs (Decidable ((Sum.inl i : Fin a ⊕ Fin b ⊕ Fin n) ∈ Y.vars))
  | .inr (.inl j) =>
    inferInstanceAs (Decidable ((Sum.inr (.inl j) : Fin a ⊕ Fin b ⊕ Fin n) ∈ X.vars))
  | .inr (.inr w) =>
    inferInstanceAs (Decidable ((Sum.inr (.inr w) : Fin a ⊕ Fin b ⊕ Fin n) ∈ X.vars ∧
      (Sum.inr (.inr w) : Fin a ⊕ Fin b ⊕ Fin n) ∈ Y.vars))

/-- The middle wires: the names that join the two sides. -/
def middle :
    Finset (Fin a ⊕ Fin b ⊕ Fin n) :=
  Finset.univ.filter (IsMiddle X Y)

/-- The internal wires with both ends in `X`. -/
def inner :
    Finset (Fin n) :=
  Finset.univ.filter fun w => (.inr (.inr w) : Fin a ⊕ Fin b ⊕ Fin n) ∈ X.vars ∧
    (.inr (.inr w) : Fin a ⊕ Fin b ⊕ Fin n) ∉ Y.vars

/-- A port of the first cell is a middle wire when it occurs in `Y`. -/
@[simp] theorem mem_middle_inl
    (i : Fin a) :
    .inl i ∈ middle X Y ↔ .inl i ∈ Y.vars := by
  simp [middle, IsMiddle]

/-- A port of the second cell is a middle wire when it occurs in `X`. -/
@[simp] theorem mem_middle_inr_inl
    (j : Fin b) :
    .inr (.inl j) ∈ middle X Y ↔ .inr (.inl j) ∈ X.vars := by
  simp [middle, IsMiddle]

/-- An internal wire is a middle wire when it occurs in both sides. -/
@[simp] theorem mem_middle_inr_inr
    (w : Fin n) :
    .inr (.inr w) ∈ middle X Y ↔ .inr (.inr w) ∈ X.vars ∧ .inr (.inr w) ∈ Y.vars := by
  simp [middle, IsMiddle]

/-- An internal wire is an inner wire of `X` when it occurs in `X` and not in `Y`. -/
@[simp] theorem mem_inner
    (w : Fin n) :
    w ∈ inner X Y ↔ .inr (.inr w) ∈ X.vars ∧ .inr (.inr w) ∉ Y.vars := by
  simp [inner]

/-- The number of an internal wire of `X`. -/
def innerIdx
    -- the inner wire
    {w : Fin n}
    (h : w ∈ inner X Y) :
    Fin (inner X Y).card :=
  ⟨rankIn (inner X Y) Fin.val w, rankIn_lt h⟩

-- ============================================================================================
-- 5. Definitions: the side
-- ============================================================================================

-- the number `k` of middle wires, and their numbering `mid`
variable (k : ℕ)
  (mid : (x : Fin a ⊕ Fin b ⊕ Fin n) → x ∈ middle X Y → Fin k)

/-- The renaming of the names of `X` into those of the side: a middle wire becomes the port
`mid x`, a port of the first cell stays a port, an internal wire of `X` gets its number. -/
def ren :
    Fin a ⊕ Fin b ⊕ Fin n → Option (Fin a ⊕ Fin k ⊕ Fin (inner X Y).card)
  | .inl i => if h : .inl i ∈ middle X Y then some (.inr (.inl (mid _ h))) else some (.inl i)
  | .inr (.inl j) =>
    if h : .inr (.inl j) ∈ middle X Y then some (.inr (.inl (mid _ h))) else none
  | .inr (.inr w) =>
    if h : .inr (.inr w) ∈ middle X Y then some (.inr (.inl (mid _ h)))
    else if h' : w ∈ inner X Y then some (.inr (.inr (innerIdx X Y h'))) else none

/-- The middle port of a port `.inl i` that occurs in `Y`. -/
def leftMid
    -- the port of the first cell
    (i : Fin a) :
    Fin a ⊕ Fin k ⊕ Fin (inner X Y).card :=
  if h : .inl i ∈ middle X Y then .inr (.inl (mid _ h)) else .inl i

/-- The ports `.inl i` that occur in `Y`. -/
def leftsOut :
    Finset (Fin a) :=
  Finset.univ.filter fun i => .inl i ∈ middle X Y

/-- The equations `i = mid(.inl i)` for the ports `.inl i` that occur in `Y`. -/
def extras :
    Net S (Fin a ⊕ Fin k ⊕ Fin (inner X Y).card) :=
  (leftsOut X Y).val.map fun i => s(var (.inl i), var (leftMid X Y k mid i))

/-- The side `X` of the decomposition, as a net on the `a` ports of the first cell and `k` middle
wires. -/
def halfNet :
    Net S (Fin a ⊕ Fin k ⊕ Fin (inner X Y).card) :=
  Net.renameOpt (ren X Y k mid) X + extras X Y k mid

/-- The side `X` of the decomposition, as a rule-shaped net: its ports are the `a` ports of the
first cell and the `k` middle wires. -/
def half :
    Rule S a k where
  internal := (inner X Y).card
  net := halfNet X Y k mid

-- ============================================================================================
-- 6. Auxiliary lemmas: the renaming
-- ============================================================================================

/-- Every name of `X` is renamed. -/
theorem ren_isSome :
    ∀ x ∈ X.vars, (ren X Y k mid x).isSome := by
  intro x hx
  rcases x with i | j | w
  · simp only [ren]; split_ifs <;> rfl
  · have : .inr (.inl j) ∈ middle X Y := (mem_middle_inr_inl X Y j).2 hx
    simp [ren, this]
  · simp only [ren]
    split_ifs with h h'
    · rfl
    · rfl
    · exact absurd ((mem_inner X Y w).2 ⟨hx, fun hy =>
        h ((mem_middle_inr_inr X Y w).2 ⟨hx, hy⟩)⟩) h'

/-- A middle wire `x` is renamed to the middle port `mid x`. -/
theorem ren_of_mem
    -- the middle wire
    {x : Fin a ⊕ Fin b ⊕ Fin n}
    (h : x ∈ middle X Y) :
    ren X Y k mid x = some (.inr (.inl (mid x h))) := by
  rcases x with i | j | w <;> simp [ren, h]

/-- The names renamed to the middle port `l` are the middle wires numbered `l`. -/
theorem ren_eq_mid
    -- the name, and the middle port
    (x : Fin a ⊕ Fin b ⊕ Fin n)
    (l : Fin k) :
    ren X Y k mid x = some (.inr (.inl l)) ↔ ∃ h : x ∈ middle X Y, mid x h = l := by
  by_cases h : x ∈ middle X Y
  · rw [ren_of_mem X Y k mid h]
    constructor
    · intro he
      exact ⟨h, by simpa using he⟩
    · rintro ⟨_, rfl⟩
      rfl
  · refine ⟨fun he => ?_, fun ⟨h', _⟩ => absurd h' h⟩
    exfalso
    rcases x with i | j | w <;> simp [ren, h] at he

/-- The only name renamed to the port `.inl i` is `.inl i` itself, when it is not a middle
wire. -/
theorem ren_eq_left
    -- the name, and the port of the first cell
    (x : Fin a ⊕ Fin b ⊕ Fin n)
    (i : Fin a) :
    ren X Y k mid x = some (.inl i) ↔ x = .inl i ∧ .inl i ∉ middle X Y := by
  by_cases h : x ∈ middle X Y
  · rw [ren_of_mem X Y k mid h]
    exact ⟨fun he => (by cases he), fun ⟨hx, hi⟩ => absurd (hx ▸ h) hi⟩
  · rcases x with i' | j | w
    · simp only [ren, h, dite_false, Option.some.injEq, Sum.inl.injEq]
      exact ⟨fun he => ⟨he, he ▸ h⟩, fun ⟨he, _⟩ => he⟩
    · simp [ren, h]
    · simp only [ren, h, dite_false]
      split_ifs <;> simp

/-- The names renamed to the internal wire `m` of the side are the inner wires numbered `m`. -/
theorem ren_eq_inner
    -- the name, and the internal wire of the side
    (x : Fin a ⊕ Fin b ⊕ Fin n)
    (m : Fin (inner X Y).card) :
    -- `x` is renamed to `m` exactly when
    ren X Y k mid x = some (.inr (.inr m)) ↔
      -- `x` is an inner wire `w` of `X`,
      ∃ w, ∃ h : w ∈ inner X Y,
        x = .inr (.inr w) ∧
        -- not a middle wire,
        x ∉ middle X Y ∧
        -- and numbered `m`
        innerIdx X Y h = m := by
  by_cases h : x ∈ middle X Y
  · rw [ren_of_mem X Y k mid h]
    exact ⟨fun he => (by cases he), fun ⟨_, _, _, hx, _⟩ => absurd h hx⟩
  · rcases x with i | j | w
    · simp only [ren, h, dite_false]
      exact ⟨fun he => (by cases he), fun ⟨_, _, he, _⟩ => (by cases he)⟩
    · simp only [ren, h, dite_false]
      exact ⟨fun he => (by cases he), fun ⟨_, _, he, _⟩ => (by cases he)⟩
    · simp only [ren, h, dite_false]
      by_cases h' : w ∈ inner X Y
      · simp only [h', dite_true]
        constructor
        · intro he
          exact ⟨w, h', rfl, by simp, by cases he; rfl⟩
        · rintro ⟨w', h'', he, -, rfl⟩
          cases he
          rfl
      · simp only [h', dite_false]
        exact ⟨fun he => (by cases he), fun ⟨w', h'', he, _⟩ => (by cases he; exact absurd h'' h')⟩

/-- The ports in `leftsOut` are the ports of the first cell that are middle wires. -/
theorem mem_leftsOut
    (i : Fin a) :
    i ∈ leftsOut X Y ↔ .inl i ∈ middle X Y := by
  simp [leftsOut]

-- ============================================================================================
-- 7. Auxiliary lemmas: the names of a side
-- ============================================================================================

/-- The net of the side is `halfNet`. -/
theorem half_net :
    (half X Y k mid).net = halfNet X Y k mid := rfl

/-- The added equations `i = mid(.inl i)` have no cell. -/
theorem extras_cells :
    (extras X Y k mid).cells = 0 := by
  simp [extras, Net.cells, Multiset.bind_map]

/-- The names of the added equations: the ports `.inl i` that occur in `Y`, and their middle
ports. -/
theorem extras_vars :
    (extras X Y k mid).vars =
      (leftsOut X Y).val.map (fun i => .inl i)
        + (leftsOut X Y).val.map (leftMid X Y k mid) := by
  simp only [extras, Net.vars, Multiset.bind_map, eqVars_mk, Term.vars_var]
  rw [Multiset.bind_add, Multiset.bind_singleton, Multiset.bind_singleton]

/-- When `x₀` is the only element sent to `some y` by `g`, `y` occurs in `m.filterMap g` as often
as `x₀` occurs in `m`. -/
theorem count_filterMap_of_iff
    -- the types, with decidable equality
    {α β : Type}
    [DecidableEq α]
    [DecidableEq β]
    -- the partial function and the multiset
    (g : α → Option β)
    (m : Multiset α)
    -- `x₀` is the only element sent to `y`
    (y : β)
    (x₀ : α)
    (h : ∀ x, g x = some y ↔ x = x₀) :
    (m.filterMap g).count y = m.count x₀ := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons z m ih =>
    cases hz : g z with
    | none =>
      have hne : z ≠ x₀ := fun he => by simp [(h z).2 he] at hz
      rw [Multiset.filterMap_cons_none _ _ hz, ih, Multiset.count_cons_of_ne (Ne.symm hne)]
    | some y' =>
      rw [Multiset.filterMap_cons_some _ _ _ hz]
      by_cases hy : y' = y
      · subst hy
        have := (h z).1 hz
        subst this
        rw [Multiset.count_cons_self, Multiset.count_cons_self, ih]
      · have hne : z ≠ x₀ := fun he => hy (Option.some.inj ((h z).2 he ▸ hz).symm)
        rw [Multiset.count_cons_of_ne (Ne.symm hy), ih, Multiset.count_cons_of_ne (Ne.symm hne)]

/-- When no element is sent to `some y` by `g`, `y` does not occur in `m.filterMap g`. -/
theorem count_filterMap_of_none
    -- the types, with decidable equality on the target
    {α β : Type}
    [DecidableEq β]
    -- the partial function and the multiset
    (g : α → Option β)
    (m : Multiset α)
    -- no element is sent to `y`
    (y : β)
    (h : ∀ x, g x ≠ some y) :
    (m.filterMap g).count y = 0 :=
  Multiset.count_eq_zero.2 fun hm => by
    obtain ⟨x, -, hx⟩ := (Multiset.mem_filterMap _ _).1 hm
    exact h x hx

section Linear

variable {X Y k mid}

/-- Distinct ports of the first cell have distinct middle ports, when `mid` is injective. -/
theorem leftMid_injective
    -- `mid` numbers distinct middle wires differently
    (hinj : ∀ x hx y hy, mid x hx = mid y hy → x = y) :
    Function.Injective (leftMid X Y k mid) := by
  intro i i' h
  by_cases h1 : .inl i ∈ middle X Y <;> by_cases h2 : .inl i' ∈ middle X Y <;>
    simp only [leftMid, h1, h2, dite_true, dite_false] at h
  · exact Sum.inl_injective (hinj _ _ _ _ (Sum.inl_injective (Sum.inr_injective h)))
  · cases h
  · cases h
  · exact Sum.inl_injective h

end Linear

-- ============================================================================================
-- 8. Main results: the properties of a side
-- ============================================================================================

/-- The cells of a side are those of `X`. -/
theorem half_cells :
    (half X Y k mid).net.cells = X.cells := by
  change Net.cells (halfNet X Y k mid) = X.cells
  have h1 := (Net.renameOpt_spec (ren X Y k mid) X (ren_isSome X Y k mid)).2.1
  have h2 := extras_cells X Y k mid
  rw [show Net.cells (halfNet X Y k mid) =
    (Net.renameOpt (ren X Y k mid) X).cells + (extras X Y k mid).cells from
    Multiset.add_bind _ _ _, h1, h2, add_zero]

/-- The plugging of trees into a side: plugging `F` into the side is plugging `G` into `X`, plus
the equations `F(.inl i) = G(.inl i)` for the ports `.inl i` that occur in `Y`, as soon as `F`
and `G` agree through the renaming. -/
theorem half_bind
    -- the names plugged into the side, and into `X`
    {κ : Type}
    (F : Fin a ⊕ Fin k ⊕ Fin (inner X Y).card → κ)
    (G : Fin a ⊕ Fin b ⊕ Fin n → κ)
    -- they agree on the middle wires,
    (h1 : ∀ x (h : x ∈ middle X Y), F (.inr (.inl (mid x h))) = G x)
    -- on the ports of the first cell that are not middle wires,
    (h2 : ∀ i, .inl i ∉ middle X Y → F (.inl i) = G (.inl i))
    -- and on the inner wires
    (h3 : ∀ w (h : w ∈ inner X Y), .inr (.inr w) ∉ middle X Y →
      F (.inr (.inr (innerIdx X Y h))) = G (.inr (.inr w))) :
    -- the side with `F` plugged is `X` with `G` plugged, plus the equations `F(.inl i) = G(.inl i)`
    (halfNet X Y k mid).bind (fun y => var (F y)) =
      X.bind (fun x => var (G x)) +
        (leftsOut X Y).val.map fun i => s(var (F (.inl i)), var (G (.inl i))) := by
  have hspec := (Net.renameOpt_spec (ren X Y k mid) X (ren_isSome X Y k mid)).2.2
    (fun y => var (F y)) (fun x => var (G x)) (by
      intro x _ y hy
      congr 1
      rcases y with i | l | m
      · obtain ⟨rfl, hi⟩ := (ren_eq_left X Y k mid x i).1 hy
        exact h2 i hi
      · obtain ⟨h, rfl⟩ := (ren_eq_mid X Y k mid x l).1 hy
        exact h1 x h
      · obtain ⟨w, h, rfl, hw, rfl⟩ := (ren_eq_inner X Y k mid x m).1 hy
        exact h3 w h hw)
  simp only [halfNet, Net.bind, Multiset.map_add] at hspec ⊢
  rw [hspec]
  congr 1
  simp only [extras, Multiset.map_map, Function.comp_def, Sym2.map_mk, Term.bind_var]
  refine Multiset.map_congr rfl fun i hi => ?_
  have hi' : .inl i ∈ middle X Y := (mem_leftsOut X Y _).1 hi
  simp only [leftMid, hi', dite_true, h1 _ hi']

section Linear

variable {X Y k mid}

/-- A side is linear: each port of the first cell and each middle wire occurs once, each internal
wire twice, when the two sides together are linear and `mid` numbers the middle wires one for
one. -/
theorem half_linear
    -- the two sides together are linear: each port of the two cells occurs once,
    (hl : ∀ i, (X.vars + Y.vars).count (.inl i) = 1)
    (hr : ∀ j, (X.vars + Y.vars).count (.inr (.inl j)) = 1)
    -- and each internal wire twice
    (hw : ∀ w, (X.vars + Y.vars).count (.inr (.inr w)) = 2)
    -- `mid` numbers the middle wires one for one
    (hinj : ∀ x hx y hy, mid x hx = mid y hy → x = y)
    (hsurj : ∀ l, ∃ x hx, mid x hx = l) :
    (half X Y k mid).Linear := by
  have hv := (Net.renameOpt_spec (ren X Y k mid) X (ren_isSome X Y k mid)).1
  have hvars : (halfNet X Y k mid).vars =
      X.vars.filterMap (ren X Y k mid) + ((leftsOut X Y).val.map (fun i => .inl i) +
        (leftsOut X Y).val.map (leftMid X Y k mid)) := by
    rw [halfNet, Net.vars_add, hv, extras_vars]
  have hmapl : ∀ i,
      ((leftsOut X Y).val.map
        (fun i => (.inl i : Fin a ⊕ Fin k ⊕ Fin (inner X Y).card))).count
      (.inl i) = if .inl i ∈ middle X Y then 1 else 0 := by
    intro i
    rw [Multiset.count_map_eq_count' _ _ Sum.inl_injective,
      Multiset.count_eq_of_nodup (Finset.nodup _)]
    simp [mem_leftsOut]
  refine ⟨fun i => ?_, fun l => ?_, fun (m : Fin (inner X Y).card) => ?_⟩
  · change Multiset.count (Sum.inl i : Fin a ⊕ Fin k ⊕ Fin (inner X Y).card)
      (Net.vars (halfNet X Y k mid)) = 1
    rw [hvars, Multiset.count_add, Multiset.count_add, hmapl]
    have h3 : ((leftsOut X Y).val.map (leftMid X Y k mid)).count (.inl i) = 0 := by
      refine Multiset.count_eq_zero.2 fun hm => ?_
      obtain ⟨i', hi', he⟩ := Multiset.mem_map.1 hm
      have : .inl i' ∈ middle X Y := (mem_leftsOut X Y _).1 hi'
      simp [leftMid, this] at he
    rw [h3]
    have hli := hl i
    rw [Multiset.count_add] at hli
    by_cases hm : .inl i ∈ middle X Y
    · rw [count_filterMap_of_none _ _ _ fun x hx => ((ren_eq_left X Y k mid x i).1 hx).2 hm]
      simp [hm]
    · rw [count_filterMap_of_iff _ _ _ (.inl i) fun x => by
        rw [ren_eq_left]; simp [hm]]
      have hY : .inl i ∉ Y.vars := fun h => hm ((mem_middle_inl X Y i).2 h)
      rw [Multiset.count_eq_zero.2 hY] at hli
      simp [hm, hli]
  · obtain ⟨x, hx, rfl⟩ := hsurj l
    change Multiset.count (Sum.inr (Sum.inl (mid x hx)) : Fin a ⊕ Fin k ⊕ Fin (inner X Y).card)
      (Net.vars (halfNet X Y k mid)) = 1
    rw [hvars, Multiset.count_add, Multiset.count_add,
      count_filterMap_of_iff _ _ _ x fun x' => by
        rw [ren_eq_mid]
        exact ⟨fun ⟨h', he⟩ => hinj _ _ _ _ he, fun he => by subst he; exact ⟨hx, rfl⟩⟩]
    have h2 : ((leftsOut X Y).val.map
          (fun i => (.inl i : Fin a ⊕ Fin k ⊕ Fin (inner X Y).card))).count
        (.inr (.inl (mid x hx))) = 0 :=
      Multiset.count_eq_zero.2 fun hm => by
        obtain ⟨_, _, he⟩ := Multiset.mem_map.1 hm
        cases he
    rw [h2]
    rcases x with i | j | w
    · have hY := (mem_middle_inl X Y i).1 hx
      have hli := hl i
      rw [Multiset.count_add] at hli
      have hX : Multiset.count (Sum.inl i) X.vars = 0 := by
        have := Multiset.one_le_count_iff_mem.2 hY
        omega
      have hlm : leftMid X Y k mid i = .inr (.inl (mid (.inl i) hx)) := by
        simp [leftMid, hx]
      rw [hX, ← hlm, Multiset.count_map_eq_count' _ _ (leftMid_injective hinj)]
      have hi : i ∈ leftsOut X Y := Finset.mem_filter.2 ⟨Finset.mem_univ _, hx⟩
      rw [Multiset.count_eq_one_of_mem (Finset.nodup (leftsOut X Y)) hi]
    · have hX := (mem_middle_inr_inl X Y j).1 hx
      have hrj := hr j
      rw [Multiset.count_add] at hrj
      have h1 := Multiset.one_le_count_iff_mem.2 hX
      have h3 : ((leftsOut X Y).val.map (leftMid X Y k mid)).count
          (.inr (.inl (mid (.inr (.inl j)) hx))) = 0 :=
        Multiset.count_eq_zero.2 fun hm => by
          obtain ⟨i, hi, he⟩ := Multiset.mem_map.1 hm
          have hi' : .inl i ∈ middle X Y := (mem_leftsOut X Y _).1 hi
          simp only [leftMid, hi', dite_true] at he
          cases hinj _ _ _ _ (Sum.inl_injective (Sum.inr_injective he))
      rw [h3]
      omega
    · obtain ⟨hX, hY⟩ := (mem_middle_inr_inr X Y w).1 hx
      have hww := hw w
      rw [Multiset.count_add] at hww
      have h1 := Multiset.one_le_count_iff_mem.2 hX
      have h1' := Multiset.one_le_count_iff_mem.2 hY
      have h3 : ((leftsOut X Y).val.map (leftMid X Y k mid)).count
          (.inr (.inl (mid (.inr (.inr w)) hx))) = 0 :=
        Multiset.count_eq_zero.2 fun hm => by
          obtain ⟨i, hi, he⟩ := Multiset.mem_map.1 hm
          have hi' : .inl i ∈ middle X Y := (mem_leftsOut X Y _).1 hi
          simp only [leftMid, hi', dite_true] at he
          cases hinj _ _ _ _ (Sum.inl_injective (Sum.inr_injective he))
      rw [h3]
      omega
  · obtain ⟨w, hwi, hm⟩ := rankIn_surj (M := inner X Y) Fin.val_injective m.isLt
    have hm' : innerIdx X Y hwi = m := Fin.ext hm
    obtain ⟨hX, hY⟩ := (mem_inner X Y w).1 hwi
    have hnm : .inr (.inr w) ∉ middle X Y := fun h => hY ((mem_middle_inr_inr X Y w).1 h).2
    change Multiset.count (Sum.inr (Sum.inr m) : Fin a ⊕ Fin k ⊕ Fin (inner X Y).card)
      (Net.vars (halfNet X Y k mid)) = 2
    rw [hvars, Multiset.count_add, Multiset.count_add,
      count_filterMap_of_iff _ _ _ (.inr (.inr w)) fun x => by
        rw [ren_eq_inner]
        constructor
        · rintro ⟨w', h', rfl, -, he⟩
          rw [← hm'] at he
          have := rankIn_injOn (M := inner X Y) Fin.val_injective h' hwi
            (congrArg Fin.val he)
          rw [this]
        · rintro rfl
          exact ⟨w, hwi, rfl, hnm, hm'⟩]
    have h2 : ((leftsOut X Y).val.map
          (fun i => (.inl i : Fin a ⊕ Fin k ⊕ Fin (inner X Y).card))).count
        (.inr (.inr m)) = 0 :=
      Multiset.count_eq_zero.2 fun hm => by
        obtain ⟨_, _, he⟩ := Multiset.mem_map.1 hm
        cases he
    have h3 : ((leftsOut X Y).val.map (leftMid X Y k mid)).count (.inr (.inr m)) = 0 :=
      Multiset.count_eq_zero.2 fun hm => by
        obtain ⟨i, hi, he⟩ := Multiset.mem_map.1 hm
        have hi' : .inl i ∈ middle X Y := (mem_leftsOut X Y _).1 hi
        simp [leftMid, hi'] at he
    have hww := hw w
    rw [Multiset.count_add, Multiset.count_eq_zero.2 hY] at hww
    rw [h2, h3, hww]

/-- A side is a reduced net when every equation of `X` is rooted at a port of the first cell:
every equation of the side has a port (of the first cell, or a middle wire) on one side. -/
theorem half_reduced
    -- every equation of `X` is rooted at a port of the first cell
    (hX : ∀ e ∈ X, LeftRooted e) :
    (half X Y k mid).Reduced := by
  intro e he
  rcases Multiset.mem_add.1 he with he | he
  · obtain ⟨e₀, he₀, hre⟩ := Net.mem_renameOpt.1 he
    obtain ⟨i, hi⟩ := hX e₀ he₀
    obtain ⟨t, rfl⟩ : ∃ t, e₀ = s(var (.inl i), t) := ⟨hi.other, (Sym2.other_spec hi).symm⟩
    obtain ⟨u', t', hu, -, rfl⟩ := renameOptEq_mk hre
    simp only [Term.renameOpt, Option.map_eq_some_iff] at hu
    obtain ⟨y, hy, rfl⟩ := hu
    refine ⟨y, t', rfl, fun w hw => ?_⟩
    subst hw
    obtain ⟨w', -, h, -⟩ := (ren_eq_inner X Y k mid _ w).1 hy
    cases h
  · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 he
    exact ⟨.inl i, _, rfl, fun w h => by cases h⟩

end Linear

end Half

end INet
