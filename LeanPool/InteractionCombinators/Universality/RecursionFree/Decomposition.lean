/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Universality.RecursionFree.DecompositionHalf
public import Mathlib.Data.Fintype.Inv

/-!
# The canonical decomposition of a rule (page 85)

Lafont 1997, page 85 (PDF page 17): "The right member of a rule is a reduced net which can be
decomposed as follows [figure], where `φ_{i,j}` and `ψ_{i,j}` are reduced nets, and `σ_{i,j}` is a
permutation. Of course, such a decomposition is not unique, but there is a canonical one." In the
figure, `φ_{i,j}` carries the auxiliary ports of `α_i`, `ψ_{i,j}` those of `α_j`, and `σ_{i,j}`
joins `k` wires of `φ_{i,j}` to `k` wires of `ψ_{i,j}`. The paper gives no proof.

## Representation

* `Decomposition S a b` — a number `k` of middle wires, `φ : Rule S a k`, `ψ : Rule S b k` and
  `σ : Equiv.Perm (Fin k)`. A side is a `Rule`-shaped net: `φ.net` is a net over
  `Fin a ⊕ Fin k ⊕ Fin φ.internal`, whose free ports are the `a` ports of the first cell
  (`.inl i`) and the `k` middle wires (`.inr (.inl l)`), and whose internal wires are
  `.inr (.inr w)`. This reuses `Rule.Linear` (each free port once, each internal wire twice) and
  `Rule.Reduced` (every equation has a free port on one side) for the sides.
* `Rule.plug φ ψ σ : Rule S a b` — the figure of page 85: the middle wire `l` of `φ` is joined to
  the middle wire `σ l` of `ψ`. The joined wires become internal wires of the result, numbered
  `0, …, k - 1`; the internal wires of `φ` and `ψ` follow.

## The canonical decomposition

`Rule.decompose r` splits the equations of `r.net` into those rooted at a port of the first cell
(`Half.LeftRooted`: one side is a leaf `.inl i`) and the others, which for a reduced rule are
rooted at a port of the second cell. So the cells of `φ` are exactly those of the trees of
`r.net` rooted at a port `.inl i`, and the cells of `ψ` those of the other trees
(`decompose_cells_left`, `decompose_cells_right`). An equation `.inl i = .inr (.inl j)` between a
port of each cell has no cell; it goes with the first cell.

The middle wires are the names of `r.net` that join the two parts (`Half.middle`): an internal
wire with one end in each part, a port `.inr (.inl j)` that occurs in the first part (in
particular in an equation `.inl i = .inr (.inl j)`), and a port `.inl i` that occurs in the second
part. In the last case `φ` gets the equation `.inl i = l` for the middle wire `l`; in the
second, `ψ` gets `.inl j = l`.

Each side numbers its middle wires by itself: first by the port at the root of the tree where the
wire occurs, then by the name of the wire in `r` (`Half.key`). The numbering of a tree's wires
thus follows the names of the rule, not their position in the tree. `σ` sends the number of a
wire in `φ` to its number in `ψ`. For `con`–`con` this gives the exchange, and for `con`–`dup` the
permutation `(1 2)` of the four wires (`Checks/Universality/RecursionFree/DecompositionCheck.lean`).
The symmetric normalisation of page 85 (`ψ_{j,i} = φ_{i,j}`) is not done here.

## Results

* `decompose_linear`, `decompose_reduced` — `φ` and `ψ` are linear and reduced.
* `decompose_cells_left`, `decompose_cells_right`, `decompose_cells` — the cells.
* `plug_linear` — plugging two linear sides gives a linear net.
* `plug_decompose` — plugging `φ` and `ψ` through `σ` gives back `r.net`, up to `Equiv` and an
  injective renaming of the internal wires of `r`, for every linear rule.

Contents, in the order of the file:

1. Definitions: a decomposition and the plug of two sides: `Decomposition`, `Rule.plugL`,
   `Rule.plugR`, `Rule.plug`.
2. Auxiliary lemmas on the plug: `plugL_injective`, `plugR_injective`,
   `Multiset.count_map_eq_zero`, `Net.cells_bind_var`.
3. Result: `plug_linear`, plugging two linear sides gives a linear net.
4. Definitions and lemmas: the two parts of a rule and its middle wires: `leftPart`,
   `rightPart`, `swapName`, `leftSw`, `rightSw`, `midL`, `midR`, with `swapName_mem_midR` and
   `card_midR`.
5. Definitions and lemmas: the numbering of the middle wires and the permutation: `kDec`, `midφ`,
   `midψ`, `unrankL`, `σfun`, `σDec`, with `σDec_midφ`.
6. Definition: `decompose`, the canonical decomposition (page 85).
7. Results on the sides: `leftPart_add_rightPart`, `vars_parts`, `vars_sw`, then
   `decompose_linear`, `decompose_reduced`, `decompose_cells_left`, `decompose_cells_right`,
   `decompose_cells`.
8. Definitions: plugging the sides back together: `plugInt`, `mem_innerR`, `iotaDec`, `mw`,
   `thetaDec`.
9. Auxiliary lemmas on the plugged net: `iotaDec_injective`, `thetaDec_of_mem`,
   `thetaDec_of_notMem`, `plug_decompose_net`, `Rule.Linear.net_linear`, `mw_injective`.
10. Main result: `plug_decompose`, the plugged canonical decomposition is the rule, up to wires
    (page 85).
-/

@[expose] public section

namespace INet

variable {S : Signature}

open Term Half

-- ============================================================================================
-- 1. Definitions: a decomposition and the plug of two sides
-- ============================================================================================

/-- A decomposition of the right member of a rule for two cells with `a` and `b` auxiliary ports
(Lafont 1997, page 85): `k` middle wires, a net `φ` on the `a` ports of the first cell and the
middle wires, a net `ψ` on the `b` ports of the second cell and the middle wires, and the
permutation `σ` that joins the middle wire `l` of `φ` to the middle wire `σ l` of `ψ`. -/
structure Decomposition
    -- the signature, and the numbers of auxiliary ports of the two cells
    (S : Signature)
    (a b : ℕ) where
  /-- The number of middle wires. -/
  k : ℕ
  /-- The side of the first cell (`φ_{i,j}`). -/
  φ : Rule S a k
  /-- The side of the second cell (`ψ_{i,j}`). -/
  ψ : Rule S b k
  /-- The permutation of the middle wires (`σ_{i,j}`). -/
  σ : Equiv.Perm (Fin k)

namespace Rule

-- the ports of the two cells (`a`, `b`), the middle wires (`k`), and the internal wires of the
-- two sides (`m`, `n`)
variable {a b k m n : ℕ}

/-- The names of `φ` in the plugged net. -/
def plugL :
    Fin a ⊕ Fin k ⊕ Fin m → Fin a ⊕ Fin b ⊕ Fin (k + m + n)
  | .inl i => .inl i
  | .inr (.inl l) => .inr (.inr (Fin.castAdd n (Fin.castAdd m l)))
  | .inr (.inr j) => .inr (.inr (Fin.castAdd n (Fin.natAdd k j)))

/-- The names of `ψ` in the plugged net: its middle wire `l` is the middle wire `σ⁻¹ l` of `φ`. -/
def plugR
    -- the permutation of the middle wires
    (σ : Equiv.Perm (Fin k)) :
    Fin b ⊕ Fin k ⊕ Fin n → Fin a ⊕ Fin b ⊕ Fin (k + m + n)
  | .inl j => .inr (.inl j)
  | .inr (.inl l) => .inr (.inr (Fin.castAdd n (Fin.castAdd m (σ.symm l))))
  | .inr (.inr j) => .inr (.inr (Fin.natAdd (k + m) j))

/-- The figure of page 85: `φ` and `ψ` plugged together, the middle wire `l` of `φ` joined to the
middle wire `σ l` of `ψ`. -/
def plug
    -- the two sides and the permutation of the middle wires
    (φ : Rule S a k)
    (ψ : Rule S b k)
    (σ : Equiv.Perm (Fin k)) :
    Rule S a b where
  internal := k + φ.internal + ψ.internal
  net := φ.net.bind (fun x => var (plugL x)) + ψ.net.bind (fun x => var (plugR σ x))

-- ============================================================================================
-- 2. Auxiliary lemmas on the plug
-- ============================================================================================

/-- The renaming `plugL` of the names of `φ` is injective. -/
theorem plugL_injective :
    Function.Injective (plugL : Fin a ⊕ Fin k ⊕ Fin m → Fin a ⊕ Fin b ⊕ Fin (k + m + n)) := by
  intro x y h
  rcases x with i | l | j <;> rcases y with i' | l' | j' <;>
    simp [plugL, Fin.ext_iff] at h ⊢ <;> omega

/-- The renaming `plugR σ` of the names of `ψ` is injective. -/
theorem plugR_injective
    -- the permutation of the middle wires
    (σ : Equiv.Perm (Fin k)) :
    Function.Injective (plugR (a := a) (m := m) (b := b) (n := n) σ) := by
  intro x y h
  rcases x with i | l | j <;> rcases y with i' | l' | j' <;>
    simp only [plugR, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, Fin.ext_iff,
      Fin.val_castAdd, Fin.val_natAdd] at h ⊢
  all_goals first
    | omega
    | (have := σ.symm.injective (Fin.ext h); exact congrArg Fin.val this)

/-- A point that is not in the image of `f` does not occur in the image of a multiset by `f`. -/
theorem _root_.Multiset.count_map_eq_zero
    -- the two types and the map
    {α β : Type}
    [DecidableEq β]
    {f : α → β}
    -- the multiset
    {s : Multiset α}
    -- a point outside the image of `f`
    {z : β}
    (h : ∀ y, f y ≠ z) :
    (s.map f).count z = 0 :=
  Multiset.count_eq_zero.2 fun hm => by
    obtain ⟨y, -, hy⟩ := Multiset.mem_map.1 hm
    exact h y hy

/-- Renaming the names of a net does not change its cells. -/
theorem _root_.INet.Net.cells_bind_var
    -- the two types of names and the renaming
    {ν μ : Type}
    (f : ν → μ)
    -- the net
    (N : Net S ν) :
    (N.bind fun x => var (f x)).cells = N.cells := by
  unfold Net.cells Net.bind
  rw [Multiset.bind_map]
  congr 1
  funext e
  induction e using Sym2.ind with
  | _ u v => simp [Term.cells_bind]

-- ============================================================================================
-- 3. Result: plugging two linear sides gives a linear net
-- ============================================================================================

/-- Plugging two linear sides together gives a linear net: each middle wire occurs once in each
side, so twice in the result (page 85). -/
theorem plug_linear
    -- the two sides
    {φ : Rule S a k}
    {ψ : Rule S b k}
    -- the permutation of the middle wires
    (σ : Equiv.Perm (Fin k))
    -- both sides are linear
    (hφ : φ.Linear)
    (hψ : ψ.Linear) :
    (plug φ ψ σ).Linear := by
  let V := Fin a ⊕ Fin b ⊕ Fin (k + φ.internal + ψ.internal)
  have hvars : ∀ z : V, Multiset.count z
      (Net.vars (φ.net.bind (fun x => var (plugL x)) + ψ.net.bind (fun x => var (plugR σ x)))) =
      (φ.net.vars.map plugL).count z + (ψ.net.vars.map (plugR σ)).count z := by
    intro z
    rw [Net.vars_add, Net.vars_bind_var, Net.vars_bind_var, Multiset.count_add]
  have hl : ∀ i, (φ.net.vars.map plugL).count (.inl i : V) +
      (ψ.net.vars.map (plugR σ)).count (.inl i : V) = 1 := by
    intro i
    rw [show (.inl i : V) = plugL (.inl i) from rfl,
      Multiset.count_map_eq_count' _ _ plugL_injective, hφ.left, Multiset.count_map_eq_zero]
    rintro (j | l | j) h <;> simp [plugR, plugL] at h
  have hr : ∀ j, (φ.net.vars.map plugL).count (.inr (.inl j) : V) +
      (ψ.net.vars.map (plugR σ)).count (.inr (.inl j) : V) = 1 := by
    intro j
    rw [show (.inr (.inl j) : V) = plugR σ (.inl j) from rfl,
      Multiset.count_map_eq_count' _ _ (plugR_injective σ), hψ.left,
      Multiset.count_map_eq_zero]
    rintro (i | l | j) h <;> simp [plugR, plugL] at h
  have hw : ∀ t, (φ.net.vars.map plugL).count (.inr (.inr t) : V) +
      (ψ.net.vars.map (plugR σ)).count (.inr (.inr t) : V) = 2 := by
    intro t
    by_cases h1 : t.val < k
    · set l : Fin k := ⟨t.val, h1⟩
      have e1 : (.inr (.inr t) : V) = plugL (.inr (.inl l)) := by simp [plugL, l]
      have e2 : (.inr (.inr t) : V) = plugR σ (.inr (.inl (σ l))) := by
        simp [plugR, l]
      rw [e1, Multiset.count_map_eq_count' _ _ plugL_injective, hφ.right, ← e1, e2,
        Multiset.count_map_eq_count' _ _ (plugR_injective σ), hψ.right]
    · by_cases h2 : t.val < k + φ.internal
      · set j : Fin φ.internal := ⟨t.val - k, by omega⟩
        have e1 : (.inr (.inr t) : V) = plugL (.inr (.inr j)) := by
          simp [plugL, j, Fin.ext_iff]; omega
        rw [e1, Multiset.count_map_eq_count' _ _ plugL_injective, hφ.internal, ← e1,
          Multiset.count_map_eq_zero]
        rintro (i | l | j') h <;> simp [plugR, Fin.ext_iff] at h <;> omega
      · set j : Fin ψ.internal := ⟨t.val - (k + φ.internal), by omega⟩
        have e2 : (.inr (.inr t) : V) = plugR σ (.inr (.inr j)) := by
          simp [plugR, j, Fin.ext_iff]; omega
        rw [e2, Multiset.count_map_eq_count' _ _ (plugR_injective σ), hψ.internal, ← e2,
          Multiset.count_map_eq_zero]
        rintro (i | l | j') h <;> simp [plugL, Fin.ext_iff] at h <;> omega
  exact ⟨fun i => (hvars _).trans (hl i), fun j => (hvars _).trans (hr j),
    fun t => (hvars _).trans (hw t)⟩

-- ============================================================================================
-- 4. Definitions and lemmas: the two parts of a rule and its middle wires
-- ============================================================================================

-- the rule to decompose, between two cells with `a` and `b` auxiliary ports
variable {a b : ℕ} (r : Rule S a b)

/-- The equations of the right member rooted at a port of the first cell. -/
def leftPart :
    Net S (Fin a ⊕ Fin b ⊕ Fin r.internal) :=
  r.net.filter LeftRooted

/-- The other equations; for a reduced rule they are rooted at a port of the second cell. -/
def rightPart :
    Net S (Fin a ⊕ Fin b ⊕ Fin r.internal) :=
  r.net.filter fun e => ¬LeftRooted e

/-- Exchange the two groups of ports, as in `Rule.swap`. -/
def swapName
    -- the numbers of ports of the two cells and of internal wires
    {a b n : ℕ} :
    Fin a ⊕ Fin b ⊕ Fin n → Fin b ⊕ Fin a ⊕ Fin n :=
  Sum.elim (fun i => .inr (.inl i)) (Sum.elim .inl fun w => .inr (.inr w))

/-- Exchanging the ports twice gives back the name. -/
theorem swapName_swapName
    -- the numbers of ports of the two cells and of internal wires
    {a b n : ℕ}
    -- the name
    (x : Fin a ⊕ Fin b ⊕ Fin n) :
    swapName (swapName x) = x := by
  rcases x with i | j | w <;> rfl

/-- Exchanging the ports is injective. -/
theorem swapName_injective
    -- the numbers of ports of the two cells and of internal wires
    {a b n : ℕ} :
    Function.Injective (swapName : Fin a ⊕ Fin b ⊕ Fin n → Fin b ⊕ Fin a ⊕ Fin n) :=
  fun x y h => by simpa [swapName_swapName] using congrArg swapName h

/-- The second part with the ports exchanged: the side being built for `ψ`. -/
def leftSw :
    Net S (Fin b ⊕ Fin a ⊕ Fin r.internal) :=
  r.rightPart.bind fun x => var (swapName x)

/-- The first part with the ports exchanged: the other side for `ψ`. -/
def rightSw :
    Net S (Fin b ⊕ Fin a ⊕ Fin r.internal) :=
  r.leftPart.bind fun x => var (swapName x)

/-- The middle wires, as names of `r`. -/
def midL :
    Finset (Fin a ⊕ Fin b ⊕ Fin r.internal) :=
  middle r.leftPart r.rightPart

/-- The middle wires, as names of `r` with the ports exchanged. -/
def midR :
    Finset (Fin b ⊕ Fin a ⊕ Fin r.internal) :=
  middle r.leftSw r.rightSw

/-- A name occurs in a net with the ports exchanged exactly when it occurs in the net. -/
theorem mem_vars_sw
    -- a net over the names of `r`
    {N : Net S (Fin a ⊕ Fin b ⊕ Fin r.internal)}
    -- a name of `r`
    {x : Fin a ⊕ Fin b ⊕ Fin r.internal} :
    swapName x ∈ (N.bind fun x => var (swapName x)).vars ↔ x ∈ N.vars := by
  rw [Net.vars_bind_var]
  exact Multiset.mem_map_of_injective swapName_injective

/-- The middle wires with the ports exchanged are the middle wires, exchanged. -/
theorem swapName_mem_midR
    -- a name of `r`
    (x : Fin a ⊕ Fin b ⊕ Fin r.internal) :
    swapName x ∈ r.midR ↔ x ∈ r.midL := by
  rcases x with i | j | w
  · exact (mem_middle_inr_inl _ _ i).trans ((r.mem_vars_sw).trans (mem_middle_inl _ _ i).symm)
  · exact (mem_middle_inl _ _ j).trans ((r.mem_vars_sw).trans (mem_middle_inr_inl _ _ j).symm)
  · exact (mem_middle_inr_inr _ _ w).trans ((and_congr r.mem_vars_sw r.mem_vars_sw).trans
      (and_comm.trans (mem_middle_inr_inr _ _ w).symm))

/-- The two sides see the same number of middle wires. -/
theorem card_midR :
    r.midR.card = r.midL.card := by
  have : r.midR = r.midL.map ⟨swapName, swapName_injective⟩ := by
    ext y
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · intro hy
      exact ⟨swapName y, (r.swapName_mem_midR _).1 (by rwa [swapName_swapName]),
        swapName_swapName y⟩
    · rintro ⟨x, hx, rfl⟩
      exact (r.swapName_mem_midR x).2 hx
  rw [this, Finset.card_map]

-- ============================================================================================
-- 5. Definitions and lemmas: the numbering of the middle wires and the permutation
-- ============================================================================================

/-- The number of middle wires. -/
def kDec :
    ℕ :=
  r.midL.card

/-- The number of a middle wire in `φ`. -/
def midφ
    -- a middle wire, as a name of `r`
    (x : Fin a ⊕ Fin b ⊕ Fin r.internal)
    (h : x ∈ r.midL) :
    Fin r.kDec :=
  ⟨rankIn r.midL (key r.leftPart) x, rankIn_lt h⟩

/-- The number of a middle wire in `ψ`. -/
def midψ
    -- a middle wire, as a name of `r` with the ports exchanged
    (y : Fin b ⊕ Fin a ⊕ Fin r.internal)
    (h : y ∈ r.midR) :
    Fin r.kDec :=
  ⟨rankIn r.midR (key r.leftSw) y, (rankIn_lt h).trans_eq r.card_midR⟩

/-- Two middle wires with the same number in `φ` are the same. -/
theorem midφ_inj :
    ∀ x hx y hy, r.midφ x hx = r.midφ y hy → x = y :=
  fun _ hx _ hy h => rankIn_injOn (key_injective _) hx hy (congrArg Fin.val h)

/-- Every number is the number of a middle wire in `φ`. -/
theorem midφ_surj :
    ∀ l, ∃ x hx, r.midφ x hx = l := fun l => by
  obtain ⟨x, hx, h⟩ := rankIn_surj (M := r.midL) (key_injective r.leftPart) l.isLt
  exact ⟨x, hx, Fin.ext h⟩

/-- The number of a middle wire in `ψ` depends only on the wire. -/
theorem midψ_congr
    -- two equal middle wires, as names of `r` with the ports exchanged
    {y y' : Fin b ⊕ Fin a ⊕ Fin r.internal}
    (e : y = y')
    (h : y ∈ r.midR)
    (h' : y' ∈ r.midR) :
    r.midψ y h = r.midψ y' h' := by
  subst e; rfl

/-- Two middle wires with the same number in `ψ` are the same. -/
theorem midψ_inj :
    ∀ x hx y hy, r.midψ x hx = r.midψ y hy → x = y :=
  fun _ hx _ hy h => rankIn_injOn (key_injective _) hx hy (congrArg Fin.val h)

/-- Every number is the number of a middle wire in `ψ`. -/
theorem midψ_surj :
    ∀ l, ∃ x hx, r.midψ x hx = l := fun l => by
  obtain ⟨x, hx, h⟩ := rankIn_surj (M := r.midR) (key_injective r.leftSw)
    (l.isLt.trans_eq r.card_midR.symm)
  exact ⟨x, hx, Fin.ext h⟩

/-- The middle wire numbered `l` in `φ`. -/
def unrankL
    -- the number
    (l : Fin r.kDec) :
    Fin a ⊕ Fin b ⊕ Fin r.internal :=
  Fintype.choose (fun x => ∃ h : x ∈ r.midL, r.midφ x h = l) (by
    obtain ⟨x, hx, h⟩ := r.midφ_surj l
    exact ⟨x, ⟨hx, h⟩, fun y ⟨hy, h'⟩ => r.midφ_inj _ hy _ hx (h'.trans h.symm)⟩)

/-- The wire `unrankL l` is a middle wire, numbered `l` in `φ`. -/
theorem unrankL_spec
    -- the number
    (l : Fin r.kDec) :
    ∃ h : r.unrankL l ∈ r.midL, r.midφ _ h = l :=
  Fintype.choose_spec (fun x => ∃ h : x ∈ r.midL, r.midφ x h = l) _

/-- `unrankL` inverts the numbering in `φ`. -/
theorem unrankL_midφ
    -- a middle wire, as a name of `r`
    (x : Fin a ⊕ Fin b ⊕ Fin r.internal)
    (h : x ∈ r.midL) :
    r.unrankL (r.midφ x h) = x := by
  obtain ⟨h', e⟩ := r.unrankL_spec (r.midφ x h)
  exact r.midφ_inj _ h' _ h e

/-- The permutation of the middle wires: the wire numbered `l` in `φ` has the number `σ l` in
`ψ`. -/
def σfun
    -- the number of the wire in `φ`
    (l : Fin r.kDec) :
    Fin r.kDec :=
  r.midψ (swapName (r.unrankL l)) ((r.swapName_mem_midR _).2 (r.unrankL_spec l).1)

/-- The renumbering `σfun` is a bijection. -/
theorem σfun_bijective :
    Function.Bijective r.σfun := by
  refine Finite.injective_iff_bijective.1 fun l l' h => ?_
  have h1 := r.midψ_inj _ _ _ _ h
  have h2 := swapName_injective h1
  obtain ⟨_, e⟩ := r.unrankL_spec l
  obtain ⟨_, e'⟩ := r.unrankL_spec l'
  rw [← e, ← e']
  simp only [h2]

/-- The permutation `σ` of the canonical decomposition. -/
def σDec :
    Equiv.Perm (Fin r.kDec) where
  toFun := r.σfun
  invFun := Fintype.bijInv r.σfun_bijective
  left_inv := Fintype.leftInverse_bijInv r.σfun_bijective
  right_inv := Fintype.rightInverse_bijInv r.σfun_bijective

/-- `σ` sends the number of a middle wire in `φ` to its number in `ψ`. -/
theorem σDec_midφ
    -- a middle wire, as a name of `r`
    (x : Fin a ⊕ Fin b ⊕ Fin r.internal)
    (h : x ∈ r.midL) :
    r.σDec (r.midφ x h) = r.midψ (swapName x) ((r.swapName_mem_midR x).2 h) := by
  exact r.midψ_congr (by rw [r.unrankL_midφ x h])
    ((r.swapName_mem_midR _).2 (r.unrankL_spec _).1) _

-- ============================================================================================
-- 6. Definition: the canonical decomposition (page 85)
-- ============================================================================================

/-- The canonical decomposition of a rule (Lafont 1997, page 85): `φ` is built from the trees
rooted at the ports of the first cell, `ψ` from the other trees, and `σ` joins their middle
wires. -/
def decompose :
    Decomposition S a b where
  k := r.kDec
  φ := half r.leftPart r.rightPart r.kDec r.midφ
  ψ := half r.leftSw r.rightSw r.kDec r.midψ
  σ := r.σDec

-- ============================================================================================
-- 7. Results on the sides: linear, reduced, and the cells (page 85)
-- ============================================================================================

/-- The two parts make up the right member. -/
theorem leftPart_add_rightPart :
    r.leftPart + r.rightPart = r.net :=
  Multiset.filter_add_not _ _

/-- The names of the two parts make up the names of the right member. -/
theorem vars_parts :
    r.leftPart.vars + r.rightPart.vars = r.net.vars := by
  rw [← Net.vars_add, leftPart_add_rightPart]

/-- The names of the two parts with the ports exchanged are the names of the right member,
exchanged. -/
theorem vars_sw :
    r.leftSw.vars + r.rightSw.vars = r.net.vars.map swapName := by
  rw [leftSw, rightSw, Net.vars_bind_var, Net.vars_bind_var, ← Multiset.map_add, add_comm,
    vars_parts]

/-- The sides of the canonical decomposition of a linear rule are linear (page 85): each port of
the cell and each middle wire occurs once, each internal wire twice. -/
theorem decompose_linear
    -- the rule is linear
    (hr : r.Linear) :
    -- `φ` is linear, and `ψ` is linear
    r.decompose.φ.Linear ∧ r.decompose.ψ.Linear := by
  refine ⟨half_linear (fun i => ?_) (fun j => ?_) (fun w => ?_) r.midφ_inj r.midφ_surj,
    half_linear (fun j => ?_) (fun i => ?_) (fun w => ?_) r.midψ_inj r.midψ_surj⟩
  · rw [vars_parts]; exact hr.left i
  · rw [vars_parts]; exact hr.right j
  · rw [vars_parts]; exact hr.internal w
  · rw [vars_sw, show (.inl j : Fin b ⊕ Fin a ⊕ Fin r.internal) = swapName (.inr (.inl j)) from rfl,
      Multiset.count_map_eq_count' _ _ swapName_injective]
    exact hr.right j
  · rw [vars_sw, show (.inr (.inl i) : Fin b ⊕ Fin a ⊕ Fin r.internal) = swapName (.inl i) from rfl,
      Multiset.count_map_eq_count' _ _ swapName_injective]
    exact hr.left i
  · rw [vars_sw, show (.inr (.inr w) : Fin b ⊕ Fin a ⊕ Fin r.internal) =
      swapName (.inr (.inr w)) from rfl, Multiset.count_map_eq_count' _ _ swapName_injective]
    exact hr.internal w

/-- The sides of the canonical decomposition of a reduced rule are reduced nets (page 85): every
equation has a free port on one side. -/
theorem decompose_reduced
    -- the rule is reduced
    (hr : r.Reduced) :
    -- `φ` is reduced, and `ψ` is reduced
    r.decompose.φ.Reduced ∧ r.decompose.ψ.Reduced := by
  refine ⟨half_reduced fun e he => (Multiset.mem_filter.1 he).2, half_reduced fun e he => ?_⟩
  obtain ⟨e₀, he₀, rfl⟩ := Multiset.mem_map.1 he
  obtain ⟨he₀, hnl⟩ := Multiset.mem_filter.1 he₀
  obtain ⟨p, t, rfl, hp⟩ := hr e₀ he₀
  rcases p with i | j | w
  · exact absurd ⟨i, Sym2.mem_mk_left _ _⟩ hnl
  · exact ⟨j, by simp [swapName]⟩
  · exact absurd rfl (hp w)

/-- The cells of `φ` are those of the trees of the right member rooted at a port of the first
cell (page 85). -/
theorem decompose_cells_left :
    r.decompose.φ.net.cells = Net.cells (r.net.filter LeftRooted) :=
  half_cells _ _ _ _

/-- The cells of `ψ` are those of the other trees of the right member (page 85). -/
theorem decompose_cells_right :
    r.decompose.ψ.net.cells = Net.cells (r.net.filter fun e => ¬LeftRooted e) :=
  (half_cells _ _ _ _).trans (Net.cells_bind_var _ _)

/-- The canonical decomposition loses no cell and creates none (page 85). -/
theorem decompose_cells :
    r.decompose.φ.net.cells + r.decompose.ψ.net.cells = r.net.cells := by
  rw [decompose_cells_left, decompose_cells_right]
  unfold Net.cells
  rw [← Multiset.add_bind, Multiset.filter_add_not]

-- ============================================================================================
-- 8. Definitions: plugging the sides back together
-- ============================================================================================

/-- The number of internal wires of the plugged canonical decomposition. -/
abbrev plugInt :
    ℕ :=
  r.kDec + (inner r.leftPart r.rightPart).card + (inner r.leftSw r.rightSw).card

/-- An internal wire of `r` with both ends in the second part, when it is neither a middle wire
nor inside the first part (for a linear rule). -/
theorem mem_innerR
    -- the rule is linear
    (hr : r.Linear)
    -- an internal wire of `r`, neither a middle wire nor inside the first part
    {w : Fin r.internal}
    (h : .inr (.inr w) ∉ r.midL)
    (h' : w ∉ inner r.leftPart r.rightPart) :
    w ∈ inner r.leftSw r.rightSw := by
  have hc := hr.internal w
  rw [← vars_parts, Multiset.count_add] at hc
  rw [midL, mem_middle_inr_inr] at h
  rw [mem_inner] at h'
  rw [mem_inner, rightSw, leftSw,
    show (.inr (.inr w) : Fin b ⊕ Fin a ⊕ Fin r.internal) = swapName (.inr (.inr w)) from rfl,
    r.mem_vars_sw, r.mem_vars_sw]
  by_cases hL : (.inr (.inr w) : Fin a ⊕ Fin b ⊕ Fin r.internal) ∈ r.leftPart.vars
  · by_cases hR : (.inr (.inr w) : Fin a ⊕ Fin b ⊕ Fin r.internal) ∈ r.rightPart.vars
    · exact absurd ⟨hL, hR⟩ h
    · exact absurd ⟨hL, hR⟩ h'
  · refine ⟨?_, hL⟩
    rw [Multiset.count_eq_zero.2 hL, zero_add] at hc
    exact Multiset.count_pos.1 (by omega)

/-- Where an internal wire of `r` goes in the plugged canonical decomposition: a middle wire to
its number in `φ`, an internal wire of `φ` or of `ψ` to its number there, shifted. -/
def iotaDec
    -- the rule is linear
    (hr : r.Linear)
    -- an internal wire of `r`
    (w : Fin r.internal) :
    Fin r.plugInt :=
  if h : .inr (.inr w) ∈ r.midL then Fin.castAdd _ (Fin.castAdd _ (r.midφ _ h))
  else if h' : w ∈ inner r.leftPart r.rightPart then
    Fin.castAdd _ (Fin.natAdd _ (innerIdx _ _ h'))
  else Fin.natAdd _ (innerIdx _ _ (r.mem_innerR hr h h'))

/-- A middle wire in the plugged net. -/
def mw
    -- the number of the middle wire
    (l : Fin r.kDec) :
    Fin a ⊕ Fin b ⊕ Fin r.plugInt :=
  .inr (.inr (Fin.castAdd _ (Fin.castAdd _ l)))

/-- Where a name of `r` goes in the plugged net before the equations between a port and a middle
wire are absorbed: a middle wire, even a port, to its wire; the other names as `iotaDec`. -/
def thetaDec
    -- the rule is linear
    (hr : r.Linear)
    -- a name of `r`
    (x : Fin a ⊕ Fin b ⊕ Fin r.internal) :
    Fin a ⊕ Fin b ⊕ Fin r.plugInt :=
  if h : x ∈ r.midL then r.mw (r.midφ x h) else Sum.map id (Sum.map id (r.iotaDec hr)) x

-- ============================================================================================
-- 9. Auxiliary lemmas on the plugged net
-- ============================================================================================

/-- An internal wire of `r` goes to one of the first `k` wires exactly when it is a middle
wire. -/
theorem iotaDec_val_lt
    -- the rule is linear
    (hr : r.Linear)
    -- an internal wire of `r`
    (w : Fin r.internal) :
    (r.iotaDec hr w).val < r.kDec ↔ .inr (.inr w) ∈ r.midL := by
  unfold iotaDec
  split_ifs with h h' <;> simp [h]
  omega

/-- A middle wire of `r` goes to its number in `φ`. -/
theorem iotaDec_of_mem
    -- the rule is linear
    (hr : r.Linear)
    -- an internal wire of `r` that is a middle wire
    {w : Fin r.internal}
    (h : .inr (.inr w) ∈ r.midL) :
    r.iotaDec hr w = Fin.castAdd _ (Fin.castAdd _ (r.midφ _ h)) := by
  simp [iotaDec, h]

/-- Distinct internal wires of `r` go to distinct internal wires of the plugged net. -/
theorem iotaDec_injective
    -- the rule is linear
    (hr : r.Linear) :
    Function.Injective (r.iotaDec hr) := by
  intro w w' he
  have hv := congrArg Fin.val he
  have hl := r.iotaDec_val_lt hr w
  have hl' := r.iotaDec_val_lt hr w'
  by_cases h1 : (.inr (.inr w) : Fin a ⊕ Fin b ⊕ Fin r.internal) ∈ r.midL <;>
    by_cases h1' : (.inr (.inr w') : Fin a ⊕ Fin b ⊕ Fin r.internal) ∈ r.midL
  · rw [r.iotaDec_of_mem hr h1, r.iotaDec_of_mem hr h1'] at hv
    simp only [Fin.val_castAdd] at hv
    exact Sum.inr_injective (Sum.inr_injective (r.midφ_inj _ _ _ _ (Fin.ext hv)))
  · exact absurd (hv ▸ hl.2 h1) (fun h => h1' (hl'.1 h))
  · exact absurd (hv.symm ▸ hl'.2 h1') (fun h => h1 (hl.1 h))
  · unfold iotaDec at hv
    by_cases h2 : w ∈ inner r.leftPart r.rightPart <;>
      by_cases h2' : w' ∈ inner r.leftPart r.rightPart <;>
      simp only [h1, h1', h2, h2', dite_true, dite_false, Fin.val_castAdd, Fin.val_natAdd,
        innerIdx] at hv
    · exact rankIn_injOn Fin.val_injective h2 h2' (by omega)
    · have := rankIn_lt (κ := Fin.val) h2
      omega
    · have := rankIn_lt (κ := Fin.val) h2'
      omega
    · exact rankIn_injOn Fin.val_injective (r.mem_innerR hr h1 h2) (r.mem_innerR hr h1' h2')
        (by omega)

/-- An internal wire inside the first part goes to its number among the internal wires of `φ`. -/
theorem iotaDec_of_innerL
    -- the rule is linear
    (hr : r.Linear)
    -- an internal wire of `r`, not a middle wire, inside the first part
    {w : Fin r.internal}
    (h : .inr (.inr w) ∉ r.midL)
    (h' : w ∈ inner r.leftPart r.rightPart) :
    r.iotaDec hr w = Fin.castAdd _ (Fin.natAdd _ (innerIdx _ _ h')) := by
  simp [iotaDec, h, h']

/-- Any other internal wire goes to its number among the internal wires of `ψ`. -/
theorem iotaDec_of_innerR
    -- the rule is linear
    (hr : r.Linear)
    -- an internal wire of `r`, neither a middle wire nor inside the first part
    {w : Fin r.internal}
    (h : .inr (.inr w) ∉ r.midL)
    (h' : w ∉ inner r.leftPart r.rightPart) :
    r.iotaDec hr w = Fin.natAdd _ (innerIdx _ _ (r.mem_innerR hr h h')) := by
  simp [iotaDec, h, h']

/-- A middle wire, even a port, goes to its middle wire in the plugged net. -/
theorem thetaDec_of_mem
    -- the rule is linear
    (hr : r.Linear)
    -- a name of `r` that is a middle wire
    {x : Fin a ⊕ Fin b ⊕ Fin r.internal}
    (h : x ∈ r.midL) :
    r.thetaDec hr x = r.mw (r.midφ x h) := by
  simp [thetaDec, h]

/-- A name that is not a middle wire goes where `iotaDec` sends it; a port stays a port. -/
theorem thetaDec_of_notMem
    -- the rule is linear
    (hr : r.Linear)
    -- a name of `r` that is not a middle wire
    {x : Fin a ⊕ Fin b ⊕ Fin r.internal}
    (h : x ∉ r.midL) :
    r.thetaDec hr x = Sum.map id (Sum.map id (r.iotaDec hr)) x := by
  simp [thetaDec, h]

/-- The plugged canonical decomposition is `r.net` renamed by `thetaDec`, plus an equation
`p = thetaDec p` for each port `p` that is a middle wire. -/
theorem plug_decompose_net
    -- the rule is linear
    (hr : r.Linear) :
    -- the plugged canonical decomposition is
    (Rule.plug r.decompose.φ r.decompose.ψ r.decompose.σ).net =
      -- `r.net` renamed by `thetaDec`,
      r.net.bind (fun x => var (r.thetaDec hr x))
      -- with an equation for each port of the first cell that is a middle wire
      + ((leftsOut r.leftPart r.rightPart).val.map
            (fun i => s(var (.inl i), var (r.thetaDec hr (.inl i))))
        -- and an equation for each port of the second cell that is a middle wire
        + (leftsOut r.leftSw r.rightSw).val.map
            (fun j => s(var (.inr (.inl j)), var (r.thetaDec hr (.inr (.inl j)))))) := by
  have hφ := half_bind r.leftPart r.rightPart r.kDec r.midφ
    (plugL (b := b) (n := (inner r.leftSw r.rightSw).card)) (r.thetaDec hr)
    (fun x h => by rw [r.thetaDec_of_mem hr h]; rfl)
    (fun i h => by rw [r.thetaDec_of_notMem hr h]; rfl)
    (fun w h hw => by
      rw [r.thetaDec_of_notMem hr hw]
      simp only [Sum.map_inr, r.iotaDec_of_innerL hr hw h]
      rfl)
  have hψ := half_bind r.leftSw r.rightSw r.kDec r.midψ
    (plugR (a := a) (m := (inner r.leftPart r.rightPart).card) r.σDec)
    (fun y => r.thetaDec hr (swapName y))
    (fun y h => by
      have hx : swapName y ∈ r.midL := (r.swapName_mem_midR _).1 (by rwa [swapName_swapName])
      rw [r.thetaDec_of_mem hr hx]
      have e : r.σDec (r.midφ _ hx) = r.midψ y h :=
        (r.σDec_midφ _ hx).trans (r.midψ_congr (swapName_swapName y) _ _)
      simp only [plugR, mw, ← e, Equiv.symm_apply_apply])
    (fun j h => by
      have hx : (.inr (.inl j) : Fin a ⊕ Fin b ⊕ Fin r.internal) ∉ r.midL :=
        fun hm => h ((r.swapName_mem_midR _).2 hm)
      rw [show swapName (.inl j : Fin b ⊕ Fin a ⊕ Fin r.internal) = .inr (.inl j) from rfl,
        r.thetaDec_of_notMem hr hx]
      rfl)
    (fun w h hw => by
      have hx : (.inr (.inr w) : Fin a ⊕ Fin b ⊕ Fin r.internal) ∉ r.midL :=
        fun hm => hw ((r.swapName_mem_midR _).2 hm)
      have hL : w ∉ inner r.leftPart r.rightPart := by
        rw [mem_inner] at h ⊢
        rw [rightSw, show (.inr (.inr w) : Fin b ⊕ Fin a ⊕ Fin r.internal) =
          swapName (.inr (.inr w)) from rfl, r.mem_vars_sw] at h
        exact fun h' => h.2 h'.1
      rw [show swapName (.inr (.inr w) : Fin b ⊕ Fin a ⊕ Fin r.internal) = .inr (.inr w) from rfl,
        r.thetaDec_of_notMem hr hx]
      simp only [Sum.map_inr, r.iotaDec_of_innerR hr hx hL]
      rfl)
  have hsw : (r.leftSw.bind fun y => var (r.thetaDec hr (swapName y))) =
      r.rightPart.bind fun x => var (r.thetaDec hr x) := by
    rw [leftSw, Net.bind_bind]
    simp only [Term.bind_var, swapName_swapName]
  change ((halfNet r.leftPart r.rightPart r.kDec r.midφ).bind
      (fun y => var (plugL (b := b) (n := (inner r.leftSw r.rightSw).card) y)) +
    (halfNet r.leftSw r.rightSw r.kDec r.midψ).bind
      (fun y => var (plugR (a := a) (m := (inner r.leftPart r.rightPart).card) r.σDec y)) :
      Net S (Fin a ⊕ Fin b ⊕ Fin r.plugInt)) = _
  rw [hφ, hψ, hsw, ← r.leftPart_add_rightPart]
  simp only [Net.bind, Multiset.map_add, plugL, plugR, swapName, Sum.elim_inl]
  abel

/-- The right member of a linear rule is a linear net. -/
theorem _root_.INet.Rule.Linear.net_linear
    -- a linear rule
    {a b : ℕ}
    {r : Rule S a b}
    (hr : r.Linear) :
    r.net.Linear := by
  intro x
  rcases x with i | j | w
  · rw [hr.left i]; omega
  · rw [hr.right j]; omega
  · rw [hr.internal w]

/-- Distinct numbers give distinct middle wires in the plugged net. -/
theorem mw_injective :
    Function.Injective r.mw := by
  intro l l' h
  simp only [mw, Sum.inr.injEq] at h
  exact Fin.ext (by simpa using congrArg Fin.val h)

-- ============================================================================================
-- 10. Main result: the plugged canonical decomposition is the rule (page 85)
-- ============================================================================================

/-- Plugging the two sides of the canonical decomposition of a linear rule through `σ` gives back
the right member of the rule (Lafont 1997, page 85): the plugged net is `r.net` with its internal
wires renamed one for one, up to `Equiv` (wire substitution). Only linearity is needed. -/
theorem plug_decompose
    -- the rule is linear
    (hr : r.Linear) :
    -- there is a renaming `ι` of the internal wires of `r` into those of the plugged net
    ∃ ι : Fin r.internal → Fin (Rule.plug r.decompose.φ r.decompose.ψ r.decompose.σ).internal,
      -- that is injective,
      Function.Injective ι ∧
      -- and the plugged net is the same graph as `r.net` renamed by `ι`
      Equiv (Rule.plug r.decompose.φ r.decompose.ψ r.decompose.σ).net
        (r.net.bind fun x => var (Sum.map id (Sum.map id ι) x)) := by
  classical
  refine ⟨r.iotaDec hr, r.iotaDec_injective hr, ?_⟩
  set θ := r.thetaDec hr with hθ
  set θ' : Fin a ⊕ Fin b ⊕ Fin r.internal → Fin a ⊕ Fin b ⊕ Fin r.plugInt :=
    Sum.map id (Sum.map id (r.iotaDec hr)) with hθ'
  set Fl := leftsOut r.leftPart r.rightPart with hFl
  set Fr := leftsOut r.leftSw r.rightSw with hFr
  let eL : Fin a ↪ Fin a ⊕ Fin b ⊕ Fin r.plugInt := ⟨Sum.inl, Sum.inl_injective⟩
  let eR : Fin b ↪ Fin a ⊕ Fin b ⊕ Fin r.plugInt :=
    ⟨fun j => .inr (.inl j), fun _ _ h => Sum.inl_injective (Sum.inr_injective h)⟩
  have hdisj : Disjoint (Fl.map eL) (Fr.map eR) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hp
    obtain ⟨j, -, h⟩ := Finset.mem_map.1 hq
    cases h
  set T := (Fl.map eL).disjUnion (Fr.map eR) hdisj with hT
  let c : Fin a ⊕ Fin b ⊕ Fin r.plugInt → Fin a ⊕ Fin b ⊕ Fin r.plugInt
    | .inl i => θ (.inl i)
    | .inr (.inl j) => θ (.inr (.inl j))
    | .inr (.inr t) => .inr (.inr t)
  -- the points of `T` are the ports that are middle wires
  have hmemT : ∀ p ∈ T, ∃ x, (∀ w, x ≠ .inr (.inr w)) ∧ ∃ h : x ∈ r.midL,
      p = θ' x ∧ c p = r.mw (r.midφ x h) := by
    intro p hp
    rcases Finset.mem_disjUnion.1 hp with hp | hp
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_map.1 hp
      have h : (.inl i : Fin a ⊕ Fin b ⊕ Fin r.internal) ∈ r.midL := (mem_leftsOut _ _ i).1 hi
      exact ⟨.inl i, (fun w h => by cases h), h, rfl, r.thetaDec_of_mem hr h⟩
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hp
      have h : (.inr (.inl j) : Fin a ⊕ Fin b ⊕ Fin r.internal) ∈ r.midL :=
        (r.swapName_mem_midR _).1 ((mem_leftsOut _ _ j).1 hj)
      exact ⟨.inr (.inl j), (fun w h => by cases h), h, rfl, r.thetaDec_of_mem hr h⟩
  have hTport : ∀ x, (∀ w, x ≠ .inr (.inr w)) → (h : x ∈ r.midL) → θ' x ∈ T ∧ c (θ' x) = θ x := by
    intro x hx h
    rcases x with i | j | w
    · exact ⟨Finset.mem_disjUnion.2 (Or.inl (Finset.mem_map.2
        ⟨i, (mem_leftsOut _ _ i).2 h, rfl⟩)), rfl⟩
    · exact ⟨Finset.mem_disjUnion.2 (Or.inr (Finset.mem_map.2
        ⟨j, (mem_leftsOut _ _ j).2 ((r.swapName_mem_midR (.inr (.inl j))).2 h), rfl⟩)), rfl⟩
    · exact absurd rfl (hx w)
  have hcT : ∀ p ∈ T, (∀ j : Fin b, c p ≠ .inr (.inl j)) ∧ (∀ i, c p ≠ .inl i) := by
    intro p hp
    obtain ⟨x, -, h, -, hc⟩ := hmemT p hp
    rw [hc]
    exact ⟨fun j h => (by cases h), fun i h => (by cases h)⟩
  have hportT : ∀ p ∈ T, ∀ t, p ≠ .inr (.inr t) := by
    intro p hp t
    obtain ⟨x, hx, -, rfl, -⟩ := hmemT p hp
    rcases x with i | j | w
    · exact fun h => by cases h
    · exact fun h => by cases h
    · exact absurd rfl (hx w)
  have hinj : Set.InjOn c T := by
    intro p hp q hq he
    obtain ⟨x, -, hx, rfl, hcx⟩ := hmemT p hp
    obtain ⟨y, -, hy, rfl, hcy⟩ := hmemT q hq
    rw [hcx, hcy] at he
    rw [r.midφ_inj _ _ _ _ (r.mw_injective he)]
  -- the extra equations
  set N := r.net.bind fun x => var (θ x) with hN
  have hE : ((Fl.val.map (fun i => s(var (.inl i), var (θ (.inl i)))) +
      Fr.val.map (fun j => s(var (.inr (.inl j)), var (θ (.inr (.inl j)))))) :
        Net S (Fin a ⊕ Fin b ⊕ Fin r.plugInt)) =
      T.val.map (fun p => s(var (c p), var p)) := by
    rw [show T.val = (Fl.map eL).val + (Fr.map eR).val from rfl, Multiset.map_add,
      Finset.map_val, Finset.map_val, Multiset.map_map, Multiset.map_map]
    congr 1 <;> exact Multiset.map_congr rfl fun _ _ => Sym2.eq_swap
  have hnet := r.plug_decompose_net hr
  rw [hE] at hnet
  have hlin : Net.Linear (N + T.val.map (fun p => s(var (c p), var p))) :=
    hnet ▸ (Rule.plug_linear r.decompose.σ (r.decompose_linear hr).1
      (r.decompose_linear hr).2).net_linear
  have hvarsN : ∀ x ∈ r.net.vars, θ x ∈ N.vars := fun x hx => by
    rw [hN, Net.vars_bind_var]
    exact Multiset.mem_map_of_mem _ hx
  have hcN : ∀ p ∈ T, c p ∈ N.vars := by
    intro p hp
    obtain ⟨x, hx, h, rfl, hc⟩ := hmemT p hp
    rw [hc, ← r.thetaDec_of_mem hr h]
    refine hvarsN x (Multiset.count_pos.1 ?_)
    rcases x with i | j | w
    · rw [hr.left i]; omega
    · rw [hr.right j]; omega
    · exact absurd rfl (hx w)
  have hcp : ∀ p ∈ T, ∀ q ∈ T, c p ≠ q := by
    intro p hp q hq he
    obtain ⟨x, hx, -, rfl, -⟩ := hmemT q hq
    rcases x with i | j | w
    · exact (hcT p hp).2 i he
    · exact (hcT p hp).1 j he
    · exact absurd rfl (hx w)
  let f : Fin a ⊕ Fin b ⊕ Fin r.plugInt → Fin a ⊕ Fin b ⊕ Fin r.plugInt := fun z =>
    if h : ∃ p ∈ T, c p = z then h.choose else z
  have hfc : ∀ p ∈ T, f (c p) = p := by
    intro p hp
    have h : ∃ q ∈ T, c q = c p := ⟨p, hp, rfl⟩
    simp only [f, h, dite_true]
    exact hinj h.choose_spec.1 hp h.choose_spec.2
  have hfp : ∀ p ∈ T, f p = p := by
    intro p hp
    have h : ¬∃ q ∈ T, c q = p := fun ⟨q, hq, he⟩ => hcp q hq p hp he
    simp only [f, h, dite_false]
  have hfix : ∀ y ∈ N.vars, (∀ p ∈ T, y ≠ c p) → f y = y := by
    intro y _ hy
    have h : ¬∃ q ∈ T, c q = y := fun ⟨q, hq, he⟩ => hy q hq he.symm
    simp only [f, h, dite_false]
  have habs := Net.equiv_absorb c f T N hlin hinj hcN hcp hfc hfp hfix
  -- the renamed net
  have hfin : N.bind (fun y => var (f y)) = r.net.bind fun x => var (θ' x) := by
    rw [hN, Net.bind_bind]
    refine Net.bind_congr fun x hx => ?_
    simp only [Term.bind_var]
    congr 1
    by_cases hm : x ∈ r.midL
    · by_cases hx' : ∀ w, x ≠ .inr (.inr w)
      · obtain ⟨hT', hc⟩ := hTport x hx' hm
        rw [← hc, hfc _ hT']
      · simp only [not_forall, not_not] at hx'
        obtain ⟨w, rfl⟩ := hx'
        have e : θ (.inr (.inr w)) = θ' (.inr (.inr w)) := by
          rw [hθ, r.thetaDec_of_mem hr hm, hθ']
          simp only [Sum.map_inr, r.iotaDec_of_mem hr hm, mw]
        rw [e]
        refine hfix _ (e ▸ hvarsN _ hx) fun p hp he => ?_
        obtain ⟨y, hy, hy', -, hc⟩ := hmemT p hp
        rw [hc, ← e, hθ, r.thetaDec_of_mem hr hm] at he
        exact hy w (r.midφ_inj _ _ _ _ (r.mw_injective he)).symm
    · have e : θ x = θ' x := r.thetaDec_of_notMem hr hm
      rw [e]
      refine hfix _ (e ▸ hvarsN _ hx) fun p hp he => ?_
      obtain ⟨y, -, hy', -, hc⟩ := hmemT p hp
      rw [hc] at he
      rcases x with i | j | w
      · cases he
      · cases he
      · simp only [hθ', Sum.map_inr, mw, Sum.inr.injEq] at he
        have hv := congrArg Fin.val he
        simp only [Fin.val_castAdd] at hv
        have := (r.iotaDec_val_lt hr w).not.2 hm
        have := (r.midφ y hy').isLt
        omega
  exact (Equiv.of_eq hnet).trans (habs.trans (Equiv.of_eq hfin))

end Rule

end INet
