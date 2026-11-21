/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Universality.Menus.Package
public import LeanPool.InteractionCombinators.Universality.Duplication.Duplication
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Order.SuccPred.Nat

/-!
# Lafont, "Interaction Combinators" (1997): a package as `π'` and its `dup` cells

Page 88, Section 2.6: "If `π` contains `n` occurrences of `δ`, it can be decomposed as follows
[picture], where `π'` is a reduced net with `3n + 1` free ports containing no `δ`." In the picture
the `n` `dup` cells sit on top; their principal ports and their `2n` auxiliary ports are plugged
into `π'`, and the root of `π` is the last free port of `π'`.

* `decomp k t` — cuts every `dup` cell out of the tree `t`. Cell `i` (`cells[i] = (x, l, r)`) is
  cut at the new name `x`, its principal port; `l` and `r` are its auxiliary subtrees with the inner
  `dup` cells cut out in the same way. `τ` is the root tree. So `π'` is the net of the `2n + 1`
  trees `τ, l₀, r₀, …`. New names are numbered from `k`.
* `decomp_equiv` — `s(u, t) ::ₘ Δ` is `Equiv` to `s(u, τ)`, the equations
  `s(var x, mkDup l r)` and `Δ`.
* `decomp_vars` — the names of `π'` are those of `t` plus the `n` cut names, each once.
* `package_decomp` — the decomposition of page 88 for a package, with all its properties.

Contents, in the order of the file:

1. Definitions: `Decomp`, the result of the decomposition; `decomp`, which cuts the `dup` cells
   out of a tree; `Decomp.cellEq`, `Decomp.net`, `Decomp.ports`, `Decomp.auxVars`,
   `Decomp.vars'`, the parts of a decomposition; `dupCount`, the number of `dup` cells of a tree;
   `DecompEquiv`, the statement of `decomp_equiv`.
2. Auxiliary lemmas on the names and cells of the decomposition: the equations of `decomp`,
   `Decomp.vars_net`, `decomp_vars`, `decomp_ports`, `cells_mkCon`, `cells_mkDup`, `cells_mkEra`,
   `decomp_length`, `decomp_dupFree`, `decomp_below`, `decomp_free`.
3. Auxiliary lemmas: the decomposition is the same graph. `Decomp.net_nil`, `Decomp.net_append`;
   for a binary cell `mk`, `equiv_cut_bin`, `linear_cut_bin`, `below_mk`; `equiv_cut_var`,
   `linear_cut_var`, `equiv_bin`; and `decomp_equiv`.
4. Main results: `package_decomp`, the decomposition of page 88 for a package;
   `package_decomp_exists`; `decomp_of_dupFree`, the case `n = 0`.
5. Examples: two computations of `decomp`, and a package for which the hypotheses of
   `package_decomp` hold.
-/

@[expose] public section

namespace INet.Comb

open Term

-- ============================================================================================
-- 1. Definitions
-- ============================================================================================

/-- A tree with its `dup` cells cut out (page 88): the root tree `τ`, and for each `dup` cell its
principal port `x` and its auxiliary trees `l`, `r`; and the next unused name `k`. -/
structure Decomp where
  /-- The root tree, without its `dup` cells. -/
  τ : Term sig ℕ
  /-- The `dup` cells: the name of the principal port, the left and right auxiliary trees. -/
  cells : List (ℕ × Term sig ℕ × Term sig ℕ)
  /-- The next unused name. -/
  k : ℕ

/-- Cut the `dup` cells out of a tree (page 88). Each `dup` cell is replaced by a new name `k`,
which becomes its principal port. The names `k + 1`, `k + 2` (and `k`, `k + 1` for a `con`) are
reserved for the proof and not used. -/
def decomp
    -- the first new name
    (k : ℕ) :
    -- a tree, to its decomposition
    Term sig ℕ → Decomp
  | .var x => ⟨var x, [], k⟩
  | .app .era _ => ⟨mkEra, [], k⟩
  | .app .con ts =>
    let ra := decomp (k + 2) (ts (0 : Fin 2))
    let rb := decomp ra.k (ts (1 : Fin 2))
    ⟨mkCon ra.τ rb.τ, ra.cells ++ rb.cells, rb.k⟩
  | .app .dup ts =>
    let ra := decomp (k + 3) (ts (0 : Fin 2))
    let rb := decomp ra.k (ts (1 : Fin 2))
    ⟨var k, (k, ra.τ, rb.τ) :: (ra.cells ++ rb.cells), rb.k⟩

namespace Decomp

/-- The equation of a `dup` cell: its principal port `x` against the cell. -/
def cellEq
    -- the cell: its principal port, its left and right auxiliary trees
    (c : ℕ × Term sig ℕ × Term sig ℕ) :
    Sym2 (Term sig ℕ) :=
  s(var c.1, mkDup c.2.1 c.2.2)

/-- The `dup` cells, as a net. -/
def net
    (D : Decomp) :
    CNet :=
  (D.cells.map cellEq : List _)

/-- The names at which the `dup` cells were cut: their principal ports. -/
def ports
    (D : Decomp) :
    Multiset ℕ :=
  (D.cells.map Prod.fst : List ℕ)

/-- The names of the auxiliary trees of the `dup` cells. -/
def auxVars
    (D : Decomp) :
    Multiset ℕ :=
  ((D.cells.map fun c => c.2.1.vars + c.2.2.vars).sum)

/-- The names of `π'`, the net of the trees `τ, l₀, r₀, …`, with multiplicity. -/
def vars'
    (D : Decomp) :
    Multiset ℕ :=
  D.τ.vars + D.auxVars

end Decomp

open Decomp

/-- Symbols of the combinators can be compared. -/
instance : DecidableEq sig.Sym := inferInstanceAs (DecidableEq Comb)

/-- The number of `dup` cells of a tree. -/
def dupCount
    (t : Term sig ℕ) :
    ℕ :=
  t.cells.count (show sig.Sym from Comb.dup)

/-- The statement of `decomp_equiv`, for one tree and one first new name. -/
def DecompEquiv
    -- the tree and the first new name
    (t : Term sig ℕ)
    (k : ℕ) :
    Prop :=
  -- for every tree `u` the tree `t` is plugged into, and every rest of the net `Δ`,
  ∀ (u : Term sig ℕ) (Δ : CNet),
    -- if the net is linear and its names are below `k`,
    Net.Linear (s(u, t) ::ₘ Δ) →
    Net.Below k (s(u, t) ::ₘ Δ) →
    -- it is the same graph as the root tree on `u`, the `dup` cells, and `Δ`
    Equiv (s(u, t) ::ₘ Δ) (s(u, (decomp k t).τ) ::ₘ ((decomp k t).net + Δ))

-- ============================================================================================
-- 2. Auxiliary lemmas: the names and the cells of the decomposition
-- ============================================================================================

/-- `decomp` on a name: nothing is cut. -/
theorem decomp_var
    (k x : ℕ) :
    decomp k (var x) = ⟨var x, [], k⟩ :=
  rfl

/-- `decomp` on an `era` cell: nothing is cut. -/
theorem decomp_mkEra
    (k : ℕ) :
    decomp k mkEra = ⟨mkEra, [], k⟩ :=
  rfl

/-- `decomp` on a `con` cell: the two subtrees are decomposed in turn, from `k + 2`. -/
theorem decomp_mkCon
    -- the first new name
    (k : ℕ)
    -- the two subtrees of the `con` cell
    (a b : Term sig ℕ) :
    decomp k (mkCon a b) =
      ⟨mkCon (decomp (k + 2) a).τ (decomp (decomp (k + 2) a).k b).τ,
        (decomp (k + 2) a).cells ++ (decomp (decomp (k + 2) a).k b).cells,
        (decomp (decomp (k + 2) a).k b).k⟩ :=
  rfl

/-- `decomp` on a `dup` cell: the cell is cut at `k`, and the two subtrees are decomposed in turn,
from `k + 3`. -/
theorem decomp_mkDup
    -- the first new name
    (k : ℕ)
    -- the two subtrees of the `dup` cell
    (a b : Term sig ℕ) :
    decomp k (mkDup a b) =
      ⟨var k, (k, (decomp (k + 3) a).τ, (decomp (decomp (k + 3) a).k b).τ) ::
        ((decomp (k + 3) a).cells ++ (decomp (decomp (k + 3) a).k b).cells),
        (decomp (decomp (k + 3) a).k b).k⟩ :=
  rfl

/-- The names of the net of `dup` cells: the principal ports and the names of the auxiliary
trees. -/
theorem Decomp.vars_net
    (D : Decomp) :
    D.net.vars = D.ports + D.auxVars := by
  obtain ⟨τ, cs, k⟩ := D
  simp only [net, ports, auxVars]
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [List.map_cons, ← Multiset.cons_coe, Net.vars_cons, List.sum_cons, ih, cellEq,
      eqVars_mk, vars_var, vars_mkDup]
    rw [Multiset.cons_coe]
    simp only [← Multiset.cons_coe, Multiset.singleton_add, Multiset.cons_add]
    abel_nf

/-- The multiset of a mapped concatenation is the sum of the two mapped lists. -/
private theorem coe_map_append
    -- the types and the function
    {α β : Type}
    (f : α → β)
    -- the two lists
    (l₁ l₂ : List α) :
    ((((l₁ ++ l₂).map f : List β)) : Multiset β) = (l₁.map f : List β) + (l₂.map f : List β) := by
  simp

/-- The names of `π'` are the names of `t` and the `n` cut names. -/
theorem decomp_vars
    -- the tree and the first new name
    (t : Term sig ℕ)
    (k : ℕ) :
    (decomp k t).vars' = t.vars + (decomp k t).ports := by
  induction t using Comb.induction generalizing k with
  | var x => simp [decomp_var, vars', auxVars, ports]
  | era => simp [decomp_mkEra, vars', auxVars, ports]
  | con a b iha ihb =>
    have ha := iha (k + 2)
    have hb := ihb (decomp (k + 2) a).k
    simp only [vars', auxVars, ports] at ha hb ⊢
    rw [decomp_mkCon]
    simp only [vars_mkCon, List.map_append, List.sum_append, ← Multiset.coe_add]
    generalize (decomp (k + 2) a) = A at ha hb ⊢
    generalize (decomp A.k b) = B at hb ⊢
    rw [show a.vars + b.vars + ((A.cells.map Prod.fst : List ℕ) + (B.cells.map Prod.fst : List ℕ) :
      Multiset ℕ) = (a.vars + (A.cells.map Prod.fst : List ℕ)) +
        (b.vars + (B.cells.map Prod.fst : List ℕ)) by abel, ← ha, ← hb]
    abel
  | dup a b iha ihb =>
    have ha := iha (k + 3)
    have hb := ihb (decomp (k + 3) a).k
    simp only [vars', auxVars, ports] at ha hb ⊢
    rw [decomp_mkDup]
    simp only [vars_mkDup, vars_var, List.map_cons, List.map_append, List.sum_cons,
      List.sum_append, ← Multiset.coe_add, ← Multiset.cons_coe]
    generalize (decomp (k + 3) a) = A at ha hb ⊢
    generalize (decomp A.k b) = B at hb ⊢
    rw [show a.vars + b.vars + (k ::ₘ ((A.cells.map Prod.fst : List ℕ) +
      (B.cells.map Prod.fst : List ℕ)) : Multiset ℕ) =
        {k} + (a.vars + (A.cells.map Prod.fst : List ℕ)) +
        (b.vars + (B.cells.map Prod.fst : List ℕ)) by
      rw [← Multiset.singleton_add]; abel, ← ha, ← hb]
    abel

/-- The cut names are distinct, and lie between `k` and the next unused name. -/
theorem decomp_ports
    -- the tree and the first new name
    (t : Term sig ℕ)
    (k : ℕ) :
    -- the cut names are distinct,
    (decomp k t).ports.Nodup ∧
      -- each lies between `k` and the next unused name,
      (∀ x ∈ (decomp k t).ports, k ≤ x ∧ x < (decomp k t).k) ∧
      -- and the next unused name is at least `k`
      k ≤ (decomp k t).k := by
  induction t using Comb.induction generalizing k with
  | var x => simp [decomp_var, ports]
  | era => simp [decomp_mkEra, ports]
  | con a b iha ihb =>
    obtain ⟨na, ra, ka⟩ := iha (k + 2)
    obtain ⟨nb, rb, kb⟩ := ihb (decomp (k + 2) a).k
    rw [decomp_mkCon]
    simp only [ports] at na ra nb rb ⊢
    simp only [List.map_append, ← Multiset.coe_add]
    generalize (decomp (k + 2) a) = A at na ra ka nb rb kb ⊢
    generalize (decomp A.k b) = B at nb rb kb ⊢
    refine ⟨Multiset.nodup_add.2 ⟨na, nb, Multiset.disjoint_left.2 fun {x} hx hx' => ?_⟩,
      fun x hx => ?_, by omega⟩
    · have := ra x hx; have := rb x hx'; omega
    · rcases Multiset.mem_add.1 hx with h | h
      · have := ra x h; omega
      · have := rb x h; omega
  | dup a b iha ihb =>
    obtain ⟨na, ra, ka⟩ := iha (k + 3)
    obtain ⟨nb, rb, kb⟩ := ihb (decomp (k + 3) a).k
    rw [decomp_mkDup]
    simp only [ports] at na ra nb rb ⊢
    simp only [List.map_cons, List.map_append, ← Multiset.coe_add, ← Multiset.cons_coe]
    generalize (decomp (k + 3) a) = A at na ra ka nb rb kb ⊢
    generalize (decomp A.k b) = B at nb rb kb ⊢
    refine ⟨Multiset.nodup_cons.2 ⟨fun h => ?_,
      Multiset.nodup_add.2 ⟨na, nb, Multiset.disjoint_left.2 fun {x} hx hx' => ?_⟩⟩,
      fun x hx => ?_, by omega⟩
    · rcases Multiset.mem_add.1 h with h | h
      · have := ra k h; omega
      · have := rb k h; omega
    · have := ra x hx; have := rb x hx'; omega
    · rcases Multiset.mem_cons.1 hx with rfl | hx
      · omega
      rcases Multiset.mem_add.1 hx with h | h
      · have := ra x h; omega
      · have := rb x h; omega

/-- The cells of a `con` cell: the `con` and the cells of its two subtrees. -/
theorem cells_mkCon
    (a b : Term sig ℕ) :
    (mkCon a b).cells = (show sig.Sym from Comb.con) ::ₘ (a.cells + b.cells) := by
  change _ ::ₘ ∑ i : Fin 2, _ = _
  rw [Fin.sum_univ_two]; rfl

/-- The cells of a `dup` cell: the `dup` and the cells of its two subtrees. -/
theorem cells_mkDup
    (a b : Term sig ℕ) :
    (mkDup a b).cells = (show sig.Sym from Comb.dup) ::ₘ (a.cells + b.cells) := by
  change _ ::ₘ ∑ i : Fin 2, _ = _
  rw [Fin.sum_univ_two]; rfl

/-- The cells of an `era` cell: the `era` alone. -/
theorem cells_mkEra :
    (mkEra : Term sig ℕ).cells = {(show sig.Sym from Comb.era)} := by
  change _ ::ₘ ∑ i : Fin 0, _ = _
  rw [Finset.univ_eq_empty, Finset.sum_empty]; rfl

/-- There is one cut name for each `dup` cell of the tree. -/
theorem decomp_length
    -- the tree and the first new name
    (t : Term sig ℕ)
    (k : ℕ) :
    (decomp k t).cells.length = dupCount t := by
  induction t using Comb.induction generalizing k with
  | var x => rfl
  | era => rw [decomp_mkEra, dupCount, cells_mkEra, Multiset.count_singleton]; rfl
  | con a b iha ihb =>
    rw [decomp_mkCon, List.length_append, iha, ihb, dupCount, dupCount, dupCount, cells_mkCon,
      Multiset.count_cons_of_ne (by decide), Multiset.count_add]
  | dup a b iha ihb =>
    rw [decomp_mkDup, List.length_cons, List.length_append, iha, ihb, dupCount, dupCount, dupCount,
      cells_mkDup, Multiset.count_cons_self, Multiset.count_add]

/-- No tree of `π'` contains a `dup` cell. -/
theorem decomp_dupFree
    -- the tree and the first new name
    (t : Term sig ℕ)
    (k : ℕ) :
    -- the root tree has no `dup` cell,
    DupFree (decomp k t).τ ∧
      -- nor has any auxiliary tree of a cut `dup` cell
      ∀ c ∈ (decomp k t).cells, DupFree c.2.1 ∧ DupFree c.2.2 := by
  induction t using Comb.induction generalizing k with
  | var x => simp [decomp_var, DupFree]
  | era => rw [decomp_mkEra]; exact ⟨trivial, by simp⟩
  | con a b iha ihb =>
    obtain ⟨ha, ha'⟩ := iha (k + 2)
    obtain ⟨hb, hb'⟩ := ihb (decomp (k + 2) a).k
    rw [decomp_mkCon]
    refine ⟨dupFree_mkCon.2 ⟨ha, hb⟩, fun c hc => ?_⟩
    rcases List.mem_append.1 hc with h | h
    · exact ha' c h
    · exact hb' c h
  | dup a b iha ihb =>
    obtain ⟨ha, ha'⟩ := iha (k + 3)
    obtain ⟨hb, hb'⟩ := ihb (decomp (k + 3) a).k
    rw [decomp_mkDup]
    refine ⟨trivial, fun c hc => ?_⟩
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ⟨ha, hb⟩
    rcases List.mem_append.1 hc with h | h
    · exact ha' c h
    · exact hb' c h

/-- The cut names and the names of the auxiliary trees are below the next unused name, if the
names of the tree are. -/
theorem decomp_below
    -- the tree and the first new name
    (t : Term sig ℕ)
    (k : ℕ)
    -- the tree `u` it is plugged into, and the rest of the net
    (u : Term sig ℕ)
    (Δ : CNet)
    -- the names of the net are below `k`
    (hb : Net.Below k (s(u, t) ::ₘ Δ)) :
    -- the names of the decomposed net are below the next unused name
    Net.Below (decomp k t).k (s(u, (decomp k t).τ) ::ₘ ((decomp k t).net + Δ)) := by
  obtain ⟨-, hr, hk⟩ := decomp_ports t k
  have hv := decomp_vars t k
  rw [Net.below_cons] at hb
  obtain ⟨hu, ht, hΔ⟩ := hb
  have h' : ∀ x ∈ (decomp k t).vars', x < (decomp k t).k := by
    rw [hv]
    intro x hx
    rcases Multiset.mem_add.1 hx with h | h
    · have := ht x h; omega
    · exact (hr x h).2
  intro x hx
  simp only [Net.vars_cons, eqVars_mk, Net.vars_add, vars_net, Multiset.mem_add] at hx
  rcases hx with (h | h) | ((h | h) | h)
  · have := hu x h; omega
  · exact h' x (Multiset.mem_add.2 (Or.inl h))
  · exact (hr x h).2
  · exact h' x (Multiset.mem_add.2 (Or.inr h))
  · have := hΔ x h; omega

/-- `π'` for a package `π` is a reduced net with `3n + 1` free ports (page 88). Its names are those
of `π`, each twice, and the `n` cut names, each once; so it is linear, and its free ports are its
`2n + 1` roots and the `n` cut names. The cut names must be new: the names of `π` below `k`. -/
theorem decomp_free
    -- the package: every name occurs twice
    (π : Term sig ℕ)
    (hπ : π.IsPackage)
    -- the first new name, above the names of the package
    (k : ℕ)
    (hb : π.Below k) :
    -- no name occurs more than twice in `π'`,
    (∀ y, (decomp k π).vars'.count y ≤ 2) ∧
      -- and the names that occur once are exactly the cut names
      (∀ y, (decomp k π).vars'.count y = 1 ↔ y ∈ (decomp k π).ports) := by
  obtain ⟨hnd, hr, -⟩ := decomp_ports π k
  have hv := decomp_vars π k
  have key : ∀ y, (decomp k π).vars'.count y =
      (if y ∈ π.vars then 2 else 0) + (if y ∈ (decomp k π).ports then 1 else 0) := by
    intro y
    rw [hv, Multiset.count_add, Multiset.count_eq_of_nodup hnd]
    congr 1
    split_ifs with h
    · exact hπ y h
    · exact Multiset.count_eq_zero.2 h
  have hdisj : ∀ y ∈ π.vars, y ∉ (decomp k π).ports := fun y h1 h => by
    have := (hr y h).1; have := hb y h1; omega
  refine ⟨fun y => ?_, fun y => ?_⟩
  · rw [key]
    by_cases h1 : y ∈ π.vars
    · simp [h1, hdisj y h1]
    · split_ifs <;> omega
  · rw [key]
    by_cases h1 : y ∈ π.vars
    · simp [h1, hdisj y h1]
    · simp [h1]

-- ============================================================================================
-- 3. Auxiliary lemmas: the decomposition is the same graph
-- ============================================================================================

/-- A decomposition without cells has the empty net of cells. -/
theorem Decomp.net_nil
    (τ : Term sig ℕ)
    (k : ℕ) :
    (Decomp.mk τ [] k).net = 0 :=
  rfl

/-- The net of cells of a concatenation is the sum of the two nets of cells; the root tree and the
next unused name play no part. -/
theorem Decomp.net_append
    -- two root trees and two next unused names
    (τ τ' : Term sig ℕ)
    (k k' : ℕ)
    -- the two lists of cells
    (cs cs' : List (ℕ × Term sig ℕ × Term sig ℕ)) :
    (Decomp.mk τ (cs ++ cs') k).net = (Decomp.mk τ cs k').net + (Decomp.mk τ' cs' k').net := by
  simp [Decomp.net]

section Cut

variable
    -- a binary cell: `mk a b` has the trees `a`, `b` on its auxiliary ports,
    (mk : Term sig ℕ → Term sig ℕ → Term sig ℕ)
    -- its names are those of its two trees,
    (hv : ∀ a b, (mk a b).vars = a.vars + b.vars)
    -- and substitution goes through it
    (hs : ∀ a b x t, (mk a b).subst x t = mk (a.subst x t) (b.subst x t))

include hv hs in
/-- Two trees on wires `y`, `z` plugged into the auxiliary ports of a binary cell are the same
graph as the cell with the trees on its auxiliary ports (page 70: a wire may be cut by a name). -/
theorem equiv_cut_bin
    -- the two wires
    (y z : ℕ)
    -- the trees on the wires, and the tree `u` the cell is plugged into
    (a b u : Term sig ℕ)
    -- the rest of the net
    (Δ : CNet)
    -- the net we start from is linear
    (hlin : Net.Linear (s(var y, a) ::ₘ s(var z, b) ::ₘ s(u, mk (var y) (var z)) ::ₘ Δ)) :
    -- it is the same graph as the cell with `a`, `b` on its auxiliary ports
    Equiv (s(var y, a) ::ₘ s(var z, b) ::ₘ s(u, mk (var y) (var z)) ::ₘ Δ)
      (s(u, mk a b) ::ₘ Δ) := by
  have hy := hlin y
  have hz := hlin z
  simp only [Net.vars_cons, eqVars_mk, vars_var, hv, Multiset.count_add,
    Multiset.count_singleton] at hy hz
  have hzy : z ≠ y := by
    rintro rfl
    simp only [ite_true] at hy
    omega
  simp only [hzy, hzy.symm, ite_true, ite_false] at hy hz
  have hyu : y ∉ u.vars := Multiset.count_eq_zero.1 (by omega)
  have hzu : z ∉ u.vars := Multiset.count_eq_zero.1 (by omega)
  have hza : z ∉ a.vars := Multiset.count_eq_zero.1 (by omega)
  have e1 : (s(var y, a) ::ₘ s(var z, b) ::ₘ s(u, mk (var y) (var z)) ::ₘ Δ : CNet) =
      s(var y, a) ::ₘ s(u, mk (var y) (var z)) ::ₘ (s(var z, b) ::ₘ Δ) := by
    rw [Multiset.cons_swap (s(var z, b))]
  have W1 := Wire.mk y a u (mk (var y) (var z)) (s(var z, b) ::ₘ Δ) (hlin.cast e1) (by simp [hv])
  rw [subst_of_notMem hyu, hs, subst_var_self,
    subst_of_notMem (show y ∉ (var z : Term sig ℕ).vars by
      simp only [vars_var, Multiset.mem_singleton]; exact hzy.symm)] at W1
  have e2 : (s(u, mk a (var z)) ::ₘ s(var z, b) ::ₘ Δ : CNet) =
      s(var z, b) ::ₘ s(u, mk a (var z)) ::ₘ Δ := Multiset.cons_swap _ _ _
  have W2 := Wire.mk z b u (mk a (var z)) Δ (W1.linear_right.cast e2) (by simp [hv])
  rw [subst_of_notMem hzu, hs, subst_var_self, subst_of_notMem hza] at W2
  exact (Equiv.of_eq e1).trans (W1.equiv.trans ((Equiv.of_eq e2).trans W2.equiv))

include hv in
/-- Cutting the two auxiliary ports of a binary cell at new names keeps the net linear. -/
theorem linear_cut_bin
    -- the two new names
    (y z : ℕ)
    -- the trees on the auxiliary ports, and the tree `u` the cell is plugged into
    (a b u : Term sig ℕ)
    -- the rest of the net
    (Δ : CNet)
    -- the net is linear
    (hlin : Net.Linear (s(u, mk a b) ::ₘ Δ))
    -- the two names are distinct and new in the net
    (hyz : y ≠ z)
    (hy : y ∉ Net.vars (s(u, mk a b) ::ₘ Δ))
    (hz : z ∉ Net.vars (s(u, mk a b) ::ₘ Δ)) :
    -- the net cut at `y` and `z` is linear
    Net.Linear (s(var y, a) ::ₘ s(var z, b) ::ₘ s(u, mk (var y) (var z)) ::ₘ Δ) := by
  refine hlin.add_fresh {y, z} (by simp [hyz]) ?_ ?_
  · intro x hx
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  · rw [Net.vars_cons, Net.vars_cons, Net.vars_cons, Net.vars_cons]
    simp only [eqVars_mk, vars_var, hv, Multiset.insert_eq_cons, ← Multiset.singleton_add]
    abel

include hv in
/-- The names of a binary cell are below `k` exactly when those of its two trees are. -/
theorem below_mk
    -- the bound and the two trees
    {k : ℕ}
    {a b : Term sig ℕ} :
    (mk a b).Below k ↔ a.Below k ∧ b.Below k := by
  simp [Term.Below, hv, or_imp, forall_and]

/-- A tree `t` on a wire `x` plugged into a leaf `x` is the same graph as `t` on that leaf. -/
theorem equiv_cut_var
    -- the wire
    (x : ℕ)
    -- the tree on the wire, and the tree `u` the leaf is plugged into
    (t u : Term sig ℕ)
    -- the rest of the net
    (Δ : CNet)
    -- the net we start from is linear
    (hlin : Net.Linear (s(var x, t) ::ₘ s(u, var x) ::ₘ Δ)) :
    -- it is the same graph as `t` plugged into `u`
    Equiv (s(var x, t) ::ₘ s(u, var x) ::ₘ Δ) (s(u, t) ::ₘ Δ) := by
  have hx := hlin x
  simp only [Net.vars_cons, eqVars_mk, vars_var, Multiset.count_add,
    Multiset.count_singleton_self] at hx
  have hxu : x ∉ u.vars := Multiset.count_eq_zero.1 (by omega)
  have W := Wire.mk x t u (var x) Δ hlin (by simp)
  rw [subst_of_notMem hxu, subst_var_self] at W
  exact W.equiv

/-- Cutting a tree at a new name keeps the net linear. -/
theorem linear_cut_var
    -- the new name
    (x : ℕ)
    -- the tree, and the tree `u` it is plugged into
    (t u : Term sig ℕ)
    -- the rest of the net
    (Δ : CNet)
    -- the net is linear, and `x` is new in it
    (hlin : Net.Linear (s(u, t) ::ₘ Δ))
    (hx : x ∉ Net.vars (s(u, t) ::ₘ Δ)) :
    -- the net cut at `x` is linear
    Net.Linear (s(var x, t) ::ₘ s(u, var x) ::ₘ Δ) := by
  refine hlin.add_fresh {x} (by simp) (by simpa using hx) ?_
  simp only [Net.vars_cons, eqVars_mk, vars_var]
  abel

include hv hs in
/-- The binary case of `decomp_equiv`: cut the auxiliary ports at `j`, `j + 1`, decompose the two
subtrees, and plug them back. -/
theorem equiv_bin
    -- the first new name
    (j : ℕ)
    -- the two subtrees of the cell, and the tree `u` the cell is plugged into
    (a b u : Term sig ℕ)
    -- the rest of the net
    (Δ : CNet)
    -- `decomp_equiv` for the two subtrees, with their first new names
    (iha : DecompEquiv a (j + 2))
    (ihb : DecompEquiv b (decomp (j + 2) a).k)
    -- the net is linear, and its names are below `j`
    (hlin : Net.Linear (s(u, mk a b) ::ₘ Δ))
    (hb : Net.Below j (s(u, mk a b) ::ₘ Δ)) :
    -- the net is the same graph as the cell on the two root trees, the two nets of `dup` cells,
    -- and `Δ`
    Equiv (s(u, mk a b) ::ₘ Δ)
      (s(u, mk (decomp (j + 2) a).τ (decomp (decomp (j + 2) a).k b).τ) ::ₘ
        ((decomp (j + 2) a).net + (decomp (decomp (j + 2) a).k b).net + Δ)) := by
  have hb2 : Net.Below (j + 2) (s(var (j + 1), b) ::ₘ s(u, mk (var j) (var (j + 1))) ::ₘ Δ) := by
    simp only [Net.below_cons, below_mk mk hv] at hb ⊢
    obtain ⟨hu, ⟨ha, hb⟩, hΔ⟩ := hb
    exact ⟨by simp, hb.mono (by omega), hu.mono (by omega), ⟨by simp, by simp⟩, hΔ.mono (by omega)⟩
  have ha2 : (a : Term sig ℕ).Below (j + 2) := by
    simp only [Net.below_cons, below_mk mk hv] at hb
    exact hb.2.1.1.mono (by omega)
  have L1 := linear_cut_bin mk hv j (j + 1) a b u Δ hlin (by omega) (hb.notMem le_rfl)
    (hb.notMem (by omega))
  have E1 := (equiv_cut_bin mk hv hs j (j + 1) a b u Δ L1).symm
  have hb1 : Net.Below (j + 2) (s(var j, a) ::ₘ
      (s(var (j + 1), b) ::ₘ s(u, mk (var j) (var (j + 1))) ::ₘ Δ)) := by
    rw [Net.below_cons]
    exact ⟨by simp, ha2, hb2⟩
  have E2 := iha (var j) _ L1 hb1
  set A := decomp (j + 2) a
  set B := decomp A.k b
  have hb3 := decomp_below a (j + 2) (var j) _ hb1
  have e2 : s(var j, A.τ) ::ₘ
      (A.net + (s(var (j + 1), b) ::ₘ s(u, mk (var j) (var (j + 1))) ::ₘ Δ)) =
      s(var (j + 1), b) ::ₘ (s(var j, A.τ) ::ₘ s(u, mk (var j) (var (j + 1))) ::ₘ (A.net + Δ)) := by
    ms
  have L2 := ((E1.trans E2).linear hlin).cast e2
  have E3 := ihb (var (j + 1)) _ L2 (hb3.cast e2)
  have e3 : s(var (j + 1), B.τ) ::ₘ
      (B.net + (s(var j, A.τ) ::ₘ s(u, mk (var j) (var (j + 1))) ::ₘ (A.net + Δ))) =
      s(var j, A.τ) ::ₘ s(var (j + 1), B.τ) ::ₘ s(u, mk (var j) (var (j + 1))) ::ₘ
        (A.net + B.net + Δ) := by
    ms
  have L3 := (E3.linear L2).cast e3
  exact E1.trans (E2.trans ((Equiv.of_eq e2).trans (E3.trans ((Equiv.of_eq e3).trans
    (equiv_cut_bin mk hv hs j (j + 1) A.τ B.τ u _ L3)))))

end Cut

/-- The decomposition of page 88 is the same graph as the tree: `s(u, t) ::ₘ Δ` is `Equiv` to the
root tree `τ` on `u`, each `dup` cell `s(var x, mkDup l r)`, and `Δ`. The net must be linear and
its names below `k`, the first new name. No hypothesis on `t` is needed. -/
theorem decomp_equiv
    -- the tree and the first new name
    (t : Term sig ℕ)
    (k : ℕ) :
    -- in every linear context with names below `k`, the decomposition is the same graph
    DecompEquiv t k := by
  induction t using Comb.induction generalizing k with
  | var x =>
    intro u Δ _ _
    exact Equiv.of_eq (by simp [decomp_var, Decomp.net])
  | era =>
    intro u Δ _ _
    exact Equiv.of_eq (by simp [decomp_mkEra, Decomp.net])
  | con a b iha ihb =>
    intro u Δ hlin hb
    have h := equiv_bin mkCon vars_mkCon subst_mkCon k a b u Δ (iha _) (ihb _) hlin hb
    rw [decomp_mkCon, Decomp.net_append _ (decomp (decomp (k + 2) a).k b).τ _ _ _ _]
    exact h
  | dup a b iha ihb =>
    intro u Δ hlin hb
    have L := linear_cut_var k (mkDup a b) u Δ hlin (hb.notMem le_rfl)
    have E1 := (equiv_cut_var k (mkDup a b) u Δ L).symm
    have hb' : Net.Below (k + 1) (s(var k, mkDup a b) ::ₘ (s(u, var k) ::ₘ Δ)) := by
      simp only [Net.below_cons, below_mkDup] at hb ⊢
      obtain ⟨hu, ⟨ha, hb⟩, hΔ⟩ := hb
      exact ⟨by simp, ⟨ha.mono (by omega), hb.mono (by omega)⟩, hu.mono (by omega), by simp,
        hΔ.mono (by omega)⟩
    have E2 := equiv_bin mkDup vars_mkDup subst_mkDup (k + 1) a b (var k) _ (iha _) (ihb _) L hb'
    refine E1.trans (E2.trans (Equiv.of_eq ?_))
    rw [decomp_mkDup]
    simp only [Decomp.net, List.map_cons, List.map_append, ← Multiset.coe_add,
      ← Multiset.cons_coe, cellEq]
    ms

-- ============================================================================================
-- 4. Main results: the decomposition of a package
-- ============================================================================================

/-- Lafont's decomposition of a package, page 88: "If `π` contains `n` occurrences of `δ`, it can
be decomposed as follows, where `π'` is a reduced net with `3n + 1` free ports containing no `δ`."

For a package `π` plugged into `u`, with any context `Δ`, and new names numbered from a bound `k`
on the names of the net, `decomp k π` gives the root tree `τ` and, for each `dup` cell `i < n`, its
principal port `x i` and auxiliary trees `l i`, `r i` (`cells[i] = (x i, l i, r i)`):
* `s(u, π) ::ₘ Δ` is `Equiv` to `s(u, τ)`, the `n` equations `s(var (x i), mkDup (l i) (r i))`,
  and `Δ`;
* `n` is the number of `dup` cells of `π`;
* `τ` and every `l i`, `r i` are without `dup`;
* `π'`, the net of the trees `τ, l i, r i`, is linear, and its free names are exactly the `n`
  distinct names `x i`, which are new in the net. -/
theorem package_decomp
    -- the package: every name occurs twice
    (π : Term sig ℕ)
    (hπ : π.IsPackage)
    -- the tree `u` the package is plugged into, and the rest of the net
    (u : Term sig ℕ)
    (Δ : CNet)
    -- the first new name
    (k : ℕ)
    -- the net is linear, and its names are below `k`
    (hlin : Net.Linear (s(u, π) ::ₘ Δ))
    (hb : Net.Below k (s(u, π) ::ₘ Δ)) :
    -- the net is the same graph as the root tree on `u`, the `dup` cells, and `Δ`;
    Equiv (s(u, π) ::ₘ Δ) (s(u, (decomp k π).τ) ::ₘ ((decomp k π).net + Δ)) ∧
      -- there is one cut cell for each `dup` cell of `π`;
      (decomp k π).cells.length = dupCount π ∧
      -- the root tree has no `dup` cell,
      DupFree (decomp k π).τ ∧
      -- nor has any auxiliary tree of a cut cell;
      (∀ c ∈ (decomp k π).cells, DupFree c.2.1 ∧ DupFree c.2.2) ∧
      -- no name occurs more than twice in `π'`,
      (∀ y, (decomp k π).vars'.count y ≤ 2) ∧
      -- the names that occur once in `π'` are exactly the cut names,
      (∀ y, (decomp k π).vars'.count y = 1 ↔ y ∈ (decomp k π).ports) ∧
      -- which are distinct,
      (decomp k π).ports.Nodup ∧
      -- and new in the net
      (∀ x ∈ (decomp k π).ports, x ∉ Net.vars (s(u, π) ::ₘ Δ)) := by
  have hπb : π.Below k := (Net.below_cons.1 hb).2.1
  obtain ⟨hd, hd'⟩ := decomp_dupFree π k
  obtain ⟨h2, h1⟩ := decomp_free π hπ k hπb
  obtain ⟨hnd, hr, -⟩ := decomp_ports π k
  exact ⟨decomp_equiv π k u Δ hlin hb, decomp_length π k, hd, hd', h2, h1, hnd,
    fun x hx => hb.notMem (hr x hx).1⟩

/-- The decomposition exists for every package in every linear context: new names are taken
above the names of the net. -/
theorem package_decomp_exists
    -- the package: every name occurs twice
    (π : Term sig ℕ)
    (hπ : π.IsPackage)
    -- the tree `u` the package is plugged into, and the rest of the net
    (u : Term sig ℕ)
    (Δ : CNet)
    -- the net is linear
    (hlin : Net.Linear (s(u, π) ::ₘ Δ)) :
    -- there is a decomposition `D` such that
    ∃ D : Decomp,
      -- the net is the same graph as the root tree on `u`, the `dup` cells, and `Δ`;
      Equiv (s(u, π) ::ₘ Δ) (s(u, D.τ) ::ₘ (D.net + Δ)) ∧
      -- there is one cut cell for each `dup` cell of `π`;
      D.cells.length = dupCount π ∧
      -- the root tree and the auxiliary trees of the cut cells have no `dup` cell;
      DupFree D.τ ∧
      (∀ c ∈ D.cells, DupFree c.2.1 ∧ DupFree c.2.2) ∧
      -- no name occurs more than twice in `π'`, and those that occur once are the cut names,
      (∀ y, D.vars'.count y ≤ 2) ∧
      (∀ y, D.vars'.count y = 1 ↔ y ∈ D.ports) ∧
      -- which are distinct and new in the net
      D.ports.Nodup ∧
      (∀ x ∈ D.ports, x ∉ Net.vars (s(u, π) ::ₘ Δ)) := by
  obtain ⟨k, hk⟩ : ∃ k, Net.Below k (s(u, π) ::ₘ Δ) :=
    ⟨(Net.vars (s(u, π) ::ₘ Δ)).sup + 1, fun x hx => by have := Multiset.le_sup hx; omega⟩
  exact ⟨decomp k π, package_decomp π hπ u Δ k hlin hk⟩

/-- Without `dup` (`n = 0`) the decomposition cuts nothing: `τ = π` and there is no cell
(page 88, the case `n = 0`). -/
theorem decomp_of_dupFree
    -- a tree without `dup`
    (t : Term sig ℕ)
    (ht : DupFree t)
    -- the first new name
    (k : ℕ) :
    -- the root tree is the tree, and no cell is cut
    (decomp k t).τ = t ∧
      (decomp k t).cells = [] := by
  induction t using Comb.induction generalizing k with
  | var x => exact ⟨rfl, rfl⟩
  | era => exact ⟨rfl, rfl⟩
  | con a b iha ihb =>
    obtain ⟨ha, hb⟩ := dupFree_mkCon.1 ht
    rw [decomp_mkCon, (iha ha _).1, (ihb hb _).1, (iha ha _).2, (ihb hb _).2]
    exact ⟨rfl, rfl⟩
  | dup a b => exact absurd ht dupFree_mkDup

-- ============================================================================================
-- 5. Examples: the hypotheses can hold
-- ============================================================================================

/-- A package without `dup` (`n = 0`): `π' = π`, there is no cell. -/
example :
    decomp 1 (mkCon (var 0) (var 0) : Term sig ℕ) = ⟨mkCon (var 0) (var 0), [], 3⟩ :=
  rfl

/-- `dup(dup(0, 1), con(0, 1))` on the free port `2`, new names from `3`: two nested `dup` cells,
cut at `3` and `6`. The left auxiliary tree of the outer cell is the name `6` of the inner one. -/
example :
    decomp 3 (mkDup (mkDup (var 0) (var 1)) (mkCon (var 0) (var 1)) : Term sig ℕ) =
      ⟨var 3, [(3, var 6, mkCon (var 0) (var 1)), (6, var 0, var 1)], 11⟩ :=
  rfl

/-- The same package: the hypotheses of `package_decomp` hold, and the decomposition is the net of
the picture of page 88, with `τ = 3`, `l₀ = 6`, `r₀ = con(0, 1)`, `l₁ = 0`, `r₁ = 1`. -/
example :
    Equiv ({s(var 2, mkDup (mkDup (var 0) (var 1)) (mkCon (var 0) (var 1)))} : CNet)
      {s(var 2, var 3), s(var 3, mkDup (var 6) (mkCon (var 0) (var 1))),
        s(var 6, mkDup (var 0) (var 1))} := by
  have hπ : (mkDup (mkDup (var 0) (var 1)) (mkCon (var 0) (var 1)) : Term sig ℕ).IsPackage :=
    by
      intro x hx
      simp only [vars_mkDup, vars_mkCon, vars_var, Multiset.mem_add, Multiset.mem_singleton] at hx
      simp only [vars_mkDup, vars_mkCon, vars_var, Multiset.count_add, Multiset.count_singleton]
      rcases hx with ((rfl | rfl) | (rfl | rfl)) <;> simp
  have h := (package_decomp _ hπ (var 2) 0 3
    (by
      intro y
      simp only [Net.vars_cons, Net.vars_zero, eqVars_mk, vars_mkDup, vars_mkCon, vars_var,
        add_zero, Multiset.count_add, Multiset.count_singleton]
      split_ifs <;> omega)
    (by simp [Net.Below])).1
  have e : decomp 3 (mkDup (mkDup (var 0) (var 1)) (mkCon (var 0) (var 1)) : Term sig ℕ) =
      ⟨var 3, [(3, var 6, mkCon (var 0) (var 1)), (6, var 0, var 1)], 11⟩ := rfl
  rw [e] at h
  simp only [Decomp.net, cellEq, List.map_cons, List.map_nil, add_zero] at h
  exact h

end INet.Comb
