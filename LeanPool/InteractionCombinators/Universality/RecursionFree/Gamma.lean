/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Universality.RecursionFree.PortTreeC
public import LeanPool.InteractionCombinators.Universality.Multiplexors.TranspositorPerm
public import LeanPool.InteractionCombinators.Universality.Menus.Package
public import LeanPool.InteractionCombinators.Text.TranslationExists
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action

/-!
# The package `Γ_{i,j}` of Fig. 6 (page 86)

Lafont 1997, Section 2.4, Fig. 6, journal page 86 (PDF page 18). The cell `[α_i]` carries a menu
`Γ_i = Γ_{1,i} & … & Γ_{m,i}`. Each package `Γ_{i,j}` is the dual multiplexor `M*_{n_i+1}`, whose
root is the free port; its first `n_i` leaves go to the `n_i` ports of `[φ_{i,j}]` on the side of
`α_i`; the `k` middle ports of `[φ_{i,j}]` go into the leaves of the transpositor `T_{σ_{i,j}}`,
whose root goes to the last leaf of `M*_{n_i+1}`. Here `[φ]` is `φ` with every cell replaced by
its translation (page 87).

A side `φ : Rule S a k` in expanded form (`Rule.Expanded`) and linear is one tree per port
(`Rule.Expanded.existsUnique_root`), so `Γ_{i,j}` is a single tree.

Contents, in the order of the file:

1. Definitions: the package.
   * `gammaName`, `gammaTree` — the tree rooted at the port `p` of `φ`, computed by
     `Rule.portTreeC` (`PortTreeC.lean`), its internal wires renamed from `k₀`: the internal wire
     `w` of `φ` is named `k₀ + w`.
   * `gammaSizes`, `gammaSize`, `gammaPort` — the trees of `[φ]`: the internal wires of the
     translations take consecutive blocks above `k₀ + φ.internal`.
   * `gamma Φ φ σ hσ k₀` — the package `Γ_{i,j}`.
2. Auxiliary lemmas: the names of the trees.
   * `gammaTree_eq_portTree` — on an expanded linear side, `gammaTree` is `Rule.portTree` of
     `PortTree.lean`, renamed.
   * `map_add_univ`, `sum_vars_gammaTree` — the names of the trees of `φ`, renamed, are both ends
     of each name of `[k₀, k₀ + φ.internal)`.
3. Main results: the names of the package.
   * `vars_gamma` — the names of `Γ_{i,j}` are both ends of each name of `[k₀, k₀ + gammaSize)`.
   * `mem_vars_gamma` — they lie in that interval.
   * `gamma_isPackage` — `Γ_{i,j}` is a package.
-/

@[expose] public section

namespace INet.Comb

open Term Translation

variable {S : Signature} {a k : ℕ}

-- ============================================================================================
-- 1. Definitions: the package
-- ============================================================================================

/-- The names of `Γ_{i,j}` given to the names of `φ` (Fig. 6, page 86): the internal wire `w` is
named `k₀ + w`. A port of `φ` does not occur in its trees when `φ` is expanded; it is sent to
`k₀`. -/
def gammaName
    -- the base of the names
    (k₀ : ℕ)
    -- the number of internal wires of `φ`
    {n : ℕ} :
    Fin a ⊕ Fin k ⊕ Fin n → ℕ :=
  Sum.elim (fun _ => k₀) (Sum.elim (fun _ => k₀) fun w => k₀ + w)

/-- The tree of `φ` at the port `p`, its internal wires named from `k₀` (Fig. 6, page 86). It is
computed by the twin `Rule.portTreeC`, which is `Rule.portTree` on an expanded linear side
(`gammaTree_eq_portTree`). -/
def gammaTree
    -- the side
    (φ : Rule S a k)
    -- the base of the names
    (k₀ : ℕ)
    -- the port, on the side of the cell or in the middle
    (p : Fin a ⊕ Fin k) :
    Term S ℕ :=
  (φ.portTreeC p).bind fun x => .var (gammaName k₀ x)

/-- The number of internal wires of the translation of each tree of `φ`, the ports numbered
`0, …, a + k - 1` by `finSumFinEquiv` (page 87). -/
def gammaSizes
    -- the translation of the cells
    (Φ : Translation S sig)
    -- the side and the base of the names
    (φ : Rule S a k)
    (k₀ : ℕ) :
    Fin (a + k) → ℕ :=
  fun q => Φ.size (gammaTree φ k₀ (finSumFinEquiv.symm q))

/-- The number of names of `Γ_{i,j}` (Fig. 6, page 86): the internal wires of `φ`, then those of
the translations of its trees. -/
def gammaSize
    -- the translation of the cells
    (Φ : Translation S sig)
    -- the side and the base of the names
    (φ : Rule S a k)
    (k₀ : ℕ) :
    ℕ :=
  φ.internal + ∑ q, gammaSizes Φ φ k₀ q

/-- The tree of `[φ]` at the port `p` (pages 86–87): the translation of the tree of `φ` at `p`,
its new wires numbered from the block of `p` above `k₀ + φ.internal`. -/
def gammaPort
    -- the translation of the cells
    (Φ : Translation S sig)
    -- the side and the base of the names
    (φ : Rule S a k)
    (k₀ : ℕ)
    -- the port
    (p : Fin a ⊕ Fin k) :
    Term sig ℕ :=
  Φ.trTerm (k₀ + φ.internal + off (gammaSizes Φ φ k₀) (finSumFinEquiv p)) (gammaTree φ k₀ p)

/-- **The package `Γ_{i,j}`** (Lafont 1997, Fig. 6, page 86): the dual multiplexor `M*_{a+1}`,
whose first `a` leaves are the trees of `[φ]` at the ports of the first cell and whose last leaf
is the transpositor `T_σ` applied to the trees of `[φ]` at the `k` middle ports. -/
def gamma
    -- the translation of the cells
    (Φ : Translation S sig)
    -- the side, and the involution `σ` of its middle ports
    (φ : Rule S a k)
    (σ : Equiv.Perm (Fin k))
    (hσ : Function.Involutive σ)
    -- the base of the names
    (k₀ : ℕ) :
    Term sig ℕ :=
  muxStar (List.ofFn (fun i => gammaPort Φ φ k₀ (.inl i)) ++
    [transpositorPerm σ hσ (fun j => gammaPort Φ φ k₀ (.inr j))])

-- ============================================================================================
-- 2. Auxiliary lemmas: the names of the trees
-- ============================================================================================

/-- On a linear side in expanded form, `gammaTree` is the tree `Rule.portTree` renamed from `k₀`
(Fig. 6, page 86). -/
theorem gammaTree_eq_portTree
    -- the side: in expanded form, and linear
    {φ : Rule S a k}
    (he : φ.Expanded)
    (hl : φ.Linear)
    -- the base of the names and the port
    (k₀ : ℕ)
    (p : Fin a ⊕ Fin k) :
    gammaTree φ k₀ p = (φ.portTree p).bind fun x => .var (gammaName k₀ x) := by
  rw [gammaTree, Rule.portTreeC_eq_portTree he hl]

/-- The names `k₀ + w` of the internal wires of `φ` form the interval `[k₀, k₀ + n)`. -/
theorem map_add_univ
    -- the base and the number of names
    (k₀ n : ℕ) :
    (Finset.univ.val.map fun w : Fin n => k₀ + (w : ℕ)) = Multiset.Ico k₀ (k₀ + n) := by
  refine Multiset.Nodup.ext (Multiset.Nodup.map (fun x y h => Fin.ext (by simpa using h))
    Finset.univ.nodup) Multiset.nodup_Ico |>.2 fun x => ?_
  simp only [Multiset.mem_map, Finset.mem_univ_val, true_and, Multiset.mem_Ico]
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨by omega, by have := w.isLt; omega⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨x - k₀, by omega⟩, by simp; omega⟩

/-- The names of the trees of an expanded linear side, renamed from `k₀`, are both ends of each
name of `[k₀, k₀ + φ.internal)` (Fig. 6, page 86). -/
theorem sum_vars_gammaTree
    -- the side: in expanded form, and linear
    {φ : Rule S a k}
    (he : φ.Expanded)
    (hl : φ.Linear)
    -- the base of the names
    (k₀ : ℕ) :
    -- each name of the interval occurs twice among the names of the trees
    ∑ p, (gammaTree φ k₀ p).vars = 2 • Multiset.Ico k₀ (k₀ + φ.internal) := by
  have h : ∀ p, (gammaTree φ k₀ p).vars = (φ.portTree p).vars.map (gammaName k₀) := fun p => by
    rw [gammaTree_eq_portTree he hl, Term.vars_bind]
    simp [Multiset.bind_singleton]
  simp only [h]
  have hm : ∑ p, (φ.portTree p).vars.map (gammaName k₀) =
      (∑ p, (φ.portTree p).vars).map (gammaName k₀) :=
    (map_sum (Multiset.mapAddMonoidHom (gammaName k₀)) _ _).symm
  rw [hm, he.sum_vars_portTree hl, Multiset.map_nsmul, Multiset.map_map, ← map_add_univ]
  rfl

-- ============================================================================================
-- 3. Main results: the names of the package
-- ============================================================================================

/-- **The names of `Γ_{i,j}`** (Fig. 6, page 86): for a linear side in expanded form, they are both
ends of each name of `[k₀, k₀ + gammaSize)`. -/
theorem vars_gamma
    -- the translation of the cells
    (Φ : Translation S sig)
    -- the side: in expanded form, and linear
    {φ : Rule S a k}
    (he : φ.Expanded)
    (hl : φ.Linear)
    -- the involution `σ` of its middle ports
    (σ : Equiv.Perm (Fin k))
    (hσ : Function.Involutive σ)
    -- the base of the names
    (k₀ : ℕ) :
    -- each name of the interval occurs twice in the package, and no other name occurs
    (gamma Φ φ σ hσ k₀).vars = 2 • Multiset.Ico k₀ (k₀ + gammaSize Φ φ k₀) := by
  set s := gammaSizes Φ φ k₀
  set B := k₀ + φ.internal
  have hport : ∀ p, (gammaPort Φ φ k₀ p).vars = (gammaTree φ k₀ p).vars +
      2 • Multiset.Ico (B + off s (finSumFinEquiv p))
        (B + off s (finSumFinEquiv p) + s (finSumFinEquiv p)) := fun p => by
    rw [gammaPort, vars_trTerm]
    simp [s, gammaSizes, B]
  have hsum : (gamma Φ φ σ hσ k₀).vars = ∑ p, (gammaPort Φ φ k₀ p).vars := by
    rw [gamma, vars_muxStar, List.map_append, List.sum_append, List.map_ofFn, List.sum_ofFn,
      Fintype.sum_sum_type]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      vars_transpositorPerm]
    rfl
  rw [hsum]
  simp only [hport]
  rw [Finset.sum_add_distrib, sum_vars_gammaTree he hl,
    Equiv.sum_comp finSumFinEquiv (fun q => 2 • Multiset.Ico (B + off s q) (B + off s q + s q)),
    ← Finset.smul_sum, sum_Ico_off, ← nsmul_add, gammaSize,
    Multiset.Ico_add_Ico_eq_Ico (by omega) (by omega), add_assoc]

/-- The names of `Γ_{i,j}` lie in `[k₀, k₀ + gammaSize)` (Fig. 6, page 86), for a linear side in
expanded form. -/
theorem mem_vars_gamma
    -- the translation of the cells
    (Φ : Translation S sig)
    -- the side: in expanded form, and linear
    {φ : Rule S a k}
    (he : φ.Expanded)
    (hl : φ.Linear)
    -- the involution `σ` of its middle ports
    (σ : Equiv.Perm (Fin k))
    (hσ : Function.Involutive σ)
    -- the base of the names
    (k₀ : ℕ)
    -- a name of the package
    {x : ℕ}
    (hx : x ∈ (gamma Φ φ σ hσ k₀).vars) :
    -- it lies in `[k₀, k₀ + gammaSize)`
    k₀ ≤ x ∧ x < k₀ + gammaSize Φ φ k₀ := by
  rw [vars_gamma Φ he hl] at hx
  exact Multiset.mem_Ico.1 (Multiset.mem_of_mem_nsmul hx)

/-- **`Γ_{i,j}` is a package** (Fig. 6, page 86; packages, page 80): for a linear side in expanded
form, every name of `gamma Φ φ σ hσ k₀` occurs exactly twice. -/
theorem gamma_isPackage
    -- the translation of the cells
    (Φ : Translation S sig)
    -- the side: in expanded form, and linear
    {φ : Rule S a k}
    (he : φ.Expanded)
    (hl : φ.Linear)
    -- the involution `σ` of its middle ports
    (σ : Equiv.Perm (Fin k))
    (hσ : Function.Involutive σ)
    -- the base of the names
    (k₀ : ℕ) :
    -- every name of the package occurs exactly twice
    (gamma Φ φ σ hσ k₀).IsPackage := by
  intro x hx
  rw [vars_gamma Φ he hl] at hx ⊢
  rw [Multiset.count_nsmul, Multiset.count_eq_one_of_mem Multiset.nodup_Ico
    (Multiset.mem_of_mem_nsmul hx)]

end INet.Comb
