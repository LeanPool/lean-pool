/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# Products over the six permutations of three tensor legs

The symmetrized quantity in Section 5 uses every permutation of the three
tensor legs. Composing by a fixed permutation preserves this product. For
the exponent calculation, each original leg occurs twice in any fixed slot.
These are finite identities; they do not assume that an individual tensor
character is invariant under exchanging its legs.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields



open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation

/-- A permutation of the three tensor legs. -/
abbrev LegPermutation := Equiv.Perm (Fin 3)

namespace LegPermutation

/-- There are six orders of the three legs. -/
theorem card : Fintype.card LegPermutation = 6 := by
  norm_num [Fintype.card_perm, Nat.factorial]

/-- Right composition just reindexes a product over all six permutations. -/
theorem prod_mul_right {M : Type*} [CommMonoid M]
    (f : LegPermutation → M) (σ : LegPermutation) :
    (∏ π, f (π * σ)) = ∏ π, f π := by
  exact Equiv.prod_comp (Equiv.mulRight σ) f

/-- Left composition also just reindexes the six factors. -/
theorem prod_mul_left {M : Type*} [CommMonoid M]
    (f : LegPermutation → M) (σ : LegPermutation) :
    (∏ π, f (σ * π)) = ∏ π, f π := by
  exact Equiv.prod_comp (Equiv.mulLeft σ) f

/-- The same reindexing statement in explicit equivalence-composition notation. -/
theorem prod_trans_right {M : Type*} [CommMonoid M]
    (f : LegPermutation → M) (σ : LegPermutation) :
    (∏ π : LegPermutation, f (π.trans σ)) = ∏ π, f π := by
  exact prod_mul_left f σ

/-- A permutation-independent sum may likewise be reindexed on the right. -/
theorem sum_mul_right {A : Type*} [AddCommMonoid A]
    (f : LegPermutation → A) (σ : LegPermutation) :
    (∑ π, f (π * σ)) = ∑ π, f π := by
  exact Equiv.sum_comp (Equiv.mulRight σ) f

/-- Each original leg occurs twice in each fixed position. -/
theorem card_apply_fiber (i j : Fin 3) :
    Fintype.card {π : LegPermutation // π i = j} = 2 := by
  let _ : Fintype LegPermutation := fintypePerm
  fin_cases i <;> fin_cases j <;> decide

/-- The product of values attached to one slot contains each leg twice. -/
theorem prod_apply {M : Type*} [CommMonoid M] (f : Fin 3 → M) (i : Fin 3) :
    (∏ π : LegPermutation, f (π i)) = (∏ j, f j) ^ 2 := by
  rw [← Fintype.prod_fiberwise' (fun π : LegPermutation => π i) f]
  simp only [Finset.prod_const, Finset.card_univ, card_apply_fiber, Finset.prod_pow]

/-- The exponent attached to one slot contains each leg exponent twice. -/
theorem sum_apply {A : Type*} [AddCommMonoid A] (p : Fin 3 → A) (i : Fin 3) :
    (∑ π : LegPermutation, p (π i)) = 2 • ∑ j, p j := by
  rw [← Fintype.sum_fiberwise' (fun π : LegPermutation => π i) p]
  simp only [Finset.sum_const, Finset.card_univ, card_apply_fiber, Finset.sum_nsmul]

/-- Inverting the permutation preserves the symmetrized product. -/
theorem prod_symm {M : Type*} [CommMonoid M] (f : LegPermutation → M) :
    (∏ π : LegPermutation, f π.symm) = ∏ π, f π := by
  exact Equiv.prod_comp (Equiv.inv LegPermutation) f

/-- Inverting the permutation preserves a sum over all six orders. -/
theorem sum_symm {A : Type*} [AddCommMonoid A] (f : LegPermutation → A) :
    (∑ π : LegPermutation, f π.symm) = ∑ π, f π := by
  exact Equiv.sum_comp (Equiv.inv LegPermutation) f

/-- The twice-per-leg count is independent of the permutation convention. -/
theorem sum_symm_apply {A : Type*} [AddCommMonoid A]
    (p : Fin 3 → A) (i : Fin 3) :
    (∑ π : LegPermutation, p (π.symm i)) = 2 • ∑ j, p j := by
  rw [sum_symm (fun π => p (π i)), sum_apply]

/-- The sum of the six singleton-leg exponents is six times their mean. -/
theorem sum_exponents (p : Fin 3 → ℝ) (i : Fin 3) (t : ℝ)
    (h : (∑ j, p j) = 3 * t) :
    (∑ π : LegPermutation, p (π i)) = 6 * t := by
  rw [sum_apply, h]
  simp only [nsmul_eq_mul]
  ring

/-- The product of the valuations of all six transforms of an object. -/
def orbitProduct {X M : Type*} [CommMonoid M]
    (transform : LegPermutation → X → X) (value : X → M) (x : X) : M :=
  ∏ π : LegPermutation, value (transform π x)

/-- A further leg transformation preserves the product whenever transforms compose. -/
theorem orbitProduct_transform {X M : Type*} [CommMonoid M]
    (transform : LegPermutation → X → X) (value : X → M)
    (compose : ∀ π σ x, transform π (transform σ x) = transform (π * σ) x)
    (σ : LegPermutation) (x : X) :
    orbitProduct transform value (transform σ x) = orbitProduct transform value x := by
  simp only [orbitProduct, compose]
  exact prod_mul_right (fun π => value (transform π x)) σ

end LegPermutation

end MatrixMultiplication.AuxiliarySeparation

end MatrixMultiplicationAllFields
