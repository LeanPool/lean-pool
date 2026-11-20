/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

module

public import LeanPool.NoncommutativeAMGM.Boolean

/-!
# Coefficient extraction by slice quadrature

This proves the linear algebra part of Lemma 3.1 for actual Boolean polynomials.
It does not yet identify the extracted matrix coefficient with `W(m,n)`.
-/

@[expose] public section

namespace NoncommutativeAMGM

open scoped BigOperators

/-- Sum of coefficients of the square-free monomials of a given degree. -/
noncomputable def layerCoefficientSum (n r : ℕ) : BooleanPolynomial n →ₗ[ℝ] ℝ :=
  (Finsupp.linearCombination ℝ (fun S : BooleanMonomial n ↦
    if (S : Finset (Fin n)).card = r then (1 : ℝ) else 0)).comp
      (MonoidAlgebra.coeffLinearEquiv ℝ).toLinearMap

theorem layerCoefficientSum_monomial {n : ℕ} (r : ℕ) (S : Finset (Fin n)) (c : ℝ) :
    layerCoefficientSum n r (booleanMonomial S c) = if S.card = r then c else 0 := by
  change Finsupp.linearCombination ℝ _ (Finsupp.single (show BooleanMonomial n from S) c) = _
  rw [Finsupp.linearCombination_single]
  split_ifs <;> simp_all

/-- A finite signed combination of interpolated slice functionals. -/
noncomputable def sliceQuadrature {J : Type*} [Fintype J] (n : ℕ) (a s : J → ℝ) :
    BooleanPolynomial n →ₗ[ℝ] ℝ := ∑ j, a j • sliceFunctional n (s j)

theorem sliceQuadrature_monomial {J : Type*} [Fintype J] {n : ℕ}
    (a s : J → ℝ) (S : Finset (Fin n)) (c : ℝ) :
    sliceQuadrature n a s (booleanMonomial S c) =
      c * ∑ j, a j * sliceMoment n (s j) S.card := by
  simp only [sliceQuadrature, LinearMap.sum_apply, LinearMap.smul_apply,
    sliceFunctional_monomial, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Slice moment constraints extract exactly the degree-`m` coefficient sum.
This is the scalar Boolean-polynomial coefficient-extraction step in Lemma 3.1. -/
theorem sliceQuadrature_extracts {J : Type*} [Fintype J] {n m : ℕ}
    (a s : J → ℝ) (c : ℝ)
    (hmom : ∀ r ≤ m, (∑ j, a j * sliceMoment n (s j) r) = if r = m then c else 0)
    (f : BooleanPolynomial n) (hf : BooleanDegreeLE f m) :
    sliceQuadrature n a s f = c * layerCoefficientSum n m f := by
  classical
  have hexpand : f = ∑ S ∈ f.coeff.support,
      booleanMonomial (S : Finset (Fin n)) (f.coeff S) := by
    exact (MonoidAlgebra.sum_coeff_single f).symm
  conv_lhs => rw [hexpand]
  rw [map_sum]
  conv_rhs => rw [hexpand]
  rw [map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  rw [sliceQuadrature_monomial a s (S : Finset (Fin n)) (f.coeff S),
    layerCoefficientSum_monomial m (S : Finset (Fin n)) (f.coeff S),
    hmom _ (hf S (Finsupp.mem_support_iff.mp hS))]
  split_ifs <;> ring

end NoncommutativeAMGM
