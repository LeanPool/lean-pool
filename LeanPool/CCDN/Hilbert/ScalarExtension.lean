/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.PolynomialLinearDescent
public import LeanPool.CCDN.Hilbert.FilteredHilbertPolynomial
import LeanPool.CCDN.Hilbert.StandardMonomials
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Scalar extension preserves the filtered Hilbert polynomial.
Coefficient-linear functionals descend elements of the extended ideal.
A functional nonzero on a leading coefficient preserves its leading exponent. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial
open scoped MonomialOrder

private lemma polynomialCoefficientLinear_monomialOrder_degree
    {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}
    (φ : L →ₗ[K] K) (g : MvPolynomial (Fin n) L) (m : MonomialOrder (Fin n))
    (hφ : φ (g.coeff (m.degree g)) ≠ 0) :
    m.degree (polynomialCoefficientLinear φ g) = m.degree g := by
  apply m.toSyn.injective
  apply le_antisymm
  · apply MonomialOrder.degree_le_iff.mpr
    intro a ha
    apply m.le_degree
    rw [mem_support_iff] at ha ⊢
    intro hz
    apply ha
    rw [polynomialCoefficientLinear_coeff, hz, map_zero]
  · apply m.le_degree
    rw [mem_support_iff, polynomialCoefficientLinear_coeff]
    exact hφ

/-- Extending scalars along a field extension `K → L` does not change the standard exponents of an
ideal. -/
theorem standardExponents_scalar_extension
    {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (m : MonomialOrder (Fin n)) :
    Ideal.standardExponents (I.map (map (algebraMap K L))) m = Ideal.standardExponents I m := by
  classical
  have hmapinj : Function.Injective (map (algebraMap K L) :
      MvPolynomial (Fin n) K → MvPolynomial (Fin n) L) :=
    map_injective _ (algebraMap K L).injective
  have hmapdeg (f : MvPolynomial (Fin n) K) :
      m.degree (map (algebraMap K L) f) = m.degree f := by
    simp only [MonomialOrder.degree]
    rw [support_map_of_injective f (algebraMap K L).injective]
  ext a
  constructor
  · intro ha f hf hf0
    have hh := ha (map (algebraMap K L) f) (Ideal.mem_map_of_mem _ hf)
      (map_ne_zero_iff _ hmapinj |>.mpr hf0)
    simpa only [hmapdeg] using hh
  · intro ha g hg hg0
    have hc := (m.coeff_degree_ne_zero_iff).mpr hg0
    obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero K hc
    have hdescent := polynomialCoefficientLinear_mem_scalar_extension I g hg φ
    have hnonzero : polynomialCoefficientLinear φ g ≠ 0 := by
      intro he
      have hh := polynomialCoefficientLinear_coeff φ g (m.degree g)
      have hz : φ (g.coeff (m.degree g)) = 0 := by simpa [he] using hh.symm
      exact hφ hz
    simpa only [polynomialCoefficientLinear_monomialOrder_degree φ g m hφ] using
      ha _ hdescent hnonzero

private theorem filteredCoordinateSpace_finrank_scalar_extension
    {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (N : ℕ) :
    Module.finrank L (filteredCoordinateSpace (I.map (map (algebraMap K L))) N) =
      Module.finrank K (filteredCoordinateSpace I N) := by
  rw [filteredCoordinateSpace_finrank_eq_standard_card,
    filteredCoordinateSpace_finrank_eq_standard_card]
  simp only [Ideal.boundedStandardExponents, standardExponents_scalar_extension]

/-- Extending scalars along a field extension `K → L` preserves the filtered Hilbert polynomial of
an ideal. -/
theorem filteredHilbertPolynomial_scalar_extension
    {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) :
    filteredHilbertPolynomial (I.map (map (algebraMap K L))) = filteredHilbertPolynomial I := by
  apply filteredHilbertPolynomial_eq_of_eventual
  obtain ⟨N, hN⟩ := filteredHilbertPolynomial_spec I
  refine ⟨N, fun M hM => ?_⟩
  rw [hN M hM, filteredCoordinateSpace_finrank_scalar_extension]

/-- Affine dimension and degree are preserved by extending the coefficient field. -/
theorem hasAffineDimensionDegree_scalar_extension
    {K L : Type*} [Field K] [Field L] [Algebra K L] {n m d : ℕ}
    {J : Ideal (MvPolynomial (Fin n) K)} (h : HasAffineDimensionDegree J m d) :
    HasAffineDimensionDegree (J.map (map (algebraMap K L))) m d :=
  h.of_filteredHilbertPolynomial_eq (filteredHilbertPolynomial_scalar_extension J)

/-- Projective dimension and degree are preserved by extending the coefficient field. -/
theorem hasProjectiveDimensionDegree_scalar_extension
    {K L : Type*} [Field K] [Field L] [Algebra K L] {n m d : ℕ}
    {J : Ideal (MvPolynomial (Fin n) K)} (h : HasProjectiveDimensionDegree J m d) :
    HasProjectiveDimensionDegree (J.map (map (algebraMap K L))) m d :=
  hasAffineDimensionDegree_scalar_extension h

end
end CCDN
