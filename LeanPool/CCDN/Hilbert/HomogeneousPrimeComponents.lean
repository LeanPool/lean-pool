/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.PolynomialLinearDescent
public import LeanPool.CCDN.Algebra.PolynomialPredicates
import LeanPool.CCDN.Algebra.IdealScalarDescent
import Mathlib.RingTheory.GradedAlgebra.Radical
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic

/-! Homogeneity survives coefficient extension and passage to
minimal-prime components. The latter uses the prime homogeneous core. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Applying a linear map to the coefficients commutes with taking homogeneous components. -/
lemma polynomialCoefficientLinear_homogeneousComponent
    {k K : Type*} [Field k] [Field K] [Algebra k K] {n : ℕ}
    (φ : K →ₗ[k] k) (N : ℕ) (f : MvPolynomial (Fin n) K) :
    polynomialCoefficientLinear φ (homogeneousComponent N f) =
      homogeneousComponent N (polynomialCoefficientLinear φ f) := by
  ext a
  simp only [polynomialCoefficientLinear_coeff, coeff_homogeneousComponent]
  split_ifs <;> simp only [map_zero]

/-- The extension of scalars of a homogeneous ideal is homogeneous. -/
theorem homogeneous_ideal_scalar_extension
    {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K))
    (hI : IsHomogeneousIdeal I) :
    ∀ f ∈ I.map (map (algebraMap K L)), ∀ N,
      homogeneousComponent N f ∈ I.map (map (algebraMap K L)) := by
  intro f hf N
  by_contra hn
  obtain ⟨φ, hφ⟩ := exists_polynomialCoefficientLinear_not_mem I _ hn
  apply hφ
  rw [polynomialCoefficientLinear_homogeneousComponent]
  exact hI _ (polynomialCoefficientLinear_mem_scalar_extension I f hf φ) N

/-- Every minimal prime over a homogeneous ideal is homogeneous. -/
theorem minimal_prime_ideal_homogeneous
    {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K))
    (hI : IsHomogeneousIdeal I)
    (P : Ideal (MvPolynomial σ K)) (hP : P ∈ Ideal.minimalPrimes I) :
    IsHomogeneousIdeal P := by
  classical
  let := MvPolynomial.gradedAlgebra (σ := σ) (R := K)
  let G := homogeneousSubmodule σ K
  let C := (P.homogeneousCore G).toIdeal
  have hCprime : C.IsPrime := hP.isPrime.homogeneousCore (𝒜 := G)
  have hCI : I ≤ C := by
    intro f hf
    rw [← sum_homogeneousComponent f]
    apply C.sum_mem
    intro N _
    exact Ideal.mem_homogeneousCore_of_homogeneous_of_mem
      (show SetLike.IsHomogeneousElem G (homogeneousComponent N f) from
        ⟨N, homogeneousComponent_mem N f⟩) (hP.le (hI f hf N))
  have hCP : C ≤ P := Ideal.toIdeal_homogeneousCore_le G P
  have hPC : P ≤ C := hP.2 ⟨hCprime, hCI⟩ hCP
  intro f hf N
  exact hCP (homogeneousComponent_mem_of_mem
    (P.homogeneousCore G).isHomogeneous (hPC hf) N)

end
end CCDN
