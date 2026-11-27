/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.RegionalWeylAlgebra
public import LeanPool.VacuumBellSeparation.Gaussian.DensityProductExtension

/-!
# Gaussian block covariance gives actual regional product expectations

The symplectic cross form removes the Weyl phase, while the covariance
cross form removes both cross terms in the Gaussian quadratic form. This
proves genuine factorization on Weyl generators, their polynomial algebras
and their operator-norm closures. Symplectic commutation alone is not used
as a substitute for the independent covariance condition.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open Matrix

variable {m : ℕ}

theorem gaussianPhysical_weyl_product
    {ρ : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}
    (hV : V.IsHermitian) (hG : HasGaussianPhysicalCharacteristic ρ V)
    (x y : Fin m × Fin 2 → ℝ)
    (hΩ : x ⬝ᵥ (modeSymplecticForm *ᵥ y) = 0)
    (hcov : x ⬝ᵥ (V *ᵥ y) = 0) :
    densityExpectation (multiModeNumberBasis m) ρ
        (physicalOscillatorWeyl x * physicalOscillatorWeyl y) =
      densityExpectation (multiModeNumberBasis m) ρ (physicalOscillatorWeyl x) *
        densityExpectation (multiModeNumberBasis m) ρ (physicalOscillatorWeyl y) := by
  have hsym : Vᵀ = V := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hV
  have hcov' : y ⬝ᵥ (V *ᵥ x) = 0 := by
    rw [← Matrix.dotProduct_transpose_mulVec V x y, hsym, hcov]
  have hquad : (x + y) ⬝ᵥ (V *ᵥ (x + y)) =
      x ⬝ᵥ (V *ᵥ x) + y ⬝ᵥ (V *ᵥ y) := by
    simp only [Matrix.mulVec_add, add_dotProduct, dotProduct_add, hcov, hcov', add_zero, zero_add]
  rw [physicalOscillatorWeyl_mul, hΩ]
  simp only [zero_div, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, one_smul]
  rw [gaussianPhysical_physicalOscillatorWeyl hG,
    gaussianPhysical_physicalOscillatorWeyl hG,
    gaussianPhysical_physicalOscillatorWeyl hG, hquad, ← Complex.ofReal_mul,
    ← Real.exp_add]
  congr 2
  ring

theorem gaussianPhysical_regional_polynomial_product
    {ρ : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hρ : IsPositiveTraceClass ρ)
    {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}
    (hV : V.IsHermitian) (hG : HasGaussianPhysicalCharacteristic ρ V)
    (L R : Submodule ℝ (Fin m × Fin 2 → ℝ))
    (hΩ : ∀ x ∈ L, ∀ y ∈ R, x ⬝ᵥ (modeSymplecticForm *ᵥ y) = 0)
    (hcov : ∀ x ∈ L, ∀ y ∈ R, x ⬝ᵥ (V *ᵥ y) = 0)
    {A B : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : A ∈ regionalWeylPolynomialAlgebra L)
    (hB : B ∈ regionalWeylPolynomialAlgebra R) :
    densityExpectation (multiModeNumberBasis m) ρ (A * B) =
      densityExpectation (multiModeNumberBasis m) ρ A *
        densityExpectation (multiModeNumberBasis m) ρ B := by
  apply linearFunctional_factorization_span
    (densityExpectationCLM (multiModeNumberBasis m) hρ).toLinearMap
    (regionalWeylGenerators L) (regionalWeylGenerators R) ?_ hA hB
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact gaussianPhysical_weyl_product hV hG x y (hΩ x hx y hy) (hcov x hx y hy)

theorem gaussianPhysical_regional_cstar_product
    {ρ : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hρ : IsPositiveTraceClass ρ)
    {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}
    (hV : V.IsHermitian) (hG : HasGaussianPhysicalCharacteristic ρ V)
    (L R : Submodule ℝ (Fin m × Fin 2 → ℝ))
    (hΩ : ∀ x ∈ L, ∀ y ∈ R, x ⬝ᵥ (modeSymplecticForm *ᵥ y) = 0)
    (hcov : ∀ x ∈ L, ∀ y ∈ R, x ⬝ᵥ (V *ᵥ y) = 0)
    {A B : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : A ∈ regionalWeylCStarAlgebra L)
    (hB : B ∈ regionalWeylCStarAlgebra R) :
    densityExpectation (multiModeNumberBasis m) ρ (A * B) =
      densityExpectation (multiModeNumberBasis m) ρ A *
        densityExpectation (multiModeNumberBasis m) ρ B := by
  apply continuousLinearFunctional_factorization_closure
    (densityExpectationCLM (multiModeNumberBasis m) hρ)
    (regionalWeylPolynomialAlgebra L) (regionalWeylPolynomialAlgebra R) ?_ hA hB
  intro A hA B hB
  exact gaussianPhysical_regional_polynomial_product hρ hV hG L R hΩ hcov hA hB

end VacuumBellSeparation.Gaussian
