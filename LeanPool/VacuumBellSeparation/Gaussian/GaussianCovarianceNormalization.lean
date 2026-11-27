/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.NormalizedCovarianceThermal
public import LeanPool.VacuumBellSeparation.Gaussian.RealMatrixOperatorNorms
public import LeanPool.VacuumBellSeparation.Gaussian.NormalizedCommutation

/-!
# From actual Gaussian covariances to source normalization coordinates

Whitening by the actual inverse square root preserves both perturbation
norms. On genuine Euclidean Hilbert space the normalized actual Gaussian
power increment equals the thermal CFC of the normalized commutation
matrix. These are coordinate identities, independent of how a source
subspace is embedded in a larger real Hilbert space.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped ENNReal MatrixOrder Matrix.Norms.L2Operator ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrix_inverse_sqrt_transpose {V : Matrix ι ι ℝ} (hV : V.PosDef) :
    ((CFC.sqrt V)⁻¹)ᵀ = (CFC.sqrt V)⁻¹ := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (matrix_sqrt_posDef hV).inv.isHermitian.eq

theorem relativeCovariancePerturbation_posDef
    {V H : Matrix ι ι ℝ} (hV : V.PosDef) (hH : H.PosDef) :
    (relativeCovariancePerturbation V H).PosDef := by
  have h := hH.mul_mul_conjTranspose_same
    (Matrix.vecMul_injective_of_isUnit (matrix_sqrt_posDef hV).inv.isUnit)
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,
    matrix_inverse_sqrt_transpose hV, relativeCovariancePerturbation] using h

/-- No symplectic assumption is needed for this simultaneous coordinate
change of the increment and perturbation matrices. -/
theorem relativeCovariancePerturbation_whitening_norms
    {V H : Matrix ι ι ℝ} (hV : V.PosDef) (hH : H.PosDef) (Δ : Matrix ι ι ℝ) :
    ‖relativeCovariancePerturbation (relativeCovariancePerturbation V H)
      (relativeCovariancePerturbation V Δ)‖ = ‖relativeCovariancePerturbation H Δ‖ ∧
    matrixTraceNorm (relativeCovariancePerturbation (relativeCovariancePerturbation V H)
      (relativeCovariancePerturbation V Δ)) = matrixTraceNorm
        (relativeCovariancePerturbation H Δ) := by
  let S := (CFC.sqrt V)⁻¹
  have ht : Sᵀ = S := matrix_inverse_sqrt_transpose hV
  have hW : (S * H * Sᵀ).PosDef := by
    rw [ht]
    exact relativeCovariancePerturbation_posDef hV hH
  have hn := norm_relativeCovariancePerturbation_congruence S hH hW Δ
  have htr := matrixTraceNorm_relativeCovariancePerturbation_congruence S hH hW Δ
  simpa only [ht, S, relativeCovariancePerturbation] using And.intro hn htr

theorem toEuclideanCLM_cfc_abs (A : Matrix ι ι ℂ) (f : ℝ → ℝ) :
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) (cfc f (CFC.abs A)) =
      cfc f (CFC.abs ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) A)) := by
  let euclideanLinear :=
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)).toAlgEquiv.toLinearEquiv.toLinearMap
  have hm := StarAlgHomClass.map_cfc (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) f (CFC.abs A)
    ((CFC.abs A).finite_real_spectrum.continuousOn f)
    euclideanLinear.continuous_of_finiteDimensional
    (CFC.abs_nonneg A).isSelfAdjoint
    (map_nonneg (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) (CFC.abs_nonneg A)).isSelfAdjoint
  simpa only [toEuclideanCLM_abs] using hm

variable {m : ℕ}

theorem gaussian_power_increment_operator_eq_normalizedThermal
    {σ : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hσ : IsFaithfulDensity σ)
    {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}
    (hV : V.IsHermitian) (hG : HasGaussianPhysicalCharacteristic σ V)
    {τ : ℝ} (hτ : 0 < τ) :
    realMatrixOperator (relativeCovariancePerturbation V (gaussianPowerIncrement σ τ)) =
      normalizedThermal τ ((Matrix.toEuclideanCLM (n := Fin m × Fin 2) (𝕜 := ℂ))
        (covarianceCommutationMatrix V modeSymplecticForm)) := by
  rw [realMatrixOperator, gaussian_power_increment_eq_cfc_commutation hσ hV hG hτ,
    toEuclideanCLM_cfc_abs]
  rfl

theorem gaussian_thermal_weight_isStrictlyPositive
    {σ : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hσ : IsFaithfulDensity σ)
    {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}
    (hV : V.IsHermitian) (hG : HasGaussianPhysicalCharacteristic σ V)
    {τ : ℝ} (hτ₀ : 0 < τ) (hτ₁ : τ < 1) :
    IsStrictlyPositive (normalizedThermal τ
      ((Matrix.toEuclideanCLM (n := Fin m × Fin 2) (𝕜 := ℂ))
        (covarianceCommutationMatrix V modeSymplecticForm))) := by
  rw [← gaussian_power_increment_operator_eq_normalizedThermal hσ hV hG hτ₀,
    realMatrixOperator]
  have hp := complexifyMatrix_posDef (relativeCovariancePerturbation_posDef
    (real_posDef_of_quantum_posDef (actual_faithful_gaussian_quantum_posDef hσ hV hG))
    (faithful_gaussian_power_increment_posDef hσ hV hG hτ₀ hτ₁))
  exact (hp.isUnit.map
    (Matrix.toEuclideanCLM (n := Fin m × Fin 2) (𝕜 :=
      ℂ)).toAlgEquiv.toRingEquiv.toMonoidHom).isStrictlyPositive
    (map_nonneg (Matrix.toEuclideanCLM (n := Fin m × Fin 2) (𝕜 := ℂ)) hp.posSemidef.nonneg)

theorem intrinsicGaussianRelativePerturbation_whitening_norms
    {ρ σ : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hσ : IsFaithfulDensity σ)
    {Vρ Vσ : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}
    (hVρ : Vρ.IsHermitian) (hVσ : Vσ.IsHermitian)
    (hGρ : HasGaussianPhysicalCharacteristic ρ Vρ)
    (hGσ : HasGaussianPhysicalCharacteristic σ Vσ)
    {τ : ℝ} (hτ₀ : 0 < τ) (hτ₁ : τ < 1) :
    let H := relativeCovariancePerturbation Vσ (gaussianPowerIncrement σ τ)
    let Δ := relativeCovariancePerturbation Vσ (Vρ - Vσ)
    ‖relativeCovariancePerturbation H Δ‖ = ‖intrinsicGaussianRelativePerturbation ρ σ τ‖ ∧
      matrixTraceNorm (relativeCovariancePerturbation H Δ) =
        matrixTraceNorm (intrinsicGaussianRelativePerturbation ρ σ τ) := by
  rw [intrinsicGaussianRelativePerturbation, gaussianPhysicalCovariance_eq hVρ hGρ,
    gaussianPhysicalCovariance_eq hVσ hGσ]
  exact relativeCovariancePerturbation_whitening_norms
    (real_posDef_of_quantum_posDef (actual_faithful_gaussian_quantum_posDef hσ hVσ hGσ))
    (faithful_gaussian_power_increment_posDef hσ hVσ hGσ hτ₀ hτ₁) (Vρ - Vσ)

end VacuumBellSeparation.Gaussian
