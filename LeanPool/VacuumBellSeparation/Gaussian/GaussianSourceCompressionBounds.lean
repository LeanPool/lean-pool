/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.GaussianCovarianceNormalization
public import LeanPool.VacuumBellSeparation.Gaussian.MatrixNormalizationOperator
public import LeanPool.VacuumBellSeparation.Gaussian.ReserveThermalCompression

/-!
# Actual Gaussian perturbation bounds from source reserve factorizations

The hypotheses identify the actual compressed commutation operator and
the actual covariance-normalized perturbation. All thermal positivity,
normalization, compression estimates, and both perturbation norm bounds
are then derived. The physical source embedding and its full-space
reserve factorization remain explicit model identifications; the desired
finite perturbation estimates are not assumed.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped ENNReal MatrixOrder Matrix.Norms.L2Operator ComplexOrder

variable {m : ℕ}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {ρ σ : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
variable {Vρ Vσ : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}

theorem intrinsicGaussianRelativePerturbation_compression_norms
    (hσ : IsFaithfulDensity σ) (hVρ : Vρ.IsHermitian) (hVσ : Vσ.IsHermitian)
    (hGρ : HasGaussianPhysicalCharacteristic ρ Vρ)
    (hGσ : HasGaussianPhysicalCharacteristic σ Vσ)
    (e : EuclideanSpace ℂ (Fin m × Fin 2) →ₗᵢ[ℂ] F)
    {B T : F →L[ℂ] F}
    (hB : compression e B = (Matrix.toEuclideanCLM (n := Fin m × Fin 2) (𝕜 := ℂ))
      (covarianceCommutationMatrix Vσ modeSymplecticForm))
    (hD : realMatrixOperator (relativeCovariancePerturbation Vσ (Vρ - Vσ)) = compression e T)
    {τ : ℝ} (hτ₀ : 0 < τ) (hτ₁ : τ < 1) :
    ‖intrinsicGaussianRelativePerturbation ρ σ τ‖ =
        ‖normalizedReserveCompression e T (normalizedThermal τ (compression e B))‖ ∧
      ENNReal.ofReal (matrixTraceNorm (intrinsicGaussianRelativePerturbation ρ σ τ)) =
        operatorTraceNorm (normalizedReserveCompression e T (normalizedThermal τ
          (compression e B))) := by
  have hH := relativeCovariancePerturbation_posDef
    (real_posDef_of_quantum_posDef (actual_faithful_gaussian_quantum_posDef hσ hVσ hGσ))
    (faithful_gaussian_power_increment_posDef hσ hVσ hGσ hτ₀ hτ₁)
  have hh : realMatrixOperator (relativeCovariancePerturbation Vσ (gaussianPowerIncrement σ τ)) =
      normalizedThermal τ (compression e B) := by
    rw [hB]
    exact gaussian_power_increment_operator_eq_normalizedThermal hσ hVσ hGσ hτ₀
  have hm := matrix_normalized_compression_norms e hH hD
  rw [hh] at hm
  have hw := intrinsicGaussianRelativePerturbation_whitening_norms
    hσ hVρ hVσ hGρ hGσ hτ₀ hτ₁
  dsimp only at hw
  exact ⟨hw.1.symm.trans hm.1, (congrArg ENNReal.ofReal hw.2).symm.trans hm.2⟩

/-- The reverse/low-parameter source normalization estimate for the
literal intrinsic actual Gaussian perturbation. -/
theorem gaussian_low_source_factorization_bounds
    (hσ : IsFaithfulDensity σ) (hVρ : Vρ.IsHermitian) (hVσ : Vσ.IsHermitian)
    (hGρ : HasGaussianPhysicalCharacteristic ρ Vρ)
    (hGσ : HasGaussianPhysicalCharacteristic σ Vσ)
    (e : EuclideanSpace ℂ (Fin m × Fin 2) →ₗᵢ[ℂ] F)
    {B Y : F →L[ℂ] F} (hB : IsSelfAdjoint B) (hnorm : ‖B‖ ≤ 1)
    (hcomp : compression e B = (Matrix.toEuclideanCLM (n := Fin m × Fin 2) (𝕜 := ℂ))
      (covarianceCommutationMatrix Vσ modeSymplecticForm))
    {a : ℝ} (ha₀ : 0 < a) (ha₁ : a ≤ 1 / 2)
    (hD : realMatrixOperator (relativeCovariancePerturbation Vσ (Vρ - Vσ)) =
      compression e (reserve B ^ a * Y * reserve B ^ a))
    (hcY : IsCompactOperator Y) (hY : IsSelfAdjoint Y) :
    ‖intrinsicGaussianRelativePerturbation ρ σ a‖ ≤ (thermalConst a)⁻¹ * ‖Y‖ ∧
      ENNReal.ofReal (matrixTraceNorm (intrinsicGaussianRelativePerturbation ρ σ a)) ≤
        ENNReal.ofReal (thermalConst a)⁻¹ * operatorTraceNorm Y := by
  have ha1 : a < 1 := by linarith
  have hH : IsStrictlyPositive (normalizedThermal a (compression e B)) := by
    rw [hcomp]
    exact gaussian_thermal_weight_isStrictlyPositive hσ hVσ hGσ ha₀ ha1
  have hn := intrinsicGaussianRelativePerturbation_compression_norms
    hσ hVρ hVσ hGρ hGσ e hcomp hD ha₀ ha1
  rw [hn.1, hn.2]
  exact low_thermal_normalized_factorization_bounds e hB hnorm ha₀ ha₁ hH hcY hY

/-- The forward/high-parameter source normalization estimate. Endpoint
spectra of the full source B are allowed; the actual Gaussian finite
reference supplies target strict positivity. -/
theorem gaussian_high_source_factorization_bounds
    (hσ : IsFaithfulDensity σ) (hVρ : Vρ.IsHermitian) (hVσ : Vσ.IsHermitian)
    (hGρ : HasGaussianPhysicalCharacteristic ρ Vρ)
    (hGσ : HasGaussianPhysicalCharacteristic σ Vσ)
    (e : EuclideanSpace ℂ (Fin m × Fin 2) →ₗᵢ[ℂ] F)
    {B Y : F →L[ℂ] F} (hB : IsSelfAdjoint B) (hnorm : ‖B‖ ≤ 1)
    (hcomp : compression e B = (Matrix.toEuclideanCLM (n := Fin m × Fin 2) (𝕜 := ℂ))
      (covarianceCommutationMatrix Vσ modeSymplecticForm))
    (n : ℕ)
    (hD : realMatrixOperator (relativeCovariancePerturbation Vσ (Vρ - Vσ)) =
      compression e (reserve B ^ (((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ)) * Y *
        reserve B ^ (((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ))))
    (hcY : IsCompactOperator Y) (hY : IsSelfAdjoint Y) :
    let b : ℝ := ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ)
    ‖intrinsicGaussianRelativePerturbation ρ σ b‖ ≤ (thermalConst b)⁻¹ * ‖Y‖ ∧
      ENNReal.ofReal (matrixTraceNorm (intrinsicGaussianRelativePerturbation ρ σ b)) ≤
        ENNReal.ofReal (thermalConst b)⁻¹ * operatorTraceNorm Y := by
  dsimp only
  have hb₀ : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ) := by positivity
  have hb₁ : ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ) < 1 := by
    apply (div_lt_one (by positivity)).mpr
    exact_mod_cast (show n + 1 < n + 2 by omega)
  have hH : IsStrictlyPositive (normalizedThermal
      (((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ)) (compression e B)) := by
    rw [hcomp]
    exact gaussian_thermal_weight_isStrictlyPositive hσ hVσ hGσ hb₀ hb₁
  have hn := intrinsicGaussianRelativePerturbation_compression_norms
    hσ hVρ hVσ hGρ hGσ e hcomp hD hb₀ hb₁
  rw [hn.1, hn.2]
  exact high_thermal_normalized_factorization_bounds e hB hnorm n hH hcY hY

end VacuumBellSeparation.Gaussian
