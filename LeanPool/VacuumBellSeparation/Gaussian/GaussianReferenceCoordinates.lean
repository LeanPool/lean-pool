/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.GaussianCoordinateTransport
public import LeanPool.VacuumBellSeparation.Gaussian.ThermalPartitionCancellation
public import LeanPool.VacuumBellSeparation.Gaussian.ThermalCovariancePerturbation

/-!
# Thermal coordinates of an actual strictly quantum Gaussian reference

Actual Williamson factorization and density-characteristic uniqueness
identify the original reference with a unitary transport of the genuine
product thermal density. The same coordinates describe its actual
normalized CFC powers and their thermal increment.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {m : ℕ}

/-- Transported thermal increment defined as `S * thermalReferenceGap q τ * Sᵀ`. -/
def transportedThermalIncrement
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) (q : Fin m → ℝ) (τ : ℝ) :
    Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ := S * thermalReferenceGap q τ * Sᵀ

/-- Transported Gaussian relative perturbation. -/
def transportedGaussianRelativePerturbation
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) (q : Fin m → ℝ) (τ : ℝ)
    (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) :
    Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ :=
  relativeCovariancePerturbation (transportedThermalIncrement S q τ)
    (V - S * thermalReferenceCovariance q * Sᵀ)

theorem transportedThermalIncrement_eq_difference
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) (q : Fin m → ℝ) (τ : ℝ) :
    transportedThermalIncrement S q τ =
      S * thermalPowerCovariance q τ * Sᵀ - S * thermalReferenceCovariance q * Sᵀ := by
  unfold transportedThermalIncrement thermalReferenceGap thermalPowerCovariance
  noncomm_ring

theorem transportedThermalIncrement_posDef
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    {q : Fin m → ℝ} {τ : ℝ} (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1)
    (hτ₀ : 0 < τ) (hτ₁ : τ < 1) : (transportedThermalIncrement S q τ).PosDef :=
  canonical_symplectic_congruence_posDef S hS (thermalReferenceGap_posDef hq₀ hq₁ hτ₀ hτ₁)

theorem transportedGaussianRelativePerturbation_norms
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    {q : Fin m → ℝ} {τ : ℝ} (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1)
    (hτ₀ : 0 < τ) (hτ₁ : τ < 1)
    (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) :
    ‖transportedGaussianRelativePerturbation S q τ V‖ =
        ‖gaussianRelativePerturbation q τ (S⁻¹ * V * (S⁻¹)ᵀ)‖ ∧
      matrixTraceNorm (transportedGaussianRelativePerturbation S q τ V) =
        matrixTraceNorm (gaussianRelativePerturbation q τ (S⁻¹ * V * (S⁻¹)ᵀ)) := by
  have hH := thermalReferenceGap_posDef hq₀ hq₁ hτ₀ hτ₁
  have hW := transportedThermalIncrement_posDef S hS hq₀ hq₁ hτ₀ hτ₁
  have hΔ : V - S * thermalReferenceCovariance q * Sᵀ =
      S * ((S⁻¹ * V * (S⁻¹)ᵀ) - thermalReferenceCovariance q) * Sᵀ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, canonical_congruence_inverse_cancel S V hS]
  rw [transportedGaussianRelativePerturbation, transportedThermalIncrement, hΔ,
    gaussianRelativePerturbation_eq_relative]
  exact ⟨norm_relativeCovariancePerturbation_congruence S hH hW _,
    matrixTraceNorm_relativeCovariancePerturbation_congruence S hH hW _⟩

theorem multiModeThermalDensity_isPositiveTraceClass
    {q : Fin m → ℝ} (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∀ j, q j < 1) :
    IsPositiveTraceClass (multiModeThermalDensity q) := by
  refine ⟨multiModeThermalDensity_nonneg hq₀ hq₁, ?_⟩
  rw [positiveTrace_multiModeThermalDensity hq₀ hq₁]
  exact ENNReal.one_lt_top

theorem gaussian_reference_eq_thermal_pullback
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    {q : Fin m → ℝ} (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∀ j, q j < 1)
    {σ : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hσ : IsPositiveTraceClass σ)
    (hG : HasGaussianPhysicalCharacteristic σ (S * thermalReferenceCovariance q * Sᵀ)) :
    σ = physicalDensityPullback S hS (multiModeThermalDensity q) := by
  apply gaussianPhysical_density_unique hσ
    (physicalDensityPullback_isPositiveTraceClass S hS
      (multiModeThermalDensity_isPositiveTraceClass hq₀ hq₁))
  · exact hG
  · exact physicalDensityPullback_hasGaussianPhysicalCharacteristic S hS
      (multiModeThermalDensity_isPositiveTraceClass hq₀ hq₁)
      (multiModeThermalDensity_hasGaussianPhysicalCharacteristic hq₀ hq₁)

theorem gaussian_reference_normalized_power_characteristic
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    {q : Fin m → ℝ} (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∀ j, q j < 1)
    {σ : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hσ : IsPositiveTraceClass σ)
    (hG : HasGaussianPhysicalCharacteristic σ (S * thermalReferenceCovariance q * Sᵀ))
    {a : ℝ} (ha : 0 < a) :
    HasGaussianPhysicalCharacteristic (normalizedPositiveDensity (σ ^ a))
      (S * thermalPowerCovariance q a * Sᵀ) := by
  let e := (physicalCongruenceUnitary S hS).symm
  have he := gaussian_reference_eq_thermal_pullback S hS hq₀ hq₁ hσ hG
  change σ = e.conjStarAlgEquiv (multiModeThermalDensity q) at he
  rw [he]
  erw [← conjStarAlgEquiv_rpow e (multiModeThermalDensity_nonneg hq₀ hq₁) ha.le,
    normalizedPositiveDensity_conjStarAlgEquiv e CFC.rpow_nonneg]
  exact physicalDensityPullback_hasGaussianPhysicalCharacteristic S hS
    (normalizedPositiveDensity_isPositiveTraceClass (multiModeNumberBasis m)
      (multiModeThermalDensity_rpow_isPositiveTraceClass hq₀ hq₁ ha))
    (normalizedPositiveDensity_thermal_power_characteristic hq₀ hq₁ ha)

theorem exists_gaussian_reference_thermal_coordinates
    {σ : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hσ : IsPositiveTraceClass σ)
    {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}
    (hQ : (quantumCovariance V modeSymplecticForm).PosDef)
    (hG : HasGaussianPhysicalCharacteristic σ V) :
    ∃ (q : Fin m → ℝ) (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
      (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm),
      (∀ j, 0 < q j) ∧ (∀ j, q j < 1) ∧
      S * thermalReferenceCovariance q * Sᵀ = V ∧
      σ = physicalDensityPullback S hS (multiModeThermalDensity q) := by
  obtain ⟨ν, S, hν, hS, hcov⟩ :=
    exists_faithful_canonical_williamson V (real_posDef_of_quantum_posDef hQ) hQ
  let q : Fin m → ℝ := fun j => covarianceThermalParameter (ν j)
  have hq₀ : ∀ j, 0 < q j := fun j => covarianceThermalParameter_pos (hν j)
  have hq₁ : ∀ j, q j < 1 := fun j => covarianceThermalParameter_lt_one (hν j).le
  have hD : thermalReferenceCovariance q = modeDiagonal ν := by
    unfold thermalReferenceCovariance q
    simp_rw [thermalQuadratureVariance_covarianceParameter (hν _).le]
  have hc : S * thermalReferenceCovariance q * Sᵀ = V := by rw [hD, hcov]
  refine ⟨q, S, hS, hq₀, hq₁, hc, ?_⟩
  exact gaussian_reference_eq_thermal_pullback S hS (fun j => (hq₀ j).le) hq₁ hσ (hc.symm ▸ hG)

end VacuumBellSeparation.Gaussian
