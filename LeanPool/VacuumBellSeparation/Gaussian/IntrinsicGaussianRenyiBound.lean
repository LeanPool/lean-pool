/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.IntrinsicGaussianPerturbationDefs
public import LeanPool.VacuumBellSeparation.Gaussian.GaussianFaithfulRenyiComparison
public import LeanPool.VacuumBellSeparation.Gaussian.GaussianCovarianceUniqueness

/-!
# Intrinsic finite-mode Gaussian Rényi bound

The perturbation uses the unique physical covariances of the actual
states and of the actual normalized reference power. The final statement
contains no chosen Williamson coordinates, no separately assumed quantum
uncertainty, and no derivative premise. The reference power increment is
proved positive definite for 0<tau<1 and a faithful Gaussian reference.

The operator space is the genuine infinite occupation Hilbert space for
finitely many modes. The quantity is the genuine bounded inverse-form
extension power trace from SandwichedRenyiQuantity.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped Matrix.Norms.L2Operator

variable {m : ℕ}
variable {ρ σ : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
variable {Vρ Vσ : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}

theorem normalizedGaussianPowerCovariance_in_coordinates
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    {q : Fin m → ℝ} (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∀ j, q j < 1)
    (hσ : IsPositiveTraceClass σ)
    (hGσ : HasGaussianPhysicalCharacteristic σ (S * thermalReferenceCovariance q * Sᵀ))
    {a : ℝ} (ha : 0 < a) :
    normalizedGaussianPowerCovariance σ a = S * thermalPowerCovariance q a * Sᵀ := by
  apply gaussianPhysicalCovariance_eq
  · exact (canonical_symplectic_congruence_posDef S hS
      (thermalPowerCovariance_posDef hq₀ hq₁ ha)).isHermitian
  · exact gaussian_reference_normalized_power_characteristic S hS hq₀ hq₁ hσ hGσ ha

theorem gaussianPowerIncrement_in_coordinates
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    {q : Fin m → ℝ} (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∀ j, q j < 1)
    (hσ : IsPositiveTraceClass σ) (hVσ : Vσ.IsHermitian)
    (hGσ : HasGaussianPhysicalCharacteristic σ Vσ)
    (hcov : S * thermalReferenceCovariance q * Sᵀ = Vσ)
    {τ : ℝ} (hτ : 0 < τ) :
    gaussianPowerIncrement σ τ = transportedThermalIncrement S q τ := by
  rw [gaussianPowerIncrement, gaussianPhysicalCovariance_eq hVσ hGσ,
    normalizedGaussianPowerCovariance_in_coordinates S hS hq₀ hq₁ hσ
      (hcov.symm ▸ hGσ) hτ, ← hcov, transportedThermalIncrement_eq_difference]

theorem intrinsicGaussianRelativePerturbation_in_coordinates
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    {q : Fin m → ℝ} (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∀ j, q j < 1)
    (hσ : IsPositiveTraceClass σ) (hVρ : Vρ.IsHermitian) (hVσ : Vσ.IsHermitian)
    (hGρ : HasGaussianPhysicalCharacteristic ρ Vρ)
    (hGσ : HasGaussianPhysicalCharacteristic σ Vσ)
    (hcov : S * thermalReferenceCovariance q * Sᵀ = Vσ)
    {τ : ℝ} (hτ : 0 < τ) :
    intrinsicGaussianRelativePerturbation ρ σ τ =
      transportedGaussianRelativePerturbation S q τ Vρ := by
  rw [intrinsicGaussianRelativePerturbation,
    gaussianPowerIncrement_in_coordinates S hS hq₀ hq₁ hσ hVσ hGσ hcov hτ,
    gaussianPhysicalCovariance_eq hVρ hGρ, gaussianPhysicalCovariance_eq hVσ hGσ,
    ← hcov]
  rfl

theorem faithful_gaussian_power_increment_posDef
    (hσ : IsFaithfulDensity σ) (hVσ : Vσ.IsHermitian)
    (hGσ : HasGaussianPhysicalCharacteristic σ Vσ) {τ : ℝ}
    (hτ₀ : 0 < τ) (hτ₁ : τ < 1) : (gaussianPowerIncrement σ τ).PosDef := by
  obtain ⟨q, S, hS, hq₀, hq₁, hcov, _⟩ :=
    exists_gaussian_reference_thermal_coordinates hσ.isPositiveTraceClass
      (actual_faithful_gaussian_quantum_posDef hσ hVσ hGσ) hGσ
  rw [gaussianPowerIncrement_in_coordinates S hS (fun j => (hq₀ j).le) hq₁
    hσ.isPositiveTraceClass hVσ hGσ hcov hτ₀]
  exact transportedThermalIncrement_posDef S hS hq₀ hq₁ hτ₀ hτ₁

/-- The finite-mode source Gaussian Rényi estimate for the actual faithful
states and their intrinsic normalized-power covariance perturbation. -/
theorem faithful_gaussian_renyi_bound
    (hρ : IsFaithfulDensity ρ) (hσ : IsFaithfulDensity σ)
    (hVρ : Vρ.IsHermitian) (hVσ : Vσ.IsHermitian)
    (hGρ : HasGaussianPhysicalCharacteristic ρ Vρ)
    (hGσ : HasGaussianPhysicalCharacteristic σ Vσ)
    {r : ℝ} (hr : 1 < r)
    (hsmall : ‖intrinsicGaussianRelativePerturbation ρ σ (gaussianRenyiTau r)‖ ≤
      (4 * max 2 (gaussianRenyiTau r)⁻¹)⁻¹) :
    0 < sandwichedRenyiQuantity ρ σ r ∧ sandwichedRenyiQuantity ρ σ r < ⊤ ∧
      Real.log (sandwichedRenyiQuantity ρ σ r).toReal ≤
        2 * r * max 2 (gaussianRenyiTau r)⁻¹ *
          matrixTraceNorm (intrinsicGaussianRelativePerturbation ρ σ (gaussianRenyiTau r)) := by
  obtain ⟨q, S, hS, hq₀, hq₁, hcov, hpower, hcomp⟩ :=
    exists_faithful_gaussian_renyi_comparison hρ hσ hVρ hVσ hGρ hGσ
  have he := intrinsicGaussianRelativePerturbation_in_coordinates S hS
    (fun j => (hq₀ j).le) hq₁ hσ.isPositiveTraceClass hVρ hVσ hGρ hGσ hcov
    (gaussianRenyiTau_pos hr)
  rw [he] at hsmall ⊢
  exact hcomp r hr hsmall

end VacuumBellSeparation.Gaussian
