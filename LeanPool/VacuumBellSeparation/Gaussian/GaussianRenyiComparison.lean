/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.GaussianThermalRenyiBound
public import LeanPool.VacuumBellSeparation.Gaussian.GaussianReferenceCoordinates

/-!
# Gaussian Rényi comparison on the original canonical oscillator system

Actual inverse symplectic coordinates transform the input and the
reference on the same Hilbert space. The unique Gaussian characteristic
recovers both original density operators after the same actual unitary
transport. Orthogonal similarity preserves the operator and nuclear norms
of the literal normalized covariance perturbation.

The covariance hypotheses are genuine strict quantum matrix positivity.
The result concerns the actual bounded extension of the inverse-domain
sandwich and its positive finite r-th power trace. No scalar kernel or
abstract state is substituted for either density operator.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {m : ℕ}
variable {ρ σ : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
variable {Vρ Vσ : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}

theorem gaussian_renyi_comparison_in_coordinates
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    {q : Fin m → ℝ} (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1)
    (hρ : IsPositiveTraceClass ρ) (hσ : IsPositiveTraceClass σ)
    (hGρ : HasGaussianPhysicalCharacteristic ρ Vρ)
    (hGσ : HasGaussianPhysicalCharacteristic σ (S * thermalReferenceCovariance q * Sᵀ))
    (hQρ : (quantumCovariance Vρ modeSymplecticForm).PosDef)
    {r : ℝ} (hr : 1 < r)
    (hδ : ‖transportedGaussianRelativePerturbation S q (gaussianRenyiTau r) Vρ‖ ≤
      (4 * max 2 (gaussianRenyiTau r)⁻¹)⁻¹) :
    ∃ Θ : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m,
      IsPositiveTraceClass Θ ∧
      (σ ^ (gaussianRenyiTau r / 2)) * Θ * (σ ^ (gaussianRenyiTau r / 2)) = ρ ∧
      0 < positiveTrace (Θ ^ r) ∧ positiveTrace (Θ ^ r) < ⊤ ∧
      Real.log (positiveTrace (Θ ^ r)).toReal ≤
        2 * r * max 2 (gaussianRenyiTau r)⁻¹ *
          matrixTraceNorm (transportedGaussianRelativePerturbation S q
            (gaussianRenyiTau r) Vρ) := by
  let A := gaussianInverseCoordinates S hS ρ
  let V := S⁻¹ * Vρ * (S⁻¹)ᵀ
  have hA := gaussianInverseCoordinates_isPositiveTraceClass S hS hρ
  have hGA := gaussianInverseCoordinates_hasGaussianPhysicalCharacteristic S hS hρ hGρ
  have hQ : (quantumCovariance V modeSymplecticForm).PosDef :=
    quantumCovariance_symplectic_congruence_posDef S⁻¹ (canonical_symplectic_inv S hS) hQρ
  have hV := real_posDef_of_quantum_posDef hQ
  have hn := transportedGaussianRelativePerturbation_norms S hS hq₀ hq₁
    (gaussianRenyiTau_pos hr) (gaussianRenyiTau_lt_one hr) Vρ
  have hsmall : ‖gaussianRelativePerturbation q (gaussianRenyiTau r) V‖ ≤
      (4 * max 2 (gaussianRenyiTau r)⁻¹)⁻¹ := by
    rwa [hn.1] at hδ
  obtain ⟨Θ₀, htc, hf, hp, hfin, hb⟩ := exists_gaussian_thermal_renyi_bound
    hq₀ hq₁ hr hA hGA hV.isHermitian (quantum_covariance_shift_posDef hQ) hQ hsmall
  let e := (physicalCongruenceUnitary S hS).symm
  have hσeq : σ = e.conjStarAlgEquiv (multiModeThermalDensity q) :=
    gaussian_reference_eq_thermal_pullback S hS (fun j => (hq₀ j).le) hq₁ hσ hGσ
  have hρeq : e.conjStarAlgEquiv A = ρ :=
    physicalDensityPullback_gaussianInverseCoordinates S hS hρ hGρ
  have hpower : positiveTrace ((e.conjStarAlgEquiv Θ₀) ^ r) = positiveTrace (Θ₀ ^ r) :=
    positiveTrace_conjStarAlgEquiv_rpow e htc.1 (by linarith)
  refine ⟨e.conjStarAlgEquiv Θ₀, IsPositiveTraceClass.conjStarAlgEquiv e htc, ?_,
    hpower.symm ▸ hp, hpower.symm ▸ hfin, ?_⟩
  · rw [hσeq]
    exact (conjStarAlgEquiv_sandwich
      (E := MultiModeOscillatorSpace m) (F := MultiModeOscillatorSpace m)
      e (σ := multiModeThermalDensity q)
      (multiModeThermalDensity_nonneg (fun j => (hq₀ j).le) hq₁)
      (τ := gaussianRenyiTau r) (gaussianRenyiTau_pos hr).le Θ₀).symm.trans
        ((congrArg e.conjStarAlgEquiv hf).trans hρeq)
  · rw [hpower, hn.2]
    exact hb

/-- Every actual strictly quantum Gaussian reference admits the source
comparison in coordinates whose increment is also identified by the
actual normalized reference powers. Both densities stay on the original
canonical oscillator Hilbert space. -/
theorem exists_gaussian_renyi_comparison
    (hρ : IsPositiveTraceClass ρ) (hσ : IsPositiveTraceClass σ)
    (hGρ : HasGaussianPhysicalCharacteristic ρ Vρ)
    (hGσ : HasGaussianPhysicalCharacteristic σ Vσ)
    (hQρ : (quantumCovariance Vρ modeSymplecticForm).PosDef)
    (hQσ : (quantumCovariance Vσ modeSymplecticForm).PosDef) :
    ∃ (q : Fin m → ℝ) (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
      (_hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm),
      (∀ j, 0 < q j) ∧ (∀ j, q j < 1) ∧
      S * thermalReferenceCovariance q * Sᵀ = Vσ ∧
      (∀ a : ℝ, 0 < a → HasGaussianPhysicalCharacteristic (normalizedPositiveDensity (σ ^ a))
        (S * thermalPowerCovariance q a * Sᵀ)) ∧
      ∀ r : ℝ, 1 < r →
        ‖transportedGaussianRelativePerturbation S q (gaussianRenyiTau r) Vρ‖ ≤
          (4 * max 2 (gaussianRenyiTau r)⁻¹)⁻¹ →
        ∃ Θ : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m,
          IsPositiveTraceClass Θ ∧
          (σ ^ (gaussianRenyiTau r / 2)) * Θ * (σ ^ (gaussianRenyiTau r / 2)) = ρ ∧
          0 < positiveTrace (Θ ^ r) ∧ positiveTrace (Θ ^ r) < ⊤ ∧
          Real.log (positiveTrace (Θ ^ r)).toReal ≤
            2 * r * max 2 (gaussianRenyiTau r)⁻¹ *
              matrixTraceNorm (transportedGaussianRelativePerturbation S q
                (gaussianRenyiTau r) Vρ) := by
  obtain ⟨q, S, hS, hq₀, hq₁, hcov, _⟩ :=
    exists_gaussian_reference_thermal_coordinates hσ hQσ hGσ
  have hGσ' : HasGaussianPhysicalCharacteristic σ (S * thermalReferenceCovariance q * Sᵀ) :=
    hcov.symm ▸ hGσ
  refine ⟨q, S, hS, hq₀, hq₁, hcov, ?_, ?_⟩
  · intro a ha
    exact gaussian_reference_normalized_power_characteristic S hS
      (fun j => (hq₀ j).le) hq₁ hσ hGσ' ha
  · intro r hr hδ
    exact gaussian_renyi_comparison_in_coordinates S hS hq₀ hq₁ hρ hσ hGρ hGσ' hQρ hr hδ

end VacuumBellSeparation.Gaussian
