/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.PhysicalWilliamsonDensity
public import LeanPool.VacuumBellSeparation.Gaussian.PurityScalar

/-!
# The actual Gaussian power trace in manuscript purity coordinates

This identifies the actual positive trace of a genuine CFC power with the
product of the source factors fᵣ(ν)⁻¹. The pure boundary ν = 1/2 and the
zero-mode product are included. Positivity and finiteness precede taking
the real logarithm. No eigenvalue differentiability is assumed here.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix

theorem covarianceThermalParameter_half_ratio {v : ℝ} (hv : 1 / 2 ≤ v) :
    covarianceThermalParameter v = (v - 1 / 2) / (v + 1 / 2) := by
  have hp : v + 1 / 2 ≠ 0 := by linarith
  have hq : 2 * v + 1 ≠ 0 := by linarith
  unfold covarianceThermalParameter
  field_simp [hp, hq]

theorem one_sub_covarianceThermalParameter {v : ℝ} (hv : 1 / 2 ≤ v) :
    1 - covarianceThermalParameter v = (v + 1 / 2)⁻¹ := by
  rw [covarianceThermalParameter_half_ratio hv]
  have hp : v + 1 / 2 ≠ 0 := by linarith
  field_simp [hp]
  ring

theorem thermalPowerTrace_covariance_eq_inv_purityFactor
    {r v : ℝ} (hr : 0 < r) (hv : 1 / 2 ≤ v) :
    (1 - covarianceThermalParameter v) ^ r /
        (1 - covarianceThermalParameter v ^ r) = (purityFactor r v)⁻¹ := by
  have hp : 0 < (v + 1 / 2) ^ r := Real.rpow_pos_of_pos (by linarith) _
  have hd : 0 < (v + 1 / 2) ^ r - (v - 1 / 2) ^ r := purityFactor_pos hr hv
  have hden : 1 - (v - 1 / 2) ^ r / (v + 1 / 2) ^ r ≠ 0 := by
    rw [← Real.div_rpow (by linarith : 0 ≤ v - 1 / 2) (by linarith : 0 ≤ v + 1 / 2),
      ← covarianceThermalParameter_half_ratio hv]
    exact ne_of_gt (sub_pos.mpr (Real.rpow_lt_one (covarianceThermalParameter_nonneg hv)
      (covarianceThermalParameter_lt_one hv) hr))
  rw [one_sub_covarianceThermalParameter hv, Real.inv_rpow (by linarith : 0 ≤ v + 1 / 2),
    covarianceThermalParameter_half_ratio hv,
    Real.div_rpow (by linarith : 0 ≤ v - 1 / 2) (by linarith : 0 ≤ v + 1 / 2), purityFactor]
  field_simp [hp.ne', hd.ne', hden]

/-- Gaussian purity product given by `∏ j, (purityFactor r (ν j))⁻¹`. -/
def gaussianPurityProduct {m : ℕ} (r : ℝ) (ν : Fin m → ℝ) : ℝ :=
  ∏ j, (purityFactor r (ν j))⁻¹

theorem gaussianPurityProduct_pos {m : ℕ} {r : ℝ} {ν : Fin m → ℝ}
    (hr : 0 < r) (hν : ∀ j, 1 / 2 ≤ ν j) : 0 < gaussianPurityProduct r ν :=
  Finset.prod_pos fun j _ => inv_pos.mpr (purityFactor_pos hr (hν j))

variable {m : ℕ}

/-- The source product formula for the trace of the actual Gaussian power. -/
theorem positiveTrace_gaussianPhysical_rpow_purity
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A)
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    {ν : Fin m → ℝ} (hν : ∀ j, 1 / 2 ≤ ν j)
    (hG : HasGaussianPhysicalCharacteristic A (S * modeDiagonal ν * Sᵀ))
    {r : ℝ} (hr : 0 < r) :
    positiveTrace (A ^ r) = ENNReal.ofReal (gaussianPurityProduct r ν) := by
  rw [positiveTrace_gaussianPhysical_rpow hA S hS hν hG hr]
  congr 1
  exact Finset.prod_congr rfl fun j _ => thermalPowerTrace_covariance_eq_inv_purityFactor hr (hν j)

theorem gaussianPhysical_rpow_trace_pos_finite
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A)
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    {ν : Fin m → ℝ} (hν : ∀ j, 1 / 2 ≤ ν j)
    (hG : HasGaussianPhysicalCharacteristic A (S * modeDiagonal ν * Sᵀ))
    {r : ℝ} (hr : 0 < r) :
    0 < positiveTrace (A ^ r) ∧ positiveTrace (A ^ r) < ⊤ := by
  rw [positiveTrace_gaussianPhysical_rpow_purity hA S hS hν hG hr]
  exact ⟨ENNReal.ofReal_pos.mpr (gaussianPurityProduct_pos hr hν), ENNReal.ofReal_lt_top⟩

theorem log_gaussianPurityProduct {r : ℝ} {ν : Fin m → ℝ}
    (hr : 0 < r) (hν : ∀ j, 1 / 2 ≤ ν j) :
    Real.log (gaussianPurityProduct r ν) = - ∑ j, logPurityFactor r (ν j) := by
  rw [gaussianPurityProduct, Real.log_prod (fun j _ =>
    inv_ne_zero (purityFactor_pos hr (hν j)).ne')]
  simp only [Real.log_inv, logPurityFactor, Finset.sum_neg_distrib]

/-- The real logarithm of a finite strictly positive actual operator trace. -/
theorem log_positiveTrace_gaussianPhysical_rpow
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A)
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    {ν : Fin m → ℝ} (hν : ∀ j, 1 / 2 ≤ ν j)
    (hG : HasGaussianPhysicalCharacteristic A (S * modeDiagonal ν * Sᵀ))
    {r : ℝ} (hr : 0 < r) :
    Real.log (positiveTrace (A ^ r)).toReal = - ∑ j, logPurityFactor r (ν j) := by
  rw [positiveTrace_gaussianPhysical_rpow_purity hA S hS hν hG hr,
    ENNReal.toReal_ofReal (gaussianPurityProduct_pos hr hν).le]
  exact log_gaussianPurityProduct hr hν

end VacuumBellSeparation.Gaussian
