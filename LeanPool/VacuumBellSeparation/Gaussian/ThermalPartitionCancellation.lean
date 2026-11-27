/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.NormalizedDensityPowers
public import LeanPool.VacuumBellSeparation.Gaussian.QuantumModePositivity
public import LeanPool.VacuumBellSeparation.Gaussian.ThermalDensityCharacteristic

/-!
# Cancellation of actual thermal partition functions

The true CFC identity (σ^a)^r=σ when ar=1 and the genuine trace-one
normalization prove the cancellation used in the Gaussian Rényi bound.
All traces are finite and strictly positive before taking logarithms.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix

variable {m : ℕ} {q : Fin m → ℝ} {a r : ℝ}

theorem positiveTrace_multiModeThermalDensity_rpow_pos_finite
    (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∀ j, q j < 1) (ha : 0 < a) :
    0 < positiveTrace (multiModeThermalDensity q ^ a) ∧
      positiveTrace (multiModeThermalDensity q ^ a) < ⊤ := by
  rw [positiveTrace_multiModeThermalDensity_rpow hq₀ hq₁ ha]
  exact ⟨ENNReal.ofReal_pos.mpr (multiThermalPowerTrace_pos hq₀ hq₁ ha),
    ENNReal.ofReal_lt_top⟩

theorem normalizedPositiveDensity_thermal_power
    (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∀ j, q j < 1) (ha : 0 < a) :
    normalizedPositiveDensity (multiModeThermalDensity q ^ a) =
      multiModeThermalDensity (fun j => q j ^ a) :=
  normalizedMultiThermalPower_eq_density hq₀ hq₁ ha

theorem normalizedPositiveDensity_thermal_power_characteristic
    (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∀ j, q j < 1) (ha : 0 < a) :
    HasGaussianPhysicalCharacteristic
      (normalizedPositiveDensity (multiModeThermalDensity q ^ a))
      (thermalPowerCovariance q a) := by
  rw [normalizedPositiveDensity_thermal_power hq₀ hq₁ ha]
  exact multiModeThermalDensity_hasGaussianPhysicalCharacteristic
    (fun j => Real.rpow_nonneg (hq₀ j) _) (fun j => Real.rpow_lt_one (hq₀ j) (hq₁ j) ha)

theorem thermalPowerCovariance_partition_cancellation
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1)
    (ha : 0 < a) (hr : 0 < r) (har : a * r = 1) :
    r * Real.log (positiveTrace (multiModeThermalDensity q ^ a)).toReal +
      covariancePurityTrace r (thermalPowerCovariance q a) = 0 := by
  have htc := multiModeThermalDensity_rpow_isPositiveTraceClass (fun j => (hq₀ j).le) hq₁ ha
  have ht := positiveTrace_multiModeThermalDensity_rpow_pos_finite (fun j => (hq₀ j).le) hq₁ ha
  have hntc := normalizedPositiveDensity_isPositiveTraceClass (multiModeNumberBasis m) htc
  have hT := thermalPowerCovariance_posDef (fun j => (hq₀ j).le) hq₁ ha
  have hQ := thermalPowerCovariance_quantum_posDef hq₀ hq₁ ha
  have hG := normalizedPositiveDensity_thermal_power_characteristic (fun j => (hq₀ j).le) hq₁ ha
  have hn := gaussianPhysical_rpow_trace_pos_finite_of_strict_quantum hntc hT hQ hG hr
  have h := log_positiveTrace_rpow_normalization (multiModeNumberBasis m) htc ht.1 hr.le hn
  have hp : (multiModeThermalDensity q ^ a) ^ r = multiModeThermalDensity q := by
    rw [CFC.rpow_rpow_of_exponent_nonneg (multiModeThermalDensity q) a r ha.le hr.le
      (multiModeThermalDensity_nonneg (fun j => (hq₀ j).le) hq₁), har,
      CFC.rpow_one _ (multiModeThermalDensity_nonneg (fun j => (hq₀ j).le) hq₁)]
  have hlog := congrArg (fun ρ => Real.log (positiveTrace ρ).toReal) hp
  rw [positiveTrace_multiModeThermalDensity (fun j => (hq₀ j).le) hq₁,
    ENNReal.toReal_one, Real.log_one] at hlog
  have hpurity := log_positiveTrace_gaussianPhysical_rpow_eq_purity hntc hT hQ hG hr
  exact (congrArg (fun x => r * Real.log (positiveTrace (multiModeThermalDensity q ^ a)).toReal + x)
    hpurity.symm).trans (hlog.symm.trans h).symm

end VacuumBellSeparation.Gaussian
