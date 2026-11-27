/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.ThermalPowerNormalizationDefs
public import LeanPool.VacuumBellSeparation.Gaussian.ThermalCoherentPowers
public import LeanPool.VacuumBellSeparation.Gaussian.QuadratureNormalization

/-!
# Normalized actual positive powers of the thermal density

Normalizing the genuine positive CFC power by its actual finite positive
trace gives the thermal density at parameter `q^τ`. This is an operator
identity on ℓ², including the pure endpoint, and yields the corresponding
real-quadrature covariance transformation.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap

theorem thermalPowerTrace_pos {q τ : ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q < 1) (hτ : 0 < τ) :
    0 < (1 - q) ^ τ / (1 - q ^ τ) :=
  div_pos (Real.rpow_pos_of_pos (sub_pos.mpr hq₁) _)
    (sub_pos.mpr (Real.rpow_lt_one hq₀ hq₁ hτ))

theorem normalizedThermalPower_eq_thermalDensity {q τ : ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q < 1) (hτ : 0 < τ) :
    normalizedThermalPower q τ = thermalDensity (q ^ τ) := by
  have hp₀ : 0 ≤ q ^ τ := Real.rpow_nonneg hq₀ _
  have hp₁ : q ^ τ < 1 := Real.rpow_lt_one hq₀ hq₁ hτ
  have hc : (1 - q) ^ τ ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (sub_pos.mpr hq₁) _)
  have hd : 1 - q ^ τ ≠ 0 := ne_of_gt (sub_pos.mpr hp₁)
  have hscalar (n : ℕ) : ((1 - q) ^ τ / (1 - q ^ τ))⁻¹ * thermalWeight q n ^ τ =
      thermalWeight (q ^ τ) n := by
    rw [thermalWeight_rpow hq₀ hq₁, thermalWeight]
    field_simp [hc, hd]
  unfold normalizedThermalPower
  rw [positiveTrace_thermalDensity_rpow hq₀ hq₁ hτ,
    ENNReal.toReal_ofReal (thermalPowerTrace_pos hq₀ hq₁ hτ).le]
  apply ContinuousLinearMap.ext_on
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr numberBasis.dense_span)
  rintro _ ⟨n, rfl⟩
  rw [smul_apply, thermalDensity_rpow_apply_numberBasis hq₀ hq₁ hτ,
    smul_smul, hscalar, thermalDensity_apply_numberBasis hp₀ hp₁]

theorem normalizedThermalPower_isFaithfulDensity {q τ : ℝ}
    (hq₀ : 0 < q) (hq₁ : q < 1) (hτ : 0 < τ) :
    IsFaithfulDensity (normalizedThermalPower q τ) := by
  rw [normalizedThermalPower_eq_thermalDensity hq₀.le hq₁ hτ]
  exact thermalDensity_isFaithfulDensity (Real.rpow_pos_of_pos hq₀ _)
    (Real.rpow_lt_one hq₀.le hq₁ hτ)

theorem normalizedThermalPower_trace_one {q τ : ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q < 1) (hτ : 0 < τ) :
    positiveTrace (normalizedThermalPower q τ) = 1 := by
  rw [normalizedThermalPower_eq_thermalDensity hq₀ hq₁ hτ]
  exact positiveTrace_thermalDensity (Real.rpow_nonneg hq₀ _)
    (Real.rpow_lt_one hq₀ hq₁ hτ)

theorem thermalPower_quadrature_characteristic {q τ : ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q < 1) (hτ : 0 < τ) (v : ℝ × ℝ) :
    thermalState (Real.rpow_nonneg hq₀ τ) (Real.rpow_lt_one hq₀ hq₁ hτ)
      (quadratureWeyl v) =
        Complex.exp (((-((1 + q ^ τ) / (4 * (1 - q ^ τ))) *
          (v.1 ^ 2 + v.2 ^ 2) : ℝ) : ℂ)) := by
  rw [thermalState_quadratureWeyl, thermalQuadratureVariance]
  have hden : (2 * (1 - q ^ τ)) * 2 = 4 * (1 - q ^ τ) := by ring
  rw [div_div, hden]

end VacuumBellSeparation.Gaussian
