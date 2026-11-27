/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.ThermalSandwichCriterion
public import LeanPool.VacuumBellSeparation.Gaussian.QuadratureNormalization

/-!
# Normalized commuting thermal sandwich and its covariance threshold

The bounded inverse-power sandwich normalizes to the actual thermal
density at parameter `p/q^τ`. The sharp trace criterion can therefore be
expressed using the proved real-quadrature covariances. These identities
are on the actual oscillator Hilbert space and retain the endpoint `p=0`.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap

/-- Continuous linear map for the normalized thermal sandwich, of type `OscillatorSpace →L[ℂ]
OscillatorSpace`. -/
noncomputable def normalizedThermalSandwich (p q τ : ℝ) :
    OscillatorSpace →L[ℂ] OscillatorSpace :=
  (positiveTrace (thermalSandwich p q τ)).toReal⁻¹ • thermalSandwich p q τ

theorem thermalSandwich_traceValue_pos {p q τ : ℝ}
    (hp₁ : p < 1) (hq₀ : 0 < q) (hq₁ : q < 1) (hpq : p < q ^ τ) :
    0 < ((1 - p) / (1 - q) ^ τ) / (1 - p / q ^ τ) := by
  have hqτ : 0 < q ^ τ := Real.rpow_pos_of_pos hq₀ _
  exact div_pos (div_pos (sub_pos.mpr hp₁)
    (Real.rpow_pos_of_pos (sub_pos.mpr hq₁) _))
    (sub_pos.mpr ((div_lt_one hqτ).mpr hpq))

theorem thermalSandwich_eq_scaled_thermalDensity {p q τ : ℝ}
    (hp₀ : 0 ≤ p) (hq₀ : 0 < q) (hq₁ : q < 1) (hpq : p < q ^ τ) :
    thermalSandwich p q τ =
      (((1 - p) / (1 - q) ^ τ) / (1 - p / q ^ τ)) • thermalDensity (p / q ^ τ) := by
  have hqτ : 0 < q ^ τ := Real.rpow_pos_of_pos hq₀ _
  have hr₀ : 0 ≤ p / q ^ τ := div_nonneg hp₀ hqτ.le
  have hr₁ : p / q ^ τ < 1 := (div_lt_one hqτ).mpr hpq
  have hd : 1 - p / q ^ τ ≠ 0 := ne_of_gt (sub_pos.mpr hr₁)
  apply continuousLinearMap_eq_of_hilbertBasis numberBasis
  intro n
  rw [thermalSandwich_apply_numberBasis hp₀ hq₀ hq₁ hpq,
    smul_apply, thermalDensity_apply_numberBasis hr₀ hr₁, smul_smul]
  congr 1
  rw [thermalSandwichWeight_geometric hq₀.le hq₁, thermalWeight]
  rw [← mul_assoc, div_mul_cancel₀ _ hd]

theorem normalizedThermalSandwich_eq_thermalDensity {p q τ : ℝ}
    (hp₀ : 0 ≤ p) (hp₁ : p < 1) (hq₀ : 0 < q) (hq₁ : q < 1)
    (hpq : p < q ^ τ) :
    normalizedThermalSandwich p q τ = thermalDensity (p / q ^ τ) := by
  have hc := thermalSandwich_traceValue_pos hp₁ hq₀ hq₁ hpq
  rw [normalizedThermalSandwich,
    positiveTrace_thermalSandwich hp₀ hp₁ hq₀ hq₁ hpq,
    ENNReal.toReal_ofReal hc.le,
    thermalSandwich_eq_scaled_thermalDensity hp₀ hq₀ hq₁ hpq,
    smul_smul, inv_mul_cancel₀ hc.ne', one_smul]

theorem normalizedThermalSandwich_trace_one {p q τ : ℝ}
    (hp₀ : 0 ≤ p) (hp₁ : p < 1) (hq₀ : 0 < q) (hq₁ : q < 1)
    (hpq : p < q ^ τ) : positiveTrace (normalizedThermalSandwich p q τ) = 1 := by
  rw [normalizedThermalSandwich_eq_thermalDensity hp₀ hp₁ hq₀ hq₁ hpq]
  exact positiveTrace_thermalDensity
    (div_nonneg hp₀ (Real.rpow_pos_of_pos hq₀ τ).le)
    ((div_lt_one (Real.rpow_pos_of_pos hq₀ τ)).mpr hpq)

theorem normalizedThermalSandwich_isFaithfulDensity {p q τ : ℝ}
    (hp₀ : 0 < p) (hp₁ : p < 1) (hq₀ : 0 < q) (hq₁ : q < 1)
    (hpq : p < q ^ τ) : IsFaithfulDensity (normalizedThermalSandwich p q τ) := by
  rw [normalizedThermalSandwich_eq_thermalDensity hp₀.le hp₁ hq₀ hq₁ hpq]
  exact thermalDensity_isFaithfulDensity (div_pos hp₀ (Real.rpow_pos_of_pos hq₀ τ))
    ((div_lt_one (Real.rpow_pos_of_pos hq₀ τ)).mpr hpq)

theorem thermalQuadratureVariance_lt_iff {p r : ℝ} (hp : p < 1) (hr : r < 1) :
    thermalQuadratureVariance p < thermalQuadratureVariance r ↔ p < r := by
  unfold thermalQuadratureVariance
  rw [div_lt_div_iff₀ (mul_pos (by norm_num) (sub_pos.mpr hp))
    (mul_pos (by norm_num) (sub_pos.mpr hr))]
  constructor <;> intro h <;> nlinarith

/-- The exact scalar covariance-gap criterion for the actual commuting
one-mode density factorization. -/
theorem exists_positiveTraceClass_thermal_factorization_iff_covariance {p q τ : ℝ}
    (hp₀ : 0 ≤ p) (hp₁ : p < 1) (hq₀ : 0 < q) (hq₁ : q < 1) (hτ : 0 < τ) :
    (∃ A : OscillatorSpace →L[ℂ] OscillatorSpace,
      IsPositiveTraceClass A ∧
      (thermalDensity q ^ (τ / 2)) * A *
        (thermalDensity q ^ (τ / 2)) = thermalDensity p) ↔
      thermalQuadratureVariance p < thermalQuadratureVariance (q ^ τ) := by
  rw [exists_positiveTraceClass_thermal_factorization_iff hp₀ hp₁ hq₀ hq₁ hτ,
    thermalQuadratureVariance_lt_iff hp₁ (Real.rpow_lt_one hq₀.le hq₁ hτ)]

end VacuumBellSeparation.Gaussian
