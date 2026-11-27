/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.ThermalPowerNormalization
public import LeanPool.VacuumBellSeparation.Gaussian.ThermalOperator

/-!
# Canonical density powers and the manuscript's thermal increment

The actual normalized density power has parameter `q^τ`. This file relates
its proved quadrature covariance to the existing manuscript scalar
function `thermalIncrement`, at `d=1/(2v)`. The pure endpoint `q=0,d=1`
is retained. General finite-dimensional Gaussian transport is separate.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

/-- Thermal commutation magnitude given by `(1 - q) / (1 + q)`. -/
noncomputable def thermalCommutationMagnitude (q : ℝ) : ℝ := (1 - q) / (1 + q)

theorem thermalCommutationMagnitude_pos {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1) :
    0 < thermalCommutationMagnitude q :=
  div_pos (sub_pos.mpr hq₁) (by linarith)

theorem thermalCommutationMagnitude_le_one {q : ℝ} (hq₀ : 0 ≤ q) :
    thermalCommutationMagnitude q ≤ 1 := by
  unfold thermalCommutationMagnitude
  rw [div_le_one (by linarith : 0 < 1 + q)]
  linarith

theorem thermalCommutationMagnitude_eq_inv_twice_variance {q : ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q < 1) :
    thermalCommutationMagnitude q = (2 * thermalQuadratureVariance q)⁻¹ := by
  unfold thermalCommutationMagnitude thermalQuadratureVariance
  field_simp [ne_of_gt (sub_pos.mpr hq₁), ne_of_gt (show 0 < 1 + q by linarith)]

/-- The manuscript's thermal increment `H_τ(I) = d coth(τ artanh d) - I`, as the scalar function
`thermalIncrement τ d`, is exactly the relative change of the covariance under the proved
normalized actual density power. -/
theorem thermalIncrement_eq_relative_covariance {q τ : ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q < 1) (hτ : 0 < τ) :
    thermalIncrement τ (thermalCommutationMagnitude q) =
      thermalQuadratureVariance (q ^ τ) / thermalQuadratureVariance q - 1 := by
  let d := thermalCommutationMagnitude q
  have hd₀ : 0 < d := thermalCommutationMagnitude_pos hq₀ hq₁
  have hd₁ : d ≤ 1 := thermalCommutationMagnitude_le_one hq₀
  have hqd : 1 - d = q * (1 + d) := by
    dsimp [d, thermalCommutationMagnitude]
    field_simp [ne_of_gt (show 0 < 1 + q by linarith)]
    ring
  have hp : (1 - d) ^ τ = q ^ τ * (1 + d) ^ τ := by
    rw [hqd, Real.mul_rpow hq₀ (by linarith : 0 ≤ 1 + d)]
  have ha : (1 + d) ^ τ ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (by linarith) τ)
  have hratio : ((1 + d) ^ τ + (1 - d) ^ τ) /
      ((1 + d) ^ τ - (1 - d) ^ τ) = (1 + q ^ τ) / (1 - q ^ τ) := by
    rw [hp]
    calc
      ((1 + d) ^ τ + q ^ τ * (1 + d) ^ τ) /
          ((1 + d) ^ τ - q ^ τ * (1 + d) ^ τ) =
          ((1 + q ^ τ) * (1 + d) ^ τ) / ((1 - q ^ τ) * (1 + d) ^ τ) := by ring
      _ = _ := mul_div_mul_right _ _ ha
  rw [thermalIncrement_eq_of_pos hτ hd₀ hd₁, hratio]
  dsimp [d, thermalCommutationMagnitude, thermalQuadratureVariance]
  have hqτ : 1 - q ^ τ ≠ 0 := ne_of_gt (sub_pos.mpr (Real.rpow_lt_one hq₀ hq₁ hτ))
  field_simp [ne_of_gt (sub_pos.mpr hq₁), ne_of_gt (show 0 < 1 + q by linarith), hqτ]

theorem relative_thermal_covariance_comparison {q τ : ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q < 1) (hτ₀ : 0 < τ) (hτ₁ : τ < 1) :
    thermalConst τ * (1 - thermalCommutationMagnitude q ^ 2) ^ τ ≤
      thermalQuadratureVariance (q ^ τ) / thermalQuadratureVariance q - 1 := by
  rw [← thermalIncrement_eq_relative_covariance hq₀ hq₁ hτ₀]
  exact thermalIncrement_ge hτ₀ hτ₁
    ⟨(thermalCommutationMagnitude_pos hq₀ hq₁).le, thermalCommutationMagnitude_le_one hq₀⟩

end VacuumBellSeparation.Gaussian
