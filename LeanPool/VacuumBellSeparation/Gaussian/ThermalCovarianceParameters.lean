/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.QuadratureNormalization
public import LeanPool.VacuumBellSeparation.Gaussian.MultiModeThermalDensity

/-!
# Actual thermal densities from admissible mode covariances

The scalar inverse of `v(q)=(1+q)/(2(1-q))` is defined explicitly. For every
mode variance at least `1/2`, it gives a genuine convergent thermal density
on the full multi-index oscillator space. Pure modes are retained; strict
variance inequalities imply injectivity, without a bounded inverse claim.
This constructs the product density, not its general symplectic transport.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

/-- Covariance thermal parameter given by `(2 * v - 1) / (2 * v + 1)`. -/
noncomputable def covarianceThermalParameter (v : ℝ) : ℝ := (2 * v - 1) / (2 * v + 1)

theorem covarianceThermalParameter_nonneg {v : ℝ} (hv : 1 / 2 ≤ v) :
    0 ≤ covarianceThermalParameter v := by
  unfold covarianceThermalParameter
  apply div_nonneg <;> linarith

theorem covarianceThermalParameter_lt_one {v : ℝ} (hv : 1 / 2 ≤ v) :
    covarianceThermalParameter v < 1 := by
  unfold covarianceThermalParameter
  rw [div_lt_one (by linarith : 0 < 2 * v + 1)]
  linarith

theorem covarianceThermalParameter_pos {v : ℝ} (hv : 1 / 2 < v) :
    0 < covarianceThermalParameter v := by
  unfold covarianceThermalParameter
  apply div_pos <;> linarith

theorem covarianceThermalParameter_half : covarianceThermalParameter (1 / 2) = 0 := by
  norm_num [covarianceThermalParameter]

theorem thermalQuadratureVariance_covarianceParameter {v : ℝ} (hv : 1 / 2 ≤ v) :
    thermalQuadratureVariance (covarianceThermalParameter v) = v := by
  have hd : 2 * v + 1 ≠ 0 := by linarith
  have hq : 1 - covarianceThermalParameter v ≠ 0 :=
    ne_of_gt (sub_pos.mpr (covarianceThermalParameter_lt_one hv))
  unfold thermalQuadratureVariance
  apply (div_eq_iff (mul_ne_zero (by norm_num) hq)).mpr
  unfold covarianceThermalParameter
  field_simp [hd]
  ring

theorem covarianceThermalParameter_variance {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1) :
    covarianceThermalParameter (thermalQuadratureVariance q) = q :=
  thermalQuadratureVariance_parameter hq₀ hq₁

/-- Continuous linear map for the covariance product density, of type `MultiModeOscillatorSpace m
→L[ℂ] MultiModeOscillatorSpace m`. -/
noncomputable def covarianceProductDensity {m : ℕ} (ν : Fin m → ℝ) :
    MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m :=
  multiModeThermalDensity (fun i => covarianceThermalParameter (ν i))

theorem covarianceProductDensity_nonneg {m : ℕ} {ν : Fin m → ℝ}
    (hν : ∀ i, 1 / 2 ≤ ν i) : 0 ≤ covarianceProductDensity ν :=
  multiModeThermalDensity_nonneg (fun i => covarianceThermalParameter_nonneg (hν i))
    (fun i => covarianceThermalParameter_lt_one (hν i))

theorem positiveTrace_covarianceProductDensity {m : ℕ} {ν : Fin m → ℝ}
    (hν : ∀ i, 1 / 2 ≤ ν i) : positiveTrace (covarianceProductDensity ν) = 1 :=
  positiveTrace_multiModeThermalDensity (fun i => covarianceThermalParameter_nonneg (hν i))
    (fun i => covarianceThermalParameter_lt_one (hν i))

theorem covarianceProductDensity_isFaithfulDensity {m : ℕ} {ν : Fin m → ℝ}
    (hν : ∀ i, 1 / 2 < ν i) : IsFaithfulDensity (covarianceProductDensity ν) :=
  multiModeThermalDensity_isFaithfulDensity (fun i => covarianceThermalParameter_pos (hν i))
    (fun i => covarianceThermalParameter_lt_one (hν i).le)

end VacuumBellSeparation.Gaussian
