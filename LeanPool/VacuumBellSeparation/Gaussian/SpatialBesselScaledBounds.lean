/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.SpatialBesselIntegral
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Uniform scaled bounds for the literal Bessel integrals

The constants three and eight are the source constants. The proofs use
the actual positive-half-line integrals and keep x>0 explicit.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

theorem scaled_bessel_sqrt {x : ℝ} (hx : 0 < x) :
    x * Real.sqrt (Real.pi / (2 * x)) = Real.sqrt (Real.pi * x / 2) := by
  apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
  rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  field_simp


theorem bessel_sqrt_le {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt (Real.pi * x / 2) ≤ 2 * Real.sqrt (1 + x) := by
  have hleft := Real.sq_sqrt (show 0 ≤ Real.pi * x / 2 by positivity)
  have hright := Real.sq_sqrt (show 0 ≤ 1 + x by positivity)
  have hnleft := Real.sqrt_nonneg (Real.pi * x / 2)
  have hnright := Real.sqrt_nonneg (1 + x)
  have hpi := mul_le_mul_of_nonneg_right Real.pi_lt_four.le hx
  nlinarith

theorem one_le_sqrt_one_add {x : ℝ} (hx : 0 ≤ x) :
    1 ≤ Real.sqrt (1 + x) := by
  have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + x by linarith)
  simpa only [Real.sqrt_one] using h

theorem modifiedBesselIntegral_one_scaled_le {x : ℝ} (hx : 0 < x) :
    x * modifiedBesselIntegral 1 x ≤ 3 * Real.sqrt (1 + x) * Real.exp (-x) := by
  calc
    x * modifiedBesselIntegral 1 x ≤
        x * (Real.exp (-x) * (x⁻¹ + Real.sqrt (Real.pi / (2 * x)))) :=
      mul_le_mul_of_nonneg_left (modifiedBesselIntegral_one_le hx) hx.le
    _ = (1 + Real.sqrt (Real.pi * x / 2)) * Real.exp (-x) := by
      calc
        _ = (x * x⁻¹ + x * Real.sqrt (Real.pi / (2 * x))) * Real.exp (-x) := by ring
        _ = _ := by rw [mul_inv_cancel₀ hx.ne', scaled_bessel_sqrt hx]
    _ ≤ 3 * Real.sqrt (1 + x) * Real.exp (-x) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      linarith [bessel_sqrt_le hx.le, one_le_sqrt_one_add hx.le]

theorem modifiedBesselIntegral_two_scaled_le {x : ℝ} (hx : 0 < x) :
    x ^ 2 * modifiedBesselIntegral 2 x ≤
      8 * (1 + x) * Real.sqrt (1 + x) * Real.exp (-x) := by
  calc
    x ^ 2 * modifiedBesselIntegral 2 x ≤ x ^ 2 * (Real.exp (-x) *
        (2 * (x ^ 2)⁻¹ + 4 * x⁻¹ + Real.sqrt (Real.pi / (2 * x)))) :=
      mul_le_mul_of_nonneg_left (modifiedBesselIntegral_two_le hx) (sq_nonneg _)
    _ = (2 + 4 * x + x * Real.sqrt (Real.pi * x / 2)) * Real.exp (-x) := by
      calc
        _ = (2 * (x ^ 2 * (x ^ 2)⁻¹) + 4 * x * (x * x⁻¹) +
            x * (x * Real.sqrt (Real.pi / (2 * x)))) * Real.exp (-x) := by ring
        _ = _ := by rw [mul_inv_cancel₀ (pow_ne_zero _ hx.ne'),
          mul_inv_cancel₀ hx.ne', scaled_bessel_sqrt hx]; ring
    _ ≤ 8 * (1 + x) * Real.sqrt (1 + x) * Real.exp (-x) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      have ht := one_le_sqrt_one_add hx.le
      have hxt := mul_le_mul_of_nonneg_left ht hx.le
      have hxs := mul_le_mul_of_nonneg_left (bessel_sqrt_le hx.le) hx.le
      nlinarith

theorem modifiedBesselIntegral_two_scaled_rpow_le {x : ℝ} (hx : 0 < x) :
    x ^ 2 * modifiedBesselIntegral 2 x ≤
      8 * (1 + x) ^ (3 / 2 : ℝ) * Real.exp (-x) := by
  have heq : (1 + x) ^ (3 / 2 : ℝ) = (1 + x) * Real.sqrt (1 + x) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add (by positivity), Real.rpow_one, ← Real.sqrt_eq_rpow]
  simpa only [heq, mul_assoc] using modifiedBesselIntegral_two_scaled_le hx

end VacuumBellSeparation.Gaussian
