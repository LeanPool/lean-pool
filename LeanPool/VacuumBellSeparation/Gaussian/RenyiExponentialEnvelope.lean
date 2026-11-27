/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.GaussianRenyiConsequences

/-!
# A finite exponential comparison gives an explicit square-root envelope
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open scoped ENNReal

theorem exp_sub_one_le_two_mul {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x - 1 ≤ 2 * x := by
  have h := Real.norm_exp_sub_one_sub_id_le (x := x)
    (by simpa only [Real.norm_eq_abs, abs_of_nonneg hx] using hx1)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hx] at h
  have hu := (abs_le.mp h).2
  nlinarith

theorem renyi_exponential_sqrt_envelope {r x : ℝ}
    (hr : 2 ≤ r) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    (ENNReal.ofReal (Real.exp x) ^ (1 / (r - 1)) - 1) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Real.sqrt (2 * x)) := by
  have hr1 : 0 < r - 1 := by linarith
  have hp0 : 0 ≤ 1 / (r - 1) := by positivity
  have hp1 : 1 / (r - 1) ≤ 1 := (div_le_one hr1).mpr (by linarith)
  have hy : 0 ≤ x * (1 / (r - 1)) := mul_nonneg hx hp0
  have hyx : x * (1 / (r - 1)) ≤ x := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hp1 hx
  have hb : Real.exp (x * (1 / (r - 1))) - 1 ≤ 2 * x :=
    (exp_sub_one_le_two_mul hy (hyx.trans hx1)).trans
      (mul_le_mul_of_nonneg_left hyx (by norm_num))
  have hENN : ENNReal.ofReal (Real.exp x) ^ (1 / (r - 1)) - 1 ≤ ENNReal.ofReal (2 * x) := by
    rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul,
      ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by norm_num : (0 : ℝ) ≤ 1)]
    exact ENNReal.ofReal_le_ofReal hb
  apply (ENNReal.rpow_le_rpow hENN (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans_eq
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow]

theorem sqrt_forward_envelope {r A s : ℝ} (hr : 0 ≤ r) (hA : 0 ≤ A) (hs : 0 < s) :
    Real.sqrt (2 * (8 * r * (A / s ^ 2))) = (4 * Real.sqrt (r * A)) / s := by
  rw [show 2 * (8 * r * (A / s ^ 2)) = 16 * (r * A) / s ^ 2 by ring,
    Real.sqrt_div (by positivity), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16), Real.sqrt_sq hs.le]
  have h16 : Real.sqrt (16 : ℝ) = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h16]

end VacuumBellSeparation.Gaussian
