/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Elementary logarithm comparisons

## Main results

* `Real.log_add_one_le_self`: `Real.log (x + 1) ≤ x` for `0 ≤ x`.
* `Real.natCast_le_of_log_le_log`: a positive natural number is bounded by a positive real once
  their logarithms compare.
* `Real.log_one_add_sub_div_four_le`: `Real.log (1 + x) - x / 4 ≤ Real.log 4 + 1` for `0 ≤ x`.
* `Real.rpow_half_mul_log_add_le`: `√B (log B + D) ≤ (1/ε + D) B^(1/2 + ε)` for `B ≥ 1`, an
  explicit absorption of the logarithm into a power.
-/

@[expose] public section

namespace Real

/-- For nonnegative `x`, `Real.log (x + 1) ≤ x`. -/
theorem log_add_one_le_self {x : ℝ} (hx : 0 ≤ x) : log (x + 1) ≤ x := by
  simpa only [add_sub_cancel_right] using log_le_sub_one_of_pos (by linarith : 0 < x + 1)

/-- A positive natural number is bounded by a positive real once their logarithms compare. -/
theorem natCast_le_of_log_le_log {n : ℕ} {y : ℝ} (hn : 0 < n) (hy : 0 < y)
    (h : log n ≤ log y) : (n : ℝ) ≤ y :=
  (log_le_log_iff (Nat.cast_pos.mpr hn) hy).mp h

/-- The logarithm `log (1 + x)` exceeds `x / 4` by at most `log 4 + 1` for `x ≥ 0`. -/
theorem log_one_add_sub_div_four_le {x : ℝ} (hx : 0 ≤ x) :
    Real.log (1 + x) - x / 4 ≤ Real.log 4 + 1 := by
  have h := Real.log_le_sub_one_of_pos (show 0 < (1 + x) / 4 by positivity)
  rw [Real.log_div (by positivity) (by norm_num)] at h
  linarith

/-- Absorb the logarithm with a specified positive exponent loss and an explicit constant. -/
theorem rpow_half_mul_log_add_le {B ε D : ℝ} (hB : 1 ≤ B) (hε : 0 < ε) (hD : 0 ≤ D) :
    B ^ (1 / 2 : ℝ) * (Real.log B + D) ≤
      (1 / ε + D) * B ^ (1 / 2 + ε : ℝ) := by
  have hB0 : 0 < B := by linarith
  have hp1 : 1 ≤ B ^ ε := Real.one_le_rpow hB hε.le
  have hl := Real.log_le_rpow_div hB0.le hε
  have hd := mul_le_mul_of_nonneg_left hp1 hD
  have hsum : Real.log B + D ≤ (1 / ε + D) * B ^ ε := by
    rw [div_eq_mul_inv] at hl
    simp only [one_div]
    nlinarith
  calc
    _ ≤ B ^ (1 / 2 : ℝ) * ((1 / ε + D) * B ^ ε) :=
      mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hB0.le _)
    _ = _ := by rw [Real.rpow_add hB0]; ring

end Real
