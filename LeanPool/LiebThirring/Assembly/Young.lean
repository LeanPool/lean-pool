/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic.Positivity

/-!
# Extended Young inequality for screening

Positivity of the finite screening coefficient in extended Young.

The exact additive extended Young bound of extended Young.
-/

public section

open scoped ENNReal

namespace LiebThirring.Assembly

private theorem young_first_coefficient (κ : ℝ) (hκ : 0 < κ) :
    ((5 * κ / 3) ^ ((3 : ℝ) / 5)) ^ ((5 : ℝ) / 3) / ((5 : ℝ) / 3) = κ := by
  have hbase : 0 ≤ 5 * κ / 3 := by positivity
  rw [← Real.rpow_mul hbase]
  norm_num
  ring

private theorem young_second_coefficient (κ : ℝ) (hκ : 0 < κ) :
    (((5 * κ / 3) ^ ((3 : ℝ) / 5))⁻¹) ^ ((5 : ℝ) / 2) / ((5 : ℝ) / 2) =
      (2 / 5 : ℝ) * (3 / 5 : ℝ) ^ ((3 : ℝ) / 2) * κ ^ (-(3 : ℝ) / 2) := by
  have hbase : 0 ≤ 5 * κ / 3 := by positivity
  have hc : 0 ≤ (5 * κ / 3) ^ ((3 : ℝ) / 5) := Real.rpow_nonneg hbase _
  rw [Real.inv_rpow hc, ← Real.rpow_mul hbase, ← Real.rpow_neg hbase]
  norm_num
  have he : (5 * κ / 3 : ℝ) = (5 / 3 : ℝ) * κ := by ring
  rw [he, Real.mul_rpow (by norm_num) hκ.le]
  rw [Real.rpow_neg_eq_inv_rpow]
  norm_num
  ring

/-- Positivity of the finite screening coefficient in extended Young. -/
theorem young_screening_coefficient_pos (κ : ℝ) (hκ : 0 < κ) :
    0 < (2 / 5 : ℝ) * (3 / 5 : ℝ) ^ ((3 : ℝ) / 2) * κ ^ (-(3 : ℝ) / 2) := by
  exact mul_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _))
    (Real.rpow_pos_of_pos hκ _)

/-- The exact additive extended Young bound of extended Young. -/
theorem young_screening (κ : ℝ) (hκ : 0 < κ) (w t : ℝ≥0∞) :
    w * t ≤ ENNReal.ofReal κ * t ^ ((5 : ℝ) / 3) +
      ENNReal.ofReal ((2 / 5 : ℝ) * (3 / 5 : ℝ) ^ ((3 : ℝ) / 2) *
        κ ^ (-(3 : ℝ) / 2)) * w ^ ((5 : ℝ) / 2) := by
  let c : ℝ := (5 * κ / 3) ^ ((3 : ℝ) / 5)
  have hc : 0 < c := Real.rpow_pos_of_pos (by positivity) _
  have hc0 : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.mpr hc).ne'
  have hcinv : 0 < c⁻¹ := inv_pos.mpr hc
  have hpq : ((5 : ℝ) / 3).HolderConjugate ((5 : ℝ) / 2) := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hy := ENNReal.young_inequality (ENNReal.ofReal c * t)
    ((ENNReal.ofReal c)⁻¹ * w) hpq
  have hleft : (ENNReal.ofReal c * t) * ((ENNReal.ofReal c)⁻¹ * w) = w * t := by
    calc
      _ = (ENNReal.ofReal c * (ENNReal.ofReal c)⁻¹) * (w * t) := by ac_rfl
      _ = w * t := by rw [ENNReal.mul_inv_cancel hc0 ENNReal.ofReal_ne_top, one_mul]
  rw [hleft, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)] at hy
  have hfirst : (ENNReal.ofReal c) ^ ((5 : ℝ) / 3) / ENNReal.ofReal ((5 : ℝ) / 3) =
      ENNReal.ofReal κ := by
    rw [ENNReal.ofReal_rpow_of_pos hc, ← ENNReal.ofReal_div_of_pos (by norm_num)]
    exact congrArg ENNReal.ofReal (young_first_coefficient κ hκ)
  have hsecond : ((ENNReal.ofReal c)⁻¹) ^ ((5 : ℝ) / 2) /
      ENNReal.ofReal ((5 : ℝ) / 2) =
      ENNReal.ofReal ((2 / 5 : ℝ) * (3 / 5 : ℝ) ^ ((3 : ℝ) / 2) *
        κ ^ (-(3 : ℝ) / 2)) := by
    rw [← ENNReal.ofReal_inv_of_pos hc, ENNReal.ofReal_rpow_of_pos hcinv,
      ← ENNReal.ofReal_div_of_pos (by norm_num)]
    exact congrArg ENNReal.ofReal (young_second_coefficient κ hκ)
  rw [ENNReal.mul_div_right_comm, ENNReal.mul_div_right_comm, hfirst, hsecond] at hy
  exact hy

end LiebThirring.Assembly

end
