/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Assembly.RuminIntegral

/-!
# The exact Rumin coefficient

The real coefficient obtained after inserting the three-dimensional low-momentum volume is the
real value of the coefficient.

Exact equality between the coefficient emitted by scalar Rumin integration and the extended
nonnegative coefficient.
-/

public section

open scoped ENNReal NNReal

namespace LiebThirring

/-- The real coefficient obtained after inserting the three-dimensional
low-momentum volume is the real value of the coefficient. -/
theorem ruminCoefficient_real_eq (q : ℕ) (hq : 1 ≤ q) :
    (9 / 35 : ℝ) *
        (((q : ℝ) * (1 / (6 * Real.pi ^ 2))) ^ (-(2 : ℝ) / 3)) =
      (ruminConstant : ℝ) * (q : ℝ) ^ (-(2 : ℝ) / 3) := by
  have hqpos : 0 < (q : ℝ) := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hq)
  have hcpos : 0 < (6 * Real.pi ^ 2 : ℝ) := by positivity
  have hbase : 0 < (9 / 35 : ℝ) * (6 * Real.pi ^ 2) ^ ((2 : ℝ) / 3) :=
    mul_pos (by norm_num) (Real.rpow_pos_of_pos hcpos _)
  unfold ruminConstant
  rw [Real.coe_toNNReal _ hbase.le]
  have hc : (1 / (6 * Real.pi ^ 2 : ℝ)) ^ (-(2 : ℝ) / 3) =
      (6 * Real.pi ^ 2 : ℝ) ^ ((2 : ℝ) / 3) := by
    rw [one_div, Real.inv_rpow] <;> try positivity
    rw [← Real.rpow_neg hcpos.le]
    congr 1
    ring
  rw [Real.mul_rpow hqpos.le (one_div_nonneg.mpr hcpos.le), hc]
  ring

/-- Exact equality between the coefficient emitted by scalar Rumin integration and the extended
nonnegative coefficient. -/
theorem ofReal_ruminCoefficient_eq (q : ℕ) (hq : 1 ≤ q) :
    ENNReal.ofReal ((9 / 35 : ℝ) *
        (((q : ℝ) * (1 / (6 * Real.pi ^ 2))) ^ (-(2 : ℝ) / 3))) =
      (ruminConstant : ℝ≥0∞) * (q : ℝ≥0∞) ^ (-(2 : ℝ) / 3) := by
  rw [ruminCoefficient_real_eq q hq]
  have hqpos : 0 < (q : ℝ) := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hq)
  rw [ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_rpow_of_pos hqpos, ENNReal.ofReal_natCast]

end LiebThirring

end
