/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Polynomial absorption by a Gaussian

A fixed positive quadratic exponential dominates the fourth power of
one plus the normal height.
-/

public section


noncomputable section

namespace ESS

/-- The fourth-order normal cutoff factor is bounded by a quadratic
exponential (`lem:bu-small-time`). -/
theorem bu_short_fourth_power_le_exp_sq
    (b y : ℝ) (hb : 0 < b) :
    (1 + y) ^ 4 ≤
      (8 * (1 + 4 / b ^ 2)) * Real.exp (b * y ^ 2) := by
  have hsq1 : (1 + y) ^ 2 ≤ 2 * (1 + y ^ 2) := by
    nlinarith only [sq_nonneg (y - 1)]
  have hsq2 : (1 + y ^ 2) ^ 2 ≤ 2 * (1 + y ^ 4) := by
    nlinarith only [sq_nonneg (y ^ 2 - 1)]
  have h4a : ((1 + y) ^ 2) ^ 2 ≤ (2 * (1 + y ^ 2)) ^ 2 :=
    (sq_le_sq₀ (sq_nonneg _) (by positivity)).2 hsq1
  have hpoly : (1 + y) ^ 4 ≤ 8 * (1 + y ^ 4) := by
    nlinarith only [h4a, hsq2]
  let t := b * y ^ 2 / 2
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hExp : t ≤ Real.exp t := by
    have h := Real.add_one_le_exp t
    linarith only [h]
  have hExpSq : t ^ 2 ≤ (Real.exp t) ^ 2 :=
    (sq_le_sq₀ ht (Real.exp_nonneg _)).2 hExp
  have hExpEq : (Real.exp t) ^ 2 = Real.exp (b * y ^ 2) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    dsimp [t]
    ring
  have hY4Exp : b ^ 2 * y ^ 4 / 4 ≤ Real.exp (b * y ^ 2) := by
    rw [← hExpEq]
    convert hExpSq using 1
    dsimp [t]
    ring
  have hCoef : 0 ≤ 4 / b ^ 2 := by positivity
  have hScaled := mul_le_mul_of_nonneg_left hY4Exp hCoef
  have hCancel : (4 / b ^ 2) * (b ^ 2 * y ^ 4 / 4) = y ^ 4 := by
    field_simp
  rw [hCancel] at hScaled
  have hOne : 1 ≤ Real.exp (b * y ^ 2) := by
    have h := Real.add_one_le_exp (b * y ^ 2)
    have hby : 0 ≤ b * y ^ 2 := by positivity
    linarith only [h, hby]
  have hsum : 1 + y ^ 4 ≤
      (1 + 4 / b ^ 2) * Real.exp (b * y ^ 2) := by
    calc
      _ ≤ Real.exp (b * y ^ 2) +
          (4 / b ^ 2) * Real.exp (b * y ^ 2) := add_le_add hOne hScaled
      _ = _ := by ring
  calc
    _ ≤ 8 * (1 + y ^ 4) := hpoly
    _ ≤ (8 * (1 + 4 / b ^ 2)) * Real.exp (b * y ^ 2) := by
      have := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 8)
      nlinarith only [this]

end ESS
