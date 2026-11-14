/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.Carrier
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Arithmetic

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Arithmetic for the small-contrast Schauder iteration

This file isolates the numerical part of the small-contrast iteration. In
particular, it retains the author's constants
`2^(-3-d/2)`, `1/8`, and `2^(d/2)` literally, so the analytic modules do not
hide any dependence on the Hölder exponent in a generic constant.
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Ported

noncomputable section

/-- The coefficient-oscillation threshold in the small-contrast estimate. -/
def smallContrastThreshold (d : ℕ) (alpha : ℝ) : ℝ :=
  (2 : ℝ) ^ (-(3 + (d : ℝ) / 2)) * (1 - alpha)

/-- The elementary numerical inequality used to select the contraction
parameter at `theta = 1/2`. -/
theorem one_add_quarter_mul_le_one_sub_eighth_mul_two_rpow
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    1 + x / 4 ≤ (1 - x / 8) * (2 : ℝ) ^ x := by
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
    linarith only [Real.log_two_gt_d9]
  have hxlog : x / 2 ≤ Real.log 2 * x := by
    nlinarith only [hlog, hx0]
  have hexp : Real.log 2 * x + 1 ≤ Real.exp (Real.log 2 * x) :=
    Real.add_one_le_exp _
  have hbase : 1 + x / 2 ≤ (2 : ℝ) ^ x := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith only [hexp, hxlog]
  have hfactor : 0 ≤ 1 - x / 8 := by linarith only [hx1]
  calc
    1 + x / 4 ≤ (1 - x / 8) * (1 + x / 2) := by nlinarith only [hx0, hx1]
    _ ≤ (1 - x / 8) * (2 : ℝ) ^ x :=
      mul_le_mul_of_nonneg_left hbase hfactor

/-- The contraction factor in the printed dyadic iteration. -/
def smallContrastContraction (alpha : ℝ) : ℝ :=
  1 - (1 - alpha) / 8

theorem smallContrastContraction_mem_Ioo {alpha : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1) :
    smallContrastContraction alpha ∈ Set.Ioo 0 1 := by
  constructor
  · simp only [smallContrastContraction]
    linarith only [halpha0, halpha1]
  · simp only [smallContrastContraction]
    linarith only [halpha1]

/-- The reciprocal contraction gap is the displayed `(1-alpha)⁻¹` price. -/
theorem one_sub_smallContrastContraction (alpha : ℝ) :
    1 - smallContrastContraction alpha = (1 - alpha) / 8 := by
  simp [smallContrastContraction]

/-- At `theta = 1/2`, the perturbative coefficient produced by the printed
threshold is exactly `(1-alpha)/4`.  This is the cancellation of the displayed
`2^(-d/2)` and `2^(d/2)` factors. -/
theorem two_mul_smallContrastThreshold_mul_half_rpow (d : ℕ) (alpha : ℝ) :
    2 * smallContrastThreshold d alpha *
        (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) = (1 - alpha) / 4 := by
  have hhalf : (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) =
      (2 : ℝ) ^ ((d : ℝ) / 2) := by
    rw [show -(d : ℝ) / 2 = -((d : ℝ) / 2) by ring,
      Real.rpow_neg_eq_inv_rpow]
    norm_num
  rw [smallContrastThreshold, hhalf]
  rw [show -(3 + (d : ℝ) / 2) = -3 - (d : ℝ) / 2 by ring,
    Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
  have hpow : (0 : ℝ) < (2 : ℝ) ^ ((d : ℝ) / 2) :=
    Real.rpow_pos_of_pos (by norm_num) _
  rw [show (2 : ℝ) ^ (-3 : ℝ) = 1 / 8 by norm_num]
  field_simp
  ring

theorem smallContrastThreshold_nonneg (d : ℕ) {alpha : ℝ} (halpha : alpha ≤ 1) :
    0 ≤ smallContrastThreshold d alpha := by
  exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (sub_nonneg.mpr halpha)

/-- The printed threshold is in particular at most `(1-alpha)/8`. -/
theorem smallContrastThreshold_le_eighth_gap (d : ℕ) {alpha : ℝ}
    (halpha : alpha ≤ 1) :
    smallContrastThreshold d alpha ≤ (1 - alpha) / 8 := by
  have hpow : 1 ≤ (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by norm_num) (by norm_num) (by
      have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
      linarith only [hd])
  have hthreshold := smallContrastThreshold_nonneg d halpha
  have hid := two_mul_smallContrastThreshold_mul_half_rpow d alpha
  have hmul : 2 * smallContrastThreshold d alpha * 1 ≤
      2 * smallContrastThreshold d alpha * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) :=
    mul_le_mul_of_nonneg_left hpow (mul_nonneg (by norm_num) hthreshold)
  rw [mul_one] at hmul
  nlinarith only [hmul, hid]

/-- The corrected coercivity step only needs `delta < 1/2`; the printed
threshold has much more room. -/
theorem smallContrastThreshold_lt_half (d : ℕ) {alpha : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1) :
    smallContrastThreshold d alpha < 1 / 2 := by
  have hle := smallContrastThreshold_le_eighth_gap d halpha1.le
  nlinarith only [hle, halpha0]

/-- The exact `theta = 1/2` contraction in the source.  No constant in this
statement depends on `alpha`: all exponent dependence is visible through
`1-alpha`. -/
theorem dyadic_smallContrast_contraction {d : ℕ} {alpha delta : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hdelta : delta ≤ smallContrastThreshold d alpha) :
    (1 + 2 * delta * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2)) *
        (1 / 2 : ℝ) ^ (1 - alpha) ≤ smallContrastContraction alpha := by
  set x : ℝ := 1 - alpha with hx
  have hx0 : 0 ≤ x := by dsimp [x]; linarith only [halpha1]
  have hx1 : x ≤ 1 := by dsimp [x]; linarith only [halpha0]
  have hvolume : 0 ≤ (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  have hpert :
      1 + 2 * delta * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) ≤ 1 + x / 4 := by
    have hmul := mul_le_mul_of_nonneg_right hdelta hvolume
    have hthreshold := two_mul_smallContrastThreshold_mul_half_rpow d alpha
    dsimp [x]
    rw [← hthreshold]
    linarith only [hmul]
  have htheta : 0 ≤ (1 / 2 : ℝ) ^ x := Real.rpow_nonneg (by norm_num) _
  have hnum := one_add_quarter_mul_le_one_sub_eighth_mul_two_rpow hx0 hx1
  have hcancel : (2 : ℝ) ^ x * (1 / 2 : ℝ) ^ x = 1 := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    norm_num
  calc
    (1 + 2 * delta * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2)) * (1 / 2 : ℝ) ^ x
        ≤ (1 + x / 4) * (1 / 2 : ℝ) ^ x :=
          mul_le_mul_of_nonneg_right hpert htheta
    _ ≤ ((1 - x / 8) * (2 : ℝ) ^ x) * (1 / 2 : ℝ) ^ x :=
      mul_le_mul_of_nonneg_right hnum htheta
    _ = smallContrastContraction alpha := by
      rw [mul_assoc, hcancel, mul_one]
      simp [smallContrastContraction, x]

/-- At the printed contraction, summing the recurrence costs exactly at most
`8 * (1-alpha)⁻¹`. -/
theorem inv_one_sub_smallContrastContraction_le {alpha : ℝ} (halpha : alpha < 1) :
    (1 - smallContrastContraction alpha)⁻¹ ≤ 8 * (1 - alpha)⁻¹ := by
  rw [one_sub_smallContrastContraction]
  have hne : 1 - alpha ≠ 0 := ne_of_gt (sub_pos.mpr halpha)
  have heq : ((1 - alpha) / 8)⁻¹ = 8 * (1 - alpha)⁻¹ := by
    field_simp
  rw [heq]

end

end Algsuperdiff.StochasticProcess.Common.Regularity.Ported
