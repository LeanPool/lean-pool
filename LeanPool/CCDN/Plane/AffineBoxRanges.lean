/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Plane.ScaledPlaneCount
import LeanPool.CCDN.ForMathlib.Log

/-! Quantitative large-box and small-box reductions for affine scaling. -/

@[expose] public section
namespace CCDN
open Real

/-- Above a fixed multiple of d², a logarithmic height of B/A is large enough
for the unscaled auxiliary-polynomial branch. -/
lemma large_box_height_threshold {d : ℕ} (hd : 0 < d) {A B : ℝ} (hA : 1 ≤ A)
    (hB : (12 * A) ^ 2 * (d : ℝ) ^ 2 ≤ B) :
    4 * (d : ℝ) * Real.log (((d : ℝ) + 1) * B) ≤ B / A := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := lt_of_lt_of_le (by positivity) hB
  have hs := Real.sqrt_nonneg B
  have hs2 := Real.sq_sqrt hB0.le
  have hslo : 12 * A * d ≤ Real.sqrt B := by nlinarith
  have hdS : (d : ℝ) ≤ Real.sqrt B := by nlinarith
  have hlogB : Real.log B ≤ 2 * Real.sqrt B := by
    have h := Real.log_le_rpow_div hB0.le (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at h
    linarith
  have hlogd : Real.log ((d : ℝ) + 1) ≤ d := Real.log_add_one_le_self d.cast_nonneg
  rw [Real.log_mul (by positivity) hB0.ne']
  apply (le_div_iff₀ hA0).mpr
  have hh : 4 * (d : ℝ) * (Real.log ((d : ℝ) + 1) + Real.log B) * A ≤
      12 * A * d * Real.sqrt B := by
    have hlog : Real.log ((d : ℝ) + 1) + Real.log B ≤ 3 * Real.sqrt B := by linarith
    have ht := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 4 * (d : ℝ) * A by positivity)
    nlinarith only [ht]
  have ht := mul_le_mul_of_nonneg_right hslo hs
  nlinarith

/-- On B<=S*d² the 2/d box power has an absolute bound depending only on S. -/
private lemma small_box_log_bound {d : ℕ} (hd : 0 < d) {S B : ℝ} (hS : 1 ≤ S)
    (hB : 1 ≤ B) (hBS : B ≤ S * (d : ℝ) ^ 2) :
    Real.log (((d : ℝ) + 1) * B) ≤ Real.log S + 3 * d := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hS0 : 0 < S := by linarith
  have hB0 : 0 < B := by linarith
  have hdplus : (0 : ℝ) < d + 1 := by positivity
  have hlogd : Real.log (d : ℝ) ≤ d := by
    have h := Real.log_le_sub_one_of_pos hd0
    linarith
  have hlogplus : Real.log ((d : ℝ) + 1) ≤ d := Real.log_add_one_le_self d.cast_nonneg
  have hlogB := Real.log_le_log hB0 hBS
  rw [Real.log_mul hS0.ne' (by positivity), Real.log_pow] at hlogB
  rw [Real.log_mul hdplus.ne' hB0.ne']
  norm_num at hlogB
  linarith

private lemma small_box_power_bound {d : ℕ} (hd : 0 < d) {S B : ℝ} (hS : 1 ≤ S)
    (hB : 1 ≤ B) (hBS : B ≤ S * (d : ℝ) ^ 2) :
    (((d : ℝ) + 1) * B) ^ (2 / (d : ℝ)) ≤ Real.exp (2 * Real.log S + 6) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hlogS := Real.log_nonneg hS
  have hlog := small_box_log_bound hd hS hB hBS
  rw [Real.rpow_def_of_pos (by positivity)]
  apply Real.exp_le_exp.mpr
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hd0).mpr
  nlinarith

/-- In the small-box range `1 ≤ B ≤ S * d ^ 2` (with `1 ≤ S`), the unscaled auxiliary degree bound
`d * scaledPlaneAuxiliaryDegreeBound d C ((d + 1) * B) 1` is at most a constant depending only on
`S` and `C`, times `d ^ 4`. -/
lemma small_box_unscaled_degree_bound {d : ℕ} (hd : 0 < d) {S B C : ℝ}
    (hS : 1 ≤ S) (hB : 1 ≤ B) (hBS : B ≤ S * (d : ℝ) ^ 2) :
    (d : ℝ) * scaledPlaneAuxiliaryDegreeBound d C (((d : ℝ) + 1) * B) 1 ≤
      (Real.log S + 6 + 2 * Real.exp (heightDeterminantError C + 23) * Real.exp 14 *
        Real.exp (2 * Real.log S + 6)) * (d : ℝ) ^ 4 := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hd3 : (d : ℝ) ≤ (d : ℝ) ^ 3 := by nlinarith [sq_nonneg ((d : ℝ) - 1)]
  have hlogS := Real.log_nonneg hS
  have hlog := small_box_log_bound hd hS hB hBS
  have hpow := small_box_power_bound hd hS hB hBS
  have hrest : (d : ℝ) + Real.log (((d : ℝ) + 1) * B) + 2 ≤
      (Real.log S + 6) * (d : ℝ) ^ 3 := by nlinarith
  have hterm := mul_le_mul_of_nonneg_left hpow (show 0 ≤
    2 * Real.exp (heightDeterminantError C + 23) * Real.exp 14 * (d : ℝ) ^ 3 by positivity)
  have hdeg : scaledPlaneAuxiliaryDegreeBound d C (((d : ℝ) + 1) * B) 1 ≤
      (Real.log S + 6 + 2 * Real.exp (heightDeterminantError C + 23) * Real.exp 14 *
        Real.exp (2 * Real.log S + 6)) * (d : ℝ) ^ 3 := by
    unfold scaledPlaneAuxiliaryDegreeBound
    simp only [Real.log_one, zero_div, add_zero, mul_one, Real.one_rpow, div_one]
    nlinarith only [hrest, hterm]
  have ht := mul_le_mul_of_nonneg_left hdeg hd0.le
  convert ht using 1
  ring

end CCDN
