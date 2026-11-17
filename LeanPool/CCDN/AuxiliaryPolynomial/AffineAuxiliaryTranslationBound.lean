/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.AuxiliaryPolynomial.PrimeScaledAffineMinimum
import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfacePositionHeight
import LeanPool.CCDN.ForMathlib.Log

/-! Translating the affine box by a vector bounded by the degree costs only
 a dimension constant in the coefficient-sensitive minimum bound. -/

@[expose] public section
namespace CCDN
noncomputable section

private lemma affine_box_translation_power {r d : ℕ} (hr : 0 < r) (hd : 0 < d)
    {B : ℝ} (hB : 1 ≤ B) :
    (B + d) ^ (1 / (d : ℝ) ^ (1 / (r : ℝ))) ≤
      Real.exp ((r : ℝ) + 1) * B ^ (1 / (d : ℝ) ^ (1 / (r : ℝ))) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hroot : (0 : ℝ) < (d : ℝ) ^ (1 / (r : ℝ)) := by positivity
  have hfactor : ((d : ℝ) + 1) ^ (1 / (d : ℝ) ^ (1 / (r : ℝ))) ≤
      Real.exp ((r : ℝ) + 1) := by
    rw [Real.rpow_def_of_pos (by positivity), Real.exp_le_exp, ← div_eq_mul_one_div]
    exact (div_le_iff₀ hroot).mpr (log_nat_add_one_le_root hr hd)
  calc
    _ ≤ (((d : ℝ) + 1) * B) ^ (1 / (d : ℝ) ^ (1 / (r : ℝ))) := by
      apply Real.rpow_le_rpow (by positivity) _ (by positivity)
      nlinarith
    _ = ((d : ℝ) + 1) ^ (1 / (d : ℝ) ^ (1 / (r : ℝ))) *
        B ^ (1 / (d : ℝ) ^ (1 / (r : ℝ))) := Real.mul_rpow (by positivity) (by linarith)
    _ ≤ _ := mul_le_mul_of_nonneg_right hfactor (by positivity)

private lemma affine_box_translation_log {d : ℕ} (hd : 0 < d) {B : ℝ} (hB : 1 ≤ B) :
    Real.log (B + d) ≤ Real.log B + Real.log ((d : ℝ) + 1) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hlog := Real.log_le_log (by positivity : 0 < B + d)
    (show B + d ≤ B * ((d : ℝ) + 1) by nlinarith)
  rwa [Real.log_mul (by linarith) (by positivity)] at hlog

private lemma affine_box_translation_min {d : ℕ} (hd : 0 < d)
    {B L b : ℝ} (hB : 1 ≤ B) (hL : 1 ≤ L) (hb : 0 ≤ b) :
    min (Real.log L + d * Real.log (B + d) + (d : ℝ) ^ 2) ((d : ℝ) ^ 2 * b) ≤
      2 * min (Real.log L + d * Real.log B + (d : ℝ) ^ 2) ((d : ℝ) ^ 2 * b) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hlogd : Real.log ((d : ℝ) + 1) ≤ d := Real.log_add_one_le_self d.cast_nonneg
  have hnum : Real.log L + d * Real.log (B + d) + (d : ℝ) ^ 2 ≤
      2 * (Real.log L + d * Real.log B + (d : ℝ) ^ 2) := by
    have hlog := affine_box_translation_log hd hB
    have hLlog := Real.log_nonneg hL
    have hBlog := Real.log_nonneg hB
    nlinarith [mul_le_mul_of_nonneg_left hlog hd0.le,
      mul_le_mul_of_nonneg_left hlogd hd0.le]
  rcases le_total (Real.log L + d * Real.log B + (d : ℝ) ^ 2) ((d : ℝ) ^ 2 * b) with h | h
  · rw [min_eq_left h]
    exact (min_le_left _ _).trans hnum
  · rw [min_eq_right h]
    exact (min_le_right _ _).trans (by nlinarith [sq_nonneg (d : ℝ)])

private lemma affine_box_translation_lower {r d : ℕ} (_hr : 0 < r) (hd : 0 < d)
    {B : ℝ} (hB : 1 ≤ B) :
    (d : ℝ) ^ (1 - 1 / (r : ℝ)) * Real.log (B + d) +
        (d : ℝ) ^ (4 - 1 / (r : ℝ)) ≤
      2 * ((d : ℝ) ^ (1 - 1 / (r : ℝ)) * Real.log B +
        (d : ℝ) ^ (4 - 1 / (r : ℝ))) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hlogd : Real.log ((d : ℝ) + 1) ≤ d := Real.log_add_one_le_self d.cast_nonneg
  have hpow : (d : ℝ) ^ (1 - 1 / (r : ℝ)) * d ≤ (d : ℝ) ^ (4 - 1 / (r : ℝ)) := by
    calc
      _ = (d : ℝ) ^ (2 - 1 / (r : ℝ)) := by
        calc
          _ = (d : ℝ) ^ (1 - 1 / (r : ℝ)) * (d : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_add hd0]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hd1 (by linarith)
  have hlog := affine_box_translation_log hd hB
  have hdlow : 0 ≤ (d : ℝ) ^ (1 - 1 / (r : ℝ)) := by positivity
  have hBlog := Real.log_nonneg hB
  nlinarith [mul_le_mul_of_nonneg_left hlog hdlow,
    mul_le_mul_of_nonneg_left hlogd hdlow]

/-- The full coefficient-sensitive affine expression is stable under the
 bounded translation used to make the constant coefficient nonzero. -/
private theorem affine_auxiliary_expression_translation_bound {r d : ℕ}
    (hr : 0 < r) (hd : 0 < d) {K B L b : ℝ}
    (hK : 0 ≤ K) (hB : 1 ≤ B) (hL : 1 ≤ L) (hb : 0 ≤ b) :
    K * (d : ℝ) ^ (2 - 1 / (r : ℝ)) *
        min (Real.log L + d * Real.log (B + d) + (d : ℝ) ^ 2) ((d : ℝ) ^ 2 * b) *
        (B + d) ^ (1 / (d : ℝ) ^ (1 / (r : ℝ))) /
          L ^ (1 / ((r : ℝ) * d * (d : ℝ) ^ (1 / (r : ℝ)))) +
      (d : ℝ) ^ (1 - 1 / (r : ℝ)) * Real.log (B + d) +
      (d : ℝ) ^ (4 - 1 / (r : ℝ)) ≤
    (2 * Real.exp ((r : ℝ) + 1)) *
      (K * (d : ℝ) ^ (2 - 1 / (r : ℝ)) *
          min (Real.log L + d * Real.log B + (d : ℝ) ^ 2) ((d : ℝ) ^ 2 * b) *
          B ^ (1 / (d : ℝ) ^ (1 / (r : ℝ))) /
            L ^ (1 / ((r : ℝ) * d * (d : ℝ) ^ (1 / (r : ℝ)))) +
        (d : ℝ) ^ (1 - 1 / (r : ℝ)) * Real.log B +
        (d : ℝ) ^ (4 - 1 / (r : ℝ))) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hLlog := Real.log_nonneg hL
  have hBlog := Real.log_nonneg hB
  have hBp : 1 ≤ B + d := by linarith
  have hBplog := Real.log_nonneg hBp
  have hmin0 : 0 ≤ min (Real.log L + d * Real.log B + (d : ℝ) ^ 2) ((d : ℝ) ^ 2 * b) := by
    positivity
  have hminp0 : 0 ≤ min (Real.log L + d * Real.log (B + d) + (d : ℝ) ^ 2)
      ((d : ℝ) ^ 2 * b) := by positivity
  have hmain := mul_le_mul (affine_box_translation_min hd hB hL hb)
    (affine_box_translation_power hr hd hB) (by positivity)
    (show 0 ≤ 2 * min (Real.log L + d * Real.log B + (d : ℝ) ^ 2)
      ((d : ℝ) ^ 2 * b) by positivity)
  have hscaled := mul_le_mul_of_nonneg_left hmain
    (show 0 ≤ K * (d : ℝ) ^ (2 - 1 / (r : ℝ)) /
      L ^ (1 / ((r : ℝ) * d * (d : ℝ) ^ (1 / (r : ℝ)))) by positivity)
  have hlower := affine_box_translation_lower hr hd hB
  have hE : 1 ≤ Real.exp ((r : ℝ) + 1) := Real.one_le_exp (by positivity)
  have hnonneg : 0 ≤ (d : ℝ) ^ (1 - 1 / (r : ℝ)) * Real.log B +
      (d : ℝ) ^ (4 - 1 / (r : ℝ)) := by positivity
  have hcost := mul_le_mul_of_nonneg_right hE hnonneg
  simp only [one_mul] at hcost
  have hcost2 := mul_le_mul_of_nonneg_left hcost (by norm_num : (0 : ℝ) ≤ 2)
  convert add_le_add hscaled (hlower.trans hcost2) using 1 <;> ring

/-- Specialization to the common minimum bound used by both affine branches. -/
theorem affineMinimumAuxiliaryBound_translation {n d : ℕ} (hd : 0 < d)
    {A B L b : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B) (hL : 1 ≤ L) (hb : 0 ≤ b) :
    affineMinimumAuxiliaryBound n d A (B + d) L b ≤
      (2 * Real.exp ((n : ℝ) + 2)) * affineMinimumAuxiliaryBound n d A B L b := by
  have hK : 0 ≤ max (affineHeightTransferConstant n) (Real.exp 1) * A :=
    mul_nonneg ((Real.exp_pos 1).le.trans (le_max_right _ _)) hA
  have hh := affine_auxiliary_expression_translation_bound (r := n + 1) (by omega) hd hK hB hL hb
  have hn : (n : ℝ) + 1 + 1 = n + 2 := by ring
  simp only [Nat.cast_add, Nat.cast_one, hn] at hh
  have hscaled := mul_le_mul_of_nonneg_left hh (hypersurfaceAbsoluteAuxiliaryConstant_pos n).le
  unfold affineMinimumAuxiliaryBound
  convert hscaled using 1
  ring

end
end CCDN
