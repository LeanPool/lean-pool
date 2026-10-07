/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCMeasureTransport

/-!
# Gaussian weight away from initial time

The Gaussian Carleman weight is uniformly bounded on every positive-time
truncation of the normalized cylinder.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The Gaussian weight is nonnegative on positive time. -/
theorem ucGaussianWeight_nonneg
    (a : ℝ) {z : ParabolicPoint} (hz : 0 < z.2) :
    0 ≤ ucGaussianWeight a z := by
  have hh : 0 < gaussCarlemanTimeWeight z.2 := by
    dsimp [gaussCarlemanTimeWeight]
    positivity
  unfold ucGaussianWeight
  positivity

/-- For a fixed positive initial cutoff time, the Gaussian weight has a
bound independent of the spatial point. -/
theorem ucGaussianWeight_le_after
    {ε a : ℝ} (hε : 0 < ε) (ha : 0 ≤ a)
    {z : ParabolicPoint} (hslo : ε ≤ z.2) (hshi : z.2 ≤ 2) :
    ucGaussianWeight a z ≤
      (ε * Real.exp (-(1 / 3 : ℝ))) ^ (-2 * a) := by
  let b : ℝ := ε * Real.exp (-(1 / 3 : ℝ))
  have hb : 0 < b := by dsimp [b]; positivity
  have hs : 0 < z.2 := hε.trans_le hslo
  have hexp : Real.exp (-(1 / 3 : ℝ)) ≤
      Real.exp ((1 - z.2) / 3) :=
    Real.exp_le_exp.mpr (by linarith only [hshi])
  have htime : b ≤ gaussCarlemanTimeWeight z.2 := by
    dsimp [b, gaussCarlemanTimeWeight]
    exact mul_le_mul hslo hexp (Real.exp_pos _).le hs.le
  have hpow := Real.rpow_le_rpow_of_nonpos hb htime (by linarith only [ha] : -2 * a ≤ 0)
  have htimepos : 0 < gaussCarlemanTimeWeight z.2 := hb.trans_le htime
  have hpow0 : 0 ≤ gaussCarlemanTimeWeight z.2 ^ (-2 * a) :=
    (Real.rpow_pos_of_pos htimepos _).le
  have hgauss : Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2)) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    have hden : 0 < 4 * z.2 := by positivity
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) hden.le
  dsimp [ucGaussianWeight]
  calc
    gaussCarlemanTimeWeight z.2 ^ (-2 * a) *
        Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2)) ≤
      gaussCarlemanTimeWeight z.2 ^ (-2 * a) * 1 :=
        mul_le_mul_of_nonneg_left hgauss hpow0
    _ ≤ b ^ (-2 * a) * 1 :=
      mul_le_mul_of_nonneg_right hpow (by norm_num)
    _ = _ := by simp [b]

/-- The Gaussian weight is measurable on space-time. -/
theorem ucGaussianWeight_measurable (a : ℝ) :
    Measurable (ucGaussianWeight a) := by
  have hnorm : Measurable (fun z : ParabolicPoint =>
      vec3EuclideanNorm z.1) :=
    continuous_vec3EuclideanNorm.measurable.comp measurable_fst
  unfold ucGaussianWeight gaussCarlemanTimeWeight
  fun_prop


end ESS
