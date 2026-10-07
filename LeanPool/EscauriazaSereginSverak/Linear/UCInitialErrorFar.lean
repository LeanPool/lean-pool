/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCInitialErrorGeometry

/-!
# Gaussian suppression away from the flatness center

Outside the quarter-power spatial ball, the initial transition carries a
Gaussian factor that dominates every inverse power of its time scale.
-/

public section


open Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- During the initial transition, the Gaussian weight is exponentially
small outside a spatial ball of radius `r`. -/
theorem ucGaussianWeight_le_far_initial
    {ε a r : ℝ} (hε : 0 < ε) (ha : 0 ≤ a)
    (hr : 0 < r) (hεsmall : ε ≤ 1) {z : ParabolicPoint}
    (hslo : ε ≤ z.2) (hshi : z.2 ≤ 2 * ε)
    (hfar : z.1 ∉ vec3Ball 0 r) :
    ucGaussianWeight a z ≤
      (ε * Real.exp (-(1 / 3 : ℝ))) ^ (-2 * a) *
        Real.exp (-(r ^ 2 / (8 * ε))) := by
  let b : ℝ := ε * Real.exp (-(1 / 3 : ℝ))
  have hb : 0 < b := by dsimp [b]; positivity
  have hs : 0 < z.2 := hε.trans_le hslo
  have hs2 : z.2 ≤ 2 := by
    linarith only [hshi, hεsmall]
  have hnorm : r ≤ vec3EuclideanNorm z.1 := by
    simpa only [mem_vec3Ball, sub_zero, not_lt] using hfar
  have hnormSq : r ^ 2 ≤ vec3EuclideanNorm z.1 ^ 2 := by
    nlinarith only [hr.le, hnorm, vec3EuclideanNorm_nonneg z.1]
  have hfrac : r ^ 2 / (8 * ε) ≤
      vec3EuclideanNorm z.1 ^ 2 / (4 * z.2) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 8 * ε)
      (by positivity : 0 < 4 * z.2)).2
    have hsmul := mul_le_mul_of_nonneg_left hshi
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (sq_nonneg r))
    have hnmul := mul_le_mul_of_nonneg_right hnormSq
      (by positivity : 0 ≤ 8 * ε)
    nlinarith only [hsmul, hnmul]
  have hgauss : Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2)) ≤
      Real.exp (-(r ^ 2 / (8 * ε))) :=
    Real.exp_le_exp.mpr (by simpa only [neg_div] using neg_le_neg hfrac)
  have hexp : Real.exp (-(1 / 3 : ℝ)) ≤
      Real.exp ((1 - z.2) / 3) :=
    Real.exp_le_exp.mpr (by linarith only [hs2])
  have htime : b ≤ gaussCarlemanTimeWeight z.2 := by
    dsimp [b, gaussCarlemanTimeWeight]
    exact mul_le_mul hslo hexp (Real.exp_pos _).le hs.le
  have hpow := Real.rpow_le_rpow_of_nonpos hb htime
    (by linarith only [ha] : -2 * a ≤ 0)
  dsimp [ucGaussianWeight]
  exact mul_le_mul hpow hgauss (Real.exp_pos _).le
    (Real.rpow_pos_of_pos hb _).le

end ESS
