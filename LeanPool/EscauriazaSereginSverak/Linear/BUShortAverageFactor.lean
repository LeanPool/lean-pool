/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortAverageRescaling

/-!
# Size of a rescaled Gaussian average

The physical parabolic normalization contributes at most two powers
of the dyadic time scale after the affine Jacobian is removed.
-/

public section


noncomputable section

namespace ESS

/-- The physical Gaussian average normalization is at most the square
of the dyadic time scale (`lem:bu-small-time`). -/
theorem bu_short_average_jacobian_factor_le
    (scale δ d : ℝ) (hscale : 0 < scale)
    (hδ : 0 < δ) (hδd : δ ≤ d) (hd : d ≤ 1) :
    let t := scale ^ 2 * δ / 2
    scale⁻¹ ^ 5 * Real.rpow t (5 / 2 : ℝ) ≤ d ^ 2 := by
  dsimp
  let t := scale ^ 2 * δ / 2
  let q := δ / 2
  have hq : 0 < q := by dsimp [q]; positivity
  have hqle : q ≤ d := by dsimp [q]; linarith only [hδd, hδ]
  have hq1 : q ≤ 1 := hqle.trans hd
  have ht : 0 < t := by dsimp [t]; positivity
  have htEq : t = scale ^ 2 * q := by dsimp [t, q]; ring
  have hsqrt : Real.sqrt t = scale * Real.sqrt q := by
    rw [htEq, Real.sqrt_mul (sq_nonneg scale), Real.sqrt_sq_eq_abs,
      abs_of_pos hscale]
  have hRpow : Real.rpow t (5 / 2 : ℝ) = (Real.sqrt t) ^ 5 := by
    have h := Real.rpow_div_two_eq_sqrt (x := t) (r := (5 : ℝ)) ht.le
    exact h.trans (Real.rpow_natCast (Real.sqrt t) 5)
  have hqroot : Real.sqrt q ≤ 1 := Real.sqrt_le_one.mpr hq1
  have hroot4 : (Real.sqrt q) ^ 4 = q ^ 2 := by
    calc
      _ = (Real.sqrt q ^ 2) ^ 2 := by ring
      _ = q ^ 2 := by rw [Real.sq_sqrt hq.le]
  have hroot5 : (Real.sqrt q) ^ 5 ≤ q ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left hqroot
      (pow_nonneg (Real.sqrt_nonneg q) 4)
    calc
      (Real.sqrt q) ^ 5 = (Real.sqrt q) ^ 4 * Real.sqrt q := by ring
      _ ≤ (Real.sqrt q) ^ 4 * 1 := hm
      _ = q ^ 2 := by rw [mul_one, hroot4]
  have hqSq : q ^ 2 ≤ d ^ 2 := by
    nlinarith only [hqle, hq, sq_nonneg (d - q)]
  calc
    scale⁻¹ ^ 5 * Real.rpow t (5 / 2 : ℝ) =
        scale⁻¹ ^ 5 * (scale * Real.sqrt q) ^ 5 := by rw [hRpow, hsqrt]
    _ = (Real.sqrt q) ^ 5 := by
      rw [mul_pow]
      have hcancel : scale⁻¹ ^ 5 * scale ^ 5 = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ (ne_of_gt hscale), one_pow]
      calc
        _ = (scale⁻¹ ^ 5 * scale ^ 5) * (Real.sqrt q) ^ 5 := by ring
        _ = _ := by rw [hcancel, one_mul]
    _ ≤ q ^ 2 := hroot5
    _ ≤ d ^ 2 := hqSq

end ESS
