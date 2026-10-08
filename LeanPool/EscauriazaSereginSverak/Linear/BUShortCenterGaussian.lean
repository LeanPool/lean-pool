/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortWeightedCellFactor

/-!
# Combining center Gaussian exponents

The small growth exponent and fixed normal phase are absorbed by the
Gaussian average, leaving tangential lattice decay and a normal dyadic
tail.
-/

public section


open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The cell-center weights retain a tangential Gaussian, a normal
Gaussian, and one dyadic normal tail (`lem:bu-small-time`). -/
theorem bu_short_center_gaussian_absorption
    (G b β d : ℝ) (Y : Vec3)
    (hGtan : G ≤ 1 / 16)
    (hGnorm : G ≤ β / 48) (hbβ : b ≤ β / 48)
    (hβ : 0 < β) (hd : 0 < d) (hd1 : d ≤ 1 / 2)
    (hY : 2 ≤ Y 2) :
    Real.exp (-(Y 0 ^ 2 + Y 1 ^ 2) / 8) *
      Real.exp (b * Y 2 ^ 2) *
      Real.exp (G * (Y 0 ^ 2 + Y 1 ^ 2 + Y 2 ^ 2)) *
      Real.exp (-(β * Y 2 ^ 2 / (12 * d))) ≤
        Real.exp (-(Y 0 ^ 2 + Y 1 ^ 2) / 16) *
          Real.exp (-(β / (12 * d))) *
          Real.exp (-(β * Y 2 ^ 2 / (48 * d))) := by
  have hTangSq : 0 ≤ Y 0 ^ 2 + Y 1 ^ 2 := by positivity
  have hNormSq : 0 ≤ Y 2 ^ 2 := by positivity
  have hTang := mul_le_mul_of_nonneg_right hGtan hTangSq
  have hGrowNorm : G + b ≤ β / 24 := by
    linarith only [hGnorm, hbβ]
  have hGd : G + b ≤ β / (24 * d) := by
    have hd1' : d ≤ 1 := hd1.trans (by norm_num)
    have hbase : β / 24 ≤ β / (24 * d) := by
      apply (le_div_iff₀ (by positivity : 0 < 24 * d)).2
      have hmul := mul_le_mul_of_nonneg_left hd1' hβ.le
      nlinarith only [hmul]
    exact hGrowNorm.trans hbase
  have hNorm := mul_le_mul_of_nonneg_right hGd hNormSq
  have hYSq : 4 ≤ Y 2 ^ 2 := by
    nlinarith only [hY, sq_nonneg (Y 2 - 2)]
  have hTail : β / (12 * d) ≤ β * Y 2 ^ 2 / (48 * d) := by
    have hmul := mul_le_mul_of_nonneg_left hYSq hβ.le
    apply (div_le_div_iff₀ (by positivity : 0 < 12 * d)
      (by positivity : 0 < 48 * d)).2
    nlinarith only [hmul, hd]
  have harg : -(Y 0 ^ 2 + Y 1 ^ 2) / 8 + b * Y 2 ^ 2 +
      G * (Y 0 ^ 2 + Y 1 ^ 2 + Y 2 ^ 2) -
      β * Y 2 ^ 2 / (12 * d) ≤
        -(Y 0 ^ 2 + Y 1 ^ 2) / 16 - β / (12 * d) -
          β * Y 2 ^ 2 / (48 * d) := by
    have hnormal0 : (G + b) * Y 2 ^ 2 ≤
        β * Y 2 ^ 2 / (24 * d) := by
      convert hNorm using 1; ring
    have hsplit : β * Y 2 ^ 2 / (24 * d) +
        β / (12 * d) + β * Y 2 ^ 2 / (48 * d) ≤
        β * Y 2 ^ 2 / (12 * d) := by
      have hdiff : β * Y 2 ^ 2 / (12 * d) -
          (β * Y 2 ^ 2 / (24 * d) +
            β * Y 2 ^ 2 / (48 * d)) =
          β * Y 2 ^ 2 / (48 * d) := by ring
      rw [← hdiff] at hTail
      linarith only [hTail]
    nlinarith only [hTang, hnormal0, hsplit]
  calc
    _ = Real.exp (-(Y 0 ^ 2 + Y 1 ^ 2) / 8 + b * Y 2 ^ 2 +
        G * (Y 0 ^ 2 + Y 1 ^ 2 + Y 2 ^ 2) -
        β * Y 2 ^ 2 / (12 * d)) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
          ring_nf
    _ ≤ Real.exp (-(Y 0 ^ 2 + Y 1 ^ 2) / 16 - β / (12 * d) -
        β * Y 2 ^ 2 / (48 * d)) := Real.exp_le_exp.mpr harg
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add]
      ring_nf

end ESS
