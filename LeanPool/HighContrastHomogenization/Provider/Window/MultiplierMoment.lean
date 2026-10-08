/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup.SourceObjects

/-!
# High-contrast homogenization: Provider.Window.MultiplierMoment

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The coupled burn gives the uniform multiplier moment

The third ceiling in `sourceBurn` was chosen so that the source-remainder
scale times the weak-Orlicz moment multiplier is at most one.  This file opens
that ceiling and records the resulting `L^Q` bound by two.
-/

namespace HCPolySupport
namespace HighContrast
namespace Window

open MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The quantitative content of the third source-burn ceiling. -/
theorem sourceRemainderScale_mul_momentMultiplier_le_one
    {Q K : ℝ} (hQ : 1 ≤ Q) {jStar M : ℤ}
    (hw : IsCoupledWindow d Q K jStar M) :
    sourceRemainderScale d jStar K * momentMultiplier Q (growthBar K) ≤ 1 := by
  set B : ℝ := growthBar K with hB
  set R : ℝ := momentMultiplier Q B with hR
  have hBtwo : 2 ≤ B := by rw [hB, growthBar]; exact le_max_left _ _
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hBtwo
  have hBlog : 0 ≤ Real.log B := Real.log_nonneg (le_trans (by norm_num) hBtwo)
  have hRpos : 0 < R := by
    rw [hR, momentMultiplier]
    apply Real.rpow_pos_of_pos
    have hzpow : 0 < B ^ (⌈Q * (Q + 1) / 2⌉ : ℤ) := zpow_pos hBpos _
    positivity
  have hceil :
      ⌈2 + 4 * ((d : ℝ) + 1) * Real.logb 3 B + Real.logb 3 R⌉ ≤ jStar := by
    have hthird :
        ⌈2 + 4 * ((d : ℝ) + 1) * Real.logb 3 (growthBar K) +
            Real.logb 3 (momentMultiplier Q (growthBar K))⌉ ≤ sourceBurn d Q K := by
      rw [sourceBurn]
      exact (le_max_right _ _).trans (le_max_right _ _)
    simpa only [hB, hR] using hthird.trans hw.1
  have hceilReal :
      (2 + 4 * ((d : ℝ) + 1) * Real.logb 3 B + Real.logb 3 R) ≤
        (jStar : ℝ) := by
    exact (Int.le_ceil _).trans (by exact_mod_cast hceil)
  have hexp :
      ((4 * (d + 1) : ℕ) : ℝ) * Real.logb 3 B +
          (((2 : ℤ) - jStar : ℤ) : ℝ) + Real.logb 3 R ≤ 0 := by
    norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Int.cast_sub,
      Int.cast_ofNat]
    linarith only [hceilReal]
  have hBpow : (3 : ℝ) ^ Real.logb 3 B = B :=
    Real.rpow_logb (by norm_num) (by norm_num) hBpos
  have hRpow : (3 : ℝ) ^ Real.logb 3 R = R :=
    Real.rpow_logb (by norm_num) (by norm_num) hRpos
  have hmain : B ^ (4 * (d + 1)) * (3 : ℝ) ^ ((2 : ℤ) - jStar) * R ≤ 1 := by
    calc
      B ^ (4 * (d + 1)) * (3 : ℝ) ^ ((2 : ℤ) - jStar) * R
          = ((3 : ℝ) ^ Real.logb 3 B) ^ (4 * (d + 1)) *
              (3 : ℝ) ^ ((2 : ℤ) - jStar) *
                ((3 : ℝ) ^ Real.logb 3 R) := by rw [hBpow, hRpow]
      _ = (3 : ℝ) ^
          (((4 * (d + 1) : ℕ) : ℝ) * Real.logb 3 B +
            (((2 : ℤ) - jStar : ℤ) : ℝ) + Real.logb 3 R) := by
        rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3),
          mul_comm (Real.logb 3 B), ← Real.rpow_intCast,
          ← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
          ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      _ ≤ (3 : ℝ) ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = 1 := Real.rpow_zero 3
  simpa only [sourceRemainderScale, hB, hR] using hmain

/-- Every common window multiplier has `L^Q` norm at most two at the coupled
exponent. -/
theorem lqNorm_le_two {P : Measure (CoeffSpace d)} {g : ℝ} {E : BlockMat d}
    {Ψ : ℝ → ℝ} {K Cd Q : ℝ} {jStar M : ℤ}
    (hQ : 1 ≤ Q) (hw : IsCoupledWindow d Q K jStar M)
    {Y : CoeffSpace d → ℝ} (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) :
    lqNorm P Q Y ≤ 2 := by
  have hmoment := hY.lp_moment Q hQ
  have hscale := sourceRemainderScale_mul_momentMultiplier_le_one hQ hw
  calc
    lqNorm P Q Y ≤ ENNReal.ofReal
        (1 + sourceRemainderScale d jStar K * momentMultiplier Q (growthBar K)) := hmoment
    _ ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal (by linarith only [hscale])
    _ = 2 := by norm_num

end

end Window
end HighContrast
end HCPolySupport
