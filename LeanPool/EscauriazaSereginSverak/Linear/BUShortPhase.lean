/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The normal Carleman phase for short-time vanishing

At exponent three quarters the normal part of the weight in
`lem:bu-small-time` increases in height and decreases in time.
-/

public section


noncomputable section

namespace ESS

/-- The normal part of the half-space Carleman phase at exponent three
quarters. -/
@[expose] def buShortF (y s : ℝ) : ℝ :=
  (1 - s) * y ^ (3 / 2 : ℝ) * s ^ (-(3 / 4 : ℝ))

/-- The normal phase is positive at positive height and time below one. -/
theorem buShortF_pos {y s : ℝ} (hy : 0 < y)
    (hs : 0 < s) (hs1 : s < 1) : 0 < buShortF y s := by
  dsimp [buShortF]
  have hfirst : 0 < 1 - s := sub_pos.mpr hs1
  positivity

/-- At fixed time the normal phase increases with height. -/
theorem buShortF_mono_height {y₁ y₂ s : ℝ}
    (hy₁ : 0 ≤ y₁) (hyle : y₁ ≤ y₂)
    (hs : 0 < s) (hs1 : s ≤ 1) :
    buShortF y₁ s ≤ buShortF y₂ s := by
  dsimp [buShortF]
  have hr := Real.rpow_le_rpow hy₁ hyle (by norm_num : (0 : ℝ) ≤ 3 / 2)
  have ht : 0 ≤ 1 - s := sub_nonneg.mpr hs1
  have hpow : 0 ≤ s ^ (-(3 / 4 : ℝ)) := by positivity
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hr ht) hpow

/-- At fixed height the normal phase decreases with time. -/
theorem buShortF_antitone_time {y s₀ s₁ : ℝ}
    (hy : 0 ≤ y) (hs₀ : 0 < s₀) (hsle : s₀ ≤ s₁)
    (hs₁ : s₁ ≤ 1) :
    buShortF y s₁ ≤ buShortF y s₀ := by
  dsimp [buShortF]
  have hfactor : 1 - s₁ ≤ 1 - s₀ := by linarith only [hsle]
  have hfactor0 : 0 ≤ 1 - s₁ := sub_nonneg.mpr hs₁
  have hyPow : 0 ≤ y ^ (3 / 2 : ℝ) := by positivity
  have htime : s₁ ^ (-(3 / 4 : ℝ)) ≤
      s₀ ^ (-(3 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hs₀ hsle (by norm_num)
  have htime0 : 0 ≤ s₀ ^ (-(3 / 4 : ℝ)) := by positivity
  calc
    (1 - s₁) * y ^ (3 / 2 : ℝ) * s₁ ^ (-(3 / 4 : ℝ)) ≤
        (1 - s₁) * y ^ (3 / 2 : ℝ) * s₀ ^ (-(3 / 4 : ℝ)) := by
      exact mul_le_mul_of_nonneg_left htime (mul_nonneg hfactor0 hyPow)
    _ ≤ (1 - s₀) * y ^ (3 / 2 : ℝ) * s₀ ^ (-(3 / 4 : ℝ)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hfactor hyPow) htime0

end ESS
