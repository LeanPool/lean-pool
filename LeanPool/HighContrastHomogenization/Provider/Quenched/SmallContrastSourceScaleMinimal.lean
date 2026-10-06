/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastCarryBack

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastSourceScaleMinimal

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The source scale, chosen minimally

The one factor that was not already a named lemma.

`exists_source_scale_minimal` produces some `sK` with `growthBar K ≤ 3 ^ sK`
above a prescribed floor, which is all the account needs.  `hentry` needs more:
it must know `3 ^ sK` is not *much larger* than `growthBar K`, because `3 ^ sK`
enters the burn-in `N1 = sK + 1 + gap` and `hentry` must convert `3 ^ N1` into a
**law-free** exponent on the base.  An unconstrained `sK` gives nothing.

The fix is the same `⌈log₃ ·⌉` device as `three_pow_ceil_logb_le`, in its
`ℤ`-ceiling form: taking `sK := max floor ⌈log₃ (growthBar K)⌉` gives both
bounds at once, and the floor costs only the factor `3 ^ floor`, which is
dimension-only because the endpoint's floor is `kZero d`.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02

noncomputable section

/-- **The source scale, minimally.**  Above any nonnegative floor there is a
source scale that dominates the growth bar and is dominated by it, up to the
floor's own factor and a single power of three. -/
theorem exists_source_scale_minimal (K : ℝ) {floor : ℤ} (hfloor : 0 ≤ floor) :
    ∃ sK : ℤ, floor ≤ sK ∧ growthBar K ≤ (3 : ℝ) ^ sK ∧
      (3 : ℝ) ^ sK ≤ (3 : ℝ) ^ floor * (3 * growthBar K) := by
  have hG2 : (2 : ℝ) ≤ growthBar K := le_max_left 2 K
  have hG0 : (0 : ℝ) < growthBar K := by linarith only [hG2]
  set c : ℤ := ⌈Real.logb 3 (growthBar K)⌉ with hc
  have hfl1 : (1 : ℝ) ≤ (3 : ℝ) ^ floor := by
    rw [show (1 : ℝ) = (3 : ℝ) ^ (0 : ℤ) from by norm_num]
    exact zpow_le_zpow_right₀ (by norm_num) hfloor
  have hlogle : Real.logb 3 (growthBar K) ≤ (c : ℝ) := by
    rw [hc]; exact Int.le_ceil _
  have hlogadd : (c : ℝ) < Real.logb 3 (growthBar K) + 1 := by
    rw [hc]; exact Int.ceil_lt_add_one _
  have hGval : (3 : ℝ) ^ (Real.logb 3 (growthBar K)) = growthBar K :=
    Real.rpow_logb (by norm_num) (by norm_num) hG0
  refine ⟨max floor c, le_max_left _ _, ?_, ?_⟩
  · -- the growth bar is below the scale
    have hstep : (3 : ℝ) ^ (Real.logb 3 (growthBar K)) ≤
        (3 : ℝ) ^ ((max floor c : ℤ) : ℝ) := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have : (c : ℝ) ≤ ((max floor c : ℤ) : ℝ) := by
        exact_mod_cast le_max_right floor c
      linarith only [hlogle, this]
    rw [hGval] at hstep
    rwa [Real.rpow_intCast] at hstep
  · -- and the scale is not much above it
    rcases le_total c floor with hle | hle
    · rw [max_eq_left hle]
      have h3G : (1 : ℝ) ≤ 3 * growthBar K := by linarith only [hG2]
      have hz0 : (0 : ℝ) < (3 : ℝ) ^ floor := by positivity
      nlinarith only [h3G, hz0]
    · rw [max_eq_right hle]
      have hstep : (3 : ℝ) ^ ((c : ℤ) : ℝ) ≤
          (3 : ℝ) ^ (Real.logb 3 (growthBar K) + 1) := by
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        linarith only [hlogadd]
      rw [Real.rpow_intCast] at hstep
      have hval : (3 : ℝ) ^ (Real.logb 3 (growthBar K) + 1) =
          growthBar K * 3 := by
        rw [Real.rpow_add (by norm_num), hGval, Real.rpow_one]
      rw [hval] at hstep
      have hz0 : (0 : ℝ) < (3 : ℝ) ^ floor := by positivity
      nlinarith only [hstep, hfl1, hG0]

end

end HCPolySupport.HighContrast.Quenched
