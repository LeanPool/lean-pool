/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Scales

/-!
# Landmarks

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Landmark characterizations for the Section 3 induction scales

ABK26 introduces two distinguished small scales.  The scale `m**` is the
largest integer `m` with `nu ^ 2 ≥ 2 (log 3) c gamma⁻³ 3 ^ (2 gamma m)` and the
scale `m*` is the largest integer `m` with
`nu ^ 2 ≥ 2 (log 3) c gamma⁻¹ 3 ^ (2 gamma m)`.

This file proves exactly those characterizations for the repository's
`Algsuperdiff.Section3.mStarStar` and `Algsuperdiff.Section3.mStar`, together
with the floor estimate that they imply and the ordering
`mStarStar ≤ mStar`.

The approved Lean surface uses the normalized Frobenius origin-mass constant
`Algsuperdiff.Section3.Disorder.cstarPlus` where the paper prints `cstar`.
That substitution is already part of the frozen definitions and is not
revisited here.

## Main results

* `le_mStar_iff`: the source "largest integer" property.
* `le_mStarStar_iff_rpow_le`, `le_mStar_iff_rpow_le`: the same property in
  quotient form, which is the convenient shape for downstream estimates.
* `mStarStar_le_mStar`: the two landmarks are ordered.
* `rpow_mStarStar_le`: the upper half of the floor sandwich, the landmark
  `mStarStar` itself meeting its threshold.

## References

* ABK26, equations `e.mstarstar` and `e.mstar`.
-/

namespace Algsuperdiff.Section3.Provider.Scales

variable {d : ℕ}

/-- The normalizing factor `2 (log 3) c⁺` of the two landmark definitions is
strictly positive. -/
private theorem two_mul_log_mul_cstarPlus_pos (M : ABKModel d) :
    (0 : ℝ) < 2 * Real.log 3 * Disorder.cstarPlus M :=
  mul_pos (mul_pos (by norm_num) (Real.log_pos (by norm_num)))
    (Disorder.cstarPlus_pos M)

/-- An integer lies below the floor of a rescaled base-three logarithm exactly
when the corresponding power of three lies below the argument. -/
private theorem int_le_floor_inv_mul_logb_iff {c A : ℝ} (hc : 0 < c) (hA : 0 < A)
    (m : ℤ) :
    m ≤ ⌊c⁻¹ * Real.logb 3 A⌋ ↔ (3 : ℝ) ^ (c * (m : ℝ)) ≤ A := by
  have hlogb : (3 : ℝ) ^ Real.logb 3 A = A :=
    Real.rpow_logb (by norm_num) (by norm_num) hA
  calc m ≤ ⌊c⁻¹ * Real.logb 3 A⌋ ↔ (m : ℝ) ≤ c⁻¹ * Real.logb 3 A := Int.le_floor
    _ ↔ c * (m : ℝ) ≤ Real.logb 3 A := by
        rw [show c⁻¹ * Real.logb 3 A = Real.logb 3 A / c by ring, le_div_iff₀' hc]
    _ ↔ (3 : ℝ) ^ (c * (m : ℝ)) ≤ (3 : ℝ) ^ Real.logb 3 A :=
        (Real.rpow_le_rpow_left_iff (by norm_num)).symm
    _ ↔ (3 : ℝ) ^ (c * (m : ℝ)) ≤ A := by rw [hlogb]

/-- The common floor characterization of both landmarks, for an arbitrary
positive weight `w` in place of `gamma ^ 3` resp. `gamma`. -/
private theorem le_floor_landmark_iff (M : ABKModel d) {w : ℝ} (hw : 0 < w)
    (m : ℤ) :
    m ≤ ⌊(2 * M.gamma)⁻¹ *
          Real.logb 3
            (M.nu ^ 2 * w / (2 * Real.log 3 * Disorder.cstarPlus M))⌋ ↔
      (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) ≤
        M.nu ^ 2 * w / (2 * Real.log 3 * Disorder.cstarPlus M) :=
  int_le_floor_inv_mul_logb_iff
    (by linarith [M.shellPrefix.gamma_pos] : (0 : ℝ) < 2 * M.gamma)
    (div_pos (mul_pos (pow_pos M.nu_pos 2) hw) (two_mul_log_mul_cstarPlus_pos M)) m

/-- The purely algebraic rearrangement behind the paper's threshold form. -/
private theorem le_div_iff_mul_inv_mul_le {t v g c : ℝ} (hg : 0 < g) (hc : 0 < c) :
    t ≤ v * g / c ↔ c * g⁻¹ * t ≤ v := by
  rw [le_div_iff₀ hc, show c * g⁻¹ * t = c * t / g by ring, div_le_iff₀ hg]
  constructor <;> intro h <;> linarith

/-- Both landmarks satisfy a sandwich: the landmark itself meets the threshold,
and going up one scale loses it, so the threshold value is exceeded after
removing a single factor `3 ^ (-(2 gamma))`. -/
private theorem landmark_sandwich {gamma A : ℝ} {k : ℤ}
    (hk : ∀ m : ℤ, m ≤ k ↔ (3 : ℝ) ^ (2 * gamma * (m : ℝ)) ≤ A) :
    (3 : ℝ) ^ (2 * gamma * (k : ℝ)) ≤ A ∧
      A * (3 : ℝ) ^ (-(2 * gamma)) < (3 : ℝ) ^ (2 * gamma * (k : ℝ)) := by
  refine ⟨(hk k).mp le_rfl, ?_⟩
  have hnot : ¬((3 : ℝ) ^ (2 * gamma * ((k + 1 : ℤ) : ℝ)) ≤ A) := by
    intro hc
    have hle := (hk (k + 1)).mpr hc
    omega
  push Not at hnot
  have hsplit : (3 : ℝ) ^ (2 * gamma * ((k + 1 : ℤ) : ℝ)) =
      (3 : ℝ) ^ (2 * gamma * (k : ℝ)) * (3 : ℝ) ^ (2 * gamma) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
      show 2 * gamma * (k : ℝ) + 2 * gamma = 2 * gamma * ((k + 1 : ℤ) : ℝ) by
        push_cast; ring]
  rw [hsplit] at hnot
  have hr : (0 : ℝ) < (3 : ℝ) ^ (2 * gamma) := Real.rpow_pos_of_pos (by norm_num) _
  have hneg : (3 : ℝ) ^ (-(2 * gamma)) = ((3 : ℝ) ^ (2 * gamma))⁻¹ :=
    Real.rpow_neg (by norm_num) _
  calc A * (3 : ℝ) ^ (-(2 * gamma)) = A * ((3 : ℝ) ^ (2 * gamma))⁻¹ := by rw [hneg]
    _ < (3 : ℝ) ^ (2 * gamma * (k : ℝ)) * (3 : ℝ) ^ (2 * gamma) *
          ((3 : ℝ) ^ (2 * gamma))⁻¹ := mul_lt_mul_of_pos_right hnot (inv_pos.mpr hr)
    _ = (3 : ℝ) ^ (2 * gamma * (k : ℝ)) := by
        rw [mul_assoc, mul_inv_cancel₀ hr.ne', mul_one]

/-- Quotient form of the defining property of `mStarStar`. -/
theorem le_mStarStar_iff_rpow_le (M : ABKModel d) (m : ℤ) :
    m ≤ mStarStar M ↔
      (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) ≤
        M.nu ^ 2 * M.gamma ^ 3 / (2 * Real.log 3 * Disorder.cstarPlus M) :=
  le_floor_landmark_iff M (pow_pos M.shellPrefix.gamma_pos 3) m

/-- Quotient form of the defining property of `mStar`. -/
theorem le_mStar_iff_rpow_le (M : ABKModel d) (m : ℤ) :
    m ≤ mStar M ↔
      (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) ≤
        M.nu ^ 2 * M.gamma / (2 * Real.log 3 * Disorder.cstarPlus M) :=
  le_floor_landmark_iff M M.shellPrefix.gamma_pos m

/-- `mStar M` is the largest integer `m` with
`2 (log 3) c⁺ gamma⁻¹ 3 ^ (2 gamma m) ≤ nu ^ 2`, which is ABK26's defining
description of `m*`. -/
theorem le_mStar_iff (M : ABKModel d) (m : ℤ) :
    m ≤ mStar M ↔
      2 * Real.log 3 * Disorder.cstarPlus M * M.gamma⁻¹ *
          (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) ≤ M.nu ^ 2 := by
  rw [le_mStar_iff_rpow_le M m]
  exact le_div_iff_mul_inv_mul_le M.shellPrefix.gamma_pos
    (two_mul_log_mul_cstarPlus_pos M)

/-- The base-case landmark never exceeds the base-plateau landmark, because
`gamma ≤ 1 / 4` forces `gamma ^ 3 ≤ gamma`. -/
theorem mStarStar_le_mStar (M : ABKModel d) : mStarStar M ≤ mStar M := by
  have hg : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hq : M.gamma ≤ 1 / 4 := M.shellPrefix.gamma_le_quarter
  have hle_one : M.gamma ≤ 1 := by linarith
  have hsq : M.gamma ^ 2 ≤ 1 := by
    calc M.gamma ^ 2 = M.gamma * M.gamma := by ring
      _ ≤ 1 * 1 := mul_le_mul hle_one hle_one hg.le zero_le_one
      _ = 1 := by norm_num
  have hcube : M.gamma ^ 3 ≤ M.gamma := by
    calc M.gamma ^ 3 = M.gamma * M.gamma ^ 2 := by ring
      _ ≤ M.gamma * 1 := mul_le_mul_of_nonneg_left hsq hg.le
      _ = M.gamma := mul_one _
  have hc : (0 : ℝ) < 2 * Real.log 3 * Disorder.cstarPlus M :=
    two_mul_log_mul_cstarPlus_pos M
  refine (le_mStar_iff_rpow_le M (mStarStar M)).mpr ?_
  refine ((le_mStarStar_iff_rpow_le M (mStarStar M)).mp le_rfl).trans ?_
  have hnum : M.nu ^ 2 * M.gamma ^ 3 ≤ M.nu ^ 2 * M.gamma :=
    mul_le_mul_of_nonneg_left hcube (sq_nonneg M.nu)
  have hmul := mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr hc.le)
  simpa only [div_eq_mul_inv] using hmul

/-- The upper half of the floor sandwich at `mStarStar`. -/
theorem rpow_mStarStar_le (M : ABKModel d) :
    (3 : ℝ) ^ (2 * M.gamma * (mStarStar M : ℝ)) ≤
      M.nu ^ 2 * M.gamma ^ 3 / (2 * Real.log 3 * Disorder.cstarPlus M) :=
  (landmark_sandwich (le_mStarStar_iff_rpow_le M)).1

end Algsuperdiff.Section3.Provider.Scales
