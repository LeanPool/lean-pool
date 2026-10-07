/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCFlatnessTransfer
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.Profile

/-!
# Time cutoffs for Gaussian unique continuation

The upper cutoff turns off before time `7/4`. The lower cutoff turns on
between times `ε` and `2ε`.
-/

public section


open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The final-time cutoff in `lem:uc-gaussian`. -/
@[expose] def ucFinalTimeCutoff (s : ℝ) : ℝ :=
  smoothTransitionProfile (7 - 4 * s)

/-- The initial-time cutoff in `lem:uc-gaussian`. -/
@[expose] def ucInitialTimeCutoff (ε s : ℝ) : ℝ :=
  smoothTransitionProfile ((s - ε) / ε)

/-- The final-time cutoff is smooth. -/
theorem ucFinalTimeCutoff_smooth :
    ContDiff ℝ (⊤ : ℕ∞) ucFinalTimeCutoff := by
  unfold ucFinalTimeCutoff
  exact smoothTransitionProfile.smooth.comp
    (contDiff_const.sub (contDiff_const.mul contDiff_id))

/-- The initial-time cutoff is smooth in the time variable. -/
theorem ucInitialTimeCutoff_smooth (ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (ucInitialTimeCutoff ε) := by
  unfold ucInitialTimeCutoff
  exact smoothTransitionProfile.smooth.comp
    ((contDiff_id.sub contDiff_const).div_const ε)

/-- The final-time cutoff equals one before time `3/2`. -/
theorem ucFinalTimeCutoff_eq_one {s : ℝ} (hs : s ≤ 3 / 2) :
    ucFinalTimeCutoff s = 1 := by
  apply smoothTransitionProfile.one_of_one_le
  linarith only [hs]

/-- The final-time cutoff vanishes from time `7/4` onward. -/
theorem ucFinalTimeCutoff_eq_zero {s : ℝ} (hs : 7 / 4 ≤ s) :
    ucFinalTimeCutoff s = 0 := by
  apply smoothTransitionProfile.zero_of_nonpos
  linarith only [hs]

/-- The initial-time cutoff vanishes through time `ε`. -/
theorem ucInitialTimeCutoff_eq_zero {ε s : ℝ} (hε : 0 < ε)
    (hs : s ≤ ε) : ucInitialTimeCutoff ε s = 0 := by
  apply smoothTransitionProfile.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs) hε.le

/-- The initial-time cutoff equals one from time `2ε` onward. -/
theorem ucInitialTimeCutoff_eq_one {ε s : ℝ} (hε : 0 < ε)
    (hs : 2 * ε ≤ s) : ucInitialTimeCutoff ε s = 1 := by
  apply smoothTransitionProfile.one_of_one_le
  apply (le_div_iff₀ hε).2
  linarith only [hs]

/-- The final-time cutoff takes values between zero and one. -/
theorem ucFinalTimeCutoff_bounds (s : ℝ) :
    0 ≤ ucFinalTimeCutoff s ∧ ucFinalTimeCutoff s ≤ 1 := by
  exact ⟨smoothTransitionProfile.nonneg _,
    smoothTransitionProfile.le_one _⟩

/-- The initial-time cutoff takes values between zero and one. -/
theorem ucInitialTimeCutoff_bounds (ε s : ℝ) :
    0 ≤ ucInitialTimeCutoff ε s ∧ ucInitialTimeCutoff ε s ≤ 1 := by
  exact ⟨smoothTransitionProfile.nonneg _,
    smoothTransitionProfile.le_one _⟩

/-- The final-time cutoff has an absolute first-derivative bound. -/
theorem ucFinalTimeCutoff_abs_deriv_le (s : ℝ) :
    |deriv ucFinalTimeCutoff s| ≤ 32 := by
  have harg : HasDerivAt (fun u : ℝ => 7 - 4 * u) (-4) s := by
    convert ((hasDerivAt_id s).const_mul (-4)).const_add 7 using 1
    all_goals
      try funext u
      try simp only [id_eq]
      try ring
  have hprofile : DifferentiableAt ℝ smoothTransitionProfile (7 - 4 * s) :=
    smoothTransitionProfile.smooth.differentiable (by simp) _
  have hD : deriv ucFinalTimeCutoff s =
      deriv smoothTransitionProfile (7 - 4 * s) * (-4) := by
    exact (hprofile.hasDerivAt.comp s harg).deriv
  rw [hD, abs_mul]
  have hb := smoothTransitionProfile.abs_deriv_le_eight (7 - 4 * s)
  norm_num
  nlinarith only [hb]

/-- The initial-time cutoff has derivative at most `8/ε` in absolute value. -/
theorem ucInitialTimeCutoff_abs_deriv_le {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    |deriv (ucInitialTimeCutoff ε) s| ≤ 8 / ε := by
  have harg : HasDerivAt (fun u : ℝ => (u - ε) / ε) (1 / ε) s := by
    convert ((hasDerivAt_id s).sub_const ε).div_const ε using 1
    all_goals
      try funext u
      try simp only [id_eq]
      try ring
  have hprofile : DifferentiableAt ℝ smoothTransitionProfile ((s - ε) / ε) :=
    smoothTransitionProfile.smooth.differentiable (by simp) _
  have hD : deriv (ucInitialTimeCutoff ε) s =
      deriv smoothTransitionProfile ((s - ε) / ε) * (1 / ε) := by
    exact (hprofile.hasDerivAt.comp s harg).deriv
  rw [hD, abs_mul, abs_div, abs_one, abs_of_pos hε]
  have hb := smoothTransitionProfile.abs_deriv_le_eight ((s - ε) / ε)
  have heps : 0 ≤ 1 / ε := by positivity
  calc
    |deriv smoothTransitionProfile ((s - ε) / ε)| * (1 / ε)
      ≤ 8 * (1 / ε) := mul_le_mul_of_nonneg_right hb heps
    _ = 8 / ε := by ring

end ESS
