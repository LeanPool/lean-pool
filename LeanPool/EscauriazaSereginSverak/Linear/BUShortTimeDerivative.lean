/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortTimeFactor

/-!
# Size and support of the lower-time derivative

The derivative of the initial-time transition is bounded by `8/ε` and
vanishes outside its transition strip.
-/

public section


open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- Differentiation commutes with shifting the time cutoff by one half. -/
theorem buShortTimeCutoff_deriv (ε s : ℝ) :
    deriv (buShortTimeCutoff ε) s =
      deriv (ucInitialTimeCutoff ε) (s - 1 / 2) := by
  have houter : DifferentiableAt ℝ (ucInitialTimeCutoff ε) (s - 1 / 2) :=
    (ucInitialTimeCutoff_smooth ε).differentiable (by simp) _
  have hinner : HasDerivAt (fun t : ℝ => t - 1 / 2) 1 s := by
    simpa only [id_eq] using (hasDerivAt_id s).sub_const (1 / 2 : ℝ)
  have h := (houter.hasDerivAt.comp s hinner).deriv
  change deriv (fun t => ucInitialTimeCutoff ε (t - 1 / 2)) s = _
  simpa only [Function.comp_def, mul_one] using h

/-- The absolute derivative of the short-time cutoff is at most `8/ε`. -/
theorem buShortTimeCutoff_abs_deriv_le
    {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    |deriv (buShortTimeCutoff ε) s| ≤ 8 / ε := by
  rw [buShortTimeCutoff_deriv]
  exact ucInitialTimeCutoff_abs_deriv_le hε (s - 1 / 2)

/-- The lower-time derivative vanishes before the transition strip. -/
theorem buShortTimeCutoff_deriv_eq_zero_early
    {ε s : ℝ} (hε : 0 < ε) (hs : s < 1 / 2 + ε) :
    deriv (buShortTimeCutoff ε) s = 0 := by
  have hconst : (ucInitialTimeCutoff ε) =ᶠ[nhds (s - 1 / 2)]
      (fun _ => 0) := by
    have hopen : IsOpen (Set.Iio ε) := isOpen_Iio
    have hmem : s - 1 / 2 ∈ Set.Iio ε := by
      change s - 1 / 2 < ε
      linarith only [hs]
    exact Filter.Eventually.mono (hopen.mem_nhds hmem) (fun t ht =>
      ucInitialTimeCutoff_eq_zero hε ht.le)
  rw [buShortTimeCutoff_deriv, hconst.deriv_eq]
  simp

/-- The lower-time derivative vanishes after the transition strip. -/
theorem buShortTimeCutoff_deriv_eq_zero_late
    {ε s : ℝ} (hε : 0 < ε) (hs : 1 / 2 + 2 * ε < s) :
    deriv (buShortTimeCutoff ε) s = 0 := by
  have hconst : (ucInitialTimeCutoff ε) =ᶠ[nhds (s - 1 / 2)]
      (fun _ => 1) := by
    have hopen : IsOpen (Set.Ioi (2 * ε)) := isOpen_Ioi
    have hmem : s - 1 / 2 ∈ Set.Ioi (2 * ε) := by
      change 2 * ε < s - 1 / 2
      linarith only [hs]
    exact Filter.Eventually.mono (hopen.mem_nhds hmem) (fun t ht =>
      ucInitialTimeCutoff_eq_one hε ht.le)
  rw [buShortTimeCutoff_deriv, hconst.deriv_eq]
  simp

end ESS
