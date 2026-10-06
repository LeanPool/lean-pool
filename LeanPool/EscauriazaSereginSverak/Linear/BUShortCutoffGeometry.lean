/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortPhase

/-!
# Negative phase on the cutoff transition region

The normal and time transitions in `lem:bu-small-time` lie in a region
where the shifted Carleman phase is uniformly negative.
-/

public section


noncomputable section

namespace ESS

/-- The upper edge of the normal cutoff transition. -/
@[expose] def buShortYPlus (scale : ℝ) : ℝ := 3 / scale + 3 / 2

/-- The reference height above the normal cutoff transition. -/
@[expose] def buShortYZero (scale : ℝ) : ℝ := 3 / scale + 2

/-- The positive phase shift used in the short-time Carleman argument. -/
@[expose] def buShortB (scale : ℝ) : ℝ :=
  2 * buShortF (buShortYZero scale) (1 / 2)

/-- A positive gap below both transition phase levels. -/
@[expose] def buShortD (scale : ℝ) : ℝ :=
  min (-2 * (buShortF (buShortYPlus scale) (1 / 2) - buShortB scale))
    (4 * buShortB scale / 3)

/-- The reference height lies strictly above the cutoff transition. -/
theorem buShortYPlus_lt_YZero (scale : ℝ) :
    buShortYPlus scale < buShortYZero scale := by
  dsimp [buShortYPlus, buShortYZero]
  norm_num

/-- The phase shift is positive at every positive spatial scale. -/
theorem buShortB_pos {scale : ℝ} (hscale : 0 < scale) : 0 < buShortB scale := by
  have hy : 0 < buShortYZero scale := by
    dsimp [buShortYZero]
    positivity
  dsimp [buShortB]
  have hF := buShortF_pos hy (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  positivity

/-- The cutoff transition has a strictly negative phase gap. -/
theorem buShortD_pos {scale : ℝ} (hscale : 0 < scale) : 0 < buShortD scale := by
  have hyplus : 0 ≤ buShortYPlus scale := by
    dsimp [buShortYPlus]
    positivity
  have hyle := (buShortYPlus_lt_YZero scale).le
  have hFle : buShortF (buShortYPlus scale) (1 / 2) ≤
      buShortF (buShortYZero scale) (1 / 2) :=
    buShortF_mono_height hyplus hyle
      (by norm_num) (by norm_num)
  have hFpos : 0 < buShortF (buShortYZero scale) (1 / 2) := by
    have hy : 0 < buShortYZero scale := by dsimp [buShortYZero]; positivity
    exact buShortF_pos hy (by norm_num) (by norm_num)
  have hB : buShortB scale =
      2 * buShortF (buShortYZero scale) (1 / 2) := rfl
  dsimp [buShortD]
  apply lt_min
  · rw [hB]
    linarith only [hFle, hFpos]
  · exact div_pos (mul_pos (by norm_num) (buShortB_pos hscale)) (by norm_num)

/-- The spatial cutoff transition lies at least half the phase gap below
zero. -/
theorem buShort_spatial_transition_phase_le
    {scale y s : ℝ}
    (hy : 0 ≤ y) (hyle : y ≤ buShortYPlus scale)
    (hs : 1 / 2 ≤ s) (hs1 : s ≤ 1) :
    buShortF y s - buShortB scale ≤ -buShortD scale / 2 := by
  have hs0 : 0 < (1 / 2 : ℝ) := by norm_num
  have hFtime : buShortF y s ≤ buShortF y (1 / 2) :=
    buShortF_antitone_time hy hs0 hs hs1
  have hFheight : buShortF y (1 / 2) ≤
      buShortF (buShortYPlus scale) (1 / 2) :=
    buShortF_mono_height hy hyle (by norm_num) (by norm_num)
  have hD : buShortD scale ≤
      -2 * (buShortF (buShortYPlus scale) (1 / 2) - buShortB scale) :=
    min_le_left _ _
  linarith only [hFtime, hFheight, hD]

/-- A positive shifted phase occurs above the completed normal cutoff. -/
theorem buShort_positive_phase_above_transition
    {scale y s : ℝ} (hscale : 0 < scale)
    (hy : 0 ≤ y) (hs : 1 / 2 ≤ s) (hs1 : s ≤ 1)
    (hphase : 0 < buShortF y s - buShortB scale) :
    buShortYPlus scale < y := by
  by_contra hnot
  have hyle : y ≤ buShortYPlus scale := le_of_not_gt hnot
  have hFtime : buShortF y s ≤ buShortF y (1 / 2) :=
    buShortF_antitone_time hy (by norm_num) hs hs1
  have hFheight : buShortF y (1 / 2) ≤
      buShortF (buShortYPlus scale) (1 / 2) :=
    buShortF_mono_height hy hyle (by norm_num) (by norm_num)
  have hyplus : 0 ≤ buShortYPlus scale := by
    dsimp [buShortYPlus]
    positivity
  have hFplus : buShortF (buShortYPlus scale) (1 / 2) ≤
      buShortF (buShortYZero scale) (1 / 2) :=
    buShortF_mono_height hyplus (buShortYPlus_lt_YZero scale).le
      (by norm_num) (by norm_num)
  have hFzero : 0 < buShortF (buShortYZero scale) (1 / 2) := by
    have hyzero : 0 < buShortYZero scale := by
      dsimp [buShortYZero]
      positivity
    exact buShortF_pos hyzero (by norm_num) (by norm_num)
  have hB : buShortB scale =
      2 * buShortF (buShortYZero scale) (1 / 2) := rfl
  linarith only [hphase, hFtime, hFheight, hFplus, hFzero, hB]

/-- Above the negative transition gap, the normal cutoff is complete. -/
theorem buShort_above_gap_above_transition
    {scale y s : ℝ}
    (hy : 0 ≤ y) (hs : 1 / 2 ≤ s) (hs1 : s ≤ 1)
    (hphase : -buShortD scale / 2 < buShortF y s - buShortB scale) :
    buShortYPlus scale < y := by
  by_contra hnot
  have hyle : y ≤ buShortYPlus scale := le_of_not_gt hnot
  have hbound := buShort_spatial_transition_phase_le hy hyle hs hs1
  linarith only [hphase, hbound]

end ESS
