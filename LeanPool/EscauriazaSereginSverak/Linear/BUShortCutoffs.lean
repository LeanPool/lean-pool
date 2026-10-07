/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCutoffGeometry
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.Profile

/-!
# Normal and phase cutoffs for short-time vanishing

The cutoff in `lem:bu-small-time` turns on above the normal transition
and on the positive shifted phase region.
-/

public section


open CKN

noncomputable section

namespace ESS

/-- The lower edge of the normal cutoff transition. -/
@[expose] def buShortYMinus (scale : ℝ) : ℝ := 3 / scale + 1

/-- The smooth normal cutoff. -/
@[expose] def buShortNormalCutoff (scale : ℝ) (y : ℝ) : ℝ :=
  smoothTransitionProfile
    ((y - buShortYMinus scale) /
      (buShortYPlus scale - buShortYMinus scale))

/-- The smooth shifted-phase cutoff. -/
@[expose] def buShortPhaseCutoff (u : ℝ) : ℝ :=
  smoothTransitionProfile (12 * u + 9)

/-- The product of the normal and shifted-phase cutoffs. -/
@[expose] def buShortCutoff (scale : ℝ) (y s : ℝ) : ℝ :=
  buShortNormalCutoff scale y *
    buShortPhaseCutoff
      ((buShortF y s - buShortB scale) / buShortB scale)

/-- The normal transition interval has width one half. -/
theorem buShortYPlus_sub_YMinus (scale : ℝ) :
    buShortYPlus scale - buShortYMinus scale = 1 / 2 := by
  dsimp [buShortYPlus, buShortYMinus]
  ring

/-- The normal cutoff vanishes below its lower transition height. -/
theorem buShortNormalCutoff_eq_zero {scale y : ℝ}
    (hy : y ≤ buShortYMinus scale) :
    buShortNormalCutoff scale y = 0 := by
  unfold buShortNormalCutoff
  apply smoothTransitionProfile.zero_of_nonpos
  rw [buShortYPlus_sub_YMinus]
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hy) (by norm_num)

/-- The normal cutoff equals one above its upper transition height. -/
theorem buShortNormalCutoff_eq_one {scale y : ℝ}
    (hy : buShortYPlus scale ≤ y) :
    buShortNormalCutoff scale y = 1 := by
  unfold buShortNormalCutoff
  apply smoothTransitionProfile.one_of_one_le
  rw [buShortYPlus_sub_YMinus]
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 1 / 2)).2
  have hwidth := buShortYPlus_sub_YMinus scale
  linarith only [hy, hwidth]

/-- The phase cutoff vanishes below the lower transition level. -/
theorem buShortPhaseCutoff_eq_zero {u : ℝ}
    (hu : u ≤ -(3 / 4 : ℝ)) :
    buShortPhaseCutoff u = 0 := by
  unfold buShortPhaseCutoff
  apply smoothTransitionProfile.zero_of_nonpos
  linarith only [hu]

/-- The phase cutoff equals one above the upper transition level. -/
theorem buShortPhaseCutoff_eq_one {u : ℝ}
    (hu : -(2 / 3 : ℝ) ≤ u) :
    buShortPhaseCutoff u = 1 := by
  unfold buShortPhaseCutoff
  apply smoothTransitionProfile.one_of_one_le
  linarith only [hu]

/-- The product cutoff vanishes below the lower shifted-phase level. -/
theorem buShortCutoff_eq_zero_of_low_phase
    {scale y s : ℝ}
    (hphase : (buShortF y s - buShortB scale) / buShortB scale ≤
      -(3 / 4 : ℝ)) :
    buShortCutoff scale y s = 0 := by
  unfold buShortCutoff
  rw [buShortPhaseCutoff_eq_zero hphase, mul_zero]

/-- The cutoff is one throughout the region above its negative phase
transition gap. -/
theorem buShortCutoff_eq_one_above_gap
    {scale y s : ℝ} (hscale : 0 < scale)
    (hy : 0 ≤ y) (hs : 1 / 2 ≤ s) (hs1 : s ≤ 1)
    (hphase : -buShortD scale / 2 < buShortF y s - buShortB scale) :
    buShortCutoff scale y s = 1 := by
  have hyplus := buShort_above_gap_above_transition hy hs hs1 hphase
  have hB := buShortB_pos hscale
  have hD : buShortD scale ≤ 4 * buShortB scale / 3 :=
    min_le_right _ _
  have hu : -(2 / 3 : ℝ) ≤
      (buShortF y s - buShortB scale) / buShortB scale := by
    apply (le_div_iff₀ hB).2
    linarith only [hphase, hD]
  unfold buShortCutoff
  rw [buShortNormalCutoff_eq_one hyplus.le,
    buShortPhaseCutoff_eq_one hu, one_mul]

end ESS
