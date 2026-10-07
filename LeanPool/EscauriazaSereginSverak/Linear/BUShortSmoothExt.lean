/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortWeight

/-!
# Smooth extension of the short-time phase

The phase can be smoothly clamped below the active normal and time ranges.
This gives a globally smooth cutoff with the prescribed values on the
half-space Carleman cylinder.
-/

public section


open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- A positive smooth extension of the normal height, equal to the height
above two. -/
@[expose] def buShortClampedHeight (y : ℝ) : ℝ :=
  1 + smoothTransitionProfile (y - 1) * (y - 1)

/-- A positive smooth extension of the time, equal to the time from one
half onward. -/
@[expose] def buShortClampedTime (s : ℝ) : ℝ :=
  1 / 4 + smoothTransitionProfile (4 * s - 1) * (s - 1 / 4)

/-- The clamped normal height is positive everywhere. -/
theorem buShortClampedHeight_pos (y : ℝ) :
    0 < buShortClampedHeight y := by
  by_cases hy : y ≤ 1
  · have hp : smoothTransitionProfile (y - 1) = 0 :=
      smoothTransitionProfile.zero_of_nonpos (sub_nonpos.mpr hy)
    simp [buShortClampedHeight, hp]
  · have hy' : 0 ≤ y - 1 := sub_nonneg.mpr (le_of_lt (lt_of_not_ge hy))
    have hp : 0 ≤ smoothTransitionProfile (y - 1) :=
      smoothTransitionProfile.nonneg _
    dsimp [buShortClampedHeight]
    positivity

/-- The clamped time is positive everywhere. -/
theorem buShortClampedTime_pos (s : ℝ) :
    0 < buShortClampedTime s := by
  by_cases hs : s ≤ 1 / 4
  · have hp : smoothTransitionProfile (4 * s - 1) = 0 := by
      apply smoothTransitionProfile.zero_of_nonpos
      linarith only [hs]
    simp [buShortClampedTime, hp]
  · have hs' : 0 ≤ s - 1 / 4 := sub_nonneg.mpr (le_of_lt (lt_of_not_ge hs))
    have hp : 0 ≤ smoothTransitionProfile (4 * s - 1) :=
      smoothTransitionProfile.nonneg _
    dsimp [buShortClampedTime]
    positivity

/-- The clamped height agrees with height above two. -/
theorem buShortClampedHeight_eq {y : ℝ} (hy : 2 ≤ y) :
    buShortClampedHeight y = y := by
  have hp : smoothTransitionProfile (y - 1) = 1 :=
    smoothTransitionProfile.one_of_one_le (by linarith only [hy])
  simp [buShortClampedHeight, hp]

/-- The clamped time agrees with time from one half onward. -/
theorem buShortClampedTime_eq {s : ℝ} (hs : 1 / 2 ≤ s) :
    buShortClampedTime s = s := by
  have hp : smoothTransitionProfile (4 * s - 1) = 1 :=
    smoothTransitionProfile.one_of_one_le (by linarith only [hs])
  dsimp [buShortClampedTime]
  rw [hp]
  ring

/-- Both clamping functions are smooth. -/
theorem buShortClampedHeight_smooth :
    ContDiff ℝ (⊤ : ℕ∞) buShortClampedHeight := by
  unfold buShortClampedHeight
  exact contDiff_const.add
    ((smoothTransitionProfile.smooth.comp (contDiff_id.sub contDiff_const)).mul
      (contDiff_id.sub contDiff_const))

/-- The time clamp is smooth. -/
theorem buShortClampedTime_smooth :
    ContDiff ℝ (⊤ : ℕ∞) buShortClampedTime := by
  unfold buShortClampedTime
  exact contDiff_const.add
    ((smoothTransitionProfile.smooth.comp
      (contDiff_const.mul contDiff_id |>.sub contDiff_const)).mul
        (contDiff_id.sub contDiff_const))

/-- The globally smooth normal phase used to define the cutoff. -/
@[expose] def buShortFExt (y s : ℝ) : ℝ :=
  (1 - buShortClampedTime s) *
    buShortClampedHeight y ^ (3 / 2 : ℝ) *
      buShortClampedTime s ^ (-(3 / 4 : ℝ))

/-- The extended phase agrees with the normal Carleman phase on the active
height and time range. -/
theorem buShortFExt_eq {y s : ℝ} (hy : 2 ≤ y) (hs : 1 / 2 ≤ s) :
    buShortFExt y s = buShortF y s := by
  simp only [buShortFExt, buShortF, buShortClampedHeight_eq hy,
    buShortClampedTime_eq hs]

/-- The extended normal phase is smooth in both variables. -/
theorem buShortFExt_smooth :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => buShortFExt q.1 q.2) := by
  have hy : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ => buShortClampedHeight q.1) :=
    buShortClampedHeight_smooth.comp contDiff_fst
  have hs : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ => buShortClampedTime q.2) :=
    buShortClampedTime_smooth.comp contDiff_snd
  have hypow : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ => buShortClampedHeight q.1 ^ (3 / 2 : ℝ)) :=
    hy.rpow_const_of_ne (fun q => (buShortClampedHeight_pos q.1).ne')
  have hspow : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ => buShortClampedTime q.2 ^ (-(3 / 4 : ℝ))) :=
    hs.rpow_const_of_ne (fun q => (buShortClampedTime_pos q.2).ne')
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun q : ℝ × ℝ => (1 - buShortClampedTime q.2) *
      buShortClampedHeight q.1 ^ (3 / 2 : ℝ) *
        buShortClampedTime q.2 ^ (-(3 / 4 : ℝ)))
  exact ((contDiff_const.sub hs).mul hypow).mul hspow

/-- A smooth extension of the normal-phase cutoff. -/
@[expose] def buShortEtaExt (scale : ℝ) (q : Vec3 × ℝ) : ℝ :=
  buShortNormalCutoff scale (q.1 2) *
    buShortPhaseCutoff
      ((buShortFExt (q.1 2) q.2 - buShortB scale) / buShortB scale)

/-- The smooth extension agrees with the geometric cutoff in the active
normal and time range. -/
theorem buShortEtaExt_eq {scale : ℝ} (hscale : 0 < scale)
    (hscale1 : scale ≤ 1)
    {q : Vec3 × ℝ} (hy : buShortYMinus scale < q.1 2)
    (hs : 1 / 2 ≤ q.2) :
    buShortEtaExt scale q = buShortCutoff scale (q.1 2) q.2 := by
  have hy2 : 2 ≤ q.1 2 := by
    have hminus : 2 < buShortYMinus scale := by
      dsimp [buShortYMinus]
      have h : 1 < 3 / scale := by
        apply (lt_div_iff₀ hscale).2
        linarith only [hscale1]
      linarith only [h]
    exact (le_of_lt hminus).trans hy.le
  simp only [buShortEtaExt, buShortCutoff, buShortFExt_eq hy2 hs]

/-- The smooth extension equals one above the negative transition gap
inside the active cylinder. -/
theorem buShortEtaExt_eq_one_above_gap
    {scale : ℝ} (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    {q : Vec3 × ℝ} (hy : 0 < q.1 2)
    (hs : 1 / 2 ≤ q.2) (hs1 : q.2 ≤ 1)
    (hphase : -buShortD scale / 2 <
      buShortF (q.1 2) q.2 - buShortB scale) :
    buShortEtaExt scale q = 1 := by
  have hyplus := buShort_above_gap_above_transition hy.le hs hs1 hphase
  have hyminus : buShortYMinus scale < q.1 2 := by
    have hwidth := buShortYPlus_sub_YMinus scale
    linarith only [hyplus, hwidth]
  rw [buShortEtaExt_eq hscale hscale1 hyminus hs]
  exact buShortCutoff_eq_one_above_gap hscale hy.le hs hs1 hphase

private theorem buShort_heightCoord_smooth :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : Vec3 × ℝ => q.1 2) := by
  exact (ContinuousLinearMap.proj 2 : Vec3 →L[ℝ] ℝ).contDiff.comp contDiff_fst

/-- The extended phase is smooth in product space-time coordinates. -/
theorem buShortFExt_product_smooth :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun q : Vec3 × ℝ => buShortFExt (q.1 2) q.2) := by
  have hpair : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : Vec3 × ℝ => ((q.1 2, q.2) : ℝ × ℝ)) :=
    buShort_heightCoord_smooth.prodMk
      (contDiff_snd : ContDiff ℝ (⊤ : ℕ∞) (fun q : Vec3 × ℝ => q.2))
  have hcomp := buShortFExt_smooth.comp hpair
  simpa only [Function.comp_def] using hcomp

private theorem buShortNormalCutoff_product_smooth (scale : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun q : Vec3 × ℝ => buShortNormalCutoff scale (q.1 2)) := by
  unfold buShortNormalCutoff
  exact smoothTransitionProfile.smooth.comp
    ((buShort_heightCoord_smooth.sub contDiff_const).div_const _)

private theorem buShortPhaseCutoff_product_smooth (scale : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun q : Vec3 × ℝ => buShortPhaseCutoff
        ((buShortFExt (q.1 2) q.2 - buShortB scale) / buShortB scale)) := by
  unfold buShortPhaseCutoff
  exact smoothTransitionProfile.smooth.comp
    (contDiff_const.mul
      ((buShortFExt_product_smooth.sub contDiff_const).div_const _) |>.add
        contDiff_const)

/-- The extended normal-phase cutoff is smooth on the full product space. -/
theorem buShortEtaExt_smooth (scale : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (buShortEtaExt scale) := by
  exact (buShortNormalCutoff_product_smooth scale).mul
    (buShortPhaseCutoff_product_smooth scale)

end ESS
