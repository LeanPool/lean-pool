/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCompactCore

/-!
# Positive normal phase

The region where the normal phase exceeds its fixed threshold is open
and lies in the plateau of the normal cutoff.
-/

public section


open Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The open positive-phase region in the rescaled half-space strip. -/
@[expose] def buShortPositivePhaseRegion (scale : ℝ) : Set ParabolicPoint :=
  {z | 2 < z.1 2 ∧ (1 / 2 : ℝ) < z.2 ∧ z.2 < 1 ∧
    buShortB scale < buShortFExt (z.1 2) z.2}

/-- The positive-phase region is open. -/
theorem buShortPositivePhaseRegion_isOpen (scale : ℝ) :
    IsOpen (buShortPositivePhaseRegion scale) := by
  have hspace : Continuous (fun z : ParabolicPoint => z.1) := by
    convert continuous_fst.comp parabolicHomeomorph.continuous using 1
    funext z
    rfl
  have hheight : Continuous (fun z : ParabolicPoint => z.1 2) :=
    (continuous_apply 2).comp hspace
  have htime : Continuous (fun z : ParabolicPoint => z.2) := by
    convert continuous_snd.comp parabolicHomeomorph.continuous using 1
    funext z
    rfl
  have hphase : Continuous (fun z : ParabolicPoint =>
      buShortFExt (z.1 2) z.2) :=
    buShortFExt_product_smooth.continuous.comp
      parabolicHomeomorph.continuous
  have h₁ := isOpen_lt (continuous_const : Continuous
    (fun _ : ParabolicPoint => (2 : ℝ))) hheight
  have h₂ := isOpen_lt (continuous_const : Continuous
    (fun _ : ParabolicPoint => (1 / 2 : ℝ))) htime
  have h₃ := isOpen_lt htime (continuous_const : Continuous
    (fun _ : ParabolicPoint => (1 : ℝ)))
  have h₄ := isOpen_lt (continuous_const : Continuous
    (fun _ : ParabolicPoint => buShortB scale)) hphase
  change IsOpen ({z : ParabolicPoint | 2 < z.1 2} ∩
    ({z : ParabolicPoint | 1 / 2 < z.2} ∩
      ({z : ParabolicPoint | z.2 < 1} ∩
        {z : ParabolicPoint | buShortB scale < buShortFExt (z.1 2) z.2})))
  exact h₁.inter (h₂.inter (h₃.inter h₄))

/-- Every positive-phase point lies above the completed normal cutoff
transition. -/
theorem buShortPositivePhaseRegion_subset_aboveGap
    {scale : ℝ} (hscale : 0 < scale) :
    buShortPositivePhaseRegion scale ⊆
      parabolicHomeomorph ⁻¹' buShortAboveGap scale := by
  intro z hz
  have hy2 : 2 ≤ z.1 2 := hz.1.le
  have hphase : 0 < buShortF (z.1 2) z.2 - buShortB scale := by
    rw [← buShortFExt_eq hy2 hz.2.1.le]
    linarith only [hz.2.2.2]
  have hD := buShortD_pos hscale
  have hgap : -buShortD scale / 2 <
      buShortF (z.1 2) z.2 - buShortB scale := by
    linarith only [hphase, hD]
  have hyplus := buShort_above_gap_above_transition
    (by linarith only [hz.1]) hz.2.1.le hz.2.2.1.le hgap
  have hwidth := buShortYPlus_sub_YMinus scale
  have hyminus : buShortYMinus scale < z.1 2 := by
    linarith only [hyplus, hwidth]
  exact ⟨hyminus, hz.2.1, hz.2.2.1, by
    change -buShortD scale / 2 <
      buShortFExt (z.1 2) z.2 - buShortB scale
    rw [buShortFExt_eq hy2 hz.2.1.le]
    exact hgap⟩

/-- On the positive phase, increasing a nonnegative Carleman parameter
can only increase the shifted weight. -/
theorem buShortShiftedWeight_zero_le_on_positive
    {scale a : ℝ} (ha : 0 ≤ a)
    {z : ParabolicPoint}
    (hz : z ∈ buShortPositivePhaseRegion scale) :
    buShortShiftedWeight scale 0 z ≤
      buShortShiftedWeight scale a z := by
  have hs : 0 < z.2 := lt_trans (by norm_num) hz.2.1
  have hphase : 0 < buShortF (z.1 2) z.2 - buShortB scale := by
    rw [← buShortFExt_eq hz.1.le hz.2.1.le]
    linarith only [hz.2.2.2]
  have harg : 0 ≤ 2 * a *
      (buShortF (z.1 2) z.2 - buShortB scale) := by
    positivity
  have hexp := Real.one_le_exp harg
  let b := z.2 ^ 2 *
    Real.exp (-(z.1 0 ^ 2 + z.1 1 ^ 2) / (4 * z.2))
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hmul := mul_le_mul_of_nonneg_left hexp hb
  rw [buShortShiftedWeight_eq scale 0 z hs,
    buShortShiftedWeight_eq scale a z hs]
  dsimp [b] at hmul
  simpa only [mul_zero, zero_mul, Real.exp_zero, mul_one] using hmul

/-- The phase-independent base of the shifted weight is continuous
throughout the positive-phase region. -/
theorem buShortShiftedWeight_zero_continuousOn_positive
    (scale : ℝ) :
    ContinuousOn (buShortShiftedWeight scale 0)
      (buShortPositivePhaseRegion scale) := by
  let U := buShortPositivePhaseRegion scale
  let b : ParabolicPoint → ℝ := fun z =>
    z.2 ^ 2 *
      Real.exp (-(z.1 0 ^ 2 + z.1 1 ^ 2) / (4 * z.2))
  have hspace : Continuous (fun z : ParabolicPoint => z.1) := by
    convert continuous_fst.comp parabolicHomeomorph.continuous using 1
    funext z
    rfl
  have htime : Continuous (fun z : ParabolicPoint => z.2) := by
    convert continuous_snd.comp parabolicHomeomorph.continuous using 1
    funext z
    rfl
  have h0 : Continuous (fun z : ParabolicPoint => z.1 0) :=
    (continuous_apply 0).comp hspace
  have h1 : Continuous (fun z : ParabolicPoint => z.1 1) :=
    (continuous_apply 1).comp hspace
  have hnum : Continuous (fun z : ParabolicPoint =>
      -(z.1 0 ^ 2 + z.1 1 ^ 2)) :=
    ((h0.pow 2).add (h1.pow 2)).neg
  have hden : Continuous (fun z : ParabolicPoint => 4 * z.2) :=
    continuous_const.mul htime
  have hdenNe : ∀ z ∈ U, 4 * z.2 ≠ 0 := by
    intro z hz
    have hs : 0 < z.2 := lt_trans (by norm_num) hz.2.1
    positivity
  have hb : ContinuousOn b U :=
    (htime.continuousOn.pow 2).mul
      (Real.continuous_exp.comp_continuousOn
        (hnum.continuousOn.div hden.continuousOn hdenNe))
  apply hb.congr
  intro z hz
  have hs : 0 < z.2 := lt_trans (by norm_num) hz.2.1
  rw [buShortShiftedWeight_eq scale 0 z hs]
  dsimp [b]
  simp only [mul_zero, zero_mul, Real.exp_zero, mul_one]

/-- The shifted half-space weight is continuous on the positive-phase
region for every fixed Carleman parameter. -/
theorem buShortShiftedWeight_continuousOn_positive
    (scale a : ℝ) :
    ContinuousOn (buShortShiftedWeight scale a)
      (buShortPositivePhaseRegion scale) := by
  let U := buShortPositivePhaseRegion scale
  let Φ : ParabolicPoint → ℝ := fun z =>
    buShortFExt (z.1 2) z.2 - buShortB scale
  have hΦ : Continuous Φ :=
    (buShortFExt_product_smooth.continuous.comp
      parabolicHomeomorph.continuous).sub continuous_const
  have hexp : ContinuousOn
      (fun z : ParabolicPoint => Real.exp (2 * a * Φ z)) U :=
    Real.continuous_exp.comp_continuousOn
      (continuousOn_const.mul hΦ.continuousOn)
  have hbase := buShortShiftedWeight_zero_continuousOn_positive scale
  have hproduct : ContinuousOn (fun z =>
      buShortShiftedWeight scale 0 z * Real.exp (2 * a * Φ z)) U :=
    hbase.mul hexp
  apply hproduct.congr
  intro z hz
  have hs : 0 < z.2 := lt_trans (by norm_num) hz.2.1
  change buShortShiftedWeight scale a z =
    buShortShiftedWeight scale 0 z * Real.exp (2 * a * Φ z)
  rw [buShortShiftedWeight_eq scale a z hs,
    buShortShiftedWeight_eq scale 0 z hs]
  have hF : buShortFExt (z.1 2) z.2 = buShortF (z.1 2) z.2 :=
    buShortFExt_eq hz.1.le hz.2.1.le
  dsimp [Φ]
  rw [hF]
  simp only [mul_zero, zero_mul, Real.exp_zero, mul_one]

end ESS
