/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortUniformError

/-!
# Closed normal edge of the negative phase gap

Including the closed lower edge of the normal transition lets every
nonzero cutoff error be assigned to the negative phase region or the
spatial shell.
-/

public section


open Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The negative phase region including the lower normal transition
edge. -/
@[expose] def buShortWideGapRegion (scale : ℝ) : Set ParabolicPoint :=
  {z | buShortYMinus scale ≤ z.1 2 ∧
    (1 / 2 : ℝ) < z.2 ∧ z.2 < 1 ∧
    buShortFExt (z.1 2) z.2 - buShortB scale ≤ -buShortD scale / 2}

/-- The region containing all normal-phase derivative errors is
measurable. -/
theorem buShortWideGapRegion_measurable (scale : ℝ) :
    MeasurableSet (buShortWideGapRegion scale) := by
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
      buShortFExt (z.1 2) z.2 - buShortB scale) := by
    exact (buShortFExt_product_smooth.continuous.comp
      parabolicHomeomorph.continuous).sub continuous_const
  unfold buShortWideGapRegion
  have h₁ := (isClosed_le (continuous_const : Continuous
    (fun _ : ParabolicPoint => buShortYMinus scale)) hheight).measurableSet
  have h₂ := (isOpen_lt (continuous_const : Continuous
    (fun _ : ParabolicPoint => (1 / 2 : ℝ))) htime).measurableSet
  have h₃ := (isOpen_lt htime (continuous_const : Continuous
    (fun _ : ParabolicPoint => (1 : ℝ)))).measurableSet
  have h₄ := (isClosed_le hphase (continuous_const : Continuous
    (fun _ : ParabolicPoint => -buShortD scale / 2))).measurableSet
  simpa only [Set.ofPred_and] using h₁.inter (h₂.inter (h₃.inter h₄))

/-- The shifted weight gains the fixed negative phase factor on the
wide gap region. -/
theorem buShortShiftedWeight_le_on_wideGap
    {scale a : ℝ} (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    (ha : 0 ≤ a) {z : ParabolicPoint}
    (hz : z ∈ buShortWideGapRegion scale) :
    buShortShiftedWeight scale a z ≤
      Real.exp (-(z.1 0 ^ 2 + z.1 1 ^ 2) / (4 * z.2)) *
        Real.exp (-(a * buShortD scale)) := by
  have hthree : 1 < 3 / scale := by
    apply (lt_div_iff₀ hscale).2
    linarith only [hscale1]
  have hy2 : 2 ≤ z.1 2 := by
    have hminus : 2 < buShortYMinus scale := by
      dsimp [buShortYMinus]
      linarith only [hthree]
    exact hminus.le.trans hz.1
  have hphase : buShortF (z.1 2) z.2 - buShortB scale ≤
      -buShortD scale / 2 := by
    rw [← buShortFExt_eq hy2 hz.2.1.le]
    exact hz.2.2.2
  exact buShortShiftedWeight_le_gap scale a ha z
    (lt_trans (by norm_num) hz.2.1) hz.2.2.1.le hphase

/-- Any nonzero cutoff error above the negative phase gap lies on the
open plateau of the normal cutoff. -/
theorem buShortCutoffHeatErrorSize_aboveGap_of_not_wideGap
    {scale R ε c₁ : ℝ} (hscale : 0 < scale)
    (hscale1 : scale ≤ 1) (hR : 0 < R) (hε : 0 < ε)
    (v : ParabolicPoint → Vec3)
    (Dv : ParabolicPoint → Fin 3 → Vec3)
    {z : ParabolicPoint}
    (hs : 1 / 2 < z.2) (hs1 : z.2 < 1)
    (hz : buShortCutoffHeatErrorSize scale R hR ε c₁ v Dv z ≠ 0)
    (hnot : z ∉ buShortWideGapRegion scale) :
    parabolicHomeomorph z ∈ buShortAboveGap scale := by
  have hloc := buShortCutoffHeatErrorSize_location
    scale R ε c₁ hscale hscale1 hR hε v Dv hz hs hs1
  have hy : buShortYMinus scale ≤ z.1 2 := hloc.1
  have hphase : -buShortD scale / 2 <
      buShortFExt (z.1 2) z.2 - buShortB scale := by
    have hnot' : ¬(buShortFExt (z.1 2) z.2 - buShortB scale ≤
        -buShortD scale / 2) := by
      intro hle
      exact hnot ⟨hy, hs, hs1, hle⟩
    exact lt_of_not_ge hnot'
  have hthree : 1 < 3 / scale := by
    apply (lt_div_iff₀ hscale).2
    linarith only [hscale1]
  have hy2 : 2 ≤ z.1 2 := by
    have hminus : 2 < buShortYMinus scale := by
      dsimp [buShortYMinus]
      linarith only [hthree]
    exact hminus.le.trans hy
  have hphaseF : -buShortD scale / 2 <
      buShortF (z.1 2) z.2 - buShortB scale := by
    rw [← buShortFExt_eq hy2 hs.le]
    exact hphase
  have hyplus := buShort_above_gap_above_transition
    (by linarith only [hy2]) hs.le hs1.le hphaseF
  have hwidth := buShortYPlus_sub_YMinus scale
  have hystrict : buShortYMinus scale < z.1 2 := by
    linarith only [hyplus, hwidth]
  exact ⟨hystrict, hs, hs1, hphase⟩

end ESS
