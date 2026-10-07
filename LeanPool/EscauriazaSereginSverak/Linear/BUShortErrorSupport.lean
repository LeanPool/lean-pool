/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCoreRegion
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortHeatSq

/-!
# Location of the short-time cutoff error

The scalar heat error vanishes below the normal transition and on the
interior plateau. Thus every nonzero error is in the phase transition,
the spatial shell, or the lower-time transition.
-/

public section


open Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The full cutoff vanishes on the open region below its normal
transition height. -/
theorem buShortFullCutoff_eq_zero_below_normal
    (scale R ε : ℝ) (hR : 0 < R) :
    EqOn (buShortFullCutoff scale R hR ε) (fun _ => 0)
      {q : Vec3 × ℝ | q.1 2 < buShortYMinus scale} := by
  intro q hq
  have hnormal : buShortNormalCutoff scale (q.1 2) = 0 :=
    buShortNormalCutoff_eq_zero hq.le
  unfold buShortFullCutoff buShortEtaExt
  rw [hnormal]
  ring

/-- Every derivative entering the scalar heat error vanishes below the
normal transition height. -/
theorem buShortFullCutoff_derivatives_zero_below_normal
    (scale R ε : ℝ) (hR : 0 < R)
    {z : ParabolicPoint} (hz : z.1 2 < buShortYMinus scale) :
    (∀ j : Fin 3,
      spatialPartial (buCutScalar (buShortFullCutoff scale R hR ε)) j z = 0) ∧
      (∀ j k : Fin 3,
        spatialSecondPartial (buCutScalar
          (buShortFullCutoff scale R hR ε)) j k z = 0) ∧
      timePartial (buCutScalar (buShortFullCutoff scale R hR ε)) z = 0 := by
  have hopen : IsOpen {q : Vec3 × ℝ | q.1 2 < buShortYMinus scale} := by
    exact isOpen_lt ((continuous_apply 2).comp continuous_fst) continuous_const
  exact buCutScalar_derivatives_eq_zero_of_eqOn hopen
    (buShortFullCutoff_eq_zero_below_normal scale R ε hR) hz

/-- The scalar cutoff error is zero below the normal transition. -/
theorem buShortCutoffHeatErrorSize_eq_zero_below_normal
    (scale R ε c₁ : ℝ) (hR : 0 < R)
    (v : ParabolicPoint → Vec3)
    (Dv : ParabolicPoint → Fin 3 → Vec3)
    {z : ParabolicPoint} (hz : z.1 2 < buShortYMinus scale) :
    buShortCutoffHeatErrorSize scale R hR ε c₁ v Dv z = 0 := by
  obtain ⟨hsp, hsp2, ht⟩ :=
    buShortFullCutoff_derivatives_zero_below_normal scale R ε hR hz
  simp [buShortCutoffHeatErrorSize, buShortCutoffGradientSize,
    hsp, hsp2, ht]

/-- The scalar cutoff error is zero on its open plateau. -/
theorem buShortCutoffHeatErrorSize_eq_zero_on_core
    (scale R ε c₁ : ℝ) (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    (hR : 0 < R) (hε : 0 < ε)
    (v : ParabolicPoint → Vec3)
    (Dv : ParabolicPoint → Fin 3 → Vec3)
    {z : ParabolicPoint}
    (hz : parabolicHomeomorph z ∈ buShortCoreRegion scale R ε) :
    buShortCutoffHeatErrorSize scale R hR ε c₁ v Dv z = 0 := by
  obtain ⟨hsp, hsp2, ht⟩ :=
    buShortFullCutoff_derivatives_zero_on_core scale R ε
      hscale hscale1 hR hε hz
  simp [buShortCutoffHeatErrorSize, buShortCutoffGradientSize,
    hsp, hsp2, ht]

/-- A nonzero scalar heat error lies in the normal transition or in one
of the three other cutoff transition regions. -/
theorem buShortCutoffHeatErrorSize_location
    (scale R ε c₁ : ℝ) (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    (hR : 0 < R) (hε : 0 < ε)
    (v : ParabolicPoint → Vec3)
    (Dv : ParabolicPoint → Fin 3 → Vec3)
    {z : ParabolicPoint}
    (hz : buShortCutoffHeatErrorSize scale R hR ε c₁ v Dv z ≠ 0)
    (hs : 1 / 2 < z.2) (hs1 : z.2 < 1) :
    buShortYMinus scale ≤ z.1 2 ∧
      (z.1 ∉ vec3Ball 0 R ∨ z.2 ≤ 1 / 2 + 2 * ε ∨
        buShortFExt (z.1 2) z.2 - buShortB scale ≤ -buShortD scale / 2) := by
  have hy : buShortYMinus scale ≤ z.1 2 := by
    by_contra hnot
    exact hz (buShortCutoffHeatErrorSize_eq_zero_below_normal
      scale R ε c₁ hR v Dv (lt_of_not_ge hnot))
  refine ⟨hy, ?_⟩
  by_contra hnot
  push Not at hnot
  have hy2 : 2 ≤ z.1 2 := by
    have hthree : 1 < 3 / scale := by
      apply (lt_div_iff₀ hscale).2
      linarith only [hscale1]
    have hminus : 2 < buShortYMinus scale := by
      dsimp [buShortYMinus]
      linarith only [hthree]
    exact hminus.le.trans hy
  have hphase : -buShortD scale / 2 <
      buShortF (z.1 2) z.2 - buShortB scale := by
    rw [← buShortFExt_eq hy2 hs.le]
    exact hnot.2.2
  have hyplus := buShort_above_gap_above_transition
    (by linarith only [hy2]) hs.le hs1.le hphase
  have hystrict : buShortYMinus scale < z.1 2 := by
    have hwidth := buShortYPlus_sub_YMinus scale
    linarith only [hyplus, hwidth]
  have hcore : parabolicHomeomorph z ∈ buShortCoreRegion scale R ε := by
    exact ⟨hnot.1, ⟨hystrict, hs, hs1, hnot.2.2⟩, hnot.2.1⟩
  exact hz (buShortCutoffHeatErrorSize_eq_zero_on_core
    scale R ε c₁ hscale hscale1 hR hε v Dv hcore)

end ESS
