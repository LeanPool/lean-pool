/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortPositivePhase
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Compact neighborhoods in the positive phase

Every positive-phase point has a compact neighborhood of positive
space-time measure contained in the positive-phase region.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

private instance : Measure.IsOpenPosMeasure
    (volume : Measure ParabolicPoint) where
  open_pos U hU hne := by
    have hopen : IsOpen (parabolicHomeomorph.symm ⁻¹' U) :=
      hU.preimage parabolicHomeomorph.symm.continuous
    have hnonempty : (parabolicHomeomorph.symm ⁻¹' U).Nonempty := by
      obtain ⟨z, hz⟩ := hne
      exact ⟨parabolicHomeomorph z, hz⟩
    exact hopen.measure_ne_zero
      (volume : Measure (Vec3 × ℝ)) hnonempty

/-- A positive-phase point lies in a compact positive-measure region
contained entirely in the positive phase. -/
theorem bu_short_positive_compact_neighborhood
    {scale : ℝ} {z : ParabolicPoint}
    (hz : z ∈ buShortPositivePhaseRegion scale) :
    ∃ S : Set ParabolicPoint,
      IsCompact S ∧ z ∈ S ∧
      S ⊆ buShortPositivePhaseRegion scale ∧
      z ∈ interior S ∧
      0 < (volume : Measure ParabolicPoint) S := by
  let q := parabolicHomeomorph z
  let O : Set (Vec3 × ℝ) :=
    parabolicHomeomorph.symm ⁻¹' buShortPositivePhaseRegion scale
  have hO : IsOpen O :=
    (buShortPositivePhaseRegion_isOpen scale).preimage
      parabolicHomeomorph.symm.continuous
  have hq : q ∈ O := by
    simpa only [q, O, Set.mem_preimage,
      parabolicHomeomorph.symm_apply_apply] using hz
  obtain ⟨r, hr, hball⟩ := (Metric.isOpen_iff.mp hO) q hq
  let S : Set ParabolicPoint :=
    parabolicHomeomorph ⁻¹' Metric.closedBall q (r / 2)
  have hrhalf : 0 < r / 2 := by positivity
  have hrsmall : r / 2 < r := by linarith only [hr]
  have hScompact : IsCompact S :=
    parabolicHomeomorph.isCompact_preimage.mpr
      (ProperSpace.isCompact_closedBall q (r / 2))
  have hzS : z ∈ S := by
    change q ∈ Metric.closedBall q (r / 2)
    exact Metric.mem_closedBall.mpr (by simpa using hrhalf.le)
  have hSsubset : S ⊆ buShortPositivePhaseRegion scale := by
    intro z' hz'
    have hclosed : parabolicHomeomorph z' ∈
        Metric.closedBall q (r / 2) := hz'
    have hopen : parabolicHomeomorph z' ∈ Metric.ball q r :=
      Metric.closedBall_subset_ball hrsmall hclosed
    have hmem : parabolicHomeomorph z' ∈ O := hball hopen
    simpa only [O, Set.mem_preimage,
      parabolicHomeomorph.symm_apply_apply] using hmem
  let U : Set ParabolicPoint :=
    parabolicHomeomorph ⁻¹' Metric.ball q (r / 2)
  have hUopen : IsOpen U :=
    Metric.isOpen_ball.preimage parabolicHomeomorph.continuous
  have hzU : z ∈ U := by
    change q ∈ Metric.ball q (r / 2)
    exact Metric.mem_ball_self hrhalf
  have hUS : U ⊆ S := by
    intro x hx
    exact Metric.ball_subset_closedBall hx
  have hSpos : 0 < (volume : Measure ParabolicPoint) S :=
    (hUopen.measure_pos _ ⟨z, hzU⟩).trans_le
      (measure_mono hUS)
  have hzIntU : z ∈ interior U := by
    simpa only [hUopen.interior_eq] using hzU
  have hzInt : z ∈ interior S := interior_mono hUS hzIntU
  exact ⟨S, hScompact, hzS, hSsubset, hzInt, hSpos⟩

end ESS
