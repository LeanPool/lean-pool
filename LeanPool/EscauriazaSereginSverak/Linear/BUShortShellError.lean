/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortSpacePhaseSize

/-!
# Shell derivatives above the phase gap

On the normal-phase plateau only the spatial ball cutoff contributes to
the spatial and heat derivative sizes.
-/

public section


open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- Above the negative phase gap, the gradient size is bounded by the
spatial shell derivative. -/
theorem buShortSpacePhaseGradientSize_shell_on_aboveGap
    {scale R : ℝ} (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    (hR : 0 < R) {z : ParabolicPoint}
    (hz : parabolicHomeomorph z ∈ buShortAboveGap scale) :
    buShortSpacePhaseGradientSize scale R hR z ≤
      3 * (cutoffGradientConstant / (2 * R)) := by
  have hη := buShortEtaExt_eq_one_on_aboveGap hscale hscale1 hz
  have hη' : buShortEtaExt scale (z.1, z.2) = 1 := by
    simpa only [parabolicHomeomorph_apply] using hη
  obtain ⟨hsp, _, _⟩ :=
    buShortEtaExt_derivatives_zero_aboveGap hscale hscale1 hz
  unfold buShortSpacePhaseGradientSize
  calc
    _ ≤ ∑ _j : Fin 3, cutoffGradientConstant / (2 * R) := by
      apply Finset.sum_le_sum
      intro j _
      rw [buShortSpacePhase_spatialPartial scale R hR j z,
        hη', hsp j]
      simp only [mul_one, mul_zero, add_zero]
      exact ucSpatialCutoff_spatialPartial_bound
        (show 0 < 2 * R by positivity) z j
    _ = _ := by simp

/-- Above the negative phase gap, the scalar heat size is bounded by
the spatial shell second derivatives. -/
theorem buShortSpacePhaseHeatSize_shell_on_aboveGap
    {scale R : ℝ} (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    (hR : 0 < R) {z : ParabolicPoint}
    (hz : parabolicHomeomorph z ∈ buShortAboveGap scale) :
    buShortSpacePhaseHeatSize scale R hR z ≤
      3 * (cutoffSecondDerivativeConstant / (2 * R) ^ 2) := by
  have hη := buShortEtaExt_eq_one_on_aboveGap hscale hscale1 hz
  have hη' : buShortEtaExt scale (z.1, z.2) = 1 := by
    simpa only [parabolicHomeomorph_apply] using hη
  obtain ⟨hsp, hsp₂, ht⟩ :=
    buShortEtaExt_derivatives_zero_aboveGap hscale hscale1 hz
  have htime : timePartial
      (buCutScalar (buShortSpacePhaseCutoff scale R hR)) z = 0 := by
    rw [buShortSpacePhase_timePartial scale R hR z, ht]
    ring
  have hsecond (j : Fin 3) :
      spatialSecondPartial
        (buCutScalar (buShortSpacePhaseCutoff scale R hR)) j j z =
      spatialSecondPartial
        (fun q : ParabolicPoint =>
          ucSpatialCutoff (2 * R) (by positivity) q.1) j j z := by
    rw [buShortSpacePhase_spatialSecondPartial_diag scale R hR j z,
      hη', hsp j, hsp₂ j j]
    ring
  unfold buShortSpacePhaseHeatSize
  rw [htime]
  simp only [zero_add]
  simp_rw [hsecond]
  calc
    _ ≤ ∑ j : Fin 3,
        |spatialSecondPartial
          (fun q : ParabolicPoint =>
            ucSpatialCutoff (2 * R) (by positivity) q.1) j j z| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin 3,
        cutoffSecondDerivativeConstant / (2 * R) ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      exact ucSpatialCutoff_spatialSecondPartial_bound
        (show 0 < 2 * R by positivity) z j j
    _ = _ := by simp

end ESS
