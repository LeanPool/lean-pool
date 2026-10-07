/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortProductDerivatives
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortTimeFactor

/-!
# Derivatives of the spatial and normal cutoffs

The two-factor cutoff separates the normal-phase derivatives from the
spatial shell derivatives.
-/

public section


open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- First spatial product rule for the two-factor cutoff. -/
theorem buShortSpacePhase_spatialPartial
    (scale R : ℝ) (hR : 0 < R)
    (j : Fin 3) (z : ParabolicPoint) :
    spatialPartial (buCutScalar (buShortSpacePhaseCutoff scale R hR)) j z =
      spatialPartial
          (fun q : ParabolicPoint =>
            ucSpatialCutoff (2 * R) (by positivity) q.1) j z *
        buShortEtaExt scale (z.1, z.2) +
      ucSpatialCutoff (2 * R) (by positivity) z.1 *
        spatialPartial (buCutScalar (buShortEtaExt scale)) j z := by
  have hχ : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : Vec3 × ℝ =>
        ucSpatialCutoff (2 * R) (by positivity) q.1) :=
    (ucSpatialCutoff_smooth (show 0 < 2 * R by positivity)).comp
      contDiff_fst
  have hη := buShortEtaExt_smooth scale
  change spatialPartial
    (fun q : ParabolicPoint =>
      ucSpatialCutoff (2 * R) (by positivity) q.1 *
        buShortEtaExt scale (q.1, q.2)) j z = _
  exact CKN.Core.Step3.spatialPartial_mul_full hχ hη j z

/-- Diagonal spatial second product rule for the two-factor cutoff. -/
theorem buShortSpacePhase_spatialSecondPartial_diag
    (scale R : ℝ) (hR : 0 < R)
    (j : Fin 3) (z : ParabolicPoint) :
    spatialSecondPartial
        (buCutScalar (buShortSpacePhaseCutoff scale R hR)) j j z =
      spatialSecondPartial
          (fun q : ParabolicPoint =>
            ucSpatialCutoff (2 * R) (by positivity) q.1) j j z *
        buShortEtaExt scale (z.1, z.2) +
      2 * spatialPartial
          (fun q : ParabolicPoint =>
            ucSpatialCutoff (2 * R) (by positivity) q.1) j z *
        spatialPartial (buCutScalar (buShortEtaExt scale)) j z +
      ucSpatialCutoff (2 * R) (by positivity) z.1 *
        spatialSecondPartial
          (buCutScalar (buShortEtaExt scale)) j j z := by
  have hχ : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : Vec3 × ℝ =>
        ucSpatialCutoff (2 * R) (by positivity) q.1) :=
    (ucSpatialCutoff_smooth (show 0 < 2 * R by positivity)).comp
      contDiff_fst
  have hη := buShortEtaExt_smooth scale
  change spatialSecondPartial
    (fun q : ParabolicPoint =>
      ucSpatialCutoff (2 * R) (by positivity) q.1 *
        buShortEtaExt scale (q.1, q.2)) j j z = _
  exact bu_spatialSecondPartial_mul_full hχ hη j z

/-- The spatial cutoff has zero time derivative. -/
theorem buShortSpatialCutoff_timePartial_zero
    (R : ℝ) (hR : 0 < R) (z : ParabolicPoint) :
    timePartial
      (fun q : ParabolicPoint =>
        ucSpatialCutoff (2 * R) (by positivity) q.1) z = 0 := by
  unfold timePartial
  simp

/-- The time derivative of the two-factor cutoff comes entirely from
the normal-phase factor. -/
theorem buShortSpacePhase_timePartial
    (scale R : ℝ) (hR : 0 < R) (z : ParabolicPoint) :
    timePartial (buCutScalar (buShortSpacePhaseCutoff scale R hR)) z =
      ucSpatialCutoff (2 * R) (by positivity) z.1 *
        timePartial (buCutScalar (buShortEtaExt scale)) z := by
  have hχ : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : Vec3 × ℝ =>
        ucSpatialCutoff (2 * R) (by positivity) q.1) :=
    (ucSpatialCutoff_smooth (show 0 < 2 * R by positivity)).comp
      contDiff_fst
  have hη := buShortEtaExt_smooth scale
  change timePartial
    (fun q : ParabolicPoint =>
      ucSpatialCutoff (2 * R) (by positivity) q.1 *
        buShortEtaExt scale (q.1, q.2)) z = _
  have hproduct := CKN.Core.Step3.timePartial_mul_full hχ hη z
  change timePartial
      (fun q : ParabolicPoint =>
        ucSpatialCutoff (2 * R) (by positivity) q.1 *
          buShortEtaExt scale (q.1, q.2)) z =
      timePartial
          (fun q : ParabolicPoint =>
            ucSpatialCutoff (2 * R) (by positivity) q.1) z *
        buShortEtaExt scale (z.1, z.2) +
      ucSpatialCutoff (2 * R) (by positivity) z.1 *
        timePartial (buCutScalar (buShortEtaExt scale)) z at hproduct
  rw [hproduct, buShortSpatialCutoff_timePartial_zero R hR z]
  ring

end ESS
