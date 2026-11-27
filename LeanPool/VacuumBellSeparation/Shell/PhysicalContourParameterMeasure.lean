/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.PhysicalContourParameterCoordinates

/-! # Actual Haar scaling for the physical Lorentz/momentum coordinates -/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory
open scoped ENNReal NNReal

instance physicalParameter_sourceHaar :
    (volume : Measure ShellPhysicalParameters).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _

/-- Physical parameter measure. -/
noncomputable def physicalParameterMeasure : Measure LorentzMomentumParameters :=
  (volume : Measure (Fin 6 → ℝ)).prod
    (volume : Measure (EuclideanSpace ℝ (Fin 3)))

instance physicalParameterMeasure_haar : physicalParameterMeasure.IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _

/-- Density factor relating Haar measure on physical parameters to the coordinate volume. -/
noncomputable def physicalParameterHaarScale : ℝ≥0 :=
  linearHaarScale (volume : Measure ShellPhysicalParameters)
    physicalParameterMeasure contourParameterReorder

theorem physicalParameterHaarScale_pos : 0 < physicalParameterHaarScale :=
  linearHaarScale_pos (volume : Measure ShellPhysicalParameters)
    physicalParameterMeasure contourParameterReorder

theorem lintegral_physicalContourParameters_image (B : ℝ)
    {s : Set ShellPhysicalParameters} (hs : MeasurableSet s)
    (g : LorentzMomentumParameters → ℝ≥0∞) :
    (∫⁻ y in physicalContourParameters B '' s, g y ∂physicalParameterMeasure) =
      (physicalParameterHaarScale : ℝ≥0∞) * ∫⁻ x in s, g (physicalContourParameters B x) := by
  have hJ : contourParameterReorder.symm.toContinuousLinearMap.comp
      contourParameterReorder.toContinuousLinearMap =
      ContinuousLinearMap.id ℝ ShellPhysicalParameters := by
    apply ContinuousLinearMap.ext
    intro x
    exact contourParameterReorder.symm_apply_apply x
  have hd : (contourParameterReorder.symm.toContinuousLinearMap.comp
      contourParameterReorder.toContinuousLinearMap).det = 1 := by
    rw [hJ]
    change LinearMap.det (LinearMap.id : ShellPhysicalParameters →ₗ[ℝ] ShellPhysicalParameters) = 1
    exact LinearMap.det_id
  have h := lintegral_image_eq_linearHaarScale_jacobian
    (volume : Measure ShellPhysicalParameters) physicalParameterMeasure contourParameterReorder hs
    (fun x hx => (hasFDerivAt_physicalContourParameters B x).hasFDerivWithinAt)
    (physicalContourParameters_bijective B).1.injOn g
  simpa only [hd, abs_one, ENNReal.ofReal_one, one_mul, physicalParameterHaarScale] using h

end VacuumBellSeparation
