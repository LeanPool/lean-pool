/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.PhysicalContourWeights

/-! # Borel weights on the actual regular chart and physical contour -/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory
open scoped ENNReal

/-- Regular chart map extension. -/
noncomputable def regularChartMapExtension (m : ℝ) (Λ : Spacetime ≃L[ℝ] Spacetime) :
    (Fin 3 → ℂ) → ComplexSpacetime := by
  classical
  exact (complexShellChartDomain m).piecewise (lorentzComplexShellChart m Λ) 0

theorem measurable_regularChartMapExtension (m : ℝ) (Λ : Spacetime ≃L[ℝ] Spacetime) :
    Measurable (regularChartMapExtension m Λ) := by
  classical
  apply ContinuousOn.measurable_piecewise _ continuous_const.continuousOn
    (isOpen_complexShellChartDomain m).measurableSet
  exact fun w hw => (differentiableAt_lorentzComplexShellChart Λ hw).continuousAt.continuousWithinAt

theorem measurable_regularChartWeight_of_measurable (m : ℝ)
    (Λ : Spacetime ≃L[ℝ] Spacetime) {F : ComplexSpacetime → ℝ≥0∞} (hF : Measurable F) :
    Measurable (regularChartWeight m Λ F) := by
  classical
  have he : regularChartWeight m Λ F = (complexShellChartDomain m).indicator
      (fun w => F (regularChartMapExtension m Λ w)) := by
    funext w
    by_cases hw : w ∈ complexShellChartDomain m
    · simp only [regularChartWeight, regularChartMapExtension,
        Set.piecewise_eq_of_mem _ _ _ hw, Set.indicator_of_mem hw]
    · simp only [regularChartWeight, Set.piecewise_eq_of_notMem _ _ _ hw,
        Set.indicator_of_notMem hw, Pi.zero_apply]
  rw [he]
  exact (hF.comp (measurable_regularChartMapExtension m Λ)).indicator
    (isOpen_complexShellChartDomain m).measurableSet

theorem measurable_physicalContourCutoffWeight_of_measurable (m θ R : ℝ)
    (Λ : Spacetime ≃L[ℝ] Spacetime) {F : ComplexSpacetime → ℝ≥0∞} (hF : Measurable F) :
    Measurable (physicalContourCutoffWeight m θ R Λ F) :=
  (hF.comp (continuous_physicalContourPoint m θ Λ).measurable).indicator
    (isClosed_le ((continuous_dispersion m).comp continuous_snd) continuous_const).measurableSet

end VacuumBellSeparation
