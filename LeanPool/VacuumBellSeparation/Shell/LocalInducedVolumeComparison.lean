/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.InducedRegularShellVolume
public import LeanPool.VacuumBellSeparation.Shell.ComplexEuclideanVolume
public import LeanPool.VacuumBellSeparation.Shell.MeasurableContourWeights
public import LeanPool.VacuumBellSeparation.FreeField.WeightedShellEvaluationSubmean

/-!
# Actual local shell volume bounded by flat chart integrals

The upper Gram-density bound has the direction needed for contour
domination. Both measures are the genuine six-dimensional measures;
the complex Euclidean coordinate transport preserves volume exactly.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Set
open scoped ENNReal

/-- Regular shell coordinate patch defined as `inducedShellPatch m Λ ∩ shellPatchCoordinates Λ ⁻¹'
s`. -/
noncomputable def regularShellCoordinatePatch (m : ℝ) (Λ : Spacetime ≃L[ℝ] Spacetime)
    (s : Set ShellEuclideanDomain) : Set (complexShell m) :=
  inducedShellPatch m Λ ∩ shellPatchCoordinates Λ ⁻¹' s

theorem measurableSet_regularShellCoordinatePatch (m : ℝ)
    (Λ : Spacetime ≃L[ℝ] Spacetime) {s : Set ShellEuclideanDomain}
    (hs : MeasurableSet s) : MeasurableSet (regularShellCoordinatePatch m Λ s) :=
  (isOpen_inducedShellPatch m Λ).measurableSet.inter
    (hs.preimage (continuous_shellPatchCoordinates Λ).measurable)

theorem isOpen_regularShellCoordinatePatch (m : ℝ)
    (Λ : Spacetime ≃L[ℝ] Spacetime) {s : Set ShellEuclideanDomain}
    (hs : IsOpen s) : IsOpen (regularShellCoordinatePatch m Λ s) :=
  (isOpen_inducedShellPatch m Λ).inter
    (hs.preimage (continuous_shellPatchCoordinates Λ))

theorem inducedRegularShellVolume_restrict_coordinatePatch {m : ℝ}
    (Λ : Spacetime ≃L[ℝ] Spacetime) (hΛ : IsLorentzMap Λ)
    {s : Set ShellEuclideanDomain} (hs : MeasurableSet s)
    (hsub : s ⊆ euclideanShellChartDomain m) :
    (inducedRegularShellVolume m).restrict (regularShellCoordinatePatch m Λ s) =
      Measure.map (shellPatchPoint m Λ hΛ) ((inducedShellCoordinateVolume m Λ).restrict s) := by
  ext t ht
  rw [Measure.restrict_apply ht,
    inducedRegularShellVolume_apply_in_chart Λ hΛ
      (ht.inter (measurableSet_regularShellCoordinatePatch m Λ hs))
      (fun _ hz => hz.2.1),
    Measure.map_apply_of_aemeasurable (aemeasurable_shellPatchPoint m Λ hΛ).restrict ht,
    Measure.restrict_apply' hs]
  congr 1
  ext w
  simp only [mem_inter_iff, mem_preimage, regularShellCoordinatePatch,
    shellPatchCoordinates_point]
  constructor
  · rintro ⟨⟨htw, _, hsw⟩, _⟩
    exact ⟨htw, hsw⟩
  · rintro ⟨htw, hsw⟩
    exact ⟨⟨htw, shellPatchPoint_mem Λ hΛ (hsub hsw), hsw⟩, hsub hsw⟩

theorem inducedRegularShellVolume_coordinatePatch_lintegral {m : ℝ}
    (Λ : Spacetime ≃L[ℝ] Spacetime) (hΛ : IsLorentzMap Λ)
    {s : Set ShellEuclideanDomain} (hs : MeasurableSet s)
    (hsub : s ⊆ euclideanShellChartDomain m)
    {F : ComplexSpacetime → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ z in regularShellCoordinatePatch m Λ s, F z.1 ∂inducedRegularShellVolume m) =
      ∫⁻ w in s, ENNReal.ofReal (inducedShellChartDensity m Λ w) *
        F (lorentzComplexShellChart m Λ (shellEuclideanCoordinates w)) := by
  rw [inducedRegularShellVolume_restrict_coordinatePatch Λ hΛ hs hsub,
    lintegral_map' (f := fun z : complexShell m => F z.1)
      (hF.comp measurable_subtype_coe).aemeasurable
      (aemeasurable_shellPatchPoint m Λ hΛ).restrict]
  exact inducedShellCoordinateVolume_lintegral Λ hs hsub _

theorem inducedRegularShellVolume_coordinatePatch_le_flat {m C : ℝ}
    (Λ : Spacetime ≃L[ℝ] Spacetime) (hΛ : IsLorentzMap Λ)
    {s : Set ShellEuclideanDomain} (hs : MeasurableSet s)
    (hsub : s ⊆ euclideanShellChartDomain m)
    (hJ : ∀ w ∈ s, inducedShellChartDensity m Λ w ≤ C)
    {t : Set (Fin 3 → ℂ)} (ht : MeasurableSet t)
    (hst : s ⊆ shellEuclideanCoordinates ⁻¹' t)
    {F : ComplexSpacetime → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ z in regularShellCoordinatePatch m Λ s, F z.1 ∂inducedRegularShellVolume m) ≤
      ENNReal.ofReal C * ∫⁻ w in t, regularChartWeight m Λ F w := by
  rw [inducedRegularShellVolume_coordinatePatch_lintegral Λ hΛ hs hsub hF]
  calc
    _ ≤ ∫⁻ w in s, ENNReal.ofReal C *
        regularChartWeight m Λ F (shellEuclideanCoordinates w) := by
      apply setLIntegral_mono' hs
      intro w hw
      rw [regularChartWeight_eq Λ F (hsub hw)]
      exact _root_.mul_le_mul_left (ENNReal.ofReal_le_ofReal (hJ w hw)) _
    _ = ENNReal.ofReal C * ∫⁻ w in s,
        regularChartWeight m Λ F (shellEuclideanCoordinates w) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C * ∫⁻ w in shellEuclideanCoordinates ⁻¹' t,
        regularChartWeight m Λ F (shellEuclideanCoordinates w) :=
      _root_.mul_le_mul_right (lintegral_mono_set hst) _
    _ = _ := by
      rw [shellEuclideanCoordinates_measurePreserving.setLIntegral_comp_preimage ht
        (measurable_regularChartWeight_of_measurable m Λ hF)]

end VacuumBellSeparation
