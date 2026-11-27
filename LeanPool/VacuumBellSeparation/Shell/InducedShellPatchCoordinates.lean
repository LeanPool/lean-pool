/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.InducedShellVolumeCompatibility
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Actual shell-valued coordinate maps and their open patches

These maps take values in the original complex shell. Their domains
carry the genuine six-dimensional Euclidean metric used by the Gram
density. Only continuity on the regular chart domain is needed; no
global continuity of the principal complex square root is asserted.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Set

/-- Shell patch point. -/
noncomputable def shellPatchPoint (m : ℝ) (Λ : Spacetime ≃L[ℝ] Spacetime)
    (hΛ : IsLorentzMap Λ) (w : ShellEuclideanDomain) : complexShell m :=
  ⟨lorentzComplexShellChart m Λ (shellEuclideanCoordinates w),
    complexifiedSpacetimeMap_mem_shell Λ hΛ (complexShellChart_mem_shell m _)⟩

/-- Shell patch coordinates defined as `shellEuclideanCoordinates.symm
(lorentzComplexShellCoordinates Λ z.1)`. -/
noncomputable def shellPatchCoordinates {m : ℝ}
    (Λ : Spacetime ≃L[ℝ] Spacetime) (z : complexShell m) : ShellEuclideanDomain :=
  shellEuclideanCoordinates.symm (lorentzComplexShellCoordinates Λ z.1)

/-- Set of points satisfying the induced shell patch condition with membership specified by `{z | 0
< ((complexifiedSpacetimeMap Λ.symm z.1).2 1).re ∧ shellPatchCoordinates Λ z ∈
euclideanShellChartDomain m}`. -/
def inducedShellPatch (m : ℝ) (Λ : Spacetime ≃L[ℝ] Spacetime) : Set (complexShell m) :=
  {z | 0 < ((complexifiedSpacetimeMap Λ.symm z.1).2 1).re ∧
    shellPatchCoordinates Λ z ∈ euclideanShellChartDomain m}

theorem continuous_shellPatchCoordinates {m : ℝ} (Λ : Spacetime ≃L[ℝ] Spacetime) :
    Continuous (shellPatchCoordinates (m := m) Λ) := by
  exact shellEuclideanCoordinates.symm.continuous.comp
    ((lorentzComplexShellCoordinates Λ).continuous.comp continuous_subtype_val)

theorem isOpen_inducedShellPatch (m : ℝ) (Λ : Spacetime ≃L[ℝ] Spacetime) :
    IsOpen (inducedShellPatch m Λ) := by
  change IsOpen ({z : complexShell m | 0 < ((complexifiedSpacetimeMap Λ.symm z.1).2 1).re} ∩
    shellPatchCoordinates Λ ⁻¹' euclideanShellChartDomain m)
  exact (isOpen_lt continuous_const (by fun_prop)).inter
    ((isOpen_euclideanShellChartDomain m).preimage (continuous_shellPatchCoordinates Λ))

theorem shellPatchCoordinates_point (m : ℝ) (Λ : Spacetime ≃L[ℝ] Spacetime)
    (hΛ : IsLorentzMap Λ) (w : ShellEuclideanDomain) :
    shellPatchCoordinates Λ (shellPatchPoint m Λ hΛ w) = w := by
  simp only [shellPatchCoordinates, shellPatchPoint, lorentzComplexShellCoordinates_chart,
    ContinuousLinearEquiv.symm_apply_apply]

theorem shellPatchPoint_coordinates {m : ℝ} (Λ : Spacetime ≃L[ℝ] Spacetime)
    (hΛ : IsLorentzMap Λ) {z : complexShell m} (hz : z ∈ inducedShellPatch m Λ) :
    shellPatchPoint m Λ hΛ (shellPatchCoordinates Λ z) = z := by
  apply Subtype.ext
  simpa only [shellPatchPoint, shellPatchCoordinates, ContinuousLinearEquiv.apply_symm_apply]
    using lorentzComplexShellChart_reconstruct Λ hΛ z.2 hz.1

theorem shellPatchPoint_mem {m : ℝ} (Λ : Spacetime ≃L[ℝ] Spacetime)
    (hΛ : IsLorentzMap Λ) {w : ShellEuclideanDomain}
    (hw : w ∈ euclideanShellChartDomain m) :
    shellPatchPoint m Λ hΛ w ∈ inducedShellPatch m Λ := by
  constructor
  · change 0 < ((complexifiedSpacetimeMap Λ.symm
      (complexifiedSpacetimeMap Λ (complexShellChart m (shellEuclideanCoordinates w)))).2 1).re
    rw [complexifiedSpacetimeMap_inverse]
    exact complexShellChart_second_re_pos hw
  · simpa only [shellPatchCoordinates_point] using hw

theorem shellPatchPoint_image_domain (m : ℝ) (Λ : Spacetime ≃L[ℝ] Spacetime)
    (hΛ : IsLorentzMap Λ) :
    shellPatchPoint m Λ hΛ '' euclideanShellChartDomain m = inducedShellPatch m Λ := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact shellPatchPoint_mem Λ hΛ hw
  · intro hz
    exact ⟨shellPatchCoordinates Λ z, hz.2, shellPatchPoint_coordinates Λ hΛ hz⟩

theorem continuousOn_shellPatchPoint (m : ℝ) (Λ : Spacetime ≃L[ℝ] Spacetime)
    (hΛ : IsLorentzMap Λ) :
    ContinuousOn (shellPatchPoint m Λ hΛ) (euclideanShellChartDomain m) := by
  apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
  intro w hw
  exact ((differentiableAt_lorentzComplexShellChart Λ hw).comp w
    shellEuclideanCoordinates.differentiableAt).continuousAt.continuousWithinAt

theorem measurableSet_shellPatch_preimage {m : ℝ} (Λ : Spacetime ≃L[ℝ] Spacetime)
    (hΛ : IsLorentzMap Λ) {s : Set (complexShell m)} (hs : MeasurableSet s) :
    MeasurableSet ((shellPatchPoint m Λ hΛ ⁻¹' s) ∩ euclideanShellChartDomain m) := by
  have hD := (isOpen_euclideanShellChartDomain m).measurableSet
  have hf := (continuousOn_iff_continuous_domRestrict.mp
    (continuousOn_shellPatchPoint m Λ hΛ)).measurable
  have hm := (MeasurableEmbedding.subtype_coe hD).measurableSet_image' (hf hs)
  convert hm using 1
  ext w
  simp only [mem_inter_iff, mem_preimage, mem_image, Subtype.exists]
  constructor
  · rintro ⟨hw, hD⟩
    exact ⟨w, hD, hw, rfl⟩
  · rintro ⟨x, hx, hsx, rfl⟩
    exact ⟨hsx, hx⟩

theorem shellPatchCoordinates_point_transition (m : ℝ)
    (Λ Γ : Spacetime ≃L[ℝ] Spacetime) (hΛ : IsLorentzMap Λ)
    (w : ShellEuclideanDomain) :
    shellPatchCoordinates Γ (shellPatchPoint m Λ hΛ w) =
      euclideanShellChartTransition m Λ Γ w := by
  simp only [shellPatchCoordinates, shellPatchPoint, euclideanShellChartTransition,
    euclideanLorentzShellCoordinates, euclideanLorentzShellChart,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply]

theorem shellPatch_preimage_patch (m : ℝ) (Λ Γ : Spacetime ≃L[ℝ] Spacetime)
    (hΛ : IsLorentzMap Λ) :
    (shellPatchPoint m Λ hΛ ⁻¹' inducedShellPatch m Γ) ∩ euclideanShellChartDomain m =
      euclideanShellChartOverlap m Λ Γ := by
  ext w
  simp only [mem_inter_iff, mem_preimage, inducedShellPatch, mem_ofPred_eq,
    euclideanShellChartOverlap,
    euclideanShellOverlapSign, shellPatchPoint]
  tauto

end VacuumBellSeparation
