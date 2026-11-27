/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.InducedShellPatchCoordinates

/-!
# Genuine pushforward measures on the original complex shell

Every chart measure is the pushforward of the actual Euclidean Gram
density. Its support and pairwise restriction compatibility are proved
from the chart reconstruction and the real Jacobian theorem.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Set

theorem aemeasurable_shellPatchPoint (m : ℝ) (Λ : Spacetime ≃L[ℝ] Spacetime)
    (hΛ : IsLorentzMap Λ) :
    AEMeasurable (shellPatchPoint m Λ hΛ) (inducedShellCoordinateVolume m Λ) := by
  exact (continuousOn_shellPatchPoint m Λ hΛ).aemeasurable
    (isOpen_euclideanShellChartDomain m).measurableSet

/-- Induced shell patch volume defined as `Measure.map (shellPatchPoint m Λ hΛ)
(inducedShellCoordinateVolume m Λ)`. -/
noncomputable def inducedShellPatchVolume (m : ℝ) (Λ : Spacetime ≃L[ℝ] Spacetime)
    (hΛ : IsLorentzMap Λ) : Measure (complexShell m) :=
  Measure.map (shellPatchPoint m Λ hΛ) (inducedShellCoordinateVolume m Λ)

theorem inducedShellPatchVolume_apply {m : ℝ} (Λ : Spacetime ≃L[ℝ] Spacetime)
    (hΛ : IsLorentzMap Λ) {s : Set (complexShell m)} (hs : MeasurableSet s) :
    inducedShellPatchVolume m Λ hΛ s = inducedShellCoordinateVolume m Λ
      ((shellPatchPoint m Λ hΛ ⁻¹' s) ∩ euclideanShellChartDomain m) := by
  rw [inducedShellPatchVolume,
    Measure.map_apply_of_aemeasurable (aemeasurable_shellPatchPoint m Λ hΛ) hs]
  unfold inducedShellCoordinateVolume
  rw [Measure.restrict_apply' (isOpen_euclideanShellChartDomain m).measurableSet,
    Measure.restrict_apply' (isOpen_euclideanShellChartDomain m).measurableSet]
  simp only [inter_assoc, inter_self]

theorem inducedShellPatchVolume_supported (m : ℝ) (Λ : Spacetime ≃L[ℝ] Spacetime)
    (hΛ : IsLorentzMap Λ) :
    (inducedShellPatchVolume m Λ hΛ).restrict (inducedShellPatch m Λ) =
      inducedShellPatchVolume m Λ hΛ := by
  ext s hs
  rw [Measure.restrict_apply hs,
    inducedShellPatchVolume_apply Λ hΛ
      (hs.inter (isOpen_inducedShellPatch m Λ).measurableSet),
    inducedShellPatchVolume_apply Λ hΛ hs]
  congr 1
  ext w
  constructor
  · exact fun hw => ⟨hw.1.1, hw.2⟩
  · exact fun hw => ⟨⟨hw.1, shellPatchPoint_mem Λ hΛ hw.2⟩, hw.2⟩

theorem shellPatchPoint_transition {m : ℝ}
    (Λ Γ : Spacetime ≃L[ℝ] Spacetime) (hΛ : IsLorentzMap Λ) (hΓ : IsLorentzMap Γ)
    {w : ShellEuclideanDomain} (hw : w ∈ euclideanShellChartOverlap m Λ Γ) :
    shellPatchPoint m Γ hΓ (euclideanShellChartTransition m Λ Γ w) =
      shellPatchPoint m Λ hΛ w := by
  apply Subtype.ext
  apply complexSpacetimeEuclideanEquiv.injective
  exact euclideanShellChartTransition_reconstruct Λ Γ hΛ hΓ hw

theorem shellPatchTransition_image_preimage {m : ℝ}
    (Λ Γ : Spacetime ≃L[ℝ] Spacetime) (hΛ : IsLorentzMap Λ) (hΓ : IsLorentzMap Γ)
    (s : Set (complexShell m)) :
    euclideanShellChartTransition m Λ Γ ''
      ((shellPatchPoint m Λ hΛ ⁻¹' (s ∩ inducedShellPatch m Γ)) ∩
        euclideanShellChartDomain m) =
      ((shellPatchPoint m Γ hΓ ⁻¹' (s ∩ inducedShellPatch m Λ)) ∩
        euclideanShellChartDomain m) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have ho : x ∈ euclideanShellChartOverlap m Λ Γ := by
      rw [← shellPatch_preimage_patch m Λ Γ hΛ]
      exact ⟨hx.1.2, hx.2⟩
    change (shellPatchPoint m Γ hΓ (euclideanShellChartTransition m Λ Γ x) ∈
      s ∩ inducedShellPatch m Λ) ∧ _
    rw [shellPatchPoint_transition Λ Γ hΛ hΓ ho]
    exact ⟨⟨hx.1.1, shellPatchPoint_mem Λ hΛ hx.2⟩, ho.2.1⟩
  · intro hy
    let x := shellPatchCoordinates Λ (shellPatchPoint m Γ hΓ y)
    have hxD : x ∈ euclideanShellChartDomain m := hy.1.2.2
    have hx : shellPatchPoint m Λ hΛ x = shellPatchPoint m Γ hΓ y :=
      shellPatchPoint_coordinates Λ hΛ hy.1.2
    refine ⟨x, ⟨?_, hxD⟩, ?_⟩
    · change shellPatchPoint m Λ hΛ x ∈ s ∩ inducedShellPatch m Γ
      rw [hx]
      exact ⟨hy.1.1, shellPatchPoint_mem Γ hΓ hy.2⟩
    · rw [← shellPatchCoordinates_point_transition m Λ Γ hΛ, hx,
        shellPatchCoordinates_point]

/-- The two actual shell measures have the same restriction to their
common patch. The compatibility is derived, not assumed as atlas data. -/
theorem inducedShellPatchVolume_compatible (m : ℝ)
    (Λ Γ : Spacetime ≃L[ℝ] Spacetime) (hΛ : IsLorentzMap Λ) (hΓ : IsLorentzMap Γ) :
    (inducedShellPatchVolume m Λ hΛ).restrict (inducedShellPatch m Γ) =
      (inducedShellPatchVolume m Γ hΓ).restrict (inducedShellPatch m Λ) := by
  ext s hs
  rw [Measure.restrict_apply hs, Measure.restrict_apply hs,
    inducedShellPatchVolume_apply Λ hΛ
      (hs.inter (isOpen_inducedShellPatch m Γ).measurableSet),
    inducedShellPatchVolume_apply Γ hΓ
      (hs.inter (isOpen_inducedShellPatch m Λ).measurableSet)]
  have hp := measurableSet_shellPatch_preimage Λ hΛ
    (hs.inter (isOpen_inducedShellPatch m Γ).measurableSet)
  have hsub : ((shellPatchPoint m Λ hΛ ⁻¹' (s ∩ inducedShellPatch m Γ)) ∩
      euclideanShellChartDomain m) ⊆ euclideanShellChartOverlap m Λ Γ := by
    intro w hw
    rw [← shellPatch_preimage_patch m Λ Γ hΛ]
    exact ⟨hw.1.2, hw.2⟩
  have h := inducedShellCoordinateVolume_overlap Λ Γ hΛ hΓ hp hsub
  rw [shellPatchTransition_image_preimage Λ Γ hΛ hΓ s] at h
  exact h.symm

end VacuumBellSeparation
