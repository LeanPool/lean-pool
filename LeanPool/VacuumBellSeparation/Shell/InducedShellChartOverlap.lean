/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.InducedShellVolumeBounds

/-!
# Actual overlap transitions of the Euclidean shell charts

The overlap retains the principal-root branch and both chart domains.
On this open set, the transition reconstructs the same original shell
point and is injective. The real derivative density transforms by the
absolute determinant of the genuine six-dimensional transition map.
-/

@[expose] public section

namespace VacuumBellSeparation

open scoped Topology

theorem lorentzComplexShellChart_reconstruct {m : ℝ}
    (Γ : Spacetime ≃L[ℝ] Spacetime) (hΓ : IsLorentzMap Γ) {z : ComplexSpacetime}
    (hz : z ∈ complexShell m)
    (hpos : 0 < ((complexifiedSpacetimeMap Γ.symm z).2 1).re) :
    lorentzComplexShellChart m Γ (lorentzComplexShellCoordinates Γ z) = z := by
  have hs := complexifiedSpacetimeMap_mem_shell Γ.symm hΓ.symm hz
  unfold lorentzComplexShellChart lorentzComplexShellCoordinates
  rw [ContinuousLinearMap.comp_apply, complexShellChart_coordinates hs hpos]
  simpa only [ContinuousLinearEquiv.symm_symm] using complexifiedSpacetimeMap_inverse Γ.symm z

/-- Change between the Euclidean coordinate representations of overlapping shell charts. -/
noncomputable def euclideanShellChartTransition (m : ℝ)
    (Λ Γ : Spacetime ≃L[ℝ] Spacetime) (w : ShellEuclideanDomain) : ShellEuclideanDomain :=
  euclideanLorentzShellCoordinates Γ (euclideanLorentzShellChart m Λ w)

/-- Euclidean shell overlap sign. -/
noncomputable def euclideanShellOverlapSign (m : ℝ)
    (Λ Γ : Spacetime ≃L[ℝ] Spacetime) (w : ShellEuclideanDomain) : ℝ :=
  ((complexifiedSpacetimeMap Γ.symm
    (lorentzComplexShellChart m Λ (shellEuclideanCoordinates w))).2 1).re

/-- Set of points satisfying the Euclidean shell chart overlap condition. -/
def euclideanShellChartOverlap (m : ℝ) (Λ Γ : Spacetime ≃L[ℝ] Spacetime) :
    Set ShellEuclideanDomain :=
  {w | w ∈ euclideanShellChartDomain m ∧
    euclideanShellChartTransition m Λ Γ w ∈ euclideanShellChartDomain m ∧
    0 < euclideanShellOverlapSign m Λ Γ w}

theorem differentiableAt_euclideanShellChartTransition {m : ℝ}
    (Λ Γ : Spacetime ≃L[ℝ] Spacetime) {w : ShellEuclideanDomain}
    (hw : w ∈ euclideanShellChartDomain m) :
    DifferentiableAt ℝ (euclideanShellChartTransition m Λ Γ) w :=
  ((euclideanLorentzShellCoordinates Γ).restrictScalars ℝ).differentiableAt.comp w
    ((differentiableAt_euclideanLorentzShellChart Λ hw).restrictScalars ℝ)

theorem continuousAt_euclideanShellOverlapSign {m : ℝ}
    (Λ Γ : Spacetime ≃L[ℝ] Spacetime) {w : ShellEuclideanDomain}
    (hw : w ∈ euclideanShellChartDomain m) :
    ContinuousAt (euclideanShellOverlapSign m Λ Γ) w := by
  have hc := (differentiableAt_lorentzComplexShellChart Λ hw).continuousAt.comp
    shellEuclideanCoordinates.continuousAt
  have hd := (complexifiedSpacetimeMap Γ.symm).continuous.continuousAt.comp hc
  exact Complex.continuous_re.continuousAt.comp
    ((continuous_apply (1 : Fin 3)).continuousAt.comp hd.snd)

theorem isOpen_euclideanShellChartOverlap (m : ℝ) (Λ Γ : Spacetime ≃L[ℝ] Spacetime) :
    IsOpen (euclideanShellChartOverlap m Λ Γ) := by
  apply isOpen_iff_mem_nhds.mpr
  intro w hw
  have h₁ := (isOpen_euclideanShellChartDomain m).mem_nhds hw.1
  have h₂ := (differentiableAt_euclideanShellChartTransition Λ Γ hw.1).continuousAt
    ((isOpen_euclideanShellChartDomain m).mem_nhds hw.2.1)
  have h₃ := (continuousAt_euclideanShellOverlapSign Λ Γ hw.1)
    (Ioi_mem_nhds hw.2.2)
  exact Filter.inter_mem h₁ (Filter.inter_mem h₂ h₃)

theorem euclideanShellChartTransition_reconstruct {m : ℝ}
    (Λ Γ : Spacetime ≃L[ℝ] Spacetime) (hΛ : IsLorentzMap Λ) (hΓ : IsLorentzMap Γ)
    {w : ShellEuclideanDomain} (hw : w ∈ euclideanShellChartOverlap m Λ Γ) :
    euclideanLorentzShellChart m Γ (euclideanShellChartTransition m Λ Γ w) =
      euclideanLorentzShellChart m Λ w := by
  have hs := complexifiedSpacetimeMap_mem_shell Λ hΛ
    (complexShellChart_mem_shell m (shellEuclideanCoordinates w))
  have h := lorentzComplexShellChart_reconstruct Γ hΓ hs hw.2.2
  simpa only [euclideanLorentzShellChart, euclideanShellChartTransition,
    euclideanLorentzShellCoordinates, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply,
    ContinuousLinearEquiv.apply_symm_apply, lorentzComplexShellChart] using
      congrArg complexSpacetimeEuclideanEquiv h

theorem euclideanShellChartTransition_injOn {m : ℝ}
    (Λ Γ : Spacetime ≃L[ℝ] Spacetime) (hΛ : IsLorentzMap Λ) (hΓ : IsLorentzMap Γ) :
    Set.InjOn (euclideanShellChartTransition m Λ Γ) (euclideanShellChartOverlap m Λ Γ) := by
  intro x hx y hy hxy
  have h := congrArg (euclideanLorentzShellChart m Γ) hxy
  rw [euclideanShellChartTransition_reconstruct Λ Γ hΛ hΓ hx,
    euclideanShellChartTransition_reconstruct Λ Γ hΛ hΓ hy] at h
  have hi := congrArg (euclideanLorentzShellCoordinates Λ) h
  simpa only [euclideanLorentzShellCoordinates_chart] using hi

theorem shellDerivativeDensity_comp
    (A : ShellEuclideanDomain →L[ℝ] ShellEuclideanAmbient)
    (B : ShellEuclideanDomain →L[ℝ] ShellEuclideanDomain) :
    shellDerivativeDensity (A.comp B) = shellDerivativeDensity A * |B.det| := by
  simp only [shellDerivativeDensity_eq_normDet]
  exact (B.toLinearMap.normDet_comp_of_finrank_eq A.toLinearMap rfl).trans
    (congrArg (fun x => A.toLinearMap.normDet * x) B.toLinearMap.normDet_eq_abs_det)

theorem inducedShellChartDensity_transition {m : ℝ}
    (Λ Γ : Spacetime ≃L[ℝ] Spacetime) (hΛ : IsLorentzMap Λ) (hΓ : IsLorentzMap Γ)
    {w : ShellEuclideanDomain} (hw : w ∈ euclideanShellChartOverlap m Λ Γ) :
    inducedShellChartDensity m Λ w =
      inducedShellChartDensity m Γ (euclideanShellChartTransition m Λ Γ w) *
        |(fderiv ℝ (euclideanShellChartTransition m Λ Γ) w).det| := by
  have he : (fun x => euclideanLorentzShellChart m Γ (euclideanShellChartTransition m Λ Γ x))
      =ᶠ[𝓝 w] euclideanLorentzShellChart m Λ := by
    filter_upwards [(isOpen_euclideanShellChartOverlap m Λ Γ).mem_nhds hw] with x hx
    exact euclideanShellChartTransition_reconstruct Λ Γ hΛ hΓ hx
  have hd := he.fderiv_eq (𝕜 := ℝ)
  change fderiv ℝ (euclideanLorentzShellChart m Γ ∘
    euclideanShellChartTransition m Λ Γ) w =
      fderiv ℝ (euclideanLorentzShellChart m Λ) w at hd
  rw [fderiv_comp w
    ((differentiableAt_euclideanLorentzShellChart Γ hw.2.1).restrictScalars ℝ)
    (differentiableAt_euclideanShellChartTransition Λ Γ hw.1)] at hd
  unfold inducedShellChartDensity
  rw [← hd, shellDerivativeDensity_comp]

end VacuumBellSeparation
