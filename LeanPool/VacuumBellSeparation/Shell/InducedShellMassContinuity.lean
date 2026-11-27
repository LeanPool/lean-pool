/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.InducedShellVolumeBounds

/-!
# Uniform chart-density control through mass zero

The mass and all six real chart coordinates vary jointly. The partial
coordinate derivative is obtained from the genuine derivative of the
joint C1 map, so compact bounds do not assume an unproved continuity
statement about a mass-indexed derivative family.
-/

@[expose] public section

namespace VacuumBellSeparation

/-- Set of points satisfying the Euclidean shell joint domain condition. -/
noncomputable def euclideanShellJointDomain : Set (ℝ × ShellEuclideanDomain) :=
  {q | q.2 ∈ euclideanShellChartDomain q.1}

private theorem contDiff_shellJointCoordinate (i : Fin 3) :
    ContDiff ℝ 1 (fun q : ℝ × ShellEuclideanDomain => shellEuclideanCoordinates q.2 i) :=
  ((contDiff_apply ℝ (fun _ : Fin 3 => ℂ) i).comp
    (shellEuclideanCoordinates.toContinuousLinearMap.restrictScalars ℝ).contDiff).comp
      contDiff_snd

theorem contDiff_shellJointRadicand :
    ContDiff ℝ 1 (fun q : ℝ × ShellEuclideanDomain =>
      complexShellRadicand q.1 (shellEuclideanCoordinates q.2)) := by
  have hm : ContDiff ℝ 1 (fun q : ℝ × ShellEuclideanDomain => (q.1 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp contDiff_fst
  simpa only [complexShellRadicand] using
    ((((contDiff_shellJointCoordinate 0).pow 2).sub
      ((contDiff_shellJointCoordinate 1).pow 2)).sub
        ((contDiff_shellJointCoordinate 2).pow 2)).sub (hm.pow 2)

theorem isOpen_euclideanShellJointDomain : IsOpen euclideanShellJointDomain :=
  isOpen_lt continuous_const
    (Complex.continuous_re.comp contDiff_shellJointRadicand.continuous)

theorem contDiffOn_euclideanLorentzShellChart_joint (Λ : Spacetime ≃L[ℝ] Spacetime) :
    ContDiffOn ℝ 1 (fun q : ℝ × ShellEuclideanDomain =>
      euclideanLorentzShellChart q.1 Λ q.2) euclideanShellJointDomain := by
  have hs : ContDiffOn ℝ 1 Complex.sqrt Complex.slitPlane :=
    (Complex.differentiableOn_sqrt.contDiffOn Complex.isOpen_slitPlane).restrict_scalars ℝ
  have hroot : ContDiffOn ℝ 1 (fun q : ℝ × ShellEuclideanDomain =>
      Complex.sqrt (complexShellRadicand q.1 (shellEuclideanCoordinates q.2)))
        euclideanShellJointDomain :=
    hs.comp contDiff_shellJointRadicand.contDiffOn
      (fun _ hw => Complex.mem_slitPlane_iff.mpr (Or.inl hw))
  have hc : ContDiffOn ℝ 1 (fun q : ℝ × ShellEuclideanDomain =>
      complexShellChart q.1 (shellEuclideanCoordinates q.2)) euclideanShellJointDomain := by
    apply ContDiffOn.prodMk
    · exact (contDiff_shellJointCoordinate 0).contDiffOn
    · apply contDiffOn_pi.mpr
      intro i
      fin_cases i <;>
        simp only [Matrix.cons_val_zero',
          Matrix.cons_val_succ']
      · exact (contDiff_shellJointCoordinate 1).contDiffOn
      · exact hroot
      · exact (contDiff_shellJointCoordinate 2).contDiffOn
  change ContDiffOn ℝ 1 (fun q : ℝ × ShellEuclideanDomain =>
    complexSpacetimeEuclideanEquiv (complexifiedSpacetimeMap Λ
      (complexShellChart q.1 (shellEuclideanCoordinates q.2)))) euclideanShellJointDomain
  exact (complexSpacetimeEuclideanEquiv.toContinuousLinearMap.restrictScalars
    ℝ).contDiff.comp_contDiffOn
    (((complexifiedSpacetimeMap Λ).restrictScalars ℝ).contDiff.comp_contDiffOn hc)

theorem euclideanLorentzShellChart_partial_derivative (Λ : Spacetime ≃L[ℝ] Spacetime)
    {q : ℝ × ShellEuclideanDomain} (hq : q ∈ euclideanShellJointDomain) :
    fderiv ℝ (euclideanLorentzShellChart q.1 Λ) q.2 =
      (fderiv ℝ (fun p : ℝ × ShellEuclideanDomain =>
        euclideanLorentzShellChart p.1 Λ p.2) q).comp
          (ContinuousLinearMap.inr ℝ ℝ ShellEuclideanDomain) := by
  have hF := ((contDiffOn_euclideanLorentzShellChart_joint Λ).contDiffAt
    (isOpen_euclideanShellJointDomain.mem_nhds hq)).differentiableAt (by norm_num)
  have hi := hasFDerivAt_prodMk_right (𝕜 := ℝ) q.1 q.2
  exact (hF.hasFDerivAt.comp q.2 hi).fderiv

theorem continuousOn_euclideanLorentzShellChart_partial_derivative
    (Λ : Spacetime ≃L[ℝ] Spacetime) :
    ContinuousOn (fun q : ℝ × ShellEuclideanDomain =>
      fderiv ℝ (euclideanLorentzShellChart q.1 Λ) q.2) euclideanShellJointDomain := by
  have hc := (contDiffOn_euclideanLorentzShellChart_joint Λ).continuousOn_fderiv_of_isOpen
    isOpen_euclideanShellJointDomain le_rfl
  have hcomp : ContinuousOn (fun q : ℝ × ShellEuclideanDomain =>
      (fderiv ℝ (fun p : ℝ × ShellEuclideanDomain =>
        euclideanLorentzShellChart p.1 Λ p.2) q).comp
          (ContinuousLinearMap.inr ℝ ℝ ShellEuclideanDomain)) euclideanShellJointDomain :=
    hc.clm_comp continuous_const.continuousOn
  exact hcomp.congr (fun q hq => euclideanLorentzShellChart_partial_derivative Λ hq)

theorem continuousOn_inducedShellChartDensity_joint (Λ : Spacetime ≃L[ℝ] Spacetime) :
    ContinuousOn (fun q : ℝ × ShellEuclideanDomain => inducedShellChartDensity q.1 Λ q.2)
      euclideanShellJointDomain :=
  continuous_shellDerivativeDensity.comp_continuousOn
    (continuousOn_euclideanLorentzShellChart_partial_derivative Λ)

/-- Uniform positive finite density bounds on compact mass-coordinate
families, with no restriction excluding zero mass. -/
theorem inducedShellChartDensity_joint_compact_bounds (Λ : Spacetime ≃L[ℝ] Spacetime)
    {K : Set (ℝ × ShellEuclideanDomain)} (hK : IsCompact K)
    (hsub : K ⊆ euclideanShellJointDomain) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ q ∈ K, c ≤ inducedShellChartDensity q.1 Λ q.2 ∧
        inducedShellChartDensity q.1 Λ q.2 ≤ C := by
  have hc := (continuousOn_inducedShellChartDensity_joint Λ).mono hsub
  obtain ⟨c, hcpos, hclower⟩ := hK.exists_forall_le' hc
    (fun q hq => inducedShellChartDensity_pos Λ (hsub hq))
  obtain ⟨C, hC⟩ := hK.bddAbove_image hc
  refine ⟨c, max 1 C, hcpos, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro q hq
  exact ⟨hclower q hq, (hC (Set.mem_image_of_mem _ hq)).trans (le_max_right _ _)⟩

end VacuumBellSeparation
