/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.InducedShellGramDensity
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Order.Compact

/-!
# Positive continuous chart density and actual compact patch bounds

Complex C1 regularity of the principal-root chart is restricted to real
scalars before taking its six-dimensional derivative. The resulting
Gram density has positive lower and finite upper bounds on every
compact subset of the actual chart domain.
-/

@[expose] public section

namespace VacuumBellSeparation

open scoped Topology

theorem contDiffOn_complexShellChart (m : ℝ) :
    ContDiffOn ℂ 1 (complexShellChart m) (complexShellChartDomain m) := by
  have hr : ContDiff ℂ 1 (complexShellRadicand m) := by
    unfold complexShellRadicand
    fun_prop
  have hs : ContDiffOn ℂ 1 Complex.sqrt Complex.slitPlane :=
    Complex.differentiableOn_sqrt.contDiffOn Complex.isOpen_slitPlane
  have hcomp : ContDiffOn ℂ 1 (fun w => Complex.sqrt (complexShellRadicand m w))
      (complexShellChartDomain m) :=
    hs.comp hr.contDiffOn (fun _ hw => Complex.mem_slitPlane_iff.mpr (Or.inl hw))
  apply ContDiffOn.prodMk
  · exact (ContinuousLinearMap.proj (0 : Fin 3) : (Fin 3 → ℂ) →L[ℂ] ℂ).contDiff.contDiffOn
  · apply contDiffOn_pi.mpr
    intro i
    fin_cases i
    · exact (ContinuousLinearMap.proj (1 : Fin 3) : (Fin 3 → ℂ) →L[ℂ] ℂ).contDiff.contDiffOn
    · exact hcomp
    · exact (ContinuousLinearMap.proj (2 : Fin 3) : (Fin 3 → ℂ) →L[ℂ] ℂ).contDiff.contDiffOn

theorem contDiffOn_lorentzComplexShellChart (m : ℝ) (Λ : Spacetime ≃L[ℝ] Spacetime) :
    ContDiffOn ℂ 1 (lorentzComplexShellChart m Λ) (complexShellChartDomain m) :=
  (complexifiedSpacetimeMap Λ).contDiff.comp_contDiffOn (contDiffOn_complexShellChart m)

theorem contDiffOn_euclideanLorentzShellChart_complex
    (m : ℝ) (Λ : Spacetime ≃L[ℝ] Spacetime) :
    ContDiffOn ℂ 1 (euclideanLorentzShellChart m Λ) (euclideanShellChartDomain m) :=
  complexSpacetimeEuclideanEquiv.contDiff.comp_contDiffOn
    ((contDiffOn_lorentzComplexShellChart m Λ).comp
      shellEuclideanCoordinates.contDiff.contDiffOn (fun _ hw => hw))

theorem contDiffOn_euclideanLorentzShellChart_real
    (m : ℝ) (Λ : Spacetime ≃L[ℝ] Spacetime) :
    ContDiffOn ℝ 1 (euclideanLorentzShellChart m Λ) (euclideanShellChartDomain m) :=
  (contDiffOn_euclideanLorentzShellChart_complex m Λ).restrict_scalars ℝ

theorem continuousOn_euclideanLorentzShellChart_real_derivative
    (m : ℝ) (Λ : Spacetime ≃L[ℝ] Spacetime) :
    ContinuousOn (fderiv ℝ (euclideanLorentzShellChart m Λ)) (euclideanShellChartDomain m) :=
  (contDiffOn_euclideanLorentzShellChart_real m Λ).continuousOn_fderiv_of_isOpen
    (isOpen_euclideanShellChartDomain m) le_rfl

theorem continuousOn_inducedShellChartDensity (m : ℝ) (Λ : Spacetime ≃L[ℝ] Spacetime) :
    ContinuousOn (inducedShellChartDensity m Λ) (euclideanShellChartDomain m) :=
  continuous_shellDerivativeDensity.comp_continuousOn
    (continuousOn_euclideanLorentzShellChart_real_derivative m Λ)

theorem inducedShellChartDensity_compact_bounds (m : ℝ)
    (Λ : Spacetime ≃L[ℝ] Spacetime) {K : Set ShellEuclideanDomain}
    (hK : IsCompact K) (hsub : K ⊆ euclideanShellChartDomain m) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ w ∈ K, c ≤ inducedShellChartDensity m Λ w ∧ inducedShellChartDensity m Λ w ≤ C := by
  have hc := (continuousOn_inducedShellChartDensity m Λ).mono hsub
  obtain ⟨c, hcpos, hclower⟩ := hK.exists_forall_le' hc
    (fun w hw => inducedShellChartDensity_pos Λ (hsub hw))
  obtain ⟨C, hC⟩ := hK.bddAbove_image hc
  refine ⟨c, max 1 C, hcpos, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro w hw
  exact ⟨hclower w hw, (hC (Set.mem_image_of_mem _ hw)).trans (le_max_right _ _)⟩

/-- Every actual regular shell chart point has a closed Euclidean ball
with positive lower and finite upper density bounds. -/
theorem inducedShellChartDensity_local_bounds {m : ℝ}
    (Λ : Spacetime ≃L[ℝ] Spacetime) {w : ShellEuclideanDomain}
    (hw : w ∈ euclideanShellChartDomain m) :
    ∃ ε c C : ℝ, 0 < ε ∧ 0 < c ∧ 0 < C ∧
      Metric.closedBall w ε ⊆ euclideanShellChartDomain m ∧
      ∀ x ∈ Metric.closedBall w ε,
        c ≤ inducedShellChartDensity m Λ x ∧ inducedShellChartDensity m Λ x ≤ C := by
  obtain ⟨ε, hε, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    ((isOpen_euclideanShellChartDomain m).mem_nhds hw)
  obtain ⟨c, C, hc, hC, hb⟩ := inducedShellChartDensity_compact_bounds m Λ
    (isCompact_closedBall w ε) hsub
  exact ⟨ε, c, C, hε, hc, hC, hsub, hb⟩

end VacuumBellSeparation
