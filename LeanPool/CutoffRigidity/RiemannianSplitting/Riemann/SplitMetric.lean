/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianPullbackMetric
public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianChartMetric
public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianMetricChartCriterion
public import LeanPool.CutoffRigidity.RiemannianSplitting.SmoothRiemannianPullbackMetric

/-! # `C^∞` regularity of the induced metric on an immersed submanifold -/

@[expose] public section
open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace CutoffRigidity.Riemann
open CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

omit [FiniteDimensional ℝ E]
  [BoundarylessManifold I M]
  [RiemannianBundle fun x : M ↦ TangentSpace I x] in
/-- The coordinate-constant tangent frame is `C^∞` near its chart center. -/
theorem contMDiffAt_chartFrame_top (x₀ : M) (u : E) :
    ContMDiffAt I I.tangent ∞ (T% (chartFrame (I := I) x₀ u)) x₀ := by
  rw [contMDiffAt_section_iff]
  apply (contMDiffAt_const (c := u)).congr_of_eventuallyEq
  filter_upwards [chart_source_mem_nhds H x₀] with y hy
  have hy' : y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by simpa using hy
  change (trivializationAt E (TangentSpace I) x₀ ⟨y, chartFrame (I := I) x₀ u y⟩).2 = _
  rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hy']
  exact (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt_symmL hy' u

/-- Actual smooth Gram functions of actual chart-constant frames imply smooth
bundle dependence of the original fiber metric. -/
theorem isContMDiffRiemannianBundle_of_chartFrame_inner_top
    (hGram : ∀ (x : M) (u v : E), ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun y ↦ inner ℝ (chartFrame (I := I) x u y) (chartFrame (I := I) x v y)) x) :
    IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := by
  refine ⟨fun x ↦ innerSL ℝ, ?_, fun _ _ _ ↦ rfl⟩
  intro x
  rw [contMDiffAt_section_iff]
  let g := fun y : M ↦
    (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
      (fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x
      ⟨y, innerSL ℝ⟩).2
  change ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞ g x
  have hcoeff (y : M) (u v : E) : g y u v =
      inner ℝ (chartFrame (I := I) x u y) (chartFrame (I := I) x v y) := by
    classical
    have ht : y ∈ (Bundle.Trivial.trivialization M ℝ).baseSet :=
      FiberBundle.mem_baseSet_trivializationAt ℝ (Bundle.Trivial M ℝ) y
    by_cases hy : y ∈ (trivializationAt E (TangentSpace I) x).baseSet
    · have hy' : y ∈ (chartAt H x).source := by simpa using hy
      simp [g, hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
        chartFrame, chartFrameCLM, Trivialization.linearMapAt_apply, hy']
      rfl
    · have hy' : y ∉ (chartAt H x).source := by simpa using hy
      simp [g, hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
        chartFrame, chartFrameCLM, Trivialization.linearMapAt_apply, hy']
  rw [contMDiffAt_iff_source, contMDiffWithinAt_iff_contDiffWithinAt]
  apply contDiffWithinAt_clm_apply.mpr
  intro u
  apply contDiffWithinAt_clm_apply.mpr
  intro v
  have htarget : (extChartAt I x).target ∈ 𝓝 (extChartAt I x x) :=
    (isOpen_extChartAt_target_of_boundarylessManifold (I := I) x).mem_nhds
      (mem_extChartAt_target x)
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I x).symm (extChartAt I x x) :=
    (contMDiffOn_extChartAt_symm (I := I) (n := ∞) x).contMDiffAt htarget
  have hinner := (hGram x u v).comp_of_eq hsymm (extChartAt_to_inv x)
  convert! hinner.contDiffAt.contDiffWithinAt (s := range I) using 1
  funext z
  exact hcoeff _ u v


section Pullback
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {K : Type*} [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
  {N : Type*} [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [BoundarylessManifold J N]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

omit [FiniteDimensional ℝ E] [BoundarylessManifold I M] in
/-- An actual `C²` immersion into an actual `C¹` Riemannian metric induces an
actual `C¹` Riemannian metric. All smoothness follows from the true tangent map. -/
theorem isContMDiffRiemannianBundle_immersionPullback_top (f : N → M)
    (hf : ContMDiff J I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv J I f x)) :
    letI := immersionPullbackRiemannianBundle f hinj
    IsContMDiffRiemannianBundle J ∞ F (fun x : N ↦ TangentSpace J x) := by
  let := immersionPullbackRiemannianBundle f hinj
  apply isContMDiffRiemannianBundle_of_chartFrame_inner_top
  intro x u v
  have ht := hf.contMDiff_tangentMap (m := ∞) (by simp)
  have hu := ht.contMDiffAt.comp x (contMDiffAt_chartFrame_top (I := J) x u)
  have hv := ht.contMDiffAt.comp x (contMDiffAt_chartFrame_top (I := J) x v)
  change ContMDiffAt J I.tangent ∞
    (fun y ↦ TotalSpace.mk' E (f y) ((mfderiv J I f y) (chartFrame (I := J) x u y))) x at hu
  change ContMDiffAt J I.tangent ∞
    (fun y ↦ TotalSpace.mk' E (f y) ((mfderiv J I f y) (chartFrame (I := J) x v y))) x at hv
  let fiberNorm (y : M) : NormedAddCommGroup (TangentSpace I y) :=
    instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal y
  have hinner := @ContMDiffAt.inner_bundle E _ _ H _ I ∞ M _ _ E _ _
    (TangentSpace I) _ fiberNorm _ _ _ F _ _ K _ J N _ _ _ f _ _ x hu hv
  convert! hinner using 1


end Pullback

end CutoffRigidity.Riemann
