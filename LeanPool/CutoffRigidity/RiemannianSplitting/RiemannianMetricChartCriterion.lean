/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianPullbackMetric
public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianChartFrames
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-! # Smooth metric coefficients from actual chart-frame Gram functions -/

@[expose] public section
open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace CutoffRigidity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [BoundarylessManifold I M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- Actual smooth Gram functions of actual chart-constant frames imply smooth
bundle dependence of the original fiber metric. -/
theorem isContMDiffRiemannianBundle_of_chartFrame_inner
    (hGram : ∀ (x : M) (u v : E), ContMDiffAt I 𝓘(ℝ, ℝ) 1
      (fun y ↦ inner ℝ (chartFrame (I := I) x u y) (chartFrame (I := I) x v y)) x) :
    IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) := by
  refine ⟨fun x ↦ innerSL ℝ, ?_, fun _ _ _ ↦ rfl⟩
  intro x
  rw [contMDiffAt_section_iff]
  let g := fun y : M ↦
    (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
      (fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x
      ⟨y, innerSL ℝ⟩).2
  change ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) 1 g x
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
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I 1 (extChartAt I x).symm (extChartAt I x x) :=
    (contMDiffOn_extChartAt_symm (I := I) (n := 1) x).contMDiffAt htarget
  have hinner := (hGram x u v).comp_of_eq hsymm (extChartAt_to_inv x)
  convert! hinner.contDiffAt.contDiffWithinAt (s := range I) using 1
  funext z
  exact hcoeff _ u v

end CutoffRigidity
