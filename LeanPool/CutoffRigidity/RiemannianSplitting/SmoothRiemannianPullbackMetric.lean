/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianMetricChartCriterion

/-! # Smoothness of the actual immersion-induced Riemannian metric -/

@[expose] public section
open Bundle Set
open scoped Manifold ContDiff Topology

namespace CutoffRigidity
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {K : Type*} [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J 2 N] [BoundarylessManifold J N]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- An actual `C²` immersion into an actual `C¹` Riemannian metric induces an
actual `C¹` Riemannian metric. All smoothness follows from the true tangent map. -/
theorem isContMDiffRiemannianBundle_immersionPullback (f : N → M)
    (hf : ContMDiff J I 2 f) (hinj : ∀ x, Function.Injective (mfderiv J I f x)) :
    letI := immersionPullbackRiemannianBundle f hinj
    IsContMDiffRiemannianBundle J 1 F (fun x : N ↦ TangentSpace J x) := by
  let := immersionPullbackRiemannianBundle f hinj
  apply isContMDiffRiemannianBundle_of_chartFrame_inner
  intro x u v
  have ht := hf.contMDiff_tangentMap (m := 1) (by norm_num)
  have hu := ht.contMDiffAt.comp x (contMDiffAt_chartFrame (I := J) x u)
  have hv := ht.contMDiffAt.comp x (contMDiffAt_chartFrame (I := J) x v)
  change ContMDiffAt J I.tangent 1
    (fun y ↦ TotalSpace.mk' E (f y) ((mfderiv J I f y) (chartFrame (I := J) x u y))) x at hu
  change ContMDiffAt J I.tangent 1
    (fun y ↦ TotalSpace.mk' E (f y) ((mfderiv J I f y) (chartFrame (I := J) x v y))) x at hv
  let fiberNorm (y : M) : NormedAddCommGroup (TangentSpace I y) :=
    instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal y
  have hinner := @ContMDiffAt.inner_bundle E _ _ H _ I 1 M _ _ E _ _
    (TangentSpace I) _ fiberNorm _ _ _ F _ _ K _ J N _ _ _ f _ _ x hu hv
  convert! hinner using 1

end CutoffRigidity
