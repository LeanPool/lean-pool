/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.SmoothRiemannianPullbackMetric

/-! # Smoothness of the induced metric on an immersed submanifold -/

@[expose] public section

open Bundle
open scoped Manifold ContDiff

namespace CutoffRigidity.Riemann

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {K : Type*} [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- Pulling back a smooth metric along a smooth immersion gives a smooth metric. -/
theorem isContMDiffRiemannianBundle_immersionPullback_top (f : N → M)
    (hf : ContMDiff J I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv J I f x)) :
    letI := immersionPullbackRiemannianBundle f hinj
    IsContMDiffRiemannianBundle J ∞ F (fun x : N ↦ TangentSpace J x) :=
  isContMDiffRiemannianBundle_immersionPullback_of_smoothness f (by simpa using hf) hinj

end CutoffRigidity.Riemann
