/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianPullbackMetric
import TauCeti.Geometry.Manifold.Riemannian.Pullback.Basic

/-! # Regularity of an immersion-induced Riemannian metric -/

@[expose] public section

open Bundle
open scoped Manifold ContDiff

namespace CutoffRigidity

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {K : Type*} [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J 2 N]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {n : ℕ∞ω} [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]

/-- The metric induced by a `C^(n+1)` immersion into a `C^n` Riemannian bundle is `C^n`. -/
theorem isContMDiffRiemannianBundle_immersionPullback_of_smoothness (f : N → M)
    (hf : ContMDiff J I (n + 1) f) (hinj : ∀ x, Function.Injective (mfderiv J I f x)) :
    letI := immersionPullbackRiemannianBundle f hinj
    IsContMDiffRiemannianBundle J n F (fun x : N ↦ TangentSpace J x) := by
  let g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x) :=
    ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle
  let pulled := g.pullback f hf hinj
  let := immersionPullbackRiemannianBundle f hinj
  refine ⟨pulled.inner, pulled.contMDiff, ?_⟩
  intro x v w
  change (immersionPullbackRiemannianMetric f hinj).inner x v w =
    (g.pullback f hf hinj).inner x v w
  rw [immersionPullbackRiemannianMetric_inner, ContMDiffRiemannianMetric.pullback_inner,
    ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle_inner]
  rfl

/-- Pulling back a `C¹` Riemannian metric along a `C²` immersion gives a `C¹` metric. -/
theorem isContMDiffRiemannianBundle_immersionPullback
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] (f : N → M)
    (hf : ContMDiff J I 2 f) (hinj : ∀ x, Function.Injective (mfderiv J I f x)) :
    letI := immersionPullbackRiemannianBundle f hinj
    IsContMDiffRiemannianBundle J 1 F (fun x : N ↦ TangentSpace J x) :=
  isContMDiffRiemannianBundle_immersionPullback_of_smoothness f hf hinj

end CutoffRigidity
