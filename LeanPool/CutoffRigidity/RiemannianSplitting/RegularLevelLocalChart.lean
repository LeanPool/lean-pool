/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.ScalarLevelChart
public import LeanPool.CutoffRigidity.RiemannianSplitting.BoundarylessChart

/-! # Actual local coordinates on a regular level
The scalar implicit-function coordinates are restricted to the actual level,
with the original subspace topology. No submanifold-chart assumption is used.
-/

@[expose] public section
open Bundle Set
open scoped Manifold ContDiff Topology
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
    normedSpaceTangentSpaceVectorSpace

namespace CutoffRigidity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [BoundarylessManifold I M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

omit [RiemannianBundle fun x : M ↦ TangentSpace I x] in
/-- An actual regular zero level has an actual open local chart into the
actual derivative kernel, with the original subspace topology. -/
theorem exists_regularScalar_levelChart {f : M → ℝ} (x : {y : M // f y = 0})
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 1 f x.val)
    (X : (y : M) → TangentSpace I y) (hne : mvfderiv I f x.val (X x.val) ≠ 0) :
    ∃ c : OpenPartialHomeomorph {y : M // f y = 0}
        (fderiv ℝ (f ∘ (extChartAt I x.val).symm) (extChartAt I x.val x.val)).ker,
      x ∈ c.source ∧ c x = 0 := by
  obtain ⟨e, heSource, heCenter, heFirst⟩ := exists_regularScalar_chart x.val hf X hne
  let c := (boundarylessExtChart (I := I) x.val).trans e
  have hcFirst (y : M) (hy : y ∈ c.source) : (c y).1 = f y := by
    change (e (extChartAt I x.val y)).1 = f y
    rw [heFirst, (extChartAt I x.val).left_inv hy.1]
  let level := scalarLevelChart f c hcFirst x
  refine ⟨level, ?_, ?_⟩
  · change x.val ∈ c.source
    exact ⟨mem_extChartAt_source x.val, heSource⟩
  · change (e (extChartAt I x.val x.val)).2 = 0
    rw [heCenter]

section ParallelGradient
variable {N : Type*} [EMetricSpace N] [ChartedSpace H N]
  [IsManifold I 2 N] [BoundarylessManifold I N] [CompleteSpace N] [PreconnectedSpace N]
  [RiemannianBundle (fun x : N ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : N ↦ TangentSpace I x)]
  [IsRiemannianManifold I N]

omit [CompleteSpace N] [IsRiemannianManifold I N] in
/-- The actual parallel-gradient zero level admits genuine local charts,
with nondegeneracy derived from nonzero parallelism everywhere. -/
theorem exists_parallelGradient_levelChart
    {X : (x : N) → TangentSpace I x} (hX : ContMDiff I I.tangent 1 (T% X))
    (hpX : ∀ x, CovariantDerivative.leviCivitaConnection I N X x = 0)
    {f : N → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 1 f)
    (hgrad : ∀ x v, mvfderiv I f x v = inner ℝ (X x) v)
    (x₀ : N) (hne : X x₀ ≠ 0) (x : {y : N // f y = 0}) :
    ∃ c : OpenPartialHomeomorph {y : N // f y = 0}
        (fderiv ℝ (f ∘ (extChartAt I x.val).symm) (extChartAt I x.val x.val)).ker,
      x ∈ c.source ∧ c x = 0 := by
  apply exists_regularScalar_levelChart x (hf x.val) X
  rw [hgrad, real_inner_self_eq_norm_sq]
  exact pow_ne_zero 2 (norm_ne_zero_iff.mpr
    (parallelField_ne_zero_everywhere hX hpX x₀ hne x.val))

end ParallelGradient
end CutoffRigidity
