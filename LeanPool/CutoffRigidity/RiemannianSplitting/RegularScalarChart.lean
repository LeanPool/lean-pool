/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.ManifoldScalarChartDerivative
public import LeanPool.CutoffRigidity.RiemannianSplitting.ParallelGradientRegularLevel
public import Mathlib.Analysis.Calculus.Implicit
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! # Regular scalar coordinates from the actual manifold differential
The Banach implicit function theorem constructs the actual local coordinates;
a local product chart is not an input to the argument.
-/

@[expose] public section
open Bundle Set Filter
open scoped Manifold ContDiff Topology
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
    normedSpaceTangentSpaceVectorSpace

namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [BoundarylessManifold I M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

omit [FiniteDimensional ℝ E] [RiemannianBundle fun x : M ↦ TangentSpace I x] in
/-- A nonzero intrinsic directional derivative makes the actual scalar chart
map a submersion at the chart center. -/
theorem surjective_fderiv_chartScalar (x : M) {f : M → ℝ}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (X : (x : M) → TangentSpace I x) (hne : mvfderiv I f x (X x) ≠ 0) :
    Function.Surjective (fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x)) := by
  intro a
  refine ⟨(a / mvfderiv I f x (X x)) •
    chartCoordinateField (I := I) x X (extChartAt I x x), ?_⟩
  rw [map_smul, fderiv_chartScalar_direction x hf X]
  simp only [smul_eq_mul]
  exact div_mul_cancel₀ a hne

omit [FiniteDimensional ℝ E]
  [IsManifold I 2 M]
  [RiemannianBundle fun x : M ↦ TangentSpace I x] in
/-- Actual `C¹` scalar functions have actual strictly differentiable chart
representatives at an interior point. -/
theorem hasStrictFDerivAt_chartScalar (x : M) {f : M → ℝ}
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 1 f x) :
    HasStrictFDerivAt (f ∘ (extChartAt I x).symm)
      (fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x)) (extChartAt I x x) := by
  have hRange : range I ∈ 𝓝 (extChartAt I x x) := range_mem_nhds_isInteriorPoint
    (BoundarylessManifold.isInteriorPoint (I := I) (x := x))
  have hi := (contMDiffWithinAt_extChartAt_symm_range_self (I := I) (n := 1) x).contMDiffAt hRange
  have hf' : ContMDiffAt I 𝓘(ℝ, ℝ) 1 f ((extChartAt I x).symm (extChartAt I x x)) := by
    simpa only [extChartAt_to_inv] using hf
  have smooth := (hf'.comp _ hi).contDiffAt
  exact smooth.hasStrictFDerivAt (smooth.differentiableAt one_ne_zero).hasFDerivAt one_ne_zero

omit [RiemannianBundle fun x : M ↦ TangentSpace I x] in
/-- The actual implicit-function chart has the original scalar function as
its first coordinate and sends the original point to `(f x,0)`. Its second
coordinate is the actual kernel of the actual chart derivative. -/
theorem exists_regularScalar_chart (x : M) {f : M → ℝ}
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 1 f x)
    (X : (x : M) → TangentSpace I x) (hne : mvfderiv I f x (X x) ≠ 0) :
    ∃ e : OpenPartialHomeomorph E (ℝ ×
        (fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x)).ker),
      (extChartAt I x x) ∈ e.source ∧
      e (extChartAt I x x) = (f x, 0) ∧
      ∀ z, (e z).1 = f ((extChartAt I x).symm z) := by
  let F := f ∘ (extChartAt I x).symm
  let D := fderiv ℝ F (extChartAt I x x)
  have hd := hasStrictFDerivAt_chartScalar x hf
  have hrange : D.range = ⊤ := LinearMap.range_eq_top.mpr
    (surjective_fderiv_chartScalar x (hf.mdifferentiableAt one_ne_zero) X hne)
  let e := hd.implicitToOpenPartialHomeomorph F D hrange
  refine ⟨e, hd.mem_implicitToOpenPartialHomeomorph_source hrange, ?_, ?_⟩
  · simpa only [F, Function.comp_apply, extChartAt_to_inv] using
      hd.implicitToOpenPartialHomeomorph_self hrange
  · intro z
    exact hd.implicitToOpenPartialHomeomorph_fst hrange z

section ParallelGradient

variable {N : Type*} [EMetricSpace N] [ChartedSpace H N]
  [IsManifold I 2 N] [BoundarylessManifold I N] [CompleteSpace N] [PreconnectedSpace N]
  [RiemannianBundle (fun x : N ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : N ↦ TangentSpace I x)]
  [IsRiemannianManifold I N]

omit [CompleteSpace N] [IsRiemannianManifold I N] in
/-- Every point admits an actual regular coordinate chart for the actual
potential of a nonzero parallel gradient. All differential nondegeneracy is
derived from the actual parallel-gradient assumptions. -/
theorem exists_parallelGradient_regularScalar_chart
    {X : (x : N) → TangentSpace I x} (hX : ContMDiff I I.tangent 1 (T% X))
    (hpX : ∀ x, CovariantDerivative.leviCivitaConnection I N X x = 0)
    {f : N → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 1 f)
    (hgrad : ∀ x v, mvfderiv I f x v = inner ℝ (X x) v)
    (x₀ : N) (hne : X x₀ ≠ 0) (x : N) :
    ∃ e : OpenPartialHomeomorph E (ℝ ×
        (fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x)).ker),
      (extChartAt I x x) ∈ e.source ∧
      e (extChartAt I x x) = (f x, 0) ∧
      ∀ z, (e z).1 = f ((extChartAt I x).symm z) := by
  apply exists_regularScalar_chart x (hf x) X
  rw [hgrad, real_inner_self_eq_norm_sq]
  exact pow_ne_zero 2 (norm_ne_zero_iff.mpr
    (parallelField_ne_zero_everywhere hX hpX x₀ hne x))

end ParallelGradient

end CutoffRigidity
