/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianChartMetric
public import Mathlib.Geometry.Manifold.Riemannian.Basic

/-! # Actual chart pullback of a flow differential and its metric
The initial and terminal tangent maps are actual manifold derivatives. The
formula keeps the original Riemannian metric rather than a flat chart metric.
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
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

omit [IsContMDiffRiemannianBundle I 1 E fun x : M ↦ TangentSpace I x]
  [FiniteDimensional ℝ E]
  [BoundarylessManifold I M]
  [RiemannianBundle fun x : M ↦ TangentSpace I x] in
/-- The actual extended-chart derivative sends its own actual coordinate frame
back to the model vector. -/
theorem mfderiv_extChartAt_chartFrame (x₀ : M) (u : E) :
    (mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) x₀) (chartFrame (I := I) x₀ u x₀) = u := by
  rw [← TangentBundle.continuousLinearMapAt_trivializationAt (by simp)]
  exact (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt_symmL (by simp) u

omit [IsContMDiffRiemannianBundle I 1 E fun x : M ↦ TangentSpace I x]
  [FiniteDimensional ℝ E]
  [BoundarylessManifold I M]
  [RiemannianBundle fun x : M ↦ TangentSpace I x] in
/-- The actual inverse-chart derivative is the actual inverse tangent
trivialization at every interior target point. -/
theorem mfderiv_extChartAt_symm_apply_eq_frame (x₀ : M) {z : E}
    (hz : z ∈ interior (extChartAt I x₀).target) (u : E) :
    (mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm z) u =
      chartFrame (I := I) x₀ u ((extChartAt I x₀).symm z) := by
  let e := extChartAt I x₀
  have hy : e.symm z ∈ (chartAt H x₀).source := by
    simpa only [e, ← extChartAt_source I x₀] using e.map_target (interior_subset hz)
  have hRange : range I ∈ 𝓝 z := mem_of_superset (isOpen_interior.mem_nhds hz)
    (interior_subset.trans (extChartAt_target_subset_range x₀))
  change (mfderiv 𝓘(ℝ, E) I e.symm z) u =
    (trivializationAt E (TangentSpace I) x₀).symmL ℝ (e.symm z) u
  rw [TangentBundle.symmL_trivializationAt hy]
  have hpoint : e (e.symm z) = z := e.right_inv (interior_subset hz)
  rw [hpoint, mfderivWithin_of_mem_nhds hRange]
  rfl

omit [IsContMDiffRiemannianBundle I 1 E fun x : M ↦ TangentSpace I x]
  [FiniteDimensional ℝ E]
  [BoundarylessManifold I M] in
/-- The metric of the actual manifold derivative of a genuine chart-defined
map is exactly the original chart-metric pairing of its actual Fréchet derivative. -/
theorem inner_mfderiv_chart_conjugate (x₀ : M) {A : E → E}
    (hA : DifferentiableAt ℝ A (extChartAt I x₀ x₀))
    (hAz : A (extChartAt I x₀ x₀) ∈ interior (extChartAt I x₀).target) (u v : E) :
    inner ℝ
      ((mfderiv I I (fun y ↦ (extChartAt I x₀).symm (A (extChartAt I x₀ y))) x₀)
        (chartFrame (I := I) x₀ u x₀))
      ((mfderiv I I (fun y ↦ (extChartAt I x₀).symm (A (extChartAt I x₀ y))) x₀)
        (chartFrame (I := I) x₀ v x₀)) =
      chartMetric (I := I) x₀ (A (extChartAt I x₀ x₀))
        ((fderiv ℝ A (extChartAt I x₀ x₀)) u) ((fderiv ℝ A (extChartAt I x₀ x₀)) v) := by
  let e := extChartAt I x₀
  let z := e x₀
  have hRange : range I ∈ 𝓝 (A z) := mem_of_superset (isOpen_interior.mem_nhds hAz)
    (interior_subset.trans (extChartAt_target_subset_range x₀))
  have hInv : MDifferentiableAt 𝓘(ℝ, E) I e.symm (A z) :=
    (mdifferentiableWithinAt_extChartAt_symm (interior_subset hAz)).mdifferentiableAt hRange
  have hC := hInv.hasMFDerivAt.comp x₀
    (hA.hasFDerivAt.hasMFDerivAt.comp x₀
      (mdifferentiableAt_extChartAt (I := I) (by simp)).hasMFDerivAt)
  change inner ℝ ((mfderiv I I (e.symm ∘ A ∘ e) x₀) (chartFrame (I := I) x₀ u x₀))
    ((mfderiv I I (e.symm ∘ A ∘ e) x₀) (chartFrame (I := I) x₀ v x₀)) = _
  rw [hC.mfderiv]
  change inner ℝ
    ((mfderiv 𝓘(ℝ, E) I e.symm (A z)) ((fderiv ℝ A z)
      ((mfderiv I 𝓘(ℝ, E) e x₀) (chartFrame (I := I) x₀ u x₀))))
    ((mfderiv 𝓘(ℝ, E) I e.symm (A z)) ((fderiv ℝ A z)
      ((mfderiv I 𝓘(ℝ, E) e x₀) (chartFrame (I := I) x₀ v x₀)))) = _
  rw [mfderiv_extChartAt_chartFrame, mfderiv_extChartAt_chartFrame,
    mfderiv_extChartAt_symm_apply_eq_frame x₀ hAz,
    mfderiv_extChartAt_symm_apply_eq_frame x₀ hAz, chartMetric_apply]

end CutoffRigidity
