/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianChartFrames
public import Mathlib.Geometry.Manifold.Riemannian.Basic

/-! # Actual scalar derivatives in actual manifold charts -/

@[expose] public section
open Bundle Set Filter
open scoped Manifold Topology


namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [BoundarylessManifold I M]

omit [FiniteDimensional ℝ E] in
/-- A scalar chart derivative in the actual coordinate direction of `X` equals
the original intrinsic differential applied to the original tangent vector. -/
theorem fderiv_chartScalar_direction (x₀ : M) {f : M → ℝ}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x₀)
    (X : (x : M) → TangentSpace I x) :
    (fderiv ℝ (f ∘ (extChartAt I x₀).symm) (extChartAt I x₀ x₀))
      (chartCoordinateField (I := I) x₀ X (extChartAt I x₀ x₀)) =
      mvfderiv I f x₀ (X x₀) := by
  let e := extChartAt I x₀
  let z := e x₀
  have hRange : range I ∈ 𝓝 z := range_mem_nhds_isInteriorPoint
    (BoundarylessManifold.isInteriorPoint (I := I) (x := x₀))
  have hsymm : MDifferentiableAt 𝓘(ℝ, E) I e.symm z :=
    (mdifferentiableWithinAt_extChartAt_symm (mem_extChartAt_target x₀)).mdifferentiableAt hRange
  have atCenter : (mfderiv 𝓘(ℝ, E) I e.symm z : E →L[ℝ] E) =
      ContinuousLinearMap.id ℝ E := by
    rw [← mfderivWithin_of_mem_nhds hRange]
    exact mfderivWithin_range_extChartAt_symm
  rw [chartCoordinateField_self]
  have derivative := mvfderiv_comp_apply_of_eq z hf hsymm
    (extChartAt_to_inv (I := I) x₀) (X x₀)
  rw [mvfderiv_eq_fderiv] at derivative
  change (fderiv ℝ (f ∘ e.symm) z) (X x₀) = _
  refine derivative.trans ?_
  have applied := congrArg (fun L : E →L[ℝ] E ↦ L (X x₀)) atCenter
  exact congrArg (fun w : E ↦ mvfderiv I f x₀ w) applied

end CutoffRigidity
