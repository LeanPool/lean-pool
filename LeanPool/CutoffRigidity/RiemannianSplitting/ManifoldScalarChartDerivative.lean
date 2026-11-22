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
open scoped Manifold ContDiff Topology


namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [BoundarylessManifold I M]

/-- The scalar derivative in an arbitrary point of the actual chart is the
intrinsic differential applied to the actual chart frame. -/
theorem fderiv_chartScalar_frame (x₀ : M) {z : E}
    (hz : z ∈ (extChartAt I x₀).target) {f : M → ℝ}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f ((extChartAt I x₀).symm z)) (v : E) :
    fderiv ℝ (f ∘ (extChartAt I x₀).symm) z v =
      mvfderiv I f ((extChartAt I x₀).symm z)
        (chartFrame (I := I) x₀ v ((extChartAt I x₀).symm z)) := by
  let e := extChartAt I x₀
  let y := e.symm z
  have hy : y ∈ (chartAt H x₀).source := by
    simpa only [y, e, extChartAt_source] using e.map_target hz
  have hround : e y = z := e.right_inv hz
  have hRange : range I ∈ 𝓝 z := by
    rw [← hround]
    have ht := (I.isInteriorPoint_iff_of_mem_atlas (by norm_num : (2 : ℕ∞ω) ≠ 0)
      (chart_mem_atlas H x₀) hy).mp
        (BoundarylessManifold.isInteriorPoint (I := I) (x := y))
    have hi : e y ∈ interior (range I) :=
      OpenPartialHomeomorph.interior_extend_target_subset_interior_range _ ht
    exact mem_of_superset (isOpen_interior.mem_nhds hi) interior_subset
  have hsymm : MDifferentiableAt 𝓘(ℝ, E) I e.symm z :=
    (mdifferentiableWithinAt_extChartAt_symm hz).mdifferentiableAt hRange
  have hframe : chartFrame (I := I) x₀ v y = mfderiv 𝓘(ℝ, E) I e.symm z v := by
    unfold chartFrame chartFrameCLM
    rw [TangentBundle.symmL_trivializationAt hy, hround, mfderivWithin_of_mem_nhds hRange]
    rfl
  rw [hframe]
  have derivative := mvfderiv_comp_apply z hf hsymm v
  rw [mvfderiv_eq_fderiv] at derivative
  exact derivative

end CutoffRigidity
