/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianChartFrames
public import Mathlib.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.IsManifold.InteriorChart
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic

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
    (v : E) :
    fderiv ℝ (f ∘ (extChartAt I x₀).symm) z v =
      mvfderiv I f ((extChartAt I x₀).symm z)
        (chartFrame (I := I) x₀ v ((extChartAt I x₀).symm z)) := by
  let e := extChartAt I x₀
  have hy := e.map_target hz
  have hy' : e.symm z ∈ (chartAt H x₀).source := by
    simpa only [e, extChartAt_source] using hy
  have hopen : IsOpen e.target :=
    (chartAt H x₀).isOpen_extend_target_of_mem_atlas (chart_mem_atlas H x₀)
  have hRange := Filter.mem_of_superset (hopen.mem_nhds hz) (extChartAt_target_subset_range x₀)
  have h := TauCeti.fderivWithin_comp_extChartAt_symm (f := f) x₀ hy
  rw [e.right_inv hz, fderivWithin_of_mem_nhds hRange] at h
  have hFrame : chartFrame (I := I) x₀ v (e.symm z) =
      tangentCoordChange I x₀ (e.symm z) (e.symm z) v := by
    unfold chartFrame chartFrameCLM
    rw [TangentBundle.symmL_trivializationAt_eq_core hy']
    rfl
  rw [hFrame]
  exact DFunLike.congr_fun h v

end CutoffRigidity
