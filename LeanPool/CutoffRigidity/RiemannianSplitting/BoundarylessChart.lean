/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.RegularScalarChart

/-! # Actual extended charts on a boundaryless manifold
The model may have boundary: actual interiority of every manifold point is
enough to show that the actual extended chart targets are open.
-/

@[expose] public section
open Set
open scoped Manifold ContDiff Topology

namespace CutoffRigidity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [BoundarylessManifold I M]

/-- Boundarylessness of the actual manifold makes the actual extended chart
target open, without requiring that its whole model be boundaryless. -/
theorem isOpen_extChartAt_target_of_boundarylessManifold (x : M) :
    IsOpen (extChartAt I x).target := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  have hsource := (extChartAt I x).map_target hz
  have hchartsource : (extChartAt I x).symm z ∈ (chartAt H x).source := by
    simpa only [extChartAt_source] using hsource
  have hInt := (I.isInteriorPoint_iff_of_mem_atlas (by norm_num : (2 : ℕ∞ω) ≠ 0)
    (chart_mem_atlas H x) hchartsource).mp
    (BoundarylessManifold.isInteriorPoint (I := I) (x := (extChartAt I x).symm z))
  change extChartAt I x ((extChartAt I x).symm z) ∈ interior (extChartAt I x).target at hInt
  rw [(extChartAt I x).right_inv hz] at hInt
  exact mem_interior_iff_mem_nhds.mp hInt

/-- The actual extended chart, equipped with its proved open target. -/
noncomputable def boundarylessExtChart (x : M) : OpenPartialHomeomorph M E where
  toPartialEquiv := extChartAt I x
  continuousOn_toFun := continuousOn_extChartAt x
  continuousOn_invFun := continuousOn_extChartAt_symm x
  open_source := isOpen_extChartAt_source x
  open_target := isOpen_extChartAt_target_of_boundarylessManifold x

@[simp] theorem boundarylessExtChart_apply (x y : M) :
    boundarylessExtChart (I := I) x y = extChartAt I x y := rfl

@[simp] theorem boundarylessExtChart_symm_apply (x : M) (z : E) :
    (boundarylessExtChart (I := I) x).symm z = (extChartAt I x).symm z := rfl

end CutoffRigidity
