/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module
public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianChartFrames

/-! # Lie brackets of chart frame fields -/
@[expose] public section
open VectorField
open scoped Manifold
namespace CutoffRigidity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [BoundarylessManifold I M]

/-- Actual coordinate-constant frame fields commute at their chart center. -/
theorem mlieBracket_chartFrames (x : M) (u v : E) :
    mlieBracket I (chartFrame (I := I) x u) (chartFrame (I := I) x v) x = 0 := by
  rw [mlieBracket_chartFrame]
  have hd : fderiv ℝ (chartCoordinateField (I := I) x (chartFrame (I := I) x u))
      (extChartAt I x x) = fderiv ℝ (fun _ : E => u) (extChartAt I x x) :=
    (chartCoordinateField_frame_eventuallyEq (I := I) x u).fderiv_eq
  rw [hd]
  simp [chartFrame, chartFrameCLM]

end CutoffRigidity
