/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module
public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianChartFrames
import TauCeti.Geometry.Manifold.VectorField.CoordinateFrame

/-! # Lie brackets of chart frame fields -/
@[expose] public section
open Bundle Filter VectorField
open scoped Manifold Topology
namespace CutoffRigidity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]

/-- Actual coordinate-constant frame fields commute at their chart center. -/
theorem mlieBracket_chartFrames (x : M) (u v : E) :
    mlieBracket I (chartFrame (I := I) x u) (chartFrame (I := I) x v) x = 0 := by
  let : IsManifold I (minSmoothness ℝ 2) M := by
    simpa using (inferInstance : IsManifold I 2 M)
  have frame_eq (w : E) :
      chartFrame (I := I) x w =ᶠ[𝓝 x]
        fun y ↦ (trivializationAt E (TangentSpace I) x).symm y w := by
    filter_upwards [chart_source_mem_nhds H x] with y hy
    exact Bundle.Trivialization.symmL_apply _ (by simpa using hy) w
  rw [(frame_eq u).mlieBracket_vectorField_eq (I := I) (frame_eq v)]
  exact TauCeti.Manifold.mlieBracket_symm_trivializationAt x (mem_extChartAt_source x) u v

end CutoffRigidity
