/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.LatticeTile
public import Mathlib.Init


/-!
# LatticeTileNonempty

Shared facts adapted from Wesley Pegden's Apache-2.0 Trellis formalization of
Levine–Pegden–Smart, replacing repeated implementations at their common dependency level.
-/

@[expose] public section

namespace ApollonianSuperharmonic
namespace LatticeTileNonempty

/-- Shared cells identity for LatticeTileNonempty. -/
theorem cells :
    (by
      classical
      exact
        ∀ (X : ProtoTile), (LatticeTile X) → (X.cells.Nonempty) ) := by
  classical
  intro X hX
  unfold LatticeTile TopologicalDisk TileRealization at hX
  rcases hX with ⟨e⟩
  have hp : (0 : Real × Real) ∈
      (Metric.closedBall (0 : Real × Real) 1 : Set (Real × Real)) := by simp
  have hm := (e ⟨(0 : Real × Real), hp⟩).property
  simp only [Set.mem_iUnion] at hm
  obtain ⟨x, hx⟩ := hm
  exact ⟨x, by simpa [TileRealization] using hx.1⟩

end LatticeTileNonempty
end ApollonianSuperharmonic

end
