/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintVertices
public import LeanPool.ApollonianSuperharmonic.ClosedSquareRealization
public import LeanPool.ApollonianSuperharmonic.FourNeighborConnected
public import LeanPool.ApollonianSuperharmonic.LatticeTile
public import LeanPool.ApollonianSuperharmonic.LatticeTileBoundarySimpleGridCycle
public import LeanPool.ApollonianSuperharmonic.LatticeTileFourNeighborConnected
public import LeanPool.ApollonianSuperharmonic.LatticeTileNoCheckerboard
public import LeanPool.ApollonianSuperharmonic.NoCheckerboardCellVertex
public import LeanPool.ApollonianSuperharmonic.ProtoTile
public import LeanPool.ApollonianSuperharmonic.SimpleGridCycle
public import LeanPool.ApollonianSuperharmonic.TileRealization

-- [TABLET NODE: LatticeTileGridStructure]

/-!
# LatticeTileGridStructure

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem LatticeTileGridStructure (T : ProtoTile) (hT : LatticeTile T) :
    FourNeighborConnected (T.cells : Set LatticeCell) ∧
    NoCheckerboardCellVertex (T.cells : Set LatticeCell) ∧
    SimpleGridCycle (BoundaryFootprintVertices T)
      (BoundaryFootprintEdges T) := by
-- BODY
  exact ⟨LatticeTileFourNeighborConnected T hT,
    LatticeTileNoCheckerboard T hT,
    LatticeTileBoundarySimpleGridCycle T hT⟩

end ApollonianSuperharmonic

end
