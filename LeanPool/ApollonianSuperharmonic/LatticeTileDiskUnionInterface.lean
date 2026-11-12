/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintEdges
public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintVertices
public import LeanPool.ApollonianSuperharmonic.CellDisjointCommonFootprintIncidence
public import LeanPool.ApollonianSuperharmonic.ClosedSquareRealization
public import LeanPool.ApollonianSuperharmonic.CommonFootprintEdgeVertices
public import LeanPool.ApollonianSuperharmonic.ConnectedCommonBoundaryPath
public import LeanPool.ApollonianSuperharmonic.FootprintEdges
public import LeanPool.ApollonianSuperharmonic.FootprintVertices
public import LeanPool.ApollonianSuperharmonic.LatticeTile
public import LeanPool.ApollonianSuperharmonic.LatticeDiskUnionIntersectionConnected
public import LeanPool.ApollonianSuperharmonic.LatticeTileGridStructure
public import LeanPool.ApollonianSuperharmonic.ProtoTile
public import LeanPool.ApollonianSuperharmonic.SimpleGridPathBetween
public import LeanPool.ApollonianSuperharmonic.TileRealization

-- [TABLET NODE: LatticeTileDiskUnionInterface]

/-!
# LatticeTileDiskUnionInterface

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem LatticeTileDiskUnionInterface (U V W : ProtoTile)
    (hU : LatticeTile U) (hV : LatticeTile V) (hW : LatticeTile W)
    (hdisjoint : Disjoint U.cells V.cells)
    (hunion : ∀ z : LatticeCell,
      z ∈ W.cells ↔ z ∈ U.cells ∨ z ∈ V.cells)
    (hcommon :
      (FootprintEdges U ∩ FootprintEdges V).Nonempty) :
    FootprintVertices U ∩ FootprintVertices V =
        CommonFootprintEdgeVertices U V ∧
      (∃ x y : GaussianInt,
        SimpleGridPathBetween
          (CommonFootprintEdgeVertices U V)
          (FootprintEdges U ∩ FootprintEdges V) x y) ∧
      FootprintEdges U ∩ FootprintEdges V =
        BoundaryFootprintEdges U ∩ BoundaryFootprintEdges V ∧
      BoundaryFootprintVertices U ∩ BoundaryFootprintVertices V =
        CommonFootprintEdgeVertices U V := by
-- BODY
  have hUstructure := LatticeTileGridStructure U hU
  have hVstructure := LatticeTileGridStructure V hV
  have hUne : U.cells.Nonempty := hUstructure.1.1
  have hVne : V.cells.Nonempty := hVstructure.1.1
  have hconnected : IsConnected
      (TileRealization U ∩ TileRealization V) :=
    LatticeDiskUnionIntersectionConnected U V W hU hV hW hdisjoint hunion hcommon
  obtain ⟨hedges, hvertices, hboundaryVertices⟩ :=
    CellDisjointCommonFootprintIncidence U V hUne hVne hdisjoint
      hconnected hcommon
  have hpath : ∃ x y : GaussianInt,
      SimpleGridPathBetween
        (CommonFootprintEdgeVertices U V)
        (FootprintEdges U ∩ FootprintEdges V) x y :=
    ConnectedCommonBoundaryPath U V hUne hVne hdisjoint hconnected
      hUstructure.2.2 hVstructure.2.2 hcommon
  exact ⟨hvertices, hpath, hedges, hboundaryVertices⟩

end ApollonianSuperharmonic

end
