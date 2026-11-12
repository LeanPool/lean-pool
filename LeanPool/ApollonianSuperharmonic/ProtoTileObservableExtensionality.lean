/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintEdges
public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintVertices
public import LeanPool.ApollonianSuperharmonic.FootprintVertices
public import LeanPool.ApollonianSuperharmonic.TileCentroid
public import LeanPool.ApollonianSuperharmonic.TileRealization

-- [TABLET NODE: ProtoTileObservableExtensionality]

/-!
# ProtoTileObservableExtensionality

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem ProtoTileObservableExtensionality
    (T U : ProtoTile) (hcells : T.cells = U.cells)
    (hanchor : T.cells = ∅ → T.anchor = U.anchor) :
    FootprintVertices T = FootprintVertices U ∧
      BoundaryFootprintVertices T = BoundaryFootprintVertices U ∧
      BoundaryFootprintEdges T = BoundaryFootprintEdges U ∧
      TileRealization T = TileRealization U ∧
      TileCentroid T = TileCentroid U := by
-- BODY
  have hnonempty : T.cells.Nonempty ↔ U.cells.Nonempty := by
    rw [hcells]
  by_cases hT : T.cells.Nonempty
  · have hU : U.cells.Nonempty := hnonempty.mp hT
    constructor
    · simp only [FootprintVertices, ite_eq_left hT, ite_eq_left hU]
      rw [hcells]
    constructor
    · simp only [BoundaryFootprintVertices, ite_eq_left hT, ite_eq_left hU,
        BoundaryFootprintEdges]
      rw [hcells]
    constructor
    · simp only [BoundaryFootprintEdges]
      rw [hcells]
    constructor
    · simp only [TileRealization]
      rw [hcells]
    · simp only [TileCentroid, ite_eq_left hT, ite_eq_left hU]
      rw [hcells]
  · have hTe : T.cells = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    have hUe : U.cells = ∅ := by rw [← hcells]; exact hTe
    have ha := hanchor hTe
    constructor
    · simp [FootprintVertices, hT, hUe, ha]
    constructor
    · simp [BoundaryFootprintVertices, hT, hUe, ha]
    constructor
    · simp [BoundaryFootprintEdges, hTe, hUe]
    constructor
    · simp [TileRealization, hTe, hUe]
    · simp [TileCentroid, hT, hUe, ha]

end ApollonianSuperharmonic

end
