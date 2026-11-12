/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintVertices
public import LeanPool.ApollonianSuperharmonic.CommonFootprintEdgeVertices
public import LeanPool.ApollonianSuperharmonic.FiniteInducedTilePatch
public import LeanPool.ApollonianSuperharmonic.SimpleGridPathBetween

-- [TABLET NODE: ExactPatchBoundaryInterface]

/-!
# ExactPatchBoundaryInterface

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
An *exact patch-boundary interface* between a finite patch $K$ and an
indexed tile $T_d$ consists of one nontrivial
`SimpleGridPathBetween` whose edge set is exactly
$E(T_K)\cap E(T_d)$ and whose vertex set is exactly
`CommonFootprintEdgeVertices`$(T_K,T_d)$.  These common footprint
edges must equal the common boundary-footprint edges, and the complete raw
common boundary-vertex set must equal the path's vertex set.  Thus the
definition excludes both an extra edge component and a stray corner
contact.
-/
def ExactPatchBoundaryInterface {ι : Type}
    {G : PlaneTriangulation ι} {tile : ι → ProtoTile}
    (K : FiniteInducedTilePatch G tile) (d : ι) : Prop :=
-- BODY
  ∃ x y : GaussianInt,
    SimpleGridPathBetween
      (CommonFootprintEdgeVertices K.unionTile (tile d))
      (FootprintEdges K.unionTile ∩ FootprintEdges (tile d)) x y ∧
    FootprintEdges K.unionTile ∩ FootprintEdges (tile d) =
      BoundaryFootprintEdges K.unionTile ∩
        BoundaryFootprintEdges (tile d) ∧
    BoundaryFootprintVertices K.unionTile ∩
        BoundaryFootprintVertices (tile d) =
      CommonFootprintEdgeVertices K.unionTile (tile d)

end ApollonianSuperharmonic

end
