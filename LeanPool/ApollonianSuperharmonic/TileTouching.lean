/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintVertices
public import LeanPool.ApollonianSuperharmonic.SimpleGridPath

-- [TABLET NODE: TileTouching]

/-!
# TileTouching

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Two nonempty prototiles touch when they have no common cell and the ordinary
intersection of their boundary-footprint graphs is a simple unit grid path
with at least two vertices.  Both the shared vertices and the shared boundary
edges are intersected; no edge is inferred from endpoint membership.

If one prototile is empty, it touches the other exactly when its assigned
singleton anchor lies in the other's boundary footprint.  This convention is
symmetric; in particular, two empty prototiles touch exactly when their
anchors agree.
-/
def TileTouching (T U : ProtoTile) : Prop :=
-- BODY
  (T.cells.Nonempty ∧ U.cells.Nonempty ∧ Disjoint T.cells U.cells ∧
    SimpleGridPath
      (BoundaryFootprintVertices T ∩ BoundaryFootprintVertices U)
      (BoundaryFootprintEdges T ∩ BoundaryFootprintEdges U)) ∨
  (T.cells = ∅ ∧ T.anchor ∈ BoundaryFootprintVertices U) ∨
  (U.cells = ∅ ∧ U.anchor ∈ BoundaryFootprintVertices T)

end ApollonianSuperharmonic

end
