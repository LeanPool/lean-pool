/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintEdges

-- [TABLET NODE: BoundaryFootprintVertices]

/-!
# BoundaryFootprintVertices

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
The boundary-footprint vertices of a nonempty prototile are the endpoints of
its boundary-footprint edges.  For an empty prototile, its boundary footprint
is instead the assigned singleton anchor, as in the paper's degenerate-tile
convention.
-/
def BoundaryFootprintVertices (T : ProtoTile) : Set GaussianInt :=
-- BODY
  if T.cells.Nonempty then
    {v | ∃ e ∈ BoundaryFootprintEdges T, v ∈ e}
  else
    {T.anchor}

end ApollonianSuperharmonic

end
