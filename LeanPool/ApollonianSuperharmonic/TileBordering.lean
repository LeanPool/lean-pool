/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintEdges

-- [TABLET NODE: TileBordering]

/-!
# TileBordering

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Two prototiles border one another when they have no common lattice cell and
their boundary-footprint graphs share a lattice edge.  A mere corner
intersection does not count as bordering, and degenerate anchor-touching does
not by itself supply a shared edge.
-/
def TileBordering (T U : ProtoTile) : Prop :=
-- BODY
  Disjoint T.cells U.cells ∧
    (BoundaryFootprintEdges T ∩ BoundaryFootprintEdges U).Nonempty

end ApollonianSuperharmonic

end
