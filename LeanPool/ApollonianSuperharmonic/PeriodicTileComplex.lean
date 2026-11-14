/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.PeriodicTileCore
public import LeanPool.ApollonianSuperharmonic.TileArea

-- [TABLET NODE: PeriodicTileComplex]

/-!
# PeriodicTileComplex

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
A periodic tile complex is an area-free periodic tile core together with the
two additional hypotheses used after coverage: the orbit-area identity
$$
  \sum_{a\in\mathcal T/L}|T_a|=[\mathbb Z[i]:L],
$$
computed using the selected vertex-orbit and lattice-coset representatives,
and the requirement that the two tiles on every graph edge have an actual
common footprint edge.  Equivalently, every prescribed graph adjacency is
supported by a nonconstant lattice-edge interface; two isolated common
footprint vertices, or a single corner contact, do not satisfy this
requirement.  The vertices belonging to such interfaces are recorded by
`CommonFootprintEdgeVertices`.
-/
structure PeriodicTileComplex (ι : Type) extends PeriodicTileCore ι where
-- BODY
  area_balance :
    (∑ a ∈ vertexOrbitReps, TileArea (tile a)) = latticeReps.card
  adjacent_has_common_edge : ∀ a b, plane.adjacent a b →
    (FootprintEdges (tile a) ∩ FootprintEdges (tile b)).Nonempty

end ApollonianSuperharmonic

end
