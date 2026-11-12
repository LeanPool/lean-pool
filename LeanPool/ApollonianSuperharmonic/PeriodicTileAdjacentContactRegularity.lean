/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.PeriodicTileComplex
public import LeanPool.ApollonianSuperharmonic.CommonFootprintEdgeVertices

-- [TABLET NODE: PeriodicTileAdjacentContactRegularity]

/-!
# PeriodicTileAdjacentContactRegularity

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
An adjacent-contact regularity certificate for a
`PeriodicTileComplex` $P$ asserts that, for every prescribed graph
edge $ab$, the complete raw common-footprint vertex set is exactly the set
of endpoints of actual common footprint edges:
$$
 \operatorname{foot}(P_a)\cap\operatorname{foot}(P_b)
 =\operatorname{CommonFootprintEdgeVertices}(P_a,P_b).
$$
Thus every raw contact of a prescribed adjacent pair is incident with a
common unit edge.  The condition is imposed only on prescribed adjacent
pairs: it neither promotes an isolated contact of a nonadjacent pair to an
edge nor forbids such a contact.
-/
structure PeriodicTileAdjacentContactRegularity {ι : Type}
    (P : PeriodicTileComplex ι) where
-- BODY
  adjacent_raw_eq_edge_vertices : ∀ a b, P.plane.adjacent a b →
    FootprintVertices (P.tile a) ∩ FootprintVertices (P.tile b) =
      CommonFootprintEdgeVertices (P.tile a) (P.tile b)

end ApollonianSuperharmonic

end
