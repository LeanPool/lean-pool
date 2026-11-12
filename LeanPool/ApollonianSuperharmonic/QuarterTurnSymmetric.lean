/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.TileCentroid
public import LeanPool.ApollonianSuperharmonic.TileRealization

-- [TABLET NODE: QuarterTurnSymmetric]

/-!
# QuarterTurnSymmetric

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
A prototile $T$ has $90^\circ$ rotational symmetry when its real realization
is invariant under the quarter-turn
$$(x,y)\longmapsto(c_1-(y-c_2),c_2+(x-c_1))$$
about its centroid $c=\operatorname{cent}(T)$.
-/
def QuarterTurnSymmetric (T : ProtoTile) : Prop :=
-- BODY
  ∀ p : Real × Real, p ∈ TileRealization T ↔
    let c := TileCentroid T
    (c.1 - (p.2 - c.2), c.2 + (p.1 - c.1)) ∈ TileRealization T

end ApollonianSuperharmonic

end
