/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.TopologicalDisk
public import LeanPool.ApollonianSuperharmonic.TileRealization

-- [TABLET NODE: LatticeTile]

/-!
# LatticeTile

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
A lattice tile is a prototile $T$ whose closed-square realization $I(T)$ is
a topological disk in the sense of `TopologicalDisk`.  Consequently,
the assigned anchor of an empty prototile does not turn its empty real
realization into a lattice tile.
-/
def LatticeTile (T : ProtoTile) : Prop :=
-- BODY
  TopologicalDisk (TileRealization T)

end ApollonianSuperharmonic

end
