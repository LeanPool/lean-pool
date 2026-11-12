/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.GaussianQuarterTurn
public import LeanPool.ApollonianSuperharmonic.ProtoTile

-- [TABLET NODE: TileQuarterTurn]

/-!
# TileQuarterTurn

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
The quarter-turn $qT$ of a prototile about the origin has cell basepoints
$qx-1$ for $x$ a cell basepoint of $T$, and has anchor $q(a_T)$.  The
subtraction of $1$ is the lower-left-corner correction: the geometric image
of the closed square based at $x$ under $(s,t)\mapsto(-t,s)$ is the closed
square based at $qx-1$.  The anchor is a vertex, not a cell basepoint, so it
receives no correction; this remains meaningful when $T$ is empty.
-/
def TileQuarterTurn (T : ProtoTile) : ProtoTile :=
-- BODY
  ⟨T.cells.image (fun x => GaussianQuarterTurn x - 1),
    GaussianQuarterTurn T.anchor⟩

end ApollonianSuperharmonic

end
