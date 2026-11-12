/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.ProtoTile

-- [TABLET NODE: TileHalfTurn]

/-!
# TileHalfTurn

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
The origin half-turn of a prototile $T$ is the prototile $-T$ whose cell
basepoints are
$$
 \{-x-1-i:x\in T_{\rm cell}\}.
$$
If $T$ is nonempty, its auxiliary anchor is normalized by the same
cell-basepoint rule, so that $a_{-T}=-a_T-1-i$.  If $T$ is empty, its
anchor represents its singleton footprint and is instead sent as a grid
vertex, so that $a_{-T}=-a_T$.
-/
def TileHalfTurn (T : ProtoTile) : ProtoTile :=
-- BODY
  { cells := T.cells.image (fun x => -x - 1 - ⟨0, 1⟩)
    anchor :=
      if T.cells.Nonempty then -T.anchor - 1 - ⟨0, 1⟩ else -T.anchor }

end ApollonianSuperharmonic

end
