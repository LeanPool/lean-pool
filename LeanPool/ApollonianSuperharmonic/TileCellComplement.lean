/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.ProtoTile

-- [TABLET NODE: TileCellComplement]

/-!
# TileCellComplement

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For prototiles $T$ and $U$, the cell complement $T\setminus U$ is the
prototile with cell set $T_{\rm cells}\setminus U_{\rm cells}$.  It keeps
$T$'s auxiliary anchor; whenever the complement is nonempty this anchor is
irrelevant.
-/
def TileCellComplement (T U : ProtoTile) : ProtoTile :=
-- BODY
  ⟨T.cells \ U.cells, T.anchor⟩

end ApollonianSuperharmonic

end
