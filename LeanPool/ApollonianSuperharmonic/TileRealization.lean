/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.ClosedSquareRealization
public import LeanPool.ApollonianSuperharmonic.ProtoTile

-- [TABLET NODE: TileRealization]

/-!
# TileRealization

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
The real realization of a prototile $T$ is the finite union
$$
 I(T)=\bigcup_{s_x\in T}\overline s_x\subset\mathbb R^2.
$$
The anchor of an empty prototile contributes no square to $I(T)$.
-/
def TileRealization (T : ProtoTile) : Set (Real × Real) :=
-- BODY
  ⋃ x ∈ T.cells, ClosedSquareRealization x

end ApollonianSuperharmonic

end
