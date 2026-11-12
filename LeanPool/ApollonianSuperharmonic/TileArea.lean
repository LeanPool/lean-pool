/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.ProtoTile

-- [TABLET NODE: TileArea]

/-!
# TileArea

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
The area $|T|$ of a prototile is the number of its constituent unit lattice
cells.  This agrees with the Euclidean area of $I(T)$ because the interiors
of distinct lattice cells are disjoint.
-/
def TileArea (T : ProtoTile) : Nat :=
-- BODY
  T.cells.card

end ApollonianSuperharmonic

end
