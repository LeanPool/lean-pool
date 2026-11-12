/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetry
public import LeanPool.ApollonianSuperharmonic.TileQuarterTurn
public import LeanPool.ApollonianSuperharmonic.TileReflection

-- [TABLET NODE: BandPackingSymmetryTileAction]

/-!
# BandPackingSymmetryTileAction

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
The grid action associated with a band-packing symmetry word sends a
prototile to itself for the identity and packing shifts and to its grid
quarter-turn for coordinate negation.  Coordinate conjugation acts by
reflection followed by a half-turn, so its linear action on grid points is
$v\mapsto-\overline v$, matching the canonical orientation of band
vectors.  A composite word acts by composing these tile maps in the same
order as its coordinate action.
-/
def BandPackingSymmetryTileAction :
    BandPackingSymmetry → ProtoTile → ProtoTile :=
-- BODY
  fun g T => match g with
    | .identity => T
    | .negate => TileQuarterTurn T
    | .conjugate => TileQuarterTurn (TileQuarterTurn (TileReflection T))
    | .shift _ => T
    | .comp g h =>
        BandPackingSymmetryTileAction g
          (BandPackingSymmetryTileAction h T)

end ApollonianSuperharmonic

end
