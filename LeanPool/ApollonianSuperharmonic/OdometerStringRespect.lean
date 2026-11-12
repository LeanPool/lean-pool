/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.LeftLatticeAdjacent
public import LeanPool.ApollonianSuperharmonic.TileString

-- [TABLET NODE: OdometerStringRespect]

/-!
# OdometerStringRespect

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a fixed unit orientation, an ordered family of tile odometers respects
an oriented tile string when it assigns
one tile odometer for $C$ to every tile of the string, in the same order,
and consecutive assigned odometers are `LeftLatticeAdjacent`.
This assertion concerns the domains, centroids, and slopes of the ordered
family.  It does not choose additive constants and does not assert that the
family has already been glued to a common extension.
-/
def OdometerStringRespect (C : BandCircle) (orientation : Bool) (base R S : ProtoTile)
    (tiles : List ProtoTile) (hs : List PartialOdometer) : Prop :=
-- BODY
  TileString C orientation base R S tiles ∧
    List.Forall₂ (fun T h => TileOdometer C.1.1 T h) tiles hs ∧
    (tiles.zip hs).IsChain (fun X Y => LeftLatticeAdjacent C X.1 Y.1 X.2 Y.2)

end ApollonianSuperharmonic

end
