/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.OdometerStringSlopeTelescoping

-- [TABLET NODE: P4261T2UnitStringTelescoping]

/-!
# P4261T2UnitStringTelescoping

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4261T2UnitStringTelescoping
    (C : BandCircle) (_hunit : C.1.1.1 = 1)
    (orientation : Bool) (base R S : ProtoTile)
    (tiles reverseTiles : List ProtoTile) (hs reverseHs : List PartialOdometer)
    (hf : OdometerStringRespect C orientation base R S tiles hs)
    (hr : OdometerStringRespect C orientation base S R reverseTiles reverseHs)
    (hendpoint : PartialOdometer)
    (hh : hs.head? = some hendpoint) (hh' : reverseHs.getLast? = some hendpoint)
    (U V : ProtoTile) (g k : PartialOdometer)
    (hU : (U, g) ∈ tiles.zip hs) (hV : (V, k) ∈ reverseTiles.zip reverseHs) :
    ∃ s t : Real × Real,
      PartialOdometerSlope g = some s ∧ PartialOdometerSlope k = some t ∧
      t.1 - s.1 = CircleMatrix C 0 0 * ((TileCentroid V).1 - (TileCentroid U).1) +
        CircleMatrix C 0 1 * ((TileCentroid V).2 - (TileCentroid U).2) ∧
      t.2 - s.2 = CircleMatrix C 1 0 * ((TileCentroid V).1 - (TileCentroid U).1) +
        CircleMatrix C 1 1 * ((TileCentroid V).2 - (TileCentroid U).2) := by
  exact odometerStringSlopeTelescoping C orientation base R S tiles reverseTiles hs reverseHs
    hf hr hendpoint hh hh' U V g k hU hV

end ApollonianSuperharmonic

end
