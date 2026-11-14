/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4458T1BoundarySide
public import LeanPool.ApollonianSuperharmonic.P4458T1RestrictionFamily

-- [TABLET NODE: P4458T1BoundaryPlacement]

/-!
# P4458T1BoundaryPlacement

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a boundary frame $F$ and a six-restriction family $D$, a boundary
placement consists of a literal joining tile $J$ with the same cells as
$D.T_i^-$, a tile-odometer certificate on $J$ for the unchanged function
$D.h_i^-$, its ancestor-odometer certificate relative to $F.h_0$, and its
negative signed occurrence certificate in $F.q$.
It records a `P4458T1BoundarySide` from $(R^-,h^-)$ to
$(J,D.h_i^-)$ and another from $(J,D.h_i^-)$ to $(R^+,h^+)$.
The same tile and the same function occur in both sides. Neither final
endpoint is replaced by a record with equal cells.
-/
structure P4458T1BoundaryPlacement
    {C : BandCircle} {orientation : Bool} {base Rminus Rplus : ProtoTile}
    {hminus hplus : PartialOdometer}
    (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus)
    (D : P4458T1RestrictionFamily F) where
-- BODY
  /-- The literal joining tile shared by the two boundary sides. -/
  join : ProtoTile
  cells : join.cells = (D.tiles F.slot false).cells
  odometer : TileOdometer C.1.1 join (D.functions F.slot false)
  ancestor : AncestorOdometer C.1.1 F.outer.1.1
    join F.tile (D.functions F.slot false) F.odometer
  occurrence : BandSubtileOccurrence F.q F.tile F.slot false join
  /-- The direct or recursive side from the initial endpoint to the joining tile. -/
  left : P4458T1BoundarySide F Rminus join hminus (D.functions F.slot false)
  /-- The direct or recursive side from the joining tile to the terminal endpoint. -/
  right : P4458T1BoundarySide F join Rplus (D.functions F.slot false) hplus

end ApollonianSuperharmonic

end
