/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.BandPrototileQuarterTurn


-- [TABLET NODE: P4055T1BandQuarterTurn]

/-!
# P4055T1BandQuarterTurn

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4055T1BandQuarterTurn (D : CircleCoordinates) (V : ProtoTile)
    (hV : BandPrototile D V) : QuarterTurnSymmetric V := by
-- BODY
  exact BandPrototileQuarterTurn.symmetry D V hV

end ApollonianSuperharmonic

end
