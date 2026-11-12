/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.TileOdometer

-- [TABLET NODE: TileOdometerBandPrototile]

/-!
# TileOdometerBandPrototile

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem TileOdometerBandPrototile (C : CircleCoordinates) (T : ProtoTile)
    (h : PartialOdometer) (hodo : TileOdometer C T h) :
    BandPrototile C T := by
-- BODY
  induction hodo with
  | line w x hw h hdom =>
      exact BandPrototile.line w x hw
  | unit z x T h hT hdom htrans =>
      cases T with
      | mk cells anchor =>
          simp_all only
          exact BandPrototile.unit z x anchor
  | decompose hq hT hsub hcells hfoot hcentroid hdom hvalue hcompat hslope ih =>
      exact hT

end ApollonianSuperharmonic

end
