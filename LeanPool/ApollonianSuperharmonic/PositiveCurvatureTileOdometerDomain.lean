/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.TileOdometerDomain

-- [TABLET NODE: PositiveCurvatureTileOdometerDomain]

/-!
# PositiveCurvatureTileOdometerDomain

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem PositiveCurvatureTileOdometerDomain :
    ∀ (C : CircleCoordinates), ∀ (T : ProtoTile), ∀ (h : PartialOdometer), (0 < C.1) →
        ((TileOdometer C T h) → ((h.domain : Set GaussianInt) = FootprintVertices T)) := by
  intro C T h _ hO
-- BODY
  exact TileOdometerDomain C T h hO

end ApollonianSuperharmonic

end
