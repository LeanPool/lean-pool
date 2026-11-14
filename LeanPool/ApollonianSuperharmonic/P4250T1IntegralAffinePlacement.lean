/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandPrototileTranslationNormalForm
public import LeanPool.ApollonianSuperharmonic.TileOdometerBandPrototile
public import LeanPool.ApollonianSuperharmonic.TileOdometerAffineTranslation
public import LeanPool.ApollonianSuperharmonic.PositiveCurvatureTileOdometerSupportTransport

-- [TABLET NODE: P4250T1IntegralAffinePlacement]

/-!
# P4250T1IntegralAffinePlacement

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4250T1IntegralAffinePlacement
    (C : CircleCoordinates) (U V : ProtoTile) (h : PartialOdometer)
    (p : Real × Real) (a : GaussianInt) (hC : 0 < C.1)
    (ho : TileOdometer C U h) (hV : BandPrototile C V)
    (hp : PartialOdometerSlope h = some p) :
    ∃ k : PartialOdometer, TileOdometer C V k ∧
      PartialOdometerSlope k = some (p + GaussianRealPoint a) := by
-- BODY
  obtain ⟨u, hu, _⟩ := BandPrototileTranslationNormalForm C V U hV
    (TileOdometerBandPrototile C U h ho)
  refine ⟨PartialOdometerAffineTranslate h u a 0, ?_, ?_⟩
  · exact PositiveCurvatureTileOdometerSupportTransport C
      (TileTranslation U u) V _ hC
      (TileOdometerAffineTranslation C U h u a 0 ho) hV hu.symm
  · rw [(PartialOdometerAffineTranslateFormulas h u a 0).2.2.2.2.2, hp]
    rfl

end ApollonianSuperharmonic

end
