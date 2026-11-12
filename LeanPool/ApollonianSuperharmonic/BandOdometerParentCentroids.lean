/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralOdometerRowData
public import Mathlib.Init


/-!
# BandOdometerParentCentroids

Shared facts adapted from Wesley Pegden's Apache-2.0 Trellis formalization of
Levine–Pegden–Smart, replacing repeated implementations at their common dependency level.
-/

@[expose] public section

namespace ApollonianSuperharmonic
namespace BandOdometerParentCentroids

/-- Shared positive identity for BandOdometerParentCentroids. -/
theorem positive :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C0 :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C0 T), ∀ (h : PartialOdometer), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (r : Fin 3 ->
            Bool -> PartialOdometer), ∀ (Q : Fin 3 -> Bool -> ProtoTile), ∀ (S : Fin 3 -> Bool ->
            ProtoTile), ∀ (u : Fin 3 -> Bool -> PartialOdometer), ∀ (v : Fin 3 -> Bool ->
            PartialOdometer), ∀ (g : IntegerLatticeFunction), (BandOrderedGeneralOdometerRowData
            q cfg C0 T cert h P r Q S u v g) → (
        let cOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        TileCentroid (P 1 true) - TileCentroid T = cOff (BandVectors.1 (q 1) (q 3))) ) := by
  classical
  intro q cfg C0 T cert h P r Q S u v g data cOff
  simpa [cOff, Fin.add_def] using data.hPcent 1 true

/-- Shared negative identity for BandOdometerParentCentroids. -/
theorem negative :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C0 :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C0 T), ∀ (h : PartialOdometer), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (r : Fin 3 ->
            Bool -> PartialOdometer), ∀ (Q : Fin 3 -> Bool -> ProtoTile), ∀ (S : Fin 3 -> Bool ->
            ProtoTile), ∀ (u : Fin 3 -> Bool -> PartialOdometer), ∀ (v : Fin 3 -> Bool ->
            PartialOdometer), ∀ (g : IntegerLatticeFunction), (BandOrderedGeneralOdometerRowData
            q cfg C0 T cert h P r Q S u v g) → (
        let cOff (z : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint z -
            (-(GaussianRealPoint z).2, (GaussianRealPoint z).1))
        TileCentroid (P 1 false) - TileCentroid T = -cOff (BandVectors.1 (q 1) (q 3))) ) := by
  classical
  intro q cfg C0 T cert h P r Q S u v g data cOff
  simpa [cOff, Fin.add_def] using data.hPcent 1 false

end BandOdometerParentCentroids
end ApollonianSuperharmonic

end
