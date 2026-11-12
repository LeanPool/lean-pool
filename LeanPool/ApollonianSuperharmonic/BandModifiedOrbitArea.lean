/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.ModifiedSubtileOccurrenceInterpretation
public import LeanPool.ApollonianSuperharmonic.TileArea

-- [TABLET NODE: BandModifiedOrbitArea]

/-!
# BandModifiedOrbitArea

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandModifiedOrbitArea (P : Fin 3 -> Bool -> ProtoTile)
    (O : ProtoTile) (R : Finset GaussianInt)
    (c0 c1 c2 c3 c4 : Nat)
    (hO : O.cells ⊆ (P 0 true).cells)
    (hA : TileArea (P 0 true) = c1)
    (hB : TileArea (P 0 false) = c1)
    (hC : TileArea (P 1 true) = c2)
    (hD : TileArea (P 1 false) = c2)
    (hE : TileArea (P 2 true) = c3)
    (hF : TileArea (P 2 false) = c3)
    (hOarea : TileArea O = c4)
    (hcurvature : 2 * c1 + 2 * c2 + 2 * c3 = c0 + c4)
    (hindex : R.card = c0) :
    TileArea (TileCellComplement (P 0 true) O) +
        TileArea (P 0 false) + TileArea (P 1 true) +
        TileArea (P 1 false) + TileArea (P 2 true) +
        TileArea (P 2 false) = R.card := by
-- BODY
  classical
  simp only [TileArea, TileCellComplement]
  rw [Finset.card_sdiff_of_subset hO]
  have areaA : (P 0 true).cells.card = c1 := hA
  have areaB : (P 0 false).cells.card = c1 := hB
  have areaC : (P 1 true).cells.card = c2 := hC
  have areaD : (P 1 false).cells.card = c2 := hD
  have areaE : (P 2 true).cells.card = c3 := hE
  have areaF : (P 2 false).cells.card = c3 := hF
  have areaO : O.cells.card = c4 := hOarea
  have sizeBound : c4 ≤ c1 := by
    have cellBound : O.cells.card ≤ (P 0 true).cells.card := Finset.card_le_card hO
    omega
  rw [areaA, areaB, areaC, areaD, areaE, areaF, areaO, hindex]
  omega

end ApollonianSuperharmonic

end
