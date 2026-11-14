/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryPartialOdometerActionFormulas
public import LeanPool.ApollonianSuperharmonic.BandPrototileCompleteSquareCentroid
public import LeanPool.ApollonianSuperharmonic.TileQuarterTurnFormulas
public import LeanPool.ApollonianSuperharmonic.TileReflectionFormulas

-- [TABLET NODE: BandPrototileFootprintSlopeCovariance]

/-!
# BandPrototileFootprintSlopeCovariance

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandPrototileFootprintSlopeCovariance
    (g : BandPackingSymmetry) (C : CircleCoordinates) (T : ProtoTile)
    (h : PartialOdometer) (hT : BandPrototile C T)
    (hne : T.cells.Nonempty)
    (hdom : (h.domain : Set GaussianInt) = FootprintVertices T) :
    PartialOdometerSlope (BandPackingSymmetryPartialOdometerAction g h) =
      (PartialOdometerSlope h).map
        (BandPackingSymmetrySlopeAction g T) := by
-- BODY
  have formulas := BandPackingSymmetryPartialOdometerActionFormulas g h h
  have centroid := BandPrototileCompleteSquareCentroid C T h hT hne hdom
  dsimp at centroid
  let squares := PartialOdometerSquares h
  let replacement : ProtoTile := ⟨squares, T.anchor⟩
  have replacement_nonempty : replacement.cells.Nonempty := by
    simpa [replacement, squares] using centroid.1
  have squares_nonempty : squares.Nonempty := by
    simpa [squares] using centroid.1
  have replacement_cells : PartialOdometerSquares h = replacement.cells := by
    rfl
  have centroid_action : ∀ k : BandPackingSymmetry, ∀ U V : ProtoTile,
      TileCentroid U = TileCentroid V →
        TileCentroid (BandPackingSymmetryTileAction k U) =
          TileCentroid (BandPackingSymmetryTileAction k V) := by
    intro k
    induction k with
    | identity =>
        intro U V huv
        simpa [BandPackingSymmetryTileAction] using huv
    | shift w =>
        intro U V huv
        simpa [BandPackingSymmetryTileAction] using huv
    | negate =>
        intro U V huv
        rw [BandPackingSymmetryTileAction, BandPackingSymmetryTileAction,
          (TileQuarterTurnFormulas U).2.2.2.2.1,
          (TileQuarterTurnFormulas V).2.2.2.2.1, huv]
    | conjugate =>
        intro U V huv
        rw [BandPackingSymmetryTileAction, BandPackingSymmetryTileAction,
          (TileQuarterTurnFormulas (TileQuarterTurn (TileReflection U))).2.2.2.2.1,
          (TileQuarterTurnFormulas (TileQuarterTurn (TileReflection V))).2.2.2.2.1,
          (TileQuarterTurnFormulas (TileReflection U)).2.2.2.2.1,
          (TileQuarterTurnFormulas (TileReflection V)).2.2.2.2.1,
          (TileReflectionFormulas U).2.2.2.2.1,
          (TileReflectionFormulas V).2.2.2.2.1, huv]
    | comp a b iha ihb =>
        intro U V huv
        apply iha
        apply ihb U V huv
  have slope_action_centroid : ∀ k : BandPackingSymmetry, ∀ U V : ProtoTile,
      TileCentroid U = TileCentroid V → ∀ p : ℝ × ℝ,
        BandPackingSymmetrySlopeAction k U p =
          BandPackingSymmetrySlopeAction k V p := by
    intro k
    induction k with
    | identity =>
        intro U V huv p
        rfl
    | shift w =>
        intro U V huv p
        simp [BandPackingSymmetrySlopeAction, huv]
    | negate =>
        intro U V huv p
        rfl
    | conjugate =>
        intro U V huv p
        rfl
    | comp a b iha ihb =>
        intro U V huv p
        rw [BandPackingSymmetrySlopeAction, BandPackingSymmetrySlopeAction]
        rw [ihb U V huv p]
        apply iha
        exact centroid_action b U V huv
  have action_eq :
      BandPackingSymmetrySlopeAction g replacement =
        BandPackingSymmetrySlopeAction g T := by
    funext p
    apply slope_action_centroid g replacement T
    have hcent : TileCentroid replacement = TileCentroid T := by
      simp only [TileCentroid, replacement, squares, ite_eq_left squares_nonempty,
        ite_eq_left hne]
      apply Prod.ext
      · have hc := congrArg Prod.fst centroid.2
        simp only [TileCentroid, ite_eq_left hne] at hc
        norm_num [Finset.sum_add_distrib] at hc ⊢
        have cardNonzero : ((PartialOdometerSquares h).card : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.ne_of_gt (Finset.card_pos.mpr squares_nonempty))
        rw [add_div, mul_div_cancel_left₀ _ cardNonzero] at hc
        linarith only [hc]
      · have hc := congrArg Prod.snd centroid.2
        simp only [TileCentroid, ite_eq_left hne] at hc
        norm_num [Finset.sum_add_distrib] at hc ⊢
        have cardNonzero : ((PartialOdometerSquares h).card : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.ne_of_gt (Finset.card_pos.mpr squares_nonempty))
        rw [add_div, mul_div_cancel_left₀ _ cardNonzero] at hc
        linarith only [hc]
    exact hcent
  have result := formulas.2.2.2.2.2.2.2 replacement replacement_nonempty
    replacement_cells
  simpa [action_eq] using result

end ApollonianSuperharmonic

end
