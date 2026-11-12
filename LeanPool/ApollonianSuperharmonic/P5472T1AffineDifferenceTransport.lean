/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryAffineVectorAction
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetrySlopeAction
public import LeanPool.ApollonianSuperharmonic.GaussianRealPoint
public import LeanPool.ApollonianSuperharmonic.TileQuarterTurnFormulas
public import Mathlib.Tactic.LinearCombination

-- [TABLET NODE: P5472T1AffineDifferenceTransport]

/-!
# P5472T1AffineDifferenceTransport

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5472T1AffineDifferenceTransport
    (s : BandPackingSymmetry)
    (hword : ∃ z : GaussianInt, s = .shift z ∨ s = (BandPackingSymmetry.shift z).comp .negate)
    (U V : ProtoTile) (x y : Real × Real) (v w : GaussianInt) (k : Real)
    (hc : TileCentroid V - TileCentroid U = k • GaussianRealPoint v)
    (hp : x - y = k • GaussianRealPoint w) :
    TileCentroid (BandPackingSymmetryTileAction s V) -
        TileCentroid (BandPackingSymmetryTileAction s U) =
      k • GaussianRealPoint (BandPackingSymmetryAffineVectorAction s (v, w)).1 ∧
    BandPackingSymmetrySlopeAction s V x - BandPackingSymmetrySlopeAction s U y =
      k • GaussianRealPoint (BandPackingSymmetryAffineVectorAction s (v, w)).2 := by
-- BODY
  have differenceShift (z : GaussianInt) (U V : ProtoTile)
      (x y : Real × Real) (v w : GaussianInt) (k : Real)
      (hc : TileCentroid V - TileCentroid U = k • GaussianRealPoint v)
      (hp : x - y = k • GaussianRealPoint w) :
      TileCentroid (BandPackingSymmetryTileAction (.shift z) V) -
          TileCentroid (BandPackingSymmetryTileAction (.shift z) U) =
        k • GaussianRealPoint
          (BandPackingSymmetryAffineVectorAction (.shift z) (v, w)).1 ∧
      BandPackingSymmetrySlopeAction (.shift z) V x -
          BandPackingSymmetrySlopeAction (.shift z) U y =
        k • GaussianRealPoint
          (BandPackingSymmetryAffineVectorAction (.shift z) (v, w)).2 := by
    rcases z with ⟨zr, zi⟩
    rcases v with ⟨vr, vi⟩
    rcases w with ⟨wr, wi⟩
    have hc1 := congrArg Prod.fst hc
    have hc2 := congrArg Prod.snd hc
    have hp1 := congrArg Prod.fst hp
    have hp2 := congrArg Prod.snd hp
    refine ⟨hc, ?_⟩
    apply Prod.ext
    · simp [BandPackingSymmetrySlopeAction, BandPackingSymmetryAffineVectorAction,
        GaussianRealPoint, GaussianReflection] at hc1 hc2 hp1 hp2 ⊢
      linear_combination hp1 + (zr : Real) * hc1 + (zi : Real) * hc2
    · simp [BandPackingSymmetrySlopeAction, BandPackingSymmetryAffineVectorAction,
        GaussianRealPoint, GaussianReflection] at hc1 hc2 hp1 hp2 ⊢
      linear_combination hp2 + (zi : Real) * hc1 - (zr : Real) * hc2
  have differenceNegate (U V : ProtoTile) (x y : Real × Real)
      (v w : GaussianInt) (k : Real)
      (hc : TileCentroid V - TileCentroid U = k • GaussianRealPoint v)
      (hp : x - y = k • GaussianRealPoint w) :
      TileCentroid (BandPackingSymmetryTileAction .negate V) -
          TileCentroid (BandPackingSymmetryTileAction .negate U) =
        k • GaussianRealPoint
          (BandPackingSymmetryAffineVectorAction .negate (v, w)).1 ∧
      BandPackingSymmetrySlopeAction .negate V x -
          BandPackingSymmetrySlopeAction .negate U y =
        k • GaussianRealPoint
          (BandPackingSymmetryAffineVectorAction .negate (v, w)).2 := by
    rcases v with ⟨vr, vi⟩
    rcases w with ⟨wr, wi⟩
    have hc1 := congrArg Prod.fst hc
    have hc2 := congrArg Prod.snd hc
    have hp1 := congrArg Prod.fst hp
    have hp2 := congrArg Prod.snd hp
    change TileCentroid (TileQuarterTurn V) - TileCentroid (TileQuarterTurn U) = _ ∧ _
    rw [(TileQuarterTurnFormulas V).2.2.2.2.1,
      (TileQuarterTurnFormulas U).2.2.2.2.1]
    simp only [BandPackingSymmetryAffineVectorAction,
      BandPackingSymmetrySlopeAction, GaussianQuarterTurn,
      GaussianRealPoint]
    constructor
    · apply Prod.ext
      · simp only [Prod.fst_add, Prod.fst_neg, sub_eq_add_neg,
          Prod.smul_fst, smul_eq_mul, Int.cast_neg]
        ring_nf
        have hh : (TileCentroid V).2 - (TileCentroid U).2 = k * (vi : Real) := by
          simpa [GaussianRealPoint] using congrArg Prod.snd hc
        linear_combination -hh
      · change (TileCentroid V).1 - (TileCentroid U).1 = k * (vr : Real)
        have hh := congrArg Prod.fst hc
        change (TileCentroid V).1 - (TileCentroid U).1 = k * (vr : Real) at hh
        exact hh
    · apply Prod.ext
      · simp only [Prod.fst_add, Prod.fst_neg, sub_eq_add_neg,
          Prod.smul_fst, smul_eq_mul, Int.cast_neg]
        ring_nf
        have hh : x.2 - y.2 = k * (wi : Real) := by
          simpa [GaussianRealPoint] using congrArg Prod.snd hp
        linear_combination -hh
      · change x.1 - y.1 = k * (wr : Real)
        have hh := congrArg Prod.fst hp
        change x.1 - y.1 = k * (wr : Real) at hh
        exact hh
  rcases hword with ⟨z, hs | hs⟩
  · rw [hs]
    exact ⟨hc, (differenceShift z U V x y v w k hc hp).2⟩
  · rw [hs]
    have hn := differenceNegate U V x y v w k hc hp
    have hs := differenceShift z (TileQuarterTurn U) (TileQuarterTurn V)
      (BandPackingSymmetrySlopeAction .negate V x)
      (BandPackingSymmetrySlopeAction .negate U y)
      (BandPackingSymmetryAffineVectorAction .negate (v, w)).1
      (BandPackingSymmetryAffineVectorAction .negate (v, w)).2 k hn.1 hn.2
    exact hs

end ApollonianSuperharmonic

end
