/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryAffineVectorAction
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetrySlopeAction
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryVectorAction
public import LeanPool.ApollonianSuperharmonic.GaussianRealPoint
public import LeanPool.ApollonianSuperharmonic.TileQuarterTurnFormulas
public import LeanPool.ApollonianSuperharmonic.TileReflectionFormulas

-- [TABLET NODE: P5625T1CentroidSlopeDifferenceCovariance]

/-!
# P5625T1CentroidSlopeDifferenceCovariance

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5625T1CentroidSlopeDifferenceCovariance :
    (∀ (g : BandPackingSymmetry) (z : GaussianInt × GaussianInt),
      (BandPackingSymmetryAffineVectorAction g z).1 =
        BandPackingSymmetryVectorAction g z.1) ∧
    ∀ (g : BandPackingSymmetry) (U V : ProtoTile)
      (x y : ℝ × ℝ) (v a : GaussianInt) (k : ℝ),
      TileCentroid V - TileCentroid U = k • GaussianRealPoint v →
      x - y = k • GaussianRealPoint a →
      TileCentroid (BandPackingSymmetryTileAction g V) -
          TileCentroid (BandPackingSymmetryTileAction g U) =
        k • GaussianRealPoint
          (BandPackingSymmetryAffineVectorAction g (v, a)).1 ∧
      BandPackingSymmetrySlopeAction g V x -
          BandPackingSymmetrySlopeAction g U y =
        k • GaussianRealPoint
          (BandPackingSymmetryAffineVectorAction g (v, a)).2 := by
-- BODY
  constructor
  · intro g
    induction g with
    | identity => intro z; rfl
    | shift w => intro z; rfl
    | negate => intro z; rfl
    | conjugate => intro z; rfl
    | comp a b iha ihb =>
        intro z
        change (BandPackingSymmetryAffineVectorAction a
          (BandPackingSymmetryAffineVectorAction b z)).1 =
          BandPackingSymmetryVectorAction a (BandPackingSymmetryVectorAction b z.1)
        rw [iha, ihb]
  · intro g
    induction g with
    | identity =>
        intro U V x y v a k hc hp
        exact ⟨hc, hp⟩
    | shift w =>
        intro U V x y v a k hc hp
        rcases w with ⟨wr, wi⟩
        rcases v with ⟨vr, vi⟩
        rcases a with ⟨ar, ai⟩
        refine ⟨hc, ?_⟩
        have hc1 := congrArg Prod.fst hc
        have hc2 := congrArg Prod.snd hc
        have hp1 := congrArg Prod.fst hp
        have hp2 := congrArg Prod.snd hp
        apply Prod.ext
        all_goals
          simp [BandPackingSymmetrySlopeAction, BandPackingSymmetryAffineVectorAction,
            GaussianRealPoint, GaussianReflection] at hc1 hc2 hp1 hp2 ⊢
          ring_nf
          nlinarith [congrArg (fun z : ℝ => (wr : ℝ) * z) hc1,
            congrArg (fun z : ℝ => (wi : ℝ) * z) hc2,
            congrArg (fun z : ℝ => (wi : ℝ) * z) hc1,
            congrArg (fun z : ℝ => (wr : ℝ) * z) hc2]
    | negate =>
        intro U V x y v a k hc hp
        have hc1 := congrArg Prod.fst hc
        have hc2 := congrArg Prod.snd hc
        have hp1 := congrArg Prod.fst hp
        have hp2 := congrArg Prod.snd hp
        change TileCentroid (TileQuarterTurn V) - TileCentroid (TileQuarterTurn U) = _ ∧ _
        rw [(TileQuarterTurnFormulas V).2.2.2.2.1,
          (TileQuarterTurnFormulas U).2.2.2.2.1]
        constructor <;> apply Prod.ext
        all_goals
          simp [BandPackingSymmetrySlopeAction, BandPackingSymmetryAffineVectorAction,
            GaussianRealPoint, GaussianQuarterTurn] at hc1 hc2 hp1 hp2 ⊢
          linarith
    | conjugate =>
        intro U V x y v a k hc hp
        have hc1 := congrArg Prod.fst hc
        have hc2 := congrArg Prod.snd hc
        have hp1 := congrArg Prod.fst hp
        have hp2 := congrArg Prod.snd hp
        change TileCentroid (TileQuarterTurn (TileQuarterTurn (TileReflection V))) -
          TileCentroid (TileQuarterTurn (TileQuarterTurn (TileReflection U))) = _ ∧ _
        rw [(TileQuarterTurnFormulas (TileQuarterTurn (TileReflection V))).2.2.2.2.1,
          (TileQuarterTurnFormulas (TileQuarterTurn (TileReflection U))).2.2.2.2.1,
          (TileQuarterTurnFormulas (TileReflection V)).2.2.2.2.1,
          (TileQuarterTurnFormulas (TileReflection U)).2.2.2.2.1,
          (TileReflectionFormulas V).2.2.2.2.1,
          (TileReflectionFormulas U).2.2.2.2.1]
        constructor <;> apply Prod.ext
        all_goals
          simp [BandPackingSymmetrySlopeAction, BandPackingSymmetryAffineVectorAction,
            GaussianRealPoint, GaussianReflection] at hc1 hc2 hp1 hp2 ⊢
          linarith
    | comp a b iha ihb =>
        intro U V x y v w k hc hp
        have hh := ihb U V x y v w k hc hp
        exact iha (BandPackingSymmetryTileAction b U)
          (BandPackingSymmetryTileAction b V)
          (BandPackingSymmetrySlopeAction b V x)
          (BandPackingSymmetrySlopeAction b U y)
          (BandPackingSymmetryAffineVectorAction b (v, w)).1
          (BandPackingSymmetryAffineVectorAction b (v, w)).2 k hh.1 hh.2

end ApollonianSuperharmonic

end
