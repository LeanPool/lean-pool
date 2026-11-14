/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.QuarterTurnSymmetricCenteredTransport

-- [TABLET NODE: P3996T1CenteredQuarterTurnInclusion]

/-!
# P3996T1CenteredQuarterTurnInclusion

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3996T1CenteredQuarterTurnInclusion (T P : ProtoTile)
    (hT : QuarterTurnSymmetric T) (hP : QuarterTurnSymmetric P)
    (hsub : P.cells ⊆ T.cells) :
    ∃ t p : GaussianInt,
      GaussianRealPoint t =
        ((TileCentroid T).1 + (TileCentroid T).2,
          (TileCentroid T).2 - (TileCentroid T).1) ∧
      GaussianRealPoint p =
        ((TileCentroid P).1 + (TileCentroid P).2,
          (TileCentroid P).2 - (TileCentroid P).1) ∧
      ∀ a : GaussianInt,
        (TileTranslation P (a + t - p)).cells ⊆
          (TileTranslation T a).cells ∧
        TileCentroid (TileTranslation P (a + t - p)) -
            TileCentroid (TileTranslation T a) =
          (-((TileCentroid P - TileCentroid T).2),
            (TileCentroid P - TileCentroid T).1) := by
-- BODY
  obtain ⟨t, ht, htcells, _⟩ := QuarterTurnSymmetricCenteredTransport T hT
  obtain ⟨p, hp, hpcells, _⟩ := QuarterTurnSymmetricCenteredTransport P hP
  refine ⟨t, p, ht, hp, ?_⟩
  intro a
  constructor
  · have hturn : (TileQuarterTurn P).cells ⊆ (TileQuarterTurn T).cells := by
      rw [(TileQuarterTurnFormulas P).1, (TileQuarterTurnFormulas T).1]
      exact Finset.image_subset_image hsub
    rw [(TileTranslationFormulas P (a + t - p)).1,
      (TileTranslationFormulas T a).1]
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    rw [← hpcells, (TileTranslationFormulas (TileQuarterTurn P) p).1] at hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    have hwt : GaussianTranslation t w ∈ T.cells := by
      rw [← htcells, (TileTranslationFormulas (TileQuarterTurn T) t).1]
      exact Finset.mem_image.mpr ⟨w, hturn hw, rfl⟩
    exact Finset.mem_image.mpr ⟨GaussianTranslation t w, hwt, by
      simp [GaussianTranslation]
      abel⟩
  · rw [(TileTranslationFormulas P (a + t - p)).2.2.2.2.1,
      (TileTranslationFormulas T a).2.2.2.2.1]
    have ht1 := congrArg Prod.fst ht
    have ht2 := congrArg Prod.snd ht
    have hp1 := congrArg Prod.fst hp
    have hp2 := congrArg Prod.snd hp
    simp only [GaussianRealPoint] at ht1 ht2 hp1 hp2
    simp only [GaussianInt.intCast_re, GaussianInt.intCast_im] at ht1 ht2 hp1 hp2
    apply Prod.ext <;> simp [Int.cast_add, Int.cast_sub] <;> linarith

end ApollonianSuperharmonic

end
