/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.TileCellComplement
public import LeanPool.ApollonianSuperharmonic.TileQuarterTurn
public import LeanPool.ApollonianSuperharmonic.TileReflection
public import LeanPool.ApollonianSuperharmonic.TileTranslation

-- [TABLET NODE: TileCellComplementCovariance]

/-!
# TileCellComplementCovariance

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem TileCellComplementCovariance : ∀ (T U : ProtoTile) (u : GaussianInt),
    TileTranslation (TileCellComplement T U) u =
      TileCellComplement (TileTranslation T u) (TileTranslation U u) ∧
    TileQuarterTurn (TileCellComplement T U) =
      TileCellComplement (TileQuarterTurn T) (TileQuarterTurn U) ∧
    TileReflection (TileCellComplement T U) =
      TileCellComplement (TileReflection T) (TileReflection U) := by
-- BODY
  have tile_equality : ∀ (A B : ProtoTile),
      A.cells = B.cells → A.anchor = B.anchor → A = B := by
    intro A B hc ha
    cases A with
    | mk ac aa =>
      cases B with
      | mk bc ba =>
        simp_all
  have image_difference : ∀ (A B : Finset GaussianInt)
      (f : GaussianInt → GaussianInt), Function.Injective f →
      (A \ B).image f = A.image f \ B.image f := by
    intro A B f hf
    exact Finset.image_sdiff A B hf
  have translation_injective (u : GaussianInt) :
      Function.Injective (GaussianTranslation u) := by
    intro a b h
    dsimp [GaussianTranslation] at h
    exact add_right_cancel h
  have quarter_injective : Function.Injective GaussianQuarterTurn := by
    intro a b h
    apply Zsqrtd.ext
    · simpa [GaussianQuarterTurn] using congrArg (fun z : GaussianInt => z.im) h
    · simpa [GaussianQuarterTurn] using congrArg (fun z : GaussianInt => z.re) h
  have reflection_injective : Function.Injective GaussianReflection := by
    intro a b h
    apply Zsqrtd.ext
    · simpa [GaussianReflection] using congrArg (fun z : GaussianInt => z.re) h
    · simpa [GaussianReflection] using congrArg (fun z : GaussianInt => -z.im) h
  intro T U u
  constructor
  · apply tile_equality
    · simp only [TileTranslation, TileCellComplement]
      exact image_difference T.cells U.cells (GaussianTranslation u)
        (translation_injective u)
    · simp only [TileTranslation, TileCellComplement]
  constructor
  · apply tile_equality
    · simp only [TileQuarterTurn, TileCellComplement]
      exact image_difference T.cells U.cells
        (fun x => GaussianQuarterTurn x - 1) (by
          intro a b h
          apply quarter_injective
          have shifted := congrArg (fun z : GaussianInt => z + 1) h
          simpa using shifted)
    · simp only [TileQuarterTurn, TileCellComplement]
  · apply tile_equality
    · simp only [TileReflection, TileCellComplement]
      exact image_difference T.cells U.cells
        (fun x => GaussianReflection x - ⟨0, 1⟩) (by
          intro a b h
          apply reflection_injective
          have shifted := congrArg (fun z : GaussianInt => z + ⟨0, 1⟩) h
          simpa using shifted)
    · simp only [TileReflection, TileCellComplement]

end ApollonianSuperharmonic

end
