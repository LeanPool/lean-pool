/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.ModifiedSubtileOccurrenceInterpretation
public import LeanPool.ApollonianSuperharmonic.SubtileOccurrenceInterpretation

-- [TABLET NODE: BandModifiedUnionEquality]

/-!
# BandModifiedUnionEquality

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandModifiedUnionEquality (P : Fin 3 -> Bool -> ProtoTile)
    (O : ProtoTile) (u v : GaussianInt)
    (hOB : O.cells ⊆ (P 0 false).cells) :
    forall x : LatticeCell,
      (exists o : PeriodicSubtileIndex,
        x ∈ (SubtileOccurrenceInterpretation P u v o).cells) <->
      (exists o : PeriodicSubtileIndex,
        x ∈ (ModifiedSubtileOccurrenceInterpretation P O u v o).cells) := by
-- BODY
  classical
  intro x
  constructor
  · rintro ⟨o, hx⟩
    cases o with
    | mk label first second =>
      cases label with
      | A =>
          change x ∈ (TileTranslation (P 0 true)
            ((first : GaussianInt) * u + (second : GaussianInt) * v)).cells at hx
          rcases Finset.mem_image.mp hx with ⟨y, hy, hxy⟩
          by_cases hyo : y ∈ O.cells
          · have hyb : y ∈ (P 0 false).cells := hOB hyo
            refine ⟨⟨.B, first, second⟩, ?_⟩
            change x ∈ (TileTranslation (P 0 false)
              ((first : GaussianInt) * u + (second : GaussianInt) * v)).cells
            apply Finset.mem_image.mpr
            exact ⟨y, hyb, hxy⟩
          · refine ⟨⟨.A, first, second⟩, ?_⟩
            change x ∈ (TileTranslation (TileCellComplement (P 0 true) O)
              ((first : GaussianInt) * u + (second : GaussianInt) * v)).cells
            apply Finset.mem_image.mpr
            exact ⟨y, Finset.mem_sdiff.mpr ⟨hy, hyo⟩, hxy⟩
      | B =>
          exact ⟨⟨.B, first, second⟩, hx⟩
      | C =>
          exact ⟨⟨.C, first, second⟩, hx⟩
      | D =>
          exact ⟨⟨.D, first, second⟩, hx⟩
      | E =>
          exact ⟨⟨.E, first, second⟩, hx⟩
      | F =>
          exact ⟨⟨.F, first, second⟩, hx⟩
  · rintro ⟨o, hx⟩
    cases o with
    | mk label first second =>
      cases label with
      | A =>
          change x ∈ (TileTranslation (TileCellComplement (P 0 true) O)
            ((first : GaussianInt) * u + (second : GaussianInt) * v)).cells at hx
          rcases Finset.mem_image.mp hx with ⟨y, hy, hxy⟩
          refine ⟨⟨.A, first, second⟩, ?_⟩
          change x ∈ (TileTranslation (P 0 true)
            ((first : GaussianInt) * u + (second : GaussianInt) * v)).cells
          apply Finset.mem_image.mpr
          exact ⟨y, (Finset.mem_sdiff.mp hy).1, hxy⟩
      | B =>
          exact ⟨⟨.B, first, second⟩, hx⟩
      | C =>
          exact ⟨⟨.C, first, second⟩, hx⟩
      | D =>
          exact ⟨⟨.D, first, second⟩, hx⟩
      | E =>
          exact ⟨⟨.E, first, second⟩, hx⟩
      | F =>
          exact ⟨⟨.F, first, second⟩, hx⟩

end ApollonianSuperharmonic

end
