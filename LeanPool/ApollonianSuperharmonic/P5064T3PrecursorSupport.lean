/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.TranslatedFordTileFootprint

public import LeanPool.ApollonianSuperharmonic.P5064T3Rectangles
public import LeanPool.ApollonianSuperharmonic.P4062T1CanonicalSupport
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas

-- [TABLET NODE: P5064T3PrecursorSupport]

/-!
# P5064T3PrecursorSupport

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5064T3PrecursorSupport (r s : Nat) (hs : 0 < s) (hrs : s < r) :
    FootprintVertices (P5064T3Rectangles r s 0 true) ∩
        FootprintVertices (P5064T3Rectangles r s 0 false) =
      {z | (s : Int) ≤ z.re ∧ z.re ≤ (r : Int) ∧
        (s : Int) ≤ z.im ∧ z.im ≤ (r : Int)} ∧
    FootprintVertices (P5064T3Rectangles r s 0 true) ∩
        FootprintVertices (P5064T3Rectangles r s 0 false) =
      FootprintVertices (P5064T3Rectangles (r - s) s 0 false) := by
-- BODY
  have root := (P4062T1CanonicalSupport r (by omega)).1
  change FootprintVertices (FordTile r) =
    {z | 0 ≤ z.re ∧ z.re ≤ (r : Int) ∧ 0 ≤ z.im ∧ z.im ≤ (r : Int)} at root
  change FootprintVertices (FordTile r) ∩
      FootprintVertices (TileTranslation (FordTile r) ⟨(s : Int), (s : Int)⟩) = _ ∧
    FootprintVertices (FordTile r) ∩
      FootprintVertices (TileTranslation (FordTile r) ⟨(s : Int), (s : Int)⟩) =
    FootprintVertices (TileTranslation (FordTile (r - s)) ⟨(s : Int), (s : Int)⟩)
  rw [root, translatedFordTileFootprint r (by omega) (s : Int) (s : Int),
    translatedFordTileFootprint (r - s) (by omega) (s : Int) (s : Int)]
  constructor <;> ext z <;> simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] <;> omega

end ApollonianSuperharmonic

end
