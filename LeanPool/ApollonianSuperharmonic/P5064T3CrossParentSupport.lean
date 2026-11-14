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

-- [TABLET NODE: P5064T3CrossParentSupport]

/-!
# P5064T3CrossParentSupport

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5064T3CrossParentSupport (r s : Nat) (hs : 0 < s) (hrs : s < r) :
    FootprintVertices (P5064T3Rectangles r s 0 true) ∩
        FootprintVertices (P5064T3Rectangles r s 1 true) =
      {z | z.re = (r : Int) ∧ 0 ≤ z.im ∧ z.im ≤ (s : Int)} ∧
    FootprintVertices (P5064T3Rectangles r s 0 true) ∩
        FootprintVertices (P5064T3Rectangles r s 1 true) ⊆
      FootprintVertices (P5064T3Rectangles (r - s) s 1 true) ∩
        FootprintVertices (P5064T3Rectangles r s 1 true) := by
-- BODY
  have root := (P4062T1CanonicalSupport r (by omega)).1
  change FootprintVertices (FordTile r) =
    {z | 0 ≤ z.re ∧ z.re ≤ (r : Int) ∧ 0 ≤ z.im ∧ z.im ≤ (r : Int)} at root
  change FootprintVertices (FordTile r) ∩
      FootprintVertices (TileTranslation (FordTile s) ⟨(r : Int), 0⟩) = _ ∧
    FootprintVertices (FordTile r) ∩
      FootprintVertices (TileTranslation (FordTile s) ⟨(r : Int), 0⟩) ⊆
    FootprintVertices (TileTranslation (FordTile s) ⟨((r - s : Nat) : Int), 0⟩) ∩
      FootprintVertices (TileTranslation (FordTile s) ⟨(r : Int), 0⟩)
  rw [root, translatedFordTileFootprint s hs (r : Int) 0,
    translatedFordTileFootprint s hs ((r - s : Nat) : Int) 0]
  constructor
  · ext z
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    omega
  · intro z hz
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at hz ⊢
    omega

end ApollonianSuperharmonic

end
