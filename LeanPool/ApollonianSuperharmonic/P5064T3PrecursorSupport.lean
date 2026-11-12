/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

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
  have shift (n : Nat) (hn : 0 < n) (a b : Int) :
      FootprintVertices (TileTranslation (FordTile n) ⟨a, b⟩) =
        {z | a ≤ z.re ∧ z.re ≤ a + (n : Int) ∧
          b ≤ z.im ∧ z.im ≤ b + (n : Int)} := by
    rw [(TileTranslationFormulas _ _).2.2.2.2.2.1,
      (P4062T1CanonicalSupport n hn).1]
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      change 0 ≤ w.re ∧ w.re ≤ (n : Int) ∧
        0 ≤ w.im ∧ w.im ≤ (n : Int) at hw
      simp only [Set.mem_ofPred_eq, GaussianTranslation, Zsqrtd.re_add,
        Zsqrtd.im_add]
      omega
    · intro hz
      refine ⟨z - ⟨a, b⟩, ?_, ?_⟩
      · change 0 ≤ (z - ⟨a, b⟩).re ∧ (z - ⟨a, b⟩).re ≤ (n : Int) ∧
          0 ≤ (z - ⟨a, b⟩).im ∧ (z - ⟨a, b⟩).im ≤ (n : Int)
        simp only [Zsqrtd.re_sub, Zsqrtd.im_sub]
        change a ≤ z.re ∧ z.re ≤ a + (n : Int) ∧
          b ≤ z.im ∧ z.im ≤ b + (n : Int) at hz
        omega
      · simp [GaussianTranslation]
  have root := (P4062T1CanonicalSupport r (by omega)).1
  change FootprintVertices (FordTile r) =
    {z | 0 ≤ z.re ∧ z.re ≤ (r : Int) ∧ 0 ≤ z.im ∧ z.im ≤ (r : Int)} at root
  change FootprintVertices (FordTile r) ∩
      FootprintVertices (TileTranslation (FordTile r) ⟨(s : Int), (s : Int)⟩) = _ ∧
    FootprintVertices (FordTile r) ∩
      FootprintVertices (TileTranslation (FordTile r) ⟨(s : Int), (s : Int)⟩) =
    FootprintVertices (TileTranslation (FordTile (r - s)) ⟨(s : Int), (s : Int)⟩)
  rw [root, shift r (by omega) (s : Int) (s : Int),
    shift (r - s) (by omega) (s : Int) (s : Int)]
  constructor <;> ext z <;> simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] <;> omega

end ApollonianSuperharmonic

end
