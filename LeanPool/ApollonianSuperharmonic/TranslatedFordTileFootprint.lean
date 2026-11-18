/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4062T1CanonicalSupport
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas

/-!
# Footprints of translated canonical squares

Adapted from Wesley Pegden's Apache-2.0 Trellis formalization.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/-- Translating a canonical Ford square translates both integer coordinate intervals. -/
theorem translatedFordTileFootprint (n : ℕ) (hn : 0 < n) (a b : ℤ) :
    FootprintVertices (TileTranslation (FordTile n) ⟨a, b⟩) =
      {z | a ≤ z.re ∧ z.re ≤ a + (n : ℤ) ∧ b ≤ z.im ∧ z.im ≤ b + (n : ℤ)} := by
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

end ApollonianSuperharmonic

end
