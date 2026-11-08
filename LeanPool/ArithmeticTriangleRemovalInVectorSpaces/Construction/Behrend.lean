/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Combinatorics.Additive.AP.Three.Defs
import Mathlib.Combinatorics.Additive.AP.Three.Behrend

/-!
# Large sets without arithmetic progressions in `ZMod P`

Behrend's construction, `Behrend.roth_lower_bound` in Mathlib, gives a subset of
`range ((P + 1) / 2)` without three-term arithmetic progressions and with at least
`P / 2 * exp (-4 * √(log P))` elements. Its image in `ZMod P` has no three-term arithmetic
progressions either, since sums of two of its elements do not wrap around.

## Main statements

* `ArithmeticTriangleRemovalInVectorSpaces.exists_threeAPFree_le_card_zmod`: the set in `ZMod P`.
-/

public section

open Finset Real

namespace ArithmeticTriangleRemovalInVectorSpaces

/-- **Behrend's construction in `ZMod P`.** There is a set `S` in `ZMod P` without three-term
arithmetic progressions and with at least `P / 2 * exp (-4 * √(log P))` elements. -/
lemma exists_threeAPFree_le_card_zmod {P : ℕ} (hP : 0 < P) :
    ∃ S : Finset (ZMod P), ThreeAPFree (S : Set (ZMod P)) ∧ P / 2 * exp (-4 * √(log P)) ≤ #S := by
  obtain ⟨t, ht, hcard, hfree⟩ := rothNumberNat_spec ((P + 1) / 2)
  have hinj := CharP.natCast_injOn_Iio (ZMod P) P
  refine ⟨t.image Nat.cast, ?_, ?_⟩
  · push_cast
    refine hfree.image' (Nat.castAddMonoidHom (ZMod P)) (hinj.mono ?_)
    rintro _ ⟨a, ha, b, hb, rfl⟩
    grind [mem_range.1 (ht ha), mem_range.1 (ht hb)]
  · rw [card_image_of_injOn (hinj.mono fun a ha ↦ by grind [mem_range.1 (ht ha)]), hcard]
    grw [← Behrend.roth_lower_bound]
    rw [neg_mul, neg_mul]
    gcongr
    · rw [div_le_iff₀ two_pos]
      exact_mod_cast (by grind : P ≤ (P + 1) / 2 * 2)
    · exact_mod_cast (by grind : 0 < (P + 1) / 2)
    · exact_mod_cast (by grind : (P + 1) / 2 ≤ P)

end ArithmeticTriangleRemovalInVectorSpaces
