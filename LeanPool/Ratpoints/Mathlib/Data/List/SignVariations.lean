/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.List.SignVariations

/-!
# The sign variations of a sequence of nonzero signs

A candidate for `Mathlib.Data.List.SignVariations`: for a sequence `s 0, …, s k` of integer signs
`±1`, the number of neighbours that differ is its number of sign variations
(`List.countP_ne_eq_signVariations`).

## Main statements

* `List.countP_ne_eq_signVariations`: the sign variations of a sequence of nonzero signs.
-/

@[expose] public section

namespace List

/-- The number of neighbours that differ in a sequence of nonzero signs is its number of sign
variations. -/
theorem countP_ne_eq_signVariations {s : ℕ → ℤ} {k : ℕ} (hs : ∀ n ≤ k, s n = -1 ∨ s n = 1) :
    (range k).countP (fun n ↦ s n != s (n + 1)) = ((range (k + 1)).map s).signVariations := by
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
    have ih' := ih (s := fun n ↦ s (n + 1)) fun n hn ↦ hs (n + 1) (by lia)
    have hR (t : ℕ → ℤ) (m : ℕ) : (range (m + 1)).map t =
        t 0 :: (range m).map fun n ↦ t (n + 1) := by
      rw [range_succ_eq_map, map_cons, map_map]; rfl
    have hL : (range (k + 1)).countP (fun n ↦ s n != s (n + 1)) =
        (range k).countP (fun n ↦ s (n + 1) != s (n + 1 + 1)) + if s 0 != s 1 then 1 else 0 := by
      rw [range_succ_eq_map, countP_cons, countP_map]; rfl
    rw [hL, ih', hR s (k + 1), hR (fun n ↦ s (n + 1)) k, signVariations_cons_cons_of_ne_zero]
    · rcases hs 0 (by lia) with h0 | h0 <;> rcases hs 1 (by lia) with h1 | h1 <;> simp [h0, h1]
    · rcases hs 0 (by lia) with h0 | h0 <;> simp [h0]
    · rcases hs 1 (by lia) with h1 | h1 <;> simp [h1]

end List

end
