/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import Mathlib.Data.Set.Card

/-!
# Finiteness from a bound on `Set.encard`

`Set.Finite.of_encard_le_add` strengthens Mathlib's `Set.Finite.finite_of_encard_le` by allowing
a natural-number slack in the bound: a set whose `encard` is at most the `encard` of a finite set
plus a natural number is finite (Mathlib-bound).
-/

@[expose] public section

/-- A set whose `encard` is bounded by that of a finite set plus a natural number is finite. -/
theorem Set.Finite.of_encard_le_add {α β : Type*} {S : Set α} {T : Set β} (hT : T.Finite) {c : ℕ}
    (h : S.encard ≤ T.encard + c) : S.Finite :=
  Set.encard_lt_top_iff.mp
    (h.trans_lt (WithTop.add_lt_top.mpr ⟨hT.encard_lt_top, WithTop.coe_lt_top c⟩))

end
