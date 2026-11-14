/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import Mathlib.RingTheory.WittVector.DiscreteValuationRing

/-!
# The characteristic of the Witt vectors

The Witt vectors of a field of characteristic `p` have characteristic zero. Mathlib has the
discrete-valuation-ring structure of `𝕎 k` but no `CharZero` instance.
-/

@[expose] public section

namespace WittVector

variable {p : ℕ} [Fact p.Prime]

/-- The Witt vectors of a field of characteristic `p` have characteristic zero:
`n = p^v·m` with `p ∤ m` has `p^v ≠ 0` (the uniformizer is irreducible) and `m ≠ 0` (its
residue is nonzero). -/
instance instCharZero {κ : Type*} [Field κ] [CharP κ p] : CharZero (WittVector p κ) := by
  have key : ∀ n : ℕ, (n : WittVector p κ) = 0 → n = 0 := by
    intro n h0
    by_contra hn0
    obtain ⟨v, m, hpm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 p
      (Fact.out : p.Prime).ne_one
    rw [Nat.cast_mul, Nat.cast_pow, mul_eq_zero] at h0
    rcases h0 with h | h
    · exact pow_ne_zero v (WittVector.irreducible p).ne_zero h
    · refine hpm ((CharP.cast_eq_zero_iff κ p m).mp ?_)
      rw [← map_natCast (WittVector.constantCoeff (p := p) (R := κ)), h, map_zero]
  have : CharP (WittVector p κ) 0 := ⟨fun n ↦ by
    rw [zero_dvd_iff]
    exact ⟨key n, fun h ↦ by simp [h]⟩⟩
  exact CharP.charP_to_charZero (WittVector p κ)

end WittVector

end
