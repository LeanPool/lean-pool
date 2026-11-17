/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import Mathlib.Algebra.Order.GroupWithZero.Finset

/-!
# Additions to the ordered-group-with-zero API

A single Mathlib gap: left multiplication distributes over `Finset.sup`
(`Finset.mul₀_sup`). Mathlib has the `Finset.sup'` form (`Finset.mul₀_sup'`) and the division
form (`Finset.sup_div₀`) but not this one; the proof is the `sup'` form plus the empty case.
-/

@[expose] public section

/-- Left multiplication distributes over `Finset.sup` in a linearly ordered commutative group
with zero — the `Finset.sup`-level companion of `Finset.mul₀_sup'`. -/
theorem Finset.mul₀_sup {ι G₀ : Type*} [LinearOrderedCommGroupWithZero G₀] (a : G₀)
    (s : Finset ι) (f : ι → G₀) : a * s.sup f = s.sup fun i ↦ a * f i := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp [bot_eq_zero]
  · rw [← Finset.sup'_eq_sup hs, ← Finset.sup'_eq_sup hs, Finset.mul₀_sup' zero_le]

end
