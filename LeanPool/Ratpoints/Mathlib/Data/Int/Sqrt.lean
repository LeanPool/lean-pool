/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.Int.Sqrt

/-!
# The square test of `Int.sqrt` through the natural numbers

A candidate for `Mathlib.Data.Int.Sqrt`: `Int.sqrt v` squares to `v` exactly when `v ≥ 0` and the
square root of the natural number `v.toNat` squares to it (`Int.sqrt_mul_self_eq_iff`), the test
that a program on natural numbers makes; `Int.exists_mul_self` turns the left side into
`∃ n, n * n = v`.

## Main statements

* `Int.sqrt_mul_self_eq_iff`: `sqrt v * sqrt v = v` exactly when `0 ≤ v` and
  `v.toNat.sqrt * v.toNat.sqrt = v.toNat`.
-/

@[expose] public section

namespace Int

theorem sqrt_mul_self_eq_iff (v : ℤ) :
    sqrt v * sqrt v = v ↔ 0 ≤ v ∧ v.toNat.sqrt * v.toNat.sqrt = v.toNat := by
  simp only [sqrt]
  exact ⟨fun h ↦ ⟨h ▸ Int.mul_nonneg (natCast_nonneg _) (natCast_nonneg _), by lia⟩,
    fun ⟨hv, h⟩ ↦ by rw [← natCast_mul, h, toNat_of_nonneg hv]⟩

end Int

end
