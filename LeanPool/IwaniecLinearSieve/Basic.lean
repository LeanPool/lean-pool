/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

module

public import LeanPool.IwaniecLinearSieve.Definitions
import Mathlib.NumberTheory.Chebyshev

/-!
# Shared notation

Iwaniec works with primes below a real bound `z`. For `p : ℕ` and `z : ℝ` we have `p < z` iff
`p < ⌈z⌉₊`, so the primes below `z` are `Nat.primesBelow ⌈z⌉₊`.
-/

@[expose] public section

open Real

namespace IwaniecLinearSieve

/-- `P(z) = ∏_{p < z} p`. -/
noncomputable def primorialLT (z : ℝ) : ℕ := ∏ p ∈ primesLT z, p

/-- Iwaniec's `R(z) = ∏_{p < z} (1 - 1/p)` (his `R_k` with `k = 1`). -/
noncomputable def R (z : ℝ) : ℝ := ∏ p ∈ primesLT z, (1 - (p : ℝ)⁻¹)

theorem mem_primesLT {z : ℝ} {p : ℕ} : p ∈ primesLT z ↔ p.Prime ∧ (p : ℝ) < z := by
  simp [primesLT, Nat.mem_primesBelow, Nat.lt_ceil, and_comm]

theorem R_nonneg (z : ℝ) : 0 ≤ R z :=
  Finset.prod_nonneg fun p hp ↦ sub_nonneg.2 <| inv_le_one_of_one_le₀ <| by
    exact_mod_cast (mem_primesLT.1 hp).1.one_lt.le

theorem R_pos (z : ℝ) : 0 < R z :=
  Finset.prod_pos fun p hp ↦ sub_pos.2 <| inv_lt_one_of_one_lt₀ <| by
    exact_mod_cast (mem_primesLT.1 hp).1.one_lt

end IwaniecLinearSieve
