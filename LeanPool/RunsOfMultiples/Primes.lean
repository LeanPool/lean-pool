/-
Copyright (c) 2026 Jason Hoelscher-Obermaier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hoelscher-Obermaier, Claude Opus 5.5
-/
module

-- Adapted for Lean Pool: module visibility, imports, and proof organization.

public import LeanPool.RunsOfMultiples.Upper
public import LeanPool.RunsOfMultiples.PrimeEstimates

/-!
# The unconditional upper bound

The Chebyshev estimates discharge every field of the prime-counting input.
-/

@[expose] public section

open Finset Real

namespace RunsOfMultiples

/-- The prime-number input for the upper bound, with `K = 4`. -/
theorem primeInput : ∃ C₁ q₀, PrimeInput 4 (log 2 / 2) C₁ q₀ := by
  obtain ⟨C₁, hC₁, hθ⟩ := theta_lower
  obtain ⟨q₀, hq₀⟩ := many_primes
  exact ⟨C₁, q₀, {
    K_pos := by norm_num
    c₁_pos := by have := log_pos (one_lt_two : (1 : ℝ) < 2); positivity
    C₁_nonneg := hC₁
    theta := fun m => by rw [sum_primesUpTo_eq_theta]; exact hθ m
    gap := hq₀ }⟩

end RunsOfMultiples

namespace RunsOfMultiples

/-- **Upper bound.** `∑_{a ∈ S} k(a) = O(n log n log log n)` for sets `S` of `n` positive
integers. -/
theorem upper_bound : ∃ C : ℝ, ∃ N : ℕ, ∀ S : Finset ℕ, (∀ a ∈ S, 0 < a) → N ≤ S.card →
    ((∑ a ∈ S, kVal S a : ℕ) : ℝ) ≤
      C * S.card * Real.log S.card * Real.log (Real.log S.card) := by
  obtain ⟨C₁, q₀, h⟩ := primeInput
  exact upper_of_primeInput h

end RunsOfMultiples
