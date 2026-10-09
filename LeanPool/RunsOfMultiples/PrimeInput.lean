/-
Copyright (c) 2026 Jason Hoelscher-Obermaier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hoelscher-Obermaier, Claude Opus 5.5
-/
module

-- Adapted for Lean Pool: module visibility, imports, and proof organization.

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Prime-counting hypotheses for runs of multiples

Separating the numerical prime input lets the entropy and Chebyshev arguments compile independently.
-/

@[expose] public section

open Finset Real

namespace RunsOfMultiples

/-- The primes `≤ m`. -/
def primesUpTo (m : ℕ) : Finset ℕ := (range (m + 1)).filter Nat.Prime

/-- Prime-number input for the upper bound. -/
structure PrimeInput (K : ℕ) (c₁ C₁ : ℝ) (q₀ : ℕ) : Prop where
  K_pos : 0 < K
  c₁_pos : 0 < c₁
  C₁_nonneg : 0 ≤ C₁
  theta : ∀ m : ℕ, c₁ * m - C₁ ≤ ∑ p ∈ primesUpTo m, log p
  gap : ∀ q : ℕ, q₀ ≤ q →
    (q : ℝ) ^ ((3 : ℝ) / 4) ≤ (((Ioc q (K * q)).filter Nat.Prime).card : ℝ)

end RunsOfMultiples
