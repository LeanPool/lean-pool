/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

module

public import LeanPool.IwaniecLinearSieve.Jacobsthal.Reduction
import LeanPool.IwaniecLinearSieve.PrimeSums.NthPrime
import LeanPool.IwaniecLinearSieve.PrimeSums.Product

/-!
# Jacobsthal's problem ([I78])

Iwaniec's application of the linear sieve: if `m` consecutive integers are each divisible by one
of `r ≥ 2` given primes, then `m ≪ (r log r)²`. The shifted sieve ([I78, Lemma 1],
`Jacobsthal/ShiftedSieve.lean`) transfers the Rosser weights for the first `r` primes to any `r`
primes; `Jacobsthal/Reduction.lean` combines it with `linearSieveEstimate`.

This port preserves the dependency closure of the corollary. The upstream repository also
formalizes other results of [I78], which are outside this import's scope.

The sieve definitions, statements and proofs were produced by AI agents under Jason Davies's
supervision. The vendored strong PNT proofs come from PrimeNumberTheoremAnd and its contributors;
their upstream revision is recorded in the project card and each vendor module.
-/

@[expose] public section

namespace IwaniecLinearSieve

/-- **Iwaniec's theorem** ([I78, Corollary]): if `m` consecutive integers are each divisible by
one of `r ≥ 2` given primes, then `m ≪ (r log r)²`. -/
theorem iwaniecBound :
    ∃ C : ℝ, ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → 2 ≤ S.card →
      ∀ (x : ℤ) (m : ℕ), (∀ k < m, ∃ p ∈ S, (p : ℤ) ∣ x + k) →
        (m : ℝ) ≤ C * ((S.card : ℝ) * Real.log S.card) ^ 2 :=
  iwaniecBound_of_estimates linearSieveEstimate R_lower nth_prime_le

end IwaniecLinearSieve
