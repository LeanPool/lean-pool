/-
Copyright (c) 2026 Jason Hoelscher-Obermaier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hoelscher-Obermaier, Claude Opus 5.5
-/
module

-- Adapted for Lean Pool: module visibility, imports, and proof organization.

public import LeanPool.RunsOfMultiples.Defs
public import Mathlib.Data.Nat.Prime.Defs

/-!
# The compression proof: shared definitions

The compression proof (`docs/first-missing-multiple.pdf`) compresses `S` to a set `T` with the
same cardinality and no fewer runs (`|A S t| ≤ |A T t|` for all `t`) that is
* (i) closed under divisors (`DivClosed`), and
* (ii) closed under replacing a prime factor `q` by a smaller prime `p` (`ShiftClosed`).
-/

@[expose] public section

namespace RunsOfMultiples

/-- (i): every divisor of an element of `T` belongs to `T`. -/
def DivClosed (T : Finset ℕ) : Prop := ∀ a ∈ T, ∀ d, d ∣ a → d ∈ T

/-- (ii): if `a ∈ T`, `q ∣ a` and `p < q` are primes, then `a / q * p ∈ T`. -/
def ShiftClosed (T : Finset ℕ) : Prop :=
  ∀ a ∈ T, ∀ p q : ℕ, p.Prime → q.Prime → p < q → q ∣ a → a / q * p ∈ T

end RunsOfMultiples
