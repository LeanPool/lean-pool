/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maxence Faldor, Moritz Firsching
-/
module

public import Mathlib.Data.Nat.Prime.Basic

/-!
# Goldbach's conjecture

The arithmetic proposition used by the Goldbach machine semantics.
-/

@[expose] public section

namespace ConjectureMachines

/-- Every even natural number greater than two is the sum of two primes. -/
def GoldbachConjecture : Prop :=
  ∀ n : ℕ, 2 < n → Even n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q

end ConjectureMachines
