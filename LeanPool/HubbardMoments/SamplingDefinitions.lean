/-
Copyright (c) 2026 Daniel Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Souza
-/
module

-- Adapted for Lean Pool.

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Card
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Factorial.Basic

/-! # Moments of sampling without replacement -/

@[expose] public section

namespace HubbardMoments

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Moments of sampling without replacement.** The `ℓ`-th moment of the sum of `k` values
drawn without replacement from the population `ε`: the average of `(∑_{i ∈ K} ε_i)^ℓ` over
the `k`-subsets `K` of `V`. For `k` non-interacting fermions of one spin species with
single-particle energies `ε`, the many-body energies are exactly these sums (one Slater
determinant per `K`), so this is the `μ_ℓ` of the paper at `U = 0`. -/
noncomputable def sampleMoment (ε : V → ℝ) (k ℓ : ℕ) : ℝ :=
  (∑ K ∈ powersetCard k univ, (∑ i ∈ K, ε i) ^ ℓ) / (Fintype.card V).choose k

/-- `p_m = k(k-1)⋯(k-m+1) / (N(N-1)⋯(N-m+1))`: the probability that `m` given distinct labels
are all among `k` labels drawn without replacement from `N`. It is `0` for `m > k`. -/
noncomputable def inclusionProb (N k m : ℕ) : ℝ := (k.descFactorial m : ℝ) / N.descFactorial m

end HubbardMoments
