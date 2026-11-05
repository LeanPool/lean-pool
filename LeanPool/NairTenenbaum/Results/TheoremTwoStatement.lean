/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Polynomials.PolynomialSystem
public import Mathlib.Data.Nat.MaxPrimeFac

/-! # Statement of Theorem 2

This file defines the target proposition; it does not assert a proof.
The polynomial is explicitly nonconstant. The integer `k` is fixed before
choosing the threshold, as in the proof in the paper. No restriction on
fixed prime divisors is imposed.
-/

@[expose] public section

namespace NairTenenbaum

open Polynomial

/-- The product of the polynomial values in the interval of Theorem 2. -/
noncomputable def polynomialValueProduct (Q : ℤ[X]) (x y : ℝ) : ℕ :=
  ∏ n ∈ shortInterval x y, (Q.eval (n : ℤ)).natAbs

/-- The greatest prime factor of the polynomial-value product. -/
noncomputable def polynomialGreatestPrimeFactor (Q : ℤ[X]) (x y : ℝ) : ℕ :=
  Nat.maxPrimeFac (polynomialValueProduct Q x y)

/-- Theorem 2 with positive degree and the fixed divisor-window parameter. -/
def TheoremTwo : Prop :=
  ∀ Q : ℤ[X], Irreducible Q → 0 < Q.natDegree →
    ∀ k : ℕ, Q.natDegree < k → ∀ α : ℝ, α < 2 - Real.log 4 →
      ∃ x₀ : ℝ, 1 < x₀ ∧ ∀ x : ℝ, x₀ < x →
        let y : ℝ := x ^ ((Q.natDegree : ℝ) / k)
        y * Real.exp ((Real.log x) ^ α) < (polynomialGreatestPrimeFactor Q x y : ℝ)

end NairTenenbaum
