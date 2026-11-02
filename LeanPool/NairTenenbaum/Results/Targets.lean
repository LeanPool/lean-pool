/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Polynomials.PolynomialSystem

/-! # Statement of the main short-sum estimate

This module records the proposition and the uniformity of its constants.
`LeanPool.NairTenenbaum.Results.TheoremOne` proves it as `NairTenenbaum.theoremOne`;
importing this statement module alone does not import that proof. The scope is recorded in
README.md.
-/

@[expose] public section

namespace NairTenenbaum

/-- Theorem 1, equation (18). `c₀` is independent of the polynomial coefficients
and discriminant. The implicit constant depends on `D` but not on the remaining
polynomial data or on the arithmetic function. Parameters preceding `∃` may
influence both constants. -/
def TheoremOne : Prop :=
  ∀ (k r g : ℕ), 0 < k → 0 < r → 0 < g →
  ∀ (A B ε δ : ℝ), 1 ≤ A → 1 ≤ B → 0 < ε → ε < 1 / (8 * (g : ℝ) ^ 2) →
    0 < δ → δ ≤ 1 →
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ C : ℕ → ℝ, (∀ D, 0 < C D) ∧
      ∀ (P : PolynomialSystem k r), P.total.natDegree = g →
        ∀ (F : ArithmeticMap k), Admissible A B (ε * δ / 3) F →
          ∀ (x y : ℝ), c₀ * (polynomialHeight P.total : ℝ) ^ δ < x →
            x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y → y ≤ x →
            shortSum P.Q F x y ≤ C P.badDiscriminant * mainTerm P F x y

end NairTenenbaum
