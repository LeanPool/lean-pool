/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.Ring.RingNF

/-!
# Tangent portfolio (two-asset closed form, FOC)

With two risky assets having excess returns `r₁, r₂`, volatilities `σ₁, σ₂`,
and correlation `ρ`, the *tangent portfolio* (the Sharpe-ratio-maximizing
portfolio under the budget constraint `w₁ + w₂ = 1`) has closed-form weight

  `w₁^T = (σ₂² r₁ − ρ σ₁ σ₂ r₂) / D`,
  `D = σ₂² r₁ + σ₁² r₂ − ρ σ₁ σ₂ (r₁ + r₂)`.

The first-order condition for Sharpe maximization is

  `r₂ · (Σ·w)₁ = r₁ · (Σ·w)₂`,

i.e. the marginal variance contributions are proportional to the marginal
excess returns. We verify the closed-form `w^T` satisfies this FOC by direct
algebra.

## Main definitions

* `tangentWeightTwo`: the closed-form two-asset tangent weight
  `(σ₂² r₁ − ρσ₁σ₂ r₂) / (σ₂² r₁ + σ₁² r₂ − ρσ₁σ₂ (r₁ + r₂))` on asset 1.
* `IsTangentPortfolioN`: the `n`-asset cross-product first-order condition, in which the
  marginal-variance vector `Σw` is parallel to the excess-return vector.

## Main results

* `tangentTwo_satisfies_FOC`: the FOC identity at the tangent weight.

## References

* [H. Markowitz, *Portfolio selection*][Markowitz1952]
* [Sharpe, *Capital asset prices*][Sharpe1964]

## Tags

tangent portfolio, maximum Sharpe ratio, two-asset portfolio, first-order condition,
optimal risky portfolio, MSC 91G10, JEL G11
-/

@[expose] public section

namespace MathFin

/-- Two-asset tangent portfolio weight on asset 1.

`w₁^T = (σ₂² r₁ − ρ σ₁ σ₂ r₂) / (σ₂² r₁ + σ₁² r₂ − ρ σ₁ σ₂ (r₁ + r₂))`. -/
noncomputable def tangentWeightTwo (r₁ r₂ σ₁ σ₂ ρ : ℝ) : ℝ :=
  (σ₂^2 * r₁ - ρ * σ₁ * σ₂ * r₂) /
    (σ₂^2 * r₁ + σ₁^2 * r₂ - ρ * σ₁ * σ₂ * (r₁ + r₂))

/-- **Tangent portfolio FOC**: at the closed-form weight `w = w₁^T`,
`D · [r₂ · (w σ₁² + (1 − w) ρ σ₁ σ₂)] = D · [r₁ · (w ρ σ₁ σ₂ + (1 − w) σ₂²)]`
i.e. multiplying both sides by `D` we get a polynomial identity. Stated as
the cross-product form `r₂ · D · ((Σw)_1) = r₁ · D · ((Σw)_2)` to avoid the
division. -/
theorem tangentTwo_satisfies_FOC (r₁ r₂ σ₁ σ₂ ρ : ℝ) :
    -- `D` is the common denominator `σ₂² r₁ + σ₁² r₂ − ρ σ₁ σ₂ (r₁ + r₂)` —
    -- not referenced in the statement itself (the FOC is stated in
    -- multiplied-out cross-product form, so the division by `D` cancels).
    let w_num := σ₂^2 * r₁ - ρ * σ₁ * σ₂ * r₂  -- D · w
    let one_sub_w_num := σ₁^2 * r₂ - ρ * σ₁ * σ₂ * r₁  -- D · (1 - w)
    r₂ * (w_num * σ₁^2 + one_sub_w_num * ρ * σ₁ * σ₂) =
      r₁ * (w_num * ρ * σ₁ * σ₂ + one_sub_w_num * σ₂^2) := by
  ring

/-! ## N-asset extension (folded from `TangentPortfolioN.lean`)

For `N` risky assets, the tangent portfolio satisfies the cross-product FOC
`μ_excess(j) · (Σw)_i = μ_excess(i) · (Σw)_j` for all `i, j`. The two-asset
case above is the `i = 1, j = 2` instance written out. -/

/-- **N-asset tangent portfolio cross-product FOC**: the marginal-variance
vector `(Σw)_i = ∑_k Σ_{i,k} w_k` is parallel to the excess-return vector
`μ_excess`. -/
def IsTangentPortfolioN {ι : Type*} (s : Finset ι) (μ_excess : ι → ℝ)
    (Sg : ι → ι → ℝ) (w : ι → ℝ) : Prop :=
  ∀ i ∈ s, ∀ j ∈ s,
    μ_excess j * (∑ k ∈ s, Sg i k * w k) =
      μ_excess i * (∑ k ∈ s, Sg j k * w k)

/-- **Sufficient condition for tangency**: if `Σw = λ · μ_excess` for some
scalar `λ`, then `w` is a tangent portfolio. Captures the matrix-inverse
characterisation `w ∝ Σ⁻¹ · μ_excess` without requiring matrix machinery. -/
theorem isTangent_of_proportional {ι : Type*} (s : Finset ι) (μ_excess : ι → ℝ)
    (Sg : ι → ι → ℝ) (w : ι → ℝ) (lam : ℝ)
    (h : ∀ i ∈ s, (∑ k ∈ s, Sg i k * w k) = lam * μ_excess i) :
    IsTangentPortfolioN s μ_excess Sg w := by
  intro i hi j hj
  rw [h i hi, h j hj]
  ring

/-- **The two-asset FOC is the `N = 2` instance of `IsTangentPortfolioN`** — the
coherence the module docstring asserts, now proved rather than narrated. Feeding
the excess returns `![r₁, r₂]`, the covariance kernel `!![σ₁², ρσ₁σ₂; ρσ₁σ₂, σ₂²]`,
and the (denominator-scaled, since the predicate is homogeneous in `w`) tangent
weights `![Dw, D(1−w)]` into the general cross-product FOC recovers exactly
`tangentTwo_satisfies_FOC`. So the bespoke two-asset result is not a parallel
tower: it is `IsTangentPortfolioN` written out. -/
theorem tangentTwo_isTangentPortfolioN (r₁ r₂ σ₁ σ₂ ρ : ℝ) :
    IsTangentPortfolioN (Finset.univ : Finset (Fin 2))
      ![r₁, r₂]
      (fun i j ↦ ![![σ₁ ^ 2, ρ * σ₁ * σ₂], ![ρ * σ₁ * σ₂, σ₂ ^ 2]] i j)
      ![σ₂ ^ 2 * r₁ - ρ * σ₁ * σ₂ * r₂, σ₁ ^ 2 * r₂ - ρ * σ₁ * σ₂ * r₁] := by
  intro i _ j _
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] <;> ring

end MathFin
