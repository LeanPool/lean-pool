/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Basic.Real.Basic

-- pointers: MathFin/Insurance/Insurance.lean
-- main-module: MathFin/Insurance/ActuarialInsurance.lean
-- benchmark: benchmarks/mathematical_finance.json
-- benchmark-id: mf-insurance-premium-principles
-- source-issue: 85
-- new-defs: expectedValuePremium, variancePremium, stdDevPremium

/-!
# Loaded premium principles

Classical loaded premium principles — expected-value `(1 + θ)·μ`, variance
`μ + α·σ²`, standard-deviation `μ + β·σ` — and their nonnegative-loading
bound: each principle prices at or above the pure premium `μ`, the mean loss.
The principles take the mean `μ`, the variance `σ²` and the standard deviation
`σ` as numbers. For a random loss `X`, `stdDevPrinciple` of
`Insurance/StandardDeviationPrinciple.lean` is `stdDevPremium` at the mean and
standard deviation of `X`.

## Main definitions

* `expectedValuePremium`: the expected-value principle `(1 + θ) · μ` with loading `θ`.
* `variancePremium`: the variance principle `μ + α · σ²` with loading `α` on the variance.
* `stdDevPremium`: the standard-deviation principle `μ + β · σ` with loading `β`.

## Main results

* `expectedValuePremium_ge_mean`: for `0 ≤ θ` and `0 ≤ μ`, the expected-value premium is at
  least `μ`.
* `variancePremium_ge_mean`: for `0 ≤ α` and `0 ≤ σ²`, the variance premium is at least `μ`.
* `stdDevPremium_ge_mean`: for `0 ≤ β` and `0 ≤ σ`, the standard-deviation premium is at least `μ`.

## Tags

premium principle, expected value principle, variance principle, standard deviation principle,
pure premium, loading, MSC 91G05, JEL G22
-/


@[expose] public section

namespace MathFin

/-- Expected-value premium principle with loading `θ`: `(1 + θ) · μ`. -/
def expectedValuePremium (θ μ : ℝ) : ℝ := (1 + θ) * μ

/-- Variance premium principle with loading `α` on the variance `σ²`:
`μ + α · σ²`. -/
def variancePremium (α μ σ2 : ℝ) : ℝ := μ + α * σ2

/-- Standard-deviation premium principle with loading `β`: `μ + β · σ`. -/
def stdDevPremium (β μ σ : ℝ) : ℝ := μ + β * σ

/-- A nonnegative loading prices at or above the mean: expected-value principle. -/
theorem expectedValuePremium_ge_mean {θ μ : ℝ} (hθ : 0 ≤ θ) (hμ : 0 ≤ μ) :
    expectedValuePremium θ μ ≥ μ :=
  le_mul_of_one_le_left hμ (le_add_of_nonneg_right hθ)

/-- A nonnegative loading prices at or above the mean: variance principle. -/
theorem variancePremium_ge_mean {α σ2 : ℝ} (μ : ℝ) (hα : 0 ≤ α) (hσ2 : 0 ≤ σ2) :
    variancePremium α μ σ2 ≥ μ :=
  le_add_of_nonneg_right (mul_nonneg hα hσ2)

/-- A nonnegative loading prices at or above the mean: standard-deviation
principle. -/
theorem stdDevPremium_ge_mean {β σ : ℝ} (μ : ℝ) (hβ : 0 ≤ β) (hσ : 0 ≤ σ) :
    stdDevPremium β μ σ ≥ μ :=
  le_add_of_nonneg_right (mul_nonneg hβ hσ)

/-- All three classical premium principles with nonnegative loadings price at
or above the pure premium. -/
theorem premium_ge_mean (μ σ2 σ θ α β : ℝ) (hμ : 0 ≤ μ) (hσ2 : 0 ≤ σ2)
    (hσ : 0 ≤ σ) (hθ : 0 ≤ θ) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    expectedValuePremium θ μ ≥ μ ∧ variancePremium α μ σ2 ≥ μ ∧
      stdDevPremium β μ σ ≥ μ :=
  ⟨expectedValuePremium_ge_mean hθ hμ, variancePremium_ge_mean μ hα hσ2,
    stdDevPremium_ge_mean μ hβ hσ⟩

end MathFin
