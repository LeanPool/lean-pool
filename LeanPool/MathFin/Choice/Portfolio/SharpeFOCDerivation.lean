/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Choice.Portfolio.Markowitz
public import LeanPool.MathFin.Choice.Performance.Ratios
public import Mathlib.Algebra.Ring.IsFormallyReal

/-!
# Markowitz cross-product FOC derived from Sharpe-ratio maximization

The pre-existing `tangentTwo_satisfies_FOC` in `Choice.Portfolio.TangentPortfolio`
verifies that the closed-form weight `tangentWeightTwo` satisfies the
cross-product FOC `r₂ · (Σw)₁ = r₁ · (Σw)₂` by direct algebra (`ring`). It
does **not derive** that FOC from a maximization problem.

This file closes that gap. It

1. defines the two-asset Sharpe-ratio-squared
   `Sh²(w) = E(w)² / V(w)` where `E(w) = w r₁ + (1 − w) r₂`,
   `V(w) = w² σ₁² + (1 − w)² σ₂² + 2 w (1 − w) ρ σ₁ σ₂`;
2. proves `HasDerivAt` of `Sh²` with the textbook formula
   `Sh²'(w) = (2 E E' V − E² V') / V²`;
3. shows the numerator factors as
   `2 E E' V − E² V' = 2 E · (r₁ · (Σw)₂ − r₂ · (Σw)₁)`;
4. concludes that the critical points of `Sh²` (where `E ≠ 0`, `V > 0`)
   are precisely the points where the cross-product FOC holds.

## Why this is "first principles"

The existing infrastructure stops at "the closed form satisfies the FOC".
This file derives the FOC itself from a maximization problem — closing the
loop between the optimization-theoretic and algebraic perspectives.

## Main definitions

* `expectedReturnTwo`: the two-asset expected return `w r₁ + (1 − w) r₂`.
* `varianceTwo`: the two-asset variance as a function of the weight `w` on asset 1
  (`portfolioVarTwo` of `Choice/Portfolio/Markowitz.lean` with the weight as first argument).
* `marginalVarOne`, `marginalVarTwo`: the components `(Σw)₁`, `(Σw)₂` of the marginal variance.
* `sharpeSqTwo`: the squared Sharpe ratio `E(w)² / V(w)` as a function of `w`.

## Main results

* `sharpeSqTwo_eq_sharpeRatio_sq`: for `V(w) ≥ 0`, `Sh²(w)` is the squared `sharpeRatio` of the
  portfolio return (zero risk-free rate) at volatility `√V(w)`.
* `varianceTwo_eq_w_dot_Sigma_w`: `V = w · (Σw)₁ + (1 − w) · (Σw)₂` (the
  self-dot identity).
* `hasDerivAt_varianceTwo`: `V'(w) = 2 · ((Σw)₁ − (Σw)₂)`.
* `sharpeSqTwo_deriv_numerator_factored`: the derivative numerator
  factors through `r₁ (Σw)₂ − r₂ (Σw)₁`.
* `sharpeSqTwo_critical_iff_crossProduct_FOC`: critical-point
  characterisation (`E ≠ 0, V > 0` regime).

## References

* [H. Markowitz, *Portfolio selection*][Markowitz1952]
* [Sharpe, *Capital asset prices*][Sharpe1964]

## Tags

Sharpe ratio maximization, tangent portfolio, first-order condition, Markowitz,
maximum Sharpe portfolio, MSC 91G10, JEL G11
-/

@[expose] public section

namespace MathFin

/-- Two-asset expected excess return parameterised by weight `w` on asset 1
(with `1 − w` on asset 2). -/
noncomputable def expectedReturnTwo (w r₁ r₂ : ℝ) : ℝ := w * r₁ + (1 - w) * r₂

/-- Two-asset portfolio variance as a function of the weight `w`: the library's
`portfolioVarTwo` (`Choice/Portfolio/Markowitz.lean`) with the weight as first argument. -/
noncomputable def varianceTwo (w σ₁ σ₂ ρ : ℝ) : ℝ :=
  portfolioVarTwo σ₁ σ₂ ρ w

/-- Marginal variance contribution of asset 1: `(Σw)₁ = w σ₁² + (1−w) ρ σ₁ σ₂`. -/
noncomputable def marginalVarOne (w σ₁ σ₂ ρ : ℝ) : ℝ :=
  w * σ₁^2 + (1 - w) * ρ * σ₁ * σ₂

/-- Marginal variance contribution of asset 2: `(Σw)₂ = w ρ σ₁ σ₂ + (1−w) σ₂²`. -/
noncomputable def marginalVarTwo (w σ₁ σ₂ ρ : ℝ) : ℝ :=
  w * ρ * σ₁ * σ₂ + (1 - w) * σ₂^2

/-- Two-asset Sharpe-ratio squared as a function of weight `w`. -/
noncomputable def sharpeSqTwo (w r₁ r₂ σ₁ σ₂ ρ : ℝ) : ℝ :=
  (expectedReturnTwo w r₁ r₂)^2 / (varianceTwo w σ₁ σ₂ ρ)

/-- **The two-asset Sharpe ratio squared is the squared Sharpe ratio** of the portfolio return
with zero risk-free rate (`returns` are excess returns): `Sh²(w) = sharpeRatio E(w) 0 σ(w) ^ 2`,
with `σ(w) = √V(w)` the portfolio volatility. `V(w)` is the variance of `w R₁ + (1 − w) R₂`
(`portfolioVarTwo_eq_variance`, `Choice/Portfolio/MarkowitzLagrangian.lean`). -/
theorem sharpeSqTwo_eq_sharpeRatio_sq (w r₁ r₂ σ₁ σ₂ ρ : ℝ) (hV : 0 ≤ varianceTwo w σ₁ σ₂ ρ) :
    sharpeSqTwo w r₁ r₂ σ₁ σ₂ ρ
      = sharpeRatio (expectedReturnTwo w r₁ r₂) 0 (√(varianceTwo w σ₁ σ₂ ρ)) ^ 2 := by
  rw [sharpeSqTwo, sharpeRatio, sub_zero, div_pow, Real.sq_sqrt hV]

/-- **Self-dot identity for V**: `V(w) = w · (Σw)₁ + (1 − w) · (Σw)₂`. -/
lemma varianceTwo_eq_w_dot_Sigma_w (w σ₁ σ₂ ρ : ℝ) :
    varianceTwo w σ₁ σ₂ ρ =
      w * marginalVarOne w σ₁ σ₂ ρ + (1 - w) * marginalVarTwo w σ₁ σ₂ ρ := by
  unfold varianceTwo portfolioVarTwo marginalVarOne marginalVarTwo
  ring

/-- **Derivative of `E(w) = w r₁ + (1 − w) r₂`** is `r₁ − r₂`. -/
lemma hasDerivAt_expectedReturnTwo (w r₁ r₂ : ℝ) :
    HasDerivAt (fun w' ↦ expectedReturnTwo w' r₁ r₂) (r₁ - r₂) w := by
  unfold expectedReturnTwo
  have h1 : HasDerivAt (fun w' : ℝ ↦ w' * r₁) r₁ w := by
    simpa using (hasDerivAt_id w).mul_const r₁
  have h_sub : HasDerivAt (fun w' : ℝ ↦ (1 : ℝ) - w') (-1) w := by
    simpa using (hasDerivAt_id w).const_sub 1
  have h2 : HasDerivAt (fun w' : ℝ ↦ (1 - w') * r₂) (-r₂) w := by
    have := h_sub.mul_const r₂
    simpa using this
  have h := h1.add h2
  convert h using 1

/-- **Derivative of `V(w) = w² σ₁² + (1−w)² σ₂² + 2 w (1−w) ρ σ₁ σ₂`** is
`V'(w) = 2 · ((Σw)₁ − (Σw)₂)`. Proof: polynomial rewrite of `V` in the form
`A w² + B w + C`, then `(A w² + B w + C)' = 2 A w + B`. -/
lemma hasDerivAt_varianceTwo (w σ₁ σ₂ ρ : ℝ) :
    HasDerivAt (fun w' ↦ varianceTwo w' σ₁ σ₂ ρ)
               (2 * (marginalVarOne w σ₁ σ₂ ρ - marginalVarTwo w σ₁ σ₂ ρ)) w := by
  -- Rewrite V as A w² + B w + C
  have h_v_poly : (fun w' : ℝ ↦ varianceTwo w' σ₁ σ₂ ρ) =
      (fun w' ↦ (σ₁^2 + σ₂^2 - 2*ρ*σ₁*σ₂) * w'^2 +
                 (-2*σ₂^2 + 2*ρ*σ₁*σ₂) * w' + σ₂^2) := by
    funext w'
    unfold varianceTwo portfolioVarTwo
    ring
  rw [h_v_poly]
  have h_sq : HasDerivAt (fun w' : ℝ ↦ w'^2) (2*w) w := by
    have := hasDerivAt_pow 2 w
    convert this using 1; push_cast; ring
  have h_term1 := h_sq.const_mul (σ₁^2 + σ₂^2 - 2*ρ*σ₁*σ₂)
  have h_term2 := (hasDerivAt_id w).const_mul (-2*σ₂^2 + 2*ρ*σ₁*σ₂)
  have h_term3 : HasDerivAt (fun _ : ℝ ↦ (σ₂^2 : ℝ)) 0 w := hasDerivAt_const w _
  have h := (h_term1.add h_term2).add h_term3
  convert h using 1 <;> first | rfl | (unfold marginalVarOne marginalVarTwo; ring)

/-- **Derivative of `E²(w)`** is `2 E (r₁ − r₂)`. -/
lemma hasDerivAt_expectedReturnTwo_sq (w r₁ r₂ : ℝ) :
    HasDerivAt (fun w' ↦ (expectedReturnTwo w' r₁ r₂)^2)
               (2 * expectedReturnTwo w r₁ r₂ * (r₁ - r₂)) w := by
  have h := (hasDerivAt_expectedReturnTwo w r₁ r₂).pow 2
  convert h using 1; push_cast; ring

/-- **Derivative of `Sh²(w) = E²/V`**: textbook formula `Sh²'(w) = (2EE'V − E²V')/V²`. -/
theorem hasDerivAt_sharpeSqTwo (w r₁ r₂ σ₁ σ₂ ρ : ℝ)
    (hV : varianceTwo w σ₁ σ₂ ρ ≠ 0) :
    HasDerivAt (fun w' ↦ sharpeSqTwo w' r₁ r₂ σ₁ σ₂ ρ)
               ((2 * expectedReturnTwo w r₁ r₂ * (r₁ - r₂) *
                   varianceTwo w σ₁ σ₂ ρ -
                 (expectedReturnTwo w r₁ r₂)^2 *
                   (2 * (marginalVarOne w σ₁ σ₂ ρ - marginalVarTwo w σ₁ σ₂ ρ))) /
                (varianceTwo w σ₁ σ₂ ρ)^2) w := by
  unfold sharpeSqTwo
  exact (hasDerivAt_expectedReturnTwo_sq w r₁ r₂).div
        (hasDerivAt_varianceTwo w σ₁ σ₂ ρ) hV

/-- **Algebraic factorization of the Sh² derivative numerator**:

  `2 E E' V − E² V' = 2 E · (r₁ (Σw)₂ − r₂ (Σw)₁)`.

This factorization is the algebraic content of the cross-product FOC: setting
the numerator to zero (with `E ≠ 0`) reduces to `r₁ (Σw)₂ = r₂ (Σw)₁`.

The identity is proved by `ring` after unfolding all definitions; the
non-trivial cancellation is that `(r₁ − r₂) V − E ((Σw)₁ − (Σw)₂)` simplifies
exactly to `r₁ (Σw)₂ − r₂ (Σw)₁`. -/
theorem sharpeSqTwo_deriv_numerator_factored (w r₁ r₂ σ₁ σ₂ ρ : ℝ) :
    2 * expectedReturnTwo w r₁ r₂ * (r₁ - r₂) * varianceTwo w σ₁ σ₂ ρ -
        (expectedReturnTwo w r₁ r₂)^2 *
          (2 * (marginalVarOne w σ₁ σ₂ ρ - marginalVarTwo w σ₁ σ₂ ρ)) =
      2 * expectedReturnTwo w r₁ r₂ *
        (r₁ * marginalVarTwo w σ₁ σ₂ ρ - r₂ * marginalVarOne w σ₁ σ₂ ρ) := by
  unfold expectedReturnTwo varianceTwo portfolioVarTwo marginalVarOne marginalVarTwo
  ring

/-- **Critical-point characterisation**: in the `E ≠ 0`, `V > 0` regime, the
Sharpe-ratio squared has a critical point at `w` (i.e., `HasDerivAt Sh² 0 w`)
*if and only if* the cross-product FOC `r₂ (Σw)₁ = r₁ (Σw)₂` holds.

This is the first-principles derivation: the FOC arises as the
critical-point condition of a real maximization problem, not as a stated
algebraic identity. -/
theorem sharpeSqTwo_critical_iff_crossProduct_FOC
    (w r₁ r₂ σ₁ σ₂ ρ : ℝ) (hV : varianceTwo w σ₁ σ₂ ρ ≠ 0)
    (hE : expectedReturnTwo w r₁ r₂ ≠ 0) :
    HasDerivAt (fun w' ↦ sharpeSqTwo w' r₁ r₂ σ₁ σ₂ ρ) 0 w ↔
      r₂ * marginalVarOne w σ₁ σ₂ ρ = r₁ * marginalVarTwo w σ₁ σ₂ ρ := by
  -- (a) The derivative computed above is unique; if HasDerivAt f 0 w, then
  --     the computed expression equals 0.
  have h_deriv := hasDerivAt_sharpeSqTwo w r₁ r₂ σ₁ σ₂ ρ hV
  constructor
  · intro h_zero
    -- Uniqueness of HasDerivAt: both derivatives must agree
    have h_eq : (2 * expectedReturnTwo w r₁ r₂ * (r₁ - r₂) *
                   varianceTwo w σ₁ σ₂ ρ -
                 (expectedReturnTwo w r₁ r₂)^2 *
                   (2 * (marginalVarOne w σ₁ σ₂ ρ - marginalVarTwo w σ₁ σ₂ ρ))) /
                (varianceTwo w σ₁ σ₂ ρ)^2 = 0 := h_deriv.unique h_zero
    have hV_sq : (varianceTwo w σ₁ σ₂ ρ)^2 ≠ 0 := pow_ne_zero _ hV
    -- Division-by-nonzero is zero implies numerator is zero
    have h_num : 2 * expectedReturnTwo w r₁ r₂ * (r₁ - r₂) *
                   varianceTwo w σ₁ σ₂ ρ -
                 (expectedReturnTwo w r₁ r₂)^2 *
                   (2 * (marginalVarOne w σ₁ σ₂ ρ - marginalVarTwo w σ₁ σ₂ ρ)) = 0 :=
      (div_eq_zero_iff.mp h_eq).resolve_right hV_sq
    -- Apply the algebraic factorization
    rw [sharpeSqTwo_deriv_numerator_factored] at h_num
    -- 2 * E * (r₁·(Σw)₂ - r₂·(Σw)₁) = 0
    have : r₁ * marginalVarTwo w σ₁ σ₂ ρ - r₂ * marginalVarOne w σ₁ σ₂ ρ = 0 := by
      have h2E_ne : (2 * expectedReturnTwo w r₁ r₂) ≠ 0 := by
        simp [hE]
      have : (2 * expectedReturnTwo w r₁ r₂) *
              (r₁ * marginalVarTwo w σ₁ σ₂ ρ - r₂ * marginalVarOne w σ₁ σ₂ ρ) = 0 := h_num
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h h2E_ne
      · exact h
    linarith
  · intro h_foc
    -- r₂ (Σw)₁ = r₁ (Σw)₂ ⟹ derivative is 0
    -- Use the factorization: 2EE'V - E²V' = 2E(r₁(Σw)₂ - r₂(Σw)₁) = 2E·0 = 0
    have h_diff_zero : r₁ * marginalVarTwo w σ₁ σ₂ ρ -
                       r₂ * marginalVarOne w σ₁ σ₂ ρ = 0 := by linarith
    have h_num_zero : 2 * expectedReturnTwo w r₁ r₂ * (r₁ - r₂) *
                        varianceTwo w σ₁ σ₂ ρ -
                      (expectedReturnTwo w r₁ r₂)^2 *
                        (2 * (marginalVarOne w σ₁ σ₂ ρ - marginalVarTwo w σ₁ σ₂ ρ)) = 0 := by
      rw [sharpeSqTwo_deriv_numerator_factored]
      rw [h_diff_zero]; ring
    have h_zero_div : (2 * expectedReturnTwo w r₁ r₂ * (r₁ - r₂) *
                         varianceTwo w σ₁ σ₂ ρ -
                       (expectedReturnTwo w r₁ r₂)^2 *
                         (2 * (marginalVarOne w σ₁ σ₂ ρ - marginalVarTwo w σ₁ σ₂ ρ))) /
                      (varianceTwo w σ₁ σ₂ ρ)^2 = 0 := by
      rw [h_num_zero]; simp
    rw [← h_zero_div]
    exact h_deriv

end MathFin
