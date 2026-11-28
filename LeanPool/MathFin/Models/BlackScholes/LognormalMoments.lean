/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.BlackScholes.Call
public import LeanPool.MathFin.Models.BlackScholes.Forward

/-!
# Second moment and variance of the terminal asset price

Under `BSCallHyp` (risk-neutral lognormal model),

  `E_Q[S_T²] = S_0² · exp(2rT + σ²T)`,
  `Var_Q[S_T] = S_0² · exp(2rT) · (exp(σ²T) − 1)`.

The second-moment formula is `nthMoment_terminal 2 h` — the n=2 instance of
the general power-moment identity, which is itself an instance of the
affine-shifted standard-normal MGF. The variance follows from the second
moment minus the squared forward `E[S_T]² = S_0² · exp(2rT)`.

This file used to duplicate the MGF computation. Following the principle
"one theorem, many corollaries", we now delegate `secondMoment_terminal` to
`nthMoment_terminal` and only do the n=2 algebraic simplification here.

## Main results

* `secondMoment_terminal`: `E_Q[S_T²] = S_0² · exp(2rT + σ²T)`.
* `variance_terminal`: `Var_Q[S_T] = S_0² · exp(2rT) · (exp(σ²T) − 1)`.

## References

* [K. Bodie and Marcus, *Investments*][BodieKaneMarcus], Ch 21
* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], Ch 14.7

## Tags

lognormal distribution, second moment, variance of terminal price, geometric Brownian motion,
risk-neutral moments, MSC 60E05, MSC 91G20
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real

/-- **Second moment of the terminal asset price**: under `BSCallHyp`,
`E_Q[S_T²] = S_0² · exp(2 r T + σ² T)`.

Instance of `nthMoment_terminal` at `n = 2`: the general formula gives
`S_0^2 · exp(2·r·T + 2·1/2·σ²T) = S_0^2 · exp(2rT + σ²T)`. -/
theorem secondMoment_terminal
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r σ T : ℝ} {Z : Ω → ℝ}
    (h : BSCallHyp Q S_0 K r σ T Z) :
    ∫ ω, (bsTerminal S_0 r σ T (Z ω))^2 ∂Q =
      S_0^2 * Real.exp (2 * r * T + σ^2 * T) := by
  have h_general := nthMoment_terminal 2 h
  -- nthMoment_terminal at n=2 produces:
  --   ∫ ... = S_0^2 * exp((↑(2:ℕ))·r·T + (↑(2:ℕ))·((↑(2:ℕ))-1)/2 · σ²·T)
  -- which equals S_0^2 * exp(2·r·T + σ²·T) after pushing the cast and
  -- simplifying `2·(2-1)/2 = 1`.
  convert h_general using 3
  push_cast
  ring

/-- **Variance of the terminal asset price**: under `BSCallHyp`,
`Var_Q[S_T] = E_Q[S_T²] − (E_Q[S_T])² = S_0² · exp(2 r T) · (exp(σ² T) − 1)`.

Combines `secondMoment_terminal` with `expected_terminal_eq_forward`. -/
theorem variance_terminal
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r σ T : ℝ} {Z : Ω → ℝ}
    (h : BSCallHyp Q S_0 K r σ T Z) :
    ∫ ω, (bsTerminal S_0 r σ T (Z ω))^2 ∂Q -
      (∫ ω, bsTerminal S_0 r σ T (Z ω) ∂Q)^2 =
        S_0^2 * Real.exp (2 * r * T) * (Real.exp (σ^2 * T) - 1) := by
  rw [secondMoment_terminal h, expected_terminal_eq_forward h]
  have h_exp_sq : (Real.exp (r * T))^2 = Real.exp (2 * r * T) := by
    rw [pow_two, ← Real.exp_add]; congr 1; ring
  have h_sq_exp : (S_0 * Real.exp (r * T))^2 = S_0^2 * Real.exp (2 * r * T) := by
    rw [mul_pow, h_exp_sq]
  rw [h_sq_exp, Real.exp_add]; ring

end MathFin
