/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Analysis.Complex.Exponential

/-!
# CDS fair spread under time-varying hazard (first-principles)

The pre-existing `Models/Credit/Credit.lean` derives the CDS fair spread
`c = h · (1 − R)` for *constant* hazard `h` via the `cds_leg_equality`
identity. The annuity factor cancels because both legs share it.

This file extends to *time-varying* hazard `h : ℝ → ℝ`. The cash-flow
balance is

  `c · annuity(T) = (1 − R) · losses(T)`,

where (with constant recovery `R` for simplicity)

  `annuity(T) = ∫_0^T S(s) · e^{−rs} ds`,
  `losses(T)  = ∫_0^T h(s) · S(s) · e^{−rs} ds`,

and `S(s) = exp(−∫_0^s h(u) du)` is the survival from `HazardCurve.lean`.
Under no arbitrage, the fair spread is `c* = (1 − R) · losses(T) /
annuity(T)`. No integral is evaluated — the balance is stated at the cash-
flow level.

The discrete piecewise-constant survival decomposition (multi-period
survival = exp of sum of hazard × duration) is a direct application of
`Real.exp_sum` and is recorded as `survival_product_eq_exp_sum` for the
finance-side narrative.

## Why this is "first principles"

The existing constant-hazard derivation specialises to a single rate `h`
for all time; this file gives the general cash-flow balance that holds for
any deterministic hazard curve.

## Main results

* `cdsFairSpread_TV_cash_flow_balance`: for a nonzero annuity, the balance equation
  `c · annuity = (1 − R) · losses` solved for the spread; the hazard enters only through the two
  legs (`Cox.cdsFairSpreadTV_balances` is the Cox-model instance).
* `survival_product_eq_exp_sum`: multi-period survival factorisation,
  i.e. `∏ exp(−h_i Δt_i) = exp(−∑ h_i Δt_i)` (a direct `Real.exp_sum`
  application stated in finance variables).

## Tags

credit default swap, CDS spread, hazard rate, protection leg, premium leg, fair spread,
survival probability, MSC 91G40, JEL G12
-/

@[expose] public section

namespace MathFin

open Real Finset

/-- **CDS time-varying fair-spread cash-flow balance**. With time-varying
hazard `h : ℝ → ℝ`, constant recovery `R`, and discount rate `r`, the
premium leg (spread `c` collected per unit notional, weighted by survival
and discount) balances the protection leg (`1 − R` paid at default,
weighted by default density `h(s) · S(s)` and discount) iff

  `c · annuity(T) = (1 − R) · losses(T)`.

For non-zero annuity, this is equivalent to the fair-spread formula
`c = (1 − R) · losses / annuity`. -/
theorem cdsFairSpread_TV_cash_flow_balance
    (c R annuity losses : ℝ) (h_annuity_ne : annuity ≠ 0) :
    c * annuity = (1 - R) * losses ↔ c = (1 - R) * losses / annuity := by
  rw [eq_div_iff h_annuity_ne]

/-- **Multi-period survival from per-period hazards**: with hazard `h_i` on
period `i` of duration `Δt_i`, the cumulative survival is

  `∏_i exp(-h_i · Δt_i) = exp(-∑_i h_i · Δt_i)`.

This is the discrete realisation of the continuous formula
`S(T) = exp(-∫_0^T h(u) du)` for step-constant `h`. -/
theorem survival_product_eq_exp_sum (n : ℕ) (h Δt : Fin n → ℝ) :
    (∏ i, Real.exp (-(h i * Δt i))) = Real.exp (-(∑ i, h i * Δt i)) := by
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.sum_neg_distrib]

end MathFin
