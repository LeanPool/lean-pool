/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.BlackScholes.GarmanNormalForm

/-!
# Black-Scholes-Merton call price with continuous dividend yield

Extension of `bs_call_formula` to an asset paying a continuous dividend yield
`q ≥ 0`. The risk-neutral dynamics become `S_T = S_0 · exp((r − q − σ²/2) T + σ √T Z)`,
i.e., the drift is the **effective rate** `r − q`. The discounted-payoff formula is

  `V_q = S_0 · e^{-qT} · Φ(d₁) − K · e^{-rT} · Φ(d₂)`,

where `d₁ = (log(S_0/K) + (r − q + σ²/2) T) / (σ √T)` and `d₂ = d₁ − σ √T`,
i.e., `bsd1 / bsd2` evaluated at the effective rate `r − q`.

Derivation: apply `bs_call_formula` with rate parameter `r − q`, then
multiply through by the additional discount `e^{-qT}` (since the discount on
the LHS uses the actual rate `r`, not the drift `r − q`).

The **Garman–Kohlhagen** FX call is the same theorem read with `r = r_d` (domestic rate) and
`q = r_f` (foreign rate): the foreign currency accrues `r_f` to its holder as a dividend yield.

## Main definitions

* `quantoForward`: the quanto-adjusted forward `S_0 · exp((r_dom − ρ σ_S σ_FX) T)`.

## Main results

* `bs_dividends_call_formula`: under `BSCallHyp` at the effective rate `r − q`, the expected
  discounted call payoff `∫ e^{−rT} · max (S_T − K) 0 ∂Q` equals
  `S_0 e^{−qT} Φ(d₁) − K e^{−rT} Φ(d₂)`, with `d₁, d₂` evaluated at `r − q`.
* `bs_dividends_price_eq_bsVGarman`: the same expected payoff equals `bsVGarman` at spot
  `S_0 e^{−qT}` and discount factor `e^{−rT}`.
* `quanto_correction_factor`: for `S_0 > 0`,
  `quantoForward / (S_0 e^{r_dom T}) = exp(−ρ σ_S σ_FX T)`.

## References

* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], 17.1; 17.3; 31.4
* [Reiner (1992)][Reiner1992]

## Tags

continuous dividend yield, Black–Scholes–Merton, effective rate, dividend-paying asset,
cost of carry, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real

/-- **Black-Scholes-Merton call** pricing formula with continuous dividend yield `q`.

Given a risk-neutral hypothesis with effective drift `r − q`
(`BSCallHyp Q S_0 K (r − q) σ T Z`), the discounted (by the **actual rate** `r`)
expected payoff of the European call is

  `S_0 · e^{-qT} · Φ(d₁) − K · e^{-rT} · Φ(d₂)`,

with `d_i = bsdi S_0 K (r − q) σ T`.

At `r = r_d`, `q = r_f` it is the Garman–Kohlhagen FX call.

Proof: factor `e^{-rT} = e^{-qT} · e^{-(r−q)T}` to apply `bs_call_formula`. -/
theorem bs_dividends_call_formula {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r q σ T : ℝ} {Z : Ω → ℝ}
    (h : BSCallHyp Q S_0 K (r - q) σ T Z) :
    ∫ ω, Real.exp (-r * T) * max (bsTerminal S_0 (r - q) σ T (Z ω) - K) 0 ∂Q
      = S_0 * Real.exp (-(q * T)) * Phi (bsd1 S_0 K (r - q) σ T)
        - K * Real.exp (-(r * T)) * Phi (bsd2 S_0 K (r - q) σ T) := by
  have h_bs := bs_call_formula h
  -- e^{-rT} = e^{-qT} · e^{-(r-q)T}
  have h_factor :
      (fun ω ↦ Real.exp (-r * T) * max (bsTerminal S_0 (r - q) σ T (Z ω) - K) 0)
      = (fun ω ↦ Real.exp (-(q * T)) *
          (Real.exp (-(r - q) * T) * max (bsTerminal S_0 (r - q) σ T (Z ω) - K) 0)) := by
    funext ω
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [h_factor, integral_const_mul, h_bs]
  have h_combine : Real.exp (-(q * T)) * Real.exp (-(r - q) * T) = Real.exp (-(r * T)) := by
    rw [← Real.exp_add]; congr 1; ring
  linear_combination -(K * Phi (bsd2 S_0 K (r - q) σ T)) * h_combine

/-- **BS-Merton dividend price is a Garman-normal-form instance**: the
discounted expected dividend-adjusted call payoff equals `bsVGarman` at
`A = S₀ · e^{−qT}`, `DF = e^{−rT}` — the dividend-discounted-asset numéraire.
Routes `bs_dividends_call_formula` through
`Models/BlackScholes/GarmanNormalForm`'s `bs_dividends_RHS_eq_bsVGarman`, making the
unification load-bearing from the consumer side. -/
theorem bs_dividends_price_eq_bsVGarman {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r q σ T : ℝ} {Z : Ω → ℝ}
    (h : BSCallHyp Q S_0 K (r - q) σ T Z) :
    ∫ ω, Real.exp (-r * T) * max (bsTerminal S_0 (r - q) σ T (Z ω) - K) 0 ∂Q
      = bsVGarman (S_0 * Real.exp (-(q * T))) K (Real.exp (-(r * T))) σ T := by
  rw [bs_dividends_call_formula h]
  exact bs_dividends_RHS_eq_bsVGarman S_0 K r q σ T h.S_0_pos h.K_pos

/-! ## Quanto correction (folded from `Quanto.lean`)

A **quanto** is a derivative paying a function of a foreign asset in domestic
currency. Under the domestic risk-neutral measure, the foreign asset acquires
a *quanto-adjusted drift* `μ^{quanto} = r_dom − ρ · σ_S · σ_FX`. The forward
becomes

  `F^{quanto} = S₀ · exp((r_dom − ρ σ_S σ_FX) · T)`,

vs the unadjusted domestic forward `F^{dom} = S₀ · exp(r_dom T)`. The
correction factor is `exp(−ρ σ_S σ_FX T)`, the log-covariance term in the
joint MGF. -/

/-- **Quanto-adjusted forward**: foreign asset's forward under the domestic
risk-neutral measure with quanto drift adjustment `−ρ σ_S σ_FX`. -/
noncomputable def quantoForward (S_0 r_dom ρ σ_S σ_FX T : ℝ) : ℝ :=
  S_0 * Real.exp ((r_dom - ρ * σ_S * σ_FX) * T)

/-- **Quanto correction factor**: ratio of quanto-adjusted forward to
unadjusted domestic forward equals `exp(−ρ σ_S σ_FX T)`. -/
theorem quanto_correction_factor (S_0 r_dom ρ σ_S σ_FX T : ℝ) (hS : 0 < S_0) :
    quantoForward S_0 r_dom ρ σ_S σ_FX T / (S_0 * Real.exp (r_dom * T))
      = Real.exp (-(ρ * σ_S * σ_FX * T)) := by
  unfold quantoForward
  have hS_ne : S_0 ≠ 0 := hS.ne'
  have h_exp_pos : 0 < Real.exp (r_dom * T) := Real.exp_pos _
  rw [mul_div_mul_left _ _ hS_ne, ← Real.exp_sub]
  congr 1
  ring

end MathFin
