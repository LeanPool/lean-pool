/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.BlackScholes.Forward
public import LeanPool.MathFin.Pricing.NoArbitrageDerivations

/-!
# FX forward: covered and uncovered interest parity

**Covered interest parity (CIP)**: with continuously-compounded domestic and
foreign rates `r_d`, `r_f` and spot `S` (domestic per unit of foreign), the
no-arbitrage forward rate for maturity `T` is

  `F(0, T) = S · exp((r_d - r_f) · T)`.

It is derived from `forward_price_from_no_arbitrage`: in a finite-state market
the forward contract paying `S_T - F` is priced by the same state prices as the
domestic zero-coupon bond (price `e^{-r_d T}`) and the foreign zero-coupon bond
held in domestic currency (price `S·e^{-r_f T}`: buy `e^{-r_f T}` units of
foreign currency at spot and invest them at `r_f`), and it is worth zero
exactly at `F = S·e^{-r_f T}/e^{-r_d T}` (`covered_interest_parity`). The
one-period discrete form is `F = S·(1 + r_d)/(1 + r_f)`.

**Uncovered interest parity**, in its risk-neutral form: under the domestic
risk-neutral measure of the Garman–Kohlhagen model (the lognormal hypothesis
`BSCallHyp` with drift `r_d - r_f`, as in `bs_dividends_call_formula` at `q = r_f`),
the expected terminal spot is the same `S·e^{(r_d - r_f)T}`
(`uncovered_interest_parity`, from `expected_terminal_eq_forward`). This is a
statement about the pricing measure; the economists' UIP, the same equation
under the physical measure, is an empirical hypothesis and is not claimed
here. The two parities agree (`covered_eq_uncovered_interest_parity`): the
forward a static market prices to zero is the model's expected spot.

## Main definitions

* `fxForward`: the covered-interest-parity FX forward rate `F(0, T) = S · exp((r_d - r_f) · T)`
  with continuous compounding.

## Main results

* `covered_interest_parity`: the zero-value forward is `fxForward`, derived
  from `forward_price_from_no_arbitrage`;
  `covered_interest_parity_discrete`: the one-period form
  `S·(1 + r_d)/(1 + r_f)`.
* `uncovered_interest_parity`: `E_Q[S_T] = fxForward` under the
  Garman–Kohlhagen risk-neutral hypothesis.
* `covered_eq_uncovered_interest_parity`: the CIP forward equals the
  risk-neutral expected spot.

## References

* [Garman and Kohlhagen, *Foreign currency option values*][GarmanKohlhagen1983]
* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull]

## Tags

covered interest parity, uncovered interest parity, FX forward, Garman–Kohlhagen, foreign exchange,
interest rate differential, MSC 91G20, JEL F31, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory

/-- Covered-interest-parity FX forward rate for maturity `T`, continuous
compounding: `F(0, T) = S · exp((r_d - r_f) · T)`. -/
noncomputable def fxForward (S r_d r_f T : ℝ) : ℝ := S * Real.exp ((r_d - r_f) * T)

/-- **Covered interest parity from no-arbitrage.** A finite-state market with
state prices `q` and terminal spot `S_T`, pricing the domestic zero-coupon bond
at `e^{-r_d T}` and the foreign zero-coupon bond, held in domestic currency, at
`S·e^{-r_f T}`. The forward contract paying `S_T - F` is worth zero iff
`F = S·e^{(r_d - r_f)T}`: `forward_price_from_no_arbitrage` with the foreign
bond as the asset. -/
theorem covered_interest_parity {ι : Type*} (s : Finset ι) (q S_T : ι → ℝ)
    (S r_d r_f T F : ℝ)
    (h_dom : ∑ i ∈ s, q i = Real.exp (-(r_d * T)))
    (h_for : ∑ i ∈ s, q i * S_T i = S * Real.exp (-(r_f * T))) :
    ∑ i ∈ s, q i * (S_T i - F) = 0 ↔ F = fxForward S r_d r_f T := by
  refine (forward_price_from_no_arbitrage s q S_T _ _ F (Real.exp_pos _).ne' h_dom h_for).trans ?_
  rw [fxForward, mul_div_assoc, ← Real.exp_sub, neg_sub_neg, ← sub_mul]

/-- **Covered interest parity, one period, discrete compounding**: with the
domestic bond priced at `1/(1 + r_d)` (`1 + r_d ≠ 0`) and the foreign bond, in
domestic currency, at `S/(1 + r_f)`, the zero-value forward is
`S·(1 + r_d)/(1 + r_f)`. The foreign bond price `S/(1 + r_f)` is a price only for
`1 + r_f > 0`; the identity holds for every `r_f`. -/
theorem covered_interest_parity_discrete {ι : Type*} (s : Finset ι) (q S_T : ι → ℝ)
    (S r_d r_f F : ℝ) (hd : 1 + r_d ≠ 0)
    (h_dom : ∑ i ∈ s, q i = 1 / (1 + r_d))
    (h_for : ∑ i ∈ s, q i * S_T i = S / (1 + r_f)) :
    ∑ i ∈ s, q i * (S_T i - F) = 0 ↔ F = S * (1 + r_d) / (1 + r_f) := by
  refine (forward_price_from_no_arbitrage s q S_T _ _ F (one_div_ne_zero hd) h_dom h_for).trans ?_
  rw [div_div_eq_mul_div, div_one, div_mul_eq_mul_div]

/-- **Uncovered interest parity, risk-neutral form.** Under the Garman–Kohlhagen
hypothesis (lognormal terminal spot with domestic risk-neutral drift
`r_d - r_f`), the expected terminal spot is the CIP forward:
`E_Q[S_T] = S·e^{(r_d - r_f)T}`. This is `expected_terminal_eq_forward` at the
drift `r_d - r_f`; it is a statement about the pricing measure `Q`, not about
the physical one. -/
theorem uncovered_interest_parity {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q] {S K r_d r_f σ T : ℝ} {Z : Ω → ℝ}
    (h : BSCallHyp Q S K (r_d - r_f) σ T Z) :
    ∫ ω, bsTerminal S (r_d - r_f) σ T (Z ω) ∂Q = fxForward S r_d r_f T :=
  expected_terminal_eq_forward h

/-- **Covered and uncovered parity agree.** The forward that a finite-state
market prices to zero (`covered_interest_parity`) is the expected terminal spot
under the Garman–Kohlhagen risk-neutral measure with the same spot and rates
(`uncovered_interest_parity`). -/
theorem covered_eq_uncovered_interest_parity {ι : Type*} (s : Finset ι) (q S_T : ι → ℝ)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S K r_d r_f σ T F : ℝ} {Z : Ω → ℝ}
    (h_dom : ∑ i ∈ s, q i = Real.exp (-(r_d * T)))
    (h_for : ∑ i ∈ s, q i * S_T i = S * Real.exp (-(r_f * T)))
    (hF : ∑ i ∈ s, q i * (S_T i - F) = 0) (h : BSCallHyp Q S K (r_d - r_f) σ T Z) :
    F = ∫ ω, bsTerminal S (r_d - r_f) σ T (Z ω) ∂Q :=
  ((covered_interest_parity s q S_T S r_d r_f T F h_dom h_for).mp hF).trans
    (uncovered_interest_parity h).symm

end MathFin
