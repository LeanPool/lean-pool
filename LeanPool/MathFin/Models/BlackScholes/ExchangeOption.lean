/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.BlackScholes.GarmanNormalForm
public import LeanPool.MathFin.Pricing.Numeraire

/-!
# Margrabe's exchange option: a two-asset option that is a one-asset BS problem

The **exchange option** pays `max(S¹_T − S²_T, 0)` — the right to exchange
asset 2 for asset 1 at maturity. Its defining structural fact (Margrabe 1978)
is that it depends only on the *ratio* `S¹/S²`, which is itself lognormal
with an **effective volatility**

  `σ² = σ₁² + σ₂² − 2 ρ σ₁ σ₂`,

so the two-asset problem collapses to a one-asset Black-Scholes problem at
that effective vol. This is the first genuinely multivariate result in the
library, and it reuses (rather than re-derives) the 1-D machinery — the same
"structural reduction" discipline as `PowerCall`.

This file establishes the two pieces of the reduction:

* `margrabe_variance_sub` / `margrabe_effective_variance` — the effective
  variance of the log-spread, from covariance bilinearity. This is the first
  consumer of the covariance machinery that `Probability/Gaussian/BivariateGaussian`
  also uses, making that machinery load-bearing.
* `exchange_payoff_eq_ratio` — the payoff reduction `max(S¹ − S², 0) = S² ·
  max(S¹/S² − 1, 0)`, exhibiting the exchange option as a (numeraire-scaled)
  vanilla call on the ratio.

The price-level formula (`margrabe_price_via_call`) prices the exchange option
in the `S²`-numeraire as a vanilla `bs_call_formula` call on the ratio
`R = S¹/S²`. Its pricing primitive is `BSCallHyp` for the ratio — the same
abstraction `bs_call_formula` takes for any underlying.
`MathFin/Models/BlackScholes/MargrabeGrounding.lean` (`margrabe_bsCallHyp_of_gaussian`) constructs
that primitive from a joint two-GBM Gaussian model: under an Esscher tilt `Q` of the model
measure, a standard-normal driver drives the actual ratio `S¹_T/S²_T` (that `Q` is the
`S²`-numéraire measure is not proved). The same file proves the price-level statement directly
under the model measure: `margrabe_exchange_price` shows that `margrabePrice` is the
discounted expected exchange payoff.

## Main definitions

* `margrabeD1`, `margrabeD2`: `d₁ = (log(S¹₀/S²₀) + σ²T/2) / (σ√T)` and `d₂ = d₁ − σ√T`, with
  `σ` the effective volatility of the log-spread.
* `margrabePrice`: the exchange-option price `S¹₀ · Φ(d₁) − S²₀ · Φ(d₂)`.

## Main results

* `margrabe_variance_sub`: `Var[L₁ − L₂] = Var L₁ + Var L₂ − 2·cov(L₁, L₂)`.
* `margrabe_effective_variance`: substituting `σ₁²T, σ₂²T, ρσ₁σ₂T` gives the
  effective variance `(σ₁² + σ₂² − 2ρσ₁σ₂)·T`.
* `exchange_payoff_eq_ratio`: `max(a − b, 0) = b · max(a/b − 1, 0)` for `b > 0`.
* `margrabe_eq_bsVGarman`: Margrabe price is a `GarmanNormalForm` instance.
* `margrabe_parity`: `Margrabe(S¹,S²) − Margrabe(S²,S¹) = S¹ − S²`.
* `margrabe_price_via_call`: the exchange option is a `bs_call_formula` call
  on the ratio (price-level reduction).

## References

* [H. Geman, N. El Karoui and J. C. Rochet, *Changes of numéraire, changes of probability measure
  and option pricing*][GemanElKarouiRochet1995]
* [W. Margrabe, *The value of an option to exchange one asset for another*][Margrabe1978]

## Tags

Margrabe, exchange option, change of numeraire, effective volatility, two-asset option, MSC 91G20,
JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory

/-- **Variance of a spread** via covariance bilinearity: for two L²
random variables, `Var[L₁ − L₂] = Var L₁ + Var L₂ − 2·cov(L₁, L₂)`. The
cross term carries the correlation — this is where the `−2ρσ₁σ₂` of the
Margrabe effective volatility comes from. -/
theorem margrabe_variance_sub {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P]
    {L₁ L₂ : Ω → ℝ} (h₁ : MemLp L₁ 2 P) (h₂ : MemLp L₂ 2 P) :
    Var[L₁ - L₂; P] = Var[L₁; P] + Var[L₂; P] - 2 * cov[L₁, L₂; P] := by
  rw [← covariance_self (h₁.sub h₂).aemeasurable,
      covariance_sub_left h₁ h₂ (h₁.sub h₂),
      covariance_sub_right h₁ h₁ h₂, covariance_sub_right h₂ h₁ h₂,
      covariance_self h₁.aemeasurable, covariance_self h₂.aemeasurable,
      covariance_comm L₂ L₁]
  ring

/-- **Margrabe effective variance**: with `Var L₁ = σ₁²T`, `Var L₂ = σ₂²T`,
and `cov(L₁, L₂) = ρσ₁σ₂T`, the log-spread variance is
`(σ₁² + σ₂² − 2ρσ₁σ₂)·T` — the effective variance at which the exchange
option prices as a one-asset Black-Scholes call. -/
theorem margrabe_effective_variance {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P]
    {L₁ L₂ : Ω → ℝ} {σ₁ σ₂ ρ T : ℝ}
    (h₁ : MemLp L₁ 2 P) (h₂ : MemLp L₂ 2 P)
    (hV₁ : Var[L₁; P] = σ₁ ^ 2 * T) (hV₂ : Var[L₂; P] = σ₂ ^ 2 * T)
    (hcov : cov[L₁, L₂; P] = ρ * σ₁ * σ₂ * T) :
    Var[L₁ - L₂; P] = (σ₁ ^ 2 + σ₂ ^ 2 - 2 * ρ * σ₁ * σ₂) * T := by
  rw [margrabe_variance_sub h₁ h₂, hV₁, hV₂, hcov]
  ring

/-- **Exchange-option payoff reduction**: `max(a − b, 0) = b · max(a/b − 1, 0)`
for `b > 0`. The exchange payoff `max(S¹_T − S²_T, 0)` is `S²_T` times a
vanilla call payoff on the ratio `S¹_T/S²_T` struck at `1` — the algebraic
form of "use `S²` as numeraire." -/
theorem exchange_payoff_eq_ratio (a b : ℝ) (hb : 0 < b) :
    max (a - b) 0 = b * max (a / b - 1) 0 := by
  rw [mul_max_of_nonneg _ _ hb.le, mul_zero,
      show b * (a / b - 1) = a - b from by field_simp]

/-! ## Margrabe price is a Garman-normal-form instance

The exchange-option closed form is the *one* BS-family formula
`V = A·Φ(d₁) − K·DF·Φ(d₂)` at `A = S¹₀`, `K = S²₀`, `DF = 1` (the
S²-numeraire / forward measure carries no discounting), and effective vol
`σ = √(σ₁² + σ₂² − 2ρσ₁σ₂)`. So Margrabe joins Black-Scholes, Black-76,
BS-Merton, Garman-Kohlhagen, and KMV-Merton as instances of `bsVGarman`. -/

/-- **Margrabe `d₁`**: `(log(S¹₀/S²₀) + σ²T/2) / (σ√T)`, with `σ` the
effective volatility of the log-spread. -/
noncomputable def margrabeD1 (S1 S2 σ T : ℝ) : ℝ :=
  (Real.log (S1 / S2) + σ ^ 2 * T / 2) / (σ * Real.sqrt T)

/-- **Margrabe `d₂`**: `d₁ − σ√T`. -/
noncomputable def margrabeD2 (S1 S2 σ T : ℝ) : ℝ :=
  margrabeD1 S1 S2 σ T - σ * Real.sqrt T

/-- **Margrabe exchange-option price**: `S¹₀·Φ(d₁) − S²₀·Φ(d₂)`. -/
noncomputable def margrabePrice (S1 S2 σ T : ℝ) : ℝ :=
  S1 * Phi (margrabeD1 S1 S2 σ T) - S2 * Phi (margrabeD2 S1 S2 σ T)

/-- **Margrabe is a Garman-normal-form instance**: the exchange-option price
equals `bsVGarman` at `A = S¹₀`, `K = S²₀`, `DF = 1`, effective vol `σ`. The
second asset plays the role of the discounted strike and `DF = 1` because the
S²-numeraire measure carries no discounting. So a *multivariate* option is the
same closed form `V = A·Φ(d₁) − K·DF·Φ(d₂)` as every BS-family price — one
more consumer of the `GarmanNormalForm` principle. -/
theorem margrabe_eq_bsVGarman (S1 S2 σ T : ℝ) :
    margrabePrice S1 S2 σ T = bsVGarman S1 S2 1 σ T := by
  have hd1 : margrabeD1 S1 S2 σ T = gbsd1 S1 S2 1 σ T := by
    unfold margrabeD1 gbsd1; rw [mul_one]
  unfold margrabePrice bsVGarman margrabeD2 gbsd2
  rw [hd1, mul_one]

/-- **Exchange-option parity** — the analog of put-call parity. The option to
exchange asset 2 for asset 1 minus the option to exchange asset 1 for asset 2
equals the forward on the spread:

  `Margrabe(S¹, S²) − Margrabe(S², S¹) = S¹ − S²`.

Foundation-certain: swapping the two assets sends `d₁ ↦ −d₂` and `d₂ ↦ −d₁`
(the `σ²T/(σ√T) = σ√T` identity), and `Φ(x) + Φ(−x) = 1` (the same symmetry
`Phi_add_Phi_neg` that drives put-call parity) collapses the rest. No
probability machinery, no assumed moments — pure algebra on the closed form. -/
theorem margrabe_parity (S1 S2 σ T : ℝ)
    (hS1 : 0 < S1) (hS2 : 0 < S2) (hσ : σ ≠ 0) (hT : 0 < T) :
    margrabePrice S1 S2 σ T - margrabePrice S2 S1 σ T = S1 - S2 := by
  have hσT : σ * Real.sqrt T ≠ 0 := mul_ne_zero hσ (Real.sqrt_pos.mpr hT).ne'
  -- The swapped d₁ and the original d₁ sum to σ√T.
  have hsum : margrabeD1 S2 S1 σ T + margrabeD1 S1 S2 σ T = σ * Real.sqrt T := by
    unfold margrabeD1
    rw [← add_div, Real.log_div hS2.ne' hS1.ne', Real.log_div hS1.ne' hS2.ne',
        show (Real.log S2 - Real.log S1 + σ ^ 2 * T / 2)
              + (Real.log S1 - Real.log S2 + σ ^ 2 * T / 2) = σ ^ 2 * T from by ring,
        div_eq_iff hσT,
        show σ * Real.sqrt T * (σ * Real.sqrt T)
              = σ ^ 2 * (Real.sqrt T * Real.sqrt T) from by ring,
        Real.mul_self_sqrt hT.le]
  -- Swap symmetry of the d's.
  have hd1 : margrabeD1 S2 S1 σ T = -(margrabeD2 S1 S2 σ T) := by
    unfold margrabeD2; linarith [hsum]
  have hd2 : margrabeD2 S2 S1 σ T = -(margrabeD1 S1 S2 σ T) := by
    unfold margrabeD2; linarith [hsum]
  unfold margrabePrice
  rw [hd1, hd2, Phi_neg, Phi_neg]
  ring

/-! ## Price-level Margrabe: the exchange option is a call on the ratio

This closes the price-level reduction. The exchange option, valued in the
`S²`-numeraire, is a vanilla Black-Scholes call on the ratio `R = S¹/S²`
struck at `1` with zero rate and effective vol `σ`. The pricing primitive is
`BSCallHyp` for the *ratio* — exactly the abstraction `bs_call_formula` takes
for any underlying; here the underlying is `R`. Its construction from a joint two-GBM
model, under an Esscher tilt not shown to be the `S²`-numeraire measure, is
`MargrabeGrounding.lean`. -/

/-- **Bridge**: standard BS `d₁` of the ratio `R₀ = S¹₀/S²₀` (strike `1`,
zero rate) is the Margrabe `d₁`. -/
private lemma bsd1_ratio_eq_margrabeD1 (S1 S2 σ T : ℝ) :
    bsd1 (S1 / S2) 1 0 σ T = margrabeD1 S1 S2 σ T := by
  unfold bsd1 margrabeD1
  rw [div_one]; congr 1; ring

/-- **Bridge** for `d₂`. -/
private lemma bsd2_ratio_eq_margrabeD2 (S1 S2 σ T : ℝ) :
    bsd2 (S1 / S2) 1 0 σ T = margrabeD2 S1 S2 σ T := by
  unfold bsd2 margrabeD2
  rw [bsd1_ratio_eq_margrabeD1]

/-- **Price-level Margrabe formula** (exchange option as a call on the ratio).
Given that the ratio `R = S¹/S²` is risk-neutral lognormal under the
`S²`-numeraire measure `Q` (`BSCallHyp Q (S¹₀/S²₀) 1 0 σ Z` — strike `1`, zero
rate, effective vol `σ`), the `S²`-numeraire value of the exchange payoff
`S²₀ · E_Q[max(R_T − 1, 0)]` equals the Margrabe price `margrabePrice`. This
is a one-line composition of `bs_call_formula` with the algebra `S²₀·R₀ = S¹₀`
and the `d`-bridges above — no new probability machinery. -/
theorem margrabe_price_via_call
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S1 S2 σ T : ℝ} {Z : Ω → ℝ} (hS2 : 0 < S2)
    (h : BSCallHyp Q (S1 / S2) 1 0 σ T Z) :
    S2 * ∫ ω, max (bsTerminal (S1 / S2) 0 σ T (Z ω) - 1) 0 ∂Q
      = margrabePrice S1 S2 σ T := by
  have hbs := bs_call_formula h
  simp only [neg_zero, zero_mul, Real.exp_zero, one_mul, mul_one] at hbs
  rw [hbs, bsd1_ratio_eq_margrabeD1, bsd2_ratio_eq_margrabeD2]
  unfold margrabePrice
  field_simp

/-! ## The S²-numéraire valuation is a change-of-numéraire instance

`exchange_payoff_eq_ratio` says the exchange payoff is `S²_T` times a call on the
ratio; the general change of numéraire (`Foundations.Numeraire.changeOfNumeraire`)
turns that algebraic fact into a genuine measure statement — the option's value in the
`S²`-numéraire equals its value under the reference measure. This makes the informal
"value in the `S²`-numéraire" of `margrabe_price_via_call` an *instance* of the general
law, rather than a bespoke reduction. -/

/-- **Exchange option in the S²-numéraire — a change-of-numéraire instance.** With the
second asset `S²` as numéraire (`numeraireMeasure Q 1 S²_T 1 S²₀`, density
`dQ^(S²)/dQ = S²_T/S²₀`), the option's `S²`-numéraire value is its value under the
reference measure `Q`:

  `S²₀ · 𝔼^{Q^(S²)}[max(S¹_T/S²_T − 1, 0)] = 𝔼^Q[max(S¹_T − S²_T, 0)]`.

This is `changeOfNumeraire` at `X = ` the exchange payoff, `N = S²`, `B ≡ 1`, composed
with `exchange_payoff_eq_ratio` (`max(S¹−S²,0) = S²·max(S¹/S²−1,0)`). No integrability
hypothesis is needed — only strict positivity of the numéraire `S²_T > 0`. -/
theorem exchangeOption_numeraire_price
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (Q : Measure Ω) (S1T S2T : Ω → ℝ) (S2_0 : ℝ)
    (hS2meas : Measurable S2T) (hS2pos : ∀ ω, 0 < S2T ω) (hS20 : 0 < S2_0) :
    S2_0 * ∫ ω, max (S1T ω / S2T ω - 1) 0
        ∂(numeraireMeasure Q (fun _ ↦ 1) S2T 1 S2_0)
      = ∫ ω, max (S1T ω - S2T ω) 0 ∂Q := by
  have hL : ∀ ω, max (S1T ω / S2T ω - 1) 0 = max (S1T ω - S2T ω) 0 / S2T ω := fun ω ↦ by
    rw [exchange_payoff_eq_ratio (S1T ω) (S2T ω) (hS2pos ω),
        mul_div_cancel_left₀ _ (hS2pos ω).ne']
  have hkey := changeOfNumeraire (Q := Q) (X := fun ω ↦ max (S1T ω - S2T ω) 0)
      (BT := fun _ ↦ (1 : ℝ)) (NT := S2T) (B0 := (1 : ℝ)) (N0 := S2_0)
      hS2meas measurable_const hS2pos (fun _ ↦ one_pos) zero_le_one hS20
  simp_rw [div_one, one_mul] at hkey
  simp_rw [hL]
  exact hkey

end MathFin
