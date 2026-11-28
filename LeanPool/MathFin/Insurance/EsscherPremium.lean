/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Pricing.OneDateMarket
public import Mathlib.MeasureTheory.Measure.Tilted

/-!
# The Esscher premium is a price

The **Esscher premium principle** charges for a loss `X` the mean of `X` under the Esscher
transform of the reference measure `P` with parameter `h`, the measure `P.tilted (h * X)` with
density `e^{hX}/𝔼[e^{hX}]` (`esscherPremium`): `𝔼[X e^{hX}] / 𝔼[e^{hX}]`.

**It is a price.** In any market with the unit numéraire, the claim that pays the asset at `T` is
worth the Esscher premium of the asset under the Esscher tilt of the reference measure
(`esscherPremium_eq_price`): the market's price is the contract value, and the discount is `1`.

**The insured market** (`insuredMarket`) is the one-date market (`Market.oneDate`) in which the
loss `X` is quoted at its Esscher premium until `T` and is `X` at `T`, with the unit numéraire.
The Esscher tilt is a pricing measure of it when `e^{hX}` and `X e^{hX}` are integrable
(`isPricingMeasure_insuredMarket_tilted`): it is equivalent to `P`, and the premium is the tilt's
mean of the loss. So the Esscher premium is the price of the loss under a pricing measure of an
insured market, where the market is built to quote the loss at that premium
(`price_insuredMarket_tilted`). Another tilt prices it exactly when its premium is the quote
(`isPricingMeasure_insuredMarket_tilted_iff`); uniqueness of the parameter is not proved here. The
model has no dynamics before `T`.

## Main definitions

* `esscherPremium`: the Esscher premium `𝔼[X e^{hX}] / 𝔼[e^{hX}]`.
* `insuredMarket`: the one-date market quoting the loss at its Esscher premium.

## Main results

* `integral_tilted_eq_esscherPremium`: the Esscher premium is the mean of `X` under the tilt.
* `esscherPremium_eq_price`: in a market with unit numéraire, the claim paying the asset at `T`
  is worth the Esscher premium of the asset under the Esscher tilt of the reference measure.
* `isPricingMeasure_insuredMarket_tilted`: the Esscher tilt is a pricing measure of the insured
  market.
* `price_insuredMarket_tilted`: under it the claim paying the loss is worth the Esscher premium.
* `isPricingMeasure_insuredMarket_tilted_iff`: for a date `T > 0`, the `h'`-tilt prices the market
  quoting the `h`-premium exactly when the two premiums agree.

## References

* [H. U. Gerber and E. S. W. Shiu, *Option pricing by Esscher transforms*][GerberShiu1994]
* [F. Esscher, *On the probability function in the collective theory of risk*][Esscher1932]

## Tags

Esscher premium, premium principle, exponential tilting, pricing measure, insured market,
MSC 91G05, MSC 91G20, JEL G22
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory MathFin.Contracts
open scoped NNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- **The Esscher premium** of a loss `X` under `P` with parameter `h`:
`𝔼[X e^{hX}] / 𝔼[e^{hX}]`, the mean of `X` under the Esscher tilt `P.tilted (h * X)` of `P`
(`integral_tilted_eq_esscherPremium`). It is the junk value `0` where `e^{hX}` is not
`P`-integrable. -/
noncomputable def esscherPremium (P : Measure Ω) (X : Ω → ℝ) (h : ℝ) : ℝ :=
  (∫ ω, X ω * Real.exp (h * X ω) ∂P) / ∫ ω, Real.exp (h * X ω) ∂P

/-- **The Esscher premium is the mean of the loss under the Esscher tilt**: the tilt has density
`e^{hX}/𝔼[e^{hX}]` with respect to `P`. -/
theorem integral_tilted_eq_esscherPremium (P : Measure Ω) (X : Ω → ℝ) (h : ℝ) :
    ∫ ω, X ω ∂(P.tilted fun ω ↦ h * X ω) = esscherPremium P X h := by
  rw [integral_tilted, esscherPremium, ← integral_div]
  refine integral_congr_ae (.of_forall fun ω ↦ ?_)
  simp only [smul_eq_mul]
  ring

/-- **The Esscher premium is the price under the Esscher tilt.** In a market with the unit
numéraire, the claim paying the asset at `T` is worth, under the Esscher tilt of the reference
measure with parameter `h`, the Esscher premium of the asset at `T`: the price is the contract
value (`Market.price`), the discount is `1`, and the mean of the asset under the tilt is the
premium (`integral_tilted_eq_esscherPremium`). -/
theorem esscherPremium_eq_price (M : Market Unit Ω) (hN : ∀ t ω, M.numeraire t ω = 1) (T : ℝ≥0)
    (h : ℝ) :
    M.price (M.P.tilted fun ω ↦ h * M.asset () T ω) (.pay T (.obs () T))
      = esscherPremium M.P (M.asset () T) h := by
  rw [← integral_tilted_eq_esscherPremium, Market.price, Contract.value_pay]
  refine integral_congr_ae (.of_forall fun ω ↦ ?_)
  simp [Market.deflator, hN, Payoff.eval, scenarioAt]

/-- **The insured market**: the one-date market (`Market.oneDate`) of the loss `X` with the unit
numéraire, quoted at its Esscher premium until the date `T` and equal to `X` at `T`. -/
noncomputable def insuredMarket (P : Measure Ω) {X : Ω → ℝ} (hX : Measurable X) (h : ℝ)
    (T : ℝ≥0) : Market Unit Ω :=
  Market.oneDate P hX (esscherPremium P X h) 0 T

variable {P : Measure Ω} {X : Ω → ℝ} {h : ℝ}

/-- **The Esscher tilt is a pricing measure of the insured market.** For a probability measure `P`
and a measurable loss `X` with `e^{hX}` and `X e^{hX}` integrable, the Esscher tilt
`P.tilted (h * X)` is a probability measure equivalent to `P`
(`tilted_absolutelyContinuous`, `absolutelyContinuous_tilted`) under which `X` is integrable with
mean the Esscher premium (`integral_tilted_eq_esscherPremium`), the market's quote
(`Market.isPricingMeasure_oneDate`). -/
theorem isPricingMeasure_insuredMarket_tilted [IsProbabilityMeasure P] (hX : Measurable X)
    (hexp : Integrable (fun ω ↦ Real.exp (h * X ω)) P)
    (hXexp : Integrable (fun ω ↦ X ω * Real.exp (h * X ω)) P) (T : ℝ≥0) :
    (insuredMarket P hX h T).IsPricingMeasure T (P.tilted fun ω ↦ h * X ω) := by
  have : IsProbabilityMeasure (P.tilted fun ω ↦ h * X ω) := isProbabilityMeasure_tilted hexp
  refine Market.isPricingMeasure_oneDate (tilted_absolutelyContinuous _ _)
    (absolutelyContinuous_tilted hexp) ?_ ?_
  · rw [integrable_tilted_iff hexp]
    refine hXexp.congr (.of_forall fun ω ↦ ?_)
    simp only [smul_eq_mul]
    exact mul_comm _ _
  · rw [integral_tilted_eq_esscherPremium]
    simp

/-- **Under the Esscher tilt the loss is worth the Esscher premium**: in the insured market the
claim paying the loss at `T` is priced by the Esscher tilt at the premium that the market
quotes. -/
theorem price_insuredMarket_tilted (hX : Measurable X) (T : ℝ≥0) :
    (insuredMarket P hX h T).price (P.tilted fun ω ↦ h * X ω) (.pay T (.obs () T))
      = esscherPremium P X h := by
  rw [insuredMarket, Market.price_pay_obs_oneDate]
  simp only [neg_zero, zero_mul, Real.exp_zero, one_mul]
  exact integral_tilted_eq_esscherPremium P X h

/-- **Which Esscher tilts price the insured market.** For a date `T > 0`, the `h'`-tilt of `P` is a
pricing measure of the insured market `insuredMarket P hX h T`, the one that quotes the loss at the
`h`-premium, exactly when the `h'`-premium is that quote,
`esscherPremium P X h' = esscherPremium P X h`.
The tilts of the other parameters price the market only through that coincidence: the pricing
measure fixes the premium, not the parameter (`Market.isPricingMeasure_oneDate` and its converse
`Market.integral_eq_of_isPricingMeasure_oneDate`). That the premium is strictly increasing in the
parameter for a non-degenerate loss, so that `h' = h` follows, is not proved here. -/
theorem isPricingMeasure_insuredMarket_tilted_iff [IsProbabilityMeasure P] (hX : Measurable X)
    {T : ℝ≥0} (hT : 0 < T) {h' : ℝ} (hexp : Integrable (fun ω ↦ Real.exp (h' * X ω)) P)
    (hXexp : Integrable (fun ω ↦ X ω * Real.exp (h' * X ω)) P) :
    (insuredMarket P hX h T).IsPricingMeasure T (P.tilted fun ω ↦ h' * X ω)
      ↔ esscherPremium P X h' = esscherPremium P X h := by
  constructor
  · intro hp
    have hp' : (Market.oneDate P hX (esscherPremium P X h) 0 T).IsPricingMeasure T
        (P.tilted fun ω ↦ h' * X ω) := hp
    have hmean := (Market.integral_eq_of_isPricingMeasure_oneDate hT hp').2
    rw [integral_tilted_eq_esscherPremium] at hmean
    simpa using hmean
  · intro heq
    have : IsProbabilityMeasure (P.tilted fun ω ↦ h' * X ω) := isProbabilityMeasure_tilted hexp
    refine Market.isPricingMeasure_oneDate (tilted_absolutelyContinuous _ _)
      (absolutelyContinuous_tilted hexp) ?_ ?_
    · rw [integrable_tilted_iff hexp]
      refine hXexp.congr (.of_forall fun ω ↦ ?_)
      simp only [smul_eq_mul]
      exact mul_comm _ _
    · rw [integral_tilted_eq_esscherPremium, heq]
      simp

end MathFin
