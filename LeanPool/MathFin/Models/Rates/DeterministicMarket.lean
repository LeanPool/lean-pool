/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Pricing.Market
public import LeanPool.MathFin.Models.Rates.DeterministicCurve
public import LeanPool.MathFin.Models.Rates.Immunization

/-!
# The deterministic-rates bond market

The simplest term-structure model as a `Market`: a deterministic bank account `N`
(`N t = e^{rt}` for a flat rate) as numéraire, and zero-coupon bonds `P(t, τᵢ) = N t / N τᵢ` as
the traded assets (`deterministicMarket`). After its maturity a bond is worth what its proceeds
earn in the bank account, so the formula holds at every date and the bond is a self-financing
position. Nothing is random, so every probability measure is a pricing measure
(`isPricingMeasure_deterministicMarket`): the deflated bond `P(t, τᵢ) / N t = 1 / N τᵢ` is
constant.

In any market with a deterministic numéraire a schedule of fixed cash flows is worth its flows
discounted by `N 0 / N` (`price_fixedFlows_deterministicMarket`), and the price of a unit payment
at `τᵢ` is the bond's price (`price_pay_deterministicMarket`). The first-order immunization and
the key-rate durations of `Models/Rates/` differentiate such a flat-rate value, and the value
of a zero-coupon portfolio is the price of its schedule when the numéraire is `e^{rt}`, and the
price of a coupon bond at an annually compounded yield `y` is the price of its schedule when the
numéraire is `(1 + y)^⌊t⌋` (`bondPortfolioValue_eq_price`).

The stochastic short-rate models (`Models/Rates/ShortRate.lean`) price the same schedules through
their zero curve; that their bonds are martingales after deflation by the bank account is not
proved here.

## Main definitions

* `MathFin.Rates.deterministicMarket`: the market of a deterministic numéraire with zero-coupon
  bonds of given maturities.

## Main results

* `MathFin.Rates.isPricingMeasure_deterministicMarket`: every probability measure prices the
  deterministic bond market, at every horizon.
* `MathFin.Rates.price_pay_deterministicMarket`: the price of a unit payment at `τᵢ` is the
  bond's market price `N 0 / N τᵢ`.
* `MathFin.Rates.price_fixedFlows_deterministicMarket`: a schedule of fixed cash flows is worth
  its flows discounted by the numéraire.
* `MathFin.Rates.bondPortfolioValue_eq_price_exp`, `bondPriceDisc_eq_price`: the flat-rate value of
  a zero-coupon portfolio (numéraire `e^{rt}`) and the annually compounded price of a coupon bond
  (numéraire `(1 + y)^⌊t⌋`) are market prices.
* `MathFin.Rates.bondPortfolioValue_eq_price`: the two in one conjunction.

## References

* [P. Bilokon, *The Contract Is Not the Model*][Bilokon2026]
* [D. Brigo and F. Mercurio, *Interest Rate Models --- Theory and Practice*][BrigoMercurio2006],
  Section 1.5
* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], ch. 4

## Tags

term structure, zero-coupon bond, bank account, pricing measure, deterministic interest rates,
bond immunization, MSC 91G30, JEL E43, JEL G12
-/

@[expose] public section

open MeasureTheory MathFin.Contracts
open scoped NNReal

namespace MathFin.Rates

variable {ι Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- **The deterministic-rates bond market**: the physical measure `P`, the trivial filtration,
the deterministic numéraire `N` (the bank account), and for each `i` the zero-coupon bond of
maturity `τ i`, worth `N t / N (τ i)` at `t`. -/
noncomputable def deterministicMarket (P : Measure Ω) (N : ℝ≥0 → ℝ) (hN : ∀ t, 0 < N t)
    (τ : ι → ℝ≥0) : Market ι Ω where
  P := P
  𝓕 := Filtration.const ℝ≥0 ⊥ bot_le
  asset i t _ := N t / N (τ i)
  numeraire t _ := N t
  numeraire_pos t _ := hN t
  asset_adapted _ _ := stronglyMeasurable_const
  numeraire_adapted _ := stronglyMeasurable_const

/-- **Every probability measure prices the deterministic bond market.** The deflated bond
`(N t / N τᵢ) / N t = 1 / N τᵢ` is constant in time and in the outcome, hence a martingale. -/
theorem isPricingMeasure_deterministicMarket (P : Measure Ω) [IsProbabilityMeasure P]
    (N : ℝ≥0 → ℝ) (hN : ∀ t, 0 < N t) (τ : ι → ℝ≥0) (T : ℝ≥0) :
    (deterministicMarket P N hN τ).IsPricingMeasure T P :=
  ⟨inferInstance, Measure.AbsolutelyContinuous.refl _, Measure.AbsolutelyContinuous.refl _,
    fun i ↦ by
      have h : (fun t (ω : Ω) ↦ (deterministicMarket P N hN τ).deflated i (min t T) ω)
          = fun _ _ ↦ 1 / N (τ i) := by
        funext t ω
        have := (hN (min t T)).ne'
        simp only [Market.deflated, deterministicMarket]
        field_simp
      rw [h]
      exact martingale_const _ _ _⟩

/-- **The price of a unit payment at `τᵢ` is the bond's price.** In the deterministic bond market
the unit payment at `τ i` is worth the bond's price `N 0 / N (τ i)` today, under any probability
measure. -/
theorem price_pay_deterministicMarket (P : Measure Ω) (N : ℝ≥0 → ℝ) (hN : ∀ t, 0 < N t)
    (τ : ι → ℝ≥0) (Q : Measure Ω) [IsProbabilityMeasure Q] (i : ι) (ω : Ω) :
    (deterministicMarket P N hN τ).price Q (.pay (τ i) (.const 1))
      = (deterministicMarket P N hN τ).asset i 0 ω := by
  rw [Market.price, Contract.value_pay]
  simp [Payoff.eval, Market.deflator, deterministicMarket]

/-- **A schedule of fixed cash flows is worth its flows discounted by the numéraire**: in the
deterministic bond market, `∑ cᵢ N 0 / N (tᵢ)`, under any probability measure. -/
theorem price_fixedFlows_deterministicMarket (P : Measure Ω) (N : ℝ≥0 → ℝ)
    (hN : ∀ t, 0 < N t) (τ : ι → ℝ≥0) (Q : Measure Ω) [IsProbabilityMeasure Q]
    (t : ℕ → ℝ≥0) (c : ℕ → ℝ) (n : ℕ) :
    (deterministicMarket P N hN τ).price Q (fixedFlows t c n)
      = ∑ i ∈ Finset.range n, N 0 / N (t i) * c i :=
  value_fixedFlows_deterministic (fun s ↦ N 0 / N s) _ t c n

/-- **The flat-rate value of a bond portfolio is a market price.** In any market with the money
market `e^{rt}` as numéraire, under any probability measure `Q`, the portfolio of zero-coupon
bonds of face `w i` and maturity `T i ≥ 0` (`bondPortfolioValue` at time `0`) is the price of the
schedule `fixedFlows`. -/
theorem bondPortfolioValue_eq_price_exp (Q : Measure Ω) [IsProbabilityMeasure Q] (n : ℕ)
    (w T : ℕ → ℝ) (hT : ∀ i, 0 ≤ T i) (M : Market ι Ω) (r : ℝ)
    (hM : ∀ t ω, M.numeraire t ω = Real.exp (r * t)) :
    MathFin.bondPortfolioValue (Finset.range n) w T 0 r =
      M.price Q (fixedFlows (fun i ↦ (T i).toNNReal) w n) := by
  have hD : M.deflator = fun (s : ℝ≥0) _ ↦ Real.exp (-(r * s)) := by
    funext s ω
    simp only [Market.deflator_of_numeraire_exp hM, neg_mul]
  rw [Market.price, hD, value_fixedFlows_deterministic, MathFin.bondPortfolioValue]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Real.coe_toNNReal _ (hT i), sub_zero]
  ring

/-- **The annually compounded price of a coupon bond is a market price.** In any market with the
numéraire `(1 + y)^⌊t⌋`, under any probability measure `Q`, the coupon bond at the annually
compounded yield `y` (`bondPriceDisc`) is the price of its cash flows. -/
theorem bondPriceDisc_eq_price (Q : Measure Ω) [IsProbabilityMeasure Q] (n : ℕ)
    (w : ℕ → ℝ) (M : Market ι Ω) (y : ℝ) (t : ℕ → ℕ)
    (hM : ∀ s ω, M.numeraire s ω = (1 + y) ^ ⌊s⌋₊) :
    MathFin.bondPriceDisc (Finset.range n) t w y =
      M.price Q (fixedFlows (fun i ↦ ((t i : ℕ) : ℝ≥0)) w n) := by
  have hD : M.deflator = fun (s : ℝ≥0) _ ↦ ((1 + y) ^ ⌊s⌋₊)⁻¹ := by
    funext s ω
    simp only [Market.deflator_of_numeraire hM, Nat.floor_zero, pow_zero, one_div]
  rw [Market.price, hD, value_fixedFlows_deterministic, MathFin.bondPriceDisc]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Nat.floor_natCast]
  ring

/-- **The flat-rate value of a bond portfolio and the discrete price of a coupon bond are market
prices** (`bondPortfolioValue_eq_price_exp`, `bondPriceDisc_eq_price`): the two facts in one
statement, one per numéraire, `e^{rt}` and `(1 + y)^⌊t⌋`. -/
theorem bondPortfolioValue_eq_price (Q : Measure Ω) [IsProbabilityMeasure Q] (n : ℕ)
    (w T : ℕ → ℝ) (hT : ∀ i, 0 ≤ T i) :
    (∀ (M : Market ι Ω) (r : ℝ), (∀ t ω, M.numeraire t ω = Real.exp (r * t)) →
      MathFin.bondPortfolioValue (Finset.range n) w T 0 r =
        M.price Q (fixedFlows (fun i ↦ (T i).toNNReal) w n)) ∧
    (∀ (M : Market ι Ω) (y : ℝ) (t : ℕ → ℕ),
      (∀ s ω, M.numeraire s ω = (1 + y) ^ ⌊s⌋₊) →
      MathFin.bondPriceDisc (Finset.range n) t w y =
        M.price Q (fixedFlows (fun i ↦ ((t i : ℕ) : ℝ≥0)) w n)) :=
  ⟨fun M r hM ↦ bondPortfolioValue_eq_price_exp Q n w T hT M r hM,
    fun M y t hM ↦ bondPriceDisc_eq_price Q n w M y t hM⟩

end MathFin.Rates
