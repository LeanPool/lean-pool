/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Contracts.Instruments.Options
public import LeanPool.MathFin.Pricing.Value
public import LeanPool.MathFin.Pricing.EquivMartingaleMeasure
public import LeanPool.MathFin.Pricing.StatePrices
public import LeanPool.MathFin.Pricing.Numeraire

/-!
# The market and its pricing functional

**A market** is a filtered measurable space with a reference measure `P`, the adapted prices
`S i t` of the traded assets and a strictly positive adapted numéraire `N t`. **A pricing
measure** up to a horizon `T` is a probability measure with the null events of `P` among the
events known at `T` (equivalent to `P` on `𝓕 T`) under which every deflated price `S i t / N t`,
frozen at `T`, is a martingale.

Equivalence is asked on `𝓕 T` only, as in Föllmer–Schied (§5.2) and Delbaen–Schachermayer: a
horizon-`T` market cannot tell measures apart beyond `𝓕 T`, and on an infinite path space the
risk-neutral and the physical laws are typically singular (i.i.d. coin flips with two
up-probabilities, Brownian motions with two drifts) while equivalent on every `𝓕 T`. For a finite
`P` nothing is lost: a pricing measure agrees on `𝓕 T` with one equivalent to `P` everywhere
(`IsPricingMeasure.exists_isEquivProbMeasure`), and a measure equivalent everywhere under which the
frozen deflated assets are martingales is a pricing measure
(`IsPricingMeasure.of_isEquivProbMeasure`). **The price** of a contract under a measure `Q` is its
value (`Contract.value`) with the deflator `N 0 / N t` on the market's assets:

  `price Q c = 𝔼_Q[∑ (N 0 / N tₖ) · cₖ]` over the contract's cash flows `cₖ` at `tₖ`.

This is the trunk the library's pricing devices hang on (docs/specs/2026-11-07-one-trunk-design.md,
§3 I1). It is a price when `Q` is a pricing measure and the deflated cash flows are integrable: the
definition is total, and the theorems that call it a price carry those conditions (docs/design.md
§2).

Two facts make it the price rather than one more integral:

* a traded asset is priced at its price: under a pricing measure, with a deterministic `N 0`, the
  claim that delivers asset `i` at a date `t ≤ T` is worth `𝔼_Q[S i 0]`
  (`IsPricingMeasure.price_pay_obs`);
* a fixed-dated contract's price depends on the market only through the law of what it reads: two
  markets, on two sample spaces, whose assets and deflators at the contract's observations and
  payment dates have one law under their measures give the same price
  (`price_eq_of_map_observation_eq`).
  A parametric price of a fixed-dated contract defined in one concrete model is therefore its
  price in every market with that law.

The price at an intermediate date `t` is the conditional expectation of the deflated cash flows
given `𝓕 t`, re-expressed at `t` (`priceAt`); deflated to `0`, it averages to the price
(`integral_deflator_mul_priceAt`, the tower property). The zero-coupon bond price `P(t, T)` of the
rates models is the price at `t` of one unit paid at `T`
(`Contracts.bondPrice_deflator_eq_priceAt`, in `Models/Rates/Caplet.lean`).

Changing the numéraire changes the measure and not the price: the market with numéraire `N`
in place of `B` prices a payment at `T` under the numéraire measure `Q^N` exactly as the original
market does under `Q` (`price_pay_withNumeraire`, the change-of-numéraire theorem
`changeOfNumeraire` read through the price). That `Q^N` is a pricing measure of the new market is
not proved here.

On a finite sample space the price of a single payment is `statePricePricing` with the state
prices `q ω = (N 0 / N t)(ω) · Q {ω}` (`price_pay_eq_statePricePricing`), non-negative for every
`Q` (`statePrice_nonneg`).

## Main definitions

* `Market`: a filtered measurable space, its reference measure, the traded assets and a numéraire.
* `Market.deflator`: `N 0 / N t`. `Market.deflated`: `S i t / N t`.
* `Market.IsPricingMeasure`: a probability measure equivalent to `P` on `𝓕 T` making every
  deflated asset a martingale up to the horizon `T`.
* `Market.price`: the value of a contract under a measure, deflated by the numéraire.
* `Market.priceAt`: the price at an intermediate date, a random variable.
* `Market.withNumeraire`: the same market with another numéraire.

## Main results

* `Market.price_eq_value_of_numeraire`: a deterministic numéraire prices by the deterministic
  deflator `f 0 / f t`; `Market.price_europeanCall_of_numeraire_eq_one`: with unit numéraire the
  call is the plain integral of its payoff.
* `Market.stronglyMeasurable_deflator`: the deflator `N 0 / N T` is `𝓕 T`-measurable.
* `Market.IsPricingMeasure.of_isEquivProbMeasure`: a measure equivalent to `P` everywhere that
  makes the deflated assets frozen martingales is a pricing measure.
* `Market.IsPricingMeasure.of_trim_eq`: a measure that agrees with a pricing measure on `𝓕 T` is
  one.
* `Market.IsPricingMeasure.exists_isEquivProbMeasure`: a pricing measure agrees on `𝓕 T` with a
  pricing measure equivalent to `P` everywhere.
* `Market.IsPricingMeasure.price_pay_obs`: a traded asset is priced at its initial price.
* `Market.price_eq_of_map_observation_eq`: law invariance of the price.
* `Market.integral_deflator_mul_priceAt`: the deflated price at `t` averages to the price.
* `Market.price_pay_withNumeraire`: the price is invariant under the change of numéraire.
* `Market.price_pay_eq_statePricePricing`: on a finite sample space the price of a payment is
  state-price pricing, with non-negative state prices (`Market.statePrice_nonneg`).

## References

* [J. M. Harrison and S. R. Pliska, *Martingales and stochastic integrals in the theory of
  continuous trading*][HarrisonPliska1981]
* [H. Geman, N. El Karoui and J.-C. Rochet, *Changes of numéraire, changes of probability measure
  and option pricing*][GemanElKarouiRochet1995]
* [H. Föllmer and A. Schied, *Stochastic Finance: An Introduction in Discrete Time*][FollmerSchied],
  §5.2
* [F. Delbaen and W. Schachermayer, *The Mathematics of Arbitrage*][DelbaenSchachermayer]
* [P. Bilokon, *The Contract Is Not the Model*][Bilokon2026]

## Tags

market, numéraire, deflator, pricing measure, equivalent martingale measure, risk-neutral
pricing, law invariance, state prices, MSC 91G20, MSC 60G44, JEL G12, JEL G13
-/

@[expose] public section

open MeasureTheory MathFin.Contracts
open scoped NNReal

namespace MathFin

/-- **A market**: a measurable space with a reference measure `P` and a filtration `𝓕`, the
adapted prices `asset i t` of the traded assets, and a strictly positive adapted numéraire. -/
structure Market (ι Ω : Type*) [mΩ : MeasurableSpace Ω] where
  /-- The reference (physical) measure. -/
  P : Measure Ω
  /-- The information available at each date. -/
  𝓕 : Filtration ℝ≥0 mΩ
  /-- The price of each traded asset at each date. -/
  asset : ι → ℝ≥0 → Ω → ℝ
  /-- The numéraire, in which prices are expressed. -/
  numeraire : ℝ≥0 → Ω → ℝ
  numeraire_pos : ∀ t ω, 0 < numeraire t ω
  asset_adapted : ∀ i, StronglyAdapted 𝓕 (asset i)
  numeraire_adapted : StronglyAdapted 𝓕 numeraire

namespace Market

variable {ι Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The deflator `N 0 / N t`: a cash flow at `t` is worth `N 0 / N t` times itself at `0`. -/
noncomputable def deflator (M : Market ι Ω) (t : ℝ≥0) (ω : Ω) : ℝ :=
  M.numeraire 0 ω / M.numeraire t ω

/-- The price of asset `i` in units of the numéraire, `S i t / N t`. -/
noncomputable def deflated (M : Market ι Ω) (i : ι) (t : ℝ≥0) (ω : Ω) : ℝ :=
  M.asset i t ω / M.numeraire t ω

/-- **`Q` prices the market up to `T`**: a probability measure with the null events of `P` among
the events known at `T` (`Q` and `P` restricted to `𝓕 T` are mutually absolutely continuous), under
which every deflated asset, frozen at `T`, is an `𝓕`-martingale. -/
structure IsPricingMeasure (M : Market ι Ω) (T : ℝ≥0) (Q : Measure Ω) : Prop where
  isProb : IsProbabilityMeasure Q
  ac : Q.trim (M.𝓕.le T) ≪ M.P.trim (M.𝓕.le T)
  ac' : M.P.trim (M.𝓕.le T) ≪ Q.trim (M.𝓕.le T)
  martingale (i : ι) : Martingale (fun t ↦ M.deflated i (min t T)) M.𝓕 Q

/-- **The price of a contract** under `Q`: its value with the deflator `N 0 / N t` on the market's
assets. It is a price when `Q` is a pricing measure (`IsPricingMeasure`) and the deflated cash flows
are `Q`-integrable. Under another measure it is an integral with no pricing meaning, and for a
non-integrable contract it is the Bochner integral's junk value `0`. -/
noncomputable def price (M : Market ι Ω) (Q : Measure Ω) (c : Contract ι) : ℝ :=
  c.value Q M.deflator M.asset

theorem deflator_pos (M : Market ι Ω) (t : ℝ≥0) (ω : Ω) : 0 < M.deflator t ω :=
  div_pos (M.numeraire_pos 0 ω) (M.numeraire_pos t ω)

theorem measurable_asset (M : Market ι Ω) (i : ι) (t : ℝ≥0) : Measurable (M.asset i t) :=
  ((M.asset_adapted i t).mono (M.𝓕.le t)).measurable

theorem measurable_numeraire (M : Market ι Ω) (t : ℝ≥0) : Measurable (M.numeraire t) :=
  ((M.numeraire_adapted t).mono (M.𝓕.le t)).measurable

theorem measurable_deflator (M : Market ι Ω) (t : ℝ≥0) : Measurable (M.deflator t) :=
  (M.measurable_numeraire 0).div (M.measurable_numeraire t)

/-- **A deterministic numéraire gives a deterministic deflator**: if `N t ω = f t` for every date
and state, the deflator is `f 0 / f t`. -/
theorem deflator_of_numeraire {M : Market ι Ω} {f : ℝ≥0 → ℝ}
    (hf : ∀ t ω, M.numeraire t ω = f t) (t : ℝ≥0) (ω : Ω) : M.deflator t ω = f 0 / f t := by
  simp only [deflator, hf]

/-- **The money-market deflator**: with the numéraire `e^{rt}` the deflator is the discount
`e^{−rt}`. The Black–Scholes, clocked-volatility and one-date markets are instances. -/
theorem deflator_of_numeraire_exp {M : Market ι Ω} {r : ℝ}
    (hN : ∀ t ω, M.numeraire t ω = Real.exp (r * t)) (t : ℝ≥0) (ω : Ω) :
    M.deflator t ω = Real.exp (-r * t) := by
  simp only [deflator_of_numeraire hN, NNReal.coe_zero, mul_zero, Real.exp_zero, one_div, neg_mul,
    Real.exp_neg]

/-- **A deterministic numéraire prices by a deterministic deflator**: if `N t ω = f t`, the price
of a contract is its value with the deflator `f 0 / f t`. The money-market, Bachelier,
clocked-volatility and one-date markets are instances. -/
theorem price_eq_value_of_numeraire {M : Market ι Ω} {f : ℝ≥0 → ℝ}
    (hf : ∀ t ω, M.numeraire t ω = f t) (Q : Measure Ω) (c : Contract ι) :
    M.price Q c = c.value Q (fun t _ ↦ f 0 / f t) M.asset :=
  congrArg (fun D ↦ c.value Q D M.asset) (funext fun t ↦ funext (deflator_of_numeraire hf t))

/-- With unit numéraire the call is priced by the plain `Q`-integral of its payoff. -/
theorem price_europeanCall_of_numeraire_eq_one {M : Market Unit Ω} {T : ℝ≥0} {Q : Measure Ω}
    (hN : ∀ t ω, M.numeraire t ω = 1) (K : ℝ) :
    M.price Q (europeanCall K T) = ∫ ω, max (M.asset () T ω - K) 0 ∂Q := by
  simp [price, europeanCall, europeanCallPayoff, Contract.value_pay, Payoff.eval, scenarioAt,
    deflator, hN]

/-- Each deflated asset is adapted. -/
theorem stronglyAdapted_deflated (M : Market ι Ω) (i : ι) : StronglyAdapted M.𝓕 (M.deflated i) :=
  fun t ↦
    ((M.asset_adapted i t).measurable.div (M.numeraire_adapted t).measurable).stronglyMeasurable

/-- The deflator `N 0 / N T` is known at `T`. -/
theorem stronglyMeasurable_deflator (M : Market ι Ω) (T : ℝ≥0) :
    StronglyMeasurable[M.𝓕 T] (M.deflator T) :=
  (((M.numeraire_adapted 0).mono (M.𝓕.mono (zero_le (a := T)))).measurable.div
    (M.numeraire_adapted T).measurable).stronglyMeasurable

/-- **A measure equivalent to `P` everywhere is a pricing measure** as soon as every deflated asset,
frozen at `T`, is a martingale under it. -/
theorem IsPricingMeasure.of_isEquivProbMeasure {M : Market ι Ω} {T : ℝ≥0} {Q : Measure Ω}
    (hQ : IsEquivProbMeasure M.P Q)
    (hmart : ∀ i, Martingale (fun t ↦ M.deflated i (min t T)) M.𝓕 Q) :
    M.IsPricingMeasure T Q :=
  ⟨hQ.isProb, hQ.ac.trim _, hQ.ac'.trim _, hmart⟩

/-- **A pricing measure equivalent to `P` everywhere** is an equivalent martingale measure for each
deflated asset. -/
theorem IsPricingMeasure.isEMM {M : Market ι Ω} {T : ℝ≥0} {Q : Measure Ω}
    (hQ : M.IsPricingMeasure T Q) (hQP : IsEquivProbMeasure M.P Q) (i : ι) :
    IsEMM M.𝓕 M.P (M.deflated i) T Q :=
  ⟨hQP, hQ.martingale i⟩

/-- **A pricing measure is determined by its restriction to `𝓕 T`**: a measure that agrees with a
pricing measure on `𝓕 T` is one. The deflated assets frozen at `T` are `𝓕 T`-measurable, so they
are martingales under both (`martingale_min_of_trim_eq`). -/
theorem IsPricingMeasure.of_trim_eq {M : Market ι Ω} {T : ℝ≥0} {Q Q' : Measure Ω}
    (hQ : M.IsPricingMeasure T Q) (h : Q.trim (M.𝓕.le T) = Q'.trim (M.𝓕.le T)) :
    M.IsPricingMeasure T Q' := by
  have := hQ.isProb
  have : IsProbabilityMeasure Q' := ⟨by
    rw [← trim_measurableSet_eq (M.𝓕.le T) (@MeasurableSet.univ _ (M.𝓕 T)), ← h,
      trim_measurableSet_eq (M.𝓕.le T) (@MeasurableSet.univ _ (M.𝓕 T)), measure_univ]⟩
  refine ⟨this, ?_, ?_, fun i ↦ martingale_min_of_trim_eq h (hQ.martingale i)⟩
  · rw [← h]
    exact hQ.ac
  · rw [← h]
    exact hQ.ac'

/-- **A pricing measure agrees on `𝓕 T` with one equivalent to `P` everywhere.** Weight `P` by the
density of `Q` with respect to `P` on `𝓕 T` (`exists_isEquivProbMeasure_trim_eq`); the deflated
assets frozen at `T` are `𝓕 T`-measurable, so they stay martingales under the new measure
(`martingale_min_of_trim_eq`). This is how a pricing measure meets the theorems stated for an
`IsEMM`. -/
theorem IsPricingMeasure.exists_isEquivProbMeasure {M : Market ι Ω} [IsFiniteMeasure M.P]
    {T : ℝ≥0} {Q : Measure Ω} (hQ : M.IsPricingMeasure T Q) :
    ∃ Q', IsEquivProbMeasure M.P Q' ∧ M.IsPricingMeasure T Q' ∧
      Q'.trim (M.𝓕.le T) = Q.trim (M.𝓕.le T) := by
  have := hQ.isProb
  obtain ⟨Q', hQ', htrim⟩ := exists_isEquivProbMeasure_trim_eq (M.𝓕.le T) hQ.ac hQ.ac'
  have := hQ'.isProb
  exact ⟨Q', hQ', .of_isEquivProbMeasure hQ' fun i ↦
    martingale_min_of_trim_eq htrim.symm (hQ.martingale i), htrim⟩

/-- **A traded asset is priced at its price.** Under a pricing measure up to `T`, with a
deterministic initial numéraire `N 0 = n₀`, the claim that delivers asset `i` at a date `t ≤ T` is
worth `𝔼_Q[S i 0]`: the deflated asset is a `Q`-martingale, so its mean at `t` is its mean at
`0`. -/
theorem IsPricingMeasure.price_pay_obs {M : Market ι Ω} {T : ℝ≥0} {Q : Measure Ω}
    (hQ : M.IsPricingMeasure T Q) {n₀ : ℝ} (hN₀ : ∀ ω, M.numeraire 0 ω = n₀) (i : ι)
    {t : ℝ≥0} (ht : t ≤ T) :
    M.price Q (.pay t (.obs i t)) = ∫ ω, M.asset i 0 ω ∂Q := by
  have := hQ.isProb
  have hmart : ∫ ω, M.deflated i t ω ∂Q = ∫ ω, M.deflated i 0 ω ∂Q := by
    rw [← integral_condExp (M.𝓕.le 0)]
    refine integral_congr_ae ?_
    have h := (hQ.martingale i).condExp_ae_eq (zero_le (a := t))
    rwa [min_eq_left ht, min_eq_left (zero_le (a := T))] at h
  calc M.price Q (.pay t (.obs i t)) = n₀ * ∫ ω, M.deflated i t ω ∂Q := by
        rw [price, Contract.value_pay, ← integral_const_mul]
        refine integral_congr_ae (.of_forall fun ω ↦ ?_)
        simp only [deflator, deflated, Payoff.eval, scenarioAt, hN₀]
        ring
    _ = ∫ ω, M.asset i 0 ω ∂Q := by
        rw [hmart, ← integral_const_mul]
        refine integral_congr_ae (.of_forall fun ω ↦ ?_)
        have hn₀ : n₀ ≠ 0 := (hN₀ ω ▸ M.numeraire_pos 0 ω).ne'
        simp only [deflated, hN₀]
        field_simp

/-- **Law invariance of the price.** A fixed-dated contract has the same price in two markets, on
two sample spaces, if what it reads has one law: the assets at its observations and the deflator at
its payment dates, under `Q` and under `Q'`. -/
theorem price_eq_of_map_observation_eq {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}
    (M : Market ι Ω) (M' : Market ι Ω') {Q : Measure Ω} {Q' : Measure Ω'} (c : Contract ι)
    (hc : c.FixedDated)
    (h : Q.map (c.observation M.deflator M.asset) = Q'.map (c.observation M'.deflator M'.asset)) :
    M.price Q c = M'.price Q' c :=
  c.value_eq_of_map_observation_eq hc M.measurable_deflator M.measurable_asset
    M'.measurable_deflator M'.measurable_asset h

/-! ### The price at an intermediate date -/

/-- **The price of a contract at date `t`**, a random variable: the conditional expectation given
`𝓕 t` of the contract's cash flows deflated to `0`, divided by the deflator `N 0 / N t` to express
it at `t`. It is a price under the conditions that make `price` one (a pricing measure and
integrable deflated cash flows); the definition is total. -/
noncomputable def priceAt (M : Market ι Ω) (Q : Measure Ω) (t : ℝ≥0) (c : Contract ι) : Ω → ℝ :=
  fun ω ↦ Q[fun ω' ↦ c.pathPV (fun s ↦ M.deflator s ω') (scenarioAt M.asset ω') | M.𝓕 t] ω
    / M.deflator t ω

/-- **The deflated price at `t` averages to the price**:
`𝔼_Q[(N 0 / N t) · price_t c] = price c`, by the tower property (`integral_condExp`). -/
theorem integral_deflator_mul_priceAt (M : Market ι Ω) (Q : Measure Ω) [IsFiniteMeasure Q]
    (t : ℝ≥0) (c : Contract ι) :
    ∫ ω, M.deflator t ω * M.priceAt Q t c ω ∂Q = M.price Q c := by
  have h (ω : Ω) : M.deflator t ω * M.priceAt Q t c ω
      = Q[fun ω' ↦ c.pathPV (fun s ↦ M.deflator s ω') (scenarioAt M.asset ω') | M.𝓕 t] ω := by
    rw [priceAt]
    field_simp [(M.deflator_pos t ω).ne']
  simp_rw [h]
  exact integral_condExp (M.𝓕.le t)

/-! ### Change of numéraire -/

/-- The market `M` with its numéraire replaced by a strictly positive adapted process `N`. -/
def withNumeraire (M : Market ι Ω) (N : ℝ≥0 → Ω → ℝ) (hN : ∀ t ω, 0 < N t ω)
    (hNa : StronglyAdapted M.𝓕 N) : Market ι Ω :=
  { M with numeraire := N, numeraire_pos := hN, numeraire_adapted := hNa }

/-- **The price is invariant under the change of numéraire.** Replace the numéraire `B` of `M` by
a strictly positive adapted `N`, with deterministic initial values `B 0 = b₀` and `N 0 = n₀`. The
new market prices a payment at `T` under the numéraire measure `Q^N`, of density
`(N_T b₀)/(n₀ B_T)` with respect to `Q`, as `M` prices it under `Q`: this is `changeOfNumeraire`,
`n₀ 𝔼^{Q^N}[X / N_T] = b₀ 𝔼^Q[X / B_T]`, and it needs no integrability. -/
theorem price_pay_withNumeraire [Nonempty Ω] (M : Market ι Ω) (Q : Measure Ω)
    {N : ℝ≥0 → Ω → ℝ} (hN : ∀ t ω, 0 < N t ω) (hNa : StronglyAdapted M.𝓕 N) {b₀ n₀ : ℝ}
    (hB₀ : ∀ ω, M.numeraire 0 ω = b₀) (hN₀ : ∀ ω, N 0 ω = n₀) (T : ℝ≥0) (a : Payoff ι) :
    (M.withNumeraire N hN hNa).price (numeraireMeasure Q (M.numeraire T) (N T) b₀ n₀) (.pay T a)
      = M.price Q (.pay T a) := by
  obtain ⟨ω₀⟩ := ‹Nonempty Ω›
  have hb₀ : 0 < b₀ := hB₀ ω₀ ▸ M.numeraire_pos 0 ω₀
  have hn₀ : 0 < n₀ := hN₀ ω₀ ▸ hN 0 ω₀
  calc (M.withNumeraire N hN hNa).price (numeraireMeasure Q (M.numeraire T) (N T) b₀ n₀) (.pay T a)
      = n₀ * ∫ ω, a.eval (scenarioAt M.asset ω) / N T ω
          ∂(numeraireMeasure Q (M.numeraire T) (N T) b₀ n₀) := by
        rw [price, Contract.value_pay, ← integral_const_mul]
        refine integral_congr_ae (.of_forall fun ω ↦ ?_)
        simp only [deflator, withNumeraire, hN₀]
        ring
    _ = b₀ * ∫ ω, a.eval (scenarioAt M.asset ω) / M.numeraire T ω ∂Q :=
        changeOfNumeraire _ ((hNa T).mono (M.𝓕.le T)).measurable (M.measurable_numeraire T)
          (hN T) (M.numeraire_pos T) hb₀.le hn₀
    _ = M.price Q (.pay T a) := by
        rw [price, Contract.value_pay, ← integral_const_mul]
        refine integral_congr_ae (.of_forall fun ω ↦ ?_)
        simp only [deflator, hB₀]
        ring

/-! ### Finite sample spaces: state prices -/

/-- The state price of `ω` for a payment at `t`: the deflator at `t` times the `Q`-mass of `ω`. -/
noncomputable def statePrice (M : Market ι Ω) (Q : Measure Ω) (t : ℝ≥0) (ω : Ω) : ℝ :=
  M.deflator t ω * Q.real {ω}

theorem statePrice_nonneg (M : Market ι Ω) (Q : Measure Ω) (t : ℝ≥0) (ω : Ω) :
    0 ≤ M.statePrice Q t ω :=
  mul_nonneg (M.deflator_pos t ω).le measureReal_nonneg

/-- **On a finite sample space, the price of a payment is state-price pricing**: the payment at
`t` of a payoff `a` is worth `∑ ω, q ω · a(ω)` with the state prices `q ω = (N 0 / N t)(ω) Q {ω}`,
for every finite measure `Q`. -/
theorem price_pay_eq_statePricePricing [Fintype Ω] [MeasurableSingletonClass Ω]
    (M : Market ι Ω) (Q : Measure Ω) [IsFiniteMeasure Q] (t : ℝ≥0) (a : Payoff ι) :
    M.price Q (.pay t a)
      = statePricePricing Finset.univ (M.statePrice Q t) fun ω ↦ a.eval (scenarioAt M.asset ω) := by
  rw [price, Contract.value_pay, integral_fintype Integrable.of_finite, statePricePricing]
  exact Finset.sum_congr rfl fun ω _ ↦ by simp only [statePrice, smul_eq_mul]; ring

end Market

end MathFin
