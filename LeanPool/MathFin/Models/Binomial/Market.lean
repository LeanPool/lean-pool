/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Binomial.Binomial
public import LeanPool.MathFin.Models.Binomial.Girsanov
public import LeanPool.MathFin.Models.Binomial.MultiPeriodFTAP
public import LeanPool.MathFin.Pricing.Market
public import LeanPool.MathFin.Probability.Martingales.TimeChange

/-!
# The binomial tree as a market

The binomial model of `Models/Binomial/Binomial.lean` as a `Market` (`Binomial.market`): coin-flip
paths `ω : ℕ → Bool` under a physical law `P`, the information of the flips made by `t`
(`flipFiltration` along the step count `t ↦ ⌊t / h⌋₊`, `Filtration.comp`), the spot after those
flips as the traded asset, and the money market `e^{ρ n}` after `n` steps as numéraire.

* **The risk-neutral law prices it.** Under no-arbitrage, i.i.d. flips that go up with the
  probability `crrUpProb u d ρ` are a pricing measure of the market at every horizon, for a
  physical law of i.i.d. flips going up with any probability `0 < p < 1`
  (`isPricingMeasure_coinFlipMeasure`): the deflated spot is the discounted spot after the steps
  made (`deflated_market`), a martingale for the flip filtration (`martingale_discountedSpot`) and
  so along the step count (`Martingale.comp`), and the two laws are equivalent on the flips made by
  the horizon (`coinFlipMeasure_trim_equiv`), though not on the whole path space when `p ≠ q`.
* **Its price is the binomial value.** On contracts paying at whole numbers of steps the
  deflator `e^{−ρ ⌊t/h⌋}` is the binomial discount `e^{−ρ t/h}`, so the market's price is the
  `Contract.value` of `Binomial.lean` (`price_market`), and a European payoff is priced at its
  backward-induction tree price (`price_market_pay_eq_binomialPrice`).
* **The pricing measure is unique on the information at the horizon.** At a horizon of `N` steps
  every pricing measure agrees with the risk-neutral law on the first `N` flips
  (`trim_eq_of_isPricingMeasure`): it maps to an equivalent martingale measure of the `N`-period
  tree (`isEMM_horizonSpot_map`), which is unique
  (`IsEMM.eq_horizonMeasure`). So every pricing measure gives a European payoff its tree price
  (`price_pay_eq_binomialPrice_of_isPricingMeasure`).
* **The fundamental theorem.** For `S₀ > 0`, `0 < d < u` and at least one step, the market has a
  pricing measure exactly when `d < e^ρ < u` (`exists_isPricingMeasure_iff`): a pricing measure
  rules out the one-period arbitrage of `binomialNoArb_of_noArbitrage`.

## Main definitions

* `Binomial.market`: the binomial tree with step `h` as a `Market`.

## Main results

* `Binomial.isPricingMeasure_coinFlipMeasure`: the risk-neutral law of the flips is a pricing
  measure, for every physical law of i.i.d. flips.
* `Binomial.price_market`: on grid dates the market's price is the binomial value.
* `Binomial.price_market_pay_eq_binomialPrice`: the price of a European payoff is its tree price.
* `Binomial.trim_eq_of_isPricingMeasure`: every pricing measure is the risk-neutral law on the flips
  made by the horizon.
* `Binomial.price_pay_eq_binomialPrice_of_isPricingMeasure`: every pricing measure gives the tree
  price.
* `Binomial.exists_isPricingMeasure_iff`: a pricing measure exists iff `d < e^ρ < u`.

## References

* [J. M. Harrison and S. R. Pliska, *Martingales and stochastic integrals in the theory of
  continuous trading*][HarrisonPliska1981]
* [J. C. Cox, S. A. Ross and M. Rubinstein, *Option pricing: a simplified
  approach*][CoxRossRubinstein1979]
* [S. E. Shreve, *Stochastic Calculus for Finance I: The Binomial Asset Pricing Model*][ShreveSCFI],
  ch. 2

## Tags

binomial tree, Cox–Ross–Rubinstein, market, numéraire, pricing measure, risk-neutral probability,
money market, fundamental theorem of asset pricing, unique pricing measure, MSC 91G20, MSC 60G42,
JEL G13
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace MathFin.Contracts.Binomial

variable {u d ρ h : ℝ}

/-- The step count `t ↦ ⌊t / h⌋₊` is monotone for a step `h ≥ 0`. -/
theorem monotone_floor_div (hh : 0 ≤ h) : Monotone fun t : ℝ≥0 ↦ ⌊(t : ℝ) / h⌋₊ :=
  fun _ _ hst ↦ Nat.floor_mono (div_le_div_of_nonneg_right (NNReal.coe_le_coe.2 hst) hh)

/-- **The binomial market** with step `h ≥ 0`, under a physical law `P` of the flips: the
information of the flips made by `t`, the spot after them, and the money market `e^{ρ n}` after
`n` steps as numéraire. -/
noncomputable def market (P : Measure (ℕ → Bool)) (S₀ u d ρ : ℝ) (hh : 0 ≤ h) :
    Market Unit (ℕ → Bool) where
  P := P
  𝓕 := flipFiltration.comp (monotone_floor_div hh)
  asset := assets S₀ u d h
  numeraire t _ := Real.exp (ρ * ⌊(t : ℝ) / h⌋₊)
  numeraire_pos _ _ := Real.exp_pos _
  asset_adapted _ t := by
    change StronglyMeasurable[(flipFiltration.comp (monotone_floor_div hh)) t]
      (spotPath S₀ u d ⌊(t : ℝ) / h⌋₊)
    rw [Filtration.comp_apply]
    exact stronglyMeasurable_flipFiltration_iff.2 (pathAdaptedAt_spotPath S₀ u d _)
  numeraire_adapted _ := stronglyMeasurable_const

/-- The deflated spot of the binomial market is the discounted spot after the steps made. -/
theorem deflated_market (P : Measure (ℕ → Bool)) (S₀ : ℝ) (hh : 0 ≤ h) (t : ℝ≥0) :
    (market P S₀ u d ρ hh).deflated () t = discountedSpot S₀ u d ρ ⌊(t : ℝ) / h⌋₊ := by
  funext ω
  simp only [Market.deflated, market, assets, discountedSpot, Real.exp_neg, div_eq_inv_mul]

variable {q : ℝ≥0} (hq : q ≤ 1)

/-- **The risk-neutral law of the flips prices the binomial market.** Under no-arbitrage, i.i.d.
flips that go up with the probability `crrUpProb u d ρ` are a pricing measure at every horizon,
for the physical law of i.i.d. flips going up with any probability `0 < p < 1`: the deflated spot is
the discounted spot after the steps made, a martingale for the flip filtration
(`martingale_discountedSpot`) and so for its time change along the step count, and the two laws are
equivalent on the flips made by the horizon (`coinFlipMeasure_trim_equiv`). -/
theorem isPricingMeasure_coinFlipMeasure (hna : BinomialNoArb u d ρ)
    (hqcrr : crrUpProb u d ρ = q) (S₀ : ℝ) (hh : 0 ≤ h) {p : ℝ≥0} (hp0 : 0 < p) (hp : p < 1)
    (T : ℝ≥0) :
    (market (coinFlipMeasure p hp.le) S₀ u d ρ hh).IsPricingMeasure T (coinFlipMeasure q hq) := by
  have hq01 : 0 < q ∧ q < 1 := by
    have := crrUpProb_mem_Ioo hna
    rw [hqcrr] at this
    exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2⟩
  have hM : Martingale (fun t ↦ (market (coinFlipMeasure p hp.le) S₀ u d ρ hh).deflated () t)
      (market (coinFlipMeasure p hp.le) S₀ u d ρ hh).𝓕 (coinFlipMeasure q hq) := by
    simp only [deflated_market]
    exact (martingale_discountedSpot hna S₀ hq hqcrr).comp (monotone_floor_div hh)
  obtain ⟨hac, hac'⟩ := coinFlipMeasure_trim_equiv hp0 hp hq01.1 hq01.2 ⌊(T : ℝ) / h⌋₊
  have liftTrim {Q₁ Q₂ : Measure (ℕ → Bool)}
      (hQR : Q₁.trim (flipFiltration.le ⌊(T : ℝ) / h⌋₊) ≪
        Q₂.trim (flipFiltration.le ⌊(T : ℝ) / h⌋₊)) :
      Q₁.trim ((market (coinFlipMeasure p hp.le) S₀ u d ρ hh).𝓕.le T) ≪
        Q₂.trim ((market (coinFlipMeasure p hp.le) S₀ u d ρ hh).𝓕.le T) := by
    refine Measure.AbsolutelyContinuous.mk fun s hs hz ↦ ?_
    rw [trim_measurableSet_eq _ hs] at hz ⊢
    have hsf : MeasurableSet[flipFiltration ⌊(T : ℝ) / h⌋₊] s := by
      change MeasurableSet[(flipFiltration.comp (monotone_floor_div hh)) T] s at hs
      rwa [Filtration.comp_apply] at hs
    rw [← trim_measurableSet_eq _ hsf]
    exact hQR (by rw [trim_measurableSet_eq _ hsf]; exact hz)
  exact ⟨inferInstance, liftTrim hac, liftTrim hac', fun ⟨⟩ ↦ martingale_min_of_martingale hM T⟩

/-- **On grid dates the binomial market's price is the binomial value**: for a fixed-dated
contract paying only at whole numbers of steps, the deflator `e^{−ρ ⌊t/h⌋}` is the discount
`e^{−ρ t/h}` of `Binomial.lean`, under any measure `Q`. -/
theorem price_market (P Q : Measure (ℕ → Bool)) (S₀ : ℝ) (hh : 0 ≤ h) {c : Contract Unit}
    (hc : c.FixedDated) (hgrid : ∀ t ∈ c.dates, ∃ n : ℕ, (t : ℝ) / h = n) :
    (market P S₀ u d ρ hh).price Q c
      = c.value Q (fun t _ ↦ discount ρ h t) (assets S₀ u d h) := by
  simp only [Market.price, Contract.value]
  refine integral_congr_ae (.of_forall fun ω ↦ c.pathPV_congr hc (fun t ht ↦ ?_) fun _ _ ↦ rfl)
  obtain ⟨n, hn⟩ := hgrid t ht
  simp [Market.deflator, market, discount, hn, Real.exp_neg]

/-- **The price of a European payoff in the binomial market is its tree price.** Under the
risk-neutral law, a cash flow at `T`, on step `N`, paying `g` of the spot at `T`, is priced at the
backward-induction price `binomialPrice u d ρ g N S₀`. -/
theorem price_market_pay_eq_binomialPrice (hqcrr : crrUpProb u d ρ = q) (P : Measure (ℕ → Bool))
    (S₀ : ℝ) (hh : 0 ≤ h) {T : ℝ≥0} {N : ℕ} (hTN : (T : ℝ) / h = N) {a : Payoff Unit}
    {g : ℝ → ℝ} (hg : ∀ s : Scenario Unit, a.eval s = g (s () T)) :
    (market P S₀ u d ρ hh).price (coinFlipMeasure q hq) (.pay T a)
      = binomialPrice u d ρ g N S₀ := by
  rw [price_market P _ S₀ hh (c := .pay T a) trivial fun t ht ↦
    ⟨N, by rw [show t = T by simpa [Contract.dates] using ht]; exact hTN⟩]
  exact value_pay_eq_binomialPrice hq hqcrr S₀ hTN hg

/-! ### Every pricing measure is the risk-neutral one -/

/-- At a horizon of `N` steps the deflated spot frozen at the horizon is the discounted spot frozen
at step `N`. -/
theorem deflated_market_min (P : Measure (ℕ → Bool)) (S₀ : ℝ) (hh : 0 ≤ h) {T : ℝ≥0} {N : ℕ}
    (hTN : ⌊(T : ℝ) / h⌋₊ = N) (t : ℝ≥0) :
    (market P S₀ u d ρ hh).deflated () (min t T)
      = discountedSpot S₀ u d ρ (min ⌊(t : ℝ) / h⌋₊ N) := by
  rw [deflated_market, ← hTN]
  congr 1
  exact (monotone_floor_div hh).map_min

variable {P Q : Measure (ℕ → Bool)} {S₀ : ℝ} {T : ℝ≥0} {N : ℕ}

/-- **Under a pricing measure the discounted spot frozen at the horizon is a martingale for the
flip filtration**: the deflated spot is one along the step count, and the step count has the right
inverse `n ↦ n h` (`Martingale.of_comp`). -/
theorem martingale_discountedSpot_of_isPricingMeasure (hh : 0 < h) (hTN : ⌊(T : ℝ) / h⌋₊ = N)
    (hQ : (market P S₀ u d ρ hh.le).IsPricingMeasure T Q) :
    Martingale (fun n ↦ discountedSpot S₀ u d ρ (min n N)) flipFiltration Q := by
  have hM := hQ.martingale ()
  simp only [deflated_market_min P S₀ hh.le hTN] at hM
  refine Martingale.of_comp (f := fun n ↦ discountedSpot S₀ u d ρ (min n N))
    (monotone_floor_div hh.le) (ψ := fun n : ℕ ↦ ⟨n * h, by positivity⟩)
    (fun a b hab ↦ NNReal.coe_le_coe.1 (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hab) hh.le))
    (fun n ↦ ?_) hM
  change ⌊(n : ℝ) * h / h⌋₊ = n
  rw [mul_div_cancel_right₀ _ hh.ne', Nat.floor_natCast]

/-- Under a pricing measure at a horizon of `N` steps, the laws of the first `N` flips under the
pricing measure and under the physical law are equivalent. -/
theorem map_flips_equiv_of_isPricingMeasure (hh : 0 < h) (hTN : ⌊(T : ℝ) / h⌋₊ = N)
    (hQ : (market P S₀ u d ρ hh.le).IsPricingMeasure T Q) :
    Q.map (flips N) ≪ P.map (flips N) ∧ P.map (flips N) ≪ Q.map (flips N) := by
  have hmeas {S : Set (Fin N → Bool)} (hS : MeasurableSet S) :
      MeasurableSet[(market P S₀ u d ρ hh.le).𝓕 T] (flips N ⁻¹' S) := by
    change MeasurableSet[(flipFiltration.comp (monotone_floor_div hh.le)) T] _
    rw [Filtration.comp_apply, hTN]
    exact MeasurableSpace.measurableSet_comap.2 ⟨S, hS, rfl⟩
  refine ⟨Measure.AbsolutelyContinuous.mk fun S hS h0 ↦ ?_,
    Measure.AbsolutelyContinuous.mk fun S hS h0 ↦ ?_⟩
  · rw [Measure.map_apply (measurable_flips N) hS] at h0 ⊢
    rw [← trim_measurableSet_eq ((market P S₀ u d ρ hh.le).𝓕.le T) (hmeas hS)] at h0 ⊢
    exact hQ.ac h0
  · rw [Measure.map_apply (measurable_flips N) hS] at h0 ⊢
    rw [← trim_measurableSet_eq ((market P S₀ u d ρ hh.le).𝓕.le T) (hmeas hS)] at h0 ⊢
    exact hQ.ac' h0

/-- **Every pricing measure is the risk-neutral law on the flips made by the horizon.** For
`S₀ > 0` under no-arbitrage, a pricing measure of the binomial market at a horizon of `N` steps
agrees with i.i.d. flips going up with probability `crrUpProb u d ρ` on the first `N` flips: the law
of those flips under it is an equivalent martingale measure of the `N`-period tree
(`isEMM_horizonSpot_map`), which is unique (`IsEMM.eq_horizonMeasure`). -/
theorem trim_eq_of_isPricingMeasure (hS₀ : 0 < S₀) (hna : BinomialNoArb u d ρ)
    (hqcrr : crrUpProb u d ρ = q) (hh : 0 < h) (hTN : ⌊(T : ℝ) / h⌋₊ = N)
    (hQ : (market P S₀ u d ρ hh.le).IsPricingMeasure T Q) :
    Q.trim (flipFiltration.le N) = (coinFlipMeasure q hq).trim (flipFiltration.le N) := by
  have := hQ.isProb
  have hmap : Q.map (flips N) = horizonMeasure N q hq :=
    (isEMM_horizonSpot_map (P := Q.map (flips N)) ⟨inferInstance, .rfl, .rfl⟩
      (martingale_discountedSpot_of_isPricingMeasure hh hTN hQ)).eq_horizonMeasure hS₀ hna hq hqcrr
  refine @Measure.ext _ (flipFiltration N) _ _ fun A hA ↦ ?_
  obtain ⟨S, hS, rfl⟩ := MeasurableSpace.measurableSet_comap.1 hA
  rw [trim_measurableSet_eq _ hA, trim_measurableSet_eq _ hA,
    ← Measure.map_apply (measurable_flips N) hS, hmap, horizonMeasure,
    Measure.map_apply (measurable_flips N) hS]

/-- **Every pricing measure gives a European payoff its tree price.** For `S₀ > 0` under
no-arbitrage, a cash flow at `T`, on step `N`, paying `g` of the spot at `T`, has the price
`binomialPrice u d ρ g N S₀` under every pricing measure of the binomial market at the horizon `T`,
whatever the physical law: the discounted payoff depends on the first `N` flips only, on which every
pricing measure is the risk-neutral law (`trim_eq_of_isPricingMeasure`). -/
theorem price_pay_eq_binomialPrice_of_isPricingMeasure (hS₀ : 0 < S₀) (hna : BinomialNoArb u d ρ)
    (hqcrr : crrUpProb u d ρ = q) (hh : 0 < h) (hTN : (T : ℝ) / h = N) {a : Payoff Unit}
    {g : ℝ → ℝ} (hg : ∀ s : Scenario Unit, a.eval s = g (s () T))
    (hQ : (market P S₀ u d ρ hh.le).IsPricingMeasure T Q) :
    (market P S₀ u d ρ hh.le).price Q (.pay T a) = binomialPrice u d ρ g N S₀ := by
  have hq : q ≤ 1 := by
    have := (crrUpProb_mem_Ioo hna).2
    rw [hqcrr] at this
    exact_mod_cast this.le
  have hfl : ⌊(T : ℝ) / h⌋₊ = N := by rw [hTN, Nat.floor_natCast]
  have hgrid : ∀ t ∈ (Contract.pay T a).dates, ∃ n : ℕ, (t : ℝ) / h = n := fun t ht ↦
    ⟨N, by rw [show t = T by simpa [Contract.dates] using ht]; exact hTN⟩
  have hF : StronglyMeasurable[flipFiltration N]
      fun ω ↦ discount ρ h T * a.eval (scenarioAt (assets S₀ u d h) ω) := by
    refine stronglyMeasurable_flipFiltration_iff.2 fun ω ω' hω ↦ ?_
    simp only [hg, scenarioAt, assets, hfl]
    rw [pathAdaptedAt_spotPath S₀ u d N ω ω' hω]
  calc (market P S₀ u d ρ hh.le).price Q (.pay T a)
      = ∫ ω, discount ρ h T * a.eval (scenarioAt (assets S₀ u d h) ω) ∂Q := by
        rw [price_market P Q S₀ hh.le (c := .pay T a) trivial hgrid, Contract.value_pay]
    _ = ∫ ω, discount ρ h T * a.eval (scenarioAt (assets S₀ u d h) ω) ∂coinFlipMeasure q hq := by
        rw [integral_trim (flipFiltration.le N) hF, integral_trim (flipFiltration.le N) hF,
          trim_eq_of_isPricingMeasure hq hS₀ hna hqcrr hh hfl hQ]
    _ = binomialPrice u d ρ g N S₀ := by
        rw [← value_pay_eq_binomialPrice hq hqcrr S₀ hTN hg, Contract.value_pay]

/-- **The fundamental theorem of asset pricing for the binomial market.** For `S₀ > 0`,
`0 < d < u`, a step `h > 0` and a horizon of `N ≥ 1` steps, under the physical law of i.i.d. flips
going up with any probability `0 < p < 1`, the market has a pricing measure exactly when
`d < e^ρ < u`. A pricing measure maps to an equivalent martingale measure of the `N`-period tree,
which rules out the one-period arbitrage of `binomialNoArb_of_noArbitrage`; conversely the
risk-neutral law is one (`isPricingMeasure_coinFlipMeasure`). -/
theorem exists_isPricingMeasure_iff (hS₀ : 0 < S₀) (hd : 0 < d) (hdu : d < u) (hh : 0 < h)
    {p : ℝ≥0} (hp0 : 0 < p) (hp : p < 1) (hN : 0 < N) (hTN : (T : ℝ) / h = N) :
    (∃ Q, (market (coinFlipMeasure p hp.le) S₀ u d ρ hh.le).IsPricingMeasure T Q)
      ↔ BinomialNoArb u d ρ := by
  have hfl : ⌊(T : ℝ) / h⌋₊ = N := by rw [hTN, Nat.floor_natCast]
  refine ⟨fun ⟨Q, hQ⟩ ↦ ?_, fun hna ↦ ?_⟩
  · have := hQ.isProb
    obtain ⟨h₁, h₂⟩ := map_flips_equiv_of_isPricingMeasure hh hfl hQ
    exact binomialNoArb_of_noArbitrage hS₀ hd hdu hN hp0 hp
      (isEMM_horizonSpot_map (P := horizonMeasure N p hp.le) ⟨inferInstance, h₁, h₂⟩
        (martingale_discountedSpot_of_isPricingMeasure hh hfl hQ)).noArbitrage
  · obtain ⟨q, hq, hqcrr⟩ := hna.exists_nnreal_crrUpProb
    exact ⟨_, isPricingMeasure_coinFlipMeasure hq hna hqcrr S₀ hh.le hp0 hp T⟩

end MathFin.Contracts.Binomial
