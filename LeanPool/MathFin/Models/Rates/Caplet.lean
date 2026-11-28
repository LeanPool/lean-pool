/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.BlackScholes.Forward
public import LeanPool.MathFin.Models.Rates.ShortRate
public import LeanPool.MathFin.Models.Rates.FRA
public import LeanPool.MathFin.Pricing.ForwardMeasure
public import LeanPool.MathFin.Models.Forwards.Black76
public import LeanPool.MathFin.Pricing.Market

/-!
# Caplets and caps, on the bond prices of a stochastic discount factor

`bondPrice Q 𝓕 D t T = 𝔼_Q[D T | 𝓕 t] / D t` is the zero-coupon bond price `P(t, T)` at time
`t`, for any stochastic discount factor `D`: the bond prices that floating payoffs need. A
model `X` carries them as observed processes. `BondModel` says the underlying `b` is
`P(T₀, T₁)` at `T₀` (a.e.) and `ℓ` is the simple forward rate it implies,
`L = (1/P − 1)/δ` (`fraForwardRate 1 P δ`), adapted to the information at `T₀`.

* A **caplet** pays `δ (L(T₀, T₁) − K)⁺` at `T₁` (`caplet`, a one-cash-flow `Contract`). In
  every `BondModel` it is worth `(1 + δK)` puts on `P(T₀, T₁)`, struck at `1/(1 + δK)` and
  expiring at `T₀` (`value_caplet_eq_bondPut`): the tower property turns the discount factor
  `D T₁` into `D T₀ · P(T₀, T₁)`, and `P · δ (L − K)⁺ = (1 − (1 + δK) P)⁺`.
* A **cap** is its schedule of caplets (`cap`), worth their sum (`value_cap`), hence
  `(1 + δK)` times a strip of bond puts (`value_cap_eq_bondPuts`).
* **Black-76.** If `L(T₀, T₁)` is lognormal under the `T₁`-forward measure
  (`forwardMeasure`), the caplet is worth `P(0, T₁) · blackCaplet F K σ T δ`
  (`value_caplet_black76`), consuming `black_futures_formula` and the change of numéraire
  `forwardMeasure_price`; with a `BondModel`, `F` is the forward rate of the zero curve
  (`BondModel.integral_libor_forward`, `value_caplet_black76_forwardRate`).

## What is not here

Lognormality of `L` under the forward measure is a hypothesis here. It does not hold in the
Gaussian short-rate models (a remark, not a theorem here): the bond `P` is lognormal
(`bondPrice_vasicek`, `bondPrice_hullWhite`), so `L = (1/P − 1)/δ` is a shifted lognormal. There
the caplet is priced through the bond put, as a Black put on the lognormal bond
(`Models/Rates/Jamshidian.lean`), in the Vasicek, Hull–White and two-piece GSR models. CMS
rates and swaptions are in `Models/Rates/CMSContract.lean`: a swap rate is a ratio of bond-price
sums,
which `Payoff` cannot express, so it is an observed underlying tied to the bond prices by a model
hypothesis.

## Main definitions

* `bondPrice`, `HasBondPrice` (the bond price alone), `BondModel` (with the forward rate),
  `capletPayoff`, `caplet`, `bondPut`, `cap`.

## Main results

* `integral_discount_mul_eq_forward` (pricing at the forward measure),
  `HasBondPrice.integral_discount` and `HasBondPrice.integral_discount_mul` (the tower property),
  `bond_mul_capletPayoff`, `value_caplet_eq_bondPut`, `value_cap`,
  `value_cap_eq_bondPuts`, `value_caplet_black76`, `BondModel.integral_libor_forward`,
  `value_caplet_black76_forwardRate`.

## References

* [P. Bilokon, *The Contract Is Not the Model*][Bilokon2026]
* [D. Brigo and F. Mercurio, *Interest Rate Models --- Theory and Practice*][BrigoMercurio2006],
  sections 1.4 and 1.5
* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], ch. 29
* [Musiela and Rutkowski, *Martingale Methods in Financial Modelling*][MusielaRutkowski], ch. 12

## Tags

caplet, interest rate cap, LIBOR, Black-76, forward measure, bond put, forward rate, MSC 91G30,
JEL G13, JEL E43
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MathFin.Contracts

variable {ι Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### The bond price at time `t`, and the caplet as a contract -/

/-- The **zero-coupon bond price at time `t`** under the stochastic discount factor `D`:
`P(t, T) = 𝔼_Q[D T | 𝓕 t] / D t`, the value at `t` of one unit paid at `T`. At `t = 0` with
`D 0 = 1` and a trivial `𝓕 0` it is the zero curve `zeroCurve Q D T`. -/
noncomputable def bondPrice (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (D : ℝ≥0 → Ω → ℝ)
    (t T : ℝ≥0) : Ω → ℝ :=
  fun ω ↦ (Q[D T | 𝓕 t]) ω / D t ω

/-- **The bond price is the price at `t` of one unit paid at `T`**: in a market whose deflator
`N 0 / N t` is the discount factor, `P(t, T)` is `Market.priceAt` of the payment of `1` at `T`. -/
theorem bondPrice_deflator_eq_priceAt (M : Market ι Ω) (Q : Measure Ω) (t T : ℝ≥0) :
    bondPrice Q M.𝓕 M.deflator t T = M.priceAt Q t (.pay T (.const 1)) := by
  funext ω
  simp [Market.priceAt, bondPrice, Contract.pathPV, Contract.cashflows, Payoff.eval]

/-- The payoff of a **caplet**: `δ (L − K)⁺`, where the underlying `ℓ` carries the
simply-compounded forward rate `L(T₀, T₁)`, observed at its reset date `T₀`. -/
noncomputable def capletPayoff (ℓ : ι) (T₀ : ℝ≥0) (δ K : ℝ) : Payoff ι :=
  .mul (.const δ) (.max (.sub (.obs ℓ T₀) (.const K)) (.const 0))

/-- A **caplet**: pays `δ (L(T₀, T₁) − K)⁺` at `T₁`, with accrual `δ` and rate `L` observed at
`T₀`. -/
noncomputable def caplet (ℓ : ι) (T₀ T₁ : ℝ≥0) (δ K : ℝ) : Contract ι :=
  .pay T₁ (capletPayoff ℓ T₀ δ K)

/-- A **put on a zero-coupon bond**: pays `(k − P(T, ·))⁺` at its expiry `T`, where the
underlying `b` carries the bond price observed at `T`. -/
noncomputable def bondPut (b : ι) (T : ℝ≥0) (k : ℝ) : Contract ι :=
  .pay T (.max (.sub (.const k) (.obs b T)) (.const 0))

/-- A **cap**: the schedule of caplets with reset dates `T 0, …, T (n − 1)`, caplet `i` paying
`δ (Lᵢ − K)⁺` at `T (i + 1)`, where `ℓ i` carries the rate `L(T i, T (i + 1))`. -/
noncomputable def cap (ℓ : ℕ → ι) (T : ℕ → ℝ≥0) (δ K : ℝ) (n : ℕ) : Contract ι :=
  payFlows (fun i ↦ T (i + 1)) (fun i ↦ capletPayoff (ℓ i) (T i) δ K) n

/-- **A model with a bond price.** The underlying `b` carries the bond price `P(T₀, T₁)` at `T₀`,
the conditional expectation `bondPrice` of the stochastic discount factor `D` given the
information `𝓕`, as a process of the model `X`. -/
structure HasBondPrice (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (D : ℝ≥0 → Ω → ℝ)
    (X : ι → ℝ≥0 → Ω → ℝ) (b : ι) (T₀ T₁ : ℝ≥0) : Prop where
  D_pos : ∀ ω, 0 < D T₀ ω
  integrable_D : Integrable (D T₁) Q
  bond_eq : X b T₀ =ᵐ[Q] bondPrice Q 𝓕 D T₀ T₁

/-- **A model with bond prices and forward rates.** Besides the bond price `P(T₀, T₁)`, the
process `ℓ` carries the simply-compounded forward rate `L(T₀, T₁) = (1/P(T₀, T₁) − 1)/δ` it
implies, adapted to the information `𝓕 T₀`. -/
structure BondModel (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (D : ℝ≥0 → Ω → ℝ)
    (X : ι → ℝ≥0 → Ω → ℝ) (b ℓ : ι) (T₀ T₁ : ℝ≥0) (δ : ℝ) : Prop
    extends HasBondPrice Q 𝓕 D X b T₀ T₁ where
  δ_pos : 0 < δ
  bond_pos : ∀ᵐ ω ∂Q, 0 < X b T₀ ω
  libor_eq : X ℓ T₀ =ᵐ[Q] fun ω ↦ fraForwardRate 1 (X b T₀ ω) δ
  libor_meas : StronglyMeasurable[𝓕 T₀] (X ℓ T₀)

variable {Q : Measure Ω} [IsProbabilityMeasure Q] {𝓕 : Filtration ℝ≥0 mΩ} {D : ℝ≥0 → Ω → ℝ}
  {X : ι → ℝ≥0 → Ω → ℝ} {b ℓ : ι} {T₀ T₁ : ℝ≥0} {δ : ℝ}

/-- **Pricing at the forward measure.** For a positive integrable discount factor `D₀`, its
expectation is positive, and `𝔼[D₀ · Y] = 𝔼[D₀]·𝔼^{Q^{D₀}}[Y]` for the forward measure
`forwardMeasure Q (1/D₀)`: the change of numéraire `forwardMeasure_price`, written for the
discount factor instead of the bank account. -/
theorem integral_discount_mul_eq_forward {D₀ : Ω → ℝ} (hD : ∀ ω, 0 < D₀ ω)
    (hDm : Measurable D₀) (hDi : Integrable D₀ Q) (Y : Ω → ℝ) :
    0 < ∫ ω, D₀ ω ∂Q ∧ (∫ ω, D₀ ω ∂Q) * ∫ ω, Y ω ∂(forwardMeasure Q fun ω ↦ 1 / D₀ ω)
      = ∫ ω, D₀ ω * Y ω ∂Q := by
  have hB : ∀ ω, 0 < 1 / D₀ ω := fun ω ↦ one_div_pos.2 (hD ω)
  have e1 : ∫ ω, 1 / (1 / D₀ ω) ∂Q = ∫ ω, D₀ ω ∂Q := by simp
  have hP0 := integral_one_div_pos (Q := Q) hB (by simpa using hDi)
  rw [e1] at hP0
  have key := forwardMeasure_price (Q := Q) (B := fun ω ↦ 1 / D₀ ω) Y
    (measurable_const.div hDm) hB (by simpa using hP0)
  rw [e1] at key
  refine ⟨hP0, key.trans (integral_congr_ae <| ae_of_all _ fun ω ↦ ?_)⟩
  field_simp [(hD ω).ne']

omit [IsProbabilityMeasure Q] in
/-- **A discounted bond price is the discount factor at the payment date, in expectation**:
`D T₀ · P(T₀, T₁)` is a version of `𝔼[D T₁ | 𝓕 T₀]`. -/
theorem HasBondPrice.discount_mul_ae (h : HasBondPrice Q 𝓕 D X b T₀ T₁) :
    (fun ω ↦ D T₀ ω * X b T₀ ω) =ᵐ[Q] Q[D T₁ | 𝓕 T₀] := by
  filter_upwards [h.bond_eq] with ω hω
  rw [hω, bondPrice]
  field_simp [(h.D_pos ω).ne']

omit [IsProbabilityMeasure Q] in
theorem HasBondPrice.integrable_discount_mul (h : HasBondPrice Q 𝓕 D X b T₀ T₁) :
    Integrable (fun ω ↦ D T₀ ω * X b T₀ ω) Q :=
  (integrable_condExp (m := 𝓕 T₀) (f := D T₁)).congr h.discount_mul_ae.symm

/-- **The tower property**: `𝔼[D T₀ · P(T₀, T₁)] = P(0, T₁)`, the zero curve. -/
theorem HasBondPrice.integral_discount (h : HasBondPrice Q 𝓕 D X b T₀ T₁) :
    ∫ ω, D T₀ ω * X b T₀ ω ∂Q = zeroCurve Q D T₁ := by
  rw [integral_congr_ae h.discount_mul_ae, integral_condExp (𝓕.le T₀)]
  rfl

/-- **The bond price turns `D T₁` into `D T₀`**: for an `𝓕 T₀`-measurable `Y`,
`𝔼[D T₁ · Y] = 𝔼[D T₀ · P(T₀, T₁) · Y]`. -/
theorem HasBondPrice.integral_discount_mul (h : HasBondPrice Q 𝓕 D X b T₀ T₁) {Y : Ω → ℝ}
    (hY : StronglyMeasurable[𝓕 T₀] Y) (hDY : Integrable (fun ω ↦ D T₁ ω * Y ω) Q) :
    ∫ ω, D T₁ ω * Y ω ∂Q = ∫ ω, D T₀ ω * X b T₀ ω * Y ω ∂Q := by
  have hcond : Q[fun ω ↦ Y ω * D T₁ ω | 𝓕 T₀] =ᵐ[Q] fun ω ↦ Y ω * (Q[D T₁ | 𝓕 T₀]) ω :=
    condExp_mul_of_stronglyMeasurable_left hY
      (hDY.congr (ae_of_all _ fun ω ↦ mul_comm _ _)) h.integrable_D
  calc ∫ ω, D T₁ ω * Y ω ∂Q = ∫ ω, Y ω * D T₁ ω ∂Q := by simp_rw [mul_comm]
    _ = ∫ ω, (Q[fun ω ↦ Y ω * D T₁ ω | 𝓕 T₀]) ω ∂Q := (integral_condExp (𝓕.le T₀)).symm
    _ = ∫ ω, Y ω * (Q[D T₁ | 𝓕 T₀]) ω ∂Q := integral_congr_ae hcond
    _ = ∫ ω, D T₀ ω * X b T₀ ω * Y ω ∂Q := integral_congr_ae <| by
        filter_upwards [h.discount_mul_ae] with ω hω
        rw [hω]; ring

/-- **The caplet payoff, valued at its reset date, is a bond put**: when `δ L = 1/P - 1`,
`P · δ (L - K)⁺ = (1 + δK) (1/(1 + δK) - P)⁺`. -/
lemma bond_mul_capletPayoff {P δ K : ℝ} (hP : 0 < P) (hδ : 0 < δ) (hK : 0 < 1 + δ * K) :
    P * (δ * max (fraForwardRate 1 P δ - K) 0) = (1 + δ * K) * max (1 / (1 + δ * K) - P) 0 := by
  have h : P * (δ * (fraForwardRate 1 P δ - K)) = (1 + δ * K) * (1 / (1 + δ * K) - P) := by
    unfold fraForwardRate
    field_simp
    ring
  rw [mul_max_of_nonneg _ _ hδ.le, mul_max_of_nonneg _ _ hP.le, mul_max_of_nonneg _ _ hK.le]
  simpa using congrArg (max · 0) h

/-- **A caplet is a multiple of a put on the bond** (the caplet–bond-put identity). In a model with
bond prices, the caplet paying `δ (L(T₀, T₁) − K)⁺` at `T₁` is worth `(1 + δK)` puts on
`P(T₀, T₁)` struck at `1/(1 + δK)` and expiring at `T₀`: pay `P(T₀, T₁) · δ (L − K)⁺` at `T₀`,
which is `(1 − (1 + δK) P)⁺`, since `δ L = 1/P − 1`. The bond price `P(T₀, T₁)` is the
conditional expectation `bondPrice` of the discount factor, not a deterministic curve. -/
theorem value_caplet_eq_bondPut (h : BondModel Q 𝓕 D X b ℓ T₀ T₁ δ) {K : ℝ}
    (hK : 0 < 1 + δ * K)
    (hint : Integrable (fun ω ↦ D T₁ ω * (δ * max (X ℓ T₀ ω - K) 0)) Q) :
    (caplet ℓ T₀ T₁ δ K).value Q D X
      = (1 + δ * K) * (bondPut b T₀ (1 / (1 + δ * K))).value Q D X := by
  have hY : StronglyMeasurable[𝓕 T₀] fun ω ↦ δ * max (X ℓ T₀ ω - K) 0 :=
    (show Continuous fun x : ℝ ↦ δ * max (x - K) 0 by fun_prop).comp_stronglyMeasurable
      h.libor_meas
  simp only [caplet, bondPut, Contract.value_pay, capletPayoff, Payoff.eval, scenarioAt]
  rw [h.integral_discount_mul hY hint, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [h.libor_eq, h.bond_pos] with ω hL hP
  rw [hL, mul_assoc, bond_mul_capletPayoff hP h.δ_pos hK]
  ring

/-! ### Caps, and the Black-76 caplet -/

omit [IsProbabilityMeasure Q] in
/-- **A cap is the sum of its caplets**, in every model in which each caplet's discounted payoff
is integrable. -/
theorem value_cap (ℓ : ℕ → ι) (T : ℕ → ℝ≥0) (δ K : ℝ) (n : ℕ)
    (hint : ∀ i < n, Integrable
      (fun ω ↦ D (T (i + 1)) ω * (δ * max (X (ℓ i) (T i) ω - K) 0)) Q) :
    (cap ℓ T δ K n).value Q D X
      = ∑ i ∈ Finset.range n, (caplet (ℓ i) (T i) (T (i + 1)) δ K).value Q D X :=
  Contract.value_payFlows Q D X _ _ n fun i hi ↦ by
    simpa [capletPayoff, Payoff.eval, scenarioAt] using hint i hi

/-- **A cap is `(1 + δK)` times a strip of bond puts.** In a model with bond prices at each
reset date, the cap with accrual `δ` and strike `K` is worth `(1 + δK)` times the sum of the
puts on `P(Tᵢ, Tᵢ₊₁)` struck at `1/(1 + δK)` and expiring at `Tᵢ`. -/
theorem value_cap_eq_bondPuts (b ℓ : ℕ → ι) (T : ℕ → ℝ≥0) {δ K : ℝ} (n : ℕ)
    (h : ∀ i < n, BondModel Q 𝓕 D X (b i) (ℓ i) (T i) (T (i + 1)) δ) (hK : 0 < 1 + δ * K)
    (hint : ∀ i < n, Integrable
      (fun ω ↦ D (T (i + 1)) ω * (δ * max (X (ℓ i) (T i) ω - K) 0)) Q) :
    (cap ℓ T δ K n).value Q D X
      = (1 + δ * K) * ∑ i ∈ Finset.range n,
          (bondPut (b i) (T i) (1 / (1 + δ * K))).value Q D X := by
  rw [value_cap ℓ T δ K n hint, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i hi ↦
    value_caplet_eq_bondPut (h i (Finset.mem_range.1 hi)) hK (hint i (Finset.mem_range.1 hi))

/-- **The caplet is `P(0, T₁)` times a Black-76 call on the forward rate**, under the
`T₁`-forward measure `Q'` (`forwardMeasure` for the bank account `1/D T₁`). If the simple rate
`L(T₀, T₁)` is lognormal there, `L = bsTerminal F 0 σ T Z` with `Z` standard normal, then the
caplet is worth `P(0, T₁) · δ · [F Φ(d₁) − K Φ(d₂)]`, which is `blackCaplet`
(`Models/Forwards/Black76.lean`). The lognormality of `L` under `Q'` is a hypothesis, not derived
from a short-rate model, and `F` is the mean of `L` under `Q'`. -/
theorem value_caplet_black76 {Q' : Measure Ω} [IsProbabilityMeasure Q']
    (hQ' : Q' = forwardMeasure Q fun ω ↦ 1 / D T₁ ω) (hD : ∀ ω, 0 < D T₁ ω)
    (hDm : Measurable (D T₁)) (hDi : Integrable (D T₁) Q) {F K σ T : ℝ} {Z : Ω → ℝ}
    (hZ : BSCallHyp Q' F K 0 σ T Z)
    (hL : X ℓ T₀ =ᵐ[Q'] fun ω ↦ bsTerminal F 0 σ T (Z ω)) :
    (caplet ℓ T₀ T₁ δ K).value Q D X = zeroCurve Q D T₁ * blackCaplet F K σ T δ := by
  subst hQ'
  obtain ⟨-, key⟩ := integral_discount_mul_eq_forward hD hDm hDi
    (fun ω ↦ δ * max (X ℓ T₀ ω - K) 0)
  have e3 : ∫ ω, δ * max (X ℓ T₀ ω - K) 0 ∂forwardMeasure Q (fun ω ↦ 1 / D T₁ ω)
      = δ * (F * Phi (bsd1 F K 0 σ T) - K * Phi (bsd2 F K 0 σ T)) := by
    rw [← show ∫ ω, max (bsTerminal F 0 σ T (Z ω) - K) 0 ∂forwardMeasure Q (fun ω ↦ 1 / D T₁ ω)
        = F * Phi (bsd1 F K 0 σ T) - K * Phi (bsd2 F K 0 σ T) by
      simpa using black_futures_formula hZ 0, ← integral_const_mul]
    exact integral_congr_ae (hL.mono fun ω hω ↦ by simp only [hω])
  simp only [caplet, Contract.value_pay, capletPayoff, Payoff.eval, scenarioAt, blackCaplet]
  rw [← key, e3]
  rfl

/-- **The forward rate has the forward rate of the zero curve as its mean at its own forward
measure**: `𝔼^{T₁}[L(T₀, T₁)] = (P(0, T₀)/P(0, T₁) − 1)/δ` (`fraForwardRate`). -/
theorem BondModel.integral_libor_forward (h : BondModel Q 𝓕 D X b ℓ T₀ T₁ δ)
    {Q' : Measure Ω} (hQ' : Q' = forwardMeasure Q fun ω ↦ 1 / D T₁ ω) (hD : ∀ ω, 0 < D T₁ ω)
    (hDm : Measurable (D T₁)) (hD0 : Integrable (D T₀) Q)
    (hint : Integrable (fun ω ↦ D T₁ ω * X ℓ T₀ ω) Q) :
    ∫ ω, X ℓ T₀ ω ∂Q' = fraForwardRate (zeroCurve Q D T₀) (zeroCurve Q D T₁) δ := by
  subst hQ'
  have hδ := h.δ_pos
  obtain ⟨hpos, key⟩ := integral_discount_mul_eq_forward hD hDm h.integrable_D (X ℓ T₀)
  have e3 : ∫ ω, D T₁ ω * X ℓ T₀ ω ∂Q = (zeroCurve Q D T₀ - zeroCurve Q D T₁) / δ := by
    rw [h.integral_discount_mul h.libor_meas hint]
    rw [← h.integral_discount, zeroCurve, ← integral_sub hD0 h.integrable_discount_mul,
      ← integral_div]
    refine integral_congr_ae ?_
    filter_upwards [h.libor_eq, h.bond_pos] with ω hL hP
    rw [hL, fraForwardRate]
    field_simp [hP.ne', hδ.ne']
  rw [e3] at key
  have hz : zeroCurve Q D T₁ = ∫ ω, D T₁ ω ∂Q := rfl
  rw [hz] at key ⊢
  rw [fraForwardRate]
  field_simp [hpos.ne', hδ.ne'] at key ⊢
  linear_combination key

/-- **The Black-76 caplet formula, at the forward rate of the zero curve.** Under the hypotheses
of `value_caplet_black76` and a model with bond prices, the caplet is worth
`P(0, T₁) · blackCaplet F K σ T δ` with `F = (P(0, T₀)/P(0, T₁) − 1)/δ`, the forward rate of the
zero curve. -/
theorem value_caplet_black76_forwardRate (h : BondModel Q 𝓕 D X b ℓ T₀ T₁ δ)
    {Q' : Measure Ω} [IsProbabilityMeasure Q']
    (hQ' : Q' = forwardMeasure Q fun ω ↦ 1 / D T₁ ω) (hD : ∀ ω, 0 < D T₁ ω)
    (hDm : Measurable (D T₁)) (hD0 : Integrable (D T₀) Q)
    (hint : Integrable (fun ω ↦ D T₁ ω * X ℓ T₀ ω) Q) {K σ T : ℝ} {Z : Ω → ℝ}
    {F : ℝ} (hZ : BSCallHyp Q' F K 0 σ T Z)
    (hL : X ℓ T₀ =ᵐ[Q'] fun ω ↦ bsTerminal F 0 σ T (Z ω)) :
    (caplet ℓ T₀ T₁ δ K).value Q D X
      = zeroCurve Q D T₁ * blackCaplet
          (fraForwardRate (zeroCurve Q D T₀) (zeroCurve Q D T₁) δ) K σ T δ := by
  have hF : F = fraForwardRate (zeroCurve Q D T₀) (zeroCurve Q D T₁) δ := by
    rw [← h.integral_libor_forward hQ' hD hDm hD0 hint, integral_congr_ae hL]
    simpa using (discounted_terminal_eq_S0 hZ).symm
  rw [← hF]
  exact value_caplet_black76 hQ' hD hDm h.integrable_D hZ hL

end MathFin.Contracts
