/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Rates.VasicekBondPriceAt
public import LeanPool.MathFin.Probability.Brownian.Ito.ItoIntegralL2
public import LeanPool.MathFin.Pricing.Market

/-!
# The Vasicek bond market

The Vasicek bond market uses a stochastic bank-account numéraire built from the
Wiener-integral integrated-rate formula. The zero-coupon bond of maturity `T` is the
traded asset (`Rates.vasicekMarket`). The model uses the reference measure `μ` as its pricing
measure. The drift `θ` and short-rate dynamics are specified under that measure.

The information is the natural filtration of the Brownian motion `B`. The short rate and the
integrated rate are Wiener integrals, that is, classes in `L²(μ)`, which are `𝓕_t`-measurable only
almost surely (`wienerIntegralLp_mem_lpMeas`), whereas a `Market` asks for exact strong
adaptedness. The market therefore uses the `𝓕_t`-measurable representatives
`μ[· | 𝓕_t]` of the Wiener integrals (`vasicekBankAccount`, `vasicekShortRate`): a Wiener
integral that is almost surely `𝓕_t`-measurable is almost surely its own conditional expectation
(`condExp_of_aestronglyMeasurable'`), so the representatives change nothing but a null set.

Before `T` the bond is worth `P(t, T) = A(T − t) exp(−B(T − t) r_t)` (`vasicekBondPriceRep`). After
`T` its proceeds are held in the bank account, so the asset is `N_t P(t∧T, T) / N_{t∧T}`, and the
deflated asset frozen at `T` is `P(t∧T, T) / N_{t∧T}`.

## Main definitions

* `MathFin.Rates.vasicekBankAccount`: the exponential of the `𝓕_t`-measurable
  representative of the Wiener-integral integrated-rate formula.
* `MathFin.Rates.vasicekShortRate`: the short rate `r_t`, through the `𝓕_t`-measurable
  representative of its diffusion term.
* `MathFin.Rates.vasicekBondPriceRep`: the bond price `A(T − t) exp(−B(T − t) r_t)`.
* `MathFin.Rates.vasicekMarket`: the market of the bank account and the zero-coupon bond.

## Main results

* `MathFin.Rates.isPricingMeasure_vasicekMarket`: the reference measure prices the market at the
  horizon `T`. The deflated bond frozen at `T` is the conditional expectation of the
  terminal discount from `vasicekIntegratedRate` (`vasicekBondPrice_condExp`), a Doob martingale.
* `MathFin.Rates.price_pay_vasicekMarket`: the market price of one unit paid at `T` is the Vasicek
  bond price `A(T) exp(−B(T) r₀)`.

## References

* [D. Brigo and F. Mercurio, *Interest Rate Models --- Theory and Practice*][BrigoMercurio2006],
  section 3.2.1
* [O. Vasicek, *An equilibrium characterization of the term structure*][Vasicek1977]

## Tags

Vasicek model, bond market, bank account, stochastic numéraire, pricing measure, short rate,
MSC 91G30, MSC 60H05, JEL E43, JEL G12
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real MathFin MathFin.Contracts
open scoped NNReal
open ItoIntegralL2

namespace MathFin.Rates

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
  [IsProbabilityMeasure μ] (hB : IsPreBrownianReal B μ) (hBm : ∀ s, Measurable (B s))
  (r₀ θ σ : ℝ) {κ : ℝ} (hκ : 0 < κ)

/-- **The bank account** through the `𝓕_t`-measurable representative
`μ[∫₀ᵗ r | 𝓕_t]` of the integrated rate. -/
noncomputable def vasicekBankAccount (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (μ[vasicekIntegratedRate hB r₀ θ σ hκ t | natFiltration hBm t] ω)

/-- **The short rate** `r_t = m_t + σ ∫₀ᵗ e^{−κ(t−u)} dB_u`, through the `𝓕_t`-measurable
representative of the Wiener integral. -/
noncomputable def vasicekShortRate (t : ℝ≥0) (ω : Ω) : ℝ :=
  vasicekSDEMean r₀ θ κ t + μ[vasicekDiffusionTerm hB κ σ hκ.le t | natFiltration hBm t] ω

/-- **The Vasicek bond price at `t ≤ T`**, `A(T − t) exp(−B(T − t) r_t)`. -/
noncomputable def vasicekBondPriceRep (T t : ℝ≥0) (ω : Ω) : ℝ :=
  vasicekBondA θ σ κ ((T - t : ℝ≥0) : ℝ)
    * Real.exp (-(vasicekBondB κ ((T - t : ℝ≥0) : ℝ) * vasicekShortRate hB hBm r₀ θ σ hκ t ω))

lemma aestronglyMeasurable_vasicekIntegratedRate (t : ℝ≥0) :
    AEStronglyMeasurable[natFiltration hBm t] (vasicekIntegratedRate hB r₀ θ σ hκ t) μ :=
  ((mem_lpMeas_iff_aestronglyMeasurable.1
    (wienerIntegralLp_mem_lpMeas hB hBm (t := t)
      (vasicekIntegratedKernelLp hκ t))).const_mul σ).const_add _

lemma aestronglyMeasurable_vasicekDiffusionTerm (t : ℝ≥0) :
    AEStronglyMeasurable[natFiltration hBm t] (vasicekDiffusionTerm hB κ σ hκ.le t) μ :=
  (mem_lpMeas_iff_aestronglyMeasurable.1
    (wienerIntegralLp_mem_lpMeas hB hBm (t := t)
      (vasicekKernelLp κ hκ.le t))).const_mul σ

lemma integrable_vasicekIntegratedRate (t : ℝ≥0) :
    Integrable (vasicekIntegratedRate hB r₀ θ σ hκ t) μ :=
  (integrable_const _).add (((Lp.memLp _).integrable one_le_two).const_mul σ)

lemma integrable_vasicekDiffusionTerm (t : ℝ≥0) :
    Integrable (vasicekDiffusionTerm hB κ σ hκ.le t) μ :=
  ((Lp.memLp _).integrable one_le_two).const_mul σ


omit [IsProbabilityMeasure μ] in
lemma vasicekIntegratedRate_zero_ae :
    ∀ᵐ ω ∂μ, vasicekIntegratedRate hB r₀ θ σ hκ 0 ω = 0 := by
  have hf : vasicekIntegratedKernelLp hκ 0 = 0 :=
    Lp.eq_zero_iff_ae_eq_zero.mpr (by
      simp only [NNReal.coe_zero, lt_self_iff_false, not_false_eq_true, Set.Ioc_eq_empty,
        Measure.restrict_empty, ae_zero]
      exact Filter.eventually_bot)
  have h : WienerIntegralL2.wienerIntegralLp B hB 0 (vasicekIntegratedKernelLp hκ 0) = 0 := by
    rw [hf, map_zero]
  filter_upwards [Lp.coeFn_zero ℝ 2 μ] with ω hω
  rw [vasicekIntegratedRate, h, hω]
  simp [vasicekIntegratedMean, vasicekBondB]

/-- The bank account is almost surely the exponential of the Wiener-form integrated rate.
The Wiener integral agrees almost surely with its `𝓕_t`-measurable representative. -/
lemma vasicekBankAccount_ae_eq (t : ℝ≥0) :
    vasicekBankAccount hB hBm r₀ θ σ hκ t
      =ᵐ[μ] fun ω ↦ Real.exp (vasicekIntegratedRate hB r₀ θ σ hκ t ω) :=
  (condExp_of_aestronglyMeasurable' ((natFiltration hBm).le t)
    (aestronglyMeasurable_vasicekIntegratedRate hB hBm r₀ θ σ hκ t)
    (integrable_vasicekIntegratedRate hB r₀ θ σ hκ t)).fun_comp Real.exp

/-- The short rate is almost surely `m_t + σ ∫₀ᵗ e^{−κ(t−u)} dB_u`. -/
lemma vasicekShortRate_ae_eq (t : ℝ≥0) :
    vasicekShortRate hB hBm r₀ θ σ hκ t
      =ᵐ[μ] fun ω ↦ vasicekSDEMean r₀ θ κ t + vasicekDiffusionTerm hB κ σ hκ.le t ω :=
  (condExp_of_aestronglyMeasurable' ((natFiltration hBm).le t)
    (aestronglyMeasurable_vasicekDiffusionTerm hB hBm σ hκ t)
    (integrable_vasicekDiffusionTerm hB σ hκ t)).fun_comp (vasicekSDEMean r₀ θ κ t + ·)

omit [IsProbabilityMeasure μ] in
lemma stronglyMeasurable_vasicekBankAccount (t : ℝ≥0) :
    StronglyMeasurable[natFiltration hBm t] (vasicekBankAccount hB hBm r₀ θ σ hκ t) :=
  Real.continuous_exp.comp_stronglyMeasurable stronglyMeasurable_condExp

omit [IsProbabilityMeasure μ] in
lemma stronglyMeasurable_vasicekBondPriceRep (T t : ℝ≥0) :
    StronglyMeasurable[natFiltration hBm t] (vasicekBondPriceRep hB hBm r₀ θ σ hκ T t) :=
  stronglyMeasurable_const.mul (Real.continuous_exp.comp_stronglyMeasurable
    (stronglyMeasurable_const.mul (stronglyMeasurable_const.add stronglyMeasurable_condExp)).neg)

/-- **The Vasicek bond market**: the information is the natural filtration of `B`, the numéraire
is the bank account `exp ∫₀ᵗ r`, and the one asset is the zero-coupon bond of maturity `T`, worth
`A(T − t) exp(−B(T − t) r_t)` before `T` and, after `T`, its proceeds held in the bank account:
`N_t P(t∧T, T) / N_{t∧T}`. The reference measure `μ` is read as the pricing measure. -/
noncomputable def vasicekMarket (T : ℝ≥0) : Market Unit Ω where
  P := μ
  𝓕 := natFiltration hBm
  asset _ t ω := vasicekBankAccount hB hBm r₀ θ σ hκ t ω
    * (vasicekBondPriceRep hB hBm r₀ θ σ hκ T (min t T) ω
      / vasicekBankAccount hB hBm r₀ θ σ hκ (min t T) ω)
  numeraire := vasicekBankAccount hB hBm r₀ θ σ hκ
  numeraire_pos _ _ := Real.exp_pos _
  asset_adapted _ t := (stronglyMeasurable_vasicekBankAccount hB hBm r₀ θ σ hκ t).mul
    (((stronglyMeasurable_vasicekBondPriceRep hB hBm r₀ θ σ hκ T _).div
      (stronglyMeasurable_vasicekBankAccount hB hBm r₀ θ σ hκ _)).mono
        ((natFiltration hBm).mono (min_le_left t T)))
  numeraire_adapted := stronglyMeasurable_vasicekBankAccount hB hBm r₀ θ σ hκ

omit [IsProbabilityMeasure μ] in
lemma deflated_vasicekMarket (T t : ℝ≥0) (ω : Ω) (i : Unit) :
    (vasicekMarket hB hBm r₀ θ σ hκ T).deflated i (min t T) ω
      = vasicekBondPriceRep hB hBm r₀ θ σ hκ T (min t T) ω
        / vasicekBankAccount hB hBm r₀ θ σ hκ (min t T) ω := by
  have h : min (min t T) T = min t T := by simp
  have := (Real.exp_pos (μ[vasicekIntegratedRate hB r₀ θ σ hκ (min t T)
    | natFiltration hBm (min t T)] ω)).ne'
  simp only [Market.deflated, vasicekMarket, h]
  field_simp

/-- **The reference measure prices the Vasicek bond market.** The deflated bond frozen at `T` is
almost surely `μ[exp(−∫₀ᵀ r) | 𝓕_{t∧T}]` (`vasicekBondPrice_condExp`), the Doob martingale of the
discount factor over `[0, T]`; `Q = μ` is trivially equivalent to the reference measure. -/
theorem isPricingMeasure_vasicekMarket (T : ℝ≥0) :
    (vasicekMarket hB hBm r₀ θ σ hκ T).IsPricingMeasure T μ := by
  refine .of_isEquivProbMeasure ⟨inferInstance, .rfl, .rfl⟩ fun i ↦ ?_
  refine (martingale_min_of_martingale (martingale_condExp
    (fun ω ↦ Real.exp (-vasicekIntegratedRate hB r₀ θ σ hκ T ω)) (natFiltration hBm) μ)
      T).congr_ae ?_ fun t ↦ ?_
  · intro t
    beta_reduce
    rw [show (vasicekMarket hB hBm r₀ θ σ hκ T).deflated i (min t T) = fun ω ↦
      vasicekBondPriceRep hB hBm r₀ θ σ hκ T (min t T) ω
        / vasicekBankAccount hB hBm r₀ θ σ hκ (min t T) ω from
      funext fun ω ↦ deflated_vasicekMarket hB hBm r₀ θ σ hκ T t ω i]
    exact (((stronglyMeasurable_vasicekBondPriceRep hB hBm r₀ θ σ hκ T _).div
      (stronglyMeasurable_vasicekBankAccount hB hBm r₀ θ σ hκ _)).mono
        ((natFiltration hBm).mono (min_le_left t T)))
  · filter_upwards [vasicekBondPrice_condExp hB hBm r₀ θ σ hκ (min_le_right t T),
      vasicekBankAccount_ae_eq hB hBm r₀ θ σ hκ (min t T),
      vasicekShortRate_ae_eq hB hBm r₀ θ σ hκ (min t T)] with ω h₁ h₂ h₃
    rw [deflated_vasicekMarket, vasicekBondPriceRep, h₃, h₂]
    refine h₁.trans ?_
    simp only [div_eq_mul_inv, ← Real.exp_neg]
    ring

/-- **The market price of one unit paid at `T` is the Vasicek bond price** `A(T) exp(−B(T) r₀)`,
under the reference measure, the pricing measure of `isPricingMeasure_vasicekMarket`: the value
of the unit payment with the stochastic deflator `N₀/N_T` built from the Wiener kernel. -/
theorem price_pay_vasicekMarket (T : ℝ≥0) :
    (vasicekMarket hB hBm r₀ θ σ hκ T).price μ (.pay T (.const 1))
      = vasicekBondA θ σ κ (T : ℝ) * Real.exp (-(vasicekBondB κ (T : ℝ) * r₀)) := by
  rw [← vasicekBondPrice_affine hB r₀ θ σ hκ T, Market.price, Contract.value_pay]
  refine integral_congr_ae ?_
  filter_upwards [vasicekBankAccount_ae_eq hB hBm r₀ θ σ hκ 0,
    vasicekBankAccount_ae_eq hB hBm r₀ θ σ hκ T,
    vasicekIntegratedRate_zero_ae hB r₀ θ σ hκ] with ω h₀ h₁ h₂
  simp [Payoff.eval, Market.deflator, vasicekMarket, h₀, h₁, h₂, Real.exp_neg]

end MathFin.Rates
