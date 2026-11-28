/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Laws.Esscher
public import LeanPool.MathFin.Pricing.ForwardMeasure
public import LeanPool.MathFin.Probability.Brownian.Wiener.WienerIntegralExpMoment

/-!
# The forward measure of a Wiener-represented bank account

For a bank account `exp(M + c₂·∫₀ˢ g dB)` whose exponent is a Wiener integral
(`wienerIntegralLp`), the discount factor `1/exp(M + c₂∫g dB)` has a Gaussian exponential moment,
so the `S`-forward measure `forwardMeasure μ (exp(M + c₂∫g dB))` (`Pricing/ForwardMeasure`) is
a probability measure. Under it a Wiener-represented rate `m + c₁·∫₀ˢ f dB` keeps its variance and
its mean shifts by minus its covariance with the account's exponent, `c₁c₂⟪f, g⟫`: the Gaussian
facts behind the bond put in the Hull–White and two-piece GSR models.

## Main results

* `integrable_one_div_exp_add_mul_wienerIntegralLp` — the discount factor of a Wiener-represented
  bank account is integrable.
* `integral_exp_mul_wienerIntegralLp_eq_forwardMeasure` — futures = forward × exp(covariance), for
  the exponential moments of a Wiener-represented rate.
* `hasLaw_forwardMeasure_wienerIntegralLp` — the law of a Wiener-represented rate under the forward
  measure of a Wiener-represented bank account; Hull–White (`Models/Rates/TimingAdjustment`) and
  GSR (`Models/Rates/GSRBondPriceAt`) short rates are its instances.

## Tags

forward measure, Wiener-represented bank account, Hull–White model, Gaussian short rate,
futures versus forward, convexity adjustment, MSC 91G30, MSC 60H05, JEL E43
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open WienerIntegralL2
open scoped NNReal InnerProductSpace

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

variable [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ}

/-- **The bond payoff of a Wiener-represented rate is integrable**: the discount factor
`1/exp(M + c·∫₀ˢ g dB) = exp(−(M + c·∫₀ˢ g dB))` has a Gaussian exponential moment. With
`forwardMeasure_isProbabilityMeasure` it makes the forward measure of the bank account
`exp(M + c·∫₀ˢ g dB)` a probability measure. -/
theorem integrable_one_div_exp_add_mul_wienerIntegralLp (hB : IsPreBrownianReal B μ) (S : ℝ≥0)
    (M c : ℝ) (g : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (S : ℝ)))) :
    Integrable (fun ω ↦ 1 / Real.exp (M + c * wienerIntegralLp B hB S g ω)) μ := by
  refine (((wienerIntegralLp_hasLaw_gaussian hB S g).integrable_fun_comp
    (integrable_exp_mul_gaussianReal (-c))).const_mul (Real.exp (-M))).congr
    (ae_of_all _ fun ω ↦ ?_)
  simp only [one_div, ← Real.exp_neg, ← Real.exp_add]
  congr 1
  ring

/-- **Futures = forward × exp(covariance), for Wiener-represented rates.** With the bank account
`exp(M + c₂·∫₀ˢ g dB)` and any rate `m + c₁·∫₀ˢ f dB`, for every `t`,

  `𝔼[e^{t(m + c₁∫f dB)}] = 𝔼^S[e^{t(m + c₁∫f dB)}] · e^{t c₁ c₂ ⟪f, g⟫}`,

`⟪f, g⟫ = Cov(∫f dB, ∫g dB)`: the instance of `futuresForwardBasis_of_integral_mul_exp_neg` with the
covariance identity `integral_exp_mul_exp_neg_wienerIntegralLp`. -/
theorem integral_exp_mul_wienerIntegralLp_eq_forwardMeasure (hB : IsPreBrownianReal B μ) (S : ℝ≥0)
    (m M c₁ c₂ t : ℝ) (f g : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (S : ℝ)))) :
    ∫ ω, Real.exp (t * (m + c₁ * wienerIntegralLp B hB S f ω)) ∂μ
      = (∫ ω, Real.exp (t * (m + c₁ * wienerIntegralLp B hB S f ω))
          ∂forwardMeasure μ fun ω ↦ Real.exp (M + c₂ * wienerIntegralLp B hB S g ω))
        * Real.exp (t * (c₁ * c₂ * ⟪f, g⟫_ℝ)) := by
  have hV (ω : Ω) : t * (m + c₁ * wienerIntegralLp B hB S f ω)
      = t * m + (t * c₁) * wienerIntegralLp B hB S f ω := by ring
  have key := integral_exp_mul_exp_neg_wienerIntegralLp hB S (t * m) M (t * c₁) c₂ f g
  refine futuresForwardBasis_of_integral_mul_exp_neg
    (Y := fun ω ↦ M + c₂ * wienerIntegralLp B hB S g ω) (t * (c₁ * c₂ * ⟪f, g⟫_ℝ)) ?_ ?_ ?_
  · exact ((Lp.stronglyMeasurable _).measurable.const_mul c₂).const_add M
  · rw [integral_exp_neg_add_mul_wienerIntegralLp]
    exact Real.exp_pos _
  · simp_rw [hV]
    rw [← mul_assoc, ← mul_assoc]
    exact key

/-- **The law of a Wiener-represented rate under the forward measure of a Wiener-represented bank
account.** If `r = m + c₁·∫₀ˢ f dB` is `N(m', v)` under `μ`, then under the forward measure of the
bank account `exp(M + c₂·∫₀ˢ g dB)` it is `N(m' − c₁c₂⟪f, g⟫, v)`: the mean shifts by minus the
covariance of the rate with the account's exponent and the variance is unchanged. The moment
generating function identity `integral_exp_mul_wienerIntegralLp_eq_forwardMeasure` determines the
law (`measure_eq_of_mgf_id_eq`). Hull–White and GSR short rates are its instances. -/
theorem hasLaw_forwardMeasure_wienerIntegralLp (hB : IsPreBrownianReal B μ) (S : ℝ≥0)
    (m M c₁ c₂ m' : ℝ) {v : ℝ≥0} (f g : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (S : ℝ))))
    (hlaw : HasLaw (fun ω ↦ m + c₁ * wienerIntegralLp B hB S f ω) (gaussianReal m' v) μ) :
    HasLaw (fun ω ↦ m + c₁ * wienerIntegralLp B hB S f ω)
      (gaussianReal (m' - c₁ * c₂ * ⟪f, g⟫_ℝ) v)
      (forwardMeasure μ fun ω ↦ Real.exp (M + c₂ * wienerIntegralLp B hB S g ω)) := by
  have := forwardMeasure_isProbabilityMeasure (Q := μ) (fun _ ↦ Real.exp_pos _)
    (integrable_one_div_exp_add_mul_wienerIntegralLp hB S M c₂ g)
  have hae : AEMeasurable (fun ω ↦ m + c₁ * wienerIntegralLp B hB S f ω)
      (forwardMeasure μ fun ω ↦ Real.exp (M + c₂ * wienerIntegralLp B hB S g ω)) :=
    hlaw.aemeasurable.mono_ac (withDensity_absolutelyContinuous _ _)
  refine ⟨hae, (measure_eq_of_mgf_id_eq integrable_exp_mul_gaussianReal ?_).symm⟩
  rw [mgf_id_gaussianReal, mgf_id_map hae]
  funext t
  have hμ := mgf_gaussianReal hlaw t
  have h := integral_exp_mul_wienerIntegralLp_eq_forwardMeasure hB S m M c₁ c₂ t f g
  simp only [mgf] at hμ ⊢
  rw [hμ, eq_comm, ← eq_div_iff (Real.exp_pos _).ne', ← Real.exp_sub] at h
  rw [h]
  congr 1
  ring

end MathFin
