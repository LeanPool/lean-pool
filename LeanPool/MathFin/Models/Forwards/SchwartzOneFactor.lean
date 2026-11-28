/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Rates.VasicekSDEGaussian

/-!
# Schwartz one-factor commodity futures

In the Schwartz (1997) one-factor model the log spot price of a commodity is
mean-reverting under the pricing measure:

  `d ln S_t = κ(θ − ln S_t) dt + σ dB_t`.

This is the Ornstein–Uhlenbeck dynamics of the Vasicek short rate, so, carrying
`ln S_T` in its Wiener representation (the SDE bridge is cited, not proven — see
`schwartzFuturesPrice_eq_integral`), it has the Gaussian law `N(m_T, v_T)` with
`m_T = vasicekSDEMean` and `v_T = vasicekSDEVariance` (`vasicekShortRate_hasLaw_gaussian`),
for `κ > 0`. The futures
price is `F(0,T) = E[S_T] = E[e^{ln S_T}]`, the Gaussian moment-generating
function at `1`:

  `F(0,T) = exp(m_T + v_T / 2)`.

In the Lean, `E` is the expectation under an arbitrary probability measure `μ` carrying the
Brownian motion: `μ` is *read* as the pricing measure, and that the futures price is
`E^Q[S_T]` is the textbook identification, not proved here. `schwartzFuturesPrice` is the
closed form, defined; `schwartzFuturesPrice_eq_integral` proves it equals `E[S_T]`.

As `T → ∞` (for `κ > 0`) the closed form flattens to `exp(θ + σ² / (4κ))`, independent of
the current spot.

This formalizes only the constant-parameter Schwartz (1997) model; Hull's
time-dependent level `q(t)` (the Hull–White-form drift calibrated to the
quoted futures curve) is out of scope.

## Main definitions

* `schwartzFuturesPrice`: the Schwartz one-factor futures price, defined as the closed form
  `exp(m_T + v_T / 2)` from the initial log spot `x₀`, long-run log level `θ`, speed `κ`,
  volatility `σ` and maturity `T`.

## Main results

* `schwartzFuturesPrice_eq_integral` — it equals `E[S_T]` for the log spot in its
  Wiener representation (the SDE bridge is cited, not proven).
* `tendsto_schwartzFuturesPrice_atTop` — for `κ > 0`, the long-maturity flattening limit
  `exp(θ + σ²/(4κ))`.

## References

* [E. S. Schwartz, *The Stochastic Behavior of Commodity Prices: Implications for Valuation
  and Hedging*][Schwartz1997].
* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull] (the time-dependent `q(t)`
  extension).

## Tags

Schwartz model, commodity futures, mean-reverting spot, Ornstein-Uhlenbeck, convenience yield,
futures curve, MSC 91G20, MSC 60J60, JEL Q02
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped NNReal
open WienerIntegralL2

/-- **Schwartz one-factor futures price** with initial log spot `x₀`, long-run
log level `θ`, mean-reversion speed `κ`, volatility `σ` and maturity `T`, defined as the
closed form `exp(m_T + v_T / 2)`; `schwartzFuturesPrice_eq_integral` proves it is the mean
`E[S_T]` of the terminal spot (for `κ > 0`, the log spot in its Wiener representation). -/
noncomputable def schwartzFuturesPrice (x₀ θ κ σ T : ℝ) : ℝ :=
  Real.exp (vasicekSDEMean x₀ θ κ T + vasicekSDEVariance σ κ T / 2)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-- **Schwartz futures price = expected terminal spot.** With the log spot
carried in its Wiener representation `ln S_T = m_T + σ ∫₀ᵀ e^{−κ(T−s)} dB_s`
(the OU solution representation of `vasicekShortRate_hasLaw_gaussian` — the
modelling bridge from the SDE is cited, not proven here) and `κ > 0`, `E[S_T] =
schwartzFuturesPrice`, the expectation taken under the given probability measure `μ`. -/
theorem schwartzFuturesPrice_eq_integral (hB : IsPreBrownianReal B μ)
    (x₀ θ σ : ℝ) {κ : ℝ} (hκ : 0 < κ) (T : ℝ≥0) :
    ∫ ω, Real.exp (vasicekSDEMean x₀ θ κ (T : ℝ)
        + σ * (wienerIntegralLp B hB T (vasicekKernelLp κ hκ.le T) ω)) ∂μ
      = schwartzFuturesPrice x₀ θ κ σ T := by
  have h := mgf_gaussianReal (vasicekShortRate_hasLaw_gaussian hB x₀ θ σ hκ T) 1
  simp only [mgf, one_mul, mul_one, one_pow] at h
  rw [h, schwartzFuturesPrice, Real.coe_toNNReal _ (vasicekSDEVariance_nonneg σ hκ T.coe_nonneg)]

/-- **Long-maturity flattening**: as `T → ∞` the Schwartz futures price tends
to `exp(θ + σ² / (4κ))`, independent of the initial spot. -/
theorem tendsto_schwartzFuturesPrice_atTop (x₀ θ σ : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (schwartzFuturesPrice x₀ θ κ σ) atTop
      (𝓝 (Real.exp (θ + σ ^ 2 / (4 * κ)))) := by
  have hm : Tendsto (fun t ↦ vasicekSDEMean x₀ θ κ t) atTop (𝓝 θ) :=
    (vasicekDeterministic_tendsto_mean x₀ θ κ hκ).congr fun t ↦
      (vasicekSDEMean_eq_deterministic x₀ θ κ t).symm
  have hv := tendsto_vasicekSDEVariance_atTop σ hκ
  have hlim : θ + σ ^ 2 / (2 * κ) / 2 = θ + σ ^ 2 / (4 * κ) := by ring
  rw [← hlim]
  exact Real.continuous_exp.tendsto _ |>.comp (hm.add (hv.div_const 2))

end MathFin
