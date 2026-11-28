/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Variance swap fair strike (Demeterfi-Derman-Kamal)

Under the BS lognormal hypothesis, the fair strike of a variance swap with
log-payoff replication

  `(2/T) · E_Q[log(F/S_T) + (S_T - F)/F] = σ²`,

where `F = S_0 · e^{rT}` is the forward price. The two terms are:

* `E_Q[log(F/S_T)] = σ² T / 2`: the log-moment of the discount factor `F/S_T`.
  Comes from `log(F/S_T) = σ² T / 2 − σ √T · Z` (after the `S_0` cancellation)
  and `E_Q[Z] = 0`.
* `E_Q[(S_T - F)/F] = 0`: zero by `expected_terminal_eq_forward` (`E_Q[S_T] = F`).

The log piece alone gives `(2/T)·σ²T/2 = σ²`. The whole identity
`(2/T) · E_Q[log(F/S_T) + (S_T − F)/F] = σ²` (`varianceSwap_fairStrike`) is the no-jump case of
`jumpDiffusion_logContract` and lives in `JumpDiffusionVarianceSwap.lean`, with `E_Q[S_T] = F`
from `expected_terminal_eq_forward` (`Forward.lean`). Under BS lognormal dynamics the fair
variance swap rate equals the squared volatility, which is the relationship that makes BS implied
volatility a "risk-neutral expected variance".

## Main results

* `log_forward_div_bsTerminal_eq`: `log(F/S_T) = σ² T / 2 − σ √T · z`.
* `integral_log_forward_div_bsTerminal_eq`:
  `E_Q[log(F/S_T)] = σ² T / 2`.
* `varianceSwap_log_contribution`: the log-payoff piece
  `(2/T) · E_Q[log(F/S_T)] = σ²`.

Model-free, for any law of the log-return `Y` with `S_T = S_0e^Y`, `S_0 > 0`, `E|Y| < ∞` and
`E[e^Y] < ∞`:

* `integral_logContract`: the expected payoff is
  `E[log(F/S_T) + (S_T − F)/F] = rT − E[Y] + (e^{−rT}E[e^Y] − 1)`.
* `integral_logContract_of_integral_exp`: when the forward is the mean of `S_T`, it is the gap
  `rT − E[Y] = log F − E[log S_T]`. In Black–Scholes that gap is half the variance of `Y`; for a
  jump-diffusion at the compensated drift it differs from half the variance by
  `ΛT·E[e^J − 1 − J − J²/2]` (`jumpDiffusion_logContract_sub_variance`,
  `JumpDiffusionVarianceSwap.lean`).

## References

* [P. Carr and D. Madan, *Towards a theory of volatility trading*][CarrMadan1998]
* [Carr and Wu, *Variance risk premiums*][CarrWu2009]
* [Cont and Tankov, *Financial Modelling with Jump Processes*][ContTankov2004]
* [Demeterfi et al., *More than you ever wanted to know about volatility
  swaps*][DemeterfiDermanKamalZou1999]

## Tags

variance swap, fair strike, log contract, Demeterfi–Derman–Kamal, static replication, MSC 91G20,
JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

/-- **The log contract under any law of the log-return.** For `S > 0`, the forward
`F = Se^{rτ}` and a law `μ` of the log-return `Y`, with `S_τ = Se^Y`, `𝔼|Y| < ∞` and
`𝔼[e^Y] < ∞`, the Demeterfi–Derman–Kamal–Zou log contract has the expected payoff
`𝔼[log(F/S_τ) + (S_τ − F)/F] = rτ − 𝔼[Y] + (e^{−rτ}𝔼[e^Y] − 1)`: pointwise, `log(F/S_τ) = rτ − Y`
and `(S_τ − F)/F = e^{Y − rτ} − 1`. -/
lemma integral_logContract {μ : Measure ℝ} [IsProbabilityMeasure μ] {S : ℝ} (hS : 0 < S)
    (r τ : ℝ) (hY : Integrable (fun y ↦ y) μ) (hE : Integrable rexp μ) :
    ∫ y, (Real.log (S * rexp (r * τ) / (S * rexp y))
        + (S * rexp y - S * rexp (r * τ)) / (S * rexp (r * τ))) ∂μ
      = r * τ - ∫ y, y ∂μ + (rexp (-(r * τ)) * ∫ y, rexp y ∂μ - 1) := by
  have hlog (y : ℝ) : Real.log (S * rexp (r * τ) / (S * rexp y)) = r * τ - y := by
    rw [mul_div_mul_left _ _ hS.ne', ← Real.exp_sub, Real.log_exp]
  have hfwd (y : ℝ) : (S * rexp y - S * rexp (r * τ)) / (S * rexp (r * τ))
      = rexp (-(r * τ)) * rexp y - 1 := by
    rw [sub_div, mul_div_mul_left _ _ hS.ne', div_self (mul_pos hS (Real.exp_pos _)).ne',
      Real.exp_neg, inv_mul_eq_div]
  have hA : Integrable (fun y ↦ r * τ - y) μ := (integrable_const _).sub hY
  have hB : Integrable (fun y ↦ rexp (-(r * τ)) * rexp y - 1) μ :=
    (hE.const_mul _).sub (integrable_const _)
  simp only [hlog, hfwd]
  rw [integral_add hA hB, integral_sub (integrable_const _) hY,
    integral_sub (hE.const_mul _) (integrable_const _), integral_const_mul (rexp (-(r * τ))) rexp]
  simp

/-- **When the forward is the mean, the log contract's expected payoff is the gap** `rτ − 𝔼[Y]`: if
`𝔼[e^Y] = e^{rτ}`, the forward `F = Se^{rτ}` is the mean of `S_τ = Se^Y`, and the expected payoff of
the log contract is `rτ − 𝔼[Y] = log F − 𝔼[log S_τ]` (`integral_logContract`). -/
lemma integral_logContract_of_integral_exp {μ : Measure ℝ} [IsProbabilityMeasure μ] {S : ℝ}
    (hS : 0 < S) (r τ : ℝ) (hY : Integrable (fun y ↦ y) μ)
    (hF : ∫ y, rexp y ∂μ = rexp (r * τ)) :
    ∫ y, (Real.log (S * rexp (r * τ) / (S * rexp y))
        + (S * rexp y - S * rexp (r * τ)) / (S * rexp (r * τ))) ∂μ = r * τ - ∫ y, y ∂μ := by
  have hE : Integrable rexp μ :=
    Integrable.of_integral_ne_zero (by rw [hF]; exact (Real.exp_pos _).ne')
  rw [integral_logContract hS r τ hY hE, hF, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
    sub_self, add_zero]

/-- **Log-moment integrand identity**: after the `S_0` cancellation,
`log((S_0 · e^{rT}) / (S_0 · exp((r − σ²/2)T + σ√T·z))) = σ²T/2 − σ√T·z`. -/
lemma log_forward_div_bsTerminal_eq {S_0 : ℝ} (hS : 0 < S_0) (r σ T z : ℝ) :
    Real.log ((S_0 * Real.exp (r * T)) /
              (S_0 * Real.exp ((r - σ^2/2) * T + σ * Real.sqrt T * z)))
      = σ^2 * T / 2 - σ * Real.sqrt T * z := by
  have hS_ne : S_0 ≠ 0 := hS.ne'
  rw [mul_div_mul_left _ _ hS_ne]
  rw [← Real.exp_sub, Real.log_exp]
  ring

/-- **Log-moment integral identity**: `∫ z, log(F/S_T(z)) ∂(gaussianReal 0 1)
= σ² T / 2`. -/
lemma integral_log_forward_div_bsTerminal_eq {S_0 : ℝ} (hS : 0 < S_0)
    (r σ T : ℝ) :
    ∫ z, Real.log ((S_0 * Real.exp (r * T)) /
                  (S_0 * Real.exp ((r - σ^2/2) * T + σ * Real.sqrt T * z)))
      ∂(gaussianReal 0 1) = σ^2 * T / 2 := by
  have h_integrand_eq : ∀ z : ℝ,
      Real.log ((S_0 * Real.exp (r * T)) /
                (S_0 * Real.exp ((r - σ^2/2) * T + σ * Real.sqrt T * z)))
        = σ^2 * T / 2 - σ * Real.sqrt T * z :=
    fun z ↦ log_forward_div_bsTerminal_eq hS r σ T z
  rw [show (fun z ↦ Real.log ((S_0 * Real.exp (r * T)) /
              (S_0 * Real.exp ((r - σ^2/2) * T + σ * Real.sqrt T * z))))
        = (fun z ↦ σ^2 * T / 2 - σ * Real.sqrt T * z) from funext h_integrand_eq]
  have h_const_integrable :
      Integrable (fun _ : ℝ ↦ σ^2 * T / 2) (gaussianReal 0 1) :=
    integrable_const _
  have h_id_basic : Integrable (id : ℝ → ℝ) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_cast)
  have h_id_integrable :
      Integrable (fun z : ℝ ↦ σ * Real.sqrt T * z) (gaussianReal 0 1) :=
    h_id_basic.const_mul (σ * Real.sqrt T)
  rw [integral_sub h_const_integrable h_id_integrable]
  rw [integral_const, integral_const_mul, integral_id_gaussianReal]
  simp

/-- **Variance swap fair strike (log-payoff contribution)**: the log-payoff
replication piece scales to give the squared volatility.

`(2/T) · E[log(F/S_T)] = σ²` under the BS lognormal hypothesis (with
`F = S_0 · e^{rT}`). The whole log contract, with the zero excess-return term
`E[(S_T − F)/F] = 0`, is `varianceSwap_fairStrike` (`JumpDiffusionVarianceSwap.lean`). -/
theorem varianceSwap_log_contribution {S_0 : ℝ} (hS : 0 < S_0)
    (r σ T : ℝ) (hT : T ≠ 0) :
    (2 / T) *
      (∫ z, Real.log ((S_0 * Real.exp (r * T)) /
            (S_0 * Real.exp ((r - σ^2/2) * T + σ * Real.sqrt T * z)))
        ∂(gaussianReal 0 1)) = σ^2 := by
  rw [integral_log_forward_div_bsTerminal_eq hS]
  field_simp

end MathFin
