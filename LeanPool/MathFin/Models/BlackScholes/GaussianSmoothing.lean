/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Jumps.JumpDiffusionMixing
public import LeanPool.MathFin.Probability.Gaussian.GaussianMoments

/-!
# Gaussian smoothing of the Black–Scholes price

Averaging the Black–Scholes call over a lognormal factor on the spot gives a Black–Scholes call.
For `G ∼ N(m, v)`,

  `𝔼[C_BS(Se^G; σ)] = C_BS(Se^{m + v/2}; σ')`  with  `σ'²T = σ²T + v`,

at the same strike, rate and maturity `T`. The spot is multiplied by `𝔼[e^G] = e^{m + v/2}` and the
log-return variance `σ²T` gains the variance `v` of `G`.

The proof reads the left side as a call. On `N(0, 1) ⊗ N(m, v)` with coordinates `Z` and `G`, the
mixing formula (`jumpDiffusion_call_eq_integral_bsV`) makes `𝔼[C_BS(Se^G; σ)]` the expected
discounted payoff of the terminal price `S·e^{(r − σ²/2)T + σ√T·Z + G}`. The total log-shock
`σ√T·Z + G` is `N(m, σ²T + v)` (`gaussianReal_conv_gaussianReal`), so this terminal price is a
Black–Scholes terminal price at the spot `Se^{m + v/2}` and the volatility `σ'`, driven by the
standardized shock.

With `G` the sum of `n` of Merton's Gaussian log-jumps, this is the `n`-th term of Merton's
series (`Models/Jumps/JumpDiffusionMerton.lean`).

## Main results

* `integral_exp_gaussianReal`: the lognormal mean `∫ eˣ dN(m, v) = e^{m + v/2}`.
* `integral_bsV_mul_exp_gaussianReal_of_sq`: `∫ C_BS(Se^x; σ) dN(m, v) = C_BS(Se^{m + v/2}; σ')`
  for any `σ' > 0` with `σ'²T = σ²T + v`.
* `integral_bsV_mul_exp_gaussianReal`: the same with `σ' = √(σ² + v/T)`.

## References

* [R. C. Merton, *Option pricing when underlying stock returns are discontinuous*][Merton1976]

## Tags

lognormal mixture, random volatility, averaging over spot, Gaussian convolution,
variance adjustment, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

/-- The exponential is integrable under a Gaussian law. -/
lemma integrable_exp_gaussianReal (m : ℝ) (v : ℝ≥0) : Integrable rexp (gaussianReal m v) := by
  simpa only [one_mul] using integrable_exp_mul_gaussianReal (μ := m) (v := v) 1

/-- **The lognormal mean**: `∫ eˣ dN(m, v) = e^{m + v/2}`, the moment generating function of
`N(m, v)` at `1`. -/
lemma integral_exp_gaussianReal (m : ℝ) (v : ℝ≥0) :
    ∫ x, rexp x ∂(gaussianReal m v) = rexp (m + v / 2) := by
  have h := congrFun (mgf_fun_id_gaussianReal (μ := m) (v := v)) 1
  simp only [mgf, one_mul, mul_one, one_pow] at h
  exact h

/-- **Gaussian smoothing of the Black–Scholes price.** For `G ∼ N(m, v)` and a volatility `σ'`
with `σ'²T = σ²T + v`, the Black–Scholes call at the spot `Se^G` and volatility `σ`, averaged over
`G`, is the Black–Scholes call at the spot `Se^{m + v/2}` and volatility `σ'`. -/
theorem integral_bsV_mul_exp_gaussianReal_of_sq {S K r σ σ' T : ℝ} (hS : 0 < S) (hK : 0 < K)
    (hσ : 0 < σ) (hσ' : 0 < σ') (hT : 0 < T) (m : ℝ) {v : ℝ≥0}
    (hvar : σ' ^ 2 * T = σ ^ 2 * T + v) :
    ∫ x, bsV K r σ (S * rexp x) T ∂(gaussianReal m v) = bsV K r σ' (S * rexp (m + v / 2)) T := by
  -- the diffusion sample `Z ∼ N(0, 1)` and `G ∼ N(m, v)`, independent, on the product space
  have hZ : HasLaw (fun ω : ℝ × ℝ ↦ ω.1) (gaussianReal 0 1)
      ((gaussianReal 0 1).prod (gaussianReal m v)) :=
    measurePreserving_fst.hasLaw
  have hG : HasLaw (fun ω : ℝ × ℝ ↦ ω.2) (gaussianReal m v)
      ((gaussianReal 0 1).prod (gaussianReal m v)) :=
    measurePreserving_snd.hasLaw
  have hGZ : (fun ω : ℝ × ℝ ↦ ω.2) ⟂ᵢ[(gaussianReal 0 1).prod (gaussianReal m v)]
      fun ω ↦ ω.1 :=
    (indepFun_prod (μ := gaussianReal 0 1) (ν := gaussianReal m v) measurable_id
      measurable_id).symm
  have hexp : Integrable (fun ω : ℝ × ℝ ↦ rexp ω.2)
      ((gaussianReal 0 1).prod (gaussianReal m v)) := by
    simpa only [one_mul] using hG.integrable_fun_comp (integrable_exp_mul_gaussianReal 1)
  -- the total log-shock `σ√T·Z + G` is `N(m, σ²T + v)`, so standardized it is `N(0, 1)`
  have hshock : HasLaw (fun ω : ℝ × ℝ ↦ σ * Real.sqrt T * ω.1 + ω.2)
      (gaussianReal m (.mk ((σ * Real.sqrt T) ^ 2) (sq_nonneg _) * 1 + v))
      ((gaussianReal 0 1).prod (gaussianReal m v)) := by
    have h := (indepFun_prod (μ := gaussianReal 0 1) (ν := gaussianReal m v)
      (by fun_prop : Measurable fun z : ℝ ↦ σ * Real.sqrt T * z) measurable_id).hasLaw_fun_add
      (gaussianReal_const_mul hZ (σ * Real.sqrt T)) hG
    rwa [gaussianReal_conv_gaussianReal, mul_zero, zero_add] at h
  have hs : 0 < σ' * Real.sqrt T := mul_pos hσ' (Real.sqrt_pos.2 hT)
  have hW := hasLaw_sub_div_of_gaussianReal hshock hs (by
    simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_one]
    linear_combination (σ ^ 2 - σ' ^ 2) * Real.sq_sqrt hT.le - hvar)
  have hbs : Measurable fun x ↦ bsV K r σ (S * rexp x) T :=
    (measurable_bsV_spot K r σ T).comp (by fun_prop)
  calc ∫ x, bsV K r σ (S * rexp x) T ∂(gaussianReal m v)
      = ∫ ω, bsV K r σ (S * rexp ω.2) T ∂((gaussianReal 0 1).prod (gaussianReal m v)) :=
        (hG.integral_comp hbs.aestronglyMeasurable).symm
    _ = ∫ ω, rexp (-r * T) * max (S * rexp ((r - σ ^ 2 / 2) * T + σ * Real.sqrt T * ω.1 + ω.2)
          - K) 0 ∂((gaussianReal 0 1).prod (gaussianReal m v)) :=
        (jumpDiffusion_call_eq_integral_bsV hZ hG.aemeasurable hGZ hexp hS hK hσ hT).symm
    _ = ∫ ω, rexp (-r * T) * max (bsTerminal (S * rexp (m + v / 2)) r σ' T
          ((σ * Real.sqrt T * ω.1 + ω.2 - m) / (σ' * Real.sqrt T)) - K) 0
          ∂((gaussianReal 0 1).prod (gaussianReal m v)) := by
        refine integral_congr_ae (ae_of_all _ fun ω ↦ ?_)
        have hw : σ' * Real.sqrt T * ((σ * Real.sqrt T * ω.1 + ω.2 - m) / (σ' * Real.sqrt T))
            = σ * Real.sqrt T * ω.1 + ω.2 - m :=
          mul_div_cancel₀ _ hs.ne'
        have hE : (r - σ ^ 2 / 2) * T + σ * Real.sqrt T * ω.1 + ω.2
            = m + v / 2 + ((r - σ' ^ 2 / 2) * T + (σ * Real.sqrt T * ω.1 + ω.2 - m)) := by
          linear_combination (1 / 2 : ℝ) * hvar
        change rexp (-r * T) * max (S * rexp ((r - σ ^ 2 / 2) * T + σ * Real.sqrt T * ω.1 + ω.2)
            - K) 0
          = rexp (-r * T) * max (bsTerminal (S * rexp (m + v / 2)) r σ' T
            ((σ * Real.sqrt T * ω.1 + ω.2 - m) / (σ' * Real.sqrt T)) - K) 0
        rw [hE, Real.exp_add (m + v / 2), ← mul_assoc, bsTerminal, hw]
    _ = bsV K r σ' (S * rexp (m + v / 2)) T :=
        integral_bsCall_payoff_eq_bsV ⟨mul_pos hS (Real.exp_pos _), hK, hσ', hT, hW⟩

/-- **Gaussian smoothing of the Black–Scholes price**, with the smoothed volatility written out:
for `G ∼ N(m, v)`, `𝔼[C_BS(Se^G; σ)] = C_BS(Se^{m + v/2}; √(σ² + v/T))`. -/
theorem integral_bsV_mul_exp_gaussianReal {S K r σ T : ℝ} (hS : 0 < S) (hK : 0 < K)
    (hσ : 0 < σ) (hT : 0 < T) (m : ℝ) (v : ℝ≥0) :
    ∫ x, bsV K r σ (S * rexp x) T ∂(gaussianReal m v)
      = bsV K r (Real.sqrt (σ ^ 2 + v / T)) (S * rexp (m + v / 2)) T :=
  integral_bsV_mul_exp_gaussianReal_of_sq hS hK hσ (Real.sqrt_pos.2 (by positivity)) hT m (by
    rw [Real.sq_sqrt (by positivity), add_mul, div_mul_cancel₀ _ hT.ne'])

end MathFin
