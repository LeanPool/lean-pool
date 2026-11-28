/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.BlackScholes.Put
public import LeanPool.MathFin.Probability.Jumps.PoissonPgf
public import LeanPool.MathFin.Models.BlackScholes.PDE
public import Mathlib.Algebra.Order.Star.Real

/-!
# Merton (1976) jump-diffusion option pricing: the Poisson-mixture series

Merton's jump-diffusion model prices a European option as a Poisson mixture
of Black–Scholes values: conditional on `n` jumps by maturity, the terminal
price is lognormal with a jump-adjusted spot and volatility, so

  `C_Merton = E_N[ C_BS(spot_N, vol_N) ],   N ∼ Poisson(Λ)`.

This file formalizes that *terminal mixture law*. With `k > −1` the mean
jump size (`E[Y] = 1 + k` for jump multiplier `Y`), `δ` the jump log-vol,
and `Λ` the expected number of jumps to maturity:

* `mertonSpot S₀ k Λ n = S₀ e^{−kΛ} (1+k)^n` — the jump-*compensated*
  conditional spot. The compensator `e^{−kΛ}` is Merton's risk-neutral
  adjustment: jumps must not change the expected return.
* `mertonVol σ δ T n = √(σ² + n δ²/T)` — total conditional variance
  `σ²T + nδ²` spread over `[0, T]`.
* `mertonCallPrice = ∫ n, mertonCallTerm n ∂(poissonMeasure Λ)` — the price
  *is defined as the expectation over the jump count*; the textbook series
  `∑ₙ e^{−Λ}Λⁿ/n! · C_BS(n)` is then a theorem (`mertonCallPrice_eq_tsum`),
  not a definition.

The classic display weights terms by the adjusted intensity `Λ' = Λ(1+k)`
with a shifted rate `r_n`; that form regroups the factor `(1+k)^n` from our
conditional spot into the weight — term-by-term the same series.

## Main definitions

* `mertonSpot`: the jump-compensated conditional spot after `n` jumps, `S₀ · e^{−kΛ} · (1+k)^n`.
* `mertonVol`: the conditional volatility given `n` jumps, `√(σ² + nδ²/T)`.
* `mertonCallTerm`, `mertonPutTerm`: the `n`-jump conditional Black–Scholes call and put values at
  the conditional spot and volatility.
* `mertonCallPrice`, `mertonPutPrice`: the Merton (1976) call and put prices, the expectation of the
  conditional values over the Poisson jump count.

## Main results

* `mertonCallTerm_eq_integral` / `mertonPutTerm_eq_integral` — each series
  term *is* a discounted conditional expected payoff: `bs_call_formula` /
  `bs_put_formula` instantiated on the canonical Gaussian space
  `(ℝ, gaussianReal 0 1)` at the jump-adjusted parameters. This grounds the
  mixture as an honest iterated expectation
  (`mertonCallPrice_eq_iterated_expectation`).
* `integrable_mertonCallTerm` / `integrable_mertonPutTerm` — the mixture is
  well-defined: conditional values are sandwiched in `[0, spot_n]` (resp.
  `[0, Ke^{−rT}]`) and the weighted spots form a convergent exponential
  series.
* `integral_mertonSpot` — **spot recombination (compensation identity)**:
  `E[mertonSpot(N)] = S₀`. The Poisson pgf at `1 + k` makes the compensator
  `e^{−kΛ}` exactly cancel the jump growth `E[(1+k)^N] = e^{kΛ}`: the
  conditional forwards recombine to the true forward — the risk-neutral
  consistency of Merton's decomposition.
* `merton_put_call_parity` — `C − P = S₀ − Ke^{−rT}`: parity survives jump
  risk, *because* of the compensation identity. Term-wise BS parity gives
  `∑ pmf(n)(spot_n − Ke^{−rT})`, and recombination collapses it.

## Honest scope

European pricing only needs the terminal law, and that is all this file
formalizes: the conditional-lognormal-given-Poisson-count mixture, exactly
parallel to how `BSCallHyp` *hypothesizes* the lognormal terminal law for
the diffusion-only model. The compound-Poisson *process* (jump SDE dynamics,
`S_t` as a càdlàg semimartingale) is upstream-gated and not claimed.

## References

* [R. C. Merton, *Option pricing when underlying stock returns are discontinuous*][Merton1976]

## Tags

Merton jump-diffusion, Poisson mixture, lognormal jumps, option pricing with jumps,
series of Black–Scholes prices, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal Nat

/-! ### Conditional (given `n` jumps) Black–Scholes parameters -/

/-- Jump-compensated conditional spot after `n` jumps:
`S₀ · e^{−kΛ} · (1+k)^n`. The factor `e^{−kΛ}` is Merton's compensator —
the drift adjustment that keeps the expected return unchanged by jumps. -/
noncomputable def mertonSpot (S_0 k : ℝ) (Λ : ℝ≥0) (n : ℕ) : ℝ :=
  S_0 * rexp (-(k * (Λ : ℝ))) * (1 + k) ^ n

/-- Conditional volatility given `n` jumps: total log-variance
`σ²T + nδ²` spread over the horizon, `√(σ² + nδ²/T)`. -/
noncomputable def mertonVol (σ δ T : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (σ ^ 2 + (n : ℝ) * δ ^ 2 / T)

/-- The Merton jump-conditional spot is positive (`S₀`, the drift `exp`, and `(1+k)ⁿ` all positive).
-/
lemma mertonSpot_pos {S_0 k : ℝ} (hS_0 : 0 < S_0) (hk : -1 < k)
    (Λ : ℝ≥0) (n : ℕ) : 0 < mertonSpot S_0 k Λ n := by
  have h1k : (0 : ℝ) < 1 + k := by linarith
  exact mul_pos (mul_pos hS_0 (Real.exp_pos _)) (pow_pos h1k n)

/-- The Merton jump-conditional volatility is positive (`σ > 0`; the radicand is a sum of
nonnegatives). -/
lemma mertonVol_pos {σ δ T : ℝ} (hσ : 0 < σ) (hT : 0 < T) (n : ℕ) :
    0 < mertonVol σ δ T n := by
  apply Real.sqrt_pos.mpr
  have hσ2 : 0 < σ ^ 2 := pow_pos hσ 2
  have hnd : (0 : ℝ) ≤ (n : ℝ) * δ ^ 2 / T :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg δ)) hT.le
  linarith

/-- `mertonVol n² · T = σ²T + nδ²`: the conditional log-variance over the horizon. -/
lemma mertonVol_sq_mul (σ δ : ℝ) {T : ℝ} (hT : 0 < T) (n : ℕ) :
    mertonVol σ δ T n ^ 2 * T = σ ^ 2 * T + n * δ ^ 2 := by
  have h0 : 0 ≤ σ ^ 2 + (n : ℝ) * δ ^ 2 / T := by positivity
  rw [mertonVol, Real.sq_sqrt h0, add_mul, div_mul_cancel₀ _ hT.ne']

/-! ### The conditional Black–Scholes values -/

/-- The `n`-jump conditional Black–Scholes call value
`spot_n Φ(d₁ⁿ) − K e^{−rT} Φ(d₂ⁿ)`. -/
noncomputable def mertonCallTerm (S_0 K r σ T k δ : ℝ) (Λ : ℝ≥0) (n : ℕ) : ℝ :=
  mertonSpot S_0 k Λ n
      * Phi (bsd1 (mertonSpot S_0 k Λ n) K r (mertonVol σ δ T n) T)
    - K * rexp (-r * T)
      * Phi (bsd2 (mertonSpot S_0 k Λ n) K r (mertonVol σ δ T n) T)

/-- The `n`-jump conditional Black–Scholes put value
`K e^{−rT} Φ(−d₂ⁿ) − spot_n Φ(−d₁ⁿ)`. -/
noncomputable def mertonPutTerm (S_0 K r σ T k δ : ℝ) (Λ : ℝ≥0) (n : ℕ) : ℝ :=
  K * rexp (-r * T)
      * Phi (-(bsd2 (mertonSpot S_0 k Λ n) K r (mertonVol σ δ T n) T))
    - mertonSpot S_0 k Λ n
      * Phi (-(bsd1 (mertonSpot S_0 k Λ n) K r (mertonVol σ δ T n) T))

/-- **Merton (1976) jump-diffusion call price**: the expectation, over the
Poisson jump count, of the conditional Black–Scholes call value. -/
noncomputable def mertonCallPrice (S_0 K r σ T k δ : ℝ) (Λ : ℝ≥0) : ℝ :=
  ∫ n, mertonCallTerm S_0 K r σ T k δ Λ n ∂(poissonMeasure Λ)

/-- **Merton (1976) jump-diffusion put price**. -/
noncomputable def mertonPutPrice (S_0 K r σ T k δ : ℝ) (Λ : ℝ≥0) : ℝ :=
  ∫ n, mertonPutTerm S_0 K r σ T k δ Λ n ∂(poissonMeasure Λ)

/-- Each conditional value *is* the Black–Scholes price function `bsV` at the
jump-adjusted spot and volatility: the Merton mixture averages genuine BS
prices. The bridge consumed by `MertonDominance` and `MertonClassicDisplay`. -/
theorem mertonCallTerm_eq_bsV (S_0 K r σ T k δ : ℝ) (Λ : ℝ≥0) (n : ℕ) :
    mertonCallTerm S_0 K r σ T k δ Λ n
      = bsV K r (mertonVol σ δ T n) (mertonSpot S_0 k Λ n) T := by
  unfold mertonCallTerm bsV
  simp only [neg_mul]

/-! ### Each term is an honest discounted expected payoff -/

/-- Each Merton call term is the discounted conditional expected payoff:
`bs_call_formula` on the canonical Gaussian space `(ℝ, gaussianReal 0 1)`
at the jump-adjusted spot and volatility. -/
theorem mertonCallTerm_eq_integral {S_0 K r σ T k : ℝ} (δ : ℝ) (Λ : ℝ≥0)
    (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) (hk : -1 < k)
    (n : ℕ) :
    mertonCallTerm S_0 K r σ T k δ Λ n
      = ∫ z, rexp (-r * T) *
          max (bsTerminal (mertonSpot S_0 k Λ n) r (mertonVol σ δ T n) T z - K) 0
          ∂(gaussianReal 0 1) :=
  (bs_call_formula (Q := gaussianReal 0 1) (Z := id)
    ⟨mertonSpot_pos hS_0 hk Λ n, hK, mertonVol_pos hσ hT n, hT, HasLaw.id⟩).symm

/-- Each Merton put term is the discounted conditional expected payoff:
`bs_put_formula` at the jump-adjusted parameters. -/
theorem mertonPutTerm_eq_integral {S_0 K r σ T k : ℝ} (δ : ℝ) (Λ : ℝ≥0)
    (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) (hk : -1 < k)
    (n : ℕ) :
    mertonPutTerm S_0 K r σ T k δ Λ n
      = ∫ z, rexp (-r * T) *
          max (K - bsTerminal (mertonSpot S_0 k Λ n) r (mertonVol σ δ T n) T z) 0
          ∂(gaussianReal 0 1) :=
  (bs_put_formula (Q := gaussianReal 0 1) (Z := id)
    ⟨mertonSpot_pos hS_0 hk Λ n, hK, mertonVol_pos hσ hT n, hT, HasLaw.id⟩).symm

/-! ### Sandwich bounds for the conditional values

`Phi_nonneg` comes from `Probability/Gaussian/StandardNormal.lean`, `Phi_le_one` from
`Models/ModelFree/PriceBounds.lean` (non-public import above). -/

lemma mertonCallTerm_nonneg {S_0 K r σ T k : ℝ} (δ : ℝ) (Λ : ℝ≥0)
    (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) (hk : -1 < k)
    (n : ℕ) : 0 ≤ mertonCallTerm S_0 K r σ T k δ Λ n := by
  rw [mertonCallTerm_eq_integral δ Λ hS_0 hK hσ hT hk n]
  exact integral_nonneg fun z ↦
    mul_nonneg (Real.exp_pos _).le (le_max_right _ _)

lemma mertonCallTerm_le_spot {S_0 K r σ T k : ℝ} (δ : ℝ) (Λ : ℝ≥0)
    (hS_0 : 0 < S_0) (hK : 0 < K) (hk : -1 < k) (n : ℕ) :
    mertonCallTerm S_0 K r σ T k δ Λ n ≤ mertonSpot S_0 k Λ n := by
  have hS := (mertonSpot_pos hS_0 hk Λ n).le
  have hKr : 0 ≤ K * rexp (-r * T)
      * Phi (bsd2 (mertonSpot S_0 k Λ n) K r (mertonVol σ δ T n) T) :=
    mul_nonneg (mul_nonneg hK.le (Real.exp_pos _).le) (Phi_nonneg _)
  have hΦ := mul_le_of_le_one_right hS
    (Phi_le_one (bsd1 (mertonSpot S_0 k Λ n) K r (mertonVol σ δ T n) T))
  unfold mertonCallTerm
  linarith

lemma mertonPutTerm_nonneg {S_0 K r σ T k : ℝ} (δ : ℝ) (Λ : ℝ≥0)
    (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) (hk : -1 < k)
    (n : ℕ) : 0 ≤ mertonPutTerm S_0 K r σ T k δ Λ n := by
  rw [mertonPutTerm_eq_integral δ Λ hS_0 hK hσ hT hk n]
  exact integral_nonneg fun z ↦
    mul_nonneg (Real.exp_pos _).le (le_max_right _ _)

lemma mertonPutTerm_le_strike {S_0 K r σ T k : ℝ} (δ : ℝ) (Λ : ℝ≥0)
    (hS_0 : 0 < S_0) (hK : 0 < K) (hk : -1 < k) (n : ℕ) :
    mertonPutTerm S_0 K r σ T k δ Λ n ≤ K * rexp (-r * T) := by
  have hS0 : 0 ≤ mertonSpot S_0 k Λ n
      * Phi (-(bsd1 (mertonSpot S_0 k Λ n) K r (mertonVol σ δ T n) T)) :=
    mul_nonneg (mertonSpot_pos hS_0 hk Λ n).le (Phi_nonneg _)
  have hΦ := mul_le_of_le_one_right (mul_nonneg hK.le (Real.exp_pos (-r * T)).le)
    (Phi_le_one (-(bsd2 (mertonSpot S_0 k Λ n) K r (mertonVol σ δ T n) T)))
  unfold mertonPutTerm
  linarith

/-! ### Well-definedness: the mixture is integrable -/

/-- The Poisson-weighted conditional spots form a convergent (exponential)
series — the quantitative heart of the mixture's well-definedness. -/
lemma summable_weights_mul_mertonSpot (S_0 k : ℝ) (Λ : ℝ≥0) :
    Summable (fun n : ℕ ↦
      rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! * mertonSpot S_0 k Λ n) := by
  refine ((PoissonPgf.hasSum_poisson_weights_mul_pow Λ (1 + k)).summable.mul_left
    (S_0 * rexp (-(k * (Λ : ℝ))))).congr fun n ↦ ?_
  unfold mertonSpot
  ring

lemma integrable_mertonCallTerm {S_0 K r σ T k : ℝ} (δ : ℝ) (Λ : ℝ≥0)
    (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) (hk : -1 < k) :
    Integrable (mertonCallTerm S_0 K r σ T k δ Λ) (poissonMeasure Λ) := by
  rw [integrable_poissonMeasure_iff]
  refine Summable.of_nonneg_of_le (fun n ↦ by positivity) (fun n ↦ ?_)
    (summable_weights_mul_mertonSpot S_0 k Λ)
  have hterm : ‖mertonCallTerm S_0 K r σ T k δ Λ n‖
      ≤ mertonSpot S_0 k Λ n := by
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mertonCallTerm_nonneg δ Λ hS_0 hK hσ hT hk n)]
    exact mertonCallTerm_le_spot δ Λ hS_0 hK hk n
  exact mul_le_mul_of_nonneg_left hterm (by positivity)

lemma integrable_mertonPutTerm {S_0 K r σ T k : ℝ} (δ : ℝ) (Λ : ℝ≥0)
    (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) (hk : -1 < k) :
    Integrable (mertonPutTerm S_0 K r σ T k δ Λ) (poissonMeasure Λ) := by
  rw [integrable_poissonMeasure_iff]
  refine Summable.of_nonneg_of_le (fun n ↦ by positivity) (fun n ↦ ?_)
    ((hasSum_one_poissonMeasure Λ).summable.mul_right (K * rexp (-r * T)))
  have hterm : ‖mertonPutTerm S_0 K r σ T k δ Λ n‖ ≤ K * rexp (-r * T) := by
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mertonPutTerm_nonneg δ Λ hS_0 hK hσ hT hk n)]
    exact mertonPutTerm_le_strike δ Λ hS_0 hK hk n
  exact mul_le_mul_of_nonneg_left hterm (by positivity)

lemma integrable_mertonSpot {S_0 k : ℝ} (Λ : ℝ≥0)
    (hS_0 : 0 < S_0) (hk : -1 < k) :
    Integrable (mertonSpot S_0 k Λ) (poissonMeasure Λ) := by
  rw [integrable_poissonMeasure_iff]
  refine (summable_weights_mul_mertonSpot S_0 k Λ).congr fun n ↦ ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (mertonSpot_pos hS_0 hk Λ n).le]

/-! ### The textbook series, the iterated expectation, and the
compensation identity -/

/-- **The Merton series.** The price expands to the textbook Poisson-weighted
sum of conditional Black–Scholes values — no hypotheses needed: the integral
over `poissonMeasure` *is* the weighted series for real-valued integrands. -/
theorem mertonCallPrice_eq_tsum (S_0 K r σ T k δ : ℝ) (Λ : ℝ≥0) :
    mertonCallPrice S_0 K r σ T k δ Λ
      = ∑' n : ℕ, rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n !
          * mertonCallTerm S_0 K r σ T k δ Λ n := by
  unfold mertonCallPrice
  rw [integral_poissonMeasure]
  simp_rw [smul_eq_mul]

/-- **The Merton price as an iterated expectation**: outer expectation over
the Poisson jump count, inner discounted expected payoff under the
conditional lognormal — the honest mixture-pricing form. -/
theorem mertonCallPrice_eq_iterated_expectation {S_0 K r σ T k : ℝ}
    (δ : ℝ) (Λ : ℝ≥0)
    (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) (hk : -1 < k) :
    mertonCallPrice S_0 K r σ T k δ Λ
      = ∫ n, (∫ z, rexp (-r * T) *
          max (bsTerminal (mertonSpot S_0 k Λ n) r (mertonVol σ δ T n) T z - K) 0
          ∂(gaussianReal 0 1)) ∂(poissonMeasure Λ) :=
  integral_congr_ae (ae_of_all _ fun n ↦
    mertonCallTerm_eq_integral δ Λ hS_0 hK hσ hT hk n)

/-- **Spot recombination (Merton's compensation identity)**:
`E[mertonSpot(N)] = S₀`. The compensator `e^{−kΛ}` exactly cancels the
expected jump growth `E[(1+k)^N] = e^{kΛ}` (the Poisson pgf at `1+k`): the
conditional forwards recombine to the true forward. No hypotheses — the
identity is exact for all `k` and `Λ`. -/
theorem integral_mertonSpot (S_0 k : ℝ) (Λ : ℝ≥0) :
    ∫ n, mertonSpot S_0 k Λ n ∂(poissonMeasure Λ) = S_0 := by
  rw [integral_poissonMeasure]
  simp_rw [smul_eq_mul]
  rw [tsum_congr (fun n ↦ show
        rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! * mertonSpot S_0 k Λ n
          = (S_0 * rexp (-(k * (Λ : ℝ))))
            * (rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! * (1 + k) ^ n) from by
      unfold mertonSpot; ring),
    tsum_mul_left, PoissonPgf.tsum_poisson_weights_mul_pow,
    show (1 + k - 1 : ℝ) = k from by ring,
    mul_assoc, ← Real.exp_add,
    show -(k * (Λ : ℝ)) + (Λ : ℝ) * k = 0 from by ring,
    Real.exp_zero, mul_one]

/-- **Term-wise put–call parity** for the conditional values: pure
`Φ(x) + Φ(−x) = 1` algebra, no hypotheses. -/
theorem mertonTerm_parity (S_0 K r σ T k δ : ℝ) (Λ : ℝ≥0) (n : ℕ) :
    mertonCallTerm S_0 K r σ T k δ Λ n - mertonPutTerm S_0 K r σ T k δ Λ n
      = mertonSpot S_0 k Λ n - K * rexp (-r * T) := by
  unfold mertonCallTerm mertonPutTerm
  linear_combination
    mertonSpot S_0 k Λ n
      * Phi_add_Phi_neg (bsd1 (mertonSpot S_0 k Λ n) K r (mertonVol σ δ T n) T)
    - K * rexp (-r * T)
      * Phi_add_Phi_neg (bsd2 (mertonSpot S_0 k Λ n) K r (mertonVol σ δ T n) T)

/-- **Merton put–call parity**: `C − P = S₀ − K e^{−rT}`. Parity survives
jump risk *because of* the compensation identity: term-wise BS parity leaves
`E[mertonSpot(N)] − Ke^{−rT}`, and spot recombination collapses the
expectation to `S₀`. -/
theorem merton_put_call_parity {S_0 K r σ T k : ℝ} (δ : ℝ) (Λ : ℝ≥0)
    (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) (hk : -1 < k) :
    mertonCallPrice S_0 K r σ T k δ Λ - mertonPutPrice S_0 K r σ T k δ Λ
      = S_0 - K * rexp (-r * T) := by
  unfold mertonCallPrice mertonPutPrice
  rw [← integral_sub (integrable_mertonCallTerm δ Λ hS_0 hK hσ hT hk)
      (integrable_mertonPutTerm δ Λ hS_0 hK hσ hT hk),
    integral_congr_ae (ae_of_all _ fun n ↦
      mertonTerm_parity S_0 K r σ T k δ Λ n),
    integral_sub (integrable_mertonSpot Λ hS_0 hk) (integrable_const _),
    integral_mertonSpot, integral_const, probReal_univ, one_smul]

end MathFin
