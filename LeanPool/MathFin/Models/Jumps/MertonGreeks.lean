/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Jumps.MertonDominance
public import LeanPool.MathFin.Probability.Gaussian.NormalQuantile
public import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# The Merton jump-diffusion Greeks

The Merton call price is a Poisson mixture of Black–Scholes prices,
`C(S) = ∑ₙ wₙ · C_BS(S·cₙ, σₙ)`, with Poisson weights `wₙ = e^{−Λ}Λⁿ/n!`, jump factors
`cₙ = e^{−kΛ}(1 + k)ⁿ` (the conditional spot is `mertonSpot S n = S·cₙ`) and conditional
volatilities `σₙ = mertonVol n = √(σ² + nδ²/T)`. Its Greeks are Poisson mixtures of the
Black–Scholes Greeks at the conditional spots and volatilities, each carrying its chain-rule
factor: `cₙ` per derivative in the spot, `σ/σₙ` for the volatility. The series can be
differentiated term by term because the Black–Scholes delta and the normal density are bounded
and the weights `wₙcₙ` sum to one, which is the compensation identity `E[mertonSpot(N)] = S` at
`S = 1`.

## Main definitions

* `mertonDelta`: `∑ₙ wₙ cₙ Φ(d₁ⁿ)`, the Poisson mixture of Black–Scholes deltas at the conditional
  spots, each with its factor `cₙ`.
* `mertonGamma`: `∑ₙ wₙ cₙ ϕ(d₁ⁿ)/(S σₙ √T)`, the corresponding mixture of gammas.
* `mertonVega`: `∑ₙ wₙ S cₙ ϕ(d₁ⁿ) √T · σ/σₙ`, the corresponding mixture of vegas.

## Main results

* `hasDerivAt_mertonCallPrice_spot`: the delta is `mertonDelta = ∑ₙ wₙ cₙ Φ(d₁ⁿ)`, where `d₁ⁿ`
  is the Black–Scholes `d₁` at the spot `S·cₙ` and the volatility `σₙ`.
* `mertonDelta_pos`, `mertonDelta_lt_one`: `0 < Δ < 1`. The upper bound is the compensation
  identity `∑ₙ wₙcₙ = 1` together with `Φ < 1`.
* `hasDerivAt_deriv_mertonCallPrice_spot`, `mertonGamma_pos`: the gamma, the second derivative
  of the price in the spot, is `mertonGamma = ∑ₙ wₙ cₙ ϕ(d₁ⁿ)/(S σₙ √T)`, and it is positive. The
  delta series is differentiated term by term (`hasDerivAt_mertonDelta`), and it is the first
  derivative of the price near the point.
* `hasDerivAt_mertonCallPrice_sigma`, `mertonVega_pos`: the vega is
  `mertonVega = ∑ₙ wₙ S cₙ ϕ(d₁ⁿ) √T · σ/σₙ`, and it is positive. The factor `σ/σₙ` is the
  derivative of `σₙ` in `σ`.
* `mertonCallPrice_strictMonoOn_spot`, `mertonCallPrice_strictConvexOn_spot`,
  `mertonCallPrice_strictMonoOn_sigma`: the signs of the Greeks as the shape of the price. On
  `(0, ∞)` the call price strictly increases and is strictly convex in the spot, and strictly
  increases in the diffusion volatility.

## References

* [R. C. Merton, *Option pricing when underlying stock returns are discontinuous*][Merton1976]

## Tags

Merton jump-diffusion, delta and gamma, Poisson mixture, term-by-term differentiation,
Greeks with jumps, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open Real Set Filter ProbabilityTheory
open scoped NNReal Nat

variable {K r σ T k δ : ℝ} {Λ : ℝ≥0}

/-! ### The jump factors -/

/-- The conditional spot is linear in the spot: `mertonSpot S n = S · mertonSpot 1 n`. -/
lemma mertonSpot_eq_mul_one (S k : ℝ) (Λ : ℝ≥0) (n : ℕ) :
    mertonSpot S k Λ n = S * mertonSpot 1 k Λ n := by
  unfold mertonSpot
  ring

/-- **The jump factors average to one**: `∑ₙ wₙ e^{−kΛ}(1 + k)ⁿ = 1`, the compensation identity
`E[mertonSpot(N)] = S₀` at `S₀ = 1`. -/
lemma hasSum_weights_mul_mertonSpot_one (k : ℝ) (Λ : ℝ≥0) :
    HasSum (fun n : ℕ ↦ rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! * mertonSpot 1 k Λ n) 1 := by
  have h := (PoissonPgf.hasSum_poisson_weights_mul_pow Λ (1 + k)).mul_left
    (rexp (-(k * (Λ : ℝ))))
  rw [← Real.exp_add, show -(k * (Λ : ℝ)) + (Λ : ℝ) * (1 + k - 1) = 0 by ring,
    Real.exp_zero] at h
  have hfun : (fun n : ℕ ↦ rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! * mertonSpot 1 k Λ n)
      = fun n ↦ rexp (-(k * (Λ : ℝ))) * (rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! * (1 + k) ^ n) := by
    funext n
    unfold mertonSpot
    ring
  rw [hfun]
  exact h

/-- The Poisson-weighted call values form a convergent series: the call terms are integrable
against `Poisson(Λ)` (`integrable_mertonCallTerm`). -/
lemma summable_weights_mul_mertonCallTerm {S : ℝ} (hS : 0 < S) (hK : 0 < K) (hσ : 0 < σ)
    (hT : 0 < T) (hk : -1 < k) :
    Summable fun n : ℕ ↦
      rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! * mertonCallTerm S K r σ T k δ Λ n := by
  simpa only [smul_eq_mul] using
    (hasSum_integral_poissonMeasure
      (integrable_mertonCallTerm (r := r) δ Λ hS hK hσ hT hk)).summable

/-! ### Delta -/

/-- **The Merton delta**: `∑ₙ wₙ cₙ Φ(d₁ⁿ)`, the Poisson mixture of the Black–Scholes deltas at
the conditional spots `S·cₙ`, each multiplied by `cₙ = ∂(S·cₙ)/∂S`. -/
noncomputable def mertonDelta (S K r σ T k δ : ℝ) (Λ : ℝ≥0) : ℝ :=
  ∑' n : ℕ, rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! *
    (mertonSpot 1 k Λ n * Phi (bsd1 (mertonSpot S k Λ n) K r (mertonVol σ δ T n) T))

/-- The delta series converges: its terms lie in `[0, wₙcₙ]`. -/
lemma summable_mertonDelta_terms (hk : -1 < k) (S : ℝ) :
    Summable fun n : ℕ ↦ rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! *
      (mertonSpot 1 k Λ n * Phi (bsd1 (mertonSpot S k Λ n) K r (mertonVol σ δ T n) T)) :=
  Summable.of_nonneg_of_le
    (fun n ↦ mul_nonneg (by positivity)
      (mul_nonneg (mertonSpot_pos one_pos hk Λ n).le (Phi_nonneg _)))
    (fun n ↦ mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_right (mertonSpot_pos one_pos hk Λ n).le (Phi_le_one _)) (by positivity))
    (hasSum_weights_mul_mertonSpot_one k Λ).summable

/-- **Delta of the Merton call.** `∂C/∂S = ∑ₙ wₙ cₙ Φ(d₁ⁿ)`: the series of Black–Scholes prices
is differentiated term by term, each term's derivative being bounded by `wₙcₙ`. -/
theorem hasDerivAt_mertonCallPrice_spot (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) (hk : -1 < k)
    {S : ℝ} (hS : 0 < S) :
    HasDerivAt (fun s ↦ mertonCallPrice s K r σ T k δ Λ) (mertonDelta S K r σ T k δ Λ) S := by
  have hc (n : ℕ) : 0 < mertonSpot 1 k Λ n := mertonSpot_pos one_pos hk Λ n
  have hw (n : ℕ) : 0 ≤ rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! := by positivity
  have hterm (n : ℕ) (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) :
      HasDerivAt
        (fun y ↦ rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! * mertonCallTerm y K r σ T k δ Λ n)
        (rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! *
          (mertonSpot 1 k Λ n * Phi (bsd1 (mertonSpot s k Λ n) K r (mertonVol σ δ T n) T))) s := by
    have hs0 : 0 < s := hs
    have hbs := (hasDerivAt_bsV_S (r := r) hK (mertonVol_pos (δ := δ) hσ hT n)
      (mul_pos hs0 (hc n)) hT).comp s (hasDerivAt_mul_const (mertonSpot 1 k Λ n))
    have hfun : (fun y ↦ rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! * mertonCallTerm y K r σ T k δ Λ n)
        = fun y ↦ rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n !
          * bsV K r (mertonVol σ δ T n) (y * mertonSpot 1 k Λ n) T := by
      funext y
      rw [mertonCallTerm_eq_bsV, mertonSpot_eq_mul_one y]
    rw [hfun]
    refine (hbs.const_mul (rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n !)).congr_deriv ?_
    rw [mertonSpot_eq_mul_one s]
    ring
  have hbound (n : ℕ) (s : ℝ) (_ : s ∈ Ioi (0 : ℝ)) :
      ‖rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! *
          (mertonSpot 1 k Λ n * Phi (bsd1 (mertonSpot s k Λ n) K r (mertonVol σ δ T n) T))‖
        ≤ rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! * mertonSpot 1 k Λ n := by
    rw [Real.norm_of_nonneg (mul_nonneg (hw n) (mul_nonneg (hc n).le (Phi_nonneg _)))]
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (hc n).le (Phi_le_one _)) (hw n)
  exact (hasDerivAt_tsum_of_isPreconnected (hasSum_weights_mul_mertonSpot_one k Λ).summable
    isOpen_Ioi isPreconnected_Ioi hterm hbound hS
    (summable_weights_mul_mertonCallTerm hS hK hσ hT hk) hS).congr_of_eventuallyEq
    (Eventually.of_forall fun s ↦ mertonCallPrice_eq_tsum s K r σ T k δ Λ)

/-- **The Merton delta is positive.** Every term is nonnegative and the no-jump term is
positive. -/
theorem mertonDelta_pos (hk : -1 < k) (S : ℝ) : 0 < mertonDelta S K r σ T k δ Λ := by
  refine (summable_mertonDelta_terms hk S).tsum_pos
    (fun n ↦ mul_nonneg (by positivity)
      (mul_nonneg (mertonSpot_pos one_pos hk Λ n).le (Phi_nonneg _))) 0 ?_
  rw [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one]
  exact mul_pos (Real.exp_pos _) (mul_pos (mertonSpot_pos one_pos hk Λ 0) (Phi_mem_Ioo _).1)

/-- **The Merton delta is below one.** `Δ = ∑ₙ wₙcₙΦ(d₁ⁿ) < ∑ₙ wₙcₙ = 1`: the compensation
identity bounds the delta exactly as the Black–Scholes bound `Φ < 1` bounds each term. -/
theorem mertonDelta_lt_one (hk : -1 < k) (S : ℝ) : mertonDelta S K r σ T k δ Λ < 1 := by
  have hc (n : ℕ) : 0 < mertonSpot 1 k Λ n := mertonSpot_pos one_pos hk Λ n
  have hsum := hasSum_weights_mul_mertonSpot_one k Λ
  rw [← hsum.tsum_eq]
  refine Summable.tsum_lt_tsum (i := 0) (Pi.le_def.mpr fun n ↦ ?_) ?_
    (summable_mertonDelta_terms hk S) hsum.summable
  · exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (hc n).le (Phi_le_one _))
      (by positivity)
  · exact mul_lt_mul_of_pos_left (mul_lt_of_lt_one_right (hc 0) (Phi_mem_Ioo _).2)
      (by rw [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one]; exact Real.exp_pos _)

/-! ### Gamma -/

/-- **The Merton gamma**: `∑ₙ wₙ cₙ ϕ(d₁ⁿ)/(S σₙ √T)`, the Poisson mixture of the Black–Scholes
gammas at the conditional spots, each multiplied by `cₙ²`. -/
noncomputable def mertonGamma (S K r σ T k δ : ℝ) (Λ : ℝ≥0) : ℝ :=
  ∑' n : ℕ, rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! *
    (mertonSpot 1 k Λ n * gaussianPDFReal 0 1 (bsd1 (mertonSpot S k Λ n) K r (mertonVol σ δ T n) T)
      / (S * mertonVol σ δ T n * Real.sqrt T))

/-- **The delta series has derivative `mertonGamma`.** Near `S`, on `(S/2, ∞)`, each term's
derivative is at most `wₙcₙ` times `1/((S/2) σ √T)`, since `ϕ ≤ 1` and `σₙ ≥ σ`, so the delta
series is differentiated term by term. -/
theorem hasDerivAt_mertonDelta (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) (hk : -1 < k)
    {S : ℝ} (hS : 0 < S) :
    HasDerivAt (fun s ↦ mertonDelta s K r σ T k δ Λ) (mertonGamma S K r σ T k δ Λ) S := by
  have hc (n : ℕ) : 0 < mertonSpot 1 k Λ n := mertonSpot_pos one_pos hk Λ n
  have hw (n : ℕ) : 0 ≤ rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! := by positivity
  have hv (n : ℕ) : 0 < mertonVol σ δ T n := mertonVol_pos hσ hT n
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hS2 : 0 < S / 2 := half_pos hS
  have hterm (n : ℕ) (s : ℝ) (hs : s ∈ Ioi (S / 2)) :
      HasDerivAt (fun y ↦ rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! *
          (mertonSpot 1 k Λ n * Phi (bsd1 (mertonSpot y k Λ n) K r (mertonVol σ δ T n) T)))
        (rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! *
          (mertonSpot 1 k Λ n
              * gaussianPDFReal 0 1 (bsd1 (mertonSpot s k Λ n) K r (mertonVol σ δ T n) T)
            / (s * mertonVol σ δ T n * Real.sqrt T))) s := by
    have hs0 : 0 < s := hS2.trans hs
    have hphi := (hasDerivAt_Phi_bsd1_S (r := r) hK (hv n) (mul_pos hs0 (hc n)) hT).comp s
      (hasDerivAt_mul_const (mertonSpot 1 k Λ n))
    have hfun : (fun y ↦ rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! *
          (mertonSpot 1 k Λ n * Phi (bsd1 (mertonSpot y k Λ n) K r (mertonVol σ δ T n) T)))
        = fun y ↦ rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! *
          (mertonSpot 1 k Λ n * Phi (bsd1 (y * mertonSpot 1 k Λ n) K r (mertonVol σ δ T n) T)) := by
      funext y
      rw [mertonSpot_eq_mul_one y]
    rw [hfun]
    refine ((hphi.const_mul (mertonSpot 1 k Λ n)).const_mul
      (rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n !)).congr_deriv ?_
    rw [mertonSpot_eq_mul_one s]
    congr 1
    calc mertonSpot 1 k Λ n
          * (gaussianPDFReal 0 1 (bsd1 (s * mertonSpot 1 k Λ n) K r (mertonVol σ δ T n) T)
            / (s * mertonSpot 1 k Λ n * mertonVol σ δ T n * Real.sqrt T) * mertonSpot 1 k Λ n)
        = mertonSpot 1 k Λ n
            * (mertonSpot 1 k Λ n
              * gaussianPDFReal 0 1 (bsd1 (s * mertonSpot 1 k Λ n) K r (mertonVol σ δ T n) T))
          / (mertonSpot 1 k Λ n * (s * mertonVol σ δ T n * Real.sqrt T)) := by
          ring
      _ = mertonSpot 1 k Λ n
          * gaussianPDFReal 0 1 (bsd1 (s * mertonSpot 1 k Λ n) K r (mertonVol σ δ T n) T)
          / (s * mertonVol σ δ T n * Real.sqrt T) :=
          mul_div_mul_left _ _ (hc n).ne'
  have hbound (n : ℕ) (s : ℝ) (hs : s ∈ Ioi (S / 2)) :
      ‖rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! *
          (mertonSpot 1 k Λ n
              * gaussianPDFReal 0 1 (bsd1 (mertonSpot s k Λ n) K r (mertonVol σ δ T n) T)
            / (s * mertonVol σ δ T n * Real.sqrt T))‖
        ≤ rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! * mertonSpot 1 k Λ n
          * (S / 2 * σ * Real.sqrt T)⁻¹ := by
    have hs' : S / 2 < s := hs
    have hs0 : 0 < s := hS2.trans hs'
    have hden : S / 2 * σ * Real.sqrt T ≤ s * mertonVol σ δ T n * Real.sqrt T :=
      mul_le_mul_of_nonneg_right (mul_le_mul hs'.le (le_mertonVol δ hσ.le hT n) hσ.le hs0.le)
        hsT.le
    have hfrac : mertonSpot 1 k Λ n
          * gaussianPDFReal 0 1 (bsd1 (mertonSpot s k Λ n) K r (mertonVol σ δ T n) T)
          / (s * mertonVol σ δ T n * Real.sqrt T)
        ≤ mertonSpot 1 k Λ n / (S / 2 * σ * Real.sqrt T) :=
      div_le_div₀ (hc n).le
        (mul_le_of_le_one_right (hc n).le (gaussianPDFReal_zero_one_le_one _))
        (mul_pos (mul_pos hS2 hσ) hsT) hden
    calc ‖rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! *
          (mertonSpot 1 k Λ n
              * gaussianPDFReal 0 1 (bsd1 (mertonSpot s k Λ n) K r (mertonVol σ δ T n) T)
            / (s * mertonVol σ δ T n * Real.sqrt T))‖
        = rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! *
          (mertonSpot 1 k Λ n
              * gaussianPDFReal 0 1 (bsd1 (mertonSpot s k Λ n) K r (mertonVol σ δ T n) T)
            / (s * mertonVol σ δ T n * Real.sqrt T)) :=
          Real.norm_of_nonneg (mul_nonneg (hw n) (div_nonneg
            (mul_nonneg (hc n).le (gaussianPDFReal_nonneg 0 1 _))
            (mul_pos (mul_pos hs0 (hv n)) hsT).le))
      _ ≤ rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! * (mertonSpot 1 k Λ n / (S / 2 * σ * Real.sqrt T)) :=
          mul_le_mul_of_nonneg_left hfrac (hw n)
      _ = rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! * mertonSpot 1 k Λ n
          * (S / 2 * σ * Real.sqrt T)⁻¹ := by
          ring
  exact hasDerivAt_tsum_of_isPreconnected
    ((hasSum_weights_mul_mertonSpot_one k Λ).summable.mul_right _) isOpen_Ioi isPreconnected_Ioi
    hterm hbound (half_lt_self hS) (summable_mertonDelta_terms hk S) (half_lt_self hS)

/-- **Gamma of the Merton call**, for the price itself: `∂²C/∂S² = mertonGamma`. The delta series
is `∂C/∂S` on all of `S > 0` (`hasDerivAt_mertonCallPrice_spot`), so near `S` the derivative of
the price is the delta series, whose derivative is the gamma series (`hasDerivAt_mertonDelta`). -/
theorem hasDerivAt_deriv_mertonCallPrice_spot (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T)
    (hk : -1 < k) {S : ℝ} (hS : 0 < S) :
    HasDerivAt (deriv fun s ↦ mertonCallPrice s K r σ T k δ Λ) (mertonGamma S K r σ T k δ Λ) S :=
  hasDerivAt_deriv_of_eventually
    ((eventually_gt_nhds hS).mono fun _ hy ↦ hasDerivAt_mertonCallPrice_spot hK hσ hT hk hy)
    (hasDerivAt_mertonDelta hK hσ hT hk hS)

/-- **The Merton gamma is positive.** Every term is nonnegative and the no-jump term is
positive. -/
theorem mertonGamma_pos (hσ : 0 < σ) (hT : 0 < T) (hk : -1 < k) {S : ℝ} (hS : 0 < S) :
    0 < mertonGamma S K r σ T k δ Λ := by
  have hc (n : ℕ) : 0 < mertonSpot 1 k Λ n := mertonSpot_pos one_pos hk Λ n
  have hden (n : ℕ) : 0 < S * mertonVol σ δ T n * Real.sqrt T :=
    mul_pos (mul_pos hS (mertonVol_pos hσ hT n)) (Real.sqrt_pos.mpr hT)
  have hterm (n : ℕ) : 0 ≤ rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! *
      (mertonSpot 1 k Λ n
          * gaussianPDFReal 0 1 (bsd1 (mertonSpot S k Λ n) K r (mertonVol σ δ T n) T)
        / (S * mertonVol σ δ T n * Real.sqrt T)) :=
    mul_nonneg (by positivity)
      (div_nonneg (mul_nonneg (hc n).le (gaussianPDFReal_nonneg 0 1 _)) (hden n).le)
  have hsum : Summable fun n : ℕ ↦ rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! *
      (mertonSpot 1 k Λ n
          * gaussianPDFReal 0 1 (bsd1 (mertonSpot S k Λ n) K r (mertonVol σ δ T n) T)
        / (S * mertonVol σ δ T n * Real.sqrt T)) := by
    refine Summable.of_nonneg_of_le hterm (fun n ↦ ?_)
      ((hasSum_weights_mul_mertonSpot_one k Λ).summable.mul_right (S * σ * Real.sqrt T)⁻¹)
    calc rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! *
          (mertonSpot 1 k Λ n
              * gaussianPDFReal 0 1 (bsd1 (mertonSpot S k Λ n) K r (mertonVol σ δ T n) T)
            / (S * mertonVol σ δ T n * Real.sqrt T))
        ≤ rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! * (mertonSpot 1 k Λ n / (S * σ * Real.sqrt T)) :=
          mul_le_mul_of_nonneg_left (div_le_div₀ (hc n).le
            (mul_le_of_le_one_right (hc n).le (gaussianPDFReal_zero_one_le_one _))
            (mul_pos (mul_pos hS hσ) (Real.sqrt_pos.mpr hT))
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_mertonVol δ hσ.le hT n)
              hS.le) (Real.sqrt_nonneg T))) (by positivity)
      _ = rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! * mertonSpot 1 k Λ n
          * (S * σ * Real.sqrt T)⁻¹ := by
          ring
  refine hsum.tsum_pos hterm 0 ?_
  rw [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one]
  exact mul_pos (Real.exp_pos _)
    (div_pos (mul_pos (hc 0) (gaussianPDFReal_pos 0 1 _ one_ne_zero)) (hden 0))

/-! ### Vega -/

/-- The conditional volatility `σₙ = √(σ² + nδ²/T)` has `σ`-derivative `σ/σₙ`. -/
lemma hasDerivAt_mertonVol_sigma (δ : ℝ) (hT : 0 < T) (n : ℕ) (hσ : 0 < σ) :
    HasDerivAt (fun s ↦ mertonVol s δ T n) (σ / mertonVol σ δ T n) σ := by
  have h0 : σ ^ 2 + (n : ℝ) * δ ^ 2 / T ≠ 0 := by positivity
  have h := ((hasDerivAt_pow 2 σ).add_const ((n : ℝ) * δ ^ 2 / T)).sqrt h0
  unfold mertonVol
  refine h.congr_deriv ?_
  rw [show ((2 : ℕ) : ℝ) * σ ^ (2 - 1) = 2 * σ by norm_num, mul_div_mul_left σ _ two_ne_zero]

/-- **The Merton vega**: `∑ₙ wₙ S cₙ ϕ(d₁ⁿ) √T · σ/σₙ`, the Poisson mixture of the Black–Scholes
vegas at the conditional spots and volatilities, each multiplied by `∂σₙ/∂σ = σ/σₙ`. -/
noncomputable def mertonVega (S K r σ T k δ : ℝ) (Λ : ℝ≥0) : ℝ :=
  ∑' n : ℕ, rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! *
    (mertonSpot S k Λ n * gaussianPDFReal 0 1 (bsd1 (mertonSpot S k Λ n) K r (mertonVol σ δ T n) T)
      * Real.sqrt T * (σ / mertonVol σ δ T n))

/-- **Vega of the Merton call.** `∂C/∂σ = mertonVega = ∑ₙ wₙ S cₙ ϕ(d₁ⁿ) √T · σ/σₙ` at every
`σ > 0`. The series is differentiated term by term: each term's `σ`-derivative is at most
`wₙ · S cₙ √T`, since `ϕ ≤ 1` and `σ ≤ σₙ`, and those bounds sum to `S√T`. -/
theorem hasDerivAt_mertonCallPrice_sigma {S : ℝ} (hS : 0 < S) (hK : 0 < K) (hT : 0 < T)
    (hk : -1 < k) (hσ : 0 < σ) :
    HasDerivAt (fun s ↦ mertonCallPrice S K r s T k δ Λ) (mertonVega S K r σ T k δ Λ) σ := by
  have hw (n : ℕ) : 0 ≤ rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! := by positivity
  have hspot (n : ℕ) : 0 < mertonSpot S k Λ n := mertonSpot_pos hS hk Λ n
  have hterm (n : ℕ) (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) :
      HasDerivAt
        (fun y ↦ rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! * mertonCallTerm S K r y T k δ Λ n)
        (rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! *
          (mertonSpot S k Λ n
            * gaussianPDFReal 0 1 (bsd1 (mertonSpot S k Λ n) K r (mertonVol s δ T n) T)
            * Real.sqrt T * (s / mertonVol s δ T n))) s := by
    have hfun : (fun y ↦ rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! * mertonCallTerm S K r y T k δ Λ n)
        = fun y ↦ rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n !
          * bsV K r (mertonVol y δ T n) (mertonSpot S k Λ n) T := by
      funext y
      rw [mertonCallTerm_eq_bsV]
    rw [hfun]
    exact ((hasDerivAt_bsV_sigma (r := r) hK (hspot n) (mertonVol_pos hs hT n) hT).comp s
      (hasDerivAt_mertonVol_sigma δ hT n hs)).const_mul _
  have hbound (n : ℕ) (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) :
      ‖rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! *
          (mertonSpot S k Λ n
            * gaussianPDFReal 0 1 (bsd1 (mertonSpot S k Λ n) K r (mertonVol s δ T n) T)
            * Real.sqrt T * (s / mertonVol s δ T n))‖
        ≤ rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! * mertonSpot S k Λ n * Real.sqrt T := by
    have hs0 : 0 < s := hs
    have hv : 0 < mertonVol s δ T n := mertonVol_pos hs0 hT n
    have hq0 : 0 ≤ s / mertonVol s δ T n := div_nonneg hs0.le hv.le
    have hq1 : s / mertonVol s δ T n ≤ 1 := (div_le_one hv).mpr (le_mertonVol δ hs0.le hT n)
    have hphi := gaussianPDFReal_zero_one_le_one
      (bsd1 (mertonSpot S k Λ n) K r (mertonVol s δ T n) T)
    have hphi0 := gaussianPDFReal_nonneg 0 1 (bsd1 (mertonSpot S k Λ n) K r (mertonVol s δ T n) T)
    have hinner : mertonSpot S k Λ n
          * gaussianPDFReal 0 1 (bsd1 (mertonSpot S k Λ n) K r (mertonVol s δ T n) T)
          * Real.sqrt T * (s / mertonVol s δ T n)
        ≤ mertonSpot S k Λ n * Real.sqrt T := by
      calc mertonSpot S k Λ n
            * gaussianPDFReal 0 1 (bsd1 (mertonSpot S k Λ n) K r (mertonVol s δ T n) T)
            * Real.sqrt T * (s / mertonVol s δ T n)
          ≤ mertonSpot S k Λ n * 1 * Real.sqrt T * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hphi (hspot n).le) (Real.sqrt_nonneg T)) hq1 hq0
              (mul_nonneg (mul_nonneg (hspot n).le zero_le_one) (Real.sqrt_nonneg T))
        _ = mertonSpot S k Λ n * Real.sqrt T := by ring
    calc ‖rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! *
          (mertonSpot S k Λ n
            * gaussianPDFReal 0 1 (bsd1 (mertonSpot S k Λ n) K r (mertonVol s δ T n) T)
            * Real.sqrt T * (s / mertonVol s δ T n))‖
        = rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! *
          (mertonSpot S k Λ n
            * gaussianPDFReal 0 1 (bsd1 (mertonSpot S k Λ n) K r (mertonVol s δ T n) T)
            * Real.sqrt T * (s / mertonVol s δ T n)) :=
          Real.norm_of_nonneg (mul_nonneg (hw n) (mul_nonneg (mul_nonneg
            (mul_nonneg (hspot n).le hphi0) (Real.sqrt_nonneg T)) hq0))
      _ ≤ rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! * (mertonSpot S k Λ n * Real.sqrt T) :=
          mul_le_mul_of_nonneg_left hinner (hw n)
      _ = rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! * mertonSpot S k Λ n * Real.sqrt T := by ring
  exact (hasDerivAt_tsum_of_isPreconnected
    ((summable_weights_mul_mertonSpot S k Λ).mul_right (Real.sqrt T)) isOpen_Ioi
    isPreconnected_Ioi hterm hbound hσ (summable_weights_mul_mertonCallTerm hS hK hσ hT hk)
    hσ).congr_of_eventuallyEq
    (Eventually.of_forall fun s ↦ mertonCallPrice_eq_tsum S K r s T k δ Λ)

/-- **The Merton vega is positive.** Every term is nonnegative and the no-jump term is
positive. -/
theorem mertonVega_pos {S : ℝ} (hS : 0 < S) (hT : 0 < T) (hk : -1 < k) (hσ : 0 < σ) :
    0 < mertonVega S K r σ T k δ Λ := by
  have hspot (n : ℕ) : 0 < mertonSpot S k Λ n := mertonSpot_pos hS hk Λ n
  have hterm (n : ℕ) : 0 ≤ rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! *
      (mertonSpot S k Λ n
          * gaussianPDFReal 0 1 (bsd1 (mertonSpot S k Λ n) K r (mertonVol σ δ T n) T)
        * Real.sqrt T * (σ / mertonVol σ δ T n)) :=
    mul_nonneg (by positivity) (mul_nonneg (mul_nonneg
      (mul_nonneg (hspot n).le (gaussianPDFReal_nonneg 0 1 _)) (Real.sqrt_nonneg T))
      (div_nonneg hσ.le (mertonVol_pos hσ hT n).le))
  have hsum : Summable fun n : ℕ ↦ rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! *
      (mertonSpot S k Λ n
          * gaussianPDFReal 0 1 (bsd1 (mertonSpot S k Λ n) K r (mertonVol σ δ T n) T)
        * Real.sqrt T * (σ / mertonVol σ δ T n)) := by
    refine Summable.of_nonneg_of_le hterm (fun n ↦ ?_)
      ((summable_weights_mul_mertonSpot S k Λ).mul_right (Real.sqrt T))
    have hv : 0 < mertonVol σ δ T n := mertonVol_pos hσ hT n
    calc rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! *
          (mertonSpot S k Λ n
            * gaussianPDFReal 0 1 (bsd1 (mertonSpot S k Λ n) K r (mertonVol σ δ T n) T)
            * Real.sqrt T * (σ / mertonVol σ δ T n))
        ≤ rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! * (mertonSpot S k Λ n * 1 * Real.sqrt T * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (gaussianPDFReal_zero_one_le_one _) (hspot n).le)
            (Real.sqrt_nonneg T)) ((div_le_one hv).mpr (le_mertonVol δ hσ.le hT n))
            (div_nonneg hσ.le hv.le)
            (mul_nonneg (mul_nonneg (hspot n).le zero_le_one) (Real.sqrt_nonneg T)))
            (by positivity)
      _ = rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! * mertonSpot S k Λ n * Real.sqrt T := by ring
  refine hsum.tsum_pos hterm 0 ?_
  rw [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one]
  exact mul_pos (Real.exp_pos _) (mul_pos (mul_pos (mul_pos (hspot 0)
    (gaussianPDFReal_pos 0 1 _ one_ne_zero)) (Real.sqrt_pos.mpr hT))
    (div_pos hσ (mertonVol_pos hσ hT 0)))

/-! ### The shape of the price -/

/-- **The Merton call price strictly increases in the spot**, its delta being positive. -/
theorem mertonCallPrice_strictMonoOn_spot (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T)
    (hk : -1 < k) : StrictMonoOn (fun s ↦ mertonCallPrice s K r σ T k δ Λ) (Ioi 0) := by
  have h (s : ℝ) (hs : 0 < s) :=
    hasDerivAt_mertonCallPrice_spot (r := r) (δ := δ) (Λ := Λ) hK hσ hT hk hs
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0)
    (fun s hs ↦ (h s hs).continuousAt.continuousWithinAt) fun s hs ↦ ?_
  rw [interior_Ioi] at hs
  rw [(h s hs).deriv]
  exact mertonDelta_pos hk s

/-- **The Merton call price is strictly convex in the spot**: its delta strictly increases, the
gamma being positive. -/
theorem mertonCallPrice_strictConvexOn_spot (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T)
    (hk : -1 < k) : StrictConvexOn ℝ (Ioi 0) fun s ↦ mertonCallPrice s K r σ T k δ Λ := by
  have h (s : ℝ) (hs : 0 < s) :=
    hasDerivAt_mertonCallPrice_spot (r := r) (δ := δ) (Λ := Λ) hK hσ hT hk hs
  have h2 (s : ℝ) (hs : 0 < s) :=
    hasDerivAt_deriv_mertonCallPrice_spot (r := r) (δ := δ) (Λ := Λ) hK hσ hT hk hs
  refine StrictMonoOn.strictConvexOn_of_deriv (convex_Ioi 0)
    (fun s hs ↦ (h s hs).continuousAt.continuousWithinAt) ?_
  rw [interior_Ioi]
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0)
    (fun s hs ↦ (h2 s hs).continuousAt.continuousWithinAt) fun s hs ↦ ?_
  rw [interior_Ioi] at hs
  rw [(h2 s hs).deriv]
  exact mertonGamma_pos hσ hT hk hs

/-- **The Merton call price strictly increases in the diffusion volatility**, its vega being
positive. -/
theorem mertonCallPrice_strictMonoOn_sigma {S : ℝ} (hS : 0 < S) (hK : 0 < K) (hT : 0 < T)
    (hk : -1 < k) : StrictMonoOn (fun s ↦ mertonCallPrice S K r s T k δ Λ) (Ioi 0) := by
  have h (s : ℝ) (hs : 0 < s) :=
    hasDerivAt_mertonCallPrice_sigma (r := r) (δ := δ) (Λ := Λ) hS hK hT hk hs
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0)
    (fun s hs ↦ (h s hs).continuousAt.continuousWithinAt) fun s hs ↦ ?_
  rw [interior_Ioi] at hs
  rw [(h s hs).deriv]
  exact mertonVega_pos hS hT hk hs

end MathFin
