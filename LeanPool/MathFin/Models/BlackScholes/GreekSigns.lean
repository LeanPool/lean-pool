/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho, Yang Ye
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.BlackScholes.Call

/-!
# Black-Scholes Greek sign constraints

The signs of the BS Greeks are determined by the structure of the call
price formula and the positivity of the standard-normal PDF/CDF. They are
collected here as named lemmas — the library has the individual derivatives
scattered across `PDE.lean`, `StrikeGreeks.lean`, and `HigherGreeks.lean`,
but the sign constraints are not explicitly stated.

The sign constraints are the *qualitative* content of the BS Greeks: a
trader can read each sign off the formula and the table below.

| Greek | Sign for call | Reason |
|---|---|---|
| δ = ∂_S V    | ≥ 0    | `Φ(d_1) ∈ [0, 1]` |
| γ = ∂²_S V   | > 0    | `ϕ(d_1) > 0`, positive denominator |
| ν = ∂_σ V    | > 0    | `S · ϕ(d_1) · √τ > 0` (already in ImpliedVolatility.lean) |
| ρ = ∂_r V    | ≥ 0    | `K · τ · e^{−rτ} · Φ(d_2) ≥ 0` |
| ∂_K V        | ≤ 0    | `−e^{−rτ} · Φ(d_2) ≤ 0` (call decreases in strike) |
| ∂²_K V       | ≥ 0    | `e^{−rτ} · ϕ(d_2)/(K σ √τ) ≥ 0` (Breeden-Litzenberger) |

Read through the mean value theorem, these signs say that a call is increasing and convex in
spot, increasing in vol, decreasing and convex in strike, and increasing in rate. This file
states only the signs of the formulas, each the derivative of the price by the lemma cited
below. Stated as properties of the price elsewhere: convexity in spot (`bsV_spot_convexOn`),
strict monotonicity in vol (`bsV_strictMonoOn_sigma`), convexity in strike
(`bsV_strike_convexOn`), and a call non-increasing in the dividend yield (`antitone_bsVDiv_q`,
`DividendsGreeks.lean`). Monotonicity in spot, strike and rate is not stated as such.

## Main results

* `bsV_delta_nonneg`, `bsV_delta_le_one`: `Φ(d_1) ∈ [0, 1]` (`∂_S V` by `hasDerivAt_bsV_S`).
* `bsV_gamma_pos`: the gamma formula, `∂²_S V` by `hasDerivAt_deriv_bsV_S`, is `> 0`.
* `bsV_rho_nonneg`: the rho formula, `∂_r V` by `hasDerivAt_bsV_r`, is `≥ 0`.
* `bsV_partial_K_nonpos`: the formula `∂_K V` of `hasDerivAt_bsV_K` is `≤ 0`.
* `bsV_partial_KK_nonneg`: the formula `∂²_K V` of `hasDerivAt_deriv_bsV_K` is `≥ 0`.
* `bsV_theta_tau_nonneg`: for `S, K, σ ≥ 0` and `r ≥ 0` the formula `∂_τ V` of
  `hasDerivAt_bsV_tau` is `≥ 0` (calendar theta `Θ = −∂_τ V ≤ 0`, Hull §19.5).
* `bsP_delta_nonpos`, `bsP_rho_nonpos`: the put column of Hull Table 19.6 (put delta
  `Φ(d₁) − 1 ≤ 0`, the formula of `hasDerivAt_bsP_S`; put rho `≤ 0` for `K, τ ≥ 0`, the formula
  of `hasDerivAt_bsP_r`); put vega equals call vega (`hasDerivAt_bsP_sigma`), whose
  sign is `bsV_vega_pos`. Put theta has no unconditional sign: for `r > 0` a deep
  in-the-money put has positive calendar theta (`Θ_put → r K e^{−rτ}` as `S → 0`; not
  formalized here).

## Tags

Greeks, delta gamma vega, sign of sensitivities, option sensitivities, monotonicity of price,
MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

/-! ## Delta sign constraints -/

/-- **Call delta is non-negative**: `0 ≤ Φ(d_1)`. -/
theorem bsV_delta_nonneg (S K r σ τ : ℝ) : 0 ≤ Phi (bsd1 S K r σ τ) :=
  Phi_nonneg _

/-- **Call delta is at most 1**: `Φ(d_1) ≤ 1`. -/
theorem bsV_delta_le_one (S K r σ τ : ℝ) : Phi (bsd1 S K r σ τ) ≤ 1 :=
  Phi_le_one _

/-! ## Gamma sign constraint -/

/-- **Call gamma is strictly positive**: the gamma formula `ϕ(d_1) / (S σ √τ)`, which is
`∂²_S V` by `hasDerivAt_deriv_bsV_S`, is positive for `S, σ, τ > 0`. Convexity in spot is
`bsV_spot_convexOn`, strict convexity `bsV_spot_strictConvexOn` (`SpotConvexity.lean`). -/
theorem bsV_gamma_pos {K r σ : ℝ} (_hK : 0 < K) (hσ : 0 < σ)
    {S τ : ℝ} (hS : 0 < S) (hτ : 0 < τ) :
    0 < gaussianPDFReal 0 1 (bsd1 S K r σ τ) / (S * σ * Real.sqrt τ) := by
  have h_pdf_pos : 0 < gaussianPDFReal 0 1 (bsd1 S K r σ τ) :=
    gaussianPDFReal_pos 0 1 _ (one_ne_zero : (1 : ℝ≥0) ≠ 0)
  have h_den_pos : 0 < S * σ * Real.sqrt τ :=
    mul_pos (mul_pos hS hσ) (Real.sqrt_pos.mpr hτ)
  exact div_pos h_pdf_pos h_den_pos

/-! ## Rho sign constraint -/

/-- **Call rho is non-negative**: `∂_r V = K · τ · e^{−rτ} · Φ(d_2) ≥ 0`
for `K ≥ 0` and `τ ≥ 0` (the formula is `∂_r V` by `hasDerivAt_bsV_r`). Read through the mean
value theorem, the call price increases in the risk-free rate; that monotonicity is not stated. -/
theorem bsV_rho_nonneg {K τ : ℝ} (hK : 0 ≤ K) (hτ : 0 ≤ τ) (S r σ : ℝ) :
    0 ≤ K * τ * Real.exp (-(r * τ)) * Phi (bsd2 S K r σ τ) := by
  have h_exp_nn : 0 ≤ Real.exp (-(r * τ)) := (Real.exp_pos _).le
  have h_Phi_nn : 0 ≤ Phi (bsd2 S K r σ τ) := Phi_nonneg _
  exact mul_nonneg (mul_nonneg (mul_nonneg hK hτ) h_exp_nn) h_Phi_nn

/-! ## Strike-direction sign constraints -/

/-- **Partial in strike is non-positive**: `∂_K V = −e^{−rτ} · Φ(d_2) ≤ 0` (the formula is
`∂_K V` by `hasDerivAt_bsV_K`). Read through the mean value theorem, the call price decreases
in the strike; that monotonicity is not stated. -/
theorem bsV_partial_K_nonpos (S K r σ τ : ℝ) :
    -(Real.exp (-(r * τ)) * Phi (bsd2 S K r σ τ)) ≤ 0 := by
  have h_exp_nn : 0 ≤ Real.exp (-(r * τ)) := (Real.exp_pos _).le
  have h_Phi_nn : 0 ≤ Phi (bsd2 S K r σ τ) := Phi_nonneg _
  have := mul_nonneg h_exp_nn h_Phi_nn
  linarith

/-- **Second partial in strike is non-negative**: `∂²_K V = e^{−rτ} · ϕ(d_2) /
(K · σ · √τ) ≥ 0` for `K, σ, τ > 0`. This is the *infinitesimal* face of
butterfly non-negativity (`butterfly_payoff_nonneg`); via Breeden-Litzenberger
it equals `e^{−rτ}` times the implied PDF, which must be non-negative because
it *is* a probability density. -/
theorem bsV_partial_KK_nonneg {K σ τ : ℝ} (hK : 0 < K) (hσ : 0 < σ) (hτ : 0 < τ)
    (S r : ℝ) :
    0 ≤ Real.exp (-(r * τ)) * gaussianPDFReal 0 1 (bsd2 S K r σ τ) /
          (K * σ * Real.sqrt τ) := by
  have h_exp_nn : 0 ≤ Real.exp (-(r * τ)) := (Real.exp_pos _).le
  have h_pdf_nn : 0 ≤ gaussianPDFReal 0 1 (bsd2 S K r σ τ) :=
    gaussianPDFReal_nonneg _ _ _
  have h_num_nn : 0 ≤ Real.exp (-(r * τ)) * gaussianPDFReal 0 1 (bsd2 S K r σ τ) :=
    mul_nonneg h_exp_nn h_pdf_nn
  have h_den_pos : 0 < K * σ * Real.sqrt τ :=
    mul_pos (mul_pos hK hσ) (Real.sqrt_pos.mpr hτ)
  exact div_nonneg h_num_nn h_den_pos.le

/-! ## Theta and put-side sign constraints -/

/-- **Call theta sign**: for `S, K, σ ≥ 0` and `r ≥ 0` the formula
`σ S ϕ(d₁)/(2√τ) + r K e^{−rτ} Φ(d₂)`, which is `∂_τ V` by `hasDerivAt_bsV_tau` (for
`K, σ, S, τ > 0`), is `≥ 0`; i.e. the calendar theta `Θ = −∂_τ V` of a call on a
non-dividend-paying stock is `≤ 0`. -/
theorem bsV_theta_tau_nonneg {S K r σ τ : ℝ} (hS : 0 ≤ S) (hK : 0 ≤ K) (hr : 0 ≤ r)
    (hσ : 0 ≤ σ) :
    0 ≤ σ * S * gaussianPDFReal 0 1 (bsd1 S K r σ τ) / (2 * Real.sqrt τ)
        + r * K * Real.exp (-(r * τ)) * Phi (bsd2 S K r σ τ) := by
  have := gaussianPDFReal_nonneg 0 1 (bsd1 S K r σ τ)
  have := Phi_nonneg (bsd2 S K r σ τ)
  positivity

/-- **Put delta is non-positive**: `Φ(d₁) − 1 ≤ 0`, the formula that is `∂_S P` by
`hasDerivAt_bsP_S`. -/
theorem bsP_delta_nonpos (S K r σ τ : ℝ) : Phi (bsd1 S K r σ τ) - 1 ≤ 0 :=
  sub_nonpos.mpr (bsV_delta_le_one S K r σ τ)

/-- **Put rho is non-positive**: `∂_r P = −K τ e^{−rτ} Φ(−d₂) ≤ 0` for `K ≥ 0` and `τ ≥ 0`
(the formula is `∂_r P` by `hasDerivAt_bsP_r`). -/
theorem bsP_rho_nonpos {K τ : ℝ} (hK : 0 ≤ K) (hτ : 0 ≤ τ) (S r σ : ℝ) :
    -(K * τ * Real.exp (-(r * τ)) * Phi (-bsd2 S K r σ τ)) ≤ 0 := by
  have := Phi_nonneg (-bsd2 S K r σ τ)
  exact neg_nonpos.mpr (by positivity)

end MathFin
