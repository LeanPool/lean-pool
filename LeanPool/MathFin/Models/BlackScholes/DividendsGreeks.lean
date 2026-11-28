/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho, Yang Ye
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.BlackScholes.PutGreeks

/-!
# Black-Scholes-Merton (continuous dividends) Greeks

For the dividends-adjusted call price `V_q(S, σ, T) = S e^{-qT} Φ(d₁') − K e^{-rT} Φ(d₂')`
with `d_i' = bsdi S K (r-q) σ T`, we identify `V_q = e^{-qT} · bsV(K, r-q, σ, S, T)`
and derive the Greeks via existing call Greeks at effective drift `r − q`.

## Main definitions

* `bsVDiv`: the dividend-adjusted call closed form `e^{−qτ} · bsV K (r − q) σ S τ`.
* `bsPDiv`: the dividend-adjusted put closed form `e^{−qτ} · bsP K (r − q) σ S τ`.

## Main results

* `hasDerivAt_bsVDiv_S` — δ_q = e^{-qT} · Φ(d₁').
* `hasDerivAt_deriv_bsVDiv_S` — γ_q = e^{-qT} · ϕ(d₁') / (S σ √τ), from the
  formula-level `hasDerivAt_bsVDiv_SS`.
* `hasDerivAt_bsVDiv_sigma` — vega_q = e^{-qT} · S · ϕ(d₁') · √τ.
* `bsVDiv_pde` — Hull eq. (19.4) with dividend yield: `Θ + (r−q) S Δ + ½ σ² S² Γ = r V`,
  stated on the Greek formulas.
* `bsVDiv_psi_nonpos` — the psi formula `−S τ e^{-qτ} Φ(d₁')` of `hasDerivAt_bsVDiv_q` is `≤ 0`
  for `S, τ ≥ 0`; `antitone_bsVDiv_q` — so, for `K, σ, τ, S > 0`, the call price is
  non-increasing in the dividend yield.
* `bsPDiv`, `bsPDiv_eq_bsVDiv` — the dividend-adjusted put and put-call parity with yield `q`
  (Hull §17.4): `P_q = V_q − S e^{-qτ} + K e^{-rτ}`.
* `hasDerivAt_bsPDiv_q`, `bsPDiv_psi_nonneg` — put psi `∂_q P_q = S τ e^{-qτ} Φ(−d₁')`, and
  that formula is `≥ 0` for `S, τ ≥ 0`; `monotone_bsPDiv_q` — so, for `K, σ, τ, S > 0`, the put
  price is non-decreasing in `q`.

## References

* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], 17.1

## Tags

dividend yield, Black–Scholes–Merton, option Greeks, effective drift, sensitivities, MSC 91G20,
JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real

/-- Dividends-adjusted BS call price. Identity: `V_q = e^{-qT} · bsV(K, r-q, σ, S, T)`. -/
noncomputable def bsVDiv (K r q σ : ℝ) (S τ : ℝ) : ℝ :=
  Real.exp (-(q * τ)) * bsV K (r - q) σ S τ

/-- **BS-Merton delta**: `∂_S V_q = e^{-qT} · Φ(d₁')` where `d₁' = bsd1 S K (r-q) σ T`. -/
lemma hasDerivAt_bsVDiv_S {K r q σ : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    {S τ : ℝ} (hS : 0 < S) (hτ : 0 < τ) :
    HasDerivAt (fun s ↦ bsVDiv K r q σ s τ)
      (Real.exp (-(q * τ)) * Phi (bsd1 S K (r - q) σ τ)) S :=
  (hasDerivAt_bsV_S (r := r - q) hK hσ hS hτ).const_mul (Real.exp (-(q * τ)))

/-- **The BS-Merton gamma formula**: the S-derivative of the delta `e^{-qτ} · Φ(d₁')` is
`e^{-qτ} · ϕ(d₁') / (S σ √τ)`. The second derivative of the price itself is
`hasDerivAt_deriv_bsVDiv_S`. -/
private lemma hasDerivAt_bsVDiv_SS {K r q σ : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    {S τ : ℝ} (hS : 0 < S) (hτ : 0 < τ) :
    HasDerivAt (fun s ↦ Real.exp (-(q * τ)) * Phi (bsd1 s K (r - q) σ τ))
      (Real.exp (-(q * τ)) * gaussianPDFReal 0 1 (bsd1 S K (r - q) σ τ)
        / (S * σ * Real.sqrt τ)) S := by
  have h_bs := hasDerivAt_Phi_bsd1_S (r := r - q) hK hσ hS hτ
  have h := h_bs.const_mul (Real.exp (-(q * τ)))
  convert h using 1
  ring

/-- **BS-Merton gamma**: `∂²V_q/∂S² = e^{-qτ} · ϕ(d₁') / (S σ √τ)`, for the price itself:
the delta `e^{-qτ} · Φ(d₁')` is `∂V_q/∂S` on all of `S > 0` (`hasDerivAt_bsVDiv_S`), and its
derivative is the gamma formula (`hasDerivAt_bsVDiv_SS`). -/
theorem hasDerivAt_deriv_bsVDiv_S {K r q σ : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    {S τ : ℝ} (hS : 0 < S) (hτ : 0 < τ) :
    HasDerivAt (deriv fun s ↦ bsVDiv K r q σ s τ)
      (Real.exp (-(q * τ)) * gaussianPDFReal 0 1 (bsd1 S K (r - q) σ τ)
        / (S * σ * Real.sqrt τ)) S :=
  hasDerivAt_deriv_of_eventually
    ((eventually_gt_nhds hS).mono fun _ hs ↦ hasDerivAt_bsVDiv_S hK hσ hs hτ)
    (hasDerivAt_bsVDiv_SS hK hσ hS hτ)

/-- **BS-Merton vega**: `∂_σ V_q = e^{-qT} · S · ϕ(d₁') · √τ`. -/
lemma hasDerivAt_bsVDiv_sigma {K r q : ℝ} (hK : 0 < K)
    {S σ τ : ℝ} (hS : 0 < S) (hσ : 0 < σ) (hτ : 0 < τ) :
    HasDerivAt (fun s ↦ bsVDiv K r q s S τ)
      (Real.exp (-(q * τ)) * S * gaussianPDFReal 0 1 (bsd1 S K (r - q) σ τ)
        * Real.sqrt τ) σ := by
  have h_bs := hasDerivAt_bsV_sigma (r := r - q) hK hS hσ hτ
  have h := h_bs.const_mul (Real.exp (-(q * τ)))
  convert h using 1 <;> try rfl
  ring

/-- **BS-Merton rho**: `∂_r V_q = K · τ · e^{-rτ} · Φ(d₂')`.

`V_q = e^{-qT} · bsV(K, r-q, σ, S, T)`. Chain rule on `r-q` gives
`∂_r V_q = e^{-qT} · bsV_rho(K, r-q, σ, S, T) = e^{-qT} · K·τ·e^{-(r-q)τ}·Φ(d₂')`,
and `e^{-qT} · e^{-(r-q)τ} = e^{-rτ}`. -/
lemma hasDerivAt_bsVDiv_r {K q σ τ : ℝ} (hK : 0 < K) (hσ : 0 < σ) (hτ : 0 < τ)
    {S : ℝ} (hS : 0 < S) (r : ℝ) :
    HasDerivAt (fun r' ↦ bsVDiv K r' q σ S τ)
      (K * τ * Real.exp (-(r * τ)) * Phi (bsd2 S K (r - q) σ τ)) r := by
  -- Chain rule on r' ↦ r' - q.
  have h_sub_q : HasDerivAt (fun r' : ℝ ↦ r' - q) 1 r := by
    simpa using (hasDerivAt_id r).sub_const q
  have h_bsV_rho := hasDerivAt_bsV_r (σ := σ) (τ := τ) hK hσ hτ hS (r - q)
  have h_comp := h_bsV_rho.comp r h_sub_q
  have h_full := h_comp.const_mul (Real.exp (-(q * τ)))
  unfold bsVDiv
  convert h_full using 1
  all_goals try rfl
  -- Value: e^{-qτ} · (K·τ·e^{-(r-q)τ}·Φ(d_2) · 1) = K·τ·e^{-rτ}·Φ(d_2)
  have h_exp_combine :
      Real.exp (-(q * τ)) * Real.exp (-((r - q) * τ)) = Real.exp (-(r * τ)) := by
    rw [← Real.exp_add]; congr 1; ring
  linear_combination
    -(K * τ * Phi (bsd2 S K (r - q) σ τ)) * h_exp_combine

/-- **BS-Merton psi** (dividend Greek): `∂_q V_q = -S · τ · e^{-qτ} · Φ(d₁')`.

`V_q = e^{-qτ} · bsV(K, r-q, σ, S, τ)`. Product rule:
* `∂_q [e^{-qτ}] = -τ · e^{-qτ}`
* `∂_q [bsV(K, r-q, σ, S, τ)] = -bsV_rho(K, r-q, σ, S, τ) = -K·τ·e^{-(r-q)τ}·Φ(d₂')`

Combining and using `S · e^{-qτ} · Φ(d₁') − K · e^{-rτ} · Φ(d₂') = V_q`,
the result collapses to `-S · τ · e^{-qτ} · Φ(d₁')`. -/
lemma hasDerivAt_bsVDiv_q {K r σ τ : ℝ} (hK : 0 < K) (hσ : 0 < σ) (hτ : 0 < τ)
    {S : ℝ} (hS : 0 < S) (q : ℝ) :
    HasDerivAt (fun q' ↦ bsVDiv K r q' σ S τ)
      (-(S * τ * Real.exp (-(q * τ)) * Phi (bsd1 S K (r - q) σ τ))) q := by
  -- Setup: f(q') = e^{-q'τ}, g(q') = bsV(K, r-q', σ, S, τ). V_q = f·g.
  -- ∂_q' f = -τ · e^{-q'τ}
  have h_f : HasDerivAt (fun q' : ℝ ↦ Real.exp (-(q' * τ)))
      (-τ * Real.exp (-(q * τ))) q := by
    have h_neg : HasDerivAt (fun q' : ℝ ↦ -(q' * τ)) (-τ) q := by
      have := (hasDerivAt_id q).mul_const τ
      convert this.neg using 1 <;> first | rfl | ring
    have h := h_neg.exp
    convert h using 1
    ring
  -- ∂_q' [bsV(K, r-q', σ, S, τ)] via chain rule on (r - q').
  have h_sub : HasDerivAt (fun q' : ℝ ↦ r - q') (-1) q := by
    have := (hasDerivAt_id q).const_sub r
    simpa using this
  have h_bsV_rho := hasDerivAt_bsV_r (σ := σ) (τ := τ) hK hσ hτ hS (r - q)
  have h_g := h_bsV_rho.comp q h_sub
  -- h_g : HasDerivAt (fun q' ↦ bsV K (r - q') σ S τ) (K·τ·e^{-(r-q)τ}·Φ(d_2) · -1) q
  -- Product: V_q' = f(q') · g(q'), derivative = f'(q)·g(q) + f(q)·g'(q).
  have h_full := h_f.mul h_g
  unfold bsVDiv
  convert h_full using 1 <;> try rfl
  simp only [Function.comp_apply]
  unfold bsV
  ring

/-- **BS-Merton theta** (`∂_τ` form): `∂_τ V_q = -q · V_q + e^{-qτ} · (call_theta_at_drift_{r-q})`.

Product rule on `V_q = e^{-qτ} · bsV(K, r-q, σ, S, τ)`. -/
lemma hasDerivAt_bsVDiv_tau {K r q σ : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    {S τ : ℝ} (hS : 0 < S) (hτ : 0 < τ) :
    HasDerivAt (fun t ↦ bsVDiv K r q σ S t)
      (-(q * bsVDiv K r q σ S τ) +
        Real.exp (-(q * τ)) *
          (σ * S * gaussianPDFReal 0 1 (bsd1 S K (r - q) σ τ) / (2 * Real.sqrt τ)
            + (r - q) * K * Real.exp (-((r - q) * τ)) * Phi (bsd2 S K (r - q) σ τ))) τ := by
  -- f(t) = e^{-qt}, derivative -q · e^{-qt}
  have h_f : HasDerivAt (fun t : ℝ ↦ Real.exp (-(q * t))) (-q * Real.exp (-(q * τ))) τ := by
    have h_neg : HasDerivAt (fun t : ℝ ↦ -(q * t)) (-q) τ := by
      have := (hasDerivAt_id τ).const_mul q
      convert this.neg using 1 <;> first | rfl | ring
    have h := h_neg.exp
    convert h using 1
    ring
  -- g(t) = bsV K (r-q) σ S t, derivative from hasDerivAt_bsV_tau
  have h_g := hasDerivAt_bsV_tau (r := r - q) hK hσ hS hτ
  -- Product
  have h_full := h_f.mul h_g
  unfold bsVDiv
  convert h_full using 1
  ring

/-- **Black–Scholes–Merton PDE with dividend yield** (Hull eq. 19.4 with `q`): writing
`Θ = −∂_τ V_q` (calendar theta, `hasDerivAt_bsVDiv_tau`), `Δ = e^{-qτ} Φ(d₁')`
(`hasDerivAt_bsVDiv_S`) and `Γ = e^{-qτ} ϕ(d₁')/(S σ √τ)` (`hasDerivAt_deriv_bsVDiv_S`), the
three formulas satisfy `Θ + (r − q) S Δ + ½ σ² S² Γ = r V_q` for `σ, S, τ > 0`. Stated on the
formulas, as `bs_pde_holds` is. -/
theorem bsVDiv_pde {K r q σ : ℝ} (hσ : 0 < σ) {S τ : ℝ} (hS : 0 < S) (hτ : 0 < τ) :
    -(-(q * bsVDiv K r q σ S τ) +
        Real.exp (-(q * τ)) *
          (σ * S * gaussianPDFReal 0 1 (bsd1 S K (r - q) σ τ) / (2 * Real.sqrt τ)
            + (r - q) * K * Real.exp (-((r - q) * τ)) * Phi (bsd2 S K (r - q) σ τ))) +
      (r - q) * S * (Real.exp (-(q * τ)) * Phi (bsd1 S K (r - q) σ τ)) +
      (1 / 2 : ℝ) * σ ^ 2 * S ^ 2 *
        (Real.exp (-(q * τ)) * gaussianPDFReal 0 1 (bsd1 S K (r - q) σ τ)
          / (S * σ * Real.sqrt τ)) =
      r * bsVDiv K r q σ S τ := by
  have h_sqrt_ne : Real.sqrt τ ≠ 0 := (Real.sqrt_pos.mpr hτ).ne'
  have hS_ne : S ≠ 0 := hS.ne'
  have hσ_ne : σ ≠ 0 := hσ.ne'
  rw [bsVDiv, bsV]
  field_simp
  ring

/-- **BS-Merton psi sign**: the psi formula `∂_q V_q = −S τ e^{-qτ} Φ(d₁')` of
`hasDerivAt_bsVDiv_q` is `≤ 0` for `S ≥ 0` and `τ ≥ 0`. -/
theorem bsVDiv_psi_nonpos {S τ : ℝ} (hS : 0 ≤ S) (hτ : 0 ≤ τ) (K r q σ : ℝ) :
    -(S * τ * Real.exp (-(q * τ)) * Phi (bsd1 S K (r - q) σ τ)) ≤ 0 := by
  have := Phi_nonneg (bsd1 S K (r - q) σ τ)
  exact neg_nonpos.mpr (by positivity)

/-- **The call is worth no more under a higher dividend yield**: for `K, σ, τ, S > 0`,
`q ↦ V_q` is antitone (non-increasing; strictness is not stated), by the mean value theorem
from `hasDerivAt_bsVDiv_q` and the sign `bsVDiv_psi_nonpos`. -/
theorem antitone_bsVDiv_q {K r σ τ : ℝ} (hK : 0 < K) (hσ : 0 < σ) (hτ : 0 < τ)
    {S : ℝ} (hS : 0 < S) :
    Antitone fun q ↦ bsVDiv K r q σ S τ :=
  antitone_of_hasDerivAt_nonpos (fun q ↦ hasDerivAt_bsVDiv_q hK hσ hτ hS q)
    fun q ↦ bsVDiv_psi_nonpos hS.le hτ.le K r q σ

/-- Dividends-adjusted BS put closed form, defined as `P_q = e^{-qτ} · bsP(K, r-q, σ, S, τ)`,
which unfolds to `K e^{-rτ} Φ(−d₂') − S e^{-qτ} Φ(−d₁')`. That it is a discounted expected
payoff is not stated here. -/
noncomputable def bsPDiv (K r q σ : ℝ) (S τ : ℝ) : ℝ :=
  Real.exp (-(q * τ)) * bsP K (r - q) σ S τ

/-- **Put-call parity with a continuous dividend yield**:
`P_q = V_q − S e^{-qτ} + K e^{-rτ}`. -/
theorem bsPDiv_eq_bsVDiv (K r q σ S τ : ℝ) :
    bsPDiv K r q σ S τ = bsVDiv K r q σ S τ - S * Real.exp (-(q * τ))
      + K * Real.exp (-(r * τ)) := by
  have h : Real.exp (-(q * τ)) * Real.exp (-((r - q) * τ)) = Real.exp (-(r * τ)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [bsPDiv, bsVDiv, bsP_eq_bsV]
  linear_combination K * h

/-- **Put psi**: `∂_q P_q = S τ e^{-qτ} Φ(−d₁')`, via parity and `hasDerivAt_bsVDiv_q`. -/
lemma hasDerivAt_bsPDiv_q {K r σ τ : ℝ} (hK : 0 < K) (hσ : 0 < σ) (hτ : 0 < τ)
    {S : ℝ} (hS : 0 < S) (q : ℝ) :
    HasDerivAt (fun q' ↦ bsPDiv K r q' σ S τ)
      (S * τ * Real.exp (-(q * τ)) * Phi (-bsd1 S K (r - q) σ τ)) q := by
  have h_eq : (fun q' : ℝ ↦ bsPDiv K r q' σ S τ) = fun q' ↦
      bsVDiv K r q' σ S τ - S * Real.exp (-(q' * τ)) + K * Real.exp (-(r * τ)) :=
    funext fun q' ↦ bsPDiv_eq_bsVDiv K r q' σ S τ
  rw [h_eq]
  have h_neg : HasDerivAt (fun q' : ℝ ↦ -(q' * τ)) (-τ) q := (hasDerivAt_mul_const τ).neg
  have h := ((hasDerivAt_bsVDiv_q (r := r) hK hσ hτ hS q).sub (h_neg.exp.const_mul S)).add_const
    (K * Real.exp (-(r * τ)))
  convert h using 1
  linear_combination S * τ * Real.exp (-(q * τ)) * Phi_add_Phi_neg (bsd1 S K (r - q) σ τ)

/-- **Put psi sign**: the put psi formula `∂_q P_q = S τ e^{-qτ} Φ(−d₁')` of
`hasDerivAt_bsPDiv_q` is `≥ 0` for `S ≥ 0` and `τ ≥ 0`. -/
theorem bsPDiv_psi_nonneg {S τ : ℝ} (hS : 0 ≤ S) (hτ : 0 ≤ τ) (K r q σ : ℝ) :
    0 ≤ S * τ * Real.exp (-(q * τ)) * Phi (-bsd1 S K (r - q) σ τ) := by
  have := Phi_nonneg (-bsd1 S K (r - q) σ τ)
  positivity

/-- **The put is worth no less under a higher dividend yield**: for `K, σ, τ, S > 0`,
`q ↦ P_q` is monotone (non-decreasing; strictness is not stated), by the mean value theorem
from `hasDerivAt_bsPDiv_q` and the sign `bsPDiv_psi_nonneg`. -/
theorem monotone_bsPDiv_q {K r σ τ : ℝ} (hK : 0 < K) (hσ : 0 < σ) (hτ : 0 < τ)
    {S : ℝ} (hS : 0 < S) :
    Monotone fun q ↦ bsPDiv K r q σ S τ :=
  monotone_of_hasDerivAt_nonneg (fun q ↦ hasDerivAt_bsPDiv_q hK hσ hτ hS q)
    fun q ↦ bsPDiv_psi_nonneg hS.le hτ.le K r q σ

end MathFin
