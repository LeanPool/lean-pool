/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.BlackScholes.Call
public import LeanPool.MathFin.Probability.Gaussian.GaussianCDFDeriv
public import LeanPool.MathFin.Probability.Analysis.DerivOfDeriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Black–Scholes PDE — forward direction

Given the BS call price `V(S, t) = S · Φ(d₁) − K · e^{-r(T−t)} · Φ(d₂)`,
this file shows `V` satisfies the Black–Scholes PDE

  `∂_t V + (1/2) σ² S² ∂²_S V + r S ∂_S V − r V = 0`

for `0 < S, t < T, 0 < K, 0 < σ`.

This is the FORWARD direction (uniqueness is left as upstream work).

The proof leverages:
* `hasDerivAt_Phi` (FTC for `Φ' = ϕ`, proved in `GaussianCDFDeriv`),
* the "Black–Scholes identity" `S · ϕ(d₁) = K · e^{-r(T−t)} · ϕ(d₂)`,
* chain rule on `d₁, d₂` to compute `∂_S V`, `∂²_S V`, `∂_t V`.

## Main definitions

* `bsV`: the Black–Scholes call price as a function of the spot `S` and the time to maturity `τ`,
  `V(S, τ) = S · Φ(d₁) − K · e^{−rτ} · Φ(d₂)`.

## Main results

* `bs_identity` — `S · ϕ(d₁) = K · e^{-r τ} · ϕ(d₂)`,
* `hasDerivAt_bsd1_S`, `hasDerivAt_bsd1_tau` — chain-rule pieces for d₁,
* `bs_pde_holds` — the BS price satisfies the BS PDE.

## References

* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], 19.3; 19.5
* [S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*][ShreveSCFII], 4.5

## Tags

Black–Scholes PDE, parabolic equation, backward equation, option price PDE, Greeks identity,
MSC 91G20, MSC 35K10, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real

/-! ### Black–Scholes identity: `S · ϕ(d₁) = K · e^{-r(T-t)} · ϕ(d₂)` -/

/-- The "Black–Scholes identity" — algebraic content of `S · ϕ(d₁) = K · e^{-rτ} · ϕ(d₂)`.
    Substituting `d₂ = d₁ - σ√τ`, the ratio `ϕ(d₁)/ϕ(d₂)` simplifies to
    `K · e^{-rτ} / S` via `exp(log(S/K) + rτ) = (S/K) · exp(rτ)`.

    We state it parametrically: for `S > 0, K > 0, σ > 0, τ > 0`, with
    `d₁ = (log(S/K) + (r + σ²/2) τ) / (σ√τ)` and `d₂ = d₁ - σ√τ`,
    `S · ϕ(d₁) = K · exp(-rτ) · ϕ(d₂)`. -/
lemma bs_identity {S K r σ τ : ℝ} (hS : 0 < S) (hK : 0 < K) (hσ : 0 < σ) (hτ : 0 < τ) :
    S * gaussianPDFReal 0 1 (bsd1 S K r σ τ)
      = K * Real.exp (-(r * τ)) * gaussianPDFReal 0 1 (bsd2 S K r σ τ) := by
  set d₁ := bsd1 S K r σ τ with hd₁_def
  set d₂ := bsd2 S K r σ τ with hd₂_def
  have h_sqrt_τ_pos : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have h_sqrt_τ_ne : Real.sqrt τ ≠ 0 := h_sqrt_τ_pos.ne'
  have h_στ : 0 < σ * Real.sqrt τ := mul_pos hσ h_sqrt_τ_pos
  have h_στ_ne : σ * Real.sqrt τ ≠ 0 := h_στ.ne'
  have h_sqrt_τ_sq : Real.sqrt τ ^ 2 = τ := Real.sq_sqrt hτ.le
  -- d₁ - d₂ = σ √τ
  have h_d₁_sub_d₂ : d₁ - d₂ = σ * Real.sqrt τ := by
    rw [hd₂_def, bsd2]; ring
  -- (d₁ - d₂)(d₁ + d₂) = d₁² - d₂², so d₂² - d₁² = -(d₁-d₂)(d₁+d₂) = -σ√τ · (d₁+d₂)
  -- Compute d₁ + d₂ algebraically:
  -- d₁ + d₂ = 2 d₁ - σ√τ
  --        = 2(log(S/K) + (r + σ²/2)τ)/(σ√τ) - σ√τ
  --        = (2 log(S/K) + 2rτ + σ²τ)/(σ√τ) - σ√τ
  --        = (2 log(S/K) + 2rτ + σ²τ - σ²τ)/(σ√τ)
  --        = (2 log(S/K) + 2rτ)/(σ√τ)
  have h_d₁_plus_d₂ : d₁ + d₂ = 2 * (Real.log (S / K) + r * τ) / (σ * Real.sqrt τ) := by
    rw [hd₁_def, hd₂_def, bsd2, bsd1]
    field_simp
    ring_nf
    rw [show σ ^ 2 * τ = (σ * Real.sqrt τ) ^ 2 from by rw [mul_pow, h_sqrt_τ_sq]]
    ring
  -- Therefore d₁² - d₂² = (d₁ + d₂)(d₁ - d₂) = 2(log(S/K) + rτ)
  have h_d₁_sq_sub : d₁ ^ 2 - d₂ ^ 2 = 2 * (Real.log (S / K) + r * τ) := by
    have h_diff_sq : d₁ ^ 2 - d₂ ^ 2 = (d₁ + d₂) * (d₁ - d₂) := by ring
    rw [h_diff_sq, h_d₁_plus_d₂, h_d₁_sub_d₂]
    field_simp
  -- ϕ(d₁) / ϕ(d₂) = exp((d₂² - d₁²) / 2) = exp(-(log(S/K) + rτ)) = K e^{-rτ} / S
  -- So S · ϕ(d₁) = K e^{-rτ} · ϕ(d₂)
  unfold gaussianPDFReal
  simp only [NNReal.coe_one, mul_one, sub_zero]
  -- Goal: S * ((√(2π))⁻¹ * exp(-d₁²/2)) = K * exp(-rτ) * ((√(2π))⁻¹ * exp(-d₂²/2))
  -- Strategy: combine all exponentials and use exp(log(S/K)) = S/K.
  have hSK_pos : 0 < S / K := div_pos hS hK
  have h_log : (d₁ ^ 2 - d₂ ^ 2) / 2 - r * τ = Real.log (S / K) := by
    rw [h_d₁_sq_sub]; ring
  -- Rewrite as `K * exp(...)` on both sides and equate exponents.
  rw [show S = K * Real.exp (Real.log (S / K)) from by
    rw [Real.exp_log hSK_pos]; field_simp]
  rw [show K * Real.exp (Real.log (S / K)) * ((Real.sqrt (2 * π))⁻¹ * Real.exp (-d₁ ^ 2 / 2))
        = K * (Real.sqrt (2 * π))⁻¹ * Real.exp (Real.log (S / K) + (-d₁ ^ 2 / 2)) from by
    rw [Real.exp_add]; ring]
  rw [show K * Real.exp (-(r * τ)) * ((Real.sqrt (2 * π))⁻¹ * Real.exp (-d₂ ^ 2 / 2))
        = K * (Real.sqrt (2 * π))⁻¹ * Real.exp (-(r * τ) + (-d₂ ^ 2 / 2)) from by
    rw [Real.exp_add]; ring]
  congr 2
  -- Goal: log(S/K) + -d₁²/2 = -(r*τ) + -d₂²/2
  linear_combination -(1 / 2) * h_d₁_sq_sub

/-! ### Partial derivatives of `bsd1`, `bsd2` w.r.t. `S` -/

/-- `∂_S d₁(S, K, r, σ, τ) = 1 / (S · σ · √τ)`. -/
lemma hasDerivAt_bsd1_S {K r σ τ : ℝ} (hK : 0 < K) (hσ : 0 < σ) (hτ : 0 < τ)
    {S : ℝ} (hS : 0 < S) :
    HasDerivAt (fun s ↦ bsd1 s K r σ τ) (1 / (S * σ * Real.sqrt τ)) S := by
  have h_sqrt_τ_pos : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have h_sqrt_τ_ne : Real.sqrt τ ≠ 0 := h_sqrt_τ_pos.ne'
  have hσ_ne : σ ≠ 0 := hσ.ne'
  have h_sK_pos : 0 < S / K := div_pos hS hK
  -- s ↦ s/K: HasDerivAt _ (1/K) S
  have h_div : HasDerivAt (fun s : ℝ ↦ s / K) (1 / K) S := by
    have := (hasDerivAt_id S).div_const K
    simpa using this
  -- s ↦ log(s/K): HasDerivAt _ (1/S) S (chain rule)
  have h_log : HasDerivAt (fun s : ℝ ↦ Real.log (s / K)) (1 / S) S := by
    have := (Real.hasDerivAt_log h_sK_pos.ne').comp S h_div
    convert this using 1 <;> try rfl
    field_simp
  -- s ↦ log(s/K) + (r + σ²/2)τ: same derivative
  have h_num : HasDerivAt (fun s : ℝ ↦ Real.log (s / K) + (r + σ ^ 2 / 2) * τ) (1 / S) S := by
    simpa using h_log.add_const ((r + σ ^ 2 / 2) * τ)
  -- s ↦ (log(s/K) + (r + σ²/2)τ) / (σ √τ): derivative is (1/S) / (σ√τ)
  have h_div_στ : HasDerivAt
      (fun s : ℝ ↦ (Real.log (s / K) + (r + σ ^ 2 / 2) * τ) / (σ * Real.sqrt τ))
      ((1 / S) / (σ * Real.sqrt τ)) S :=
    h_num.div_const (σ * Real.sqrt τ)
  have h_val_eq : (1 : ℝ) / (S * σ * Real.sqrt τ) = 1 / S / (σ * Real.sqrt τ) := by field_simp
  rw [h_val_eq]
  exact h_div_στ

/-- `∂_S d₂(S, K, r, σ, τ) = 1 / (S · σ · √τ)` (same as `∂_S d₁` since `d₂ − d₁` is
`S`-independent). -/
lemma hasDerivAt_bsd2_S {K r σ τ : ℝ} (hK : 0 < K) (hσ : 0 < σ) (hτ : 0 < τ)
    {S : ℝ} (hS : 0 < S) :
    HasDerivAt (fun s ↦ bsd2 s K r σ τ) (1 / (S * σ * Real.sqrt τ)) S := by
  have h_diff := (hasDerivAt_bsd1_S (r := r) hK hσ hτ hS).sub_const (σ * Real.sqrt τ)
  have h_fun_eq : (fun s : ℝ ↦ bsd1 s K r σ τ - σ * Real.sqrt τ)
        = (fun s : ℝ ↦ bsd2 s K r σ τ) := by
    funext s; rw [bsd2]
  rw [← h_fun_eq]
  exact h_diff

/-! ### Partial derivatives of `bsd1`, `bsd2` w.r.t. `τ` -/

/-- `∂_τ d₁(S, K, r, σ, τ) = ((r + σ²/2)τ − log(S/K)) / (2 σ τ √τ)`. -/
lemma hasDerivAt_bsd1_tau (S K r σ : ℝ) (hσ : 0 < σ)
    {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt (fun t ↦ bsd1 S K r σ t)
      (((r + σ ^ 2 / 2) * τ - Real.log (S / K)) / (2 * σ * τ * Real.sqrt τ)) τ := by
  have h_sqrt_pos : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have h_sqrt_ne : Real.sqrt τ ≠ 0 := h_sqrt_pos.ne'
  have hσ_ne : σ ≠ 0 := hσ.ne'
  have hτ_ne : τ ≠ 0 := hτ.ne'
  have h_στ : 0 < σ * Real.sqrt τ := mul_pos hσ h_sqrt_pos
  have h_στ_ne : σ * Real.sqrt τ ≠ 0 := h_στ.ne'
  have h_sqrt_sq : Real.sqrt τ ^ 2 = τ := Real.sq_sqrt hτ.le
  -- Numerator: f(τ) = log(S/K) + (r + σ²/2)τ → f' = r + σ²/2
  have h_f : HasDerivAt (fun t : ℝ ↦ Real.log (S / K) + (r + σ ^ 2 / 2) * t)
      (r + σ ^ 2 / 2) τ := by
    have h_lin : HasDerivAt (fun t : ℝ ↦ (r + σ ^ 2 / 2) * t) (r + σ ^ 2 / 2) τ := by
      have := (hasDerivAt_id τ).const_mul (r + σ ^ 2 / 2)
      simpa using this
    exact h_lin.const_add (Real.log (S / K))
  -- Denominator: g(τ) = σ √τ → g' = σ/(2√τ)
  have h_g : HasDerivAt (fun t : ℝ ↦ σ * Real.sqrt t) (σ / (2 * Real.sqrt τ)) τ := by
    have h_sqrt_deriv : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt τ)) τ :=
      Real.hasDerivAt_sqrt hτ.ne'
    have := h_sqrt_deriv.const_mul σ
    convert this using 1
    field_simp
  -- Quotient rule
  have h_quot := h_f.div h_g h_στ_ne
  have h_fun_eq : (fun t : ℝ ↦ (Real.log (S / K) + (r + σ ^ 2 / 2) * t) / (σ * Real.sqrt t))
        = (fun t : ℝ ↦ bsd1 S K r σ t) := by
    funext t; rfl
  rw [← h_fun_eq]
  convert h_quot using 1
  -- Value: ((r+σ²/2)τ - log(S/K))/(2 σ τ √τ) = ((r+σ²/2)(σ√τ) - (log + (r+σ²/2)τ)(σ/(2√τ))) /
  -- (σ√τ)²
  field_simp
  rw [h_sqrt_sq]
  ring

/-- `∂_τ d₂(S, K, r, σ, τ) = ∂_τ d₁ − σ/(2√τ)`. -/
lemma hasDerivAt_bsd2_tau (S K r σ : ℝ) (hσ : 0 < σ)
    {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt (fun t ↦ bsd2 S K r σ t)
      (((r + σ ^ 2 / 2) * τ - Real.log (S / K)) / (2 * σ * τ * Real.sqrt τ)
        - σ / (2 * Real.sqrt τ)) τ := by
  have h_d1 := hasDerivAt_bsd1_tau S K r σ hσ hτ
  have h_sqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt τ)) τ := Real.hasDerivAt_sqrt hτ.ne'
  have h_const_mul := h_sqrt.const_mul σ
  -- h_const_mul : HasDerivAt (fun t ↦ σ * sqrt t) (σ * (1/(2√τ))) τ
  have h_diff := h_d1.sub h_const_mul
  have h_fun_eq : (fun t : ℝ ↦ bsd1 S K r σ t - σ * Real.sqrt t)
        = (fun t : ℝ ↦ bsd2 S K r σ t) := by
    funext t; rw [bsd2]
  rw [← h_fun_eq]
  convert h_diff using 1
  field_simp

/-! ### Partial derivatives of `bsd1`, `bsd2` w.r.t. `σ` -/

/-- `∂_σ d₁(S, K, r, σ, τ) = (σ²τ/2 − log(S/K) − rτ) / (σ²√τ)`. -/
lemma hasDerivAt_bsd1_sigma (S K r : ℝ) {σ : ℝ} (hσ : 0 < σ)
    {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt (fun s ↦ bsd1 S K r s τ)
      ((σ ^ 2 * τ / 2 - Real.log (S / K) - r * τ) / (σ ^ 2 * Real.sqrt τ)) σ := by
  have h_sqrt_pos : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have h_sqrt_ne : Real.sqrt τ ≠ 0 := h_sqrt_pos.ne'
  have hσ_ne : σ ≠ 0 := hσ.ne'
  have hτ_ne : τ ≠ 0 := hτ.ne'
  have h_στ : 0 < σ * Real.sqrt τ := mul_pos hσ h_sqrt_pos
  have h_στ_ne : σ * Real.sqrt τ ≠ 0 := h_στ.ne'
  have h_sqrt_sq : Real.sqrt τ ^ 2 = τ := Real.sq_sqrt hτ.le
  -- N(σ) = log(S/K) + (r + σ²/2) τ; N'(σ) = στ
  have h_sq : HasDerivAt (fun s : ℝ ↦ s ^ 2) (2 * σ) σ := by
    simpa using hasDerivAt_pow 2 σ
  have h_sq_div : HasDerivAt (fun s : ℝ ↦ s ^ 2 / 2) σ σ := by
    have := h_sq.div_const 2; simpa using this
  have h_inner : HasDerivAt (fun s : ℝ ↦ r + s ^ 2 / 2) σ σ := h_sq_div.const_add r
  have h_inner_mul : HasDerivAt (fun s : ℝ ↦ (r + s ^ 2 / 2) * τ) (σ * τ) σ := by
    have := h_inner.mul_const τ; simpa using this
  have h_N : HasDerivAt (fun s : ℝ ↦ Real.log (S / K) + (r + s ^ 2 / 2) * τ)
      (σ * τ) σ := h_inner_mul.const_add (Real.log (S / K))
  -- D(σ) = σ√τ; D'(σ) = √τ
  have h_D : HasDerivAt (fun s : ℝ ↦ s * Real.sqrt τ) (Real.sqrt τ) σ := by
    have := (hasDerivAt_id σ).mul_const (Real.sqrt τ); simpa using this
  -- Quotient rule
  have h_quot := h_N.div h_D h_στ_ne
  have h_fun_eq : (fun s : ℝ ↦ (Real.log (S / K) + (r + s ^ 2 / 2) * τ) / (s * Real.sqrt τ))
        = (fun s : ℝ ↦ bsd1 S K r s τ) := by funext s; rfl
  rw [← h_fun_eq]
  convert h_quot using 1
  field_simp
  ring

/-- `∂_σ d₂ = ∂_σ d₁ − √τ` (since `d₂ = d₁ − σ√τ`). -/
lemma hasDerivAt_bsd2_sigma (S K r : ℝ) {σ : ℝ} (hσ : 0 < σ)
    {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt (fun s ↦ bsd2 S K r s τ)
      ((σ ^ 2 * τ / 2 - Real.log (S / K) - r * τ) / (σ ^ 2 * Real.sqrt τ)
        - Real.sqrt τ) σ := by
  have h_d1 := hasDerivAt_bsd1_sigma S K r hσ hτ
  -- ∂_σ (σ √τ) = √τ
  have h_σsqrt : HasDerivAt (fun s : ℝ ↦ s * Real.sqrt τ) (Real.sqrt τ) σ := by
    have := (hasDerivAt_id σ).mul_const (Real.sqrt τ); simpa using this
  have h_diff := h_d1.sub h_σsqrt
  have h_fun_eq : (fun s : ℝ ↦ bsd1 S K r s τ - s * Real.sqrt τ)
        = (fun s : ℝ ↦ bsd2 S K r s τ) := by funext s; rw [bsd2]
  rw [← h_fun_eq]
  exact h_diff

/-! ### Partial derivatives of `bsd1`, `bsd2` w.r.t. `r` -/

/-- `∂_r d₁(S, K, r, σ, τ) = √τ / σ`. -/
lemma hasDerivAt_bsd1_r (S K σ τ : ℝ) (hσ : 0 < σ) (hτ : 0 < τ)
    (r : ℝ) :
    HasDerivAt (fun r' ↦ bsd1 S K r' σ τ) (Real.sqrt τ / σ) r := by
  have h_sqrt_pos : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have h_sqrt_ne : Real.sqrt τ ≠ 0 := h_sqrt_pos.ne'
  have hσ_ne : σ ≠ 0 := hσ.ne'
  -- N(r) = log(S/K) + (r + σ²/2) τ; N'(r) = τ
  have h_id : HasDerivAt (fun r' : ℝ ↦ r') 1 r := hasDerivAt_id r
  have h_inner : HasDerivAt (fun r' : ℝ ↦ r' + σ ^ 2 / 2) 1 r := by
    have := h_id.add_const (σ ^ 2 / 2); simpa using this
  have h_inner_mul : HasDerivAt (fun r' : ℝ ↦ (r' + σ ^ 2 / 2) * τ) τ r := by
    have := h_inner.mul_const τ; simpa using this
  have h_N : HasDerivAt (fun r' : ℝ ↦ Real.log (S / K) + (r' + σ ^ 2 / 2) * τ) τ r :=
    h_inner_mul.const_add (Real.log (S / K))
  -- d_1(r) = N(r) / (σ √τ); D is constant, so ∂_r d_1 = N'(r) / (σ√τ) = τ/(σ√τ) = √τ/σ
  have h_div : HasDerivAt
      (fun r' : ℝ ↦ (Real.log (S / K) + (r' + σ ^ 2 / 2) * τ) / (σ * Real.sqrt τ))
      (τ / (σ * Real.sqrt τ)) r := h_N.div_const (σ * Real.sqrt τ)
  have h_fun_eq : (fun r' : ℝ ↦ (Real.log (S / K) + (r' + σ ^ 2 / 2) * τ) / (σ * Real.sqrt τ))
        = (fun r' : ℝ ↦ bsd1 S K r' σ τ) := by funext r'; rfl
  rw [← h_fun_eq]
  convert h_div using 1
  -- τ/(σ√τ) = √τ/σ
  have h_τ_eq : Real.sqrt τ * Real.sqrt τ = τ := Real.mul_self_sqrt hτ.le
  field_simp
  linarith [h_τ_eq]

/-- `∂_r d₂ = ∂_r d₁ = √τ / σ` (since `d₂ − d₁` is `r`-independent). -/
lemma hasDerivAt_bsd2_r (S K σ τ : ℝ) (hσ : 0 < σ) (hτ : 0 < τ)
    (r : ℝ) :
    HasDerivAt (fun r' ↦ bsd2 S K r' σ τ) (Real.sqrt τ / σ) r := by
  have h_diff := (hasDerivAt_bsd1_r S K σ τ hσ hτ r).sub_const (σ * Real.sqrt τ)
  have h_fun_eq : (fun r' : ℝ ↦ bsd1 S K r' σ τ - σ * Real.sqrt τ)
        = (fun r' : ℝ ↦ bsd2 S K r' σ τ) := by funext r'; rw [bsd2]
  rw [← h_fun_eq]
  exact h_diff

/-! ### Partial derivatives of the Black–Scholes call price `V` -/

/-- The Black–Scholes call price as a function of `(S, τ)` with `τ = T − t`:
`V(S, τ) = S · Φ(d₁) − K · e^{-rτ} · Φ(d₂)`. -/
noncomputable def bsV (K r σ : ℝ) (S τ : ℝ) : ℝ :=
  S * Phi (bsd1 S K r σ τ) - K * Real.exp (-(r * τ)) * Phi (bsd2 S K r σ τ)

/-- The Black–Scholes call price is the discounted expected call payoff: `bs_call_formula`,
stated for `bsV`. -/
lemma integral_bsCall_payoff_eq_bsV {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω}
    [IsProbabilityMeasure Q] {S_0 K r σ T : ℝ} {Z : Ω → ℝ} (h : BSCallHyp Q S_0 K r σ T Z) :
    ∫ ω, rexp (-r * T) * max (bsTerminal S_0 r σ T (Z ω) - K) 0 ∂Q = bsV K r σ S_0 T := by
  rw [bs_call_formula h, bsV, neg_mul]

/-- **Delta**: `∂_S V = Φ(d₁)` — the magic identity makes everything else cancel. -/
lemma hasDerivAt_bsV_S {K r σ : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    {S τ : ℝ} (hS : 0 < S) (hτ : 0 < τ) :
    HasDerivAt (fun s ↦ bsV K r σ s τ) (Phi (bsd1 S K r σ τ)) S := by
  have h_sqrt_τ_pos : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have h_sqrt_τ_ne : Real.sqrt τ ≠ 0 := h_sqrt_τ_pos.ne'
  have hσ_ne : σ ≠ 0 := hσ.ne'
  have hS_ne : S ≠ 0 := hS.ne'
  -- Pieces
  have h_d1_S := hasDerivAt_bsd1_S (r := r) hK hσ hτ hS
  have h_d2_S := hasDerivAt_bsd2_S (r := r) hK hσ hτ hS
  have h_Phi_d1 := (hasDerivAt_Phi (bsd1 S K r σ τ)).comp S h_d1_S
  have h_Phi_d2 := (hasDerivAt_Phi (bsd2 S K r σ τ)).comp S h_d2_S
  -- d/dS [S · Φ(d₁)] = Φ(d₁) + S · pdf(d₁) · ∂_S d₁
  have h_id : HasDerivAt (fun s : ℝ ↦ s) 1 S := hasDerivAt_id S
  have h_S_Phi_d1 := h_id.mul h_Phi_d1
  -- d/dS [K · exp(-rτ) · Φ(d₂)] = K · exp(-rτ) · pdf(d₂) · ∂_S d₂
  have h_K_exp_Phi_d2 := h_Phi_d2.const_mul (K * Real.exp (-(r * τ)))
  have h_V := h_S_Phi_d1.sub h_K_exp_Phi_d2
  have h_fun_eq : (fun s : ℝ ↦ s * Phi (bsd1 s K r σ τ) -
      K * Real.exp (-(r * τ)) * Phi (bsd2 s K r σ τ))
        = (fun s : ℝ ↦ bsV K r σ s τ) := by
    funext s; rfl
  rw [← h_fun_eq]
  convert h_V using 1 <;> try rfl
  -- Value simplification: cancel via magic identity
  have h_bs := bs_identity (r := r) hS hK hσ hτ
  simp only [Function.comp]
  field_simp
  linear_combination -h_bs

/-- **The gamma formula**: the S-derivative of the delta `Φ(d₁(S))` is
`ϕ(d₁) / (S σ √τ)`, by the chain rule. This differentiates the delta's formula; the second
derivative of the price itself is `hasDerivAt_deriv_bsV_S`. -/
lemma hasDerivAt_Phi_bsd1_S {K r σ : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    {S τ : ℝ} (hS : 0 < S) (hτ : 0 < τ) :
    HasDerivAt (fun s ↦ Phi (bsd1 s K r σ τ))
      (gaussianPDFReal 0 1 (bsd1 S K r σ τ) / (S * σ * Real.sqrt τ)) S := by
  -- `S` is `bsd1`'s first argument, so the chain rule is elaborated before its target
  have h := (hasDerivAt_Phi (bsd1 S K r σ τ)).comp S (hasDerivAt_bsd1_S (r := r) hK hσ hτ hS)
  exact h.congr_deriv (mul_one_div _ _)

/-- **Gamma**: `∂²V/∂S² = ϕ(d₁) / (S σ √τ)`, for the call price itself. The delta `Φ(d₁)` is
`∂V/∂S` on all of `S > 0` (`hasDerivAt_bsV_S`), so near `S` the derivative of the price is the
delta formula, whose own derivative is the gamma formula (`hasDerivAt_Phi_bsd1_S`). -/
theorem hasDerivAt_deriv_bsV_S {K r σ : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    {S τ : ℝ} (hS : 0 < S) (hτ : 0 < τ) :
    HasDerivAt (deriv fun s ↦ bsV K r σ s τ)
      (gaussianPDFReal 0 1 (bsd1 S K r σ τ) / (S * σ * Real.sqrt τ)) S :=
  hasDerivAt_deriv_of_eventually
    ((eventually_gt_nhds hS).mono fun _ hs ↦ hasDerivAt_bsV_S hK hσ hs hτ)
    (hasDerivAt_Phi_bsd1_S hK hσ hS hτ)

/-- **Theta (without τ → t sign flip)**: `∂_τ V = σ S ϕ(d₁) / (2 √τ) + r K e^{-rτ} Φ(d₂)`.
The combination of product/chain rules + the magic identity (`K e^{-rτ} ϕ(d₂) = S ϕ(d₁)`)
collapses the `pdf(d₂) ∂_τ d₂` term into `−S ϕ(d₁) ∂_τ d₂`, leaving
`S ϕ(d₁) (∂_τ d₁ − ∂_τ d₂) = S ϕ(d₁) · σ/(2√τ)`. -/
lemma hasDerivAt_bsV_tau {K r σ : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    {S τ : ℝ} (hS : 0 < S) (hτ : 0 < τ) :
    HasDerivAt (fun t ↦ bsV K r σ S t)
      (σ * S * gaussianPDFReal 0 1 (bsd1 S K r σ τ) / (2 * Real.sqrt τ)
        + r * K * Real.exp (-(r * τ)) * Phi (bsd2 S K r σ τ)) τ := by
  have h_sqrt_pos : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have h_sqrt_ne : Real.sqrt τ ≠ 0 := h_sqrt_pos.ne'
  have hτ_ne : τ ≠ 0 := hτ.ne'
  have hσ_ne : σ ≠ 0 := hσ.ne'
  have hS_ne : S ≠ 0 := hS.ne'
  have hK_ne : K ≠ 0 := hK.ne'
  -- Pieces
  have h_d1_τ := hasDerivAt_bsd1_tau S K r σ hσ hτ
  have h_d2_τ := hasDerivAt_bsd2_tau S K r σ hσ hτ
  have h_Phi_d1 := (hasDerivAt_Phi (bsd1 S K r σ τ)).comp τ h_d1_τ
  have h_Phi_d2 := (hasDerivAt_Phi (bsd2 S K r σ τ)).comp τ h_d2_τ
  -- d/dτ[S · Phi(d₁(τ))]
  have h_S_Phi_d1 := h_Phi_d1.const_mul S
  -- d/dτ[exp(-rτ)] = -r exp(-rτ)
  have h_neg_r : HasDerivAt (fun t : ℝ ↦ -(r * t)) (-r) τ := by
    have h1 : HasDerivAt (fun t : ℝ ↦ r * t) r τ := by
      simpa using (hasDerivAt_id τ).const_mul r
    exact h1.neg
  have h_exp : HasDerivAt (fun t : ℝ ↦ Real.exp (-(r * t)))
      (Real.exp (-(r * τ)) * -r) τ := h_neg_r.exp
  -- d/dτ[K · exp(-rτ)] = K · (-r) exp(-rτ)
  have h_K_exp : HasDerivAt (fun t : ℝ ↦ K * Real.exp (-(r * t)))
      (K * (Real.exp (-(r * τ)) * -r)) τ := h_exp.const_mul K
  -- d/dτ[K · exp(-rτ) · Phi(d₂(τ))] = product rule
  have h_K_exp_Phi_d2 := h_K_exp.mul h_Phi_d2
  have h_V := h_S_Phi_d1.sub h_K_exp_Phi_d2
  have h_fun_eq : (fun t : ℝ ↦
      S * (Phi ∘ fun t' ↦ bsd1 S K r σ t') t -
        (fun y ↦ K * Real.exp (-(r * y)) * (Phi ∘ fun t' ↦ bsd2 S K r σ t') y) t)
        = (fun t : ℝ ↦ bsV K r σ S t) := by
    funext t; rfl
  rw [← h_fun_eq]
  convert h_V using 1
  -- Value match using magic identity (field_simp already absorbs √τ² = τ).
  have h_bs := bs_identity (r := r) hS hK hσ hτ
  simp only [Function.comp]
  field_simp
  linear_combination
    (σ ^ 2 * τ - 2 * τ * r + 2 * Real.log (S / K)) * h_bs

/-- **Theta**: `∂_t V = -∂_τ V` via the chain rule on `τ = T − t`. -/
lemma hasDerivAt_bsV_t {K T r σ : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    {S t : ℝ} (hS : 0 < S) (ht_T : t < T) :
    HasDerivAt (fun t' ↦ bsV K r σ S (T - t'))
      (-(σ * S * gaussianPDFReal 0 1 (bsd1 S K r σ (T - t)) / (2 * Real.sqrt (T - t))
        + r * K * Real.exp (-(r * (T - t))) * Phi (bsd2 S K r σ (T - t)))) t := by
  have hτ : 0 < T - t := sub_pos.mpr ht_T
  have h_τ_deriv : HasDerivAt (fun t' : ℝ ↦ T - t') (-1) t := by
    have := (hasDerivAt_id t).const_sub T
    simpa using this
  have h_V_τ := hasDerivAt_bsV_tau (r := r) hK hσ hS hτ
  have h_comp := h_V_τ.comp t h_τ_deriv
  convert h_comp using 1 <;> try rfl
  ring

/-- **Theta in maturity form**: at a fixed calendar date `t`, `∂_T V(S, T − t) = ∂_τ V`, the
negative of the calendar theta `hasDerivAt_bsV_t` (`∂_t V = −∂_τ V`). Theta stated as `∂/∂τ`
or as `∂/∂T` is therefore the same number; theta stated as `∂/∂t` has the opposite sign. -/
lemma hasDerivAt_bsV_maturity {K t r σ : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    {S T : ℝ} (hS : 0 < S) (ht_T : t < T) :
    HasDerivAt (fun T' ↦ bsV K r σ S (T' - t))
      (σ * S * gaussianPDFReal 0 1 (bsd1 S K r σ (T - t)) / (2 * Real.sqrt (T - t))
        + r * K * Real.exp (-(r * (T - t))) * Phi (bsd2 S K r σ (T - t))) T := by
  have h := (hasDerivAt_bsV_tau (r := r) hK hσ hS (sub_pos.mpr ht_T)).comp T
    ((hasDerivAt_id T).sub_const t)
  rwa [mul_one] at h

/-! ### Vega and Rho -/

/-- **Vega**: `∂_σ V = S · ϕ(d₁) · √τ`.

The product/chain rules yield `S · pdf(d₁) · ∂_σ d₁ − K e^{-rτ} · pdf(d₂) · ∂_σ d₂`.
Since `d₂ = d₁ − σ√τ`, we have `∂_σ d₂ = ∂_σ d₁ − √τ`. After substitution the
`∂_σ d₁` terms collapse via the magic identity `S · ϕ(d₁) = K e^{-rτ} · ϕ(d₂)`,
leaving `K e^{-rτ} · ϕ(d₂) · √τ = S · ϕ(d₁) · √τ`. -/
lemma hasDerivAt_bsV_sigma {K r : ℝ} (hK : 0 < K)
    {S σ τ : ℝ} (hS : 0 < S) (hσ : 0 < σ) (hτ : 0 < τ) :
    HasDerivAt (fun s ↦ bsV K r s S τ)
      (S * gaussianPDFReal 0 1 (bsd1 S K r σ τ) * Real.sqrt τ) σ := by
  have h_sqrt_pos : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have h_sqrt_ne : Real.sqrt τ ≠ 0 := h_sqrt_pos.ne'
  have hσ_ne : σ ≠ 0 := hσ.ne'
  have hS_ne : S ≠ 0 := hS.ne'
  have hK_ne : K ≠ 0 := hK.ne'
  have h_d1_σ := hasDerivAt_bsd1_sigma S K r hσ hτ
  have h_d2_σ := hasDerivAt_bsd2_sigma S K r hσ hτ
  have h_Phi_d1 := (hasDerivAt_Phi (bsd1 S K r σ τ)).comp σ h_d1_σ
  have h_Phi_d2 := (hasDerivAt_Phi (bsd2 S K r σ τ)).comp σ h_d2_σ
  -- d/dσ [S · Phi(d₁(σ))]
  have h_S_Phi_d1 := h_Phi_d1.const_mul S
  -- d/dσ [K · exp(-rτ) · Phi(d₂(σ))]
  have h_K_exp_Phi_d2 := h_Phi_d2.const_mul (K * Real.exp (-(r * τ)))
  have h_V := h_S_Phi_d1.sub h_K_exp_Phi_d2
  have h_fun_eq : (fun s : ℝ ↦
      S * (Phi ∘ fun s' ↦ bsd1 S K r s' τ) s -
        K * Real.exp (-(r * τ)) * (Phi ∘ fun s' ↦ bsd2 S K r s' τ) s)
        = (fun s : ℝ ↦ bsV K r s S τ) := by funext s; rfl
  rw [← h_fun_eq]
  convert h_V using 1
  have h_bs := bs_identity (r := r) hS hK hσ hτ
  have h_sq_sqrt : Real.sqrt τ ^ 2 = τ := Real.sq_sqrt hτ.le
  field_simp
  simp only [show (τ * r : ℝ) = r * τ from mul_comm τ r, h_sq_sqrt]
  rw [h_bs]
  ring

/-- **Rho**: `∂_r V = K · τ · e^{-rτ} · Φ(d₂)`.

Again the magic identity collapses the `∂_r d₁`, `∂_r d₂` chain-rule contributions,
because `∂_r d₁ = ∂_r d₂ = √τ/σ` (the difference `d₁ − d₂` is `r`-independent).
The remaining surviving term comes from `∂_r [exp(-rτ)] = −τ · exp(-rτ)`. -/
lemma hasDerivAt_bsV_r {K σ τ : ℝ} (hK : 0 < K) (hσ : 0 < σ) (hτ : 0 < τ)
    {S : ℝ} (hS : 0 < S) (r : ℝ) :
    HasDerivAt (fun r' ↦ bsV K r' σ S τ)
      (K * τ * Real.exp (-(r * τ)) * Phi (bsd2 S K r σ τ)) r := by
  have h_sqrt_pos : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have h_sqrt_ne : Real.sqrt τ ≠ 0 := h_sqrt_pos.ne'
  have hσ_ne : σ ≠ 0 := hσ.ne'
  have hτ_ne : τ ≠ 0 := hτ.ne'
  have hS_ne : S ≠ 0 := hS.ne'
  have hK_ne : K ≠ 0 := hK.ne'
  have h_d1_r := hasDerivAt_bsd1_r S K σ τ hσ hτ r
  have h_d2_r := hasDerivAt_bsd2_r S K σ τ hσ hτ r
  have h_Phi_d1 := (hasDerivAt_Phi (bsd1 S K r σ τ)).comp r h_d1_r
  have h_Phi_d2 := (hasDerivAt_Phi (bsd2 S K r σ τ)).comp r h_d2_r
  -- d/dr [S · Phi(d₁(r))]
  have h_S_Phi_d1 := h_Phi_d1.const_mul S
  -- d/dr [exp(-rτ)] = -τ · exp(-rτ)
  have h_neg_r : HasDerivAt (fun r' : ℝ ↦ -(r' * τ)) (-τ) r := by
    have h_lin : HasDerivAt (fun r' : ℝ ↦ r' * τ) τ r := by
      have := (hasDerivAt_id r).mul_const τ; simpa using this
    exact h_lin.neg
  have h_exp : HasDerivAt (fun r' : ℝ ↦ Real.exp (-(r' * τ)))
      (Real.exp (-(r * τ)) * -τ) r := h_neg_r.exp
  -- d/dr [K · exp(-rτ)] = K · -τ · exp(-rτ)
  have h_K_exp : HasDerivAt (fun r' : ℝ ↦ K * Real.exp (-(r' * τ)))
      (K * (Real.exp (-(r * τ)) * -τ)) r := h_exp.const_mul K
  -- d/dr [K · exp(-rτ) · Phi(d₂(r))]
  have h_K_exp_Phi_d2 := h_K_exp.mul h_Phi_d2
  have h_V := h_S_Phi_d1.sub h_K_exp_Phi_d2
  have h_fun_eq : (fun r' : ℝ ↦
      S * (Phi ∘ fun r'' ↦ bsd1 S K r'' σ τ) r' -
        (fun r'' ↦ K * Real.exp (-(r'' * τ)) * (Phi ∘ fun r''' ↦ bsd2 S K r''' σ τ) r'') r')
        = (fun r' : ℝ ↦ bsV K r' σ S τ) := by funext r'; rfl
  rw [← h_fun_eq]
  convert h_V using 1
  have h_bs := bs_identity (r := r) hS hK hσ hτ
  simp only [Function.comp_apply]
  field_simp
  simp only [show (τ * r : ℝ) = r * τ from mul_comm τ r]
  rw [h_bs]
  ring

/-- **Black–Scholes PDE** (forward direction): the European call price
`V(S, t) = S · Φ(d₁) − K · e^{-r(T−t)} · Φ(d₂)` satisfies
`∂_t V + (1/2) σ² S² ∂²_S V + r S ∂_S V − r V = 0` for `0 < S, t < T, 0 < K, 0 < σ`. -/
theorem bs_pde_holds {K T r σ : ℝ} (hσ : 0 < σ)
    {S t : ℝ} (hS : 0 < S) (ht_T : t < T) :
    -(σ * S * gaussianPDFReal 0 1 (bsd1 S K r σ (T - t)) / (2 * Real.sqrt (T - t))
      + r * K * Real.exp (-(r * (T - t))) * Phi (bsd2 S K r σ (T - t))) +
    (1 / 2 : ℝ) * σ ^ 2 * S ^ 2 *
      (gaussianPDFReal 0 1 (bsd1 S K r σ (T - t)) / (S * σ * Real.sqrt (T - t))) +
    r * S * Phi (bsd1 S K r σ (T - t)) -
    r * bsV K r σ S (T - t) = 0 := by
  have hτ : 0 < T - t := sub_pos.mpr ht_T
  have h_sqrt_pos : 0 < Real.sqrt (T - t) := Real.sqrt_pos.mpr hτ
  have hS_ne : S ≠ 0 := hS.ne'
  have hσ_ne : σ ≠ 0 := hσ.ne'
  have h_sqrt_ne : Real.sqrt (T - t) ≠ 0 := h_sqrt_pos.ne'
  rw [bsV]
  field_simp
  ring

end MathFin
