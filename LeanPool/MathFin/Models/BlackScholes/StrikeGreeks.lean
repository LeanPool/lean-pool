/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.BlackScholes.PutGreeks
public import LeanPool.MathFin.Models.BlackScholes.DigitalGreeks

/-!
# Black-Scholes strike derivatives

Standard derivative-Greek identities in the strike direction:

* `∂_K bsV = -e^{-rτ} · Φ(d₂)`; its sign, `≤ 0`, is `bsV_partial_K_nonpos`.
* `∂_K bsP = e^{-rτ} · Φ(-d₂)`, via put-call parity `bsP = bsV - S + K · e^{-rτ}`.
* `∂²_K bsV = e^{-rτ} · ϕ(d₂) / (K σ √τ)`; its sign, `≥ 0`, is `bsV_partial_KK_nonneg`. The
  convexity of the price in `K` (`StrikeConvexity.bsV_strike_convexOn`) is proved from the
  payoff, not from this sign, and gives the sign back
  (`lognormalTerminalPDF_nonneg_via_strike_convexity`).

The clean closed forms come from the magic identity
`S · ϕ(d₁) = K · e^{-rτ} · ϕ(d₂)` (`bs_identity`) which collapses the
`d₁`-derivative contribution.

## Main results

* `hasDerivAt_bsd1_K`, `hasDerivAt_bsd2_K`: `∂_K d_i = −1/(K σ √τ)`.
* `hasDerivAt_bsV_K`: `∂_K bsV = −e^{-rτ} · Φ(d₂)`.
* `hasDerivAt_bsP_K`: `∂_K bsP = e^{-rτ} · Φ(-d₂)`.
* `hasDerivAt_bsCashDigital_K`: the strike derivative of the cash-or-nothing digital
  `bsCashDigital = e^{-rτ} · Φ(d₂)` is `−e^{-rτ} · ϕ(d₂) / (K σ √τ)`.
* `hasDerivAt_deriv_bsV_K`: `∂²_K bsV = e^{-rτ} · ϕ(d₂) / (K σ √τ)`, for the price itself: the
  first strike derivative is minus the digital.

## References

* [F. Black and M. Scholes, *The pricing of options and corporate liabilities*][BlackScholes1973]
* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], 26.1; Ch 12.8; Ch 17

## Tags

strike derivative, dual delta, implied density, digital option, Breeden–Litzenberger, MSC 91G20,
JEL G13
-/

@[expose] public section

namespace MathFin

open Real ProbabilityTheory

/-- `∂_K d₁(S, K, r, σ, τ) = −1 / (K · σ · √τ)`. Mirror of `hasDerivAt_bsd1_S`. -/
lemma hasDerivAt_bsd1_K (S r σ τ : ℝ) (hS : 0 < S) (hσ : 0 < σ) (hτ : 0 < τ)
    {K : ℝ} (hK : 0 < K) :
    HasDerivAt (fun k ↦ bsd1 S k r σ τ) (-(1 / (K * σ * Real.sqrt τ))) K := by
  have h_sqrt_τ_pos : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have h_sqrt_τ_ne : Real.sqrt τ ≠ 0 := h_sqrt_τ_pos.ne'
  have hσ_ne : σ ≠ 0 := hσ.ne'
  have hK_ne : K ≠ 0 := hK.ne'
  -- k ↦ log k has derivative 1/K at K.
  have h_log : HasDerivAt Real.log (1 / K) K := by
    rw [one_div]; exact Real.hasDerivAt_log hK_ne
  -- k ↦ log S - log k has derivative -(1/K) at K.
  have h_minus_log : HasDerivAt
      (fun k : ℝ ↦ Real.log S - Real.log k) (-(1 / K)) K := by
    have h_neg := h_log.neg
    have h_add := h_neg.const_add (Real.log S)
    have : (fun k : ℝ ↦ Real.log S - Real.log k) = fun x ↦ Real.log S + (-Real.log) x := by
      funext x; simp [sub_eq_add_neg]
    rw [this]; exact h_add
  -- log(S/k) =ᶠ[𝓝 K] log S - log k (since K ≠ 0 in a nbhd).
  have h_eventually : (fun k : ℝ ↦ Real.log (S / k)) =ᶠ[nhds K]
                       (fun k ↦ Real.log S - Real.log k) := by
    filter_upwards [eventually_ne_nhds hK_ne] with k hk
    exact Real.log_div hS.ne' hk
  have h_log_div : HasDerivAt (fun k : ℝ ↦ Real.log (S / k)) (-(1 / K)) K :=
    h_minus_log.congr_of_eventuallyEq h_eventually
  -- Add the constant `(r + σ²/2)τ`.
  have h_num : HasDerivAt
      (fun k : ℝ ↦ Real.log (S / k) + (r + σ ^ 2 / 2) * τ) (-(1 / K)) K := by
    simpa using h_log_div.add_const ((r + σ ^ 2 / 2) * τ)
  -- Divide by σ√τ.
  have h_div_στ : HasDerivAt
      (fun k : ℝ ↦ (Real.log (S / k) + (r + σ ^ 2 / 2) * τ) / (σ * Real.sqrt τ))
      (-(1 / K) / (σ * Real.sqrt τ)) K :=
    h_num.div_const (σ * Real.sqrt τ)
  have h_val_eq :
      -(1 / K) / (σ * Real.sqrt τ) = -(1 / (K * σ * Real.sqrt τ)) := by
    field_simp
  rw [h_val_eq] at h_div_στ
  exact h_div_στ

/-- `∂_K d₂(S, K, r, σ, τ) = −1 / (K · σ · √τ)` (same as `∂_K d_1` since `d_2 − d_1`
is `K`-independent). -/
lemma hasDerivAt_bsd2_K (S r σ τ : ℝ) (hS : 0 < S) (hσ : 0 < σ) (hτ : 0 < τ)
    {K : ℝ} (hK : 0 < K) :
    HasDerivAt (fun k ↦ bsd2 S k r σ τ) (-(1 / (K * σ * Real.sqrt τ))) K := by
  have h_diff := (hasDerivAt_bsd1_K S r σ τ hS hσ hτ hK).sub_const (σ * Real.sqrt τ)
  have h_fun_eq : (fun k : ℝ ↦ bsd1 S k r σ τ - σ * Real.sqrt τ)
        = (fun k : ℝ ↦ bsd2 S k r σ τ) := by
    funext k; rw [bsd2]
  rw [← h_fun_eq]
  exact h_diff

/-- **Strike-derivative of the call price**: `∂_K bsV = −e^{-rτ} · Φ(d₂)`.
The magic identity `S · ϕ(d₁) = K · e^{-rτ} · ϕ(d₂)` collapses the `d_1`
contribution. -/
lemma hasDerivAt_bsV_K {S r σ : ℝ} (hS : 0 < S) (hσ : 0 < σ)
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 < τ) :
    HasDerivAt (fun k ↦ bsV k r σ S τ)
      (-(Real.exp (-(r * τ)) * Phi (bsd2 S K r σ τ))) K := by
  have h_sqrt_τ_pos : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have h_sqrt_τ_ne : Real.sqrt τ ≠ 0 := h_sqrt_τ_pos.ne'
  have hσ_ne : σ ≠ 0 := hσ.ne'
  have hK_ne : K ≠ 0 := hK.ne'
  have hS_ne : S ≠ 0 := hS.ne'
  -- Pieces
  have h_d1_K := hasDerivAt_bsd1_K S r σ τ hS hσ hτ hK
  have h_d2_K := hasDerivAt_bsd2_K S r σ τ hS hσ hτ hK
  have h_Phi_d1 := (hasDerivAt_Phi (bsd1 S K r σ τ)).comp K h_d1_K
  have h_Phi_d2 := (hasDerivAt_Phi (bsd2 S K r σ τ)).comp K h_d2_K
  -- d/dK [S · Phi(d_1(K))] = S · ϕ(d_1) · ∂_K d_1
  have h_S_Phi_d1 := h_Phi_d1.const_mul S
  -- d/dK [K · exp(-rτ) · Phi(d_2(K))] = exp(-rτ)·Phi(d_2) + K·exp(-rτ)·ϕ(d_2)·∂_K d_2
  have h_id : HasDerivAt (fun k : ℝ ↦ k) 1 K := hasDerivAt_id K
  have h_K_Phi_d2 := h_id.mul h_Phi_d2
  have h_K_exp_Phi_d2 := h_K_Phi_d2.const_mul (Real.exp (-(r * τ)))
  have h_V := h_S_Phi_d1.sub h_K_exp_Phi_d2
  have h_fun_eq : (fun k : ℝ ↦
        S * Phi (bsd1 S k r σ τ) -
        Real.exp (-(r * τ)) * (k * Phi (bsd2 S k r σ τ))) =
      (fun k : ℝ ↦ bsV k r σ S τ) := by
    funext k
    show S * Phi (bsd1 S k r σ τ) -
          Real.exp (-(r * τ)) * (k * Phi (bsd2 S k r σ τ)) =
        bsV k r σ S τ
    unfold bsV
    ring
  rw [← h_fun_eq]
  -- Value from h_V equals -(exp(-rτ)·Φ(d₂)) via magic identity
  have h_bs := bs_identity (r := r) hS hK hσ hτ
  have hKστ_ne : K * σ * Real.sqrt τ ≠ 0 := by positivity
  refine h_V.congr_deriv ?_
  -- Goal: S*(g1*(-(1/(Kστ)))) - exp*(1*Φ2 + K*(g2*(-(1/(Kστ))))) = -(exp*Φ2)
  -- by h_bs: S*g1 = K*exp*g2, so the extra terms cancel
  simp only [Function.comp_apply]
  have hKστ_pos : (0 : ℝ) < K * σ * Real.sqrt τ := by positivity
  field_simp
  linarith [h_bs]

/-- **Strike-derivative of the put price**: `∂_K bsP = e^{-rτ} · Φ(-d₂)`. Follows
from put-call parity `bsP = bsV − S + K · e^{-rτ}`. -/
lemma hasDerivAt_bsP_K {S r σ : ℝ} (hS : 0 < S) (hσ : 0 < σ)
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 < τ) :
    HasDerivAt (fun k ↦ bsP k r σ S τ)
      (Real.exp (-(r * τ)) * Phi (-bsd2 S K r σ τ)) K := by
  have h_eq : (fun k : ℝ ↦ bsP k r σ S τ) =
        fun k ↦ bsV k r σ S τ - S + k * Real.exp (-(r * τ)) := by
    funext k; rw [bsP_eq_bsV k r σ S τ]
  rw [h_eq]
  have h_V := hasDerivAt_bsV_K (S := S) (r := r) (σ := σ) hS hσ hK hτ
  have h_const : HasDerivAt (fun _ : ℝ ↦ S) 0 K := hasDerivAt_const K S
  have h_lin : HasDerivAt (fun k : ℝ ↦ k * Real.exp (-(r * τ)))
      (Real.exp (-(r * τ))) K := by
    have := (hasDerivAt_id K).mul_const (Real.exp (-(r * τ)))
    simpa using this
  have h := (h_V.sub h_const).add h_lin
  -- Adapt h's function and value to match the goal
  have h_Phi := Phi_neg (bsd2 S K r σ τ)
  -- Step 1: fix the function (regrouped form), keeping the same value
  have h1 := h.congr_of_eventuallyEq (f₁ := fun k ↦ bsV k r σ S τ - S + k * Real.exp (-(r * τ)))
    (Filter.Eventually.of_forall fun k ↦ by simp only [Pi.add_apply, Pi.sub_apply])
  -- Step 2: fix the value: -(exp*Φ(d2)) - 0 + exp = exp*Φ(-d2)
  have hval : -(Real.exp (-(r * τ)) * Phi (bsd2 S K r σ τ)) - 0 + Real.exp (-(r * τ))
      = Real.exp (-(r * τ)) * Phi (-bsd2 S K r σ τ) := by
    have : Real.exp (-(r * τ)) * Phi (-bsd2 S K r σ τ) =
        Real.exp (-(r * τ)) * (1 - Phi (bsd2 S K r σ τ)) := by rw [h_Phi]
    linarith [mul_comm (Real.exp (-(r * τ))) (Phi (bsd2 S K r σ τ))]
  exact hval ▸ h1

/-- **Strike derivative of the cash-or-nothing digital**: `∂_K (e^{-rτ} Φ(d₂)) =
−e^{-rτ} · ϕ(d₂) / (K σ √τ)`, minus `e^{-rτ}` times the lognormal density formula
`lognormalTerminalPDF` at `K` (`BreedenLitzenberger.lean`). The digital is minus the strike
derivative of the call price (`hasDerivAt_bsV_K`), so this is minus the second strike derivative of
the call, and `≤ 0` by the convexity in `K` (`bsV_strike_convexOn`, proved from the payoff). -/
lemma hasDerivAt_bsCashDigital_K {S r σ : ℝ} (hS : 0 < S) (hσ : 0 < σ)
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 < τ) :
    HasDerivAt (fun k ↦ bsCashDigital k r σ S τ)
      (-(Real.exp (-(r * τ)) * gaussianPDFReal 0 1 (bsd2 S K r σ τ) /
        (K * σ * Real.sqrt τ))) K :=
  (((hasDerivAt_Phi (bsd2 S K r σ τ)).comp K (hasDerivAt_bsd2_K S r σ τ hS hσ hτ hK)).const_mul
    (Real.exp (-(r * τ)))).congr_deriv (by ring)

/-- **Second strike-derivative of the call**: `∂²C/∂K² = e^{-rτ} · ϕ(d₂) / (K σ √τ)`, for the
price itself: `∂_K bsV` is minus the digital on all of `K > 0` (`hasDerivAt_bsV_K`), and the
digital's strike derivative is `hasDerivAt_bsCashDigital_K`. -/
theorem hasDerivAt_deriv_bsV_K {S r σ : ℝ} (hS : 0 < S) (hσ : 0 < σ)
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 < τ) :
    HasDerivAt (deriv fun k ↦ bsV k r σ S τ)
      (Real.exp (-(r * τ)) * gaussianPDFReal 0 1 (bsd2 S K r σ τ) / (K * σ * Real.sqrt τ)) K :=
  hasDerivAt_deriv_of_eventually
    ((eventually_gt_nhds hK).mono fun _ hk ↦ hasDerivAt_bsV_K hS hσ hk hτ)
    ((hasDerivAt_bsCashDigital_K (r := r) hS hσ hK hτ).fun_neg.congr_deriv (neg_neg _))

end MathFin
