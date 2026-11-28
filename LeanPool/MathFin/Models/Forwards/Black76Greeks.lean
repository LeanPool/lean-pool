/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.BlackScholes.PDE
public import LeanPool.MathFin.Models.BlackScholes.HigherGreeks

/-!
# Black-76 Greeks

For the Black-76 futures call price `V_B(F, σ, T) = e^{-rT} · [F Φ(d₁) − K Φ(d₂)]`
with `d_i = bsdi F K 0 σ T` (i.e., zero drift), the Greeks are simply the BS
Greeks evaluated at `r = 0` and post-multiplied by the discount factor `e^{-rT}`:

* `hasDerivAt_blackV_F` — δ = e^{-rT} · Φ(d₁).
* `hasDerivAt_deriv_blackV_F` — γ = e^{-rT} · ϕ(d₁) / (F σ √T), from the
  formula-level `hasDerivAt_blackV_FF`.
* `hasDerivAt_deriv_deriv_blackV_F` — speed = e^{-rT} · (-ϕ(d₁) (d₁ + σ√T) / (F² σ² T)).
* `hasDerivAt_blackV_sigma` — vega = e^{-rT} · F · ϕ(d₁) · √T.

## Main definitions

* `blackV`: the Black-76 futures call price `e^{−rT}·bsV(K, 0, σ, F, T)` as a function of
  `(F, σ, T)` and the discount rate `r`.

## Main results

* `hasDerivAt_blackV_F`: delta, `∂_F V_B = e^{−rT} Φ(d₁)`.
* `hasDerivAt_deriv_blackV_F`: gamma, `∂²_F V_B = e^{−rT} ϕ(d₁) / (F σ √T)`.
* `hasDerivAt_deriv_deriv_blackV_F`: speed, the third `F`-derivative of `V_B`.
* `hasDerivAt_blackV_sigma`: vega, `∂_σ V_B = e^{−rT} F ϕ(d₁) √T`.
* `hasDerivAt_blackV_r`: rho, `∂_r V_B = −T · V_B`.
* `hasDerivAt_blackV_T`: the `T`-derivative of `V_B`, `−r V_B + e^{−rT} σ F ϕ(d₁) / (2√T)`.

These hold for `K, σ, F, T > 0` (rho for all reals).

## References

* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], 17.6

## Tags

Black-76 model, futures option, delta, gamma, vega, speed, option sensitivities, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real

/-- Black-76 futures call price as a function of `(F, σ, T)` plus discount rate `r`.
Specialization of `bsV` to zero drift, times an external discount `e^{-rT}`. -/
noncomputable def blackV (K σ : ℝ) (r F T : ℝ) : ℝ :=
  Real.exp (-(r * T)) * bsV K 0 σ F T

/-- **Black-76 delta**: `∂_F V_B = e^{-rT} · Φ(d₁)`. -/
lemma hasDerivAt_blackV_F {K σ : ℝ} (hK : 0 < K) (hσ : 0 < σ) (r : ℝ)
    {F T : ℝ} (hF : 0 < F) (hT : 0 < T) :
    HasDerivAt (fun f ↦ blackV K σ r f T) (Real.exp (-(r * T)) * Phi (bsd1 F K 0 σ T)) F :=
  (hasDerivAt_bsV_S (r := 0) hK hσ hF hT).const_mul (Real.exp (-(r * T)))

/-- **The Black-76 gamma formula**: the F-derivative of the delta `e^{-rT} · Φ(d₁)` is
`e^{-rT} · ϕ(d₁) / (F σ √T)`. The second derivative of the price itself is
`hasDerivAt_deriv_blackV_F`. -/
private lemma hasDerivAt_blackV_FF {K σ : ℝ} (hK : 0 < K) (hσ : 0 < σ) (r : ℝ)
    {F T : ℝ} (hF : 0 < F) (hT : 0 < T) :
    HasDerivAt (fun f ↦ Real.exp (-(r * T)) * Phi (bsd1 f K 0 σ T))
      (Real.exp (-(r * T)) * gaussianPDFReal 0 1 (bsd1 F K 0 σ T) / (F * σ * Real.sqrt T)) F := by
  have h_bs := hasDerivAt_Phi_bsd1_S (r := 0) hK hσ hF hT
  have h := h_bs.const_mul (Real.exp (-(r * T)))
  convert h using 1
  ring

/-- **Black-76 gamma**: `∂²V_B/∂F² = e^{-rT} · ϕ(d₁) / (F σ √T)`, for the price itself: the
delta `e^{-rT} · Φ(d₁)` is `∂V_B/∂F` on all of `F > 0` (`hasDerivAt_blackV_F`), and its
derivative is the gamma formula (`hasDerivAt_blackV_FF`). -/
theorem hasDerivAt_deriv_blackV_F {K σ : ℝ} (hK : 0 < K) (hσ : 0 < σ) (r : ℝ)
    {F T : ℝ} (hF : 0 < F) (hT : 0 < T) :
    HasDerivAt (deriv fun f ↦ blackV K σ r f T)
      (Real.exp (-(r * T)) * gaussianPDFReal 0 1 (bsd1 F K 0 σ T) / (F * σ * Real.sqrt T)) F :=
  hasDerivAt_deriv_of_eventually
    ((eventually_gt_nhds hF).mono fun _ hf ↦ hasDerivAt_blackV_F hK hσ r hf hT)
    (hasDerivAt_blackV_FF hK hσ r hF hT)

/-- **The Black-76 speed formula**: the F-derivative of the gamma formula is
`e^{-rT} · (-ϕ(d₁) (d₁ + σ√T) / (F² σ² T))`. The third derivative of the price itself is
`hasDerivAt_deriv_deriv_blackV_F`.

Same shape as the other Black-76 Greeks: the discount factor does not depend on
`F`, so it rides through the differentiation as a constant multiplier on the
zero-drift BS speed. -/
private lemma hasDerivAt_blackV_FFF {K σ : ℝ} (hK : 0 < K) (hσ : 0 < σ) (r : ℝ)
    {F T : ℝ} (hF : 0 < F) (hT : 0 < T) :
    HasDerivAt (fun f ↦ Real.exp (-(r * T)) *
        (gaussianPDFReal 0 1 (bsd1 f K 0 σ T) / (f * σ * Real.sqrt T)))
      (Real.exp (-(r * T)) * -(gaussianPDFReal 0 1 (bsd1 F K 0 σ T) *
        (bsd1 F K 0 σ T + σ * Real.sqrt T) / (F ^ 2 * σ ^ 2 * T))) F :=
  (hasDerivAt_bsV_SSS (r := 0) hK hσ hF hT).const_mul (Real.exp (-(r * T)))

/-- **Black-76 speed**: `∂³V_B/∂F³ = e^{-rT} · (-ϕ(d₁) (d₁ + σ√T) / (F² σ² T))`, for the
price itself: the genuine gamma `hasDerivAt_deriv_blackV_F` holds on all of `F > 0`, and the
derivative of its formula is `hasDerivAt_blackV_FFF`. -/
theorem hasDerivAt_deriv_deriv_blackV_F {K σ : ℝ} (hK : 0 < K) (hσ : 0 < σ) (r : ℝ)
    {F T : ℝ} (hF : 0 < F) (hT : 0 < T) :
    HasDerivAt (deriv (deriv fun f ↦ blackV K σ r f T))
      (Real.exp (-(r * T)) * -(gaussianPDFReal 0 1 (bsd1 F K 0 σ T) *
        (bsd1 F K 0 σ T + σ * Real.sqrt T) / (F ^ 2 * σ ^ 2 * T))) F :=
  hasDerivAt_deriv_of_eventually
    ((eventually_gt_nhds hF).mono fun _ hf ↦
      (hasDerivAt_deriv_blackV_F hK hσ r hf hT).congr_deriv (mul_div_assoc _ _ _))
    (hasDerivAt_blackV_FFF hK hσ r hF hT)

/-- **Black-76 vega**: `∂_σ V_B = e^{-rT} · F · ϕ(d₁) · √T`. -/
lemma hasDerivAt_blackV_sigma {K : ℝ} (hK : 0 < K) (r : ℝ)
    {F σ T : ℝ} (hF : 0 < F) (hσ : 0 < σ) (hT : 0 < T) :
    HasDerivAt (fun s ↦ blackV K s r F T)
      (Real.exp (-(r * T)) * F * gaussianPDFReal 0 1 (bsd1 F K 0 σ T) * Real.sqrt T) σ := by
  have h_bs := hasDerivAt_bsV_sigma (r := 0) hK hF hσ hT
  have h := h_bs.const_mul (Real.exp (-(r * T)))
  convert h using 1 <;> try rfl
  ring

/-- **Black-76 rho**: `∂_r V_B = -T · V_B`.

`V_B = e^{-rT} · bsV(K, 0, σ, F, T)`; the inner bsV is `r`-independent (zero-drift
futures setup), so only the discount factor contributes. Clean closed form. -/
lemma hasDerivAt_blackV_r (K σ F T : ℝ) (r : ℝ) :
    HasDerivAt (fun r' ↦ blackV K σ r' F T)
      (-T * blackV K σ r F T) r := by
  have h_neg : HasDerivAt (fun r' : ℝ ↦ -(r' * T)) (-T) r := by
    have h := (hasDerivAt_id r).mul_const T
    convert h.neg using 1 <;> first | rfl | ring
  have h_exp : HasDerivAt (fun r' : ℝ ↦ Real.exp (-(r' * T)))
      (Real.exp (-(r * T)) * (-T)) r := h_neg.exp
  have h := h_exp.mul_const (bsV K 0 σ F T)
  unfold blackV
  convert h using 1
  ring

/-- **Black-76 theta** (`∂_T` form): `∂_T V_B = -r · V_B + e^{-rT} · σ · F · ϕ(d₁) / (2√T)`.

Product rule on `V_B = e^{-rT} · bsV(K, 0, σ, F, T)`:
* `∂_T e^{-rT} = -r · e^{-rT}`
* `∂_T bsV(K, 0, σ, F, T) = σ · F · ϕ(d₁) / (2√T)` from `hasDerivAt_bsV_tau` at `r = 0`. -/
lemma hasDerivAt_blackV_T {K σ : ℝ} (hK : 0 < K) (hσ : 0 < σ) (r : ℝ)
    {F T : ℝ} (hF : 0 < F) (hT : 0 < T) :
    HasDerivAt (fun t ↦ blackV K σ r F t)
      (-r * blackV K σ r F T +
        Real.exp (-(r * T)) *
          (σ * F * gaussianPDFReal 0 1 (bsd1 F K 0 σ T) / (2 * Real.sqrt T))) T := by
  have h_neg : HasDerivAt (fun t : ℝ ↦ -(r * t)) (-r) T := by
    have h := (hasDerivAt_id T).const_mul r
    convert h.neg using 1 <;> first | rfl | ring
  have h_exp : HasDerivAt (fun t : ℝ ↦ Real.exp (-(r * t)))
      (Real.exp (-(r * T)) * (-r)) T := h_neg.exp
  have h_bsV := hasDerivAt_bsV_tau (r := 0) hK hσ hF hT
  have h := h_exp.mul h_bsV
  unfold blackV
  convert h using 1
  simp
  ring

end MathFin
