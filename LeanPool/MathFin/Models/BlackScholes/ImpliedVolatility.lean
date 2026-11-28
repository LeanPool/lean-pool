/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho, Yang Ye
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.BlackScholes.PutGreeks
public import LeanPool.MathFin.Probability.Gaussian.NormalTail
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Smooth.Flat

/-!
# Implied volatility: uniqueness, and existence above a reference volatility

The **implied volatility** of a market option price `c` is the value of `σ`
for which the Black–Scholes price equals `c`. Existence requires the option
price to lie in the no-arbitrage range; **uniqueness** follows from strict
monotonicity of the BS call price in `σ`.

Strict monotonicity in `σ` follows from **positive vega**: by
`hasDerivAt_bsV_sigma`, `∂_σ V = S · ϕ(d_1) · √τ`. For `S > 0, T > 0`, this
is strictly positive (since `ϕ > 0`). A function with positive derivative
on an interval is strictly monotone there, hence injective.

As `σ → ∞` the call price tends to the spot. So a price above the Black–Scholes
price at some `σ₀ > 0` and below the spot has an implied volatility, above `σ₀`.
This is the existence result `JumpImpliedVol.lean` needs. Existence for every
price in the no-arbitrage range would also need the `σ → 0` limit, which is not
proved.

## Main definitions

* `newtonStep`: the Newton–Raphson step `σ − f σ / f' σ`.

## Main results

* `bsV_strictMonoOn_sigma`: the BS call price `σ ↦ V(K, r, σ, S, T)` is
  strictly monotone on `(0, ∞)` for `K, S, T > 0`.
* `implied_volatility_unique`: as a corollary, the implied volatility is
  unique whenever it exists.
* `impliedVol_put_eq_call`: under put-call parity, put and call implied volatilities coincide.
* `tendsto_bsV_sigma_atTop`: the call price tends to the spot as `σ → ∞`.
* `exists_impliedVol_gt_of_bsV_lt`: a price strictly between the Black–Scholes
  price at `σ₀ > 0` and the spot has a unique positive implied volatility, and it
  exceeds `σ₀`.

## References

* [J. Gatheral, *The Volatility Surface: A Practitioner's Guide*][Gatheral2006]
* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], 19.10
* [S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*][ShreveSCFII], 4.5

## Tags

implied volatility, uniqueness of implied volatility, strict monotonicity in volatility,
Newton step, no-arbitrage price range, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open Filter MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal Topology

/-- **Vega is strictly positive** for `S > 0, T > 0` and any `σ > 0`. -/
lemma bsV_vega_pos {K r : ℝ} (_hK : 0 < K)
    {S σ T : ℝ} (hS : 0 < S) (_hσ : 0 < σ) (hT : 0 < T) :
    0 < S * gaussianPDFReal 0 1 (bsd1 S K r σ T) * Real.sqrt T := by
  have h_pdf_pos : 0 < gaussianPDFReal 0 1 (bsd1 S K r σ T) :=
    gaussianPDFReal_pos 0 1 _ (one_ne_zero : (1 : ℝ≥0) ≠ 0)
  positivity

/-- **The BS call price is continuous in `σ`** on `(0, ∞)`: it is differentiable
there (`hasDerivAt_bsV_sigma`). -/
theorem bsV_continuousOn_sigma {K r T : ℝ} (hK : 0 < K) (hT : 0 < T)
    {S : ℝ} (hS : 0 < S) :
    ContinuousOn (fun σ ↦ bsV K r σ S T) (Set.Ioi 0) := fun _ hσ ↦
  (hasDerivAt_bsV_sigma hK hS hσ hT).continuousAt.continuousWithinAt

/-- **The BS call price is strictly monotone in `σ`** on `(0, ∞)`.

A direct consequence of positive vega (`hasDerivAt_bsV_sigma` + `bsV_vega_pos`)
and the mean-value theorem (`strictMonoOn_of_deriv_pos`). -/
theorem bsV_strictMonoOn_sigma {K r T : ℝ} (hK : 0 < K) (hT : 0 < T)
    {S : ℝ} (hS : 0 < S) :
    StrictMonoOn (fun σ ↦ bsV K r σ S T) (Set.Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0) (bsV_continuousOn_sigma hK hT hS)
  · intro σ hσ_int
    rw [interior_Ioi] at hσ_int
    have hσ_pos : 0 < σ := hσ_int
    have h_deriv := hasDerivAt_bsV_sigma (r := r) hK hS hσ_pos hT
    rw [h_deriv.deriv]
    exact bsV_vega_pos hK hS hσ_pos hT

/-- **Uniqueness of implied volatility.** If two volatilities `σ₁, σ₂ ∈ (0, ∞)`
give the same BS call price, then `σ₁ = σ₂`. Direct consequence of strict
monotonicity. -/
theorem implied_volatility_unique {K r T : ℝ} (hK : 0 < K) (hT : 0 < T)
    {S : ℝ} (hS : 0 < S) {σ₁ σ₂ : ℝ} (hσ₁ : 0 < σ₁) (hσ₂ : 0 < σ₂)
    (h_eq : bsV K r σ₁ S T = bsV K r σ₂ S T) :
    σ₁ = σ₂ := by
  exact (bsV_strictMonoOn_sigma hK hT hS).injOn hσ₁ hσ₂ h_eq

/-- **Put and call implied volatilities coincide** (Hull §20.1). If market prices `C` and `P`
satisfy put-call parity `C − P = S − K e^{−rT}`, the call is priced by Black–Scholes at `σ_c`
and the put at `σ_p`, then `σ_c = σ_p`: by `bsP_eq_bsV` the put price at `σ_p` determines the
call price at `σ_p`, which must be `C`, and implied volatility is unique. -/
theorem impliedVol_put_eq_call {K r T : ℝ} (hK : 0 < K) (hT : 0 < T)
    {S C P σc σp : ℝ} (hS : 0 < S) (hσc : 0 < σc) (hσp : 0 < σp)
    (h_parity : C - P = S - K * Real.exp (-(r * T)))
    (hC : bsV K r σc S T = C) (hP : bsP K r σp S T = P) :
    σc = σp := by
  refine implied_volatility_unique (r := r) hK hT hS hσc hσp ?_
  rw [bsP_eq_bsV] at hP
  linarith

/-! ## Existence above a reference volatility

As `σ → ∞`, `d₁ = (log(S/K) + rT)/(σ√T) + σ√T/2 → ∞` and `d₂ = d₁ − σ√T → −∞`, so the call
price tends to the spot. A price strictly between the Black–Scholes price at some `σ₀ > 0` and
the spot is therefore attained at a volatility above `σ₀` (intermediate value theorem), and at no
other positive volatility (`implied_volatility_unique`). -/

/-- `d₁` with the volatility split out, at the maturity `s²`, where `√(s²) = s`. -/
lemma bsd1_sq_eq (S K r : ℝ) {σ s : ℝ} (hσ : σ ≠ 0) (hs : 0 < s) :
    bsd1 S K r σ (s ^ 2) = (Real.log (S / K) + r * s ^ 2) / s * σ⁻¹ + s / 2 * σ := by
  have hs' : s ≠ 0 := hs.ne'
  rw [bsd1, Real.sqrt_sq hs.le]
  generalize Real.log (S / K) = L
  field_simp
  ring

/-- `d₁ = (log(S/K) + rT)/√T · σ⁻¹ + √T/2 · σ`. -/
lemma bsd1_eq_inv_add (S K r : ℝ) {σ T : ℝ} (hσ : σ ≠ 0) (hT : 0 < T) :
    bsd1 S K r σ T = (Real.log (S / K) + r * T) / Real.sqrt T * σ⁻¹ + Real.sqrt T / 2 * σ := by
  have h := bsd1_sq_eq S K r hσ (Real.sqrt_pos.2 hT)
  rwa [Real.sq_sqrt hT.le] at h

/-- `d₁ → ∞` as `σ → ∞`. -/
lemma tendsto_bsd1_sigma_atTop (S K r : ℝ) {T : ℝ} (hT : 0 < T) :
    Tendsto (fun σ ↦ bsd1 S K r σ T) atTop atTop := by
  have h : Tendsto (fun σ : ℝ ↦ (Real.log (S / K) + r * T) / Real.sqrt T * σ⁻¹
      + Real.sqrt T / 2 * σ) atTop atTop :=
    (tendsto_inv_atTop_zero.const_mul _).add_atTop
      (tendsto_id.const_mul_atTop (half_pos (Real.sqrt_pos.2 hT)))
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with σ hσ
  exact (bsd1_eq_inv_add S K r hσ.ne' hT).symm

/-- `d₂ → −∞` as `σ → ∞`. -/
lemma tendsto_bsd2_sigma_atTop (S K r : ℝ) {T : ℝ} (hT : 0 < T) :
    Tendsto (fun σ ↦ bsd2 S K r σ T) atTop atBot := by
  have h : Tendsto (fun σ : ℝ ↦ (Real.log (S / K) + r * T) / Real.sqrt T * σ⁻¹
      + -(Real.sqrt T / 2 * σ)) atTop atBot :=
    (tendsto_inv_atTop_zero.const_mul _).add_atBot (tendsto_neg_atTop_atBot.comp
      (tendsto_id.const_mul_atTop (half_pos (Real.sqrt_pos.2 hT))))
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with σ hσ
  rw [bsd2, bsd1_eq_inv_add S K r hσ.ne' hT]
  ring

/-- **The Black–Scholes call tends to the spot as `σ → ∞`**: `S·Φ(d₁) − Ke^{−rT}·Φ(d₂) → S`,
since `d₁ → ∞` and `d₂ → −∞`. -/
theorem tendsto_bsV_sigma_atTop (S K r : ℝ) {T : ℝ} (hT : 0 < T) :
    Tendsto (fun σ ↦ bsV K r σ S T) atTop (𝓝 S) := by
  have h := ((tendsto_Phi_atTop.comp (tendsto_bsd1_sigma_atTop S K r hT)).const_mul S).sub
    ((tendsto_Phi_atBot.comp (tendsto_bsd2_sigma_atTop S K r hT)).const_mul
      (K * Real.exp (-(r * T))))
  rw [mul_one, mul_zero, sub_zero] at h
  exact h

/-- **Implied volatility above a reference volatility.** A price `C` strictly between the
Black–Scholes price at a volatility `σ₀ > 0` and the spot has an implied volatility `σ > σ₀`,
and no other positive volatility prices to `C`. -/
theorem exists_impliedVol_gt_of_bsV_lt {K r T S σ₀ C : ℝ} (hK : 0 < K) (hT : 0 < T)
    (hS : 0 < S) (hσ₀ : 0 < σ₀) (hlo : bsV K r σ₀ S T < C) (hhi : C < S) :
    ∃ σ, σ₀ < σ ∧ bsV K r σ S T = C ∧ ∀ σ' > 0, bsV K r σ' S T = C → σ' = σ := by
  obtain ⟨σ₁, hC, hσ₁⟩ := (((tendsto_bsV_sigma_atTop S K r hT).eventually
    (lt_mem_nhds hhi)).and (eventually_gt_atTop σ₀)).exists
  have hpos : Set.Icc σ₀ σ₁ ⊆ Set.Ioi 0 := fun v hv ↦ hσ₀.trans_le hv.1
  have hCmem : C ∈ Set.Ioo (bsV K r σ₀ S T) (bsV K r σ₁ S T) := ⟨hlo, hC⟩
  obtain ⟨σ, hσ, hσC⟩ := intermediate_value_Ioo hσ₁.le
    ((bsV_continuousOn_sigma (r := r) hK hT hS).mono hpos) hCmem
  exact ⟨σ, hσ.1, hσC, fun σ' hσ' h ↦
    implied_volatility_unique hK hT hS hσ' (hσ₀.trans hσ.1) (h.trans hσC.symm)⟩

/-! ## Newton-Raphson iteration (folded from `NewtonRaphsonIV.lean`)

The Newton iteration `σ_{n+1} = σ_n − f(σ_n)/f'(σ_n)` for root-finding. In
the BS implied-vol setting, `f(σ) = bsV(σ) − C_obs` and `f'(σ) = vega(σ) > 0`
(positive by `bsV_vega_pos`), so the iteration is well-defined for `σ > 0`.

Quadratic convergence requires bounding the residual via Taylor with
remainder; we record only the fixed-point-at-root and error-decomposition
identities. -/

/-- **Newton-Raphson iteration step**: `σ_{n+1} = σ_n − f(σ_n) / f'(σ_n)`. -/
noncomputable def newtonStep (f f' : ℝ → ℝ) (σ : ℝ) : ℝ := σ - f σ / f' σ

/-- **A root is a fixed point of the Newton iteration**. -/
theorem newtonStep_fixed_at_root (f f' : ℝ → ℝ) {σ : ℝ} (h_root : f σ = 0) :
    newtonStep f f' σ = σ := by
  unfold newtonStep
  rw [h_root, zero_div, sub_zero]

/-- **Error decomposition for one Newton step** when `σ_*` is a root of `f`. -/
theorem newtonStep_error_via_root
    (f f' : ℝ → ℝ) {σ_star σ : ℝ} (_h_root : f σ_star = 0) :
    newtonStep f f' σ - σ_star = (σ - σ_star) - f σ / f' σ := by
  unfold newtonStep
  ring

end MathFin
