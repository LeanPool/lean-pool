/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.BlackScholes.GaussianSmoothing
public import LeanPool.MathFin.Models.Jumps.JumpDiffusionOptionPrices
public import LeanPool.MathFin.Models.Jumps.MertonJumpDiffusion

/-!
# Merton's formula from the general jump-diffusion

Merton (1976) priced the call of a jump-diffusion with lognormal jumps as a Poisson series of
Black–Scholes prices (`mertonCallPrice`): given `n` jumps the log-return is Gaussian, so the call
is the Black–Scholes call at the jump-adjusted spot `S₀e^{−kΛ}(1 + k)ⁿ` and the volatility
`√(σ² + nδ²/T)`. This file derives it from the general jump-diffusion (`JumpDiffusionHyp`). With
log-jumps `N(log(1 + k) − δ²/2, δ²)`, whose multipliers `e^{Jᵢ}` have mean `1 + k`, Merton's
formula for a general jump law
(`JumpDiffusionHyp.call_poisson_mixture`) averages the Black–Scholes price over the sum of `n`
log-jumps, which is `N(n(log(1 + k) − δ²/2), nδ²)`. Gaussian smoothing
(`integral_bsV_mul_exp_gaussianReal_of_sq`) turns each average into the `n`-th term of the
series.

The same computation prices the call in the price process. At the compensated drift the call
price function is the call of the canonical model (`jumpDiffusionCallPrice_eq_canonical`). With
Gaussian jumps it is therefore Merton's series, and the conditional value of the call at every
date before maturity is Merton's 1976 formula at the current price and the remaining maturity.

## Main results

* `JumpDiffusionHyp.call_eq_mertonCallPrice`: with Gaussian log-jumps and the compensator `kΛ`,
  the call is `mertonCallPrice`.
* `JumpDiffusionHyp.put_eq_mertonPutPrice`: the put is `mertonPutPrice`, from the call by
  put–call parity (`merton_put_call_parity`) at the terminal law.
* `JumpDiffusionHyp.discounted_terminal_merton`: with the compensator `kΛ` the discounted
  terminal price has mean `S₀`.
* Merton's model exists: `jumpDiffusionHyp_canonical` at Merton's jump law
  `N(log(1 + k) − δ²/2, δ²)`.
* `jumpDiffusionCallPrice_gaussian_eq_mertonCallPrice`: with Gaussian jumps and the compensated
  drift `b = r − σ²/2 − Λk`, the call price function over `τ` is `mertonCallPrice` at the expected
  jump count `Λτ`.
* `JumpDiffusionProcess.condExp_call_eq_mertonCallPrice`: for `t < T`, the conditional value of
  the call given `𝓕_t` is `mertonCallPrice` at `S_t`, `T − t` and `Λ(T − t)`.
* `jumpDiffusionPutPrice_gaussian_eq_mertonPutPrice` and
  `JumpDiffusionProcess.condExp_put_eq_mertonPutPrice`: the same for the put and `mertonPutPrice`,
  through the two put–call parities.

## References

* [Cont and Tankov, *Financial Modelling with Jump Processes*][ContTankov2004]
* [R. C. Merton, *Option pricing when underlying stock returns are discontinuous*][Merton1976]

## Tags

Merton jump-diffusion, Poisson series, lognormal jumps, jump-adjusted volatility,
option pricing with jumps, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

/-- Merton's log-jump law `N(log(1 + k) − δ²/2, δ²)` has `𝔼[e^J] = 1 + k`: the jump multipliers
have mean `1 + k` (the lognormal mean, `integral_exp_gaussianReal`). -/
lemma integral_exp_mertonJump {k : ℝ} (hk : -1 < k) (δ : ℝ) :
    ∫ x, rexp x ∂(gaussianReal (Real.log (1 + k) - δ ^ 2 / 2) (δ ^ 2).toNNReal) = 1 + k := by
  rw [integral_exp_gaussianReal, Real.coe_toNNReal _ (sq_nonneg δ), sub_add_cancel,
    Real.exp_log (show (0 : ℝ) < 1 + k by linarith)]

/-- With Merton's log-jumps the compensated drift `r − σ²/2 − Λ(𝔼[e^J] − 1)` is
`r − σ²/2 − Λk`. -/
lemma mertonJump_compensated {k : ℝ} (hk : -1 < k) (δ : ℝ) {r b σ : ℝ} {Λ : ℝ≥0}
    (hb : b = r - σ ^ 2 / 2 - Λ * k) :
    b = r - σ ^ 2 / 2 - Λ * (∫ x, rexp x
      ∂(gaussianReal (Real.log (1 + k) - δ ^ 2 / 2) (δ ^ 2).toNNReal) - 1) := by
  rw [integral_exp_mertonJump hk δ, hb]
  ring

/-- **Put–call parity for discounted payoffs.** For an integrable terminal price `S` under a
probability measure, the discounted put payoff `D(K − S)⁺` has expectation
`𝔼[D(S − K)⁺] − 𝔼[D·S] + D·K`: pointwise the put payoff is the call payoff minus the forward plus
the strike (`max_zero_sub_max_neg_zero_eq_self`). -/
lemma integral_discounted_put_payoff {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω}
    [IsProbabilityMeasure Q] {S : Ω → ℝ} (hS : Integrable S Q) (D K : ℝ) :
    ∫ ω, D * max (K - S ω) 0 ∂Q
      = ∫ ω, D * max (S ω - K) 0 ∂Q - ∫ ω, D * S ω ∂Q + D * K := by
  have hcall : Integrable (fun ω ↦ D * max (S ω - K) 0) Q :=
    ((hS.sub' (integrable_const K)).pos_part).const_mul D
  have hfwd : Integrable (fun ω ↦ D * S ω) Q := hS.const_mul D
  have hpar (ω : Ω) : D * max (K - S ω) 0
      = D * max (S ω - K) 0 - (D * S ω - D * K) := by
    have hx := max_zero_sub_max_neg_zero_eq_self (S ω - K)
    rw [neg_sub] at hx
    linear_combination -D * hx
  have hfwd' : Integrable (fun ω ↦ D * S ω - D * K) Q := hfwd.sub (integrable_const _)
  rw [integral_congr_ae (ae_of_all _ hpar), integral_sub hcall hfwd',
    integral_sub hfwd (integrable_const (D * K)), integral_const, probReal_univ, one_smul]
  ring

namespace JumpDiffusionHyp

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} {Λ : ℝ≥0} {Z : Ω → ℝ}
  {N : Ω → ℕ} {J : ℕ → Ω → ℝ}

/-- **Merton's formula from the general jump-diffusion.** With log-jumps
`Jᵢ ∼ N(log(1 + k) − δ²/2, δ²)` and the compensator `κ = kΛ`, the call is Merton's series
`mertonCallPrice`. With `n` jumps the jump part is `N(n(log(1 + k) − δ²/2), nδ²)`, and Gaussian
smoothing of the Black–Scholes price gives the `n`-th term
(`integral_bsV_mul_exp_gaussianReal_of_sq`). -/
theorem call_eq_mertonCallPrice (h : JumpDiffusionHyp Q Λ Z N J) {k δ : ℝ} (hk : -1 < k)
    (hJ : HasLaw (J 0) (gaussianReal (Real.log (1 + k) - δ ^ 2 / 2) (δ ^ 2).toNNReal) Q)
    {S_0 K r σ T : ℝ} (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) :
    ∫ ω, rexp (-r * T) * max (jumpDiffusionTerminal S_0 r σ T (k * Λ) (Z ω) (N ω)
        (fun i ↦ J i ω) - K) 0 ∂Q
      = mertonCallPrice S_0 K r σ T k δ Λ := by
  have hJexp : Integrable (fun ω ↦ rexp (J 0 ω)) Q := by
    simpa only [one_mul] using hJ.integrable_fun_comp (integrable_exp_mul_gaussianReal 1)
  have h1k : (0 : ℝ) < 1 + k := by linarith
  rw [h.call_poisson_mixture hJexp hS_0 hK hσ hT (k * Λ), mertonCallPrice]
  refine integral_congr_ae (ae_of_all _ fun n ↦ ?_)
  -- with `n` jumps the jump part is Gaussian
  have hsum : HasLaw (fun ω ↦ ∑ i ∈ Finset.range n, J i ω)
      (gaussianReal (n * (Real.log (1 + k) - δ ^ 2 / 2)) (n * (δ ^ 2).toNNReal)) Q :=
    (hasLaw_sum_range_gaussianReal (fun i ↦ (h.J_ident i).symm.hasLaw hJ) h.J_indep n).congr
      (ae_of_all _ fun ω ↦ (Finset.sum_apply ω _ _).symm)
  have hvar : mertonVol σ δ T n ^ 2 * T = σ ^ 2 * T + ((n * (δ ^ 2).toNNReal : ℝ≥0) : ℝ) := by
    rw [mertonVol_sq_mul σ δ hT n, NNReal.coe_mul, NNReal.coe_natCast,
      Real.coe_toNNReal _ (sq_nonneg δ)]
  have hbs : Measurable fun x ↦ bsV K r σ (S_0 * rexp (-(k * Λ)) * rexp x) T :=
    (measurable_bsV_spot K r σ T).comp (by fun_prop)
  calc ∫ ω, bsV K r σ (S_0 * rexp (-(k * Λ) + ∑ i ∈ Finset.range n, J i ω)) T ∂Q
      = ∫ ω, bsV K r σ (S_0 * rexp (-(k * Λ)) * rexp (∑ i ∈ Finset.range n, J i ω)) T ∂Q := by
        simp only [Real.exp_add, mul_assoc]
    _ = ∫ x, bsV K r σ (S_0 * rexp (-(k * Λ)) * rexp x) T
          ∂(gaussianReal (n * (Real.log (1 + k) - δ ^ 2 / 2)) (n * (δ ^ 2).toNNReal)) :=
        hsum.integral_comp hbs.aestronglyMeasurable
    _ = bsV K r (mertonVol σ δ T n) (S_0 * rexp (-(k * Λ))
          * rexp (n * (Real.log (1 + k) - δ ^ 2 / 2) + ((n * (δ ^ 2).toNNReal : ℝ≥0) : ℝ) / 2))
          T :=
        integral_bsV_mul_exp_gaussianReal_of_sq (mul_pos hS_0 (Real.exp_pos _)) hK hσ
          (mertonVol_pos hσ hT n) hT _ hvar
    _ = mertonCallTerm S_0 K r σ T k δ Λ n := by
        rw [mertonCallTerm_eq_bsV, mertonSpot, NNReal.coe_mul, NNReal.coe_natCast,
          Real.coe_toNNReal _ (sq_nonneg δ),
          show (n : ℝ) * (Real.log (1 + k) - δ ^ 2 / 2) + n * δ ^ 2 / 2 = n * Real.log (1 + k)
            by ring,
          Real.exp_nat_mul, Real.exp_log h1k]

/-- The discounted terminal price at the compensator `kΛ`, with Merton's Gaussian log-jumps, has
mean `S₀`: `𝔼[e^J] = 1 + k` (`integral_exp_mertonJump`), so the compensator of
`discounted_terminal_eq_iff` is `Λ(𝔼[e^J] − 1) = kΛ`. -/
theorem discounted_terminal_merton (h : JumpDiffusionHyp Q Λ Z N J) {k δ : ℝ} (hk : -1 < k)
    (hJ : HasLaw (J 0) (gaussianReal (Real.log (1 + k) - δ ^ 2 / 2) (δ ^ 2).toNNReal) Q)
    (S_0 r σ : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ∫ ω, rexp (-r * T) * jumpDiffusionTerminal S_0 r σ T (k * Λ) (Z ω) (N ω)
        (fun i ↦ J i ω) ∂Q = S_0 := by
  have hJexp : Integrable (fun ω ↦ rexp (J 0 ω)) Q := by
    simpa only [one_mul] using hJ.integrable_fun_comp (integrable_exp_mul_gaussianReal 1)
  have hmean : ∫ ω, rexp (J 0 ω) ∂Q = 1 + k :=
    (hJ.integral_comp (f := rexp) measurable_exp.aestronglyMeasurable).trans
      (integral_exp_mertonJump hk δ)
  rw [h.discounted_terminal hJexp S_0 r σ hT (k * Λ), hmean,
    show -(k * (Λ : ℝ)) + Λ * (1 + k - 1) = 0 by ring, Real.exp_zero, mul_one]

/-- **Merton's put formula from the general jump-diffusion.** With log-jumps
`Jᵢ ∼ N(log(1 + k) − δ²/2, δ²)` and the compensator `κ = kΛ`, the put is Merton's series
`mertonPutPrice`: the put payoff is the call payoff minus the forward and plus the strike
(`max_zero_sub_max_neg_zero_eq_self`), so the put is the call (`call_eq_mertonCallPrice`)
minus the discounted forward `S₀` (`discounted_terminal_merton`) plus `Ke^{−rT}`, which is
`mertonPutPrice` by `merton_put_call_parity`. -/
theorem put_eq_mertonPutPrice (h : JumpDiffusionHyp Q Λ Z N J) {k δ : ℝ} (hk : -1 < k)
    (hJ : HasLaw (J 0) (gaussianReal (Real.log (1 + k) - δ ^ 2 / 2) (δ ^ 2).toNNReal) Q)
    {S_0 K r σ T : ℝ} (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) :
    ∫ ω, rexp (-r * T) * max (K - jumpDiffusionTerminal S_0 r σ T (k * Λ) (Z ω) (N ω)
        (fun i ↦ J i ω)) 0 ∂Q = mertonPutPrice S_0 K r σ T k δ Λ := by
  have := h.J_indep.isProbabilityMeasure
  have hJexp : Integrable (fun ω ↦ rexp (J 0 ω)) Q := by
    simpa only [one_mul] using hJ.integrable_fun_comp (integrable_exp_mul_gaussianReal 1)
  have hS : Integrable (fun ω ↦ jumpDiffusionTerminal S_0 r σ T (k * Λ) (Z ω) (N ω)
      (fun i ↦ J i ω)) Q := by
    simp_rw [jumpDiffusionTerminal_eq]
    exact integrable_jumpDiffusion_terminal h.Z_law (h.indepFun_jumpPart _)
      (h.integrable_exp_jumpPart hJexp _)
  have hparity := merton_put_call_parity (r := r) δ Λ hS_0 hK hσ hT hk
  have hcall := h.call_eq_mertonCallPrice hk hJ hS_0 hK hσ hT (r := r)
  have hfwd := h.discounted_terminal_merton hk hJ S_0 r σ hT.le
  rw [integral_discounted_put_payoff hS, hcall, hfwd]
  linarith

end JumpDiffusionHyp

/-- **Merton's 1976 formula for the call price function.** With log-jumps
`N(log(1 + k) − δ²/2, δ²)` and the compensated drift `b = r − σ²/2 − Λk`, the call price
function over a time `τ > 0` is Merton's series `mertonCallPrice` at the expected jump count
`Λτ`: the price function is the call of the canonical model with that expected jump count
(`jumpDiffusionCallPrice_eq_canonical`), with `𝔼[e^J] = 1 + k`
(`integral_exp_mertonJump`). -/
theorem jumpDiffusionCallPrice_gaussian_eq_mertonCallPrice {S K r b σ k δ : ℝ} (hS : 0 < S)
    (hK : 0 < K) (hσ : 0 < σ) (hk : -1 < k) {Λ : ℝ≥0} (hb : b = r - σ ^ 2 / 2 - Λ * k)
    {τ : ℝ≥0} (hτ : 0 < τ) :
    jumpDiffusionCallPrice S K r b σ Λ
        (gaussianReal (Real.log (1 + k) - δ ^ 2 / 2) (δ ^ 2).toNNReal) τ
      = mertonCallPrice S K r σ τ k δ (Λ * τ) := by
  obtain ⟨h, hJ⟩ := jumpDiffusionHyp_canonical (Λ * τ)
    (gaussianReal (Real.log (1 + k) - δ ^ 2 / 2) (δ ^ 2).toNNReal)
  rw [jumpDiffusionCallPrice_eq_canonical S K (mertonJump_compensated hk δ hb) τ,
    integral_exp_mertonJump hk δ,
    show (Λ : ℝ) * τ * (1 + k - 1) = k * (Λ * τ : ℝ≥0) by push_cast; ring]
  exact h.call_eq_mertonCallPrice hk (hJ 0) hS hK hσ (NNReal.coe_pos.2 hτ)

/-- **Merton's 1976 put formula for the put price function.** With log-jumps
`N(log(1 + k) − δ²/2, δ²)` and the compensated drift `b = r − σ²/2 − Λk`, the put price function
over a time `τ > 0` is Merton's put series `mertonPutPrice` at the expected jump count `Λτ`: both
satisfy put–call parity with the same right side `S − Ke^{−rτ}`
(`jumpDiffusionCallPrice_eq_of_compensated`, `merton_put_call_parity`), and the calls agree. -/
theorem jumpDiffusionPutPrice_gaussian_eq_mertonPutPrice {S K r b σ k δ : ℝ} (hS : 0 < S)
    (hK : 0 < K) (hσ : 0 < σ) (hk : -1 < k) {Λ : ℝ≥0} (hb : b = r - σ ^ 2 / 2 - Λ * k)
    {τ : ℝ≥0} (hτ : 0 < τ) :
    jumpDiffusionPutPrice S K r b σ Λ
        (gaussianReal (Real.log (1 + k) - δ ^ 2 / 2) (δ ^ 2).toNNReal) τ
      = mertonPutPrice S K r σ τ k δ (Λ * τ) := by
  have hpar := jumpDiffusionCallPrice_eq_of_compensated (S := S) (K := K)
    (integrable_exp_gaussianReal _ _) (mertonJump_compensated hk δ hb) τ
  rw [jumpDiffusionCallPrice_gaussian_eq_mertonCallPrice hS hK hσ hk hb hτ] at hpar
  linarith [merton_put_call_parity (r := r) δ (Λ * τ) hS hK hσ (NNReal.coe_pos.2 hτ) hk]

namespace JumpDiffusionProcess

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {b σ : ℝ} {Λ : ℝ≥0}

/-- **Merton's 1976 formula at every date before maturity.** In a jump-diffusion with log-jumps
`N(log(1 + k) − δ²/2, δ²)` at the compensated drift `b = r − σ²/2 − Λk`, for `t < T` the
conditional value of the call given `𝓕_t` is Merton's series `mertonCallPrice` at the current
price `S_t = S₀e^{X_t}`, the remaining maturity `T − t` and the expected number of jumps
`Λ(T − t)` (`condExp_call`, `jumpDiffusionCallPrice_gaussian_eq_mertonCallPrice`). -/
theorem condExp_call_eq_mertonCallPrice {k δ : ℝ}
    (h : JumpDiffusionProcess P 𝓕 X b σ Λ
      (gaussianReal (Real.log (1 + k) - δ ^ 2 / 2) (δ ^ 2).toNNReal))
    (hk : -1 < k) {r : ℝ} (hb : b = r - σ ^ 2 / 2 - Λ * k)
    {S_0 K : ℝ} (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) {t T : ℝ≥0} (htT : t < T) :
    P[fun ω ↦ rexp (-r * (T - t : ℝ≥0)) * max (S_0 * rexp (X T ω) - K) 0 | 𝓕 t]
      =ᵐ[P] fun ω ↦ mertonCallPrice (S_0 * rexp (X t ω)) K r σ (T - t : ℝ≥0) k δ
        (Λ * (T - t)) :=
  (h.condExp_call (integrable_exp_gaussianReal _ _) S_0 K r htT.le).trans <|
    ae_of_all _ fun _ ↦ jumpDiffusionCallPrice_gaussian_eq_mertonCallPrice
      (mul_pos hS_0 (Real.exp_pos _)) hK hσ hk hb (tsub_pos_of_lt htT)

/-- **Merton's 1976 put formula at every date before maturity.** Under the hypotheses of
`condExp_call_eq_mertonCallPrice`, the conditional value of the put given `𝓕_t` is Merton's put
series `mertonPutPrice` at `S_t`, `T − t` and `Λ(T − t)` (`condExp_put`,
`jumpDiffusionPutPrice_gaussian_eq_mertonPutPrice`). -/
theorem condExp_put_eq_mertonPutPrice {k δ : ℝ}
    (h : JumpDiffusionProcess P 𝓕 X b σ Λ
      (gaussianReal (Real.log (1 + k) - δ ^ 2 / 2) (δ ^ 2).toNNReal))
    (hk : -1 < k) {r : ℝ} (hb : b = r - σ ^ 2 / 2 - Λ * k)
    {S_0 K : ℝ} (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) {t T : ℝ≥0} (htT : t < T) :
    P[fun ω ↦ rexp (-r * (T - t : ℝ≥0)) * max (K - S_0 * rexp (X T ω)) 0 | 𝓕 t]
      =ᵐ[P] fun ω ↦ mertonPutPrice (S_0 * rexp (X t ω)) K r σ (T - t : ℝ≥0) k δ
        (Λ * (T - t)) :=
  have := h.isProbabilityMeasure
  (h.condExp_put hS_0.le K r htT.le).trans <|
    ae_of_all _ fun _ ↦ jumpDiffusionPutPrice_gaussian_eq_mertonPutPrice
      (mul_pos hS_0 (Real.exp_pos _)) hK hσ hk hb (tsub_pos_of_lt htT)

end JumpDiffusionProcess

end MathFin
