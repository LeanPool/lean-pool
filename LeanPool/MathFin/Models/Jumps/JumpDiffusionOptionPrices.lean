/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Jumps.JumpDiffusionProcess
public import LeanPool.MathFin.Models.Jumps.JumpImpliedVol

/-!
# Option prices at intermediate dates in a jump-diffusion

In the jump-diffusion price process (`JumpDiffusionProcess`), the conditional expectation given
`𝓕_t` of a European payoff `f(X_T)` is a function of the current state alone: it is `F(X_t)`, with
`F(x) = ∫ f(x + y) dμ(y)` the payoff averaged over the log-return law `μ` over the remaining time
`T − t` (`JumpDiffusionProcess.condExp_comp`). This is the conditional freezing lemma
(`condExp_comp_prodMk_of_indep`): `X_t` is known at `t`, and the increment `X_T − X_t` is
independent of `𝓕_t` with law `μ`. For the discounted put and call payoffs, `F` is a price
function, the discounted expected payoff over a time `τ` started from a spot
(`jumpDiffusionPutPrice`, `jumpDiffusionCallPrice`), here at the current price `S_t` and
`τ = T − t`. The put payoff is bounded; the call payoff is integrable because `e^{X_T}` is.

The price functions satisfy put–call parity (`jumpDiffusionCallPrice_eq`): the payoff identity
`(x − K)⁺ − (K − x)⁺ = x − K` (`max_zero_sub_max_neg_zero_eq_self`) integrated against the
log-return law.

At the compensated drift `b = r − σ²/2 − Λ(𝔼[e^J] − 1)` the call price function is Merton's
formula for the jump law: the log-return law over `τ` is the law of the canonical model with
expected jump count `Λτ`, on which the call is the `Poisson(Λτ)` mixture of Black–Scholes prices
(`JumpDiffusionHyp.call_eq_integral_infinitePi`). So Merton's formula is the conditional value of
the call at every date before maturity, at the current spot and the remaining maturity. On the
same canonical model the call has a Black–Scholes implied volatility above `σ` once jumps occur
and move the price (`JumpDiffusionHyp.impliedVol_gt`), so the implied volatility of the
conditional call value is above `σ` at every date before maturity, almost surely.

## Main definitions

* `jumpDiffusionPutPrice`: the discounted expected put payoff `e^{−rτ}(K − Se^Y)⁺` over a time `τ`,
  with `Y` a jump-diffusion log-return over `τ` of drift `b`, volatility `σ`, rate `Λ` and jump
  law `ν`.
* `jumpDiffusionCallPrice`: the discounted expected call payoff `e^{−rτ}(Se^Y − K)⁺` for the same
  log-return.

## Main results

* `JumpDiffusionProcess.condExp_comp_prodMk`:
  `𝔼[g(X_t, X_T − X_t) | 𝓕_t] = ∫ g(X_t, y) dμ_{T−t}(y)`, with `μ_{T−t}` the log-return law over
  `T − t`, for Banach-valued `g`; and its case `JumpDiffusionProcess.condExp_comp`,
  `𝔼[f(X_T) | 𝓕_t] = ∫ f(X_t + y) dμ_{T−t}(y)`.
* `jumpDiffusionCallPrice_eq`, put–call parity of the price functions:
  `C(S, τ) = P(S, τ) + S·e^{(b + σ²/2 + Λ(𝔼[e^J] − 1) − r)τ} − Ke^{−rτ}`; at the compensated
  drift, `C − P = S − Ke^{−rτ}` (`jumpDiffusionCallPrice_eq_of_compensated`).
* `jumpDiffusionCallPrice_eq_merton`: at the compensated drift, `C(S, τ)` is Merton's formula.
* `jumpDiffusionCallPrice_impliedVol_gt`: at the compensated drift, with `Λ > 0` and a jump law
  other than `δ₀`, `C(S, τ)` has a unique Black–Scholes implied volatility, above `σ`.
* `JumpDiffusionProcess.condExp_put`: `𝔼[e^{−r(T−t)}(K − S_T)⁺ | 𝓕_t] = P(S_t, T − t)`, for
  `S₀ ≥ 0`.
* `JumpDiffusionProcess.condExp_call`: `𝔼[e^{−r(T−t)}(S_T − K)⁺ | 𝓕_t] = C(S_t, T − t)`, for
  `𝔼[e^J] < ∞`.
* `JumpDiffusionProcess.condExp_call_eq_merton`: at the compensated drift and for `t < T`, the
  conditional call value is Merton's formula at `S_t` and `T − t`.
* `JumpDiffusionProcess.condExp_call_impliedVol_gt`: under the same hypotheses as
  `jumpDiffusionCallPrice_impliedVol_gt`, the conditional call value has, almost surely, a unique
  implied volatility at `S_t` and `T − t`, above `σ`.

## References

* [Cont and Tankov, *Financial Modelling with Jump Processes*][ContTankov2004]
* [R. C. Merton, *Option pricing when underlying stock returns are discontinuous*][Merton1976]

## Tags

conditional expectation, Markov property, freezing lemma, option price at intermediate date,
jump-diffusion, MSC 91G20, MSC 60G51, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

/-- The jump-diffusion put price function: the discounted expected payoff `e^{−rτ}(K − Se^Y)⁺`
over a time `τ`, with `Y` a jump-diffusion log-return over `τ` (`jumpDiffusionIncrementLaw`). It
is an arbitrage-free price only at the compensated drift, where the discounted price is a
martingale (`JumpDiffusionProcess.martingale_iff`). -/
noncomputable def jumpDiffusionPutPrice (S K r b σ : ℝ) (Λ : ℝ≥0) (ν : Measure ℝ) (τ : ℝ≥0) :
    ℝ :=
  ∫ y, rexp (-r * τ) * max (K - S * rexp y) 0 ∂(jumpDiffusionIncrementLaw b σ Λ ν τ)

/-- The jump-diffusion call price function: the discounted expected payoff `e^{−rτ}(Se^Y − K)⁺`
over a time `τ`, with `Y` a jump-diffusion log-return over `τ`. Like the put's, it is an
arbitrage-free price only at the compensated drift. -/
noncomputable def jumpDiffusionCallPrice (S K r b σ : ℝ) (Λ : ℝ≥0) (ν : Measure ℝ) (τ : ℝ≥0) :
    ℝ :=
  ∫ y, rexp (-r * τ) * max (S * rexp y - K) 0 ∂(jumpDiffusionIncrementLaw b σ Λ ν τ)

/-- **Put–call parity for the price functions**:
`C(S, τ) = P(S, τ) + S·e^{(b + σ²/2 + Λ(𝔼[e^J] − 1) − r)τ} − Ke^{−rτ}`. The forward
`e^{−rτ}Se^Y` has mean `S·e^{(b + σ²/2 + Λ(𝔼[e^J] − 1) − r)τ}`
(`integral_exp_jumpDiffusionIncrementLaw`), which is `S` at the compensated drift; pointwise, the
call payoff is the put payoff plus the forward (`max_zero_sub_max_neg_zero_eq_self`). -/
theorem jumpDiffusionCallPrice_eq (S K r b σ : ℝ) (Λ : ℝ≥0) {ν : Measure ℝ}
    [IsProbabilityMeasure ν] (hν : Integrable rexp ν) (τ : ℝ≥0) :
    jumpDiffusionCallPrice S K r b σ Λ ν τ
      = jumpDiffusionPutPrice S K r b σ Λ ν τ
        + S * rexp ((b + σ ^ 2 / 2 + Λ * (∫ x, rexp x ∂ν - 1) - r) * τ)
        - K * rexp (-r * τ) := by
  have hexp := integrable_exp_jumpDiffusionIncrementLaw b σ Λ hν τ
  have hput : Integrable (fun y ↦ rexp (-r * τ) * max (K - S * rexp y) 0)
      (jumpDiffusionIncrementLaw b σ Λ ν τ) :=
    ((integrable_const K).sub (hexp.const_mul S)).pos_part.const_mul _
  have hfwd : Integrable (fun y ↦ rexp (-r * τ) * (S * rexp y))
      (jumpDiffusionIncrementLaw b σ Λ ν τ) :=
    (hexp.const_mul S).const_mul _
  have hdiff : Integrable (fun y ↦ rexp (-r * τ) * (S * rexp y) - rexp (-r * τ) * K)
      (jumpDiffusionIncrementLaw b σ Λ ν τ) :=
    hfwd.sub (integrable_const _)
  have hfwdI : ∫ y, rexp (-r * τ) * (S * rexp y) ∂(jumpDiffusionIncrementLaw b σ Λ ν τ)
      = S * rexp ((b + σ ^ 2 / 2 + Λ * (∫ x, rexp x ∂ν - 1) - r) * τ) := by
    rw [integral_const_mul, integral_const_mul,
      integral_exp_jumpDiffusionIncrementLaw b σ Λ hν τ, mul_left_comm, ← Real.exp_add]
    congr 2
    ring
  -- the call payoff is the put payoff plus the forward
  have hpar (y : ℝ) : rexp (-r * τ) * max (S * rexp y - K) 0
      = rexp (-r * τ) * max (K - S * rexp y) 0
        + (rexp (-r * τ) * (S * rexp y) - rexp (-r * τ) * K) := by
    have hx := max_zero_sub_max_neg_zero_eq_self (S * rexp y - K)
    rw [neg_sub] at hx
    linear_combination rexp (-r * τ) * hx
  rw [jumpDiffusionCallPrice, jumpDiffusionPutPrice, integral_congr_ae (ae_of_all _ hpar),
    integral_add hput hdiff, integral_sub hfwd (integrable_const _), hfwdI, integral_const,
    probReal_univ, one_smul]
  ring

/-- **Put–call parity at the compensated drift**: when `b = r − σ²/2 − Λ(𝔼[e^J] − 1)` the
forward is worth `S`, and `C(S, τ) = P(S, τ) + S − Ke^{−rτ}`. -/
theorem jumpDiffusionCallPrice_eq_of_compensated {S K r b σ : ℝ} {Λ : ℝ≥0} {ν : Measure ℝ}
    [IsProbabilityMeasure ν] (hν : Integrable rexp ν)
    (hb : b = r - σ ^ 2 / 2 - Λ * (∫ x, rexp x ∂ν - 1)) (τ : ℝ≥0) :
    jumpDiffusionCallPrice S K r b σ Λ ν τ
      = jumpDiffusionPutPrice S K r b σ Λ ν τ + S - K * rexp (-r * τ) := by
  have h0 : (b + σ ^ 2 / 2 + Λ * (∫ x, rexp x ∂ν - 1) - r) * τ = 0 := by
    rw [hb]
    ring
  rw [jumpDiffusionCallPrice_eq S K r b σ Λ hν τ, h0, Real.exp_zero, mul_one]

/-- At the compensated drift the call price function is the call of the canonical model with
expected jump count `Λτ`: the log-return over `τ` (`jumpDiffusionLogReturn`) is the exponent of
`jumpDiffusionTerminal` with the compensator `κ = Λτ(𝔼[e^J] − 1)`. -/
lemma jumpDiffusionCallPrice_eq_canonical (S K : ℝ) {r b σ : ℝ} {Λ : ℝ≥0} {ν : Measure ℝ}
    (hb : b = r - σ ^ 2 / 2 - Λ * (∫ x, rexp x ∂ν - 1)) (τ : ℝ≥0) :
    jumpDiffusionCallPrice S K r b σ Λ ν τ
      = ∫ ω, rexp (-r * τ) * max (jumpDiffusionTerminal S r σ τ (Λ * τ * (∫ x, rexp x ∂ν - 1))
          ω.1 ω.2.1 (fun i ↦ ω.2.2 i) - K) 0 ∂(jumpDiffusionMeasure (Λ * τ) ν) := by
  have hf : Measurable fun y : ℝ ↦ rexp (-r * τ) * max (S * rexp y - K) 0 := by fun_prop
  rw [jumpDiffusionCallPrice, jumpDiffusionIncrementLaw,
    integral_map (measurable_jumpDiffusionLogReturn b σ τ).aemeasurable hf.aestronglyMeasurable]
  refine integral_congr_ae (ae_of_all _ fun ω ↦ ?_)
  have hE : jumpDiffusionLogReturn b σ τ ω = (r - σ ^ 2 / 2) * τ - Λ * τ * (∫ x, rexp x ∂ν - 1)
      + σ * Real.sqrt τ * ω.1 + ∑ i ∈ Finset.range ω.2.1, ω.2.2 i := by
    rw [jumpDiffusionLogReturn, hb]
    ring
  simp only [hE, jumpDiffusionTerminal]

/-- **Merton's formula for the call price function.** At the compensated drift
`b = r − σ²/2 − Λ(𝔼[e^J] − 1)`, the call price function is Merton's formula for the jump law `ν`:
the `Poisson(Λτ)` mixture, over the jump count `n`, of the Black–Scholes price at the spot
`Se^{−Λτ(𝔼[e^J] − 1) + ∑_{i<n} jᵢ}`, averaged over the jump sizes `j ∼ ν^ℕ`. The price function is
the call of the canonical model with expected jump count `Λτ`
(`jumpDiffusionCallPrice_eq_canonical`), on which the call is
`JumpDiffusionHyp.call_eq_integral_infinitePi`. -/
theorem jumpDiffusionCallPrice_eq_merton {S K r b σ : ℝ} (hS : 0 < S) (hK : 0 < K) (hσ : 0 < σ)
    {Λ : ℝ≥0} {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : Integrable rexp ν)
    (hb : b = r - σ ^ 2 / 2 - Λ * (∫ x, rexp x ∂ν - 1)) {τ : ℝ≥0} (hτ : 0 < τ) :
    jumpDiffusionCallPrice S K r b σ Λ ν τ
      = ∫ n, ∫ j, bsV K r σ (S * rexp (-(Λ * τ * (∫ x, rexp x ∂ν - 1))
          + ∑ i ∈ Finset.range n, j i)) τ
          ∂(Measure.infinitePi fun _ : ℕ ↦ ν) ∂(poissonMeasure (Λ * τ)) := by
  obtain ⟨h, hJ⟩ := jumpDiffusionHyp_canonical (Λ * τ) ν
  have key := h.call_eq_integral_infinitePi (r := r) (integrable_exp_canonical_jump hν) hS hK hσ
    (NNReal.coe_pos.2 hτ) (Λ * τ * (∫ x, rexp x ∂ν - 1))
  rw [(hJ 0).map_eq] at key
  exact (jumpDiffusionCallPrice_eq_canonical S K hb τ).trans key

/-- **Jumps lift the implied volatility of the call price function.** At the compensated drift,
if jumps occur (`Λ > 0`, `τ > 0`) and move the price (the jump law is not the point mass at `0`),
the call price function `C(S, τ)` is the Black–Scholes price at exactly one positive volatility,
and that volatility is above `σ`: `JumpDiffusionHyp.impliedVol_gt` on the canonical model with
expected jump count `Λτ`. -/
theorem jumpDiffusionCallPrice_impliedVol_gt {S K r b σ : ℝ} (hS : 0 < S) (hK : 0 < K)
    (hσ : 0 < σ) {Λ : ℝ≥0} (hΛ : 0 < Λ) {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : Integrable rexp ν) (hν0 : ν ≠ Measure.dirac 0)
    (hb : b = r - σ ^ 2 / 2 - Λ * (∫ x, rexp x ∂ν - 1)) {τ : ℝ≥0} (hτ : 0 < τ) :
    ∃ σ_imp, σ < σ_imp ∧ bsV K r σ_imp S τ = jumpDiffusionCallPrice S K r b σ Λ ν τ ∧
      ∀ σ' > 0, bsV K r σ' S τ = jumpDiffusionCallPrice S K r b σ Λ ν τ → σ' = σ_imp := by
  obtain ⟨h, hJ⟩ := jumpDiffusionHyp_canonical (Λ * τ) ν
  -- the jumps move the price: the first jump size is not almost surely `0`
  have hJ0 : ¬(fun ω : ℝ × ℕ × (ℕ → ℝ) ↦ ω.2.2 0) =ᵐ[jumpDiffusionMeasure (Λ * τ) ν] 0 :=
    fun h0 ↦ hν0 ((hJ 0).map_eq.symm.trans (hasLaw_dirac_of_ae_eq (x := 0) h0).map_eq)
  have hcall : jumpDiffusionCallPrice S K r b σ Λ ν τ
      = ∫ ω, rexp (-r * τ) * max (jumpDiffusionTerminal S r σ τ
          ((Λ * τ : ℝ≥0) * (∫ ω', rexp (ω'.2.2 0) ∂(jumpDiffusionMeasure (Λ * τ) ν) - 1))
          ω.1 ω.2.1 (fun i ↦ ω.2.2 i) - K) 0 ∂(jumpDiffusionMeasure (Λ * τ) ν) := by
    rw [jumpDiffusionCallPrice_eq_canonical S K hb τ, integral_exp_canonical_jump (Λ * τ) ν,
      NNReal.coe_mul]
  rw [hcall]
  exact h.impliedVol_gt (integrable_exp_canonical_jump hν) (mul_pos hΛ hτ) hJ0 hS hK hσ
    (NNReal.coe_pos.2 hτ)

namespace JumpDiffusionProcess

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {b σ : ℝ} {Λ : ℝ≥0} {ν : Measure ℝ}

/-- **Payoffs of the current state and the increment.** Given `𝓕_t`, a payoff
`g(X_t, X_T − X_t)` at `T ≥ t`, with values in any Banach space, `g` strongly measurable and the
payoff integrable, has conditional expectation `∫ g(X_t, y) dμ(y)`, with `μ` the log-return law
over the remaining time `T − t` (`jumpDiffusionIncrementLaw`): the conditional freezing lemma
(`condExp_comp_prodMk_of_indep`) on the process, since `X_t` is known at `t` and the increment is
independent of `𝓕_t` with law `μ`. A payoff of the increment alone is a forward-start payoff. -/
theorem condExp_comp_prodMk {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (h : JumpDiffusionProcess P 𝓕 X b σ Λ ν) [IsFiniteMeasure P]
    {g : ℝ × ℝ → E} (hg : StronglyMeasurable g) {t T : ℝ≥0} (htT : t ≤ T)
    (hgi : Integrable (fun ω ↦ g (X t ω, X T ω - X t ω)) P) :
    P[fun ω ↦ g (X t ω, X T ω - X t ω) | 𝓕 t]
      =ᵐ[P] fun ω ↦ ∫ y, g (X t ω, y) ∂(jumpDiffusionIncrementLaw b σ Λ ν (T - t)) := by
  rw [← (h.law t T htT).map_eq]
  exact condExp_comp_prodMk_of_indep (𝓕.le t) (h.adapted t).measurable
    (h.law t T htT).aemeasurable (h.indep t T htT) hg hgi

/-- **European payoffs at intermediate dates.** Given `𝓕_t`, a payoff `f(X_T)` at `T ≥ t`, with
`f` measurable and `f(X_T)` integrable, has conditional expectation `F(X_t)`, where
`F(x) = ∫ f(x + y) dμ(y)` averages over the log-return law `μ` over the remaining time `T − t`
(`jumpDiffusionIncrementLaw`): the case `g(x, y) = f(x + y)` of `condExp_comp_prodMk`. -/
theorem condExp_comp (h : JumpDiffusionProcess P 𝓕 X b σ Λ ν) [IsFiniteMeasure P] {f : ℝ → ℝ}
    (hf : Measurable f) {t T : ℝ≥0} (htT : t ≤ T) (hfi : Integrable (fun ω ↦ f (X T ω)) P) :
    P[fun ω ↦ f (X T ω) | 𝓕 t]
      =ᵐ[P] fun ω ↦ ∫ y, f (X t ω + y) ∂(jumpDiffusionIncrementLaw b σ Λ ν (T - t)) := by
  simpa only [add_sub_cancel] using h.condExp_comp_prodMk (g := fun z : ℝ × ℝ ↦ f (z.1 + z.2))
    (hf.comp measurable_add).stronglyMeasurable htT (by simpa only [add_sub_cancel] using hfi)

/-- **The put at an intermediate date.** Given `𝓕_t`, the discounted put payoff at `T` has
conditional expectation `P(S_t, T − t)`, the put price function at the current price and the
remaining maturity (`condExp_comp`). For `S₀ ≥ 0` the payoff is bounded by
`e^{−r(T−t)}·max K 0`, so no moment of the jumps is needed. -/
theorem condExp_put (h : JumpDiffusionProcess P 𝓕 X b σ Λ ν) [IsFiniteMeasure P] {S_0 : ℝ}
    (hS_0 : 0 ≤ S_0) (K r : ℝ) {t T : ℝ≥0} (htT : t ≤ T) :
    P[fun ω ↦ rexp (-r * (T - t : ℝ≥0)) * max (K - S_0 * rexp (X T ω)) 0 | 𝓕 t]
      =ᵐ[P] fun ω ↦ jumpDiffusionPutPrice (S_0 * rexp (X t ω)) K r b σ Λ ν (T - t) := by
  have hf : Measurable fun x ↦ rexp (-r * (T - t : ℝ≥0)) * max (K - S_0 * rexp x) 0 := by
    fun_prop
  have hbd (x : ℝ) : ‖rexp (-r * (T - t : ℝ≥0)) * max (K - S_0 * rexp x) 0‖
      ≤ rexp (-r * (T - t : ℝ≥0)) * max K 0 := by
    rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (le_max_right _ _))]
    exact mul_le_mul_of_nonneg_left
      (max_le_max (sub_le_self K (mul_nonneg hS_0 (Real.exp_pos x).le)) le_rfl)
      (Real.exp_pos _).le
  refine (h.condExp_comp hf htT <| (integrable_const _).mono'
    (hf.comp ((h.adapted T).mono (𝓕.le T)).measurable).aestronglyMeasurable
    (ae_of_all _ fun ω ↦ hbd (X T ω))).trans (ae_of_all _ fun ω ↦ ?_)
  simp only [jumpDiffusionPutPrice, Real.exp_add, mul_assoc]

/-- **The call at an intermediate date.** Given `𝓕_t`, the discounted call payoff at `T` has
conditional expectation `C(S_t, T − t)`, the call price function at the current price and the
remaining maturity (`condExp_comp`). The payoff is integrable because `e^{X_T}` is, which needs
`𝔼[e^J] < ∞` under the jump law. -/
theorem condExp_call (h : JumpDiffusionProcess P 𝓕 X b σ Λ ν) [IsProbabilityMeasure ν]
    (hν : Integrable rexp ν) (S_0 K r : ℝ) {t T : ℝ≥0} (htT : t ≤ T) :
    P[fun ω ↦ rexp (-r * (T - t : ℝ≥0)) * max (S_0 * rexp (X T ω) - K) 0 | 𝓕 t]
      =ᵐ[P] fun ω ↦ jumpDiffusionCallPrice (S_0 * rexp (X t ω)) K r b σ Λ ν (T - t) := by
  have := h.isProbabilityMeasure
  refine (h.condExp_comp (f := fun x ↦ rexp (-r * (T - t : ℝ≥0)) * max (S_0 * rexp x - K) 0)
    (by fun_prop) htT ((((h.integrable_exp hν T).const_mul S_0).sub
      (integrable_const K)).pos_part.const_mul _)).trans (ae_of_all _ fun ω ↦ ?_)
  simp only [jumpDiffusionCallPrice, Real.exp_add, mul_assoc]

/-- **Merton's formula at intermediate dates.** At the compensated drift
`b = r − σ²/2 − Λ(𝔼[e^J] − 1)` and for `t < T`, the discounted call payoff at `T` has conditional
expectation given `𝓕_t` equal to Merton's formula for the jump law `ν` at the current price
`S_t = S₀e^{X_t}` and the remaining maturity `T − t` (`condExp_call`,
`jumpDiffusionCallPrice_eq_merton`). -/
theorem condExp_call_eq_merton (h : JumpDiffusionProcess P 𝓕 X b σ Λ ν)
    [IsProbabilityMeasure ν] (hν : Integrable rexp ν) {r : ℝ}
    (hb : b = r - σ ^ 2 / 2 - Λ * (∫ x, rexp x ∂ν - 1)) {S_0 K : ℝ} (hS_0 : 0 < S_0)
    (hK : 0 < K) (hσ : 0 < σ) {t T : ℝ≥0} (htT : t < T) :
    P[fun ω ↦ rexp (-r * (T - t : ℝ≥0)) * max (S_0 * rexp (X T ω) - K) 0 | 𝓕 t]
      =ᵐ[P] fun ω ↦ ∫ n, ∫ j, bsV K r σ (S_0 * rexp (X t ω)
          * rexp (-(Λ * (T - t : ℝ≥0) * (∫ x, rexp x ∂ν - 1)) + ∑ i ∈ Finset.range n, j i))
          (T - t : ℝ≥0) ∂(Measure.infinitePi fun _ : ℕ ↦ ν) ∂(poissonMeasure (Λ * (T - t))) :=
  (h.condExp_call hν S_0 K r htT.le).trans <| ae_of_all _ fun _ ↦
    jumpDiffusionCallPrice_eq_merton (mul_pos hS_0 (Real.exp_pos _)) hK hσ hν hb
      (tsub_pos_of_lt htT)

/-- **Jumps lift the implied volatility at every date before maturity.** At the compensated drift,
if jumps occur (`Λ > 0`) and move the price (the jump law is not the point mass at `0`), then for
`t < T`, almost surely, the conditional value of the call given `𝓕_t` is the Black–Scholes price,
at the current price `S_t` and the remaining maturity `T − t`, of exactly one positive volatility,
and that volatility is above `σ` (`condExp_call`, `jumpDiffusionCallPrice_impliedVol_gt`). -/
theorem condExp_call_impliedVol_gt (h : JumpDiffusionProcess P 𝓕 X b σ Λ ν)
    [IsProbabilityMeasure ν] (hν : Integrable rexp ν)
    (hν0 : ν ≠ Measure.dirac 0) (hΛ : 0 < Λ) {r : ℝ}
    (hb : b = r - σ ^ 2 / 2 - Λ * (∫ x, rexp x ∂ν - 1)) {S_0 K : ℝ} (hS_0 : 0 < S_0)
    (hK : 0 < K) (hσ : 0 < σ) {t T : ℝ≥0} (htT : t < T) :
    ∀ᵐ ω ∂P, ∃ σ_imp, σ < σ_imp ∧ bsV K r σ_imp (S_0 * rexp (X t ω)) (T - t : ℝ≥0)
        = P[fun ω' ↦ rexp (-r * (T - t : ℝ≥0)) * max (S_0 * rexp (X T ω') - K) 0 | 𝓕 t] ω ∧
      ∀ σ' > 0, bsV K r σ' (S_0 * rexp (X t ω)) (T - t : ℝ≥0)
        = P[fun ω' ↦ rexp (-r * (T - t : ℝ≥0)) * max (S_0 * rexp (X T ω') - K) 0 | 𝓕 t] ω →
        σ' = σ_imp := by
  filter_upwards [h.condExp_call hν S_0 K r htT.le] with ω hω
  obtain ⟨σ_imp, hlt, heq, huniq⟩ := jumpDiffusionCallPrice_impliedVol_gt
    (mul_pos hS_0 (Real.exp_pos (X t ω))) hK hσ hΛ hν hν0 hb (tsub_pos_of_lt htT)
  exact ⟨σ_imp, hlt, heq.trans hω.symm, fun σ' hσ' h' ↦ huniq σ' hσ' (h'.trans hω)⟩

end JumpDiffusionProcess

end MathFin
