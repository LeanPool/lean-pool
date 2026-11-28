/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.BlackScholes.PutGreeks
public import LeanPool.MathFin.Contracts.Instruments.CallPayoff
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Smooth.Flat

/-!
# Strike-direction convexity at every scale

The European call satisfies *the same* convexity-in-`K` fact at every scale of
resolution:

1. **Payoff level**, `K ↦ max(S − K, 0)`. Convex because the positive
   part of an affine function is convex (`ConvexOn.sup` on `(S − ·)` and
   `0`).
2. **Price level, under any law**, `K ↦ ∫ (X − K)⁺ dμ`. Convex because
   integration against a positive measure preserves the convexity of the
   payoff (`convexOn_integral_call`, Mathlib's
   `integral_convexOn_of_integrand_ae`). Strictly convex wherever the law
   charges every interval of strikes (`strictConvexOn_integral_call`): a
   butterfly spread with distinct strikes pays a positive amount when `X`
   ends strictly between its outer strikes.
3. **Finite-state price level**, `K ↦ Σ q_i · max(S_i − K, 0)`. Convex
   because non-negative linear combinations of convex functions are convex
   (`ConvexPricingFunctional.callPrice_finiteState_convexOn_K`).
4. **Continuous BS price level**, `K ↦ bsV K r σ S τ`. Convex on `(0, ∞)`
   for `S, σ, τ > 0`, as scale 2 for the standard normal law, the
   Black–Scholes price being the discounted expected payoff
   (`integral_bsCall_payoff_eq_bsV`). Strictly convex: the jump-diffusion
   without jumps, `bsV_strike_strictConvexOn` in
   `JumpDiffusionStrikeConvexity.lean`.

The scales are one principle realised at different levels of integration:
scale 4 is scale 2 for the standard normal law, and scale 3, proved in
`ConvexPricingFunctional.lean` by summing convex functions, is scale 2 for a
finitely supported measure.

## Downstream consequences (one principle, many faces)

* **Bull spread** `V(K₁) ≥ V(K₂)` for `K₁ ≤ K₂` — `Antitone`-payoff after
  pricing-functional preservation of monotonicity.
* **Butterfly non-negativity at payoff** (`butterfly_payoff_nonneg`) —
  convex-payoff second-difference inequality.
* **Butterfly non-negativity at price** (`callPrice_finiteState_butterfly_nonneg`) —
  pricing functional preserves convexity, hence the same second-difference
  is non-negative at the price level.
* **Breeden-Litzenberger PDF positivity**
  (`lognormalTerminalPDF_nonneg_via_strike_convexity`) — the infinitesimal
  manifestation of price-level convexity, from `bsV_strike_convexOn` below via
  `deriv_deriv_nonneg_of_convexOn`. That convexity comes from the payoff through
  integration (`convexOn_integral_call`), not from the sign of the closed form, so
  this derives the sign of the density from the convexity of the payoff and the
  positivity of the standard normal law (used as `ϕ ≥ 0` inside
  `bs_call_formula`).

## Main results

* `StrictConvexOn.smul`: a strictly convex function scaled by a positive
  constant is strictly convex.
* `convexOn_integral_call`: `K ↦ ∫ (X − K)⁺ dμ` is convex, for any integrable
  `X` under a finite measure.
* `strictConvexOn_integral_call`: it is strictly convex on a convex set of
  strikes `s` when `μ {k₁ < X < k₂} ≠ 0` for all `k₁ < k₂` in `s`.
* `bsV_strike_convexOn`: `K ↦ bsV K r σ S τ` is convex on `(0, ∞)`
  (continuous BS price level).

## References

* [Breeden and Litzenberger, *Prices of state-contingent claims implicit in option
  prices*][BreedenLitzenberger1978]
* [R. C. Merton, *Theory of rational option pricing*][Merton1973]

## Tags

call price convexity, butterfly arbitrage, Breeden–Litzenberger, implied density, strike convexity,
MSC 91G20, JEL G13
-/

@[expose] public section

/-- A strictly convex function scaled by a positive constant is strictly convex: the strict
counterpart of Mathlib's `ConvexOn.smul`. -/
theorem StrictConvexOn.smul {𝕜 E β : Type*} [CommSemiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E]
    [AddCommMonoid β] [PartialOrder β] [SMul 𝕜 E] [Module 𝕜 β] [PosSMulStrictMono 𝕜 β]
    {s : Set E} {f : E → β} {c : 𝕜} (hc : 0 < c) (hf : StrictConvexOn 𝕜 s f) :
    StrictConvexOn 𝕜 s fun x ↦ c • f x :=
  ⟨hf.1, fun x hx y hy hxy a b ha hb hab ↦
    calc c • f (a • x + b • y) < c • (a • f x + b • f y) :=
          smul_lt_smul_of_pos_left (hf.2 hx hy hxy ha hb hab) hc
      _ = a • c • f x + b • c • f y := by rw [smul_add, smul_comm c, smul_comm c]⟩

namespace MathFin

open MeasureTheory Set Real ProbabilityTheory

/-! ## The price under any law

Integrating the convex payoff against a law keeps it convex, and a law that
charges every interval of strikes makes it strictly convex. Nothing about the
law is assumed beyond a finite mean. -/

/-- **The call price is convex in the strike, under any law.** For an integrable `X` under a finite
measure `μ`, `k ↦ ∫ (X − k)⁺ dμ` is convex: integration against a positive measure preserves the
convexity of the payoff (`convexOn_call_payoff`), which is Mathlib's
`integral_convexOn_of_integrand_ae`. -/
theorem convexOn_integral_call {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : Integrable X μ) :
    ConvexOn ℝ univ fun k ↦ ∫ ω, max (X ω - k) 0 ∂μ :=
  integral_convexOn_of_integrand_ae convex_univ (ae_of_all _ fun ω ↦ convexOn_call_payoff (X ω))
    fun k _ ↦ (hX.sub (integrable_const k)).pos_part

/-- **The call price is strictly convex in the strike wherever the law charges every interval.** For
an integrable `X` under a finite measure `μ` and a convex set `s` of strikes such that
`μ {k₁ < X < k₂} ≠ 0` whenever `k₁ < k₂` lie in `s`, `k ↦ ∫ (X − k)⁺ dμ` is strictly convex on `s`:
every butterfly spread `a C(k₁) + b C(k₂) − C(a k₁ + b k₂)` (`a, b > 0`, `a + b = 1`) with distinct
strikes `k₁ ≠ k₂` in `s` has a positive price. Its payoff is nonnegative (`convexOn_call_payoff`),
and positive when `k₁ < X < k₂`, where the call struck at `k₂` pays nothing. -/
theorem strictConvexOn_integral_call {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : Integrable X μ) {s : Set ℝ} (hs : Convex ℝ s)
    (hμ : ∀ k₁ ∈ s, ∀ k₂ ∈ s, k₁ < k₂ → μ {ω | k₁ < X ω ∧ X ω < k₂} ≠ 0) :
    StrictConvexOn ℝ s fun k ↦ ∫ ω, max (X ω - k) 0 ∂μ := by
  have hcall (k : ℝ) : Integrable (fun ω ↦ max (X ω - k) 0) μ :=
    (hX.sub (integrable_const k)).pos_part
  refine LinearOrder.strictConvexOn_of_lt hs fun k₁ hk₁ k₂ hk₂ hk a b ha hb hab ↦ ?_
  obtain rfl : b = 1 - a := by linarith
  simp only [smul_eq_mul]
  have hA : Integrable (fun ω ↦ a * max (X ω - k₁) 0 + (1 - a) * max (X ω - k₂) 0) μ :=
    ((hcall k₁).const_mul a).add ((hcall k₂).const_mul (1 - a))
  have hφ : Integrable (fun ω ↦ a * max (X ω - k₁) 0 + (1 - a) * max (X ω - k₂) 0
      - max (X ω - (a * k₁ + (1 - a) * k₂)) 0) μ := hA.sub (hcall _)
  -- the butterfly payoff is nonnegative, and positive when `k₁ < X < k₂`
  have h0 : 0 < ∫ ω, (a * max (X ω - k₁) 0 + (1 - a) * max (X ω - k₂) 0
      - max (X ω - (a * k₁ + (1 - a) * k₂)) 0) ∂μ := by
    refine (integral_pos_iff_support_of_nonneg (fun ω ↦ ?_) hφ).2
      (pos_iff_ne_zero.2 fun h ↦ hμ k₁ hk₁ k₂ hk₂ hk (measure_mono_null (fun ω hω ↦ ?_) h))
    · exact sub_nonneg.2 (by simpa only [smul_eq_mul] using
        (convexOn_call_payoff (X ω)).2 (mem_univ k₁) (mem_univ k₂) ha.le hb.le hab)
    · obtain ⟨h₁, h₂⟩ := hω
      simp only [Function.mem_support, max_eq_left (sub_pos.2 h₁).le,
        max_eq_right (sub_nonpos.2 h₂.le), mul_zero, add_zero]
      exact (sub_pos.2 (max_lt (by linarith [mul_pos hb (sub_pos.2 h₂)])
        (mul_pos ha (sub_pos.2 h₁)))).ne'
  rw [integral_sub hA (hcall _), integral_add ((hcall k₁).const_mul a)
    ((hcall k₂).const_mul (1 - a)), integral_const_mul, integral_const_mul] at h0
  linarith

/-! ## The continuous-price face

The Black–Scholes price is the discounted call payoff integrated against the
standard normal law (`integral_bsCall_payoff_eq_bsV`), so it inherits the
convexity of the payoff through `convexOn_integral_call`. The second strike
derivative `e^{-rτ} · ϕ(d_2) / (K σ √τ)` (`hasDerivAt_deriv_bsV_K`) is then
nonnegative as a consequence (`lognormalTerminalPDF_nonneg_via_strike_convexity`),
and also by its sign (`bsV_partial_KK_nonneg`). Both routes use the positivity of
the standard normal density: this one inside `bs_call_formula`. -/

/-- **BS call price is convex in the strike on `(0, ∞)`** — the continuous-
price face of the K-convexity principle.

The Black–Scholes price is the discounted expected call payoff under the standard normal law
(`integral_bsCall_payoff_eq_bsV`), so this is `convexOn_integral_call` for that law. The sign of
the second strike derivative is not used. -/
theorem bsV_strike_convexOn {S r σ τ : ℝ} (hS : 0 < S) (hσ : 0 < σ) (hτ : 0 < τ) :
    ConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun K ↦ bsV K r σ S τ) :=
  (((convexOn_integral_call (integrable_bsTerminal_gaussianReal S r σ τ)).subset
      (subset_univ _) (convex_Ioi 0)).smul (Real.exp_pos (-r * τ)).le).congr fun K hK ↦ by
    simp only [smul_eq_mul]
    rw [← integral_const_mul]
    exact integral_bsCall_payoff_eq_bsV (Q := gaussianReal 0 1) (Z := id)
      ⟨hS, mem_Ioi.1 hK, hσ, hτ, HasLaw.id⟩

/-- **Put price is convex in the strike on `(0, ∞)`** — free from the call's
strike-convexity: `bsP = bsV + (K·e^{-rτ} − S)` differs from `bsV` by an affine
function of `K`, and convexity is preserved by adding an affine function. The
second-derivative apparatus of `PutStrikeConvexity` is not needed. -/
theorem bsP_strike_convexOn {S r σ τ : ℝ} (hS : 0 < S) (hσ : 0 < σ) (hτ : 0 < τ) :
    ConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun K ↦ bsP K r σ S τ) := by
  have h_eq : (fun K ↦ bsP K r σ S τ)
      = (fun K ↦ bsV K r σ S τ) + (fun K ↦ K * Real.exp (-(r * τ)) - S) := by
    funext K; simp only [Pi.add_apply]; rw [bsP_eq_bsV K r σ S τ]; ring
  rw [h_eq]
  refine (bsV_strike_convexOn hS hσ hτ).add ⟨convex_Ioi 0, fun K₁ _ K₂ _ s t _ _ hst ↦ ?_⟩
  dsimp only
  simp only [smul_eq_mul]
  nlinarith [show s * S + t * S = S from by linear_combination S * hst]

end MathFin
