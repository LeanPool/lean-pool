/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye, Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.BlackScholes.ImpliedVolatility
public import LeanPool.MathFin.Models.ModelFree.SVI.BlackScholesBridge
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
public import Mathlib.Probability.Martingale.Basic

/-!
# Calendar arbitrage: Gatheral–Jacquier Lemma 2.1

Gatheral and Jacquier, *Arbitrage-free SVI volatility surfaces* (Quantitative Finance 14(1),
2014), §2.1, Lemma 2.1: an implied total-variance surface `w(k, t)` is free of calendar spread
arbitrage iff `t ↦ w(k, t)` is non-decreasing for every log-moneyness `k`. The proof runs in two
steps, both proved here with zero rates, for maturities `t > 0`.

1. **Martingale step.** If the (forward) price `X_t` is a martingale, then for every level `L`
   the undiscounted call value `t ↦ E[(X_t − L)⁺]` is non-decreasing: by conditional Jensen,
   `(X_s − L)⁺ = (E[X_t | ℱ_s] − L)⁺ ≤ E[(X_t − L)⁺ | ℱ_s]` for `s ≤ t`.
2. **Black–Scholes step.** With zero rates the Black–Scholes call depends on volatility and
   maturity only through the total variance `w = σ²T` (for `σ, T > 0`; `totalVarianceCall` is
   the call at unit maturity and volatility `√w`), and for strike and spot `K, S > 0` it is
   strictly increasing in `w > 0` (positive vega, `bsV_strictMonoOn_sigma`). So call prices are
   non-decreasing in maturity at every strike iff total variance is non-decreasing in maturity
   at every log-moneyness.

## Main definitions

* `totalVarianceCall`: the zero-rate, unit-maturity Black–Scholes call `bsV K 0 (√w) S 1` at
  strike `K` and spot (forward) `S`, parametrised by total variance `w = σ²T`.

## Main results

* `integral_posPart_sub_mono_of_martingale`: `s ≤ t → E[(X_s − L)⁺] ≤ E[(X_t − L)⁺]`.
* `deriv_integral_posPart_sub_nonneg`: the maturity derivative of that call value is
  nonnegative (`∂_T C ≥ 0`, as a `deriv`).
* `bsV_eq_totalVarianceCall`: the zero-rate Black–Scholes call is a function of `σ²T`.
* `strictMonoOn_totalVarianceCall`: it is strictly increasing in total variance.
* `calendar_free_iff`: call prices non-decreasing in maturity on `t > 0` at every strike ↔
  `t ↦ w(k, t)` non-decreasing on `t > 0` at every `k` (the price form of Lemma 2.1).
* `monotone_totalVariance_of_martingale`: a total-variance surface whose Black–Scholes prices
  are the call values of a martingale is non-decreasing in maturity on `t > 0`.
* `SVI.bsSmile_calendar_free_iff`: the same equivalence for a maturity-indexed family of raw
  SVI slices, on the SVI library's `bsSmile` price.

**Scope.** Rates and dividends are zero and the forward is the spot `S`. In the last three
results the total variance is assumed positive on maturities `t > 0` and the monotonicity is on
`t > 0` (`MonotoneOn … (Ioi 0)`); nothing is assumed at `t ≤ 0`, so surfaces with
`w(k, t) → 0` as `t → 0⁺`, such as the flat `w = σ²t`, are covered. The local-variance
characterisation (crossed total-variance lines ↔ negative local variance) is not formalised
here.

## References

* [Gatheral and Jacquier, *Arbitrage-free SVI volatility surfaces*][GatheralJacquier2014], Section
  2.1, Lemma 2.1

## Tags

calendar spread arbitrage, total variance surface, Gatheral–Jacquier, SVI,
implied volatility surface, static arbitrage, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin
open MeasureTheory Set

/-! ### Martingale step -/

/-- **Calls on a martingale are non-decreasing in maturity** (Gatheral–Jacquier 2014,
Lemma 2.1, martingale half). For a real martingale `X` on a finite measure space and any level
`L`, `s ≤ t` implies `∫ (X_s − L)⁺ ≤ ∫ (X_t − L)⁺`. The proof is conditional Jensen
(`ConvexOn.map_condExp_le`) applied to the convex payoff `x ↦ (x − L)⁺`. -/
theorem integral_posPart_sub_mono_of_martingale {Ω ι : Type*} [Preorder ι] {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] {ℱ : Filtration ι mΩ} {X : ι → Ω → ℝ}
    (hX : Martingale X ℱ μ) (L : ℝ) {s t : ι} (hst : s ≤ t) :
    ∫ ω, (X s ω - L)⁺ ∂μ ≤ ∫ ω, (X t ω - L)⁺ ∂μ := by
  set φ : ℝ → ℝ := fun x ↦ (x - L)⁺
  have hφc : Continuous φ := by fun_prop
  have hcvx : ConvexOn ℝ univ φ :=
    ((convexOn_id convex_univ).sub (concaveOn_const L convex_univ)).sup
      (convexOn_const 0 convex_univ)
  have hint : ∀ u, Integrable (X u) μ := fun u ↦ hX.integrable u
  have hφint : ∀ u, Integrable (φ ∘ X u) μ := fun u ↦
    ((hint u).sub (integrable_const L)).pos_part
  have hJ := hcvx.map_condExp_le (ℱ.le s) (hφc.lowerSemicontinuous.lowerSemicontinuousOn univ)
    (by simp) isClosed_univ (hint t) (hφint t)
  have heq : φ ∘ X s =ᵐ[μ] φ ∘ μ[X t | ℱ s] := by
    filter_upwards [hX.2 s t hst] with ω hω
    simp [Function.comp, hω]
  calc ∫ ω, (X s ω - L)⁺ ∂μ = ∫ ω, (φ ∘ X s) ω ∂μ := rfl
    _ = ∫ ω, (φ ∘ μ[X t | ℱ s]) ω ∂μ := integral_congr_ae heq
    _ ≤ ∫ ω, (μ[φ ∘ X t | ℱ s]) ω ∂μ :=
        integral_mono_ae ((hφint s).congr heq) integrable_condExp hJ
    _ = ∫ ω, (X t ω - L)⁺ ∂μ := integral_condExp (ℱ.le s)

/-- **`∂_T C ≥ 0`**: the maturity derivative of the undiscounted call value on a real-indexed
martingale is nonnegative wherever it is taken (Mathlib's `deriv`, which is `0` where the
function is not differentiable). -/
theorem deriv_integral_posPart_sub_nonneg {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] {ℱ : Filtration ℝ mΩ} {X : ℝ → Ω → ℝ}
    (hX : Martingale X ℱ μ) (L t : ℝ) :
    0 ≤ deriv (fun u ↦ ∫ ω, (X u ω - L)⁺ ∂μ) t :=
  Monotone.deriv_nonneg fun _ _ h ↦ integral_posPart_sub_mono_of_martingale hX L h

/-! ### Black–Scholes step -/

/-- The zero-rate, unit-maturity Black–Scholes call at strike `K` and spot (forward) `S`,
parametrised by total variance `w = σ²T`. -/
noncomputable def totalVarianceCall (K S w : ℝ) : ℝ := bsV K 0 (Real.sqrt w) S 1

/-- With zero rates the Black–Scholes call depends on `σ` and `T` only through the total
variance `σ²T`, for `σ > 0` and `T > 0`. -/
theorem bsV_eq_totalVarianceCall {K S σ T : ℝ} (hσ : 0 < σ) (hT : 0 < T) :
    bsV K 0 σ S T = totalVarianceCall K S (σ ^ 2 * T) := by
  have hs : Real.sqrt (σ ^ 2 * T) = σ * Real.sqrt T := by
    rw [Real.sqrt_mul (sq_nonneg σ), Real.sqrt_sq hσ.le]
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hd1 : bsd1 S K 0 (σ * Real.sqrt T) 1 = bsd1 S K 0 σ T := by
    simp only [bsd1, Real.sqrt_one, mul_one, zero_add, mul_pow, Real.sq_sqrt hT.le]
    congr 1
    ring
  unfold totalVarianceCall bsV
  simp only [bsd2, hd1, hs, Real.sqrt_one, mul_one, zero_mul, neg_zero, Real.exp_zero]

/-- The total-variance call is strictly increasing in total variance on `(0, ∞)`, for strike
and spot `K, S > 0`. -/
theorem strictMonoOn_totalVarianceCall {K S : ℝ} (hK : 0 < K) (hS : 0 < S) :
    StrictMonoOn (totalVarianceCall K S) (Ioi 0) := by
  intro a ha b hb hab
  exact bsV_strictMonoOn_sigma hK one_pos hS (Real.sqrt_pos.mpr ha) (Real.sqrt_pos.mpr hb)
    (Real.sqrt_lt_sqrt (le_of_lt ha) hab)

/-- **Gatheral–Jacquier 2014, Lemma 2.1 (price form).** Let `w(k, t) > 0` be a total-variance
surface over log-moneyness `k` and maturity `t > 0`, priced with zero rates at forward `S > 0`:
the call at strike `K > 0` and maturity `t` is `totalVarianceCall K S (w (log (K / S)) t)`. Call
prices are non-decreasing in maturity on `t > 0` at every strike iff `t ↦ w(k, t)` is
non-decreasing on `t > 0` at every `k`. Nothing is assumed about `w` at `t ≤ 0`, so the flat
surface `w = σ²t` is covered. -/
theorem calendar_free_iff {S : ℝ} (hS : 0 < S) (w : ℝ → ℝ → ℝ)
    (hw : ∀ k, ∀ t, 0 < t → 0 < w k t) :
    (∀ K, 0 < K →
        MonotoneOn (fun t ↦ totalVarianceCall K S (w (Real.log (K / S)) t)) (Ioi 0)) ↔
      ∀ k, MonotoneOn (w k) (Ioi 0) := by
  constructor
  · intro h k a ha b hb hab
    have hK : 0 < S * Real.exp k := mul_pos hS (Real.exp_pos k)
    have hk : Real.log (S * Real.exp k / S) = k := by
      rw [mul_div_cancel_left₀ _ hS.ne', Real.log_exp]
    have := h _ hK ha hb hab
    simp only [hk] at this
    exact ((strictMonoOn_totalVarianceCall hK hS).le_iff_le (hw k a ha) (hw k b hb)).mp this
  · intro h K hK a ha b hb hab
    exact ((strictMonoOn_totalVarianceCall hK hS).le_iff_le (hw _ a ha) (hw _ b hb)).mpr
      (h _ ha hb hab)

/-- **Gatheral–Jacquier 2014, Lemma 2.1 (martingale direction).** If, at every strike `K > 0`
and maturity `t > 0`, the zero-rate Black–Scholes price of a total-variance surface `w`,
positive on `t > 0`, is the call value `∫ (X_t − K)⁺` of a real-indexed martingale `X`, then
`t ↦ w(k, t)` is non-decreasing on `t > 0` at every log-moneyness `k`. -/
theorem monotone_totalVariance_of_martingale {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] {ℱ : Filtration ℝ mΩ} {X : ℝ → Ω → ℝ}
    (hX : Martingale X ℱ μ) {S : ℝ} (hS : 0 < S) (w : ℝ → ℝ → ℝ)
    (hw : ∀ k, ∀ t, 0 < t → 0 < w k t)
    (hprice : ∀ K, 0 < K → ∀ t, 0 < t →
      ∫ ω, (X t ω - K)⁺ ∂μ = totalVarianceCall K S (w (Real.log (K / S)) t)) :
    ∀ k, MonotoneOn (w k) (Ioi 0) :=
  (calendar_free_iff hS w hw).mp fun K hK a ha b hb hab ↦ by
    simpa only [hprice K hK a ha, hprice K hK b hb] using
      integral_posPart_sub_mono_of_martingale hX K hab

namespace SVI

/-- **No calendar arbitrage for a family of raw SVI slices.** For raw SVI parameters `p t`
indexed by maturity `t > 0`, with positive variance, the SVI-smiled Black–Scholes price
`bsSmile` (spot, maturity and discount normalised to one) is non-decreasing in maturity on
`t > 0` at every strike iff the SVI total variance `t ↦ variance (p t) k` is non-decreasing on
`t > 0` at every log-moneyness `k` (Gatheral–Jacquier 2014, Lemma 2.1, specialised to the raw
SVI slices of their §3.1). -/
theorem bsSmile_calendar_free_iff (p : ℝ → Params)
    (hw : ∀ t, 0 < t → ∀ k, 0 < variance (p t) k) :
    (∀ K, 0 < K → MonotoneOn (fun t ↦ bsSmile (p t) K) (Ioi 0)) ↔
      ∀ k, MonotoneOn (fun t ↦ variance (p t) k) (Ioi 0) := by
  have := calendar_free_iff one_pos (fun k t ↦ variance (p t) k) fun k t ht ↦ hw t ht k
  simpa only [div_one, totalVarianceCall, bsSmile, rootVariance] using this

end SVI

end MathFin
