/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Pricing.Market
public import LeanPool.MathFin.Models.BlackScholes.StrikeConvexity
public import LeanPool.MathFin.Models.ModelFree.CallPriceFunction

/-!
# A pricing measure gives a normalised call price function

Call prices in the strike are the static face of the fundamental theorem. In a market with unit
numéraire and a positive asset, a pricing measure `Q` up to `T` makes the asset a `Q`-martingale,
so its forward `F` is its mean, and the calls at the strikes `k F`, priced in units of `F`, are the
call prices `k ↦ 𝔼[(X − k)⁺]` of the positive mean-one variable `X = S_T / F`. Those are a
normalised call price function (`IsNormalizedCallPrice`): this is the forward direction of Roper's
Theorem 2.1. The converse, a market with a nonnegative asset for every normalised call price
function, is `exists_market_of_isNormalizedCallPrice` (`RoperConverse.lean`).

## Main results

* `isNormalizedCallPrice_integral_call`: for a positive integrable `X` of mean one under a
  probability measure, `k ↦ 𝔼[(X − k)⁺]` is a normalised call price function.
* `Market.IsPricingMeasure.isNormalizedCallPrice`: the same for the calls of a market with unit
  numéraire and a positive asset under a pricing measure, in units of the forward.

## References

* [Roper, *Arbitrage free implied volatility surfaces*][Roper2010], Theorem 2.1
* [Breeden and Litzenberger, *Prices of state-contingent claims implicit in option
  prices*][BreedenLitzenberger1978]

## Tags

call price in strike, pricing measure, static no-arbitrage, butterfly spread, forward,
MSC 91G20, JEL G13
-/

@[expose] public section

open MeasureTheory Filter Topology Set MathFin.Contracts
open scoped NNReal

namespace MathFin

/-- **The call prices of a positive mean-one variable are a normalised call price function.**
Convexity is that of the payoff carried through the integral (`convexOn_integral_call`); the
intrinsic bound is `𝔼[(X − K)⁺] ≥ 𝔼[X − K] = 1 − K`; the upper bound is `(X − K)⁺ ≤ X`; and the
price vanishes at large strikes by dominated convergence. -/
theorem isNormalizedCallPrice_integral_call {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Integrable X μ) (hpos : ∀ ω, 0 < X ω)
    (hmean : ∫ ω, X ω ∂μ = 1) :
    IsNormalizedCallPrice fun k ↦ ∫ ω, max (X ω - k) 0 ∂μ := by
  have hint (k : ℝ) : Integrable (fun ω ↦ max (X ω - k) 0) μ :=
    (hX.sub (integrable_const k)).pos_part
  refine .of_convexOn ((convexOn_integral_call hX).subset (subset_univ _) (convex_Ioi 0))
    (fun K _ ↦ max_le ?_ (integral_nonneg fun ω ↦ le_max_right _ _))
    (fun K hK ↦ ?_) ?_
  · calc 1 - K = ∫ ω, (X ω - K) ∂μ := by rw [integral_sub hX (integrable_const K), hmean]; simp
      _ ≤ _ := integral_mono (hX.sub (integrable_const K)) (hint K) fun ω ↦ le_max_left _ _
  · exact hmean ▸ integral_mono (hint K) hX fun ω ↦
      max_le (by linarith [Set.mem_Ioi.1 hK]) (hpos ω).le
  · simpa using tendsto_integral_filter_of_dominated_convergence (l := atTop) (f := fun _ ↦ 0) X
      (.of_forall fun k ↦ (hint k).1)
      (by
        filter_upwards [eventually_ge_atTop 0] with k hk
        exact .of_forall fun ω ↦ by
          rw [Real.norm_of_nonneg (le_max_right _ _)]
          exact max_le (by linarith) (hpos ω).le)
      hX
      (.of_forall fun ω ↦ tendsto_const_nhds.congr' (by
        filter_upwards [eventually_ge_atTop (X ω)] with k hk
        exact (max_eq_right (by linarith)).symm))

namespace Market

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {M : Market Unit Ω} {T : ℝ≥0} {Q : Measure Ω}

/-- **A pricing measure gives a normalised call price function.** In a market with unit numéraire
and a positive asset, priced at `T` by `Q`, the forward `F` of the asset is its price, and the
calls at the strikes `k F` priced in units of `F` are a normalised call price function: convex,
nonincreasing, between the intrinsic value and one, with limits one at strike `0` and zero at large
strikes. -/
theorem IsPricingMeasure.isNormalizedCallPrice (hQ : M.IsPricingMeasure T Q)
    (hN : ∀ t ω, M.numeraire t ω = 1) (hpos : ∀ ω, 0 < M.asset () T ω) {F : ℝ}
    (hF : F = M.price Q (.pay T (.obs () T))) :
    IsNormalizedCallPrice fun k ↦ M.price Q (europeanCall (k * F) T) / F := by
  have := hQ.isProb
  have hint : Integrable (M.asset () T) Q :=
    ((hQ.martingale ()).integrable T).congr (.of_forall fun ω ↦ by simp [deflated, hN])
  have hF' : F = ∫ ω, M.asset () T ω ∂Q := by
    simp [hF, price, Contract.value_pay, Payoff.eval, scenarioAt, deflator, hN]
  have hFpos : 0 < F := by
    rw [hF']
    refine (integral_pos_iff_support_of_nonneg (fun ω ↦ (hpos ω).le) hint).2 ?_
    have hsupp : Function.support (M.asset () T) = univ :=
      eq_univ_of_forall fun ω ↦ (hpos ω).ne'
    rw [hsupp, measure_univ]
    exact one_pos
  have key := isNormalizedCallPrice_integral_call (μ := Q) (X := fun ω ↦ M.asset () T ω / F)
    (hint.div_const F) (fun ω ↦ div_pos (hpos ω) hFpos)
    (by rw [integral_div, ← hF', div_self hFpos.ne'])
  refine key.of_eqOn fun k _ ↦ ?_
  simp only [price_europeanCall_of_numeraire_eq_one hN, ← integral_div]
  refine integral_congr_ae (.of_forall fun ω ↦ ?_)
  change max (M.asset () T ω / F - k) 0 = max (M.asset () T ω - k * F) 0 / F
  rw [← max_div_div_right hFpos.le, zero_div]
  congr 1
  field_simp

end Market

end MathFin
