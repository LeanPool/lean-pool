/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Pricing.StatePrices
public import LeanPool.MathFin.Contracts.Instruments.CallPayoff

/-!
# Convexity passes through the pricing functional

**If the payoffs `g i K` are convex in a parameter `K` in every state, and the state prices `q i`
are non-negative, then the price `K ↦ statePricePricing s q (g · K)` is convex in `K`.** Pricing
with non-negative state prices is a positive linear functional, and a positive linear functional
preserves convexity.

That is why call prices are convex in the strike and why a butterfly spread costs nothing
negative: the call payoff is convex in the strike (`convexOn_call_payoff`,
`Contracts/Instruments/CallPayoff.lean`), and the pricing functional carries the convexity from
payoff to price. Neither fact about prices is separate from this one.

The same principle under an arbitrary law is `convexOn_integral_call`
(`Models/BlackScholes/StrikeConvexity.lean`), Mathlib's `integral_convexOn_of_integrand_ae`
applied to the call payoff, of which the finite-state statements here are the finitely supported
case; its infinitesimal face is `∂²_K bsV ≥ 0` (`bsV_partial_KK_nonneg`) and the non-negativity of
the implied density (`Models/ModelFree/BreedenLitzenberger.lean`).

## Main results

* `statePricePricing_convexOn`: pricing with non-negative state prices preserves convexity in any
  parameter.
* `callPrice_finiteState_convexOn_K`: in a finite-state market the call price is convex in the
  strike.
* `callPrice_finiteState_butterfly_nonneg`: a butterfly spread has non-negative price, the
  price-level face of `butterfly_payoff_nonneg` (`Models/ModelFree/Spreads.lean`).

## References

* [Breeden and Litzenberger, *Prices of state-contingent claims implicit in option
  prices*][BreedenLitzenberger1978]
* [R. C. Merton, *Theory of rational option pricing*][Merton1973]

## Tags

state prices, convexity preservation, butterfly spread, finite-state market, Arrow–Debreu,
MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open Finset

variable {ι : Type*}

/-- **The pricing functional preserves convexity.** With non-negative state prices `q i` on `s`,
if each state's payoff `g i K` is convex in `K`, so is the price `statePricePricing s q (g · K)`:
each state's convexity inequality, multiplied by `q i ≥ 0`, sums to the price's. -/
theorem statePricePricing_convexOn
    (s : Finset ι) (q : ι → ℝ) (hq : ∀ i ∈ s, 0 ≤ q i)
    (g : ι → ℝ → ℝ) (hg : ∀ i ∈ s, ConvexOn ℝ (Set.univ : Set ℝ) (g i)) :
    ConvexOn ℝ (Set.univ : Set ℝ) (fun K ↦ statePricePricing s q (fun i ↦ g i K)) := by
  refine ⟨convex_univ, fun K₁ _ K₂ _ a b ha hb hab ↦ ?_⟩
  change ∑ i ∈ s, q i * g i (a • K₁ + b • K₂)
        ≤ a • (∑ i ∈ s, q i * g i K₁) + b • (∑ i ∈ s, q i * g i K₂)
  simp only [smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i hi ↦ ?_
  have hconv := (hg i hi).2 (Set.mem_univ K₁) (Set.mem_univ K₂) ha hb hab
  simp only [smul_eq_mul] at hconv
  linarith [mul_le_mul_of_nonneg_left hconv (hq i hi),
    show q i * (a * g i K₁ + b * g i K₂) = a * (q i * g i K₁) + b * (q i * g i K₂) by ring]

/-- **The call price is convex in the strike (finite-state market).** With non-negative state
prices and terminal values `S i`, the price `K ↦ statePricePricing s q (max (S · − K) 0)` of the
call struck at `K` is convex: the payoff is (`convexOn_call_payoff`), and pricing preserves it
(`statePricePricing_convexOn`). -/
theorem callPrice_finiteState_convexOn_K (s : Finset ι)
    (S : ι → ℝ) (q : ι → ℝ) (hq : ∀ i ∈ s, 0 ≤ q i) :
    ConvexOn ℝ (Set.univ : Set ℝ)
      (fun K ↦ statePricePricing s q (fun i ↦ max (S i - K) 0)) :=
  statePricePricing_convexOn s q hq (fun i K ↦ max (S i - K) 0) fun i _ ↦
    convexOn_call_payoff (S i)

/-- **A butterfly spread has non-negative price (finite-state market).** For strikes `K₁, K₃`
and their midpoint, with `C(K) = statePricePricing s q (max (S · − K) 0)` the call price,
`C(K₁) − 2 C((K₁ + K₃)/2) + C(K₃) ≥ 0`: the midpoint inequality of the convex price
(`callPrice_finiteState_convexOn_K`). Its payoff-level face is `butterfly_payoff_nonneg`, and its
continuous-law counterpart, through `convexOn_integral_call`, is the non-negativity of the implied
density. -/
theorem callPrice_finiteState_butterfly_nonneg (s : Finset ι)
    (S : ι → ℝ) (q : ι → ℝ) (hq : ∀ i ∈ s, 0 ≤ q i) (K₁ K₃ : ℝ) :
    0 ≤ statePricePricing s q (fun i ↦ max (S i - K₁) 0)
        - 2 * statePricePricing s q (fun i ↦ max (S i - (K₁ + K₃) / 2) 0)
        + statePricePricing s q (fun i ↦ max (S i - K₃) 0) := by
  have h := (callPrice_finiteState_convexOn_K s S q hq).2 (Set.mem_univ K₁) (Set.mem_univ K₃)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) + 1/2 = 1)
  simp only [smul_eq_mul] at h
  rw [show (1/2 * K₁ + 1/2 * K₃ : ℝ) = (K₁ + K₃) / 2 by ring] at h
  linarith

end MathFin
