/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Analysis.Convex.Function

/-!
# Call payoffs in the strike

The call payoff `K ↦ max(S − K, 0)`, as a function of the strike, is convex and antitone. These are
facts about the payoff, before any model: the static no-arbitrage relations of option prices
(convexity in the strike, butterflies, the implied density) are these facts carried to prices by
the pricing functional (`Pricing/ConvexPricingFunctional.lean`, and under an arbitrary law
`Models/BlackScholes/StrikeConvexity.lean`).

A capped call with strikes `K₁ ≤ K₂` pays `min(max(S − K₁, 0), K₂ − K₁)`. Below `K₁` the payoff is
`0`; between `K₁` and `K₂` it tracks `S − K₁`; above `K₂` it is capped at `K₂ − K₁`. That is the
bull-call spread `max(S − K₁, 0) − max(S − K₂, 0)`, so a capped call is a long call at `K₁` and a
short call at `K₂` (`Contracts/Instruments/Options.lean` builds it that way).

## Main results

* `convexOn_call_payoff`: `K ↦ max(S − K, 0)` is convex.
* `antitone_call_payoff`: `K ↦ max(S − K, 0)` is antitone.
* `cappedCall_eq_bull_spread`: the capped call is the bull-call spread.

## References

* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], 11.2
* [R. C. Merton, *Theory of rational option pricing*][Merton1973]

## Tags

call payoff, strike convexity, capped call, bull call spread, payoff decomposition, static
replication, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

/-- The affine function `K ↦ a − K` is convex on `Set.univ`. Affine
functions are simultaneously convex and concave; the inequality holds
with equality. -/
lemma convexOn_sub_const_id (a : ℝ) :
    ConvexOn ℝ Set.univ (fun K : ℝ ↦ a - K) := by
  refine ⟨convex_univ, fun K₁ _ K₂ _ s t _ _ hst ↦ ?_⟩
  change a - (s • K₁ + t • K₂) ≤ s • (a - K₁) + t • (a - K₂)
  simp only [smul_eq_mul]
  -- Equality (affine functions are tight): `s·a + t·a = a` via `s + t = 1`.
  have h_sa_ta : s * a + t * a = a := by linear_combination a * hst
  linarith

/-- **Call payoff is convex in the strike**: `K ↦ max(S − K, 0)` is convex.

This is the structural spine of static option-price no-arbitrage relations.
Butterfly non-negativity and Breeden-Litzenberger PDF positivity are
discrete and infinitesimal consequences (respectively) of this single fact,
after passing through risk-neutral expectation. -/
lemma convexOn_call_payoff (S : ℝ) :
    ConvexOn ℝ Set.univ (fun K : ℝ ↦ max (S - K) 0) :=
  (convexOn_sub_const_id S).sup (convexOn_const (0 : ℝ) convex_univ)

/-- **Call payoff is antitone in the strike**: higher strikes pay less.

Equivalent to monotonicity of `max(·, 0)` composed with `K ↦ S − K` (which
is itself antitone). The single-line consequence of monotonicity of `max`. -/
lemma antitone_call_payoff (S : ℝ) :
    Antitone (fun K : ℝ ↦ max (S - K) 0) :=
  fun _ _ h ↦ max_le_max (by linarith) le_rfl


/-- **Capped call as a bull call spread**: for `K₁ ≤ K₂`,
`min(max(S − K₁, 0), K₂ − K₁) = max(S − K₁, 0) − max(S − K₂, 0)`. -/
lemma cappedCall_eq_bull_spread (S K₁ K₂ : ℝ) (h : K₁ ≤ K₂) :
    min (max (S - K₁) 0) (K₂ - K₁) =
      max (S - K₁) 0 - max (S - K₂) 0 := by
  by_cases h1 : S ≤ K₁
  · have e1 : max (S - K₁) 0 = 0 := max_eq_right (by linarith)
    have e2 : max (S - K₂) 0 = 0 := max_eq_right (by linarith)
    rw [e1, e2]
    rw [min_eq_left (by linarith : (0:ℝ) ≤ K₂ - K₁)]; ring
  push Not at h1
  by_cases h2 : S ≤ K₂
  · have e1 : max (S - K₁) 0 = S - K₁ := max_eq_left (by linarith)
    have e2 : max (S - K₂) 0 = 0 := max_eq_right (by linarith)
    rw [e1, e2]
    rw [min_eq_left (by linarith : S - K₁ ≤ K₂ - K₁)]; ring
  · push Not at h2
    have e1 : max (S - K₁) 0 = S - K₁ := max_eq_left (by linarith)
    have e2 : max (S - K₂) 0 = S - K₂ := max_eq_left (by linarith)
    rw [e1, e2]
    rw [min_eq_right (by linarith : K₂ - K₁ ≤ S - K₁)]; ring

end MathFin
