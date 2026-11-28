/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.BlackScholes.StrikeConvexity

/-!
# Static spread no-arbitrage relations (bull-call, butterfly)

Two static no-arbitrage payoff inequalities at expiry, both expressing
*structural properties of the call payoff in the strike*:

* **Bull-call spread** `max(S − K₂, 0) ≤ max(S − K₁, 0)` for `K₁ ≤ K₂`:
  the payoff `K ↦ max(S − K, 0)` is *antitone* in `K`.
* **Butterfly spread** `0 ≤ max(S − K₁, 0) − 2 · max(S − (K₁+K₃)/2, 0) +
  max(S − K₃, 0)`: the payoff is *convex* in `K`, so its discrete
  second-difference at the midpoint is non-negative.

These are not two independent theorems; they are the *antitone* and *convex*
faces of `K ↦ max(S − K, 0)`. Both structural facts are recorded in
`StrikeConvexity.lean` (`antitone_call_payoff` and `convexOn_call_payoff`).

The same convexity, applied infinitesimally rather than discretely, yields
non-negativity of the second `K`-derivative of the European call price —
i.e. the Breeden-Litzenberger implied PDF.

## Main results

* `bull_call_spread_payoff_le`: for `K₁ ≤ K₂`, `max (S - K₂) 0 ≤ max (S - K₁) 0`.
* `butterfly_payoff_nonneg`: `0 ≤ max (S - K₁) 0 - 2 * max (S - (K₁ + K₃) / 2) 0 + max (S - K₃) 0`.
  Both are payoff inequalities at expiry, not statements about prices.

## References

* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], 11.5

## Tags

bull spread, butterfly spread, static arbitrage, call payoff, Breeden–Litzenberger, MSC 91G20,
JEL G13
-/

@[expose] public section

namespace MathFin

/-- **Bull-call spread payoff non-negativity**: for `K₁ ≤ K₂`,
`max(S − K₂, 0) ≤ max(S − K₁, 0)`. Antitone face of the call payoff in `K`. -/
lemma bull_call_spread_payoff_le (S K₁ K₂ : ℝ) (h : K₁ ≤ K₂) :
    max (S - K₂) 0 ≤ max (S - K₁) 0 :=
  antitone_call_payoff S h

/-- **Butterfly spread payoff non-negativity**: for `K₂ = (K₁ + K₃)/2`,
`0 ≤ max(S − K₁, 0) − 2 · max(S − (K₁+K₃)/2, 0) + max(S − K₃, 0)`.

The discrete second-difference of the convex function `K ↦ max(S − K, 0)` at
the midpoint of `K₁` and `K₃` is non-negative: this is Jensen's inequality
`f((K₁+K₃)/2) ≤ (f(K₁) + f(K₃))/2`, multiplied by 2 and rearranged. The
hypothesis `K₁ ≤ K₃` is retained for API stability but is not needed for
the inequality. -/
lemma butterfly_payoff_nonneg (S K₁ K₃ : ℝ) (_h : K₁ ≤ K₃) :
    0 ≤
      max (S - K₁) 0 -
        2 * max (S - (K₁ + K₃) / 2) 0 +
        max (S - K₃) 0 := by
  -- Convexity inequality at α = β = 1/2 (midpoint convex combination).
  have h_conv := (convexOn_call_payoff S).2 (Set.mem_univ K₁) (Set.mem_univ K₃)
    (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1/2:ℝ) + 1/2 = 1)
  simp only [smul_eq_mul] at h_conv
  rw [show (1/2 * K₁ + 1/2 * K₃ : ℝ) = (K₁ + K₃) / 2 from by ring] at h_conv
  -- h_conv: max(S − midpoint, 0) ≤ (1/2)·max(S−K₁, 0) + (1/2)·max(S−K₃, 0)
  -- Multiply by 2 and rearrange.
  linarith

end MathFin
