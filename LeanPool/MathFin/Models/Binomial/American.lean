/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Binomial.PathMeasure

/-!
# American option pricing in the binomial tree

For a binomial tree with up-factor `u`, down-factor `d`, per-step rate `r`,
under the no-arbitrage condition `d < e^r < u`, an American option with
intrinsic payoff `g : ℝ → ℝ` (e.g. `S ↦ max(S − K, 0)` for a call) has price

  `V_n(S) = max(g(S), e^{-r} · (p · V_{n-1}(uS) + (1 − p) · V_{n-1}(dS)))`

with `V_0(S) = g(S)`, where `p = crrUpProb u d r`. `n` counts steps remaining.

This is the exercise-everywhere case of the tree's one recursion `bermudanPrice`
(`Models/Binomial/Model.lean`); its dominance and supermartingale clauses
(`le_bermudanPrice`, `bermudanPrice_supermartingale`), its Snell-envelope characterization
(`Models/Binomial/SnellEnvelope.lean`) and its monotonicity in the exercise set, hence the
European ≤ American ordering (`Models/Binomial/Bermudan.lean`), all apply to it.

This file defines `americanPrice`, with the one-step Bellman equation `americanPrice_succ`, and
identifies it with the Snell envelope. Under the risk-neutral coin flips `coinFlipMeasure q`, with
`q = crrUpProb u d ρ`, the price is the time-`0` value of the library's Snell envelope
`snellEnvelope` (`Probability/Discrete/SnellEnvelope.lean`, Mathlib's conditional expectation on
the flip filtration) of the discounted intrinsic value `e^{−ρn} g(Sₙ)` along the spot path, with
every date an exercise date: the exercise-everywhere case of
`snellEnvelope_discounted_bermudanPrice` at time `0`.

Not proved here: the envelope as a supremum over stopping times, or any statement about the
price at a later time.

## Main definitions

* `americanPrice`: the American option price in the binomial tree, the Bellman recursion taking
  at each step the larger of the intrinsic payoff and the discounted risk-neutral continuation.

## Main results

* `americanPrice_zero`: with no steps remaining, the price is the intrinsic payoff `g S`.
* `americanPrice_succ`: one-step Bellman equation `V_{n+1}(S) = max(g(S), continuation)`.
* `americanPrice_eq_snellEnvelope`: almost surely under `coinFlipMeasure q`, the Snell envelope at
  time `0` of the discounted intrinsic value is `americanPrice u d ρ g N S₀`.

## References

* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], 21.5
* [S. E. Shreve, *Stochastic Calculus for Finance I: The Binomial Asset Pricing Model*][ShreveSCFI],
  4.4

## Tags

American option, early exercise, Bellman equation, binomial tree, dynamic programming,
optimal exercise, Snell envelope, optimal stopping, MSC 91G20, MSC 49L20, MSC 60G40, JEL G13
-/

@[expose] public section

namespace MathFin

open Real MeasureTheory
open scoped NNReal

/-- American option price in the binomial tree: the Bellman recursion taking, at each
step, the maximum of immediate exercise (`g S`) and the discounted expected continuation,
i.e. `bermudanPrice` with early exercise at every step. `n` counts steps remaining; `g` is
the intrinsic payoff function. -/
noncomputable def americanPrice (u d r : ℝ) (g : ℝ → ℝ) : ℕ → ℝ → ℝ :=
  bermudanPrice Set.univ u d r g

/-- At maturity (`n = 0`), the American price equals the intrinsic payoff. -/
@[simp]
lemma americanPrice_zero (u d r : ℝ) (g : ℝ → ℝ) (S : ℝ) :
    americanPrice u d r g 0 S = g S := rfl

/-- One-step Bellman: `V_{n+1}(S) = max(g(S), one-period continuation)`. -/
lemma americanPrice_succ (u d r : ℝ) (g : ℝ → ℝ) (n : ℕ) (S : ℝ) :
    americanPrice u d r g (n + 1) S = max (g S)
      (binomialOptionPriceOnePeriod u d r
        (americanPrice u d r g n (S * u))
        (americanPrice u d r g n (S * d))) :=
  bermudanPrice_succ_of_mem (Set.mem_univ _) u d r g S

/-- **The binomial American price is the Snell envelope.** Under the risk-neutral coin flips
(`crrUpProb u d ρ = q`), the Snell envelope of the discounted intrinsic value `e^{−ρn} g(Sₙ)`
along the spot path, for the flip filtration, horizon `N` and exercise at every date, is at time
`0` almost surely `americanPrice u d ρ g N S₀`. -/
theorem americanPrice_eq_snellEnvelope {u d ρ : ℝ} {q : ℝ≥0} (hq : q ≤ 1)
    (hqcrr : crrUpProb u d ρ = q) (g : ℝ → ℝ) (S₀ : ℝ) (N : ℕ) :
    ∀ᵐ ω ∂coinFlipMeasure q hq,
      snellEnvelope (coinFlipMeasure q hq) flipFiltration Set.univ
        (fun n ω ↦ Real.exp (-ρ * n) * g (spotPath S₀ u d n ω)) N 0 ω
      = americanPrice u d ρ g N S₀ := by
  have h := snellEnvelope_discounted_bermudanPrice (E := Set.univ) hq u d ρ g S₀ hqcrr
    (N := N) (k := 0) (Nat.zero_le N)
  simp only [Set.mem_univ, Set.ofPred_true] at h
  filter_upwards [h] with ω hω
  rw [hω]
  simp [americanPrice, spotPath]

end MathFin
