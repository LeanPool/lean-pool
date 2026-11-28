/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Pricing.StatePrices

/-!
# Core quant-finance results derived from no-arbitrage (first principles)

This file derives the canonical static no-arbitrage relations — **put-call
parity** and the **forward price** — from a single structural object: a
non-negative linear pricing functional on payoffs.

The pattern: a "market" is parameterised by

* a finite state space `s : Finset ι`,
* non-negative state prices `q : ι → ℝ` (`hq : 0 ≤ q i`),
* terminal asset values `S : ι → ℝ`,

with two structural constraints:

* **Bond pricing**: `∑ q i = DF`, where `DF` is the time-0 price of a
  contract paying `1` at maturity in every state.
* **Stock pricing**: `∑ q i · S i = S_0`, where `S_0` is the time-0 spot
  price of the asset.

A general claim with payoff `g : ι → ℝ` has time-0 price `Λ(g) := statePricePricing s q g`
(`Pricing/StatePrices.lean`, `∑ q i · g i`). This `Λ` is a non-negative linear
functional, and its linearity lemmas (`statePricePricing_add`, `_smul`, `_const`) are what the
derivations below use. The state prices are an EMM scaled by the discount factor: the bridge
`exists_statePrices_of_hasEMM` (`Pricing/FTAP/FTAPMultiState.lean`) produces `q` with the bond
and stock constraints from `HasEMMMultiState`.

## Why this is "first principles"

The pre-existing `bsP_eq_bsV` (in `Models.BlackScholes.PutGreeks`) is an *algebraic*
verification: starting from the closed forms `bsV` and `bsP`, prove they
differ by `S - K · e^{-rτ}`. The proof is `unfold` + `linear_combination`
on the gaussian-CDF identity `Φ(x) + Φ(-x) = 1`.

The *first-principles* version below — `putCall_parity_from_no_arbitrage` —
makes no reference to `bsV`, `bsP`, the BS formula, or any closed form. It
says: whenever a market admits a non-negative linear pricing functional
with the bond and stock constraints, *any* call and put prices satisfy
parity. The proof is two lines:

1. Pointwise: `max(S - K, 0) - max(K - S, 0) = S - K`.
2. Linearity of `Λ`: `Λ(C-payoff) - Λ(P-payoff) = Λ(S - K) = S_0 - K · DF`.

The same template gives the forward price `F = S_0 / DF`.

## Main results

* `putCall_parity_from_no_arbitrage`: the parity derivation.
* `forward_price_from_no_arbitrage`: the forward price characterisation.

## Tags

put–call parity, forward price, state prices, linear pricing functional,
static no-arbitrage relations, cost of carry, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open Finset

/-- **Put-call parity from no-arbitrage** (first-principles derivation).

In a finite-state market with non-negative state prices `q : ι → ℝ`,
terminal asset values `S : ι → ℝ`, discount factor `DF = ∑ q i`, and spot
price `S_0 = statePricePricing s q S`, the call price
`C(K) = statePricePricing s q (max(S − K, 0))` and the put price
`P(K) = statePricePricing s q (max(K − S, 0))` satisfy

  `C(K) − P(K) = S_0 − K · DF`.

The proof has *no reference to the Black-Scholes formula*. It uses only:
* linearity of the pricing functional `statePricePricing s q`,
* the pointwise payoff identity `max(S - K, 0) - max(K - S, 0) = S - K`
  (`max_zero_sub_max_neg_zero_eq_self`),
* the bond and stock pricing constraints.

Specialisation to the BS model recovers `bsP_eq_bsV` (currently proved
algebraically); the algebraic proof there can now be seen as
"the BS closed forms are realised by some such pricing functional." -/
theorem putCall_parity_from_no_arbitrage
    {ι : Type*} (s : Finset ι) (q : ι → ℝ) (S : ι → ℝ)
    (DF S₀ K : ℝ)
    (h_bond : ∑ i ∈ s, q i = DF)
    (h_stock : statePricePricing s q S = S₀) :
    statePricePricing s q (fun i ↦ max (S i - K) 0)
      - statePricePricing s q (fun i ↦ max (K - S i) 0) = S₀ - K * DF := by
  -- pointwise: `max(S i − K, 0) + (−1) · max(K − S i, 0) = S i + (−K)`
  have h_payoff : (fun i ↦ max (S i - K) 0 + (-1) * max (K - S i) 0) = fun i ↦ S i + (-K) :=
    funext fun i ↦ by
      have h := max_zero_sub_max_neg_zero_eq_self (S i - K)
      rw [show -(S i - K) = K - S i from by ring] at h
      linarith
  calc statePricePricing s q (fun i ↦ max (S i - K) 0)
        - statePricePricing s q (fun i ↦ max (K - S i) 0)
      = statePricePricing s q (fun i ↦ max (S i - K) 0 + (-1) * max (K - S i) 0) := by
        rw [statePricePricing_add, statePricePricing_smul]; ring
    _ = statePricePricing s q (fun i ↦ S i + (-K)) := by rw [h_payoff]
    _ = S₀ - K * DF := by
        rw [statePricePricing_add, statePricePricing_const, h_stock, h_bond]; ring

/-- **Forward price from no-arbitrage** (first-principles derivation).

The fair forward price `F` — the strike at which the forward contract
with terminal payoff `S_T − F` has zero time-0 price — is

  `F = S_0 / DF`.

With continuous compounding (`DF = e^{−rT}`), this is the classical
`F = S_0 · e^{rT}` cash-and-carry formula.

The proof: by linearity, `Λ(S_T − F) = Λ(S_T) − F · Λ(1) = S_0 − F · DF`.
Setting this equal to zero and solving gives `F = S_0 / DF`. -/
theorem forward_price_from_no_arbitrage
    {ι : Type*} (s : Finset ι) (q : ι → ℝ) (S : ι → ℝ)
    (DF S₀ F : ℝ) (hDF : DF ≠ 0)
    (h_bond : ∑ i ∈ s, q i = DF)
    (h_stock : statePricePricing s q S = S₀) :
    statePricePricing s q (fun i ↦ S i - F) = 0 ↔ F = S₀ / DF := by
  -- Λ(S - F) = Λ(S) - F · Λ(1) = S_0 - F · DF.
  have h_eval : statePricePricing s q (fun i ↦ S i - F) = S₀ - F * DF := by
    rw [show (fun i ↦ S i - F) = fun i ↦ S i + (-F) from funext fun i ↦ sub_eq_add_neg _ _,
      statePricePricing_add, statePricePricing_const, h_stock, h_bond]
    ring
  rw [h_eval]
  constructor
  · intro h
    have : F * DF = S₀ := by linarith
    field_simp
    linarith
  · intro hF
    rw [hF]; field_simp; ring

/-- **Forward price (closed form)**: the unique fair forward is `F = S_0 / DF`. -/
theorem forward_price_eq_spot_div_discount
    {ι : Type*} (s : Finset ι) (q : ι → ℝ) (S : ι → ℝ)
    (DF S₀ : ℝ) (hDF : DF ≠ 0)
    (h_bond : ∑ i ∈ s, q i = DF)
    (h_stock : statePricePricing s q S = S₀) :
    ∃! F : ℝ, statePricePricing s q (fun i ↦ S i - F) = 0 := by
  refine ⟨S₀ / DF, ?_, ?_⟩
  · exact (forward_price_from_no_arbitrage s q S DF S₀ (S₀ / DF) hDF h_bond h_stock).mpr rfl
  · intro F hF
    exact (forward_price_from_no_arbitrage s q S DF S₀ F hDF h_bond h_stock).mp hF

end MathFin
