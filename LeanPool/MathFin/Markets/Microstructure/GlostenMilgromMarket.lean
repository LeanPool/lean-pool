/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Markets.Microstructure.GlostenMilgromCondExp
public import LeanPool.MathFin.Pricing.DiscreteMarket

/-!
# A quote process is priced by its own measure

A market maker who quotes the conditional expectation of the asset's value given the public
information `𝓖 n` (the Glosten–Milgrom zero-profit quote, `condExp_payoff_eq_quote` for one trade)
posts the price process `n ↦ P[V | 𝓖 n]`. This file reads that process as a market: it is the
discrete `Market` (`toMarket`) with the unit numéraire, and the measure `P` that defines the
quotes is a pricing measure of it, since a conditional expectation process is a `P`-martingale
(Mathlib's `martingale_condExp`).

## Main results

* `isPricingMeasure_toMarket_condExp`: for any probability measure `P` and filtration `𝓖`, `P`
  prices the market whose asset is `n ↦ P[V | 𝓖 n]`.

## Scope

The value `V` and the information `𝓖` are arbitrary; that the quotes of the Glosten–Milgrom
dealer along a sequence of trades are these conditional expectations is not shown here (one
trade is `condExp_payoff_eq_quote`).

## References

* [L. R. Glosten and P. R. Milgrom, *Bid, ask and transaction prices in a specialist market with
  heterogeneously informed traders*][GlostenMilgrom1985]

## Tags

Glosten–Milgrom model, market maker quotes, pricing measure, Doob martingale, conditional
expectation, MSC 91B26, MSC 60G42, JEL D82
-/

@[expose] public section

open MeasureTheory

namespace MathFin.Execution

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **The measure that defines the quotes prices them.** For a probability measure `P`, a
filtration `𝓖` and a value `V`, `P` is a pricing measure, at every horizon `T`, of the discrete
market whose asset is the quote process `n ↦ P[V | 𝓖 n]`: a conditional expectation process is a
`P`-martingale. -/
theorem isPricingMeasure_toMarket_condExp (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓖 : Filtration ℕ mΩ) (V : Ω → ℝ) (T : ℕ) :
    (Contracts.DiscreteMarket.toMarket P 𝓖 (fun n ↦ P[V | 𝓖 n]) T
      fun _ _ ↦ stronglyMeasurable_condExp).IsPricingMeasure T P :=
  Contracts.DiscreteMarket.isPricingMeasure_toMarket_of_isEMM
    (.of_martingale (martingale_condExp V 𝓖 P) .rfl .rfl T)

end MathFin.Execution
