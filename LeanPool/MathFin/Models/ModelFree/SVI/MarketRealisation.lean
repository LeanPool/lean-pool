/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.ModelFree.MarketCallPrice
public import LeanPool.MathFin.Models.ModelFree.RoperConverse
public import LeanPool.MathFin.Models.ModelFree.SVI.TailCondition

/-!
# The SVI smile and the market: butterfly-free exactly when realised

The static fundamental theorem meets the SVI sign formula in both directions. Forward
(`Market.IsPricingMeasure.isNormalizedCallPrice`): if the calls of a market with a pricing
measure, in units of the forward, are the SVI-smiled Black prices, and the parameters are
admissible, then `butterflyFreeFormula` holds. Converse (`exists_market_of_isNormalizedCallPrice`,
Roper's converse): a butterfly-free slice is the call price function, at maturity one, of a market
with unit numéraire, a nonnegative asset of forward one and a pricing measure.

## Main results

* `SVI.butterflyFreeFormula_of_isPricingMeasure`: a pricing measure whose normalised calls are the
  SVI smile forces the finite sign formula `butterflyFreeFormula`.
* `SVI.exists_market_of_butterflyFreeFormula`: a butterfly-free slice is the call price function
  of a market.

## References

* [Gatheral and Jacquier, *Arbitrage-free SVI volatility surfaces*][GatheralJacquier2014], Lemma 2.2
* [Roper, *Arbitrage free implied volatility surfaces*][Roper2010], Theorem 2.1

## Tags

SVI smile, pricing measure, butterfly arbitrage, no static arbitrage, MSC 91G20, JEL G13
-/

@[expose] public section

open MeasureTheory MathFin.Contracts
open scoped NNReal

namespace MathFin.SVI

/-- **A market that prices the SVI smile makes the slice butterfly-free.** In a market with unit
numéraire and a positive asset, priced at `T` by `Q`, if the calls at the strikes `k F`, in units
of the forward `F`, have the SVI-smiled Black price at every `k > 0`, and the parameters satisfy
`σ ≥ 0`, `b ≥ 0`, `ρ² ≤ 1` with positive variance everywhere, then `butterflyFreeFormula` holds:
the call price function is convex and satisfies the tail condition. -/
theorem butterflyFreeFormula_of_isPricingMeasure {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {M : Market Unit Ω} {T : ℝ≥0} {Q : Measure Ω} {p : Params}
    (hp : 0 ≤ p.sigma ∧ 0 ≤ p.b ∧ 0 ≤ 1 - p.rho ^ 2 ∧ ∀ k, 0 < variance p k)
    (hQ : M.IsPricingMeasure T Q) (hN : ∀ t ω, M.numeraire t ω = 1)
    (hpos : ∀ ω, 0 < M.asset () T ω) {F : ℝ} (hF : F = M.price Q (.pay T (.obs () T)))
    (hsmile : ∀ k > 0, M.price Q (europeanCall (k * F) T) / F = bsSmile p k) :
    butterflyFreeFormula.eval p = true :=
  (butterflyFreeFormula_iff_isNormalizedCallPrice p).2
    ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2,
      (hQ.isNormalizedCallPrice hN hpos hF).of_eqOn fun k hk ↦ hsmile k hk⟩

/-- **A butterfly-free SVI slice is the call price function of a market.** If the raw SVI
parameters satisfy `butterflyFreeFormula`, there is a market with unit numéraire, a nonnegative
asset of forward one at maturity one and a pricing measure, in which the call at every strike
`k > 0` is worth the SVI-smiled Black call `bsSmile p k`: the sign formula makes `bsSmile p` a
normalised call price function (`butterflyFreeFormula_iff_isNormalizedCallPrice`), and Roper's
converse realises it. -/
theorem exists_market_of_butterflyFreeFormula {p : Params}
    (h : butterflyFreeFormula.eval p = true) :
    ∃ (M : Market Unit ℝ) (Q : Measure ℝ), (∀ t ω, M.numeraire t ω = 1) ∧
      (∀ ω, 0 ≤ M.asset () 1 ω) ∧ M.IsPricingMeasure 1 Q ∧
      M.price Q (.pay 1 (.obs () 1)) = 1 ∧ ∀ k > 0, M.price Q (europeanCall k 1) = bsSmile p k :=
  exists_market_of_isNormalizedCallPrice
    ((butterflyFreeFormula_iff_isNormalizedCallPrice p).1 h).2.2.2.2

end MathFin.SVI
