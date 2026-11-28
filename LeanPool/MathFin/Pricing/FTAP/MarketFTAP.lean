/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Pricing.ContinuousMarket
public import LeanPool.MathFin.Pricing.DiscreteMarket

/-!
# The fundamental theorem of asset pricing for a market

No arbitrage as a property of a `Market` (`Market.NoArbitrage`) and the fundamental theorem stated
about markets: no arbitrage if and only if there is a pricing measure.

A market trades at a grid of dates `t 0 ≤ t 1 ≤ ⋯ ≤ t N`. Its **no arbitrage on the grid** is the
library's `NoArbitrage` (`Pricing/FTAP/FTAP.lean`) of the deflated price sampled along the grid,
for the sampled filtration `n ↦ 𝓕 (t n)`: no bounded predictable strategy turns zero wealth into
a `P`-almost surely non-negative gain that is not almost surely zero. The market **traded on the
grid** (`Market.onGrid`) is the same deflated asset quoted in numéraire units, constant between
the dates; its pricing measures are the measures that agree on the information at the last date
with an equivalent martingale measure of the sampled price (`isPricingMeasure_toMarket_iff`).

* A pricing measure of the market up to a horizon rules out arbitrage on every grid inside the
  horizon (`Market.IsPricingMeasure.noArbitrage`), whatever the market: the continuous-time
  martingale property is sampled (`IsEMM.sampled`).
* On a finite sample space charged everywhere by `P`, the converse holds
  (`Market.noArbitrage_iff_exists_isPricingMeasure_of_finite`, Harrison–Pliska through
  `ftap_discrete`): no arbitrage on the grid exists exactly when the market traded on the grid has
  a pricing measure.
* On a general probability space the same equivalence holds **assuming
  `ConditionalOnePeriodFTAP`**, which is not proved in this library
  (`Market.noArbitrage_iff_exists_isPricingMeasure`, Dalang–Morton–Willinger through
  `DalangMortonWillinger.lean`). The unconditional statement is the frontier node `thm:dmw-ftap`.

The bare-process theorems (`ftap_discrete`, `noArbitrage_iff_exists_isEMM`) are what these are
proved from; this page is the statement about markets.

## Main definitions

* `Market.NoArbitrage`: no arbitrage for trading at the dates of a monotone grid.
* `Market.onGrid`: the market traded at the dates of a grid, in numéraire units.

## Main results

* `Market.IsPricingMeasure.noArbitrage`: a pricing measure rules out arbitrage on every grid
  inside its horizon.
* `Market.noArbitrage_iff_exists_isPricingMeasure_of_finite`: the fundamental theorem on a finite
  sample space.
* `Market.noArbitrage_iff_exists_isPricingMeasure`: the fundamental theorem, assuming the
  conditional one-period FTAP.

## References

* [J. M. Harrison and S. R. Pliska, *Martingales and stochastic integrals in the theory of
  continuous trading*][HarrisonPliska1981]
* [H. Föllmer and A. Schied, *Stochastic Finance: An Introduction in Discrete Time*][FollmerSchied],
  §5.2
* [F. Delbaen and W. Schachermayer, *The Mathematics of Arbitrage*][DelbaenSchachermayer]

## Tags

fundamental theorem of asset pricing, no arbitrage, pricing measure, market, Harrison–Pliska,
Dalang–Morton–Willinger, JEL G13, MSC 91G20
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace MathFin.Market

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **No arbitrage on a grid.** A one-asset market has no arbitrage when trading at the dates
`t 0 ≤ ⋯ ≤ t N` if the deflated price sampled at those dates has none for the sampled filtration:
no bounded predictable strategy turns zero initial wealth into a `P`-almost surely non-negative
gain that is not almost surely zero. -/
def NoArbitrage (M : Market Unit Ω) {t : ℕ → ℝ≥0} (ht : Monotone t) (N : ℕ) : Prop :=
  _root_.MathFin.NoArbitrage (ContinuousMarket.sampledFiltration M.𝓕 ht) M.P
    (fun n ↦ M.deflated () (t n)) N

/-- **The market traded on a grid**: the deflated asset sampled at the dates `t 0 ≤ ⋯ ≤ t N`,
constant between them and frozen at `t N`, for the sampled filtration, with the unit numéraire
(`DiscreteMarket.toMarket`). -/
noncomputable def onGrid (M : Market Unit Ω) {t : ℕ → ℝ≥0} (ht : Monotone t) (N : ℕ) :
    Market Unit Ω :=
  Contracts.DiscreteMarket.toMarket M.P (ContinuousMarket.sampledFiltration M.𝓕 ht)
    (fun n ↦ M.deflated () (t n)) N fun n _ ↦ M.stronglyAdapted_deflated () (t n)

variable {M : Market Unit Ω} {t : ℕ → ℝ≥0} (ht : Monotone t) {N : ℕ}

/-- **A pricing measure rules out arbitrage on every grid inside its horizon.** It agrees on the
information at the horizon with an equivalent martingale measure of the deflated asset
(`IsPricingMeasure.exists_isEquivProbMeasure`), whose sampling along the grid is one for the
sampled price (`IsEMM.sampled`), which rules out arbitrage (`IsEMM.noArbitrage`). -/
theorem IsPricingMeasure.noArbitrage [IsFiniteMeasure M.P] {T : ℝ≥0} {Q : Measure Ω}
    (hQ : M.IsPricingMeasure T Q) (hT : t N ≤ T) : M.NoArbitrage ht N := by
  obtain ⟨Q', hQ'P, hQ', -⟩ := hQ.exists_isEquivProbMeasure
  exact ((hQ'.isEMM hQ'P ()).sampled ht N hT).noArbitrage

/-- **The fundamental theorem of asset pricing for a market on a finite sample space**
(Harrison–Pliska): when `P` charges every state, a one-asset market has no arbitrage on the grid
exactly when the market traded on the grid has a pricing measure. This is
`noArbitrage_iff_exists_isPricingMeasure_of_finite` for the sampled deflated price. -/
theorem noArbitrage_iff_exists_isPricingMeasure_of_finite [Finite Ω] [Nonempty Ω]
    [MeasurableSingletonClass Ω] [IsFiniteMeasure M.P] (hP : ∀ ω, 0 < M.P {ω}) :
    M.NoArbitrage ht N ↔ ∃ Q, (M.onGrid ht N).IsPricingMeasure N Q :=
  Contracts.DiscreteMarket.noArbitrage_iff_exists_isPricingMeasure_of_finite
    (fun n ↦ M.stronglyAdapted_deflated () (t n)) hP

/-- **The fundamental theorem of asset pricing for a market, assuming the conditional one-period
FTAP** (Dalang–Morton–Willinger): on a probability space, for a deflated price integrable at the
dates of the grid, if `ConditionalOnePeriodFTAP` holds (a hypothesis, **not proved** in this
library: see `DalangMortonWillinger.lean`), no arbitrage on the grid is equivalent to a pricing
measure of the market traded on the grid. Only the forward direction uses the hypothesis. -/
theorem noArbitrage_iff_exists_isPricingMeasure [IsProbabilityMeasure M.P]
    (hint : ∀ n ≤ N, Integrable (M.deflated () (t n)) M.P)
    (hcond : ConditionalOnePeriodFTAP (ContinuousMarket.sampledFiltration M.𝓕 ht) M.P
      (fun n ↦ M.deflated () (t n)) N) :
    M.NoArbitrage ht N ↔ ∃ Q, (M.onGrid ht N).IsPricingMeasure N Q :=
  Contracts.DiscreteMarket.noArbitrage_iff_exists_isPricingMeasure
    (fun n _ ↦ M.stronglyAdapted_deflated () (t n)) hint hcond

end MathFin.Market
