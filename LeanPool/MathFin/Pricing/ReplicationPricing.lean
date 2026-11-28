/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# A replicated claim is worth its initial wealth

The argument behind "complete ⟹ the pricing measure is unique", once. Fix a class `Gains` of
terminal gains (the terminal wealth of a self-financing strategy started from nothing) and call a
measure `Q` *gains-neutral* if every gain is `Q`-integrable with `Q`-mean zero. A gains-neutral
probability measure dominated by `P` prices a claim replicated `P`-almost surely, `H = x + G` with
`G ∈ Gains`, at its initial wealth `x` (`integral_eq_of_replicates`). If every event of a
σ-algebra `𝓖` has its indicator replicated, two gains-neutral measures then agree on `𝓖`
(`measure_eq_of_replicates`): both give the event the initial wealth of its replication.

It has two instances, which differ only in what makes the gains neutral:
* the discrete market (`IsEMM.measure_eq_of_isCompleteMarket`, `Pricing/FTAP/FTAP.lean`): the gains
  `martingaleTransform φ S T` are a `Q`-martingale started at `0` under any equivalent martingale
  measure;
* the Brownian market (`measure_eq_of_pricesGainsAtZero`, `Pricing/MarketCompleteness.lean`):
  the gains are the terminal Itô integrals `∫₀ᵀ φ dB`, centered under the reference measure, and
  neutrality under other measures is the hypothesis `PricesGainsAtZero`.

## Main results

* `integral_eq_of_replicates` — a gains-neutral probability measure `Q ≪ P` prices a replicated
  claim `H =ᵐ[P] x + G` at `x`.
* `measureReal_eq_of_replicates` — the indicator case: `Q A = x`.
* `measure_eq_of_replicates` — two gains-neutral probability measures `≪ P` agree on every event
  of `𝓖` whose indicator is replicated.

## References

* [J. M. Harrison and S. R. Pliska, *Martingales and stochastic integrals in the theory of
  continuous trading*][HarrisonPliska1981]
* [S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*][ShreveSCFII], Section
  5.4

## Tags

replication, law of one price, gains-neutral measure, unique pricing measure, complete market,
initial wealth, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **A replicated claim is worth its initial wealth.** If `Q` is a probability measure dominated
by `P`, the gain `G` is `Q`-integrable with `Q`-mean zero, and `H = x + G` `P`-almost surely, then
`∫ H dQ = x`: transport the almost-sure equality along `Q ≪ P`, then integrate. -/
theorem integral_eq_of_replicates {Q : Measure Ω} [IsProbabilityMeasure Q] (hQP : Q ≪ P)
    {H G : Ω → ℝ} {x : ℝ} (hG : Integrable G Q) (hG0 : ∫ ω, G ω ∂Q = 0)
    (hrep : H =ᵐ[P] fun ω ↦ x + G ω) : ∫ ω, H ω ∂Q = x := by
  rw [integral_congr_ae (hQP.ae_le hrep), integral_add (integrable_const x) hG, hG0,
    integral_const, probReal_univ, one_smul, add_zero]

/-- **A replicated event has probability its initial wealth.** The indicator case of
`integral_eq_of_replicates`: if `1_A = x + G` `P`-almost surely for a `Q`-neutral gain `G`, then
`Q A = x`. -/
theorem measureReal_eq_of_replicates {Q : Measure Ω} [IsProbabilityMeasure Q] (hQP : Q ≪ P)
    {A : Set Ω} (hA : MeasurableSet A) {G : Ω → ℝ} {x : ℝ} (hG : Integrable G Q)
    (hG0 : ∫ ω, G ω ∂Q = 0) (hrep : A.indicator (1 : Ω → ℝ) =ᵐ[P] fun ω ↦ x + G ω) :
    Q.real A = x := by
  rw [← integral_indicator_one hA]
  exact integral_eq_of_replicates hQP hG hG0 hrep

/-- **Replication determines the pricing measure.** Let `Gains` be a class of gains, and `Q₁`, `Q₂`
probability measures dominated by `P` under which every gain is integrable with mean zero. If the
indicator of every `𝓖`-measurable event is `P`-almost surely `x + G` for some `x` and `G ∈ Gains`
(the market is complete for `𝓖`), then `Q₁` and `Q₂` agree on `𝓖`: replicate the indicator of `A`;
both measures give `A` the initial wealth `x` (`measureReal_eq_of_replicates`). -/
theorem measure_eq_of_replicates {Q₁ Q₂ : Measure Ω} [IsProbabilityMeasure Q₁]
    [IsProbabilityMeasure Q₂] (h₁ : Q₁ ≪ P) (h₂ : Q₂ ≪ P) {Gains : Set (Ω → ℝ)}
    (hg₁ : ∀ G ∈ Gains, Integrable G Q₁ ∧ ∫ ω, G ω ∂Q₁ = 0)
    (hg₂ : ∀ G ∈ Gains, Integrable G Q₂ ∧ ∫ ω, G ω ∂Q₂ = 0) {𝓖 : MeasurableSpace Ω}
    (h𝓖 : 𝓖 ≤ mΩ)
    (hcomplete : ∀ A, MeasurableSet[𝓖] A →
      ∃ x, ∃ G ∈ Gains, A.indicator (1 : Ω → ℝ) =ᵐ[P] fun ω ↦ x + G ω)
    {A : Set Ω} (hA : MeasurableSet[𝓖] A) : Q₁ A = Q₂ A := by
  obtain ⟨x, G, hG, hrep⟩ := hcomplete A hA
  refine (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 ?_
  exact (measureReal_eq_of_replicates h₁ (h𝓖 _ hA) (hg₁ G hG).1 (hg₁ G hG).2 hrep).trans
    (measureReal_eq_of_replicates h₂ (h𝓖 _ hA) (hg₂ G hG).1 (hg₂ G hG).2 hrep).symm

end MathFin
