/-
Copyright (c) 2026 Alfredo Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alfredo Garcia
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Markets.Microstructure.GlostenMilgrom
public import LeanPool.MathFin.Probability.Laws.FiniteWeights

/-!
# A model satisfying the Glosten-Milgrom hypotheses

`MathFin.Execution.spread_pos_of_model` quantifies over a probability space and
three events tied together by four equations. If nothing satisfies those
equations the theorem is vacuously true and says nothing — which is the same
failure mode the module it belongs to exists to warn about, one level up.

This file removes the doubt by exhibiting the model. Six outcomes: the value is
high or low, the arriving trader is informed or not, and an uninformed trader
tosses a coin.

| `i` | value | trader     | acts | mass           |
|-----|-------|------------|------|----------------|
| `0` | high  | informed   | buy  | `θp`           |
| `1` | high  | uninformed | buy  | `θ(1-p)/2`     |
| `2` | high  | uninformed | sell | `θ(1-p)/2`     |
| `3` | low   | informed   | sell | `(1-θ)p`       |
| `4` | low   | uninformed | buy  | `(1-θ)(1-p)/2` |
| `5` | low   | uninformed | sell | `(1-θ)(1-p)/2` |

The witness is symbolic: it works for *every* `0 < θ < 1` and `0 < p ≤ 1`, not
at one convenient point.

## Main definitions

* `gmWeight`: the masses of the six outcomes (value high or low, trader informed or not, and an
  uninformed trader's coin).
* `gmMeasure`: the measure on `Fin 6` with those masses.
* `gmHigh`, `gmBuy`, `gmInformed`: the events that the value is high, that the trader buys, and
  that the trader is informed.

## Main results

* `gm_buy_inter_inf`: an informed trader buys exactly when the value is high —
  on this space, a set identity.
* `gmMeasure_univ_eq_one`: the six masses add to one.
* `spread_pos_witness`: the spread is strictly positive, with no
  measure-theoretic hypothesis left in front of it.

## References

* [L. R. Glosten and P. R. Milgrom, *Bid, ask and transaction prices in a specialist market with
  heterogeneously informed traders*][GlostenMilgrom1985]

## Tags

Glosten–Milgrom model, bid–ask spread, adverse selection, finite probability space, informed trader,
market maker, MSC 91B26, JEL D82
-/

@[expose] public section

namespace MathFin.Execution

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The six outcome masses. -/
noncomputable def gmWeight (θ p : ℝ) : Fin 6 → ℝ :=
  ![θ * p, θ * (1 - p) / 2, θ * (1 - p) / 2,
    (1 - θ) * p, (1 - θ) * (1 - p) / 2, (1 - θ) * (1 - p) / 2]

/-- The model measure: the six masses on the six outcomes. -/
noncomputable def gmMeasure (θ p : ℝ) : Measure (Fin 6) :=
  Measure.ofWeights Finset.univ (gmWeight θ p)

/-- The value is high. -/
def gmHigh : Set (Fin 6) := {0, 1, 2}
/-- The arriving trader buys. -/
def gmBuy : Set (Fin 6) := {0, 1, 4}
/-- The arriving trader is informed. -/
def gmInformed : Set (Fin 6) := {0, 3}

/-- Every set's measure is the sum of the masses it contains. -/
theorem gmMeasure_apply (θ p : ℝ) (s : Set (Fin 6)) :
    gmMeasure θ p s
      = ∑ i, Set.indicator s (fun j => ENNReal.ofReal (gmWeight θ p j)) i := by
  have h : gmMeasure θ p
      = Measure.sum fun i => ENNReal.ofReal (gmWeight θ p i) • Measure.dirac i := by
    rw [gmMeasure, Measure.ofWeights, Measure.sum_fintype]
  rw [h, Measure.sum_apply _ MeasurableSet.of_discrete, tsum_fintype]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_apply, Measure.dirac_apply' i MeasurableSet.of_discrete, smul_eq_mul]
  by_cases h : i ∈ s <;> simp [h]

/-- On the parameter range that matters, every mass is nonnegative. -/
theorem gmWeight_nonneg {θ p : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∀ i, 0 ≤ gmWeight θ p i := by
  intro i; fin_cases i <;> simp [gmWeight] <;> nlinarith

/-- The measure of a set, as one real number. -/
theorem gmMeasure_eq_ofReal {θ p : ℝ} (hnn : ∀ i, 0 ≤ gmWeight θ p i) (s : Set (Fin 6)) :
    gmMeasure θ p s = ENNReal.ofReal (∑ i, Set.indicator s (gmWeight θ p) i) := by
  rw [gmMeasure_apply, ENNReal.ofReal_sum_of_nonneg]
  · refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i ∈ s <;> simp [hi]
  · intro i _; by_cases hi : i ∈ s <;> simp [hi, hnn i]

/-! ## The masses of the sets the model constrains -/

section Values
variable {θ p : ℝ} (hnn : ∀ i, 0 ≤ gmWeight θ p i)
include hnn

theorem gmMeasure_univ_eq_one : gmMeasure θ p Set.univ = 1 := by
  rw [gmMeasure_eq_ofReal hnn, show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
  congr 1
  simp [gmWeight, Fin.sum_univ_six]; ring

theorem gmMeasure_high_eq : gmMeasure θ p gmHigh = ENNReal.ofReal θ := by
  rw [gmMeasure_eq_ofReal hnn]; congr 1
  simp [gmHigh, gmWeight, Fin.sum_univ_six]; ring

theorem gmMeasure_high_compl_eq : gmMeasure θ p gmHighᶜ = ENNReal.ofReal (1 - θ) := by
  rw [gmMeasure_eq_ofReal hnn]; congr 1
  simp [gmHigh, gmWeight, Fin.sum_univ_six]; ring

theorem gmMeasure_high_inter_inf (hp0 : 0 ≤ p) :
    gmMeasure θ p (gmHigh ∩ gmInformed) = ENNReal.ofReal p * ENNReal.ofReal θ := by
  rw [gmMeasure_eq_ofReal hnn, ← ENNReal.ofReal_mul hp0]; congr 1
  simp [gmHigh, gmInformed, gmWeight, Fin.sum_univ_six]; ring

theorem gmMeasure_low_inter_inf (hp0 : 0 ≤ p) :
    gmMeasure θ p (gmHighᶜ ∩ gmInformed) = ENNReal.ofReal p * ENNReal.ofReal (1 - θ) := by
  rw [gmMeasure_eq_ofReal hnn, ← ENNReal.ofReal_mul hp0]; congr 1
  simp [gmHigh, gmInformed, gmWeight, Fin.sum_univ_six]; ring

theorem gmMeasure_uninformed_high :
    2 * gmMeasure θ p ((gmHigh ∩ gmBuy) \ gmInformed) = gmMeasure θ p (gmHigh \ gmInformed) := by
  rw [gmMeasure_eq_ofReal hnn, gmMeasure_eq_ofReal hnn,
    show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  simp [gmHigh, gmBuy, gmInformed, gmWeight, Fin.sum_univ_six]; ring

theorem gmMeasure_uninformed_low :
    2 * gmMeasure θ p ((gmHighᶜ ∩ gmBuy) \ gmInformed) = gmMeasure θ p (gmHighᶜ \ gmInformed) := by
  rw [gmMeasure_eq_ofReal hnn, gmMeasure_eq_ofReal hnn,
    show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  simp [gmHigh, gmBuy, gmInformed, gmWeight, Fin.sum_univ_six]; ring

end Values

/-- **An informed trader buys exactly when the value is high.** The one
behavioural primitive, and on this space it is a set identity. -/
theorem gm_buy_inter_inf : gmBuy ∩ gmInformed = gmHigh ∩ gmInformed := by
  ext i; fin_cases i <;> simp [gmBuy, gmInformed, gmHigh]

/-- The six masses add to one. -/
theorem gmMeasure_isProbabilityMeasure {θ p : ℝ} (hnn : ∀ i, 0 ≤ gmWeight θ p i) :
    IsProbabilityMeasure (gmMeasure θ p) :=
  ⟨gmMeasure_univ_eq_one hnn⟩

/-- **The model exists, so the theorem is not vacuous.** Every hypothesis of
`spread_pos_of_model` is discharged by the six-point space, for *every*
`0 < θ < 1` and `0 < p ≤ 1` — not merely at one lucky point. What is left is the
conclusion, with no measure-theoretic hypothesis in front of it: the ask strictly
exceeds the bid. -/
theorem spread_pos_witness {θ p VL VH : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hp0 : 0 < p) (hp1 : p ≤ 1) (hV : VL < VH) :
    0 < (∫ ω, payoff gmHigh VL VH ω ∂((gmMeasure θ p)[|gmBuy]))
      - (∫ ω, payoff gmHigh VL VH ω ∂((gmMeasure θ p)[|gmBuyᶜ])) := by
  have hnn := gmWeight_nonneg hθ0.le hθ1.le hp0.le hp1
  have := gmMeasure_isProbabilityMeasure hnn
  exact spread_pos_of_model (gmMeasure θ p) gmHigh gmBuy gmInformed
    MeasurableSet.of_discrete MeasurableSet.of_discrete MeasurableSet.of_discrete
    hθ0 hθ1 hp0 hV (gmMeasure_high_eq hnn) gm_buy_inter_inf
    (gmMeasure_high_inter_inf hnn hp0.le) (gmMeasure_low_inter_inf hnn hp0.le)
    (gmMeasure_uninformed_high hnn) (gmMeasure_uninformed_low hnn)

end MathFin.Execution
