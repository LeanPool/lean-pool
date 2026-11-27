/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Sum
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Actual gluing of a countable compatible family of chart measures

The measure is a countable sum over disjointed chart patches. Its
restriction to every patch is proved equal to the original chart
measure. This is a measure construction, not a field containing a
postulated global induced volume.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X]

/-- Glued chart measure given by `Measure.sum (fun n => (μ n).restrict (disjointed U n))`. -/
noncomputable def gluedChartMeasure (U : ℕ → Set X) (μ : ℕ → Measure X) : Measure X :=
  Measure.sum (fun n => (μ n).restrict (disjointed U n))

theorem gluedChartMeasure_restrict_patch (U : ℕ → Set X) (μ : ℕ → Measure X)
    (hU : ∀ n, MeasurableSet (U n)) (hsupport : ∀ n, (μ n).restrict (U n) = μ n)
    (hcompat : ∀ i j, (μ i).restrict (U j) = (μ j).restrict (U i)) (j : ℕ) :
    (gluedChartMeasure U μ).restrict (U j) = μ j := by
  have hD : ∀ n, MeasurableSet (disjointed U n) := fun n => MeasurableSet.disjointed hU n
  have hterm (n : ℕ) : ((μ n).restrict (disjointed U n)).restrict (U j) =
      (μ j).restrict (disjointed U n) := by
    rw [Measure.restrict_restrict (hU j), inter_comm,
      ← Measure.restrict_restrict (hD n), hcompat n j,
      Measure.restrict_restrict_of_subset (disjointed_subset U n)]
  rw [gluedChartMeasure, Measure.restrict_sum _ (hU j)]
  simp_rw [hterm]
  rw [← Measure.restrict_iUnion (disjoint_disjointed U) hD, iUnion_disjointed]
  calc
    (μ j).restrict (⋃ n, U n) = ((μ j).restrict (U j)).restrict (⋃ n, U n) := by
      rw [hsupport j]
    _ = μ j := by
      rw [Measure.restrict_restrict (MeasurableSet.iUnion hU),
        inter_eq_right.mpr (subset_iUnion U j), hsupport j]

theorem gluedChartMeasure_supported_union (U : ℕ → Set X) (μ : ℕ → Measure X)
    (hU : ∀ n, MeasurableSet (U n)) :
    (gluedChartMeasure U μ).restrict (⋃ n, U n) = gluedChartMeasure U μ := by
  rw [gluedChartMeasure, Measure.restrict_sum _ (MeasurableSet.iUnion hU)]
  congr 1
  funext n
  rw [Measure.restrict_restrict (MeasurableSet.iUnion hU),
    inter_eq_right.mpr ((disjointed_subset U n).trans (subset_iUnion U n))]

theorem gluedChartMeasure_unique (U : ℕ → Set X) (μ : ℕ → Measure X)
    (hU : ∀ n, MeasurableSet (U n)) (hsupport : ∀ n, (μ n).restrict (U n) = μ n)
    (hcompat : ∀ i j, (μ i).restrict (U j) = (μ j).restrict (U i))
    {ν : Measure X} (hνsupport : ν.restrict (⋃ n, U n) = ν)
    (hν : ∀ n, ν.restrict (U n) = μ n) : ν = gluedChartMeasure U μ := by
  have h : ν.restrict (⋃ n, U n) = (gluedChartMeasure U μ).restrict (⋃ n, U n) :=
    Measure.restrict_iUnion_congr.mpr (fun n => (hν n).trans
      (gluedChartMeasure_restrict_patch U μ hU hsupport hcompat n).symm)
  simpa only [hνsupport, gluedChartMeasure_supported_union U μ hU] using h

end VacuumBellSeparation
