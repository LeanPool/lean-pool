/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace

/-!
# Measure domination from small-ball bounds

Besicovitch covering turns uniform small-ball estimates into domination of measures.
This is the last measure-theoretic step in the intended log-concave absolute-continuity
argument. It does not prove the needed uniform bound from log-concavity.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Metric Topology

namespace FunctionalInequalities.Probability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- A uniform finite bound on sufficiently small ball ratios implies domination on every
measurable set. The admissible radius may depend on the center. -/
theorem measure_le_smul_of_eventually_closedBall_le (μ m : Measure E)
    [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure m] (C : NNReal)
    (h : ∀ x : E, ∀ᶠ r : ℝ in 𝓝[>] 0,
      μ (closedBall x r) ≤ (C : ENNReal) * m (closedBall x r)) :
    μ ≤ (C : ENNReal) • m := by
  have : IsLocallyFiniteMeasure ((C : ENNReal) • m) := by
    change IsLocallyFiniteMeasure (C • m)
    infer_instance
  apply Measure.le_iff.mpr
  intro s _
  apply (Besicovitch.vitaliFamily μ).measure_le_of_frequently_le
    ((C : ENNReal) • m) Measure.AbsolutelyContinuous.rfl s
  intro x _
  apply (Besicovitch.tendsto_filterAt μ x).frequently
  exact (h x).mono (by intro r hr; simpa using hr) |>.frequently

/-- Small-ball domination supplies absolute continuity without assuming it in the covering
step. The Vitali family is built for the source measure itself. -/
theorem absolutelyContinuous_of_eventually_closedBall_le (μ m : Measure E)
    [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure m] (C : NNReal)
    (h : ∀ x : E, ∀ᶠ r : ℝ in 𝓝[>] 0,
      μ (closedBall x r) ≤ (C : ENNReal) * m (closedBall x r)) : μ ≪ m :=
  Measure.absolutelyContinuous_of_le_smul (measure_le_smul_of_eventually_closedBall_le μ m C h)

end FunctionalInequalities.Probability
