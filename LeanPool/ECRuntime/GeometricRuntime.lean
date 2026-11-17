/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.StochasticDomination
public import Mathlib.Probability.Distributions.Geometric

/-!
# Geometric Runtime

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open MeasureTheory

namespace ECRuntime

/--
Canonical geometric failure-count law supplied by mathlib.  Under parameter `p`, a
sample `n` records `n` failures before the first success.
-/
noncomputable def geometricFailureMeasure (p : unitInterval) : Measure ℕ :=
  ProbabilityTheory.geometricMeasure p

instance instIsProbabilityMeasureGeometricFailureMeasure (p : unitInterval) :
    IsProbabilityMeasure (geometricFailureMeasure p) := by
  unfold geometricFailureMeasure
  infer_instance

/-- The EC waiting-time convention: one plus the number of failures before success. -/
def geometricWaitingTime (n : ℕ) : ENNReal :=
  (n + 1 : ℕ)

/-- The one-based geometric waiting time is measurable on the discrete natural space. -/
theorem measurable_geometricWaitingTime : Measurable geometricWaitingTime := by
  exact measurable_of_countable geometricWaitingTime

/-- The geometric waiting-time law on `ENNReal`, obtained by pushing the failure-count law
forward. -/
noncomputable def geometricWaitingMeasure (p : unitInterval) : Measure ENNReal :=
  (geometricFailureMeasure p).map geometricWaitingTime

instance instIsProbabilityMeasureGeometricWaitingMeasure (p : unitInterval) :
    IsProbabilityMeasure (geometricWaitingMeasure p) := by
  unfold geometricWaitingMeasure
  exact (Measure.isProbabilityMeasure_map_iff
    measurable_geometricWaitingTime.aemeasurable).mpr inferInstance

@[simp] theorem geometricWaitingTime_zero :
    geometricWaitingTime 0 = 1 := by
  simp [geometricWaitingTime]

/-- The point mass of the canonical geometric failure-count law. -/
theorem geometricFailureMeasure_singleton
    {p : unitInterval} (hp : p ≠ 0) (n : ℕ) :
    geometricFailureMeasure p {n} =
      ENNReal.ofReal ((1 - (p : ℝ)) ^ n * (p : ℝ)) := by
  simpa [geometricFailureMeasure] using
    (ProbabilityTheory.geometricMeasure_singleton hp n)

/-- The geometric survival profile appropriate for a one-based waiting time. -/
noncomputable def geometricSurvival (p : unitInterval) (k : ℕ) : ENNReal :=
  ENNReal.ofReal ((1 - (p : ℝ)) ^ k)

@[simp] theorem geometricSurvival_zero (p : unitInterval) :
    geometricSurvival p 0 = 1 := by
  simp [geometricSurvival]

/--
A distribution-free geometric tail certificate.  It says that the runtime tail above
integer threshold `k` is at most the survival probability `(1-p)^k` of a geometric
waiting time with success probability `p`.

The next Stage-26 step will identify this profile with the tails of
`geometricWaitingTime` under `geometricFailureMeasure`, and then use independent
products of these laws in the domination version of the fitness-level theorem.
-/
def HasGeometricTailBound
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ENNReal) (p : unitInterval) : Prop :=
  ∀ k : ℕ,
    runtimeTailMass μ X (k : ENNReal) ≤ geometricSurvival p k

/-- A geometric tail certificate is preserved when the runtime decreases pointwise. -/
theorem hasGeometricTailBound_of_pointwise_le
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {X Y : Ω → ENNReal} (p : unitInterval)
    (hXY : ∀ ω, X ω ≤ Y ω)
    (hY : HasGeometricTailBound μ Y p) :
    HasGeometricTailBound μ X p := by
  intro k
  calc
    runtimeTailMass μ X (k : ENNReal) ≤
        runtimeTailMass μ Y (k : ENNReal) := by
      unfold runtimeTailMass
      exact measure_mono
        (runtimeTailEvent_mono_of_pointwise_le hXY (k : ENNReal))
    _ ≤ geometricSurvival p k := hY k

end ECRuntime
