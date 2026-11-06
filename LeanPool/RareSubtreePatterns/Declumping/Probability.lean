/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Declumping.Deterministic
public import LeanPool.RareSubtreePatterns.Probability.TotalVariation
public import Mathlib.Probability.Distributions.Poisson.Basic

import Mathlib.Tactic.Linarith

/-!
# From declumped Poisson counts to raw zero events

The probabilistic reduction in Lemma `lem:declump_to_raw`, source lines
2343–2399, for arbitrary laws on finite plane trees and arbitrary limit filters.
This does not construct the conditioned Bienaymé law or prove its hypotheses.

The finite-measure sandwich also holds for nonmeasurable raw/root events,
with `Measure.real` interpreted using the outer extension. Applications to the
paper use measurable events (in particular, the discrete tree sigma algebra).
The declumped count must be measurable when its distribution is pushed forward.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace PoissonDeclumping.PlaneTree

variable [MeasurableSpace PlaneTree] {B : Set ℕ} {G : PlaneTree → Prop}

/-- The difference of the zero-event probabilities is between zero and the
root-mark probability, exactly as in the proof of Lemma `lem:declump_to_raw`. -/
theorem zero_probability_sandwich (μ : Measure PlaneTree) [IsFiniteMeasure μ]
    (hprop : PropagatesOutside B G) :
    0 ≤ μ.real {T | markCount (declumpedMark B G) T = 0} -
      μ.real {T | markCount G T = 0} ∧
    μ.real {T | markCount (declumpedMark B G) T = 0} -
      μ.real {T | markCount G T = 0} ≤ μ.real {T | G T} := by
  have hl := measureReal_mono (μ := μ) (raw_zero_subset_declumped_zero B G)
  have hu := (measureReal_mono (μ := μ)
    (declumped_zero_subset_raw_zero_union_root hprop)).trans
      (measureReal_union_le {T | markCount G T = 0} {T | G T})
  constructor <;> linarith

/-- Absolute version of the zero-event sandwich. -/
theorem abs_raw_zero_sub_declumped_zero_le (μ : Measure PlaneTree) [IsFiniteMeasure μ]
    (hprop : PropagatesOutside B G) :
    |μ.real {T | markCount G T = 0} -
      μ.real {T | markCount (declumpedMark B G) T = 0}| ≤ μ.real {T | G T} := by
  obtain ⟨hl, hu⟩ := zero_probability_sandwich μ hprop
  rw [abs_sub_comm, abs_of_nonneg hl]
  exact hu

/-- A finite-parameter error bound underlying Lemma `lem:declump_to_raw`.
No boundedness assumption on the Poisson rate is needed. -/
theorem raw_zero_poisson_error_le (μ : Measure PlaneTree) [IsProbabilityMeasure μ]
    (rate : ℝ≥0) (hprop : PropagatesOutside B G)
    (hmeas : Measurable (markCount (declumpedMark B G))) :
    |μ.real {T | markCount G T = 0} - Real.exp (-(rate : ℝ))| ≤
      μ.real {T | G T} +
        paperTVDist (μ.map (markCount (declumpedMark B G))) (poissonMeasure rate) := by
  have ht := abs_sub_measureReal_le_paperTVDist
    (μ.map (markCount (declumpedMark B G))) (poissonMeasure rate)
    (measurableSet_singleton 0)
  have hzero : (μ.map (markCount (declumpedMark B G))).real {0} =
      μ.real {T | markCount (declumpedMark B G) T = 0} := by
    rw [map_measureReal_apply hmeas (measurableSet_singleton 0)]
    rfl
  have hp : (poissonMeasure rate).real {0} = Real.exp (-(rate : ℝ)) := by
    simp [poissonMeasure_real_singleton]
  rw [hzero, hp] at ht
  exact (abs_sub_le _ (μ.real {T | markCount (declumpedMark B G) T = 0}) _).trans
    (add_le_add (abs_raw_zero_sub_declumped_zero_le μ hprop) ht)

/-- The abstract law-level reduction of Lemma `lem:declump_to_raw`.

An arbitrary filter permits subsequent use along admissible tree sizes. The
conditioned Bienaymé law and the hypotheses for its application remain separate
obligations; they are not supplied by this reduction. -/
theorem declump_to_raw {ι : Type*} (l : Filter ι) (μ : ι → Measure PlaneTree)
    [∀ i, IsProbabilityMeasure (μ i)] (B : Set ℕ) (G : ι → PlaneTree → Prop)
    (rate : ι → ℝ≥0)
    (hprop : ∀ i, PropagatesOutside B (G i))
    (hmeas : ∀ i, Measurable (markCount (declumpedMark B (G i))))
    (hroot : Tendsto (fun i => (μ i).real {T | G i T}) l (𝓝 0))
    (htv : Tendsto (fun i => paperTVDist
      ((μ i).map (markCount (declumpedMark B (G i)))) (poissonMeasure (rate i)))
      l (𝓝 0)) :
    Tendsto (fun i => (μ i).real {T | markCount (G i) T = 0} -
      Real.exp (-(rate i : ℝ))) l (𝓝 0) := by
  refine squeeze_zero_norm
    (a := fun i => (μ i).real {T | G i T} + paperTVDist
      ((μ i).map (markCount (declumpedMark B (G i)))) (poissonMeasure (rate i)))
    (fun i => ?_) ?_
  · simpa only [Real.norm_eq_abs] using
      raw_zero_poisson_error_le (μ i) (rate i) (hprop i) (hmeas i)
  · simpa only [zero_add] using hroot.add htv

end PoissonDeclumping.PlaneTree
