/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Compact-set log-concavity of probability laws

`KLS.LogConcave` tests log-concavity on compact sets and admits laws on proper affine supports.
The property keeps the namespace `KLS.LogConcave` although this module lies in `Probability/`.
The affine combination of compact sets is compact in every real normed space. Equivalence with
density
representations belongs to the separate log-concave representation modules; no Poincaré energy,
constant, approximation theorem or nondegeneracy premise is part of this definition.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace FunctionalInequalities.KLS

section LogConcavity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Compact-set log-concavity, including measures on proper affine supports.
The displayed combination of compact sets is compact in every real normed space. -/
def LogConcave (μ : ProbabilityMeasure E) : Prop :=
  ∀ (K₀ K₁ : Set E), IsCompact K₀ → IsCompact K₁ →
    ∀ t : ℝ, 0 < t → t < 1 →
      (μ : Measure E) K₀ ^ t * (μ : Measure E) K₁ ^ (1 - t) ≤
        (μ : Measure E) {z | ∃ x ∈ K₀, ∃ y ∈ K₁, z = t • x + (1 - t) • y}

end LogConcavity

end FunctionalInequalities.KLS
