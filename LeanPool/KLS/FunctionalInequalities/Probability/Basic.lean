/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Probability-measure boundary

Public measure-dependent definitions in the new foundation take a bundled
`ProbabilityMeasure`. Low-level lemmas that already carry a `Measure` together with an
`IsProbabilityMeasure` instance can cross that boundary through the single constructor here.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace FunctionalInequalities.Probability

variable {α : Type*} [MeasurableSpace α]

/-- Bundle a measure whose probability normalization is already available as an instance. -/
def ofMeasure (μ : Measure α) [IsProbabilityMeasure μ] : ProbabilityMeasure α :=
  ⟨μ, inferInstance⟩

/-- Unbundling `ofMeasure` recovers the original measure definitionally. -/
@[simp]
theorem coe_ofMeasure (μ : Measure α) [IsProbabilityMeasure μ] :
    (ofMeasure μ : Measure α) = μ :=
  rfl

end FunctionalInequalities.Probability
