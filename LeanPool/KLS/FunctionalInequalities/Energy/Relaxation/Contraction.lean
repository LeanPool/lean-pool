/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Energy.Relaxation.LowerSemicontinuous

/-!
# Contraction bounds under sequential relaxation

This module isolates a generic mechanism for transferring an energy bound from concrete tests to
their sequential relaxation. The hypothesis is deliberately stated using the already-relaxed
energy at the transformed test: it does not require the transformation to preserve the concrete
test class.

Continuity of the transformation and lower semicontinuity of the relaxation then extend the bound
to every ambient point. No lattice, truncation, or Markov structure is asserted here.
-/

@[expose] public section

noncomputable section

open Filter Topology

namespace FunctionalInequalities.Energy.PreEnergy


universe u

section TopologicalSpace

variable {X : Type u} [TopologicalSpace X] (P : PreEnergy X)

/-- A transformation does not increase the relaxed energy of any realized concrete test. -/
def RelaxedContractionBound (C : X → X) : Prop :=
  ∀ f : P.Test,
    P.sequentialRelaxation (C (P.toAmbient f)) ≤ (P.energy f : ENNReal)

/-- Recovery sequences at transformed concrete tests imply the relaxed contraction bound. -/
theorem relaxedContractionBound_of_recovery_sequences {C : X → X}
    (h : ∀ f : P.Test, ∃ approximation : P.ApproximatingSequence (C (P.toAmbient f)),
      Tendsto (fun n ↦ (P.energy (approximation.1 n) : ENNReal)) atTop
        (𝓝 (P.energy f : ENNReal))) :
    P.RelaxedContractionBound C := by
  intro f
  obtain ⟨approximation, henergy⟩ := h f
  calc
    P.sequentialRelaxation (C (P.toAmbient f)) ≤ P.sequenceEnergy approximation :=
      P.sequentialRelaxation_le_sequenceEnergy approximation
    _ = (P.energy f : ENNReal) := henergy.liminf_eq

end TopologicalSpace

section PseudoMetricSpace

variable {X : Type u} [PseudoMetricSpace X] (P : PreEnergy X)

namespace RelaxedContractionBound

/-- A continuous transformation satisfying the relaxed contraction bound on concrete tests does
not increase the sequential relaxation anywhere. -/
theorem sequentialRelaxation_comp_le {C : X → X}
    (h : P.RelaxedContractionBound C) (hC : Continuous C) :
    ∀ x : X, P.sequentialRelaxation (C x) ≤ P.sequentialRelaxation x := by
  intro x
  exact P.le_sequentialRelaxation_of_lowerSemicontinuous
    (P.sequentialRelaxation.comap C) (P.lowerSemicontinuous_sequentialRelaxation.comp hC) h x

end RelaxedContractionBound

end PseudoMetricSpace

end FunctionalInequalities.Energy.PreEnergy
