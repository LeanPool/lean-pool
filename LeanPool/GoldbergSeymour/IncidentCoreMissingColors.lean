/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.IncidentCoreIncidence
public import LeanPool.GoldbergSeymour.IncidentVertexFintype
public import LeanPool.GoldbergSeymour.MissingColors

/-!
# Incident Core Missing Colors

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem IncidentCoreMissingColors {V E : Type*} [Finite V] [Fintype E]
    (G : LooplessMultigraph V E) (k : ℕ) (phi : PartialEdgeColoring E k)
    (x : IncidentVertex G) :
    PresentColors (IncidentCore G) phi x = PresentColors G phi x.1 ∧
      MissingColors (IncidentCore G) phi x = MissingColors G phi x.1 := by
  classical
  let _ := Fintype.ofFinite V
  have hp : PresentColors (IncidentCore G) phi x = PresentColors G phi x.1 := by
    unfold PresentColors
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨e, he, hc⟩
      exact ⟨e, (IncidentCoreIncidence G x e).1 he, hc⟩
    · rintro ⟨e, he, hc⟩
      exact ⟨e, (IncidentCoreIncidence G x e).2 he, hc⟩
  refine ⟨hp, ?_⟩
  unfold MissingColors
  rw [hp]

end GoldbergSeymour

end
