/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.Critical
public import LeanPool.GoldbergSeymour.IncidentCoreChromaticIndex

/-!
# Incident Core Critical

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem IncidentCoreCritical {V E : Type*} [Finite V] [Fintype E]
    [DecidableEq E] (G : LooplessMultigraph V E) :
    Critical (IncidentCore G) ↔ Critical G := by
  classical
  let _ := Fintype.ofFinite V
  constructor
  · intro hcore e
    change ChromaticIndex (RestrictEdges G (Finset.univ.erase e)) <
      ChromaticIndex G
    rw [← (IncidentCoreChromaticIndex G).2 (Finset.univ.erase e),
      ← (IncidentCoreChromaticIndex G).1]
    exact hcore e
  · intro horiginal e
    change ChromaticIndex (RestrictEdges (IncidentCore G) (Finset.univ.erase e)) <
      ChromaticIndex (IncidentCore G)
    rw [(IncidentCoreChromaticIndex G).2 (Finset.univ.erase e),
      (IncidentCoreChromaticIndex G).1]
    exact horiginal e

end GoldbergSeymour

end
