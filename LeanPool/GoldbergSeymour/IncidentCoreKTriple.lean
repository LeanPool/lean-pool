/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.IncidentCoreCritical
public import LeanPool.GoldbergSeymour.IncidentCoreMaximumDegree
public import LeanPool.GoldbergSeymour.KTriple

/-!
# Incident Core KTriple

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem IncidentCoreKTriple {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) :
    KTriple (IncidentCore G) k e0 phi ↔ KTriple G k e0 phi := by
  constructor
  · rintro ⟨hcrit, hchi, hdegree, hproper, huncolored⟩
    exact ⟨(IncidentCoreCritical G).1 hcrit,
      (IncidentCoreChromaticIndex G).1 ▸ hchi,
      (IncidentCoreMaximumDegree G) ▸ hdegree,
      (IncidentCoreColoringTransport G).2.1 k phi |>.1 hproper,
      huncolored⟩
  · rintro ⟨hcrit, hchi, hdegree, hproper, huncolored⟩
    exact ⟨(IncidentCoreCritical G).2 hcrit,
      (IncidentCoreChromaticIndex G).1.symm ▸ hchi,
      (IncidentCoreMaximumDegree G).symm ▸ hdegree,
      (IncidentCoreColoringTransport G).2.1 k phi |>.2 hproper,
      huncolored⟩

end GoldbergSeymour

end
