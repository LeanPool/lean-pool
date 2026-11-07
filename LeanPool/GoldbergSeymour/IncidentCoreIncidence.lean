/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.IncidentCoreEndpoints

/-!
# Incident Core Incidence

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem IncidentCoreIncidence {V E : Type*} (G : LooplessMultigraph V E)
    (x : IncidentVertex G) (e : E) :
    Incident (IncidentCore G) x e ↔ Incident G x.1 e := by
  classical
  change x ∈ (IncidentCore G).ends e ↔ x.1 ∈ G.ends e
  constructor
  · intro hx
    rw [← IncidentCoreEndpoints G e]
    exact Sym2.mem_map.mpr ⟨x, hx, rfl⟩
  · intro hx
    have hx' : x.1 ∈ Sym2.map (fun y : IncidentVertex G => y.1)
        ((IncidentCore G).ends e) := by
      rw [IncidentCoreEndpoints G e]
      exact hx
    obtain ⟨y, hy, heq⟩ := Sym2.mem_map.mp hx'
    have : y = x := Subtype.ext heq
    simpa [this] using hy

end GoldbergSeymour

end
