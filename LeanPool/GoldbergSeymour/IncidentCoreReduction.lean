/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.IncidentCoreElementaryTransfer

public import LeanPool.GoldbergSeymour.IncidentCoreNoIsolated
public import LeanPool.GoldbergSeymour.IncidentCoreTashkinovOrder

/-!
# Incident Core Reduction

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem IncidentCoreReduction {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] (G : LooplessMultigraph V E) :
    let H := IncidentCore G
    (∀ e : E,
      Sym2.map (fun x : IncidentVertex G => x.1) (H.ends e) = G.ends e) ∧
    (∀ x : IncidentVertex G, ∃ e : E, Incident H x e) ∧
    (Critical H ↔ Critical G) ∧
    ChromaticIndex H = ChromaticIndex G ∧
    MaximumDegree H = MaximumDegree G ∧
    TashkinovOrder H = TashkinovOrder G ∧
    (Elementary H → Elementary G) := by
  dsimp
  exact ⟨IncidentCoreEndpoints G, IncidentCoreNoIsolated G,
    IncidentCoreCritical G, (IncidentCoreChromaticIndex G).1,
    IncidentCoreMaximumDegree G, IncidentCoreTashkinovOrder G,
    IncidentCoreElementaryTransfer G⟩

end GoldbergSeymour

end
