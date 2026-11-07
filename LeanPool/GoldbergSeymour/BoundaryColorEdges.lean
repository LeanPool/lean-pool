/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.BoundaryEdges
public import LeanPool.GoldbergSeymour.PartialEdgeColoring

/-!
# Boundary Color Edges

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Edges crossing the vertex-set boundary and carrying the specified color. -/
noncomputable def BoundaryColorEdges {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) {k : ℕ} (phi : PartialEdgeColoring E k) (X : Finset V)
    (alpha : Fin k) : Finset E := by
  classical
  exact (BoundaryEdges G X).filter fun f => phi f = some alpha

end GoldbergSeymour

end
