/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ColoredVertexSetClosed

/-!
# Colored Vertex Set Strongly Closed

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A closed vertex set whose distinct boundary edges have distinct colors. -/
def ColoredVertexSetStronglyClosed {V E : Type*} [Fintype V] [Fintype E]
  (G : LooplessMultigraph V E) {k : ℕ} (phi : PartialEdgeColoring E k) (X : Finset V) : Prop :=
 ColoredVertexSetClosed G phi X ∧
  ∀ {f g c}, f ∈ BoundaryEdges G X → g ∈ BoundaryEdges G X → f ≠ g → phi f = some c → phi g ≠ some c

end GoldbergSeymour

end
