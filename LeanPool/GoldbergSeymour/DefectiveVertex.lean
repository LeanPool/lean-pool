/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.DefectiveEdge
public import LeanPool.GoldbergSeymour.Incident

/-!
# Defective Vertex

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A vertex inside the set incident to an edge of a defective boundary color. -/
def DefectiveVertex {V E : Type*} [Fintype V] [Fintype E] (G : LooplessMultigraph V E) {k : ℕ}
  (phi : PartialEdgeColoring E k) (X : Finset V) (v : V) : Prop :=
 v ∈ X ∧ ∃ f : E, DefectiveEdge G phi X f ∧ Incident G v f

end GoldbergSeymour

end
