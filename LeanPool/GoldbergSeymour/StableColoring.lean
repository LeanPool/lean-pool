/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TreeIncidentEdge
public import LeanPool.GoldbergSeymour.TreeMissingColors

/-!
# Stable Coloring

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Preservation of relevant incident-edge colors and every missing-color set on the tree. -/
def StableColoring {V E : Type*} [Fintype E] {G : LooplessMultigraph V E} {k : ℕ}
  {e0 : E} (T : TreeSequence G e0) (C : Finset (Fin k)) (phi pi : PartialEdgeColoring E k) : Prop :=
 (∀ f, TreeIncidentEdge T f → (∃ c ∈ TreeMissingColors phi T ∪ C, phi f = some c) → pi f = phi f) ∧
  ∀ v ∈ TreeSequenceVertexSet T, MissingColors G pi v = MissingColors G phi v

end GoldbergSeymour

end
