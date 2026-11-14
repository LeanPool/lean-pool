/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.Incident
public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet

/-!
# Tree Incident Edge

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- An edge incident to at least one tree vertex. -/
def TreeIncidentEdge {V E : Type*} {G : LooplessMultigraph V E} {e0 : E} (T : TreeSequence G e0)
  (f : E) : Prop :=
 ∃ v ∈ TreeSequenceVertexSet T, Incident G v f

end GoldbergSeymour

end
