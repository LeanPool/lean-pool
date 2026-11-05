/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.MissingColors

public import LeanPool.GoldbergSeymour.TreeVerticesBefore

/-!
# Stable Coloring Before Vertex

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Stability restricted to tree vertices preceding the given vertex. -/
def StableColoringBeforeVertex {V E : Type*} [Fintype E] {G : LooplessMultigraph V E}
  {k : ℕ} {e0 : E} (T : TreeSequence G e0) (v : V) (hv : v ∈ TreeSequenceVertexSet T)
  (C : Finset (Fin k)) (phi pi : PartialEdgeColoring E k) : Prop :=
 (∀ f,
   (∃ w ∈ TreeVerticesBefore T v hv, Incident G w f) →
    (∃ c ∈ ((TreeVerticesBefore T v hv).biUnion fun w => MissingColors G phi w) ∪ C,
      phi f = some c) →
     pi f = phi f) ∧
  ∀ w ∈ TreeVerticesBefore T v hv, MissingColors G pi w = MissingColors G phi w

end GoldbergSeymour

end
