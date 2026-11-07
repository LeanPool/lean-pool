/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.Incident

/-!
# Adjacent Edges

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Two edges are adjacent when they have a common incident vertex. -/
def AdjacentEdges {V E : Type*} (G : LooplessMultigraph V E) (e f : E) : Prop :=
 ∃ v, Incident G v e ∧ Incident G v f

end GoldbergSeymour

end
