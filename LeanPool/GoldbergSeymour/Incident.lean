/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.LooplessMultigraph

/-!
# Incident

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A vertex is incident to an edge when it belongs to its unordered pair of endpoints. -/
def Incident {V E : Type*} (G : LooplessMultigraph V E) (v : V) (e : E) : Prop :=
 v ∈ G.ends e

end GoldbergSeymour

end
