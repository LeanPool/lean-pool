/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ChromaticIndex
public import LeanPool.GoldbergSeymour.DeleteEdge

/-!
# Critical

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Deleting any edge strictly decreases the chromatic index. -/
def Critical {V E : Type*} [Fintype E] [DecidableEq E] (G : LooplessMultigraph V E) :
  Prop :=
 ∀ e : E, ChromaticIndex (DeleteEdge G e) < ChromaticIndex G

end GoldbergSeymour

end
