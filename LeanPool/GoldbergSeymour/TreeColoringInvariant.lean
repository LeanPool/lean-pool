/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.MissingColors

public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet

/-!
# Tree Coloring Invariant

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- The noninitial tree-edge colors and every tree vertex's missing-color set are unchanged. -/
def TreeColoringInvariant {V E : Type*} [Fintype E] {G : LooplessMultigraph V E} {k : ℕ}
  {e0 : E} (T : TreeSequence G e0) (phi pi : PartialEdgeColoring E k) : Prop :=
 (∀ j : Fin T.length, 1 ≤ j.val → pi (T.edge j) = phi (T.edge j)) ∧
  ∀ v ∈ TreeSequenceVertexSet T, MissingColors G pi v = MissingColors G phi v

end GoldbergSeymour

end
