/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegment

/-!
# Tree Sequence Adjoin Edge

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- An initial-segment extension adding exactly the specified final edge. -/
def TreeSequenceAdjoinEdge {V E : Type*} {G : LooplessMultigraph V E} {e0 : E}
  (T : TreeSequence G e0) (f : E) (Tplus : TreeSequence G e0) : Prop :=
 ∃ hlen : Tplus.length = T.length + 1,
  TreeSequenceInitialSegment T Tplus ∧ Tplus.edge (Fin.cast hlen.symm (Fin.last T.length)) = f

end GoldbergSeymour

end
