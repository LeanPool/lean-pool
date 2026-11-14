/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TreeSequence

/-!
# Tree Sequence Initial Segment

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- The shorter tree's ordered vertices and edges agree with the beginning of the longer tree. -/
def TreeSequenceInitialSegment {V E : Type*} {G : LooplessMultigraph V E} {e0 : E}
  (T T' : TreeSequence G e0) : Prop :=
 ∃ hlen : T.length ≤ T'.length,
  (∀ i : Fin (T.length + 1), T'.vertex (Fin.castLE (Nat.succ_le_succ hlen) i) = T.vertex i) ∧
   ∀ j : Fin T.length, T'.edge (Fin.castLE hlen j) = T.edge j

end GoldbergSeymour

end
