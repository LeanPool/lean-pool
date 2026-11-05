/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TreeSequenceEdgeSet
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegment
public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet

/-!
# Ordered Tree Union

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A union tree extending the left tree and preserving the relative order of new entries from the
right tree.
-/
structure OrderedTreeUnion {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    {G : LooplessMultigraph V E} {e0 : E} (left right union : TreeSequence G e0) where
  leftSegment : TreeSequenceInitialSegment left union
  vertexSet : TreeSequenceVertexSet union = TreeSequenceVertexSet left ∪ TreeSequenceVertexSet right
  newEntryFromRight :
    ∀ j : Fin union.length,
      left.length ≤ j.val →
        ∃ i : Fin right.length,
          union.edge j = right.edge i ∧ union.vertex j.succ = right.vertex i.succ
  everyNewRightEntry :
    ∀ i : Fin right.length, right.vertex i.succ ∉ TreeSequenceVertexSet left →
    ∃ j : Fin union.length, left.length ≤ j.val ∧ union.edge j = right.edge i ∧ union.vertex
        j.succ = right.vertex i.succ
  rightOrder :
    ∀ i j : Fin right.length, right.vertex i.succ ∉ TreeSequenceVertexSet left → right.vertex
        j.succ ∉ TreeSequenceVertexSet left → i.val < j.val →
    ∀ p q : Fin union.length, union.vertex p.succ = right.vertex i.succ → union.vertex q.succ =
        right.vertex j.succ → p.val < q.val

end GoldbergSeymour

end
