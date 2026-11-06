/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TreeVerticesBefore
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentFacts
public import LeanPool.GoldbergSeymour.MissingColors

/-!
# Facts About Strict Tree Prefixes

Shared facts from Wesley Pegden's Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12, generalized during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A vertex strictly before another vertex cannot equal it. -/
theorem TreeVerticesBefore.ne_self {V E : Type*} {G : LooplessMultigraph V E} {e0 : E}
    {tree : TreeSequence G e0} {vertex value : V}
    {member : vertex ∈ TreeSequenceVertexSet tree}
    (membership : value ∈ TreeVerticesBefore tree vertex member) : value ≠ vertex := by
  classical
  unfold TreeVerticesBefore at membership
  obtain ⟨-, first, last, firstValue, lastVertex, ordered⟩ := Finset.mem_filter.mp membership
  intro equal
  have samePosition : first = last := tree.vertex_injective
    (firstValue.trans (equal.trans lastVertex.symm))
  omega

/-- Equality away from two erased vertices gives equality throughout a strict tree prefix. -/
theorem TreeVerticesBefore.missingColors_eq_of_erase {V E : Type*}
    [DecidableEq V] [Fintype E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {tree : TreeSequence G e0} {vertex special : V}
    {member : vertex ∈ TreeSequenceVertexSet tree} {extra : Finset V}
    {first second : PartialEdgeColoring E k}
    (offSpecial : ∀ value ∈ ((extra ∪
      (TreeVerticesBefore tree vertex member ∪ {vertex})).erase vertex).erase special,
      MissingColors G second value = MissingColors G first value)
    (atSpecial : special ∈ TreeVerticesBefore tree vertex member →
      MissingColors G second special = MissingColors G first special)
    {value : V} (membership : value ∈ TreeVerticesBefore tree vertex member) :
    MissingColors G second value = MissingColors G first value := by
  classical
  by_cases equal : value = special
  · subst value
    exact atSpecial membership
  · apply offSpecial value
    apply Finset.mem_erase.mpr
    refine ⟨equal, Finset.mem_erase.mpr ⟨TreeVerticesBefore.ne_self membership, ?_⟩⟩
    exact Finset.mem_union_right _ (Finset.mem_union_left _ membership)

/-- A strictly shorter initial segment lies before any supplied cutoff for the middle tree. -/
theorem TreeSequenceInitialSegment.mem_before_of_length {V E : Type*}
    {G : LooplessMultigraph V E} {e0 : E} {initial middle tree : TreeSequence G e0}
    (initialMiddle : TreeSequenceInitialSegment initial middle)
    (middleTree : TreeSequenceInitialSegment middle tree)
    (strictLength : initial.length < middle.length) {vertex : V}
    {member : vertex ∈ TreeSequenceVertexSet tree}
    (beforePositions : ∀ index : Fin (tree.length + 1), index.val < middle.length →
      tree.vertex index ∈ TreeVerticesBefore tree vertex member)
    {value : V} (membership : value ∈ TreeSequenceVertexSet initial) :
    value ∈ TreeVerticesBefore tree vertex member := by
  classical
  obtain ⟨index, _, rfl⟩ := Finset.mem_image.mp membership
  have segment := initialMiddle.trans middleTree
  have bound : index.val ≤ initial.length := Nat.le_of_lt_succ index.isLt
  rw [← segment.2.1 index]
  exact beforePositions (Fin.castLE (Nat.succ_le_succ segment.1) index)
    (lt_of_le_of_lt bound strictLength)

end GoldbergSeymour

end
