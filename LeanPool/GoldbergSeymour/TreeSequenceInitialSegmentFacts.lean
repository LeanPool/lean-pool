/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TreeSequencePrefix

public import LeanPool.GoldbergSeymour.TreeVertexOrder

public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegment
public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet

/-!
# Initial segments of Tashkinov tree sequences

Shared order and vertex-set facts used by the Goldberg–Seymour construction.
The proofs collect repeated arguments from Wesley Pegden's Trellis formalization.
-/

@[expose] public section

namespace GoldbergSeymour.TreeSequenceInitialSegment

variable {V E : Type*} {G : LooplessMultigraph V E} {e0 : E}

theorem refl (tree : TreeSequence G e0) : TreeSequenceInitialSegment tree tree := by
  exact ⟨le_rfl, fun _ ↦ rfl, fun _ ↦ rfl⟩

theorem trans {first second third : TreeSequence G e0}
    (firstSecond : TreeSequenceInitialSegment first second)
    (secondThird : TreeSequenceInitialSegment second third) :
    TreeSequenceInitialSegment first third := by
  obtain ⟨firstLength, firstVertices, firstEdges⟩ := firstSecond
  obtain ⟨secondLength, secondVertices, secondEdges⟩ := secondThird
  refine ⟨le_trans firstLength secondLength, ?_, ?_⟩
  · intro index
    simpa only [Fin.castLE] using
      (secondVertices (Fin.castLE (Nat.succ_le_succ firstLength) index)).trans
        (firstVertices index)
  · intro index
    simpa only [Fin.castLE] using
      (secondEdges (Fin.castLE firstLength index)).trans (firstEdges index)

theorem vertexSet_subset {first second : TreeSequence G e0}
    (segment : TreeSequenceInitialSegment first second) :
    TreeSequenceVertexSet first ⊆ TreeSequenceVertexSet second := by
  classical
  obtain ⟨lengthBound, vertices, _⟩ := segment
  intro vertex membership
  obtain ⟨index, _, rfl⟩ := Finset.mem_image.mp membership
  exact Finset.mem_image.mpr
    ⟨Fin.castLE (Nat.succ_le_succ lengthBound) index, Finset.mem_univ _, vertices index⟩

theorem of_common_extension {first second extension : TreeSequence G e0}
    (firstExtension : TreeSequenceInitialSegment first extension)
    (secondExtension : TreeSequenceInitialSegment second extension)
    (lengthBound : second.length ≤ first.length) :
    TreeSequenceInitialSegment second first := by
  obtain ⟨firstLength, firstVertices, firstEdges⟩ := firstExtension
  obtain ⟨secondLength, secondVertices, secondEdges⟩ := secondExtension
  refine ⟨lengthBound, ?_, ?_⟩
  · intro index
    calc
      first.vertex (Fin.castLE (Nat.succ_le_succ lengthBound) index) =
          extension.vertex (Fin.castLE (Nat.succ_le_succ firstLength)
            (Fin.castLE (Nat.succ_le_succ lengthBound) index)) :=
        (firstVertices _).symm
      _ = extension.vertex (Fin.castLE (Nat.succ_le_succ secondLength) index) := by
        congr 1
      _ = second.vertex index := secondVertices index
  · intro index
    calc
      first.edge (Fin.castLE lengthBound index) =
          extension.edge (Fin.castLE firstLength (Fin.castLE lengthBound index)) :=
        (firstEdges _).symm
      _ = extension.edge (Fin.castLE secondLength index) := by congr 1
      _ = second.edge index := secondEdges index

/-- A tree's last vertex does not occur in a strictly shorter initial segment. -/
theorem last_vertex_ne {initial tree : TreeSequence G e0}
    (segment : TreeSequenceInitialSegment initial tree) (shorter : initial.length < tree.length)
    (index : Fin (initial.length + 1)) :
    tree.vertex (Fin.last tree.length) ≠ initial.vertex index := by
  intro equal
  have positions := congrArg Fin.val (tree.vertex_injective (equal.trans (segment.2.1 index).symm))
  have bound := index.isLt
  change tree.length = index.val at positions
  omega

/-- Every vertex of a prefix precedes a tree position lying strictly beyond that prefix. -/
theorem vertex_precedes {initial tree : TreeSequence G e0}
    (segment : TreeSequenceInitialSegment initial tree) {position : Fin (tree.length + 1)}
    (later : initial.length < position.val) {vertex : V}
    (member : vertex ∈ TreeSequenceVertexSet initial) :
    TreeVertexOrder tree vertex (tree.vertex position) := by
  classical
  obtain ⟨index, equality⟩ : ∃ index, initial.vertex index = vertex := by
    simpa [TreeSequenceVertexSet] using member
  refine ⟨Fin.castLE (Nat.succ_le_succ segment.1) index, position,
    (segment.2.1 index).trans equality, rfl, ?_⟩
  have bound := index.isLt
  change index.val < position.val
  omega

/-- A tree position beyond an initial segment has a vertex outside that segment. -/
theorem vertex_not_mem_after {initial tree : TreeSequence G e0}
    (segment : TreeSequenceInitialSegment initial tree) {position : Fin (tree.length + 1)}
    (later : initial.length < position.val) :
    tree.vertex position ∉ TreeSequenceVertexSet initial := by
  classical
  intro member
  obtain ⟨index, equality⟩ : ∃ index, initial.vertex index = tree.vertex position := by
    simpa [TreeSequenceVertexSet] using member
  have equal := congrArg Fin.val (tree.vertex_injective ((segment.2.1 index).trans equality))
  have bound := index.isLt
  change index.val = position.val at equal
  omega

/-- Every nonempty prefix is an initial segment of its source tree. -/
theorem prefix_segment (tree : TreeSequence G e0) (length : ℕ)
    (positive : 1 ≤ length) (bound : length ≤ tree.length) :
    TreeSequenceInitialSegment (TreeSequencePrefix tree length positive bound) tree := by
  exact ⟨bound, fun _ => rfl, fun _ => rfl⟩

/-- Prefixes of the same tree are nested in the order of their lengths. -/
theorem prefix_prefix (tree : TreeSequence G e0) (first last : ℕ)
    (firstPositive : 1 ≤ first) (lastPositive : 1 ≤ last)
    (firstBound : first ≤ tree.length) (lastBound : last ≤ tree.length)
    (ordered : first ≤ last) :
    TreeSequenceInitialSegment
      (TreeSequencePrefix tree first firstPositive firstBound)
      (TreeSequencePrefix tree last lastPositive lastBound) := by
  refine ⟨ordered, ?_, ?_⟩
  · intro index
    change tree.vertex _ = tree.vertex _
    congr 1
  · intro index
    change tree.edge _ = tree.edge _
    congr 1


/-- A prefix of an extension contains an initial segment whose length is below its cutoff. -/
theorem prefix_of_segment {initial tree : TreeSequence G e0}
    (segment : TreeSequenceInitialSegment initial tree) (length : ℕ)
    (lower : initial.length ≤ length) (upper : length ≤ tree.length) :
    TreeSequenceInitialSegment initial
      (TreeSequencePrefix tree length (initial.positive.trans lower) upper) := by
  exact (prefix_segment tree length (initial.positive.trans lower) upper).of_common_extension
    segment lower


end GoldbergSeymour.TreeSequenceInitialSegment

end
