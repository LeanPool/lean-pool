/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

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

end GoldbergSeymour.TreeSequenceInitialSegment

end
