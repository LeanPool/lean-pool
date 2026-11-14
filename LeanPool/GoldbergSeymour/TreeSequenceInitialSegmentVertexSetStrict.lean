/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentVertexSetSubset

/-!
# Tree Sequence Initial Segment Vertex Set Strict

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem TreeSequenceInitialSegmentVertexSetStrict
    {V E : Type*} [Finite V] [Finite E] {G : LooplessMultigraph V E} {e0 : E} {A B : TreeSequence
        G e0}
    (hAB : TreeSequenceInitialSegment A B) (hlen : A.length < B.length) :
    TreeSequenceVertexSet A < TreeSequenceVertexSet B := by
  classical
  let := Fintype.ofFinite V
  let := Fintype.ofFinite E
  have hsubset := TreeSequenceInitialSegmentVertexSetSubset hAB
  refine Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, ?_⟩
  intro heq
  have hcard : (TreeSequenceVertexSet A).card =
      (TreeSequenceVertexSet B).card := congrArg Finset.card heq
  have hcardA : (TreeSequenceVertexSet A).card = A.length + 1 := by
    simp [TreeSequenceVertexSet, Finset.card_image_of_injective,
      A.vertex_injective]
  have hcardB : (TreeSequenceVertexSet B).card = B.length + 1 := by
    simp [TreeSequenceVertexSet, Finset.card_image_of_injective,
      B.vertex_injective]
  rw [hcardA, hcardB] at hcard
  omega

end GoldbergSeymour

end
