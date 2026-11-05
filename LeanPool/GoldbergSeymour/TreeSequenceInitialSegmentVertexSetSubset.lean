/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegment
public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet

/-!
# Tree Sequence Initial Segment Vertex Set Subset

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem TreeSequenceInitialSegmentVertexSetSubset
    {V E : Type*} [Finite V] [Finite E] {G : LooplessMultigraph V E} {e0 : E} {A B : TreeSequence
        G e0}
    (hAB : TreeSequenceInitialSegment A B) :
    TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet B := by
  classical
  let := Fintype.ofFinite V
  let := Fintype.ofFinite E
  intro v hv
  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
    true_and] at hv ⊢
  obtain ⟨i, rfl⟩ := hv
  obtain ⟨hlen, hvertices, _⟩ := hAB
  exact ⟨Fin.castLE (Nat.succ_le_succ hlen) i, hvertices i⟩

end GoldbergSeymour

end
