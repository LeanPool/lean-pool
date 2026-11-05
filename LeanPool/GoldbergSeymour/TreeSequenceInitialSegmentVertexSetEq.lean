/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegment
public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet
public import Mathlib.Data.Fintype.Card

/-!
# Tree Sequence Initial Segment Vertex Set Eq

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem TreeSequenceInitialSegmentVertexSetEq
    {V E : Type*}
    {G : LooplessMultigraph V E} {e0 : E}
    (A B : TreeSequence G e0)
    (hAB : TreeSequenceInitialSegment A B)
    (hvertices : TreeSequenceVertexSet A = TreeSequenceVertexSet B) :
    A = B := by
  have hcard (S : TreeSequence G e0) :
      (TreeSequenceVertexSet S).card = S.length + 1 := by
    classical
    rw [TreeSequenceVertexSet, Finset.card_image_of_injective _ S.vertex_injective]
    simp
  have hlength : A.length = B.length := by
    have := congrArg Finset.card hvertices
    rw [hcard A, hcard B] at this
    omega
  rcases hAB with ⟨hlen, hvertex, hedge⟩
  cases A with
  | mk la pa va ea via eia fa aa =>
    cases B with
    | mk lb pb vb eb vib eib fb ab =>
      simp only at hlength
      subst lb
      rw [TreeSequence.mk.injEq]
      refine ⟨rfl, ?_, ?_⟩
      · apply heq_of_eq
        funext i
        simpa only [Fin.castLE] using (hvertex i).symm
      · apply heq_of_eq
        funext i
        simpa only [Fin.castLE] using (hedge i).symm

end GoldbergSeymour

end
