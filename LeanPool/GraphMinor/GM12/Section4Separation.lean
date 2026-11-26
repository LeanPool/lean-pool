/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM10.TangleLemmas

/-!
# Putting a path into a small side

At the start of Graph Minors XII, (4.1), page 248, the path has all its
vertices in the small side, but some of its edges may be on the other side.
Move those edges to the small side. Its vertex set and the separator stay
the same, and Graph Minors X, (2.9), keeps the separation in the tangle.
-/

public section

namespace GraphMinor.GM12

open Set Hypergraph GM10

/-- Move a subhypergraph whose vertices already lie in the left side into
that side. This is the separation adjustment at the start of XII (4.1). -/
theorem separation_move_subhypergraph {α β : Type*} {G A B H : Hypergraph α β}
    (hs : G.IsSeparation A B) (hH : H ≤ G) (hV : H.vertexSet ⊆ A.vertexSet) :
    G.IsSeparation (A ∪ H) (B.deleteEdges H.edgeSet) ∧
      (A ∪ H).vertexSet = A.vertexSet ∧
      separationOrder (A ∪ H) (B.deleteEdges H.edgeSet) = separationOrder A B := by
  have hVA : (A ∪ H).vertexSet = A.vertexSet := by
    rw [union_vertexSet, Set.union_eq_left.mpr hV]
  refine ⟨?_, hVA, ?_⟩
  · apply (isSeparation_iff_of_le (union_le hs.left_le hH)
      ((deleteEdges_le B H.edgeSet).trans hs.right_le)).mpr
    refine ⟨?_, ?_, ?_⟩
    · change (A ∪ H).vertexSet ∪ B.vertexSet = G.vertexSet
      rw [hVA, hs.vertexSet_union]
    · ext e
      change (e ∈ A.edgeSet ∨ e ∈ H.edgeSet) ∨
        (e ∈ B.edgeSet ∧ e ∉ H.edgeSet) ↔ e ∈ G.edgeSet
      constructor
      · rintro ((he | he) | ⟨he, _⟩)
        · exact hs.left_le.edgeSet_subset he
        · exact hH.edgeSet_subset he
        · exact hs.right_le.edgeSet_subset he
      · intro he
        by_cases heH : e ∈ H.edgeSet
        · exact Or.inl (Or.inr heH)
        · have heAB : e ∈ A.edgeSet ∪ B.edgeSet := hs.edgeSet_union.symm ▸ he
          exact heAB.elim (fun h => Or.inl (Or.inl h)) (fun h => Or.inr ⟨h, heH⟩)
    · apply Set.eq_empty_iff_forall_notMem.mpr
      rintro e ⟨heA | heH, heB, heH'⟩
      · exact hs.notMem_edgeSet_right heA heB
      · exact heH' heH
  · change ((A ∪ H).vertexSet ∩ B.vertexSet).ncard = _
    rw [hVA]
    rfl

/-- Graph Minors X, (2.9), applied as in XII (4.1), page 248: moving the
path edges leaves the separator unchanged and preserves tangle membership. -/
theorem tangle_move_subhypergraph {α β : Type*} {G A B H : Hypergraph α β}
    {θ : ℕ} {T : Set (Hypergraph α β × Hypergraph α β)}
    (hT : IsTangle G θ T) (hAB : (A, B) ∈ T) (hH : H ≤ G)
    (hV : H.vertexSet ⊆ A.vertexSet) :
    (A ∪ H, B.deleteEdges H.edgeSet) ∈ T ∧
      separationOrder (A ∪ H) (B.deleteEdges H.edgeSet) = separationOrder A B := by
  obtain ⟨hs, _, ho⟩ := separation_move_subhypergraph (hT.isSeparation hAB) hH hV
  refine ⟨GraphMinor.GM10.theorem_2_9_proof hT hAB hs ?_ (Or.inl subset_rfl), ho⟩
  rw [ho]
  exact hT.order_lt hAB

end GraphMinor.GM12
