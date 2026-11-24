/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
public import LeanPool.GraphMinor.GM10.TangleLemmas

/-!
# Tangles induced by subgraphs

This file supplies the assertion following (4.1) of Graph Minors XII, page 248.
Intersect a separation with the subgraph, then apply each tangle axiom there.
The argument works for hypergraphs as well as graphs.
-/

public section

namespace GraphMinor.GM12

open Set Hypergraph GM10

variable {α β : Type*} {G H A B : Hypergraph α β}

/-- Intersecting both sides of a separation with a subgraph gives a separation
of that subgraph, as used in Graph Minors XII, Section 4, page 248. -/
theorem separation_inter_subgraph (hs : G.IsSeparation A B) (hH : H ≤ G) :
    H.IsSeparation (A ∩ H) (B ∩ H) := by
  refine (isSeparation_iff_of_le (inter_le_right hs.left_le hH)
    (inter_le_right hs.right_le hH)).mpr ⟨?_, ?_, ?_⟩
  · rw [inter_vertexSet, inter_vertexSet, ← Set.union_inter_distrib_right,
      hs.vertexSet_union, Set.inter_eq_right.mpr hH.vertexSet_subset]
  · rw [inter_edgeSet, inter_edgeSet, ← Set.union_inter_distrib_right,
      hs.edgeSet_union, Set.inter_eq_right.mpr hH.edgeSet_subset]
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro e he
    exact hs.notMem_edgeSet_right he.1.1 he.2.1

/-- Restriction does not increase the order of a separation. -/
theorem separationOrder_inter_subgraph_le (A B H : Hypergraph α β) :
    separationOrder (A ∩ H) (B ∩ H) ≤ separationOrder A B := by
  exact Set.ncard_le_ncard (fun _ hx => ⟨hx.1.1, hx.2.1⟩)
    (A ∩ B).vertexSet_finite

/-- Graph Minors XII, Section 4, page 248: the tangle induced by a tangle in a
subgraph is a tangle of the same order. Each axiom follows by intersection with
that subgraph. -/
theorem inducedBySubgraph_isTangle {θ : ℕ}
    {T : Set (Hypergraph α β × Hypergraph α β)}
    (hH : H ≤ G) (hT : IsTangle H θ T) :
    IsTangle G θ (inducedBySubgraph G H θ T) := by
  refine ⟨hT.one_le, fun _ _ h => h.1, fun _ _ h => h.2.1, ?_, ?_, ?_⟩
  · intro A B hs ho
    have hsH := separation_inter_subgraph hs hH
    have hoH := lt_of_le_of_lt (separationOrder_inter_subgraph_le A B H) ho
    rcases hT.axiom1 hsH hoH with h | h
    · exact Or.inl ⟨hs, ho, h⟩
    · exact Or.inr ⟨hs.symm, by rwa [separationOrder_comm], h⟩
  · intro A₁ B₁ A₂ B₂ A₃ B₃ h₁ h₂ h₃ heq
    apply hT.axiom2 h₁.2.2 h₂.2.2 h₃.2.2
    have hle := union_le (union_le
      (inter_le_right h₁.1.left_le hH) (inter_le_right h₂.1.left_le hH))
      (inter_le_right h₃.1.left_le hH)
    refine eq_of_le_of_vertexSet_eq_of_edgeSet_eq hle le_rfl ?_ ?_
    · simp only [union_vertexSet, inter_vertexSet]
      rw [← Set.union_inter_distrib_right, ← Set.union_inter_distrib_right]
      change (A₁ ∪ A₂ ∪ A₃).vertexSet ∩ H.vertexSet = H.vertexSet
      rw [heq, Set.inter_eq_right.mpr hH.vertexSet_subset]
    · simp only [union_edgeSet, inter_edgeSet]
      rw [← Set.union_inter_distrib_right, ← Set.union_inter_distrib_right]
      change (A₁ ∪ A₂ ∪ A₃).edgeSet ∩ H.edgeSet = H.edgeSet
      rw [heq, Set.inter_eq_right.mpr hH.edgeSet_subset]
  · intro A B h heq
    apply hT.axiom3 h.2.2
    change A.vertexSet ∩ H.vertexSet = H.vertexSet
    rw [heq, Set.inter_eq_right.mpr hH.vertexSet_subset]


/-- The free boundary vertices exclude any induced small side containing them.
This is the contradiction in claim (2) of the proof of Graph Minors XII, (6.1),
page 258, after the enclosing walk has supplied its separation. -/
theorem free_set_not_subset_induced_small_side {θ : ℕ}
    {T : Set (Hypergraph α β × Hypergraph α β)} {X : Set α}
    (hfree : IsFreeSet H T θ X)
    (hmem : (A, B) ∈ inducedBySubgraph G H θ T)
    (horder : separationOrder A B < X.ncard) : ¬ X ⊆ A.vertexSet := by
  intro hXA
  have hXAH : X ⊆ (A ∩ H).vertexSet := fun _ hx => ⟨hXA hx, hfree.1 hx⟩
  have hbound := hfree.2.2 hmem.2.2 hXAH
  exact (not_lt_of_ge (hbound.trans (separationOrder_inter_subgraph_le A B H))) horder

/-- Control of a minor in a subgraph gives control in the whole graph for the
induced tangle. This justifies the reduction to the drawing in the proof of
Graph Minors XII, (4.3), page 249. -/
theorem controlsMinor_inducedBySubgraph {γ δ : Type*} {L : Graph γ δ} {θ : ℕ}
    {T : Set (Hypergraph α β × Hypergraph α β)} (hH : H ≤ G)
    (hc : ControlsMinor H θ T L) :
    ControlsMinor G θ (inducedBySubgraph G H θ T) L := by
  obtain ⟨a, b, ha, hdisj, hlink, hloop, hinj, hcard, hcontrol⟩ := hc
  refine ⟨a, b, ?_, hdisj, ?_, ?_, hinj, hcard, ?_⟩
  · intro v hv
    have hvH : a v ≤ H := (ha v hv).1
    exact ⟨hvH.trans hH, (ha v hv).2⟩
  · intro e u v he huv
    obtain ⟨heH, hxH, hyH⟩ := hlink e u v he huv
    obtain ⟨x, hx, hxe⟩ := hxH
    obtain ⟨y, hy, hye⟩ := hyH
    refine ⟨hH.edgeSet_subset heH, ⟨x, hx, ?_⟩, ⟨y, hy, ?_⟩⟩
    · exact (inc_iff_of_le hH heH).mp hxe
    · exact (inc_iff_of_le hH heH).mp hye
  · intro e v he
    obtain ⟨heH, hen, hend⟩ := hloop e v he
    exact ⟨hH.edgeSet_subset heH, hen,
      fun x hx => hend x ((inc_iff_of_le hH heH).mpr hx)⟩
  · intro A B hm ho v hv hsub
    apply hcontrol (A ∩ H) (B ∩ H) hm.2.2
      (lt_of_le_of_lt (separationOrder_inter_subgraph_le A B H) ho) v hv
    exact fun x hx => ⟨hsub hx, (ha v hv).1.vertexSet_subset hx⟩

end GraphMinor.GM12
