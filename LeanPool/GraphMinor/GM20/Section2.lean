/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Cited
public import LeanPool.GraphMinor.GM10.TangleLemmas

/-!
# Graph Minors XX, Section 2

This file proves (2.1), that a tangle in a subhypergraph induces a tangle in the whole hypergraph.

(2.1) is proved by checking the three tangle axioms, after seeing that intersecting a separation of
`G` with `G'` gives a separation of `G'` of no larger order.
-/

@[expose] public section

namespace GraphMinor.GM20

open Set GraphMinor.GM18 GraphMinor.GM10 Hypergraph

universe u v

variable {α : Type u} {β : Type v}

/-- Intersecting a separation of `G` with `G' ⊆ G` gives a separation of `G'`. -/
theorem isSeparation_inter {G G' A B : Hypergraph α β} (hG' : G' ≤ G) (h : G.IsSeparation A B) :
    G'.IsSeparation (A ∩ G') (B ∩ G') := by
  have hA : A ∩ G' ≤ G' := inter_le_right h.left_le hG'
  have hB : B ∩ G' ≤ G' := inter_le_right h.right_le hG'
  refine (isSeparation_iff_of_le hA hB).mpr ⟨?_, ?_, ?_⟩
  · refine Set.Subset.antisymm (fun v hv ↦ hv.elim (·.2) (·.2)) fun v hv ↦ ?_
    have : v ∈ A.vertexSet ∪ B.vertexSet := h.vertexSet_union ▸ hG'.vertexSet_subset hv
    exact this.elim (fun h ↦ Or.inl ⟨h, hv⟩) fun h ↦ Or.inr ⟨h, hv⟩
  · refine Set.Subset.antisymm (fun e he ↦ he.elim (·.2) (·.2)) fun e he ↦ ?_
    have : e ∈ A.edgeSet ∪ B.edgeSet := h.edgeSet_union ▸ hG'.edgeSet_subset he
    exact this.elim (fun h ↦ Or.inl ⟨h, he⟩) fun h ↦ Or.inr ⟨h, he⟩
  · refine Set.eq_empty_of_forall_notMem fun e he ↦ ?_
    exact Set.disjoint_left.mp h.disjoint_edgeSet he.1.1 he.2.1

/-- The order of `(A ∩ G', B ∩ G')` is at most that of `(A, B)`. -/
theorem separationOrder_inter_le {G' A B : Hypergraph α β} (hG : (A ∩ B).vertexSet.Finite) :
    separationOrder (A ∩ G') (B ∩ G') ≤ separationOrder A B :=
  Set.ncard_le_ncard (fun _ hv ↦ ⟨hv.1.1, hv.2.1⟩) hG

/-- Graph Minors XX, (2.1) (page 327): "Let $G$ be a hypergraph, let $G' \subseteq G$ and let
$\mathcal{T}'$ be a tangle in $G'$ of
order $\theta$. Let $\mathcal{T}$ be the set of all separations $(A, B)$ of $G$ of order $<
\theta$ such that $(A \cap G', B \cap G') \in \mathcal{T}'$. Then $\mathcal{T}$ is a tangle
in $G$ of order $\theta$." -/
theorem theorem_2_1_proof {G G' : Hypergraph α β} {θ : ℕ} (hG' : G' ≤ G)
    {𝒯' : Set (Hypergraph α β × Hypergraph α β)} (h𝒯' : IsTangle G' θ 𝒯') :
    IsTangle G θ {p | G.IsSeparation p.1 p.2 ∧ separationOrder p.1 p.2 < θ ∧
      (p.1 ∩ G', p.2 ∩ G') ∈ 𝒯'} where
  one_le := h𝒯'.one_le
  isSeparation _ _ h := h.1
  order_lt _ _ h := h.2.1
  axiom1 A B hsep hord := by
    have hfin : (A ∩ B).vertexSet.Finite := (A ∩ B).vertexSet_finite
    have hlt := (separationOrder_inter_le (G' := G') hfin).trans_lt hord
    rcases h𝒯'.axiom1 (isSeparation_inter hG' hsep) hlt with h | h
    · exact Or.inl ⟨hsep, hord, h⟩
    · refine Or.inr ⟨hsep.symm, by rwa [separationOrder_comm], h⟩
  axiom2 A₁ B₁ A₂ B₂ A₃ B₃ h₁ h₂ h₃ hU := by
    refine h𝒯'.axiom2 h₁.2.2 h₂.2.2 h₃.2.2 ?_
    have hA₁ := h₁.1.left_le
    have hA₂ := h₂.1.left_le
    have hA₃ := h₃.1.left_le
    have hV : A₁.vertexSet ∪ A₂.vertexSet ∪ A₃.vertexSet = G.vertexSet := by
      rw [← hU]; rfl
    have hE : A₁.edgeSet ∪ A₂.edgeSet ∪ A₃.edgeSet = G.edgeSet := by
      rw [← hU]; rfl
    have l₁ := inter_le_right hA₁ hG'
    have l₂ := inter_le_right hA₂ hG'
    have l₃ := inter_le_right hA₃ hG'
    refine eq_of_le_of_vertexSet_eq_of_edgeSet_eq (G := G') (union_le (union_le l₁ l₂) l₃) le_rfl
      ?_ ?_
    · apply Set.Subset.antisymm
      · rintro v (⟨hv | hv⟩ | hv) <;> exact hv.2
      · intro v hv
        have : v ∈ A₁.vertexSet ∪ A₂.vertexSet ∪ A₃.vertexSet :=
          hV ▸ hG'.vertexSet_subset hv
        rcases this with (h | h) | h
        · exact Or.inl (Or.inl ⟨h, hv⟩)
        · exact Or.inl (Or.inr ⟨h, hv⟩)
        · exact Or.inr ⟨h, hv⟩
    · apply Set.Subset.antisymm
      · rintro v (⟨hv | hv⟩ | hv) <;> exact hv.2
      · intro v hv
        have : v ∈ A₁.edgeSet ∪ A₂.edgeSet ∪ A₃.edgeSet :=
          hE ▸ hG'.edgeSet_subset hv
        rcases this with (h | h) | h
        · exact Or.inl (Or.inl ⟨h, hv⟩)
        · exact Or.inl (Or.inr ⟨h, hv⟩)
        · exact Or.inr ⟨h, hv⟩
  axiom3 A B h hV := by
    refine h𝒯'.axiom3 h.2.2 ?_
    refine Set.Subset.antisymm ?_ ?_
    · intro v hv
      exact (show v ∈ A.vertexSet ∧ v ∈ G'.vertexSet from hv).2
    · intro v hv
      exact ⟨hV ▸ hG'.vertexSet_subset hv, hv⟩

end GraphMinor.GM20
