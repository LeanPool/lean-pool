/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.HypergraphImage

/-!
# Recovering subhypergraphs after relabelling

A subhypergraph of an injective image has a unique preimage in the
original hypergraph. This applies to both sides of a separation and
preserves its order. These facts supply the inverse operation needed
to transport the grid tangle in XVI (4.2).
-/

@[expose] public section
namespace GraphMinor.GM16
open Set Function Hypergraph
universe u v u' v'
variable {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}

/-- The preimage of a hypergraph, restricted to the vertices and edges
of a fixed finite hypergraph. -/
def preimageHypergraph (f : α → α') (g : β → β') (G : Hypergraph α β)
    (B : Hypergraph α' β') : Hypergraph α β where
  vertexSet := {v ∈ G.vertexSet | f v ∈ B.vertexSet}
  edgeSet := {e ∈ G.edgeSet | g e ∈ B.edgeSet}
  Inc e v := B.Inc (g e) (f v) ∧ v ∈ G.vertexSet ∧ e ∈ G.edgeSet
  vertex_mem_of_inc _ _ h := ⟨h.2.1, B.vertex_mem_of_inc h.1⟩
  edge_mem_of_inc _ _ h := ⟨h.2.2, B.edge_mem_of_inc h.1⟩
  vertexSet_finite := G.vertexSet_finite.subset fun _ h => h.1
  edgeSet_finite := G.edgeSet_finite.subset fun _ h => h.1

/-- A subhypergraph of the image pulls back to a subhypergraph of the
original hypergraph. -/
theorem preimageHypergraph_le (f : α → α') (g : β → β')
    (hf : Injective f) (hg : Injective g) {G : Hypergraph α β} {B : Hypergraph α' β'}
    (hB : B ≤ imageHypergraph f g G) : preimageHypergraph f g G B ≤ G := by
  refine ⟨fun _ h => h.1, fun _ h => h.1, ?_⟩
  intro e he
  ext v
  constructor
  · intro hi
    have him : (imageHypergraph f g G).Inc (g e) (f v) := ⟨e, v, hi, rfl, rfl⟩
    have hib : B.Inc (g e) (f v) := Set.ext_iff.mp (hB.ends_eq (g e) he.2) (f v) |>.mp him
    exact ⟨hib, G.vertex_mem_of_inc hi, he.1⟩
  · rintro ⟨hib, _, _⟩
    have him : (imageHypergraph f g G).Inc (g e) (f v) :=
      Set.ext_iff.mp (hB.ends_eq (g e) he.2) (f v) |>.mpr hib
    exact (imageHypergraph_inc f g hf hg G e v).mp him

/-- Every subhypergraph of the image is the image of its preimage. -/
theorem imageHypergraph_preimage (f : α → α') (g : β → β')
    {G : Hypergraph α β} {B : Hypergraph α' β'} (hB : B ≤ imageHypergraph f g G) :
    imageHypergraph f g (preimageHypergraph f g G B) = B := by
  apply Hypergraph.ext
  · ext v
    constructor
    · rintro ⟨v₀, ⟨_, hv⟩, rfl⟩
      exact hv
    · intro hv
      obtain ⟨v₀, hv₀, rfl⟩ := hB.vertexSet_subset hv
      exact ⟨v₀, ⟨hv₀, hv⟩, rfl⟩
  · ext e
    constructor
    · rintro ⟨e₀, ⟨_, he⟩, rfl⟩
      exact he
    · intro he
      obtain ⟨e₀, he₀, rfl⟩ := hB.edgeSet_subset he
      exact ⟨e₀, ⟨he₀, he⟩, rfl⟩
  · funext e v
    apply propext
    constructor
    · rintro ⟨e₀, v₀, ⟨hi, _, _⟩, rfl, rfl⟩
      exact hi
    · intro hi
      obtain ⟨e₀, he₀, rfl⟩ := hB.edgeSet_subset (B.edge_mem_of_inc hi)
      obtain ⟨v₀, hv₀, rfl⟩ := hB.vertexSet_subset (B.vertex_mem_of_inc hi)
      exact ⟨e₀, v₀, ⟨hi, hv₀, he₀⟩, rfl, rfl⟩

/-- The preimage of a separation of the image is a separation. -/
theorem preimageHypergraph_isSeparation (f : α → α') (g : β → β')
    (hf : Injective f) (hg : Injective g) {G : Hypergraph α β} {A B : Hypergraph α' β'}
    (h : (imageHypergraph f g G).IsSeparation A B) :
    G.IsSeparation (preimageHypergraph f g G A) (preimageHypergraph f g G B) := by
  refine ⟨preimageHypergraph_le f g hf hg h.left_le,
    preimageHypergraph_le f g hf hg h.right_le, ?_, ?_⟩
  · apply imageHypergraph_injective f g hf hg
    rw [imageHypergraph_union, imageHypergraph_preimage f g h.left_le,
      imageHypergraph_preimage f g h.right_le, h.union_eq]
  · apply eq_empty_iff_forall_notMem.mpr
    intro e he
    have hge : g e ∈ (A ∩ B).edgeSet := ⟨he.1.2, he.2.2⟩
    rw [h.edgeSet_inter_eq] at hge
    exact hge

/-- Separation order is unchanged on passing to the preimage. -/
theorem preimageHypergraph_separationOrder (f : α → α') (g : β → β')
    (hf : Injective f) {G : Hypergraph α β} {A B : Hypergraph α' β'}
    (hA : A ≤ imageHypergraph f g G) (hB : B ≤ imageHypergraph f g G) :
    separationOrder (preimageHypergraph f g G A) (preimageHypergraph f g G B) =
      separationOrder A B := by
  have h := imageHypergraph_separationOrder f g hf
    (preimageHypergraph f g G A) (preimageHypergraph f g G B)
  rw [imageHypergraph_preimage f g hA, imageHypergraph_preimage f g hB] at h
  exact h.symm

end GraphMinor.GM16
