/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM10.Defs

/-!
# Relabelling hypergraphs by injections

The grid contraction in XVI (4.2) changes the names of vertices and
edges. These lemmas carry hypergraphs and their separations through
injective maps. Keeping the maps explicit lets the grid tangle be
compared with the tangle in the contracted wall.
-/

@[expose] public section
namespace GraphMinor.GM16
open Set Function Hypergraph
universe u v u' v'
variable {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}

/-- Relabel the vertices and edges, with the incidence relation given by
its image under the two maps. -/
def imageHypergraph (f : α → α') (g : β → β') (A : Hypergraph α β) : Hypergraph α' β' where
  vertexSet := f '' A.vertexSet
  edgeSet := g '' A.edgeSet
  Inc e v := ∃ e₀ v₀, A.Inc e₀ v₀ ∧ g e₀ = e ∧ f v₀ = v
  vertex_mem_of_inc _ _ h := by
    obtain ⟨e, v, hinc, _, rfl⟩ := h
    exact mem_image_of_mem f (A.vertex_mem_of_inc hinc)
  edge_mem_of_inc _ _ h := by
    obtain ⟨e, v, hinc, rfl, _⟩ := h
    exact mem_image_of_mem g (A.edge_mem_of_inc hinc)
  vertexSet_finite := A.vertexSet_finite.image f
  edgeSet_finite := A.edgeSet_finite.image g

/-- Incidence at an image vertex and image edge can be read in the
original hypergraph. -/
theorem imageHypergraph_inc (f : α → α') (g : β → β')
    (hf : Injective f) (hg : Injective g) (A : Hypergraph α β) (e : β) (v : α) :
    (imageHypergraph f g A).Inc (g e) (f v) ↔ A.Inc e v := by
  constructor
  · rintro ⟨e₀, v₀, hi, he, hv⟩
    exact hg he ▸ hf hv ▸ hi
  · intro hi
    exact ⟨e, v, hi, rfl, rfl⟩

/-- Relabelling preserves unions. -/
theorem imageHypergraph_union (f : α → α') (g : β → β') (A B : Hypergraph α β) :
    imageHypergraph f g (A ∪ B) = imageHypergraph f g A ∪ imageHypergraph f g B := by
  apply Hypergraph.ext
  · exact image_union _ _ _
  · exact image_union _ _ _
  · funext e v
    apply propext
    constructor
    · rintro ⟨e₀, v₀, hi, he, hv⟩
      rcases hi with hi | hi
      · exact Or.inl ⟨e₀, v₀, hi, he, hv⟩
      · exact Or.inr ⟨e₀, v₀, hi, he, hv⟩
    · rintro (⟨e₀, v₀, hi, he, hv⟩ | ⟨e₀, v₀, hi, he, hv⟩)
      · exact ⟨e₀, v₀, Or.inl hi, he, hv⟩
      · exact ⟨e₀, v₀, Or.inr hi, he, hv⟩

/-- Injective relabelling preserves intersections. -/
theorem imageHypergraph_inter (f : α → α') (g : β → β')
    (hf : Injective f) (hg : Injective g) (A B : Hypergraph α β) :
    imageHypergraph f g (A ∩ B) = imageHypergraph f g A ∩ imageHypergraph f g B := by
  apply Hypergraph.ext
  · exact image_inter hf
  · exact image_inter hg
  · funext e v
    apply propext
    constructor
    · rintro ⟨e₀, v₀, hi, he, hv⟩
      exact ⟨⟨e₀, v₀, hi.1, he, hv⟩, ⟨e₀, v₀, hi.2, he, hv⟩⟩
    · rintro ⟨⟨e₀, v₀, hi, he, hv⟩, ⟨e₁, v₁, hj, he', hv'⟩⟩
      have heq := hg (he.trans he'.symm)
      have hvq := hf (hv.trans hv'.symm)
      subst e₁
      subst v₁
      exact ⟨e₀, v₀, ⟨hi, hj⟩, he, hv⟩

/-- Edge injectivity is enough to preserve the subhypergraph relation. -/
theorem imageHypergraph_mono (f : α → α') (g : β → β') (hg : Injective g)
    {A B : Hypergraph α β} (h : A ≤ B) : imageHypergraph f g A ≤ imageHypergraph f g B := by
  refine ⟨image_mono h.vertexSet_subset, image_mono h.edgeSet_subset, ?_⟩
  rintro _ ⟨e₀, he₀, rfl⟩
  ext v
  constructor
  · rintro ⟨e₁, v₁, hi, he, hv⟩
    have heq := hg he
    subst e₁
    have hia : A.Inc e₀ v₁ := Set.ext_iff.mp (h.ends_eq e₀ he₀) v₁ |>.mp hi
    exact ⟨e₀, v₁, hia, rfl, hv⟩
  · rintro ⟨e₁, v₁, hi, he, hv⟩
    have heq := hg he
    subst e₁
    have hib : B.Inc e₀ v₁ := Set.ext_iff.mp (h.ends_eq e₀ he₀) v₁ |>.mpr hi
    exact ⟨e₀, v₁, hib, rfl, hv⟩

/-- Injective relabelling preserves separations. -/
theorem imageHypergraph_isSeparation (f : α → α') (g : β → β')
    (hf : Injective f) (hg : Injective g) {G A B : Hypergraph α β}
    (h : G.IsSeparation A B) :
    (imageHypergraph f g G).IsSeparation (imageHypergraph f g A) (imageHypergraph f g B) := by
  refine ⟨imageHypergraph_mono f g hg h.left_le, imageHypergraph_mono f g hg h.right_le, ?_, ?_⟩
  · rw [← imageHypergraph_union, h.union_eq]
  · rw [← imageHypergraph_inter f g hf hg]
    change g '' (A ∩ B).edgeSet = ∅
    rw [h.edgeSet_inter_eq, image_empty]

/-- The order of a separation is unchanged by injective relabelling. -/
theorem imageHypergraph_separationOrder (f : α → α') (g : β → β') (hf : Injective f)
    (A B : Hypergraph α β) :
    separationOrder (imageHypergraph f g A) (imageHypergraph f g B) = separationOrder A B := by
  change (f '' A.vertexSet ∩ f '' B.vertexSet).ncard = (A.vertexSet ∩ B.vertexSet).ncard
  rw [← image_inter hf]
  exact ncard_image_of_injective _ hf

/-- Injective relabelling distinguishes hypergraphs. -/
theorem imageHypergraph_injective (f : α → α') (g : β → β')
    (hf : Injective f) (hg : Injective g) : Injective (imageHypergraph f g) := by
  intro A B h
  apply Hypergraph.ext
  · exact hf.image_injective (congrArg Hypergraph.vertexSet h)
  · exact hg.image_injective (congrArg Hypergraph.edgeSet h)
  · funext e v
    apply propext
    rw [← imageHypergraph_inc f g hf hg A e v, h, imageHypergraph_inc f g hf hg B e v]

end GraphMinor.GM16
