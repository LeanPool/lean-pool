/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.HypergraphImageTangle

/-!
# Reflecting separations and tangles through injections

Injective relabelling neither creates subhypergraphs nor creates
separations. It also reflects the three tangle axioms. These facts
allow the proof of XVI (4.2) to discard extra names introduced while
relabelling a minor.
-/

public section
namespace GraphMinor.GM16
open Set Function Hypergraph GM10
universe u v u' v'
variable {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}

/-- An injective image reflects the subhypergraph relation. -/
theorem le_of_imageHypergraph_le (f : α → α') (g : β → β')
    (hf : Injective f) (hg : Injective g) {A G : Hypergraph α β}
    (h : imageHypergraph f g A ≤ imageHypergraph f g G) : A ≤ G := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, heq⟩ := h.vertexSet_subset (mem_image_of_mem f hx)
    exact hf heq ▸ hy
  · intro e he
    obtain ⟨d, hd, heq⟩ := h.edgeSet_subset (mem_image_of_mem g he)
    exact hg heq ▸ hd
  · intro e he
    ext x
    change G.Inc e x ↔ A.Inc e x
    rw [← imageHypergraph_inc f g hf hg G e x, ← imageHypergraph_inc f g hf hg A e x]
    exact Set.ext_iff.mp (h.ends_eq (g e) (mem_image_of_mem g he)) (f x)

/-- An injective image reflects separations. -/
theorem isSeparation_of_imageHypergraph (f : α → α') (g : β → β')
    (hf : Injective f) (hg : Injective g) {G A B : Hypergraph α β}
    (h : (imageHypergraph f g G).IsSeparation (imageHypergraph f g A) (imageHypergraph f g B)) :
    G.IsSeparation A B := by
  refine ⟨le_of_imageHypergraph_le f g hf hg h.left_le,
    le_of_imageHypergraph_le f g hf hg h.right_le, ?_, ?_⟩
  · apply imageHypergraph_injective f g hf hg
    rw [imageHypergraph_union]
    exact h.union_eq
  · have hImg : g '' (A ∩ B).edgeSet = ∅ := by
      change (imageHypergraph f g (A ∩ B)).edgeSet = ∅
      rw [imageHypergraph_inter f g hf hg]
      exact h.edgeSet_inter_eq
    exact image_eq_empty.mp hImg

/-- If an injective image of a set of separations is a tangle, the
original set is a tangle of the same order. -/
theorem isTangle_of_imageHypergraphTangle (f : α → α') (g : β → β')
    (hf : Injective f) (hg : Injective g) {G : Hypergraph α β} {θ : ℕ}
    {T : Set (Hypergraph α β × Hypergraph α β)}
    (hT : IsTangle (imageHypergraph f g G) θ (imageHypergraphTangle f g T)) : IsTangle G θ T := by
  have hMem {A B : Hypergraph α β} (hp : (A,B) ∈ T) :
      (imageHypergraph f g A, imageHypergraph f g B) ∈ imageHypergraphTangle f g T
        := ⟨(A,B), hp, rfl⟩
  refine ⟨hT.one_le, ?_, ?_, ?_, ?_, ?_⟩
  · intro A B hp
    exact isSeparation_of_imageHypergraph f g hf hg (hT.isSeparation (hMem hp))
  · intro A B hp
    have hOrd := hT.order_lt (hMem hp)
    rwa [imageHypergraph_separationOrder f g hf] at hOrd
  · intro A B hSep hOrd
    have hSep' := imageHypergraph_isSeparation f g hf hg hSep
    have hOrd' : separationOrder (imageHypergraph f g A) (imageHypergraph f g B) < θ := by
      rwa [imageHypergraph_separationOrder f g hf]
    rcases hT.axiom1 hSep' hOrd' with hm | hm
    · exact Or.inl ((mem_imageHypergraphTangle f g hf hg A B).mp hm)
    · exact Or.inr ((mem_imageHypergraphTangle f g hf hg B A).mp hm)
  · intro A₁ B₁ A₂ B₂ A₃ B₃ h₁ h₂ h₃ hUnion
    apply hT.axiom2 (hMem h₁) (hMem h₂) (hMem h₃)
    rw [← imageHypergraph_union, ← imageHypergraph_union, hUnion]
  · intro A B hp hV
    exact hT.axiom3 (hMem hp) (congrArg (fun X : Set α => f '' X) hV)

end GraphMinor.GM16
