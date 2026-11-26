/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.HypergraphPreimage

/-!
# Tangles under injective relabelling

Relabel both sides of every separation. The first tangle axiom follows
by taking the preimage of a separation. The other two axioms follow
from preservation of unions and injectivity on vertex sets. This lets
the proof of XVI (4.2) use the grid tangle with the edge names of the
contracted wall.
-/

@[expose] public section
namespace GraphMinor.GM16
open Set Function Hypergraph GM10
universe u v u' v'
variable {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}

/-- Relabel every separation in a set of separations. -/
def imageHypergraphTangle (f : α → α') (g : β → β')
    (T : Set (Hypergraph α β × Hypergraph α β)) :
    Set (Hypergraph α' β' × Hypergraph α' β') :=
  (fun p => (imageHypergraph f g p.1, imageHypergraph f g p.2)) '' T

/-- The image of a tangle under injective vertex and edge maps is a
tangle of the same order. -/
theorem isTangle_imageHypergraphTangle (f : α → α') (g : β → β')
    (hf : Injective f) (hg : Injective g) {G : Hypergraph α β} {θ : ℕ}
    {T : Set (Hypergraph α β × Hypergraph α β)} (hT : IsTangle G θ T) :
    IsTangle (imageHypergraph f g G) θ (imageHypergraphTangle f g T) := by
  refine ⟨hT.one_le, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ _ ⟨⟨A, B⟩, hp, heq⟩
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp heq
    exact imageHypergraph_isSeparation f g hf hg (hT.isSeparation hp)
  · rintro _ _ ⟨⟨A, B⟩, hp, heq⟩
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp heq
    change separationOrder (imageHypergraph f g A) (imageHypergraph f g B) < θ
    rw [imageHypergraph_separationOrder f g hf]
    exact hT.order_lt hp
  · intro A B hSep hOrd
    let A₀ := preimageHypergraph f g G A
    let B₀ := preimageHypergraph f g G B
    have hSep₀ : G.IsSeparation A₀ B₀ := preimageHypergraph_isSeparation f g hf hg hSep
    have hOrd₀ : separationOrder A₀ B₀ < θ := by
      rw [preimageHypergraph_separationOrder f g hf hSep.left_le hSep.right_le]
      exact hOrd
    have hA : imageHypergraph f g A₀ = A := imageHypergraph_preimage f g hSep.left_le
    have hB : imageHypergraph f g B₀ = B := imageHypergraph_preimage f g hSep.right_le
    rcases hT.axiom1 hSep₀ hOrd₀ with hm | hm
    · exact Or.inl ⟨(A₀, B₀), hm, Prod.ext hA hB⟩
    · exact Or.inr ⟨(B₀, A₀), hm, Prod.ext hB hA⟩
  · rintro _ _ _ _ _ _ ⟨⟨A₁, B₁⟩, hp₁, heq₁⟩
      ⟨⟨A₂, B₂⟩, hp₂, heq₂⟩ ⟨⟨A₃, B₃⟩, hp₃, heq₃⟩ hUnion
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp heq₁
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp heq₂
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp heq₃
    apply hT.axiom2 hp₁ hp₂ hp₃
    apply imageHypergraph_injective f g hf hg
    rw [imageHypergraph_union, imageHypergraph_union]
    exact hUnion
  · rintro _ _ ⟨⟨A, B⟩, hp, heq⟩ hV
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp heq
    exact hT.axiom3 hp (hf.image_injective hV)

/-- Injective relabelling also reflects membership of the tangle. -/
theorem mem_imageHypergraphTangle (f : α → α') (g : β → β')
    (hf : Injective f) (hg : Injective g)
    {T : Set (Hypergraph α β × Hypergraph α β)} (A B : Hypergraph α β) :
    (imageHypergraph f g A, imageHypergraph f g B) ∈ imageHypergraphTangle f g T ↔
      (A, B) ∈ T := by
  constructor
  · rintro ⟨⟨A₀, B₀⟩, hp, heq⟩
    obtain ⟨hA, hB⟩ := Prod.ext_iff.mp heq
    have hA₀ := imageHypergraph_injective f g hf hg hA
    have hB₀ := imageHypergraph_injective f g hf hg hB
    exact hA₀ ▸ hB₀ ▸ hp
  · intro hp
    exact ⟨(A, B), hp, rfl⟩

end GraphMinor.GM16
