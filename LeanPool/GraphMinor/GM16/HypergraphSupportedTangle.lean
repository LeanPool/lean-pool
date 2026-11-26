/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.HypergraphImageTangle
import LeanPool.GraphMinor.GM16.HypergraphImageReflection
import LeanPool.GraphMinor.GM16.HypergraphImageComposition

/-!
# Relabelling a tangle on its actual vertices and edges

Unused names must impose no restriction on a minor's edge map.
Augment the vertex and edge maps by sending unused names to separate
summands. The augmented maps are injective everywhere and transport
the tangle. The image uses only the left summands, so reflection
removes the augmentation. This supplies the relabelling step for the
wall minor of an arbitrary graph in XVI (4.2).
-/

public section
namespace GraphMinor.GM16
open Set Function Hypergraph GM10
universe u v u' v'
variable {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}

/-- Relabel a tangle using maps injective on the actual vertex and
edge sets. Values on unused names are immaterial. -/
theorem isTangle_imageHypergraphTangle_on (f : α → α') (g : β → β')
    {G : Hypergraph α β} (hf : InjOn f G.vertexSet) (hg : InjOn g G.edgeSet)
    {θ : ℕ} {T : Set (Hypergraph α β × Hypergraph α β)} (hT : IsTangle G θ T) :
    IsTangle (imageHypergraph f g G) θ (imageHypergraphTangle f g T) := by
  let F := supportedInjection G.vertexSet f
  let E := supportedInjection G.edgeSet g
  let inV : α' → Sum α' α := Sum.inl
  let inE : β' → Sum β' β := Sum.inl
  have hEq {A : Hypergraph α β} (hA : A ≤ G) :
      imageHypergraph inV inE (imageHypergraph f g A) = imageHypergraph F E A := by
    rw [imageHypergraph_comp]
    apply imageHypergraph_congr_on
    · intro x hx
      exact (supportedInjection_apply f (hA.vertexSet_subset hx)).symm
    · intro e he
      exact (supportedInjection_apply g (hA.edgeSet_subset he)).symm
  have hG : imageHypergraph inV inE (imageHypergraph f g G) = imageHypergraph F E G := hEq le_rfl
  have hTImage : imageHypergraphTangle inV inE (imageHypergraphTangle f g T) =
      imageHypergraphTangle F E T := by
    unfold imageHypergraphTangle
    rw [image_image]
    apply Set.image_congr
    intro p hp
    exact Prod.ext (hEq (hT.isSeparation hp).left_le) (hEq (hT.isSeparation hp).right_le)
  have hAug := isTangle_imageHypergraphTangle F E
    (supportedInjection_injective f hf) (supportedInjection_injective g hg) hT
  rw [← hG, ← hTImage] at hAug
  exact isTangle_of_imageHypergraphTangle inV inE Sum.inl_injective Sum.inl_injective hAug

end GraphMinor.GM16
