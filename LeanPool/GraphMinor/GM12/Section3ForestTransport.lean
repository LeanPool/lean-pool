/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3AmbientTransfer
public import LeanPool.GraphMinor.GM07.Defs
import LeanPool.GraphMinor.GM11.Walks
import LeanPool.GraphMinor.GM12.Section3SubspaceArcs

/-!
# Forests under inclusion of a closed subspace

The auxiliary-disc step in XII (3.2), page 247, reads the same
forest in a smaller surface. An injective map of vertices and edges
preserves simple closed walks and their lengths. Thus a forest in
the ambient surface stays a forest when its support is read in a
subspace. The walk transport also keeps boundary connections.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

private theorem exists_walk_of_link_map
    {α β α' β' : Type*} {G : Graph α β} {G' : Graph α' β'}
    (f : α → α') (g : β → β')
    (hV : ∀ x ∈ G.vertexSet, f x ∈ G'.vertexSet)
    (hL : ∀ {e x y}, G.IsLink e x y → G'.IsLink (g e) (f x) (f y))
    {x y : α} (W : GraphWalk G x y) :
    ∃ W' : GraphWalk G' (f x) (f y), W'.support = W.support.map f ∧
      W'.edges = W.edges.map g := by
  induction W with
  | nil hx => exact ⟨.nil (hV _ hx), rfl, rfl⟩
  | cons he R ih =>
    obtain ⟨R', hs, he'⟩ := ih
    exact ⟨.cons (hL he) R', congrArg (List.cons _) hs, congrArg (List.cons _) he'⟩

/-- An injective map of vertices and edges into a forest has no
nontrivial simple closed walks. -/
theorem isGraphForest_of_injective_link_map
    {α β α' β' : Type*} {G : Graph α β} {G' : Graph α' β'}
    (f : α → α') (g : β → β') (hf : Function.Injective f) (hg : Function.Injective g)
    (hV : ∀ x ∈ G.vertexSet, f x ∈ G'.vertexSet)
    (hL : ∀ {e x y}, G.IsLink e x y → G'.IsLink (g e) (f x) (f y))
    (hforest : IsGraphForest G') : IsGraphForest G := by
  intro x W hW
  obtain ⟨W', hs, he⟩ := exists_walk_of_link_map f g hV hL W
  have hsmap : (W.support.map f).tail = W.support.tail.map f := by
    cases W.support <;> rfl
  have hW' : W'.IsSimpleClosed := by
    constructor
    · rw [hs, hsmap]
      exact hW.1.map hf
    · rw [he]
      exact hW.2.map hg
  have hlen := hforest (f x) W' hW'
  change W'.edges.length = 0 at hlen
  rw [he, List.length_map] at hlen
  exact hlen

/-- Including a drawing restricted to a closed subspace recovers
its original vertex and edge sets. -/
theorem drawingFromClosedSubspace_drawingInSubspace
    {S : Type*} [TopologicalSpace S]
    (Γ : Drawing S) (C : Set S) (hC : IsClosed C) (hUC : Γ.U ⊆ C) :
    drawingFromClosedSubspace C hC (drawingInSubspace Γ C hUC) = Γ := by
  apply Drawing.ext_of_V_E
  · rw [drawingFromClosedSubspace_V, drawingInSubspace_V, Subtype.image_preimage_coe]
    exact inter_eq_right.mpr (Γ.V_subset_U.trans hUC)
  · rw [drawingFromClosedSubspace_E, drawingInSubspace_E, image_image]
    have heq : ∀ e ∈ Γ.E, (Subtype.val : C → S) '' (Subtype.val ⁻¹' e) = e := by
      intro e he
      rw [Subtype.image_preimage_coe]
      exact inter_eq_right.mpr (fun _ hx => hUC (he.2.1 hx).1)
    ext e
    constructor
    · rintro ⟨e', he', he'e⟩
      change (Subtype.val : C → S) '' (Subtype.val ⁻¹' e') = e at he'e
      rw [heq e' he'] at he'e
      exact he'e ▸ he'
    · intro he
      exact ⟨e, he, heq e he⟩

/-- A link lifts when the entire drawing is read in a subspace. -/
theorem isLink_drawingInSubspace
    {S : Type*} [TopologicalSpace S] (Γ : Drawing S)
    (C : Set S) (hUC : Γ.U ⊆ C) {e : Set S} {x y : C}
    (hl : Γ.toGraph.IsLink e x.val y.val) :
    (drawingInSubspace Γ C hUC).toGraph.IsLink (Subtype.val ⁻¹' e) x y := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [drawingInSubspace_E]
    exact ⟨e, hl.1, rfl⟩
  · rw [drawingInSubspace_V]
    exact hl.2.1
  · rw [drawingInSubspace_V]
    exact hl.2.2.1
  · rw [drawingInSubspace_V, closure_subtype_preimage
      (fun z hz => hUC (hl.1.2.1 hz).1), ← preimage_inter, hl.2.2.2]
    ext z
    simp only [mem_preimage, mem_insert_iff, mem_singleton_iff, Subtype.ext_iff]

/-- A walk lifts to the subspace containing the drawing support. -/
theorem exists_walk_drawingInSubspace
    {S : Type*} [TopologicalSpace S] (Γ : Drawing S)
    (C : Set S) (hUC : Γ.U ⊆ C) {x y : S} (W : GraphWalk Γ.toGraph x y)
    (hx : x ∈ C) (hy : y ∈ C) :
    Nonempty (GraphWalk (drawingInSubspace Γ C hUC).toGraph ⟨x, hx⟩ ⟨y, hy⟩) := by
  induction W with
  | nil hxV =>
    exact ⟨.nil (by
      change (⟨_, hx⟩ : C) ∈ (drawingInSubspace Γ C hUC).V
      rw [drawingInSubspace_V]
      exact hxV)⟩
  | @cons x z y e hl R ih =>
    have hz : z ∈ C := hUC (Γ.V_subset_U hl.2.2.1)
    obtain ⟨R'⟩ := ih hz hy
    exact ⟨.cons (isLink_drawingInSubspace Γ C hUC hl) R'⟩

/-- Reading a drawing in a closed subspace preserves graph
connections between its vertices. -/
theorem walk_drawingInSubspace_iff
    {S : Type*} [TopologicalSpace S]
    (Γ : Drawing S) (C : Set S) (hC : IsClosed C) (hUC : Γ.U ⊆ C) {x y : C} :
    Nonempty (GraphWalk (drawingInSubspace Γ C hUC).toGraph x y) ↔
      Nonempty (GraphWalk Γ.toGraph x.val y.val) := by
  constructor
  · rintro ⟨W⟩
    have h := exists_walk_drawingFromClosedSubspace C hC (drawingInSubspace Γ C hUC) W
    rwa [drawingFromClosedSubspace_drawingInSubspace Γ C hC hUC] at h
  · rintro ⟨W⟩
    exact exists_walk_drawingInSubspace Γ C hUC W x.property y.property

/-- A forest remains a forest on reading its support in a closed
subspace. This supplies the no-circuit part of the auxiliary-disc
step in XII (3.2), page 247. -/
theorem isGraphForest_drawingInSubspace
    {S : Type*} [TopologicalSpace S]
    {Γ : Drawing S} (hforest : IsGraphForest Γ.toGraph)
    (C : Set S) (hC : IsClosed C) (hUC : Γ.U ⊆ C) :
    IsGraphForest (drawingInSubspace Γ C hUC).toGraph := by
  let H := drawingInSubspace Γ C hUC
  have hback := drawingFromClosedSubspace_drawingInSubspace Γ C hC hUC
  apply isGraphForest_of_injective_link_map (G' := Γ.toGraph) (Subtype.val : C → S)
    (Set.image Subtype.val)
    Subtype.val_injective (Set.image_injective.mpr Subtype.val_injective)
  · intro x hx
    change x ∈ (drawingInSubspace Γ C hUC).V at hx
    rw [drawingInSubspace_V] at hx
    exact hx
  · intro e x y hl
    have h := isLink_drawingFromClosedSubspace C hC H hl
    rw [hback] at h
    exact h
  · exact hforest

end GraphMinor.GM12
