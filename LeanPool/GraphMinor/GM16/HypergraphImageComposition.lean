/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.HypergraphImage

/-!
# Composing and restricting relabellings

Images depend only on the maps on actual vertices and edges.
Relabellings also compose. A map that is injective only on those
actual elements can be made globally injective by sending unused
names to a separate summand. This avoids imposing conditions on
unused edge names in XVI (4.2).
-/

@[expose] public section
namespace GraphMinor.GM16
open Set Function Hypergraph
universe u v u' v' u'' v''
variable {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}

/-- Equal maps on the vertices and edges give the same image. -/
theorem imageHypergraph_congr_on (f f' : α → α') (g g' : β → β') (A : Hypergraph α β)
    (hf : ∀ x ∈ A.vertexSet, f x = f' x) (hg : ∀ e ∈ A.edgeSet, g e = g' e) :
    imageHypergraph f g A = imageHypergraph f' g' A := by
  apply Hypergraph.ext
  · exact Set.image_congr hf
  · exact Set.image_congr hg
  · funext e v
    apply propext
    constructor
    · rintro ⟨e₀, v₀, hi, he, hv⟩
      exact ⟨e₀, v₀, hi, (hg e₀ (A.edge_mem_of_inc hi)).symm.trans he,
        (hf v₀ (A.vertex_mem_of_inc hi)).symm.trans hv⟩
    · rintro ⟨e₀, v₀, hi, he, hv⟩
      exact ⟨e₀, v₀, hi, (hg e₀ (A.edge_mem_of_inc hi)).trans he,
        (hf v₀ (A.vertex_mem_of_inc hi)).trans hv⟩

/-- Relabelling a relabelled hypergraph composes the maps. -/
theorem imageHypergraph_comp {α'' : Type u''} {β'' : Type v''}
    (f : α → α') (g : β → β') (f' : α' → α'') (g' : β' → β'') (A : Hypergraph α β) :
    imageHypergraph f' g' (imageHypergraph f g A) = imageHypergraph (f' ∘ f) (g' ∘ g) A := by
  apply Hypergraph.ext
  · exact Set.image_image _ _ _
  · exact Set.image_image _ _ _
  · funext e v
    apply propext
    constructor
    · rintro ⟨e₁, v₁, ⟨e₀, v₀, hi, he₀, hv₀⟩, he₁, hv₁⟩
      exact ⟨e₀, v₀, hi, congrArg g' he₀ |>.trans he₁, congrArg f' hv₀ |>.trans hv₁⟩
    · rintro ⟨e₀, v₀, hi, he, hv⟩
      exact ⟨g e₀, f v₀, ⟨e₀, v₀, hi, rfl, rfl⟩, he, hv⟩

/-- Keep the given map on a set and send unused names to a separate
summand, so they cannot collide with images of actual elements. -/
noncomputable def supportedInjection (S : Set α) (f : α → α') : α → Sum α' α := by
  classical
  exact fun x => if x ∈ S then Sum.inl (f x) else Sum.inr x

/-- On the specified set the augmented map is the given map followed
by the left inclusion. -/
theorem supportedInjection_apply {S : Set α} (f : α → α') {x : α} (hx : x ∈ S) :
    supportedInjection S f x = Sum.inl (f x) := by
  classical
  simp only [supportedInjection, ite_eq_left hx]

/-- Injectivity on the specified set makes the augmented map globally
injective. -/
theorem supportedInjection_injective {S : Set α} (f : α → α') (hf : InjOn f S) :
    Injective (supportedInjection S f) := by
  classical
  intro x y hEq
  unfold supportedInjection at hEq
  by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
  · rw [ite_eq_left hx, ite_eq_left hy] at hEq
    exact hf hx hy (Sum.inl.inj hEq)
  · rw [ite_eq_left hx, ite_eq_right hy] at hEq
    cases hEq
  · rw [ite_eq_right hx, ite_eq_left hy] at hEq
    cases hEq
  · rw [ite_eq_right hx, ite_eq_right hy] at hEq
    exact Sum.inr.inj hEq

end GraphMinor.GM16
