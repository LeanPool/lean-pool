/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Defs
import LeanPool.GraphMinor.GM16.GraphIsoEdgeEnds

/-!
# A drawing isomorphism gives a span embedding

Invert the vertex and edge equivalences of a drawing of a
subgraph. Extend these maps arbitrarily off the actual vertices
and edges. Their bijections and incidence preservation give the
span embedding, whose image is exactly the original subgraph.
This identifies the drawn subdivision as a subgraph of the
original graph at the end of XVI (4.2).
-/

public section
namespace GraphMinor.GM16
open Set Graph Topology Surface GM14
universe u v w

private theorem drawing_inc_iff_of_mem {S : Type w} [TopologicalSpace S]
    {D : Drawing S} {e : Set S} (he : e ∈ D.E) {x : S} (hx : x ∈ D.V) :
    D.toGraph.Inc e x ↔ x ∈ closure e := by
  obtain ⟨a,b,hLink⟩ := D.toGraph.exists_isLink_of_mem_edgeSet he
  constructor
  · rintro ⟨y,hy⟩
    have hxPair : x ∈ closure e ∩ D.V := hy.2.2.2.symm ▸ mem_insert x {y}
    exact hxPair.1
  · intro hxCl
    have hxPair : x ∈ ({a,b} : Set S) := hLink.2.2.2 ▸ ⟨hxCl,hx⟩
    rcases hxPair with h | h
    · exact ⟨b,h.symm ▸ hLink⟩
    · rw [mem_singleton_iff] at h
      exact ⟨a,h.symm ▸ hLink.symm⟩

/-- A graph drawing of a subgraph gives a span embedding with exactly
that image graph and the inverse isomorphism maps on its support. -/
theorem exists_spanEmbedding_of_graphDrawing
    {α : Type u} {β : Type v} [Nonempty α] [Nonempty β]
    {S : Type w} [TopologicalSpace S] {N G : Graph α β} (hNG : N ≤ G)
    (Γ : GraphDrawing N S) :
    ∃ η : SpanEmbedding Γ.drawing G, η.imageGraph=N ∧
      (∀ x : Γ.drawing.V, η.vMap x.val=(Γ.iso.vertexEquiv.symm x).val) ∧
      (∀ e : Γ.drawing.E, η.eMap e.val=(Γ.iso.edgeEquiv.symm e).val) := by
  classical
  let vm : S → α := fun x => if hx : x ∈ Γ.drawing.V then
    (Γ.iso.vertexEquiv.symm ⟨x,hx⟩).val else Classical.choice ‹Nonempty α›
  let em : Set S → β := fun e => if he : e ∈ Γ.drawing.E then
    (Γ.iso.edgeEquiv.symm ⟨e,he⟩).val else Classical.choice ‹Nonempty β›
  have hv (x : Γ.drawing.V) : vm x.val=(Γ.iso.vertexEquiv.symm x).val := dite_eq_left x.property
  have he (e : Γ.drawing.E) : em e.val=(Γ.iso.edgeEquiv.symm e).val := dite_eq_left e.property
  have hVBij : BijOn vm Γ.drawing.V V(N) := by
    refine ⟨?_,?_,?_⟩
    · intro x hx
      rw [hv ⟨x,hx⟩]
      exact (Γ.iso.vertexEquiv.symm ⟨x,hx⟩).property
    · intro x hx y hy hxy
      rw [hv ⟨x,hx⟩,hv ⟨y,hy⟩] at hxy
      exact congrArg Subtype.val (Γ.iso.vertexEquiv.symm.injective (Subtype.ext hxy))
    · intro x hx
      let y := Γ.iso.vertexEquiv ⟨x,hx⟩
      refine ⟨y.val,y.property,?_⟩
      rw [hv y]
      exact congrArg Subtype.val (Γ.iso.vertexEquiv.symm_apply_apply ⟨x,hx⟩)
  have hEBij : BijOn em Γ.drawing.E E(N) := by
    refine ⟨?_,?_,?_⟩
    · intro e he₀
      rw [he ⟨e,he₀⟩]
      exact (Γ.iso.edgeEquiv.symm ⟨e,he₀⟩).property
    · intro e he₀ f hf hef
      rw [he ⟨e,he₀⟩,he ⟨f,hf⟩] at hef
      exact congrArg Subtype.val (Γ.iso.edgeEquiv.symm.injective (Subtype.ext hef))
    · intro e he₀
      let f := Γ.iso.edgeEquiv ⟨e,he₀⟩
      refine ⟨f.val,f.property,?_⟩
      rw [he f]
      exact congrArg Subtype.val (Γ.iso.edgeEquiv.symm_apply_apply ⟨e,he₀⟩)
  have hInc (e : Set S) (he₀ : e ∈ Γ.drawing.E) (x : S) (hx : x ∈ Γ.drawing.V) :
      N.Inc (em e) (vm x) ↔ x ∈ closure e := by
    rw [he ⟨e,he₀⟩,hv ⟨x,hx⟩]
    have h := graphIso_inc_iff Γ.iso (Γ.iso.edgeEquiv.symm ⟨e,he₀⟩)
      (Γ.iso.vertexEquiv.symm ⟨x,hx⟩)
    simp only [Equiv.apply_symm_apply] at h
    exact h.trans (drawing_inc_iff_of_mem he₀ hx)
  exact ⟨⟨N,vm,em,hNG,hVBij,hEBij,hInc⟩,rfl,hv,he⟩

end GraphMinor.GM16
