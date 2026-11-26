/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs

/-!
# Extending the forward maps of a graph drawing

A graph drawing gives bijections only on actual vertices and
edges. Extend the maps off those sets with harmless default
values. On their supports they retain the isomorphism values
and are injective. This permits the tangle relabelling at the
end of XVI (4.2), without assuming injectivity on unused names.
-/

public section
namespace GraphMinor.GM16
open Set Graph Surface
universe u v w

/-- The forward vertex and edge maps of a graph drawing extend to
all names and are injective on the actual graph support. -/
theorem exists_graphDrawing_forward_maps {α : Type u} {β : Type v}
    {S : Type w} [TopologicalSpace S] [Nonempty S] {N : Graph α β}
    (Γ : GraphDrawing N S) :
    ∃ (f : α → S) (g : β → Set S),
      (∀ x : V(N), f x.val=(Γ.iso.vertexEquiv x).val) ∧
      (∀ e : E(N), g e.val=(Γ.iso.edgeEquiv e).val) ∧ InjOn f V(N) ∧ InjOn g E(N) := by
  classical
  let f : α → S := fun x => if hx : x ∈ V(N) then
    (Γ.iso.vertexEquiv ⟨x,hx⟩).val else Classical.choice ‹Nonempty S›
  let g : β → Set S := fun e => if he : e ∈ E(N) then
    (Γ.iso.edgeEquiv ⟨e,he⟩).val else ∅
  have hf (x : V(N)) : f x.val=(Γ.iso.vertexEquiv x).val := dite_eq_left x.property
  have hg (e : E(N)) : g e.val=(Γ.iso.edgeEquiv e).val := dite_eq_left e.property
  refine ⟨f,g,hf,hg,?_,?_⟩
  · intro x hx y hy he
    rw [hf ⟨x,hx⟩,hf ⟨y,hy⟩] at he
    exact congrArg Subtype.val (Γ.iso.vertexEquiv.injective (Subtype.ext he))
  · intro e he f hf hef
    rw [hg ⟨e,he⟩,hg ⟨f,hf⟩] at hef
    exact congrArg Subtype.val (Γ.iso.edgeEquiv.injective (Subtype.ext hef))

end GraphMinor.GM16
