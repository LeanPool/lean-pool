/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.Surface.ArcTools
import LeanPool.GraphMinor.Surface.SurfaceGraph

/-!
# Splitting the source edges at their crossings

In XII (4.5), claim (1), page 253, every subdivided edge has
one crossing. Split its simple arc at that point and orient
both halves from their original vertex to the crossing. Each
half contains only its own original vertex. Distinct halves
meet only at original vertices or crossing points, including
the case of the two halves of the same edge.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- Splitting a source arc at its interior crossing produces
its two half-edges and retains their vertex and intersection
conditions, as used in XII (4.5), claim (1), page 253. -/
theorem exists_source_halfedges {S V E : Type*} [TopologicalSpace S] [T2Space S]
    (v : V → S) (κ : E × Bool → V) (P : E → Set S) (x : E → S)
    (hP : ∀ e, IsLineWithEnds (P e) (v (κ (e, false))) (v (κ (e, true))))
    (hx : ∀ e, x e ∈ P e) (hxV : ∀ e, x e ∉ range v)
    (hPV : ∀ e w, v w ∈ P e → w = κ (e, false) ∨ w = κ (e, true))
    (hPP : ∀ e f, e ≠ f → P e ∩ P f ⊆ range v ∪ range x) :
    ∃ L : E × Bool → Set S,
      (∀ i, IsLineWithEnds (L i) (v (κ i)) (x i.1)) ∧
      (∀ i, L i ⊆ P i.1) ∧
      (∀ i w, v w ∈ L i → w = κ i) ∧
      (∀ i j, i ≠ j → L i ∩ L j ⊆ range v ∪ range (fun q : E × Bool => x q.1)) ∧
      (∀ e, L (e, false) ∪ L (e, true) = P e) ∧
      ∀ e, L (e, false) ∩ L (e, true) = {x e} := by
  classical
  have hex : ∀ e, ∃ A B : Set S,
      IsLineWithEnds A (v (κ (e, false))) (x e) ∧
      IsLineWithEnds B (x e) (v (κ (e, true))) ∧ A ∪ B = P e ∧ A ∩ B = {x e} := by
    intro e
    exact (hP e).split (hx e)
      (fun h => hxV e ⟨κ (e, false), h.symm⟩)
      (fun h => hxV e ⟨κ (e, true), h.symm⟩)
  choose A B hA hB hcover hinter using hex
  let L : E × Bool → Set S := fun i => if i.2 then B i.1 else A i.1
  have hline : ∀ i, IsLineWithEnds (L i) (v (κ i)) (x i.1) := by
    rintro ⟨e, b⟩
    cases b
    · exact hA e
    · exact (hB e).symm
  have hsub : ∀ i, L i ⊆ P i.1 := by
    rintro ⟨e, b⟩ z hz
    rw [← hcover e]
    cases b
    · exact Or.inl hz
    · exact Or.inr hz
  have hvertex : ∀ i w, v w ∈ L i → w = κ i := by
    rintro ⟨e, b⟩ w hw
    have hends := hPV e w (hsub (e, b) hw)
    cases b
    · rcases hends with h | h
      · exact h
      · have hwB : v w ∈ B e := h.symm ▸ (hB e).right_mem
        have hvx : v w = x e := mem_singleton_iff.mp ((hinter e).subset ⟨hw, hwB⟩)
        exact False.elim (hxV e ⟨w, hvx⟩)
    · rcases hends with h | h
      · have hwA : v w ∈ A e := h.symm ▸ (hA e).left_mem
        have hvx : v w = x e := mem_singleton_iff.mp ((hinter e).subset ⟨hwA, hw⟩)
        exact False.elim (hxV e ⟨w, hvx⟩)
      · exact h
  refine ⟨L, hline, hsub, hvertex, ?_, hcover, hinter⟩
  rintro ⟨e, b⟩ ⟨f, c⟩ hne z hz
  by_cases hef : e = f
  · subst f
    have hbc : b ≠ c := fun h => hne (by subst c; rfl)
    have hzx : z = x e := by
      cases b <;> cases c
      · exact False.elim (hbc rfl)
      · exact mem_singleton_iff.mp ((hinter e).subset hz)
      · exact mem_singleton_iff.mp ((hinter e).subset ⟨hz.2, hz.1⟩)
      · exact False.elim (hbc rfl)
    exact Or.inr ⟨(e, false), hzx.symm⟩
  · rcases hPP e f hef ⟨hsub (e, b) hz.1, hsub (f, c) hz.2⟩ with hzV | hzX
    · exact Or.inl hzV
    · obtain ⟨g, hg⟩ := hzX
      exact Or.inr ⟨(g, false), hg⟩

end GraphMinor.GM12
