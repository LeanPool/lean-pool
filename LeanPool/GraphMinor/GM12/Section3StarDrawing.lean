/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.GM11.RadialChord
import LeanPool.GraphMinor.GM11.PaintingCells

/-!
# Drawing a finite star

For the forest in XII (3.1), page 245, finitely many lines join a
centre to the prescribed points in a feasibility disc. Lines with
distinct ends meet only at the centre. Glue their line drawings one
at a time, retaining exact formulas for support, vertices and edges.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- Finitely many lines meeting only at their common centre form a
drawing, with exactly their open interiors as edges. -/
theorem exists_drawing_of_finite_star
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {Z : Set S} (hZ : Z.Finite) (c : S) (L : S → Set S)
    (hline : ∀ a ∈ Z, IsLineWithEnds (L a) c a)
    (hmeet : ∀ a ∈ Z, ∀ b ∈ Z, a ≠ b → L a ∩ L b = {c})
    (hcZ : c ∉ Z) :
    ∃ H : Drawing S, H.U = {c} ∪ ⋃ a ∈ Z, L a ∧ H.V = insert c Z ∧
      H.E = (fun a => L a \ {c, a}) '' Z := by
  revert hline hmeet hcZ
  induction Z, hZ using Set.Finite.induction_on with
  | empty =>
    intro _ _ _
    refine ⟨pointsDrawing (finite_singleton c), ?_, ?_, ?_⟩
    · change {c} = {c} ∪ ⋃ a ∈ (∅ : Set S), L a
      simp
    · change {c} = insert c (∅ : Set S)
      ext x
      simp only [mem_singleton_iff, mem_insert_iff, mem_empty_iff_false, or_false]
    · change arcComponentsIn ({c} \ {c}) = (fun a => L a \ {c, a}) '' ∅
      rw [Set.sdiff_self, image_empty]
      ext e
      constructor
      · rintro ⟨⟨x, hx⟩, hsub, _⟩
        exact hsub hx
      · intro he
        exact False.elim he
  | @insert a Z ha hZ ih =>
    intro hline hmeet hcZ
    obtain ⟨H, hU, hV, hE⟩ := ih
      (fun b hb => hline b (mem_insert_of_mem a hb))
      (fun b hb d hd hbd => hmeet b (mem_insert_of_mem a hb) d (mem_insert_of_mem a hd) hbd)
      (fun hc => hcZ (mem_insert_of_mem a hc))
    have hca : c ≠ a := by
      intro he
      exact hcZ (mem_insert_iff.mpr (Or.inl he))
    let K := lineDrawing (hline a (Or.inl rfl)) hca
    have hK_U : K.U = L a := rfl
    have hK_V : K.V = {c, a} := rfl
    have hK_E : K.E = {L a \ {c, a}} := lineDrawing_E _ _
    have hcap : H.U ∩ K.U ⊆ {c} := by
      rintro x ⟨hxH, hxK⟩
      rw [hU] at hxH
      rw [hK_U] at hxK
      rcases hxH with hxC | hxL
      · exact hxC
      · obtain ⟨b, hb⟩ := mem_iUnion.mp hxL
        obtain ⟨hbZ, hxb⟩ := mem_iUnion.mp hb
        have hba : b ≠ a := by
          intro he
          exact ha (he ▸ hbZ)
        have hx : x ∈ L b ∩ L a := ⟨hxb, hxK⟩
        rw [hmeet b (mem_insert_of_mem a hbZ) a (Or.inl rfl) hba] at hx
        exact hx
    have hglue : H.U ∩ K.U ⊆ H.V ∩ K.V := by
      intro x hx
      have hxc : x = c := hcap hx
      subst x
      rw [hV, hK_V]
      exact ⟨Or.inl rfl, Or.inl rfl⟩
    refine ⟨H.glue K hglue, ?_, ?_, ?_⟩
    · change H.U ∪ K.U = _
      rw [hU, hK_U, biUnion_insert]
      ac_rfl
    · change H.V ∪ K.V = _
      rw [hV, hK_V]
      ext x
      simp only [mem_union, mem_insert_iff, mem_singleton_iff]
      tauto
    · rw [Drawing.glue_E, hE, hK_E, image_insert_eq, union_singleton]

end GraphMinor.GM12
