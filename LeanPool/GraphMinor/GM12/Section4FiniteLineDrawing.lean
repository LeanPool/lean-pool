/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.GM11.PaintingCells
import LeanPool.GraphMinor.GM11.RadialChord
import LeanPool.GraphMinor.GM11.RadialExists

/-!
# Drawing a finite family of graph edges

The drawing of the loopless target in XII (4.3), pages 249--251,
may be given by vertex points and edge lines. Assemble these lines
into a drawing. Start with the vertex points and glue one line
at a time. The intersection assumptions ensure that the new line
meets the existing drawing only at its ends.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- A finite family of lines with prescribed ends and disjoint
interiors forms a drawing, as used for the target in XII (4.3). -/
theorem exists_drawing_of_finite_lines
    {S ι : Type*} [TopologicalSpace S] [T2Space S]
    {V : Set S} (hV : V.Finite) {E : Set ι} (hE : E.Finite)
    (L : ι → Set S) (u v : ι → S)
    (hline : ∀ i ∈ E, IsLineWithEnds (L i) (u i) (v i))
    (hne : ∀ i ∈ E, u i ≠ v i)
    (hends : ∀ i ∈ E, L i ∩ V = {u i, v i})
    (hmeet : ∀ i ∈ E, ∀ j ∈ E, i ≠ j → L i ∩ L j ⊆ V) :
    ∃ H : Drawing S, H.U = V ∪ ⋃ i ∈ E, L i ∧ H.V = V ∧
      H.E = (fun i => L i \ {u i, v i}) '' E := by
  revert hline hne hends hmeet
  induction E, hE using Set.Finite.induction_on with
  | empty =>
    intro _ _ _ _
    refine ⟨pointsDrawing hV, ?_, rfl, ?_⟩
    · change V = V ∪ ⋃ i ∈ (∅ : Set ι), L i
      simp
    · rw [pointsDrawing_E, image_empty]
  | @insert i E hi hE ih =>
    intro hline hne hends hmeet
    obtain ⟨H, hHU, hHV, hHE⟩ := ih
      (fun j hj => hline j (Or.inr hj)) (fun j hj => hne j (Or.inr hj))
      (fun j hj => hends j (Or.inr hj))
      (fun j hj k hk hjk => hmeet j (Or.inr hj) k (Or.inr hk) hjk)
    let K := lineDrawing (hline i (Or.inl rfl)) (hne i (Or.inl rfl))
    have hKU : K.U = L i := rfl
    have hKV : K.V = {u i, v i} := rfl
    have hKE : K.E = {L i \ {u i, v i}} := lineDrawing_E _ _
    have hKiV : K.V ⊆ V := by
      rw [hKV, ← hends i (Or.inl rfl)]
      exact inter_subset_right
    have hglue : H.U ∩ K.U ⊆ H.V ∩ K.V := by
      rintro x ⟨hxH, hxK⟩
      have hxL : x ∈ L i := hxK
      have hxV : x ∈ V := by
        rw [hHU] at hxH
        rcases hxH with hxV | hxH
        · exact hxV
        · obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hxH
          exact hmeet j (Or.inr hj) i (Or.inl rfl)
            (fun heq => hi (heq ▸ hj)) ⟨hxj, hxL⟩
      refine ⟨hHV.symm ▸ hxV, ?_⟩
      rw [hKV, ← hends i (Or.inl rfl)]
      exact ⟨hxL, hxV⟩
    refine ⟨H.glue K hglue, ?_, ?_, ?_⟩
    · change H.U ∪ K.U = _
      rw [hHU, hKU, biUnion_insert]
      ac_rfl
    · change H.V ∪ K.V = V
      rw [hHV]
      exact union_eq_left.mpr hKiV
    · rw [Drawing.glue_E, hHE, hKE, image_insert_eq, union_singleton]

end GraphMinor.GM12
