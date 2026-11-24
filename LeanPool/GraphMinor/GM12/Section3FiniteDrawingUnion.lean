/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.GM11.RadialBasics
import LeanPool.GraphMinor.GM11.PaintingCells

/-!
# Finite disjoint unions of drawings

The forests in the feasibility discs of XII (3.1), page 245, have
pairwise disjoint supports. Their finite union is a drawing, obtained
by gluing one component at a time. Its support, vertices and edges
are exactly the unions of those of the components.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- A finite family of drawings with disjoint supports has a drawing
as its union, with the expected support, vertex and edge sets. -/
theorem exists_finite_disjoint_drawing_union
    {S ι : Type*} [TopologicalSpace S] [T2Space S] [Finite ι]
    (H : ι → Drawing S) (hdis : Pairwise (fun i j => Disjoint (H i).U (H j).U)) :
    ∃ K : Drawing S, K.U = ⋃ i, (H i).U ∧ K.V = ⋃ i, (H i).V ∧ K.E = ⋃ i, (H i).E := by
  classical
  have hfinite : ∀ I : Set ι, I.Finite → ∃ K : Drawing S,
      K.U = ⋃ i ∈ I, (H i).U ∧ K.V = ⋃ i ∈ I, (H i).V ∧ K.E = ⋃ i ∈ I, (H i).E := by
    intro I hI
    induction I, hI using Set.Finite.induction_on with
    | empty =>
      refine ⟨pointsDrawing finite_empty, ?_, ?_, ?_⟩
      · change ∅ = ⋃ i ∈ (∅ : Set ι), (H i).U
        simp
      · change ∅ = ⋃ i ∈ (∅ : Set ι), (H i).V
        simp
      · change arcComponentsIn (∅ \ ∅ : Set S) = ⋃ i ∈ (∅ : Set ι), (H i).E
        simp only [Set.sdiff_self, Set.biUnion_empty]
        ext e
        constructor
        · rintro ⟨⟨x, hx⟩, hsub, _⟩
          exact hsub hx
        · intro he
          exact False.elim he
    | @insert a I ha hI ih =>
      obtain ⟨K, hU, hV, hE⟩ := ih
      have hcap : K.U ∩ (H a).U ⊆ K.V ∩ (H a).V := by
        rintro x ⟨hxK, hxa⟩
        rw [hU] at hxK
        obtain ⟨i, hi⟩ := mem_iUnion.mp hxK
        obtain ⟨hiI, hxi⟩ := mem_iUnion.mp hi
        have hia : i ≠ a := by
          intro he
          exact ha (he ▸ hiI)
        exact False.elim (Set.disjoint_left.mp (hdis hia) hxi hxa)
      refine ⟨K.glue (H a) hcap, ?_, ?_, ?_⟩
      · change K.U ∪ (H a).U = _
        rw [hU, biUnion_insert, union_comm]
      · change K.V ∪ (H a).V = _
        rw [hV, biUnion_insert, union_comm]
      · rw [Drawing.glue_E, hE, biUnion_insert, union_comm]
  obtain ⟨K, hU, hV, hE⟩ := hfinite univ (Set.toFinite _)
  refine ⟨K, ?_, ?_, ?_⟩
  · simpa only [Set.biUnion_univ] using hU
  · simpa only [Set.biUnion_univ] using hV
  · simpa only [Set.biUnion_univ] using hE

end GraphMinor.GM12
