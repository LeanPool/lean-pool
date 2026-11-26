/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
import LeanPool.GraphMinor.GM11.ArcDrawings
import LeanPool.GraphMinor.GM11.DrawingOps

/-!
# Constructing the refined seam graph `J⁺`

VII (4.6), page 225, keeps the point set of the seam graph and adds `W`
to its vertices. A finite enlargement of a drawing's vertex set is again
a drawing: mark each closed edge at the new vertices, then glue these
finite line or circle drawings at their shared old vertices.
-/

public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface GraphMinor.GM11

universe u

/-- A finite enlargement of the vertex set gives an actual drawing on the
same point set. This constructs `J⁺` in VII (4.6), page 225. -/
theorem exists_drawing_with_more_vertices {S : Type u} [TopologicalSpace S]
    [T2Space S] (D : Drawing S) {A : Set S} (hA : A.Finite)
    (hVA : D.V ⊆ A) (hAU : A ⊆ D.U) :
    ∃ D' : Drawing S, D'.U = D.U ∧ D'.V = A := by
  classical
  have key : ∀ T : Finset (Set S), (∀ e ∈ T, e ∈ D.E) →
      ∃ C : Drawing S, C.U = A ∪ ⋃ e ∈ T, closure e ∧ C.V = A := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨pointsDrawing hA, by simp [pointsDrawing], rfl⟩
    | insert e T he ih =>
      intro hT
      obtain ⟨C, hCU, hCV⟩ := ih fun f hf => hT f (Finset.mem_insert_of_mem hf)
      have heE := hT e (Finset.mem_insert_self _ _)
      let B := closure e ∩ A
      have hB : B.Finite := hA.subset inter_subset_right
      obtain ⟨L, hLU, hLV⟩ : ∃ L : Drawing S, L.U = closure e ∧ L.V = B := by
        rcases D.edge_cond e heE with ⟨u, v, huv, hcap, hline⟩ | ⟨u, hcap, hcircle⟩
        · have hu : u ∈ closure e ∩ D.V := hcap ▸ mem_insert u {v}
          have hv : v ∈ closure e ∩ D.V := hcap ▸ mem_insert_of_mem u (mem_singleton v)
          exact exists_drawing_on_line _ hline huv hB
            ⟨hu.1, hVA hu.2⟩ ⟨hv.1, hVA hv.2⟩ inter_subset_left le_rfl
        · have hu : u ∈ closure e ∩ D.V := hcap ▸ mem_singleton u
          exact exists_drawing_on_oArc hcircle hB ⟨u, hu.1, hVA hu.2⟩ inter_subset_left
      have hmeet : C.U ∩ L.U ⊆ C.V ∩ L.V := by
        rw [hCU, hCV, hLU, hLV]
        rintro x ⟨hx | hx, hxe⟩
        · exact ⟨hx, hxe, hx⟩
        · obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp hx
          have hfE := hT f (Finset.mem_insert_of_mem hf)
          by_cases hxA : x ∈ A
          · exact ⟨hxA, hxe, hxA⟩
          · have hxV : x ∉ D.V := fun h => hxA (hVA h)
            have hxf' : x ∈ f := D.closure_diff_V hfE ▸ (⟨hxf, hxV⟩ : x ∈ closure f \ D.V)
            have hxe' : x ∈ e := D.closure_diff_V heE ▸ (⟨hxe, hxV⟩ : x ∈ closure e \ D.V)
            exact (he ((D.edge_eq_of_mem hfE heE hxf' hxe') ▸ hf)).elim
      refine ⟨C.glue L hmeet, ?_, ?_⟩
      · change C.U ∪ L.U = _
        rw [hCU, hLU]
        ext x
        simp only [mem_union, mem_iUnion, Finset.mem_insert, exists_prop]
        constructor
        · rintro ((hx | ⟨f, hf, hx⟩) | hx)
          · exact .inl hx
          · exact .inr ⟨f, .inr hf, hx⟩
          · exact .inr ⟨e, .inl rfl, hx⟩
        · rintro (hx | ⟨f, rfl | hf, hx⟩)
          · exact .inl (.inl hx)
          · exact .inr hx
          · exact .inl (.inr ⟨f, hf, hx⟩)
      · change C.V ∪ L.V = A
        rw [hCV, hLV]
        exact union_eq_self_of_subset_right inter_subset_right
  obtain ⟨D', hU, hV⟩ := key D.finite_edges.toFinset fun e he => D.finite_edges.mem_toFinset.mp he
  refine ⟨D', ?_, hV⟩
  rw [hU]
  apply Subset.antisymm
  · rintro x (hx | hx)
    · exact hAU hx
    · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
      exact D.closure_subset_U (D.finite_edges.mem_toFinset.mp he) hxe
  · intro x hx
    rw [D.U_eq] at hx
    rcases hx with hx | hx
    · exact .inl (hVA hx)
    · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
      exact .inr (mem_iUnion₂.mpr ⟨e, D.finite_edges.mem_toFinset.mpr he, hxe⟩)

/-- The graph `(U(J), V(J) ∪ W)` of VII (4.6), page 225, exists as a drawing. -/
theorem exists_J_plus {S : Type u} [TopologicalSpace S] [T2Space S]
    (J : Drawing S) {W : Set S} (hW : W.Finite) (hWU : W ⊆ J.U) :
    ∃ J' : Drawing S, J'.U = J.U ∧ J'.V = J.V ∪ W :=
  exists_drawing_with_more_vertices J (J.finite_V.union hW) subset_union_left
    (union_subset J.V_subset_U hWU)

end GraphMinor.GM07
