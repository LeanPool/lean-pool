/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.GM11.PaintingCells
import LeanPool.GraphMinor.GM11.RadialBasics

/-!
# Gluing a finite family of drawings

The drawings meet only in a fixed finite vertex set, and every
point of that set on a drawing is one of its vertices. Start with
the drawing of the fixed vertices and glue the drawings one at a
time. The resulting support, vertices, and edges are exactly the
respective unions. This glues the replacing paths of the wall
subdivision in XVI (4.2).
-/

public section
namespace GraphMinor.GM16
open Set Topology Surface GM11
universe u v

/-- A finite family of drawings meeting only at common prescribed
vertices has a drawing with exactly the union support and edges. -/
theorem exists_drawing_of_finite_drawings {S : Type u}
    [TopologicalSpace S] [T2Space S] {ι : Type v} {I : Set ι} (hI : I.Finite)
    {Z : Set S} (hZ : Z.Finite) (D : ι → Drawing S)
    (hZMeet : ∀ i ∈ I, (D i).U ∩ Z ⊆ (D i).V)
    (hMeet : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (D i).U ∩ (D j).U ⊆ Z) :
    ∃ H : Drawing S, H.U = Z ∪ ⋃ i ∈ I, (D i).U ∧
      H.V = Z ∪ ⋃ i ∈ I, (D i).V ∧ H.E = ⋃ i ∈ I, (D i).E := by
  classical
  have key : ∀ T : Finset ι, (∀ i ∈ T, i ∈ I) →
      ∃ H : Drawing S, H.U = Z ∪ ⋃ i ∈ T, (D i).U ∧
        H.V = Z ∪ ⋃ i ∈ T, (D i).V ∧ H.E = ⋃ i ∈ T, (D i).E := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨pointsDrawing hZ,by simp [pointsDrawing],by simp [pointsDrawing],?_⟩
      simp only [Finset.notMem_empty,iUnion_of_empty,iUnion_empty]
      apply eq_empty_of_forall_notMem
      rintro C ⟨⟨x,hx⟩,hSub,-⟩
      simpa [pointsDrawing] using hSub hx
    | insert i T hiT ih =>
      intro hT
      have hi := hT i (Finset.mem_insert_self _ _)
      obtain ⟨H,hHU,hHV,hHE⟩ := ih (fun j hj => hT j (Finset.mem_insert_of_mem hj))
      have hGlue : H.U ∩ (D i).U ⊆ H.V ∩ (D i).V := by
        rintro x ⟨hxH,hxi⟩
        have hxZ : x ∈ Z := by
          rw [hHU] at hxH
          rcases hxH with hxZ | hxOld
          · exact hxZ
          · obtain ⟨j,hj,hxj⟩ := mem_iUnion₂.mp hxOld
            exact hMeet i hi j (hT j (Finset.mem_insert_of_mem hj))
              (fun he => hiT (he.symm ▸ hj)) ⟨hxi,hxj⟩
        exact ⟨hHV.symm ▸ Or.inl hxZ,hZMeet i hi ⟨hxi,hxZ⟩⟩
      refine ⟨H.glue (D i) hGlue,?_,?_,?_⟩
      · change H.U ∪ (D i).U = _
        rw [hHU,Finset.set_biUnion_insert,union_assoc,
          union_comm (⋃ j ∈ T, (D j).U) ((D i).U)]
      · change H.V ∪ (D i).V = _
        rw [hHV,Finset.set_biUnion_insert,union_assoc,
          union_comm (⋃ j ∈ T, (D j).V) ((D i).V)]
      · rw [Drawing.glue_E,hHE,Finset.set_biUnion_insert,union_comm]
  obtain ⟨H,hU,hV,hE⟩ := key hI.toFinset (fun i hi => hI.mem_toFinset.mp hi)
  exact ⟨H,by simpa only [hI.mem_toFinset] using hU,
    by simpa only [hI.mem_toFinset] using hV,by simpa only [hI.mem_toFinset] using hE⟩

end GraphMinor.GM16
