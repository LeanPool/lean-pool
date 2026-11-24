/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.GM11.RadialChord
import LeanPool.GraphMinor.GM11.RadialBasics
import LeanPool.GraphMinor.GM11.PaintingCells

/-!
# Drawings from finite families of lines

To draw the wall and its subdivision in XVI (4.2), start with the
finite vertex set and add one line at a time. Distinct lines meet
only at prescribed vertices. Each addition is therefore a gluing of
drawings along vertices, and its open line is one new edge.
-/

public section
namespace GraphMinor.GM16
open Set Topology GraphMinor.Surface GraphMinor.GM11
universe u v

/-- A finite family of lines meeting only at their prescribed endpoint
vertices gives a drawing with exactly those vertices and open edges. -/
theorem exists_drawing_of_finite_lines
    {S : Type u} [TopologicalSpace S] [T2Space S] {ι : Type v}
    {I : Set ι} (hI : I.Finite) {Z : Set S} (hZ : Z.Finite)
    (a b : ι → S) (L : ι → Set S)
    (hLine : ∀ i ∈ I, IsLineWithEnds (L i) (a i) (b i))
    (hNe : ∀ i ∈ I, a i ≠ b i)
    (hEnds : ∀ i ∈ I, L i ∩ Z = {a i,b i})
    (hMeet : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → L i ∩ L j ⊆ Z) :
    ∃ D : Drawing S, D.U = Z ∪ ⋃ i ∈ I, L i ∧ D.V = Z ∧
      D.E = (fun i => L i \ {a i,b i}) '' I := by
  classical
  have key : ∀ T : Finset ι, (∀ i ∈ T, i ∈ I) →
      ∃ D : Drawing S, D.U = Z ∪ ⋃ i ∈ T, L i ∧ D.V = Z ∧
        D.E = (fun i => L i \ {a i,b i}) '' (T : Set ι) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨pointsDrawing hZ, by simp [pointsDrawing], rfl, ?_⟩
      simp only [Finset.coe_empty, image_empty]
      apply eq_empty_of_forall_notMem
      rintro C ⟨⟨x,hx⟩,hSub,-⟩
      simpa [pointsDrawing] using hSub hx
    | insert i T hiT ih =>
      intro hT
      have hi := hT i (Finset.mem_insert_self _ _)
      obtain ⟨D, hDU, hDV, hDE⟩ := ih fun j hj => hT j (Finset.mem_insert_of_mem hj)
      have hPair : ({a i,b i} : Set S) ⊆ Z := by
        intro x hx
        have hx' : x ∈ L i ∩ Z := (hEnds i hi).symm ▸ hx
        exact hx'.2
      have hGlue : D.U ∩ (lineDrawing (hLine i hi) (hNe i hi)).U ⊆
          D.V ∩ (lineDrawing (hLine i hi) (hNe i hi)).V := by
        rintro x ⟨hxD, hxL⟩
        have hxZ : x ∈ Z := by
          rw [hDU] at hxD
          rcases hxD with hxZ | hxOld
          · exact hxZ
          · obtain ⟨j,hj,hxJ⟩ := mem_iUnion₂.mp hxOld
            have hij : i ≠ j := fun heq => hiT (heq.symm ▸ hj)
            exact hMeet i hi j (hT j (Finset.mem_insert_of_mem hj)) hij ⟨hxL,hxJ⟩
        refine ⟨hDV.symm ▸ hxZ, ?_⟩
        change x ∈ ({a i,b i} : Set S)
        exact (hEnds i hi) ▸ (show x ∈ L i ∩ Z from ⟨hxL,hxZ⟩)
      refine ⟨D.glue (lineDrawing (hLine i hi) (hNe i hi)) hGlue, ?_, ?_, ?_⟩
      · change D.U ∪ L i = _
        rw [hDU, Finset.set_biUnion_insert, union_assoc,
          union_comm (⋃ j ∈ T, L j) (L i)]
      · change D.V ∪ {a i,b i} = Z
        rw [hDV]
        exact union_eq_self_of_subset_right hPair
      · rw [Drawing.glue_E, lineDrawing_E, hDE, Finset.coe_insert, image_insert_eq,
          union_comm, singleton_union]
  obtain ⟨D, hU, hV, hE⟩ := key hI.toFinset (fun i hi => hI.mem_toFinset.mp hi)
  exact ⟨D, by simpa only [hI.mem_toFinset] using hU, hV,
    by simpa only [hI.coe_toFinset] using hE⟩

end GraphMinor.GM16
