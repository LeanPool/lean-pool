/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3PuncturedBoundary
import LeanPool.GraphMinor.Surface.DiscArcs

/-!
# Adding a disc disjoint from the drawing

The auxiliary disc in XII (3.2), page 247, has no boundary vertices.
Adding it to the prescribed family preserves the boundary vertex
union. A forest disjoint from that disc also keeps its contact set.
These are the set identities needed in the two-disc reduction.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- The auxiliary disc has no drawing vertices on its boundary. -/
theorem boundary_vertices_eq_empty_of_disc_disjoint
    {S : Type*} [TopologicalSpace S] (Γ : Drawing S) {E : Set S}
    (hE : Disjoint E Γ.U) : Γ.V ∩ discBd E = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact Set.disjoint_left.mp hE (Surface.discBd_subset E hx.2) (Γ.V_subset_U hx.1)

/-- Adding an empty-boundary disc does not change the prescribed
boundary vertex set in XII (3.2), page 247. -/
theorem discBoundaryVertices_fin_cons_of_disjoint
    {S : Type*} [TopologicalSpace S] {t : ℕ} (Γ : Drawing S) (Δ : Fin t → Set S)
    {E : Set S} (hE : Disjoint E Γ.U) :
    discBoundaryVertices Γ (Fin.cons E Δ) = discBoundaryVertices Γ Δ := by
  have hVE := boundary_vertices_eq_empty_of_disc_disjoint Γ hE
  ext x
  simp only [discBoundaryVertices, mem_iUnion, Fin.exists_fin_succ, Fin.cons_zero, Fin.cons_succ]
  exact or_iff_right (fun hx => Set.notMem_empty x (hVE ▸ hx))

/-- A drawing avoiding the auxiliary disc keeps its contacts with
the enlarged prescribed family. -/
theorem drawing_contact_fin_cons_of_disjoint
    {S : Type*} [TopologicalSpace S] {t : ℕ} (K : Drawing S) (Δ : Fin t → Set S)
    {E : Set S} (hE : Disjoint E K.U) :
    (K.U ∩ ⋃ i : Fin (t + 1), (Fin.cons E Δ : Fin (t + 1) → Set S) i) = (K.U ∩ ⋃ i, Δ i) ∧
      (K.V ∩ ⋃ i : Fin (t + 1), (Fin.cons E Δ : Fin (t + 1) → Set S) i) = (K.V ∩ ⋃ i, Δ i) := by
  have hU : K.U ∩ E = ∅ := hE.symm.inter_eq
  have hV : K.V ∩ E = ∅ := (hE.mono_right K.V_subset_U).symm.inter_eq
  have hUnion : (⋃ i : Fin (t + 1), (Fin.cons E Δ : Fin (t + 1) → Set S) i) = E ∪ ⋃ i, Δ i := by
    ext x
    simp only [mem_iUnion, Fin.exists_fin_succ, Fin.cons_zero, Fin.cons_succ, mem_union]
  constructor
  · rw [hUnion, inter_union_distrib_left, hU, empty_union]
  · rw [hUnion, inter_union_distrib_left, hV, empty_union]

end GraphMinor.GM12
