/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section72
import LeanPool.GraphMinor.GM12.Section73DiscAttachment
import LeanPool.GraphMinor.GM12.Section73VertexReduction
import LeanPool.GraphMinor.GM11.Section810

/-!
# The merged region in the induction of XII (7.4)

The disc reduction in XII (7.4), page 263, creates the region
`r ∪ (D \ {v})`. Its closure contains `v`. Any later subdrawing
whose region contains `v` therefore absorbs this whole region:
an open neighbourhood of `v` meets it, and connectedness keeps
it within one region. The old point set is contained in the
restricted point set together with the removed disc. Thus the
point-set containment from the smaller drawing passes back to
the original drawing.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- An old region whose closure contains a point of a new region
is wholly contained in that new region of a subdrawing. -/
theorem region_subset_of_closure_mem_subdrawing_region
    {S : Type*} [TopologicalSpace S]
    (hS : IsClosedSurface S) {Γ Γ' : Drawing S} (hsub : Γ'.IsSubdrawing Γ)
    {r r' : Set S} (hr : r ∈ Γ.R) (hr' : r' ∈ Γ'.R)
    {v : S} (hvr : v ∈ closure r) (hvr' : v ∈ r') : r ⊆ r' := by
  let : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨x, hxr', hxr⟩ := mem_closure_iff.mp hvr r' (region_isOpen hr') hvr'
  exact subset_region hr' (region_isPreconnected hr)
    (disjoint_left.mpr fun y hyr hyU => region_subset hr hyr (hsub.U_subset hyU)) hxr hxr'

/-- The removed normal disc lies in the final region containing
its boundary vertex, once the reduced drawing satisfies (7.4)(i).
This is the region containment used in the induction on page 263. -/
theorem normal_disc_subset_final_vertex_region
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {Γ Γ' : Drawing S} {D F r r' : Set S} {v : S}
    (hD : IsClosedDisc D) (hbd : subBd D = F)
    (hn : (PaintingOrDrawing.drawing Γ).IsNormal F) (hFV : F ∩ Γ.V = {v})
    (hr : r ∈ Γ.R) (hFr : F \ {v} ⊆ r)
    (hsub : Γ'.IsSubdrawing (Γ.interSet (closure (univ \ D))))
    (hr' : r' ∈ Γ'.R) (hvr' : v ∈ r') :
    r ∪ D ⊆ r' := by
  have hY := theorem_7_2_region hS hD hbd hn hFV hr hFr
  have hvD : v ∈ D := by
    have hvF : v ∈ F := (hFV.symm ▸ mem_singleton v).1
    have hvfr : v ∈ frontier D := ((subBd_eq_frontier D).symm.trans hbd).symm ▸ hvF
    exact hD.isClosed.closure_subset_iff.mpr subset_rfl hvfr.1
  have hvY : v ∈ closure (r ∪ (D \ {v})) :=
    closure_mono subset_union_right (disc_subset_closure_punctured hD v hvD)
  have hYr' := region_subset_of_closure_mem_subdrawing_region hS hsub hY hr' hvY hvr'
  intro x hx
  rcases hx with hx | hx
  · exact hYr' (Or.inl hx)
  · by_cases hxv : x = v
    · exact hxv.symm ▸ hvr'
    · exact hYr' (Or.inr ⟨hx, hxv⟩)

/-- The point set removed by restricting outside a normal disc
is contained in that disc. -/
theorem drawing_subset_outside_disc_union_disc
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {Γ : Drawing S} {D F : Set S} (hbd : subBd D = F)
    (hn : (PaintingOrDrawing.drawing Γ).IsNormal F) :
    Γ.U ⊆ (Γ.interSet (closure (univ \ D))).U ∪ D := by
  have hfrD : frontier D = F := (subBd_eq_frontier D).symm.trans hbd
  have hnorm : frontier (closure (univ \ D)) ∩ Γ.U ⊆ Γ.V := by
    rw [← compl_eq_univ_sdiff, closure_compl, frontier_compl]
    intro x hx
    exact hn ⟨hfrD ▸ frontier_interior_subset hx.1, hx.2⟩
  rw [interSet_U_eq_of_normal_frontier isClosed_closure hnorm]
  intro x hx
  by_cases hxD : x ∈ D
  · exact Or.inr hxD
  · exact Or.inl ⟨hx, subset_closure ⟨mem_univ x, hxD⟩⟩

end GraphMinor.GM12
