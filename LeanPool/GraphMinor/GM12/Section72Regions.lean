/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section72Tangle
import LeanPool.GraphMinor.GM12.Section1
import LeanPool.GraphMinor.Surface.DiscGrow
import LeanPool.GraphMinor.GM11.PaintingCells
import LeanPool.GraphMinor.GM11.Section64

/-!
# The merged region in Graph Minors XII, (7.2)

The outside restriction keeps precisely the points of the original drawing
outside the disc interior. Its new region is the union of the old region
with the disc minus the one boundary vertex. The proofs use connectedness
of edges and of the punctured disc, and the boundaries of the two regions.
-/

public section

namespace GraphMinor.GM12

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-- The point set of a drawing restricted to a closed set with normal frontier
is its intersection with that set. In XII (7.2), the set is the outside disc. -/
theorem interSet_U_eq_of_normal_frontier {Γ : Drawing S} {X : Set S}
    (hX : IsClosed X) (hn : frontier X ∩ Γ.U ⊆ Γ.V) :
    (Γ.interSet X).U = Γ.U ∩ X := by
  apply Subset.antisymm
  · exact subset_inter (Drawing.span_isSubdrawing Γ _ _).U_subset (interSet_U_subset hX)
  · rintro x ⟨hxU, hxX⟩
    by_cases hxV : x ∈ Γ.V
    · exact (Γ.interSet X).V_subset_U (mem_interSet_V hxV hxX)
    · obtain ⟨e, he, hxe⟩ := Γ.exists_edge_of_mem hxU hxV
      have hd : Disjoint e (frontier X) := by
        refine disjoint_left.mpr fun y hy hf => ?_
        exact (he.2.1 hy).2 (hn ⟨hf, (he.2.1 hy).1⟩)
      have heX : e ⊆ X :=
        subset_of_disjoint_frontier he.2.2.1.isConnected.isPreconnected hX hd hxe hxX
      exact ((mem_interSet_E_iff.mpr ⟨he, heX⟩).2.1 hxe).1

/-- Restricting a drawing to the outside of a normal disc keeps its points outside the interior. -/
theorem outside_normal_disc_drawing_U {Γ : Drawing S} {Δ F : Set S}
    (hF : frontier Δ = F) (hn : (PaintingOrDrawing.drawing Γ).IsNormal F) :
    (Γ.interSet (closure (univ \ Δ))).U = Γ.U ∩ closure (univ \ Δ) := by
  apply interSet_U_eq_of_normal_frontier isClosed_closure
  rw [← compl_eq_univ_sdiff, closure_compl, frontier_compl]
  exact fun x hx => hn ⟨hF ▸ frontier_interior_subset hx.1, hx.2⟩

/-- The drawing outside a normal disc meets the disc only at its sole boundary vertex. -/
theorem outside_normal_disc_drawing_inter_subset {Γ : Drawing S} {Δ F : Set S} {v : S}
    (hF : frontier Δ = F) (hn : (PaintingOrDrawing.drawing Γ).IsNormal F)
    (hv : F ∩ Γ.V = {v}) :
    (Γ.interSet (closure (univ \ Δ))).U ∩ Δ ⊆ {v} := by
  rw [outside_normal_disc_drawing_U hF hn]
  rintro x ⟨⟨hxU, hxOut⟩, hxΔ⟩
  have hxF : x ∈ F := by
    rw [← hF, frontier_eq_closure_inter_closure, compl_eq_univ_sdiff]
    exact ⟨subset_closure hxΔ, hxOut⟩
  exact hv ▸ ⟨hxF, hn ⟨hxF, hxU⟩⟩

/-- The outside drawing and the punctured disc cover the original drawing when the puncture
lies on the disc frontier. -/
theorem drawing_U_subset_outside_normal_disc_union {Γ : Drawing S} {Δ F : Set S} {v : S}
    (hF : frontier Δ = F) (hn : (PaintingOrDrawing.drawing Γ).IsNormal F)
    (hv : v ∈ F) :
    Γ.U ⊆ (Γ.interSet (closure (univ \ Δ))).U ∪ (Δ \ {v}) := by
  rw [outside_normal_disc_drawing_U hF hn, ← compl_eq_univ_sdiff, closure_compl]
  intro x hx
  by_cases hxi : x ∈ interior Δ
  · exact Or.inr ⟨interior_subset hxi, fun hxv =>
      (hF.symm ▸ hv).2 (mem_singleton_iff.mp hxv ▸ hxi)⟩
  · exact Or.inl ⟨hx, hxi⟩

omit [T2Space S] in
private theorem frontier_region_subset_drawing [LocallyConnectedSpace S]
    {Γ : Drawing S} {r : Set S} (hr : r ∈ Γ.R) : frontier r ⊆ Γ.U := by
  intro x hx
  by_contra hxU
  have hx_compl : x ∈ univ \ Γ.U := ⟨mem_univ x, hxU⟩
  have hopen : IsOpen (connectedComponentIn (univ \ Γ.U) x) :=
    IsOpen.connectedComponentIn (isOpen_univ.sdiff Γ.isClosed_U)
  obtain ⟨y, hy_cc, hy_r⟩ := mem_closure_iff.mp hx.1 _ hopen (mem_connectedComponentIn hx_compl)
  have hr' : connectedComponentIn (univ \ Γ.U) x ∈ Γ.R :=
    (mem_R_iff Γ).mpr ⟨x, hxU, rfl⟩
  have heq : connectedComponentIn (univ \ Γ.U) x = r :=
    region_eq_of_mem hr' hr hy_cc hy_r
  have hxr : x ∈ r := heq ▸ mem_connectedComponentIn hx_compl
  exact hx.2 ((region_isOpen hr).interior_eq.symm ▸ hxr)

omit [T2Space S] in
/-- A disc with one boundary point removed is preconnected. This is the
connected part of the merged-region assertion in XII (7.2), page 260. -/
theorem disc_sdiff_boundary_point_isPreconnected {Δ : Set S} (hΔ : IsClosedDisc Δ)
    {v : S} (hv : v ∈ discBd Δ) : IsPreconnected (Δ \ {v}) := by
  refine hΔ.isPreconnected_discInt.subset_closure ?_
    (sdiff_subset.trans hΔ.subset_closure_discInt)
  rintro x ⟨hx, hxb⟩
  exact ⟨hx, fun h => hxb (mem_singleton_iff.mp h ▸ hv)⟩

/-- Removing a normal disc through one vertex merges its punctured disc with
the region containing the rest of its boundary, as in XII (7.2), page 260. -/
theorem theorem_7_2_region (hS : IsClosedSurface S)
    {Γ : Drawing S} {Δ F r : Set S} {v : S}
    (hΔ : IsClosedDisc Δ) (hbd : subBd Δ = F)
    (hn : (PaintingOrDrawing.drawing Γ).IsNormal F)
    (hFV : F ∩ Γ.V = {v}) (hr : r ∈ Γ.R) (hFr : F \ {v} ⊆ r) :
    r ∪ (Δ \ {v}) ∈ (Γ.interSet (closure (univ \ Δ))).R := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hclosed : IsClosed Δ := hΔ.isClosed
  have hfr : frontier Δ = F := (subBd_eq_frontier Δ).symm.trans hbd
  have hdb : discBd Δ = F := (IsClosedDisc.frontier_eq_discBd hS hΔ).symm.trans hfr
  have hvFV : v ∈ F ∩ Γ.V := hFV.symm ▸ mem_singleton v
  have hvb : v ∈ discBd Δ := hdb.symm ▸ hvFV.1
  have hX : closure (univ \ Δ) = (interior Δ)ᶜ := by
    rw [← compl_eq_univ_sdiff, closure_compl]
  have hU := outside_normal_disc_drawing_U hfr hn
  let Γ' := Γ.interSet (closure (univ \ Δ))
  let Y := r ∪ (Δ \ {v})
  have hYeq : Y = r ∪ interior Δ := by
    apply Subset.antisymm
    · rintro x (hx | ⟨hxΔ, hxv⟩)
      · exact Or.inl hx
      · by_cases hxi : x ∈ interior Δ
        · exact Or.inr hxi
        · exact Or.inl (hFr ⟨hfr ▸ ⟨subset_closure hxΔ, hxi⟩, hxv⟩)
    · rintro x (hx | hxi)
      · exact Or.inl hx
      · exact Or.inr ⟨interior_subset hxi, fun hxv =>
          (show v ∉ interior Δ from fun h => (hfr.symm ▸ hvFV.1).2 h)
            (mem_singleton_iff.mp hxv ▸ hxi)⟩
  have hYo : IsOpen Y := hYeq ▸ (region_isOpen hr).union isOpen_interior
  have hYoff : Y ⊆ univ \ Γ'.U := by
    rintro x (hxr | ⟨hxΔ, hxv⟩)
    · exact ⟨mem_univ x, fun hx => region_subset hr hxr ((Drawing.span_isSubdrawing Γ _ _).U_subset
        hx)⟩
    · refine ⟨mem_univ x, fun hx => ?_⟩
      rw [hU] at hx
      have hxfr : x ∈ frontier Δ := by
        rw [frontier_eq_closure_inter_closure, compl_eq_univ_sdiff]
        exact ⟨subset_closure hxΔ, hx.2⟩
      have hxF : x ∈ F := hfr ▸ hxfr
      exact hxv (hFV ▸ ⟨hxF, hn ⟨hxF, hx.1⟩⟩)
  obtain ⟨w, hwF, hwv⟩ := (infinite_of_isOArc hΔ.isOArc_discBd).exists_notMem_finite
    (finite_singleton v)
  have hwr : w ∈ r := hFr ⟨hdb ▸ hwF, hwv⟩
  have hwD : w ∈ Δ \ {v} := ⟨Surface.discBd_subset Δ hwF, hwv⟩
  have hYconn : IsPreconnected Y :=
    (region_isPreconnected hr).union w hwr hwD (disc_sdiff_boundary_point_isPreconnected hΔ hvb)
  have hYfr : frontier Y ⊆ Γ'.U := by
    intro x hx
    have hxnot : x ∉ Y := fun hy => hx.2 (hYo.interior_eq.symm ▸ hy)
    have hxnotr : x ∉ r := fun h => hxnot (Or.inl h)
    have hxnoti : x ∉ interior Δ := fun h => hxnot (hYeq.symm ▸ Or.inr h)
    have hxold : x ∈ Γ.U := by
      rw [hYeq] at hx
      rcases frontier_union_subset r (interior Δ) hx with ⟨hxr, _⟩ | ⟨_, hxi⟩
      · exact frontier_region_subset_drawing hr hxr
      · have hxF : x ∈ F := hfr ▸ frontier_interior_subset hxi
        by_cases hxv : x ∈ ({v} : Set S)
        · exact Γ.V_subset_U (mem_singleton_iff.mp hxv ▸ hvFV.2)
        · exact (hxnotr (hFr ⟨hxF, hxv⟩)).elim
    change x ∈ (Γ.interSet (closure (univ \ Δ))).U
    rw [hU, hX]
    exact ⟨hxold, hxnoti⟩
  have hwY : w ∈ Y := Or.inl hwr
  let C := connectedComponentIn (univ \ Γ'.U) w
  have hYC : Y ⊆ C := hYconn.subset_connectedComponentIn hwY hYoff
  have hCY : C ⊆ Y := by
    have hcover : C ⊆ Y ∪ (closure Y)ᶜ := by
      intro x hxC
      by_cases hxcl : x ∈ closure Y
      · refine Or.inl ?_
        by_contra hxY
        have hxfr : x ∈ frontier Y := ⟨hxcl, fun h => hxY (interior_subset h)⟩
        exact (connectedComponentIn_subset (univ \ Γ'.U) w hxC).2 (hYfr hxfr)
      · exact Or.inr hxcl
    exact isPreconnected_connectedComponentIn.subset_left_of_subset_union hYo
      isClosed_closure.isOpen_compl
      (disjoint_left.mpr fun x hx hxcl => hxcl (subset_closure hx)) hcover
      ⟨w, mem_connectedComponentIn (hYoff hwY), hwY⟩
  have hCreg : C ∈ Γ'.R := (mem_R_iff Γ').mpr ⟨w, (hYoff hwY).2, rfl⟩
  change Y ∈ Γ'.R
  rw [← Subset.antisymm hCY hYC]
  exact hCreg

end GraphMinor.GM12
