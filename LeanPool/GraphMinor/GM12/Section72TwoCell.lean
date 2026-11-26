/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section72OpenDisc

/-!
# Two-cellness after the disc restriction in XII (7.2)

The merged region is an open disc. Every other new region is an old
region: outside the merged region the two drawings have the same point
set. Thus the outside restriction is two-cell, as in the first paragraph
of the proof of XII (7.2), page 260.
-/

public section

namespace GraphMinor.GM12

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-- The two-cell assertion of XII (7.2), pages 259–260. The old region
containing the punctured boundary is enlarged to an open disc. All other
regions of the restricted drawing are unchanged old regions. -/
theorem theorem_7_2_twoCell (hS : IsClosedSurface S)
    {Γ : Drawing S} (htwo : (PaintingOrDrawing.drawing Γ).IsTwoCell)
    {Δ F r : Set S} {v : S}
    (hΔ : IsClosedDisc Δ) (hbd : subBd Δ = F)
    (hn : (PaintingOrDrawing.drawing Γ).IsNormal F)
    (hFV : F ∩ Γ.V = {v}) (hr : r ∈ Γ.R) (hFr : F \ {v} ⊆ r) :
    (PaintingOrDrawing.drawing (Γ.interSet (closure (univ \ Δ)))).IsTwoCell := by
  have : ConnectedSpace S := htwo.1
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  let Γ' := Γ.interSet (closure (univ \ Δ))
  let Y := r ∪ (Δ \ {v})
  have hY := theorem_7_2_region hS hΔ hbd hn hFV hr hFr
  have hfr : frontier Δ = F := (subBd_eq_frontier Δ).symm.trans hbd
  have hdb : discBd Δ = F := (IsClosedDisc.frontier_eq_discBd hS hΔ).symm.trans hfr
  have hvFV : v ∈ F ∩ Γ.V := hFV.symm ▸ mem_singleton v
  have hYo : IsOpenDisc Y := isOpenDisc_union_disc_sdiff_point hS (htwo.2 r hr) hΔ
    (hdb.symm ▸ hvFV.1) (fun hvr => region_subset hr hvr (Γ.V_subset_U hvFV.2))
    (by rw [hdb]; exact hFr)
  have hcover : Γ.U ⊆ Γ'.U ∪ Y :=
    (drawing_U_subset_outside_normal_disc_union hfr hn hvFV.1).trans
      (union_subset_union subset_rfl subset_union_right)
  refine ⟨inferInstance, fun s hs => ?_⟩
  by_cases hsY : s = Y
  · exact hsY.symm ▸ hYo
  · have hoff : s ⊆ univ \ Γ.U := by
      intro x hx
      refine ⟨mem_univ x, fun hxU => ?_⟩
      rcases hcover hxU with hxU' | hxY
      · exact region_subset hs hx hxU'
      · exact hsY (region_eq_of_mem hs hY hx hxY)
    obtain ⟨x, hx⟩ := region_nonempty hs
    let C := connectedComponentIn (univ \ Γ.U) x
    have hC : C ∈ Γ.R := (mem_R_iff Γ).mpr ⟨x, (hoff hx).2, rfl⟩
    have hsC : s ⊆ C := (region_isPreconnected hs).subset_connectedComponentIn hx hoff
    have hxnew : x ∈ univ \ Γ'.U := ⟨mem_univ x, region_subset hs hx⟩
    have hCCnew : connectedComponentIn (univ \ Γ'.U) x ∈ Γ'.R :=
      (mem_R_iff Γ').mpr ⟨x, hxnew.2, rfl⟩
    have hnewEq : connectedComponentIn (univ \ Γ'.U) x = s :=
      region_eq_of_mem hCCnew hs (mem_connectedComponentIn hxnew) hx
    have hCs : C ⊆ s := by
      rw [← hnewEq]
      exact connectedComponentIn_mono x (fun y hy =>
        ⟨mem_univ y, fun hyU' => hy.2 ((Drawing.span_isSubdrawing Γ _ _).U_subset hyU')⟩)
    have heq : s = C := Subset.antisymm hsC hCs
    exact heq.symm ▸ htwo.2 C hC

end GraphMinor.GM12
