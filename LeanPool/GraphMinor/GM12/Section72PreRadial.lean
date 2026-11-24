/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section72NoBigon
import LeanPool.GraphMinor.GM12.Section77
import LeanPool.GraphMinor.GM11.Section810

/-!
# The radial conditions after deleting the interior pieces

In XII (7.2), page 260, the closed outside of the two-spoke circuit
and the deletion of one boundary spoke satisfy the defining radial
conditions before maximality. The point-set and hub results give the
first conditions. A possible empty bigon in an unchanged region was
already empty. The new merged region is handled by cutting along the
deleted boundary spoke.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- The radial deletion in XII (7.2), page 260, satisfies all radial
conditions apart from maximality. -/
theorem radialDiscDeletion_isPreRadial
    {S : Type*} [TopologicalSpace S] [T2Space S] (hS : IsClosedSurface S)
    {Γ K C : Drawing S} (hK : (PaintingOrDrawing.drawing Γ).IsPreRadialDrawing K)
    (hC : C.IsSubdrawing K) {D r f : Set S} {v u : S}
    (hD : IsClosedDisc D) (hb : frontier D = C.U) (hCV : C.V = {v, u})
    (hr : r ∈ Γ.R) (hv : v ∈ Γ.V) (hur : u ∈ r) (huK : u ∈ K.V)
    (hCZ : C.U ⊆ r ∪ {v}) (hmeet : Γ.U ∩ C.U = {v})
    (hfC : f ∈ C.E) (hf : K.toGraph.IsLink f v u) :
    (PaintingOrDrawing.drawing (Γ.interSet (closure (univ \ D)))).IsPreRadialDrawing
      (radialDiscDeletion K D f) := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  let Γ' := Γ.interSet (closure (univ \ D))
  let K' := radialDiscDeletion K D f
  let Y := r ∪ (D \ {v})
  have hΓ : Γ'.IsSubdrawing Γ := Drawing.span_isSubdrawing Γ _ _
  have hKK : K'.IsSubdrawing K := radialDiscDeletion_isSubdrawing K D f
  have hn : (PaintingOrDrawing.drawing Γ).IsNormal C.U := by
    rintro x ⟨hxC, hxΓ⟩
    exact mem_singleton_iff.mp (hmeet.subset ⟨hxΓ, hxC⟩) ▸ hv
  have hvC : v ∈ C.U := C.V_subset_U (hCV.symm ▸ Or.inl rfl)
  have hFV : C.U ∩ Γ.V = {v} := by
    apply Subset.antisymm
    · rintro x ⟨hxC, hxΓ⟩
      exact hmeet.subset ⟨Γ.V_subset_U hxΓ, hxC⟩
    · rintro x hx
      have hxv := mem_singleton_iff.mp hx
      subst x
      exact ⟨hvC, hv⟩
  have hFr : C.U \ {v} ⊆ r := fun x hx => (hCZ hx.1).resolve_right hx.2
  have hbd : subBd D = C.U := (subBd_eq_frontier D).trans hb
  have hY : Y ∈ Γ'.R := theorem_7_2_region hS hD hbd hn hFV hr hFr
  have hnorm : frontier (closure (univ \ D)) ∩ Γ.U ⊆ Γ.V := by
    rw [← compl_eq_univ_sdiff, closure_compl, frontier_compl]
    exact fun x hx => hn ⟨hb ▸ frontier_interior_subset hx.1, hx.2⟩
  have hUeq := interSet_U_eq_of_normal_frontier isClosed_closure hnorm
  have hcover : Γ.U ⊆ Γ'.U ∪ Y := by
    intro x hx
    by_cases hxo : x ∈ closure (univ \ D)
    · exact Or.inl (hUeq.symm ▸ ⟨hx, hxo⟩)
    · have hxi : x ∈ interior D := by
        by_contra hnxi
        exact hxo (by rw [← compl_eq_univ_sdiff, closure_compl]; exact hnxi)
      exact Or.inr (Or.inr ⟨interior_subset hxi, fun hxv =>
        (hb.symm ▸ hvC).2 (mem_singleton_iff.mp hxv ▸ hxi)⟩)
  have huNew : u ∈ K'.V := by
    have huf : u ∈ frontier D := hb.symm ▸ C.V_subset_U (hCV.symm ▸ Or.inr rfl)
    rw [frontier_eq_closure_inter_closure] at huf
    rw [radialDiscDeletion_V]
    exact ⟨huK, by simpa only [compl_eq_univ_sdiff] using huf.2⟩
  refine ⟨radialDiscDeletion_inter hK D f, radialDiscDeletion_vertex_subset hK D f,
    radialDiscDeletion_region_hubs hS hK hC hD hb hCV hr hv hur huK hCZ hmeet,
    radialDiscDeletion_vertex_region hK D f, radialDiscDeletion_edge_ends hK D f, ?_⟩
  intro g hg h hh hgh x hx s hs w hw hcapg hcaph
  have hcapgK : closure g ∩ K.V = {x, w} := (hKK.closure_inter_V hg).symm.trans hcapg
  have hcaphK : closure h ∩ K.V = {x, w} := (hKK.closure_inter_V hh).symm.trans hcaph
  by_cases hsY : s = Y
  · subst s
    have hwu : w = u :=
      (radialDiscDeletion_merged_hub hK hC hb hCV hr hur huK).unique hw ⟨Or.inl hur, huNew⟩
    subst w
    exact no_empty_bigon_in_merged_region hS hK hC hD hb hCZ hr hv hur huK hfC hf
      hg hh hgh (hΓ.1 hx) hcapgK hcaphK
  · have hsOld := region_mem_of_ne_merged_region hΓ hY hcover hs hsY
    exact hK.2.2.2.2.2 g (hKK.2 hg) h (hKK.2 hh) hgh x (hΓ.1 hx) s hsOld
      w ⟨hw.1, hKK.1 hw.2⟩ hcapgK hcaphK

end GraphMinor.GM12
