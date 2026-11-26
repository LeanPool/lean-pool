/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section72RadialDeletion
public import LeanPool.GraphMinor.GM12.Section72Regions
import LeanPool.GraphMinor.GM12.Section77
import LeanPool.GraphMinor.GM12.Section76
import LeanPool.GraphMinor.GM11.Section810
import LeanPool.GraphMinor.GM11.Section87

/-!
# Region hubs after the radial deletion in XII (7.2)

The merged region retains the old hub on the two-spoke boundary.
Any retained radial vertex in the removed disc lies on its boundary,
whose only vertices are the old vertex and that hub. Every other
region of the reduced drawing is an old region. Its old hub remains
outside the removed disc.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

variable {S : Type*} [TopologicalSpace S] [T2Space S]

/-- The merged region in XII (7.2), page 260, retains precisely the
old hub after deleting the interior radial pieces and one spoke. -/
theorem radialDiscDeletion_merged_hub {Γ K C : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsPreRadialDrawing K)
    (hC : C.IsSubdrawing K) {D r f : Set S} {v u : S}
    (hb : frontier D = C.U) (hCV : C.V = {v, u})
    (hr : r ∈ Γ.R) (hur : u ∈ r) (huK : u ∈ K.V) :
    ∃! w, w ∈ r ∪ (D \ {v}) ∧ w ∈ (radialDiscDeletion K D f).V := by
  have huC : u ∈ C.U := C.V_subset_U (hCV.symm ▸ Or.inr rfl)
  have huOut : u ∈ closure (univ \ D) := by
    have huf : u ∈ frontier D := hb.symm ▸ huC
    rw [frontier_eq_closure_inter_closure] at huf
    simpa only [compl_eq_univ_sdiff] using huf.2
  refine ⟨u, ⟨Or.inl hur, radialDiscDeletion_V K D f |>.symm ▸ ⟨huK, huOut⟩⟩, ?_⟩
  rintro w ⟨hwY, hwK'⟩
  obtain ⟨hwK, hwOut⟩ := (radialDiscDeletion_V K D f).subset hwK'
  rcases hwY with hwr | ⟨hwD, hwv⟩
  · exact (hK.2.2.1 r hr).unique ⟨hwr, hwK⟩ ⟨hur, huK⟩
  · have hwfront : w ∈ frontier D := by
      rw [frontier_eq_closure_inter_closure]
      exact ⟨subset_closure hwD, by simpa only [compl_eq_univ_sdiff] using hwOut⟩
    have hwCV : w ∈ C.V := mem_V_of_mem_U' hC (hb ▸ hwfront) hwK
    rcases hCV.subset hwCV with hwv' | hwu
    · exact (hwv hwv').elim
    · exact hwu

omit [T2Space S] in
/-- If the deleted drawing points are all in one new region, every
other new region is an old region. This is the region classification
used in XII (7.2), page 260. -/
theorem region_mem_of_ne_merged_region {Γ Γ' : Drawing S}
    (hΓ : Γ'.IsSubdrawing Γ) {Y s : Set S} (hY : Y ∈ Γ'.R)
    (hcover : Γ.U ⊆ Γ'.U ∪ Y) (hs : s ∈ Γ'.R) (hsY : s ≠ Y) : s ∈ Γ.R := by
  have hoff : s ⊆ univ \ Γ.U := by
    intro x hx
    refine ⟨mem_univ _, fun hxΓ => ?_⟩
    rcases hcover hxΓ with hxΓ' | hxY
    · exact region_subset hs hx hxΓ'
    · exact hsY (region_eq_of_mem hs hY hx hxY)
  obtain ⟨x, hx⟩ := region_nonempty hs
  let R := connectedComponentIn (univ \ Γ.U) x
  have hR : R ∈ Γ.R := (mem_R_iff Γ).mpr ⟨x, (hoff hx).2, rfl⟩
  have hxR : x ∈ R := mem_connectedComponentIn (hoff hx)
  have hsR : s ⊆ R := (region_isPreconnected hs).subset_connectedComponentIn hx hoff
  have hRs : R ⊆ s := region_subset_region_of_inter_nonempty hΓ hR hs ⟨x, hxR, hx⟩
  exact (Subset.antisymm hsR hRs).symm ▸ hR

/-- Every region retains exactly one hub in the radial deletion of
XII (7.2), page 260. The merged region keeps its boundary hub, and
all other regions keep their original hubs outside the removed disc. -/
theorem radialDiscDeletion_region_hubs (hS : IsClosedSurface S)
    {Γ K C : Drawing S} (hK : (PaintingOrDrawing.drawing Γ).IsPreRadialDrawing K)
    (hC : C.IsSubdrawing K) {D r f : Set S} {v u : S}
    (hD : IsClosedDisc D) (hb : frontier D = C.U) (hCV : C.V = {v, u})
    (hr : r ∈ Γ.R) (hv : v ∈ Γ.V) (hur : u ∈ r) (huK : u ∈ K.V)
    (hCZ : C.U ⊆ r ∪ {v}) (hmeet : Γ.U ∩ C.U = {v}) :
    ∀ s ∈ (Γ.interSet (closure (univ \ D))).R,
      ∃! w, w ∈ s ∧ w ∈ (radialDiscDeletion K D f).V := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  let Γ' := Γ.interSet (closure (univ \ D))
  let Y := r ∪ (D \ {v})
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
  have hcover : Γ.U ⊆ Γ'.U ∪ Y :=
    (drawing_U_subset_outside_normal_disc_union hb hn hvC).trans
      (union_subset_union subset_rfl subset_union_right)
  intro s hs
  by_cases hsY : s = Y
  · subst s
    exact radialDiscDeletion_merged_hub hK hC hb hCV hr hur huK
  · have hsOld := region_mem_of_ne_merged_region
      (Drawing.span_isSubdrawing Γ _ _) hY hcover hs hsY
    obtain ⟨w, hw, huniq⟩ := hK.2.2.1 s hsOld
    have hwD : w ∉ D := by
      intro hwD
      have hwv : w ≠ v := fun hwv => region_subset hsOld (hwv ▸ hw.1) (Γ.V_subset_U hv)
      exact hsY (region_eq_of_mem hs hY hw.1 (Or.inr ⟨hwD, hwv⟩))
    have hwOut : w ∈ closure (univ \ D) := subset_closure ⟨mem_univ _, hwD⟩
    refine ⟨w, ⟨hw.1, (radialDiscDeletion_V K D f).symm ▸ ⟨hw.2, hwOut⟩⟩, ?_⟩
    rintro z ⟨hzs, hzK⟩
    exact huniq z ⟨hzs, ((radialDiscDeletion_V K D f).subset hzK).1⟩

end GraphMinor.GM12
