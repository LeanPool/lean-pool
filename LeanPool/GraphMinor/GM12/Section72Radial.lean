/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section72MergedParallel
public import LeanPool.GraphMinor.GM12.Section72OtherParallel
public import LeanPool.GraphMinor.GM12.Section72MaximalCriterion
import LeanPool.GraphMinor.GM12.Section72TwoCell
import LeanPool.GraphMinor.GM11.Section810

/-!
# The radial drawing after the one-vertex disc deletion

This proves the radial construction in XII (7.2), page 260. Keep the
closed outside of the two-spoke circuit and delete one boundary
spoke. The reduced drawing is two-cell, and the radial conditions
are proved in the preceding lemmas. For maximality, every possible
extra spoke has an old parallel spoke in an unchanged region, or a
retained parallel spoke obtained by diversion in the merged region.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- The radial construction in XII (7.2), page 260: deleting one
boundary spoke and all radial pieces strictly inside the two-spoke
circuit gives a radial drawing of the reduced drawing. -/
theorem radialDiscDeletion_isRadial
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {Γ K C : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K) (hC : C.IsSubdrawing K)
    {D r e f : Set S} {v u : S} (hD : IsClosedDisc D) (hb : frontier D = C.U)
    (hCE : C.E = {e, f}) (hCV : C.V = {v, u}) (hef : e ≠ f)
    (hCU : C.U = closure e ∪ closure f) (hCZ : C.U ⊆ r ∪ {v})
    (he : K.toGraph.IsLink e v u) (hf : K.toGraph.IsLink f v u)
    (hmeet : Γ.U ∩ C.U = {v}) (hr : r ∈ Γ.R) (hv : v ∈ Γ.V)
    (hur : u ∈ r) (huK : u ∈ K.V) :
    (PaintingOrDrawing.drawing (Γ.interSet (closure (univ \ D)))).IsRadialDrawing
      (radialDiscDeletion K D f) := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  let Γ' := Γ.interSet (closure (univ \ D))
  let K' := radialDiscDeletion K D f
  let Y := r ∪ (D \ {v})
  have hfC : f ∈ C.E := hCE.symm ▸ Or.inr rfl
  have hΓ : Γ'.IsSubdrawing Γ := Drawing.span_isSubdrawing Γ _ _
  obtain ⟨hn, hvC, hFV, hFr, hY, hcover⟩ :=
    radialDiscDeletion_region_facts hS hD hb hr hv hCZ hmeet
  have hbd : subBd D = C.U := (subBd_eq_frontier D).trans hb
  have htwo : (PaintingOrDrawing.drawing Γ').IsTwoCell :=
    theorem_7_2_twoCell hS hK.1 hD hbd hn hFV hr hFr
  have hpre : (PaintingOrDrawing.drawing Γ').IsPreRadialDrawing K' :=
    radialDiscDeletion_isPreRadial hS hK.2.1 hC hD hb hCV hr hv hur huK hCZ hmeet hfC hf
  have huNew : u ∈ K'.V := radialDiscDeletion_mem_vertexSet_of_mem_frontier
    (hb.symm ▸ C.V_subset_U (hCV.symm ▸ Or.inr rfl)) huK
  have hvNew : v ∈ Γ'.V := by
    have hvf : v ∈ frontier D := hb.symm ▸ hvC
    rw [frontier_eq_closure_inter_closure] at hvf
    exact (mem_interSet_V_iff isClosed_closure).mpr
      ⟨hv, by simpa only [compl_eq_univ_sdiff] using hvf.2⟩
  refine ⟨htwo, hpre, radMax_of_parallel_spokes hS htwo hpre ?_⟩
  intro s hs w hw x hx L hL hwx hLs hLK
  by_cases hsY : s = Y
  · subst s
    have hwu : w = u :=
      (radialDiscDeletion_merged_hub hK.2.1 hC hb hCV hr hur huK).unique hw ⟨Or.inl hur, huNew⟩
    subst w
    exact exists_parallel_spoke_in_merged_region hS hK hC hD hb hCE hCV hef hCU hCZ
      he hf hmeet hr hv hur huK hx hL hLs hLK
  · have hsOld := region_mem_of_ne_merged_region hΓ hY hcover hs hsY
    have hsD : Disjoint s D := by
      apply disjoint_left.mpr
      intro y hys hyD
      have hyv : y ≠ v := fun hyv => region_subset hs (hyv ▸ hys) (Γ'.V_subset_U hvNew)
      exact hsY (region_eq_of_mem hs hY hys (Or.inr ⟨hyD, hyv⟩))
    exact exists_parallel_spoke_in_unchanged_region hS hK hC hD hb hfC hsOld hsD hw hx hL hwx hLs
      hLK

end GraphMinor.GM12
