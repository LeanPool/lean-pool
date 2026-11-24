/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section72RadialDeletion
import LeanPool.GraphMinor.GM11.RadialCorners
import LeanPool.GraphMinor.GM11.Section810
import LeanPool.GraphMinor.Surface.DiscGrow

/-!
# The fixed boundary of the radial deletion

For the maximality argument in XII (7.2), page 260, the reduced old
drawing meets the removed disc only at the boundary vertex. The
retained radial drawing meets it in the retained boundary spoke.
These facts let the disc-pushing map fix both retained drawings.
An old radial edge with an end outside the disc also survives.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

variable {S : Type*} [TopologicalSpace S] [T2Space S]

/-- A boundary spoke different from the deleted spoke survives. -/
theorem boundary_spoke_retained {K C : Drawing S} (hC : C.IsSubdrawing K)
    {D e f : Set S} (hb : frontier D = C.U) (he : e ∈ C.E) (hef : e ≠ f) :
    e ∈ (radialDiscDeletion K D f).E := by
  rw [radialDiscDeletion_E]
  refine ⟨hC.2 he, ?_, hef⟩
  intro y hy
  have hybd : y ∈ frontier D := hb.symm ▸ (he.2.1 hy).1
  rw [frontier_eq_closure_inter_closure] at hybd
  simpa only [compl_eq_univ_sdiff] using hybd.2

/-- Inside the removed disc, the retained radial drawing is exactly
the closure of the retained boundary spoke. -/
theorem radialDiscDeletion_inter_disc {K C : Drawing S} (hC : C.IsSubdrawing K)
    {D e f : Set S} {v u : S} (hD : IsClosedDisc D) (hb : frontier D = C.U)
    (he : e ∈ C.E) (hf : f ∈ C.E) (hef : e ≠ f)
    (hCU : C.U = closure e ∪ closure f)
    (hcapf : closure f ∩ K.V = {v, u}) (hcape : closure e ∩ K.V = {v, u}) :
    (radialDiscDeletion K D f).U ∩ D = closure e := by
  have heNew := boundary_spoke_retained hC hb he hef
  apply Subset.antisymm
  · rintro y ⟨hyK, hyD⟩
    obtain ⟨⟨_, hyOut⟩, hynf⟩ := (radialDiscDeletion_U hC hb hf).subset hyK
    have hybd : y ∈ frontier D := by
      rw [frontier_eq_closure_inter_closure]
      exact ⟨subset_closure hyD, by simpa only [compl_eq_univ_sdiff] using hyOut⟩
    rcases hCU.subset (hb ▸ hybd) with hye | hyf
    · exact hye
    · have hyV : y ∈ K.V := by
        by_contra hnV
        exact hynf ((K.closure_diff_V (hC.2 hf)).subset ⟨hyf, hnV⟩)
      exact (hcape.superset (hcapf.subset ⟨hyf, hyV⟩)).1
  · intro y hye
    refine ⟨(radialDiscDeletion K D f).closure_subset_U heNew hye, ?_⟩
    have hybd : y ∈ frontier D := hb.symm ▸ C.closure_subset_U he hye
    exact hD.isClosed.closure_subset_iff.mpr subset_rfl hybd.1

/-- The retained old drawing meets the removed disc only at its one
old boundary vertex. -/
theorem oldDrawing_outside_inter_disc {Γ C : Drawing S} {D : Set S} {v : S}
    (hb : frontier D = C.U) (hmeet : Γ.U ∩ C.U = {v}) :
    (Γ.interSet (closure (univ \ D))).U ∩ D ⊆ {v} := by
  rintro y ⟨hyΓ, hyD⟩
  have hyOut := interSet_U_subset isClosed_closure hyΓ
  have hybd : y ∈ frontier D := by
    rw [frontier_eq_closure_inter_closure]
    exact ⟨subset_closure hyD, by simpa only [compl_eq_univ_sdiff] using hyOut⟩
  exact hmeet.subset ⟨(Drawing.span_isSubdrawing Γ _ _).U_subset hyΓ, hb ▸ hybd⟩

/-- A retained old vertex other than the boundary vertex is outside
the whole removed disc. -/
theorem retained_vertex_notMem_disc {Γ C : Drawing S} {D : Set S} {v x : S}
    (hb : frontier D = C.U) (hmeet : Γ.U ∩ C.U = {v})
    (hx : x ∈ (Γ.interSet (closure (univ \ D))).V) (hxv : x ≠ v) : x ∉ D := by
  intro hxD
  exact hxv (oldDrawing_outside_inter_disc hb hmeet
    ⟨(Γ.interSet (closure (univ \ D))).V_subset_U hx, hxD⟩)

/-- An old edge with an end outside the disc is retained by the
radial deletion. The boundary is a subdrawing, so it cannot cut that
edge into an inside part and an outside part. -/
theorem edge_retained_of_end_outside_disc (hS : IsClosedSurface S)
    {K C : Drawing S} (hC : C.IsSubdrawing K) {D f g : Set S}
    (hD : IsClosedDisc D) (hb : frontier D = C.U) (hf : f ∈ C.E)
    (hg : g ∈ K.E) {x : S} (hx : x ∈ closure g) (hxD : x ∉ D) :
    g ∈ (radialDiscDeletion K D f).E := by
  have hCD : C.U ⊆ D := by
    intro y hy
    have hybd : y ∈ frontier D := hb.symm ▸ hy
    exact hD.isClosed.closure_subset_iff.mpr subset_rfl hybd.1
  have hdis : Disjoint g (discBd D) := by
    apply disjoint_left.mpr
    intro y hyg hybd
    have hyC : y ∈ C.U := hb ▸ (IsClosedDisc.frontier_eq_discBd hS hD).symm ▸ hybd
    have hgC := edge_mem_of_meets_subdrawing hC hg ⟨y, hyg, hyC⟩
    exact hxD (hCD (C.closure_subset_U hgC hx))
  have hout : Disjoint g D := by
    rcases hD.side (fun y => (hS.2.2 y).isManifoldPoint) hg.2.2.1.isConnected.isPreconnected hdis
      with hin | hout
    · exact (hxD ((closure_minimal (hin.trans (discInt_subset D)) hD.isClosed) hx)).elim
    · exact hout
  have hgf : g ≠ f := by
    intro hgf
    obtain ⟨y, hyg⟩ := hg.1
    exact disjoint_left.mp hout hyg (hCD ((hgf.symm ▸ hf).2.1 hyg).1)
  rw [radialDiscDeletion_E]
  exact ⟨hg, fun y hy => subset_closure ⟨mem_univ _, disjoint_left.mp hout hy⟩, hgf⟩

end GraphMinor.GM12
