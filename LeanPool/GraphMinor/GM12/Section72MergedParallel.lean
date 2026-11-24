/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section72ParallelReplacement
public import LeanPool.GraphMinor.GM12.Section72RetainedBoundary
public import LeanPool.GraphMinor.GM12.Section72PushSpoke
import LeanPool.GraphMinor.GM11.Section810
import LeanPool.GraphMinor.Surface.SurfaceGraph

/-!
# Every extra spoke in the merged region has a retained parallel spoke

For maximality in XII (7.2), page 260, divert an extra spoke off the
removed disc while fixing both retained drawings. Old maximality
provides a parallel old spoke. If its old end is not the boundary
vertex, it survives. At the boundary vertex, the parallel-spoke
replacement lemma handles the deleted spoke. Pull the resulting disc
back by the diversion to compare with the original extra spoke.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- The extra-spoke comparison in the merged region, completing its
part of the maximality verification in XII (7.2), page 260. -/
theorem exists_parallel_spoke_in_merged_region
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {Γ K C : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K) (hC : C.IsSubdrawing K)
    {D r e f : Set S} {v u : S} (hD : IsClosedDisc D) (hb : frontier D = C.U)
    (hCE : C.E = {e, f}) (hCV : C.V = {v, u}) (hef : e ≠ f)
    (hCU : C.U = closure e ∪ closure f) (hCZ : C.U ⊆ r ∪ {v})
    (he : K.toGraph.IsLink e v u) (hf : K.toGraph.IsLink f v u)
    (hmeet : Γ.U ∩ C.U = {v}) (hr : r ∈ Γ.R) (hv : v ∈ Γ.V)
    (hur : u ∈ r) (huK : u ∈ K.V)
    {x : S} (hx : x ∈ (Γ.interSet (closure (univ \ D))).V)
    {L : Set S} (hL : IsLineWithEnds L u x)
    (hLY : L \ {u, x} ⊆ r ∪ (D \ {v}))
    (hLK : Disjoint (L \ {u, x}) (radialDiscDeletion K D f).U) :
    ∃ g ∈ (radialDiscDeletion K D f).E,
      closure g ∩ (radialDiscDeletion K D f).V = {x, u} ∧
      ∃ P : Set S, IsClosedDisc P ∧ P ⊆ (r ∪ (D \ {v})) ∪ {x} ∧
        subBd P = closure g ∪ L := by
  let Γ' := Γ.interSet (closure (univ \ D))
  let K' := radialDiscDeletion K D f
  let Y := r ∪ (D \ {v})
  let G := Γ'.U ∪ K'.U
  have hΓ : Γ'.IsSubdrawing Γ := Drawing.span_isSubdrawing Γ _ _
  have hKK : K'.IsSubdrawing K := radialDiscDeletion_isSubdrawing K D f
  have heC : e ∈ C.E := hCE.symm ▸ Or.inl rfl
  have hfC : f ∈ C.E := hCE.symm ▸ Or.inr rfl
  have heNew : e ∈ K'.E := boundary_spoke_retained hC hb heC hef
  have hEline : IsLineWithEnds (closure e) v u :=
    isLine_closure he.1 (fun hvu => region_subset hr (hvu ▸ hur) (Γ.V_subset_U hv)) he.2.2.2
  have hbdD : discBd D = C.U := (IsClosedDisc.frontier_eq_discBd hS hD).symm.trans hb
  have hEbd : closure e ⊆ discBd D := hbdD.symm ▸ C.closure_subset_U heC
  have hEU : closure e ⊆ K'.U := K'.closure_subset_U heNew
  have hvG : v ∈ G := Or.inr (hEU ((he.2.2.2.superset (Or.inl rfl)).1))
  have huG : u ∈ G := Or.inr (hEU ((he.2.2.2.superset (Or.inr rfl)).1))
  have hxG : x ∈ G := Or.inl (Γ'.V_subset_U hx)
  have hGD : G ∩ D ⊆ closure e := by
    rintro y ⟨hyΓ | hyK, hyD⟩
    · have hyv := oldDrawing_outside_inter_disc hb hmeet ⟨hyΓ, hyD⟩
      exact (he.2.2.2.superset (Or.inl (mem_singleton_iff.mp hyv))).1
    · exact (radialDiscDeletion_inter_disc hC hD hb heC hfC hef hCU hf.2.2.2 he.2.2.2).subset ⟨hyK,
        hyD⟩
  have hn : (PaintingOrDrawing.drawing Γ).IsNormal C.U := by
    rintro y ⟨hyC, hyΓ⟩
    exact mem_singleton_iff.mp (hmeet.subset ⟨hyΓ, hyC⟩) ▸ hv
  have hFV : C.U ∩ Γ.V = {v} := by
    apply Subset.antisymm
    · rintro y ⟨hyC, hyΓ⟩
      exact hmeet.subset ⟨Γ.V_subset_U hyΓ, hyC⟩
    · rintro y hy
      have hyv := mem_singleton_iff.mp hy
      subst y
      exact ⟨C.V_subset_U (hCV.symm ▸ Or.inl rfl), hv⟩
  have hY : Y ∈ Γ'.R := theorem_7_2_region hS hD ((subBd_eq_frontier D).trans hb)
    hn hFV hr (fun y hy => (hCZ hy.1).resolve_right hy.2)
  have hLG : L ∩ G ⊆ {x, u} := by
    rintro y ⟨hyL, hyG⟩
    by_contra hyn
    have hyn' : y ∉ ({u, x} : Set S) := by simpa only [pair_comm] using hyn
    rcases hyG with hyΓ | hyK
    · exact region_subset hY (hLY ⟨hyL, hyn'⟩) hyΓ
    · exact disjoint_left.mp hLK ⟨hyL, hyn'⟩ hyK
  have hLE : L ∩ closure e ⊆ {v, u} := by
    rintro y ⟨hyL, hye⟩
    rcases hLG ⟨hyL, Or.inr (hEU hye)⟩ with hyx | hyu
    · have hyv : y = v := hmeet.subset
        ⟨hyx.symm ▸ Γ.V_subset_U (hΓ.1 hx), C.closure_subset_U heC hye⟩
      exact Or.inl hyv
    · exact Or.inr hyu
  obtain ⟨a, hfix, hpush, hdis⟩ := push_extra_spoke_off_disc hS hC hD hb hfC hEline hEbd
    (Γ'.isClosed_U.union K'.isClosed_U) hvG huG hGD subset_union_right
    hL.isCompact.isClosed hLE hLG
  have hfixΓ : ∀ y ∈ Γ'.U, a y = y := fun y hy => hfix y (Or.inl hy)
  have hfixK : ∀ y ∈ K'.U, a y = y := fun y hy => hfix y (Or.inr hy)
  have hau : a u = u := hfix u huG
  have hax : a x = x := hfix x hxG
  have haY : a '' Y ⊆ Y := image_region_subset_of_fixed a hfixΓ hY (Or.inl hur) hau
  have hline : IsLineWithEnds (a '' L) u x := by
    simpa only [hau, hax] using lineWithEnds_image_homeomorph a hL
  have hux : u ≠ x := fun hux => region_subset hr (hux ▸ hur) (Γ.V_subset_U (hΓ.1 hx))
  have hlineR : (a '' L) \ {u, x} ⊆ r := by
    rintro y ⟨⟨z, hzL, hzy⟩, hyn⟩
    have hzn : z ∉ ({u, x} : Set S) := by
      rintro (hzu | hzx)
      · exact hyn (Or.inl (hzy.symm.trans ((congrArg a hzu).trans hau)))
      · exact hyn (Or.inr (hzy.symm.trans ((congrArg a hzx).trans hax)))
    have hyY := haY ⟨z, hLY ⟨hzL, hzn⟩, hzy⟩
    rcases hyY with hyr | ⟨hyD, _⟩
    · exact hyr
    · have hyend := hpush ⟨⟨z, hzL, hzy⟩, hyD⟩
      have hyK : y ∈ K.U := by
        rcases hyend with hyv | hyu
        · exact hyv ▸ K.V_subset_U (hK.2.1.2.1 hv)
        · exact hyu ▸ K.V_subset_U huK
      exact (disjoint_left.mp hdis ⟨⟨z, hzL, hzy⟩, by simpa only [pair_comm] using hyn⟩ hyK).elim
  have hdis' : Disjoint ((a '' L) \ {u, x}) K.U := by simpa only [pair_comm] using hdis
  obtain ⟨g, hg, hcapg, Q, hQ, hQr, hQbd⟩ := parallel_of_line ⟨hK.1, hK.2.1⟩ hK.2.2 hS
    hr hur huK (hΓ.1 hx) hline hux hlineR hdis'
  have finish : ∀ g ∈ K'.E, closure g ∩ K.V = {x, u} →
      ∀ Q : Set S, IsClosedDisc Q → Q ⊆ Y ∪ {x} → subBd Q = closure g ∪ a '' L →
      ∃ g ∈ K'.E, closure g ∩ K'.V = {x, u} ∧
        ∃ P : Set S, IsClosedDisc P ∧ P ⊆ Y ∪ {x} ∧ subBd P = closure g ∪ L := by
    intro g hg hcap Q hQ hQr hQbd
    obtain ⟨P, hP, hPr, hPbd⟩ := pullback_spoke_disc hS a hfixΓ hfixK hY
      (Or.inl hur) hau hax hg hQ hQr hQbd
    exact ⟨g, hg, (hKK.closure_inter_V hg).trans hcap, P, hP, hPr, hPbd⟩
  by_cases hxv : x = v
  · subst x
    have hbdQ : discBd Q = closure g ∪ a '' L :=
      (IsClosedDisc.frontier_eq_discBd hS hQ).symm.trans ((subBd_eq_frontier Q).symm.trans hQbd)
    rcases parallel_spoke_retained_or_replaced hS hK.2.1 hC hD hbdD hCE hef hCU
        he hf hr hv hur huK hg hcapg (Surface.IsLineWithEnds.symm hline) hpush
        (by simpa only [pair_comm] using hdis') hQ hQr hbdQ with hgNew | hreplace
    · exact finish g hgNew hcapg Q hQ (hQr.trans (union_subset_union_left _ subset_union_left)) hQbd
    · obtain ⟨P, hP, hPr, hPbd⟩ := hreplace
      exact finish e heNew he.2.2.2 P hP hPr hPbd
  · have hxD := retained_vertex_notMem_disc hb hmeet hx hxv
    have hxcl : x ∈ closure g := (hcapg.superset (Or.inl rfl)).1
    have hgNew := edge_retained_of_end_outside_disc hS hC hD hb hfC hg hxcl hxD
    exact finish g hgNew hcapg Q hQ (hQr.trans (union_subset_union_left _ subset_union_left)) hQbd

end GraphMinor.GM12
