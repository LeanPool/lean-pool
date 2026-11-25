/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Battlefields
public import LeanPool.GraphMinor.GM16.Cited
public import LeanPool.GraphMinor.GM14.Cited
import LeanPool.GraphMinor.GM14.Section9a
import LeanPool.GraphMinor.GM14.Section7b
import LeanPool.GraphMinor.GM14.Section6c
import LeanPool.GraphMinor.GM14.Section5
import LeanPool.GraphMinor.GM14.Section3b
import LeanPool.GraphMinor.GM09.PlanarNests
import LeanPool.GraphMinor.GM11.RadialFacts
import LeanPool.GraphMinor.GM11.Section6
import LeanPool.GraphMinor.GM11.Theorem63
import LeanPool.GraphMinor.Thomas.Separator
import LeanPool.GraphMinor.Menger.Basic

import LeanPool.GraphMinor.GM12.Section710
import LeanPool.GraphMinor.Surface.SurfaceGraph

/-!
# Graph Minors XIV, Section 9 (Part 2): Rigid Zones (9.3) and Battlefields (9.5)

This file formalizes (9.3) and (9.5) of N. Robertson and P. D. Seymour,
*Graph Minors. XIV. Extending an embedding*, J. Combin. Theory Ser. B **65** (1995) 23–50
(pages 44–47):

- `enlarge_disc_past_disconnected_region`: if a circuit `C` of a rigid drawing `H` bounds an open
  disc `Λ` with `closure Λ ⊆ Δ_out \ subBd Δ_out` (`subBd Δ_out ⊆ H.U`) and
  `clearedSubdrawing H Λ` is not rigid, then by (6.3) and (5.2) there is a circuit `C'` of `H`
  bounding a strictly larger open disc `Λ'` in `Δ_out \ subBd Δ_out` containing `Λ` and at least
  one edge `e₀ ∈ C.E`.
- `theorem_9_3`: Graph Minors XIV, (9.3) (pages 44–45), proving `GM16.GM14Theorem93Statement`.
- `theorem_9_5`: Graph Minors XIV, (9.5) (pages 45–47), proving `GM16.GM14Theorem95Statement`.
-/

@[expose] public section

namespace GraphMinor.GM14

open Set Function Topology Graph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM09.PlanarNests
  GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM16 GraphMinor.Thomas Hypergraph

universe u w

variable {S : Type w} [TopologicalSpace S]

/-! ## 1. Enlarging a Disc Past a Disconnected Region -/

private theorem exists_edge_of_mem_walk_support {P : Drawing S} {a b : S}
    (W : GraphWalk P.toGraph a b) (hpos : 0 < W.length) {v : S} (hv : v ∈ W.support) :
    ∃ e ∈ W.edges, v ∈ closure e := by
  induction W with
  | nil _ => exact absurd hpos (Nat.lt_irrefl 0)
  | @cons u₀ w₀ c e hl r ih =>
    rcases List.mem_cons.mp hv with rfl | hvr
    · have : v ∈ closure e ∩ P.V := by rw [hl.2.2.2]; exact Or.inl rfl
      exact ⟨e, List.mem_cons_self, this.1⟩
    · cases r with
      | nil _ =>
        rcases List.mem_singleton.mp hvr with rfl
        have : v ∈ closure e ∩ P.V := by rw [hl.2.2.2]; exact Or.inr rfl
        exact ⟨e, List.mem_cons_self, this.1⟩
      | cons hl' r' =>
        obtain ⟨f, hf, hvf⟩ := ih (Nat.succ_pos _) hvr
        exact ⟨f, List.mem_cons_of_mem _ hf, hvf⟩

private theorem disc_on_other_side_gives_larger_zone
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    [ConnectedSpace S]
    (hS : IsClosedSurface S)
    {H : Drawing S}
    {C : Drawing S}
    {Δ_out : Set S}
    {Λ : Set S}
    (hΔ_out : IsClosedDisc Δ_out)
    (hC : C.IsCircuit)
    (hCs : C.IsSubdrawing H)
    (hΛ_open : IsOpenDisc Λ)
    (hΛ_cl : IsClosedDisc (closure Λ))
    (hbd_cl : subBd (closure Λ) = C.U)
    (hdiff : closure Λ \ C.U = Λ)
    (hcl_sub : closure Λ ⊆ Δ_out \ subBd Δ_out)
    (r : Set S)
    (v₁ : S)
    (v₂ : S)
    (F₂ : Set S)
    (P₂ : Drawing S)
    (hr : r ∈ H.R)
    (hdis_rΛ : Disjoint r Λ)
    (hv12 : v₁ ≠ v₂)
    (hv₁C : v₁ ∈ C.V)
    (hv₂C : v₂ ∈ C.V)
    (hF₂_r : F₂ \ {v₁, v₂} ⊆ r)
    (hCU_sub_cl : C.U ⊆ closure Λ)
    (hCU_sub_int : C.U ⊆ Δ_out \ subBd Δ_out)
    (hfr_out : frontier Δ_out = subBd Δ_out)
    (hF₂_sub_int : F₂ ⊆ Δ_out \ subBd Δ_out)
    (hI_2F : P₂.U ∩ F₂ = {v₁, v₂}) :
    ∀ (P P' : Drawing S) (D_big : Set S), P.IsSubdrawing C → P'.IsSubdrawing C → P.IsPathBetween
      v₁ v₂ → Disjoint P.E P'.E → C.U = P.U ∪ P'.U → ¬P.U ⊆ closure r → D_big ⊆ Δ_out →
      IsClosedDisc D_big → discBd D_big = F₂ ∪ P'.U → P.U ⊆ D_big → ∃ (C' : Drawing S) (Λ' : Set S),
      C'.IsSubdrawing H ∧
      C'.IsCircuit ∧ C'.U ⊆ Δ_out \ subBd Δ_out ∧ IsOpenDisc Λ' ∧ closure Λ' ⊆ Δ_out \ subBd Δ_out
      ∧ IsClosedDisc (closure Λ') ∧ subBd Λ' = C'.U ∧ subBd (closure Λ') = C'.U ∧ closure Λ' \
      C'.U = Λ' ∧ Λ ⊆ Λ' ∧ closure Λ ⊆ closure Λ' ∧ {e | e ∈ H.E ∧ e ⊆ Λ}.ncard < {e | e ∈ H.E ∧ e
      ⊆ Λ'}.ncard := by
  intro P P' D_big hPC hP'C hP_path hPE_dis hCU_PP' hnot_P_r hD_sub hD_disc hD_bd hPU_D
  have hPH : P.IsSubdrawing H := hPC.trans hCs
  have hP'H : P'.IsSubdrawing H := hP'C.trans hCs
  have hD_cl : IsClosed D_big := hD_disc.isCompact.isClosed
  have hD_fr : frontier D_big = F₂ ∪ P'.U :=
    (IsClosedDisc.frontier_eq_discBd hS hD_disc).trans hD_bd
  have hD_subBd : subBd D_big = F₂ ∪ P'.U := by
    rw [subBd_eq_frontier, hD_fr]
  have hfr_in_D : F₂ ∪ P'.U ⊆ D_big := hD_fr ▸ hD_cl.frontier_subset
  have hCU_in_D : C.U ⊆ D_big :=
    hCU_PP' ▸ union_subset hPU_D (subset_union_right.trans hfr_in_D)
  -- Show `closure Λ ⊆ D_big`.
  have hclΛ_in_D : closure Λ ⊆ D_big := by
    obtain ⟨D₀, ⟨hD₀_sub, hD₀_disc, hD₀_bd, -⟩, _⟩ :=
      disc_oArc D_big C.U hD_disc hCU_in_D (isOArc_of_isCircuit hC)
    obtain ⟨_, huniq_out⟩ := discIns_spec hΔ_out hC (hCU_sub_int.trans sdiff_subset)
    have h1 : D₀ = discIns Δ_out C := huniq_out D₀ (hD₀_sub.trans hD_sub) hD₀_disc hD₀_bd
    have h2 : closure Λ = discIns Δ_out C :=
      huniq_out (closure Λ) (hcl_sub.trans sdiff_subset) hΛ_cl
        ((IsClosedDisc.subBd_eq_discBd hS hΛ_cl).symm.trans hbd_cl)
    exact (h2.trans h1.symm) ▸ hD₀_sub
  -- Show `D_big ⊆ Δ_out \ subBd Δ_out`.
  have hD_sub_int : D_big ⊆ Δ_out \ subBd Δ_out := by
    intro x hxD
    refine ⟨hD_sub hxD, fun hxbd => ?_⟩
    have hx_fr_out : x ∈ frontier Δ_out := hfr_out.symm ▸ hxbd
    have hx_fr_D : x ∈ frontier D_big :=
      ⟨subset_closure hxD, fun hxi => hx_fr_out.2 (interior_mono hD_sub hxi)⟩
    rw [hD_fr] at hx_fr_D
    rcases hx_fr_D with hxF₂ | hxP'
    · exact (hF₂_sub_int hxF₂).2 hxbd
    · exact (hCU_sub_int (hP'C.U_subset hxP')).2 hxbd
  -- Find an edge `e₀ ∈ P.E` with `¬ e₀ ⊆ closure r`.
  have hex_e₀ : ∃ e₀ ∈ P.E, ¬ e₀ ⊆ closure r := by
    by_contra hno_e₀
    push Not at hno_e₀
    apply hnot_P_r
    obtain ⟨W, _, hPV, hPE⟩ := hP_path
    have hW_pos : 0 < W.length := by
      cases W with
      | nil _ => exact absurd rfl hv12
      | cons _ _ => exact Nat.succ_pos _
    rw [P.U_eq]
    refine union_subset ?_ (iUnion₂_subset fun e he =>
      isClosed_closure.closure_subset_iff.mpr (hno_e₀ e he))
    intro v hv
    rw [hPV, mem_ofPred_eq] at hv
    obtain ⟨e, he, hve⟩ := exists_edge_of_mem_walk_support W hW_pos hv
    have heP : e ∈ P.E := by rw [hPE]; exact he
    exact isClosed_closure.closure_subset_iff.mpr (hno_e₀ e heP) hve
  obtain ⟨e₀, he₀P, hnot_e₀_r⟩ := hex_e₀
  have he₀C : e₀ ∈ C.E := hPC.2 he₀P
  have he₀H : e₀ ∈ H.E := hCs.2 he₀C
  have hdis_cl_r_e₀ : Disjoint (closure r) e₀ := by
    rw [disjoint_iff_inter_eq_empty, ← not_nonempty_iff_eq_empty]
    rintro ⟨p, hpr, hpe₀⟩
    exact hnot_e₀_r (edge_subset_closure_of_incident hS he₀H hr ⟨p, hpe₀, hpr⟩)
  have hdis_cl_r_Λ : Disjoint (closure r) Λ :=
    Disjoint.closure_left hdis_rΛ hΛ_open.1
  have he₀_sub_CU : e₀ ⊆ C.U := fun x hx => (he₀C.2.1 hx).1
  have he₀_dis_bdD : Disjoint e₀ (subBd D_big) := by
    rw [hD_subBd]
    refine disjoint_union_right.mpr ⟨?_, ?_⟩
    · refine disjoint_left.mpr fun x hxe₀ hxF₂ => ?_
      by_cases hx12 : x ∈ ({v₁, v₂} : Set S)
      · rcases hx12 with rfl | rfl
        · exact (he₀H.2.1 hxe₀).2 (hCs.1 hv₁C)
        · exact (he₀H.2.1 hxe₀).2 (hCs.1 hv₂C)
      · exact region_subset hr (hF₂_r ⟨hxF₂, hx12⟩) (he₀H.2.1 hxe₀).1
    · refine disjoint_left.mpr fun x hxe₀ hxP' => ?_
      have hxV : x ∉ P'.V := fun hxV => (he₀H.2.1 hxe₀).2 (hP'H.1 hxV)
      obtain ⟨f, hfP', hxf⟩ := P'.exists_edge_of_mem hxP' hxV
      have heq : e₀ = f := H.edge_eq_of_mem he₀H (hP'H.2 hfP') hxe₀ hxf
      exact disjoint_left.mp hPE_dis he₀P (heq ▸ hfP')
  have hΛ_dis_bdD : Disjoint Λ (subBd D_big) := by
    rw [hD_subBd]
    refine disjoint_union_right.mpr ⟨?_, ?_⟩
    · refine disjoint_left.mpr fun x hxΛ hxF₂ => ?_
      have hx_not_CU : x ∉ C.U := fun hxC => (hdiff ▸ hxΛ).2 hxC
      have hx12 : x ∉ ({v₁, v₂} : Set S) := by
        rintro (rfl | rfl)
        · exact hx_not_CU (C.V_subset_U hv₁C)
        · exact hx_not_CU (C.V_subset_U hv₂C)
      exact disjoint_left.mp hdis_rΛ (hF₂_r ⟨hxF₂, hx12⟩) hxΛ
    · refine disjoint_left.mpr fun x hxΛ hxP' => ?_
      exact (hdiff ▸ hxΛ).2 (hP'C.U_subset hxP')
  -- Define `Z = Λ ∪ e₀`.
  set Z := Λ ∪ e₀
  have hΛ_sub_D_int : Λ ⊆ D_big \ subBd D_big :=
    fun x hx => ⟨hclΛ_in_D (subset_closure hx), disjoint_left.mp hΛ_dis_bdD hx⟩
  have he₀_sub_D_int : e₀ ⊆ D_big \ subBd D_big :=
    fun x hx => ⟨hCU_in_D (he₀_sub_CU hx), disjoint_left.mp he₀_dis_bdD hx⟩
  have hZ_sub_D_int : Z ⊆ D_big \ subBd D_big := union_subset hΛ_sub_D_int he₀_sub_D_int
  obtain ⟨q₀, hq₀⟩ := he₀H.1
  have hZne : Z.Nonempty := ⟨q₀, Or.inr hq₀⟩
  have hZconn : IsPreconnected Z :=
    hΛ_open.isPathConnected.isConnected.isPreconnected.subset_closure
      subset_union_left (union_subset subset_closure (he₀_sub_CU.trans hCU_sub_cl))
  have hdis_cl_r_Z : Disjoint (closure r) Z :=
    disjoint_union_right.mpr ⟨hdis_cl_r_Λ, hdis_cl_r_e₀⟩
  have hint_D_eq : D_big \ subBd D_big = interior D_big := by
    rw [subBd_eq_frontier]
    ext x
    exact ⟨fun ⟨hx, hnf⟩ => by_contra fun hni => hnf ⟨subset_closure hx, hni⟩,
      fun hx => ⟨interior_subset hx, fun hf => hf.2 hx⟩⟩
  have hreg_sub : ∀ s ∈ H.R, (closure s ∩ Z).Nonempty → s ⊆ D_big \ subBd D_big := by
    rintro s hs ⟨p, hps, hpZ⟩
    have hsr : s ≠ r := fun heq => disjoint_left.mp hdis_cl_r_Z (heq ▸ hps) hpZ
    have hdis_sr : Disjoint s r :=
      disjoint_left.mpr fun x hxs hxr => hsr (region_eq_of_mem hs hr hxs hxr)
    have hdis_s_fr : Disjoint s (frontier D_big) := by
      rw [hD_fr]
      refine disjoint_union_right.mpr ⟨?_, ?_⟩
      · refine disjoint_left.mpr fun x hxs hxF₂ => ?_
        by_cases hx12 : x ∈ ({v₁, v₂} : Set S)
        · rcases hx12 with rfl | rfl
          · exact region_subset hs hxs (H.V_subset_U (hCs.1 hv₁C))
          · exact region_subset hs hxs (H.V_subset_U (hCs.1 hv₂C))
        · exact disjoint_left.mp hdis_sr hxs (hF₂_r ⟨hxF₂, hx12⟩)
      · exact disjoint_left.mpr fun x hxs hxP' =>
          region_subset hs hxs (hP'H.U_subset hxP')
    have hp_int : p ∈ interior D_big := hint_D_eq ▸ hZ_sub_D_int hpZ
    obtain ⟨y, hy_int, hys⟩ := mem_closure_iff.mp hps (interior D_big) isOpen_interior hp_int
    have hs_D : s ⊆ D_big :=
      subset_of_disjoint_frontier (region_isPreconnected hs) hD_cl hdis_s_fr hys
        (interior_subset hy_int)
    exact fun x hxs => ⟨hs_D hxs, disjoint_left.mp (subBd_eq_frontier D_big ▸ hdis_s_fr) hxs⟩
  obtain ⟨C', Λ', hC'H, hC', hC'U_D, hOpenΛ', hclΛ'_D, hclΛ'_disc, hbdΛ', hbd_clΛ',
    hdiffΛ', hZΛ', -⟩ :=
    theorem_5_2_full hS H hD_disc hZne hZconn hreg_sub
  have hΛ_sub_Λ' : Λ ⊆ Λ' := subset_union_left.trans hZΛ'
  have he₀_sub_Λ' : e₀ ⊆ Λ' := subset_union_right.trans hZΛ'
  have hcl_sub_cl' : closure Λ ⊆ closure Λ' := closure_mono hΛ_sub_Λ'
  have hC'U_int : C'.U ⊆ Δ_out \ subBd Δ_out := hC'U_D.trans hD_sub_int
  have hclΛ'_int : closure Λ' ⊆ Δ_out \ subBd Δ_out := hclΛ'_D.trans hD_sub_int
  have he₀_not_Λ : ¬ e₀ ⊆ Λ := by
    intro hsub
    exact (hdiff ▸ hsub hq₀).2 (he₀_sub_CU hq₀)
  have hlt_ncard : {e ∈ H.E | e ⊆ Λ}.ncard < {e ∈ H.E | e ⊆ Λ'}.ncard := by
    refine Set.ncard_lt_ncard ⟨fun e he => ⟨he.1, he.2.trans hΛ_sub_Λ'⟩, ?_⟩
      (H.finite_edges.subset fun _ h => h.1)
    intro hsub
    exact he₀_not_Λ (hsub ⟨he₀H, he₀_sub_Λ'⟩).2
  exact ⟨C', Λ', hC'H, hC', hC'U_int, hOpenΛ', hclΛ'_int, hclΛ'_disc, hbdΛ', hbd_clΛ',
    hdiffΛ', hΛ_sub_Λ', hcl_sub_cl', hlt_ncard⟩

/-- If `C` is a circuit of a rigid drawing `H` bounding an open disc `Λ` with
`closure Λ ⊆ Δ_out \ subBd Δ_out` in a closed disc `Δ_out` (`subBd Δ_out ⊆ H.U`), and
`clearedSubdrawing H Λ` is not rigid, then there is a circuit `C'` of `H` bounding an open disc
`Λ'` with `closure Λ' ⊆ Δ_out \ subBd Δ_out`, `Λ ⊆ Λ'`, `closure Λ ⊆ closure Λ'`, and strictly
more edges of `H` included in `Λ'`. -/
theorem enlarge_disc_past_disconnected_region [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {H C : Drawing S} {Δ_out Λ : Set S}
    (hRig : IsRigid H) (hΔ_out : IsClosedDisc Δ_out) (hbd_out_U : subBd Δ_out ⊆ H.U)
    (hC : C.IsCircuit) (hCs : C.IsSubdrawing H)
    (hΛ_open : IsOpenDisc Λ) (hΛ_cl : IsClosedDisc (closure Λ))
    (hbd : subBd Λ = C.U) (hbd_cl : subBd (closure Λ) = C.U) (hdiff : closure Λ \ C.U = Λ)
    (hcl_sub : closure Λ ⊆ Δ_out \ subBd Δ_out)
    (hnot_rig : ¬ IsRigid (clearedSubdrawing H Λ)) :
    ∃ (C' : Drawing S) (Λ' : Set S),
      C'.IsSubdrawing H ∧ C'.IsCircuit ∧ C'.U ⊆ Δ_out \ subBd Δ_out ∧
      IsOpenDisc Λ' ∧ closure Λ' ⊆ Δ_out \ subBd Δ_out ∧ IsClosedDisc (closure Λ') ∧
      subBd Λ' = C'.U ∧ subBd (closure Λ') = C'.U ∧ closure Λ' \ C'.U = Λ' ∧
      Λ ⊆ Λ' ∧ closure Λ ⊆ closure Λ' ∧
      {e ∈ H.E | e ⊆ Λ}.ncard < {e ∈ H.E | e ⊆ Λ'}.ncard := by
  have : CompactSpace S := hS.1
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hex : ∃ (r : Set S) (v₁ v₂ : S) (F₂ : Set S) (P₁ P₂ : Drawing S),
      r ∈ H.R ∧ Disjoint r Λ ∧ v₁ ≠ v₂ ∧ v₁ ∈ C.V ∧ v₂ ∈ C.V ∧
      IsLineWithEnds F₂ v₁ v₂ ∧ F₂ \ {v₁, v₂} ⊆ r ∧
      P₁.IsPathBetween v₁ v₂ ∧ P₂.IsPathBetween v₁ v₂ ∧
      P₁.IsSubdrawing C ∧ P₂.IsSubdrawing C ∧
      P₁.V ∩ P₂.V = {v₁, v₂} ∧ Disjoint P₁.E P₂.E ∧ C.sup P₁ P₂ = C ∧
      ¬ (P₁.U ⊆ closure r ∨ P₂.U ⊆ closure r) := by
    by_contra hno
    push Not at hno
    exact hnot_rig (isRigid_clearedSubdrawing_of_arc_subset hS hRig hΛ_open hΛ_cl hC hCs hbd hno)
  obtain ⟨r, v₁, v₂, F₂, P₁, P₂, hr, hdis_rΛ, hv12, hv₁C, hv₂C, hF₂_line, hF₂_r,
    hP₁, hP₂, hP₁C, hP₂C, hV12, hE12, hsup12, hnot_or⟩ := hex
  rw [not_or] at hnot_or
  obtain ⟨hnot_P₁_r, hnot_P₂_r⟩ := hnot_or
  have hP₁H : P₁.IsSubdrawing H := hP₁C.trans hCs
  have hP₂H : P₂.IsSubdrawing H := hP₂C.trans hCs
  have hCU_eq : C.U = P₁.U ∪ P₂.U := by
    have := congrArg Drawing.U hsup12.symm
    rwa [PlanarNests.Drawing.sup_U hP₁C hP₂C] at this
  have hCU_sub_cl : C.U ⊆ closure Λ := by
    rw [← hbd_cl, subBd_eq_frontier]
    exact isClosed_closure.frontier_subset
  have hCU_sub_int : C.U ⊆ Δ_out \ subBd Δ_out := hCU_sub_cl.trans hcl_sub
  -- Show `r ⊆ Δ_out \ subBd Δ_out` and `F₂ ⊆ Δ_out \ subBd Δ_out`.
  have hΔ_cl : IsClosed Δ_out := hΔ_out.isCompact.isClosed
  have hfr_out : frontier Δ_out = subBd Δ_out := (subBd_eq_frontier Δ_out).symm
  have hint_out_eq : Δ_out \ subBd Δ_out = interior Δ_out := by
    rw [← hfr_out]
    ext x
    exact ⟨fun ⟨hx, hnf⟩ => by_contra fun hni => hnf ⟨subset_closure hx, hni⟩,
      fun hx => ⟨interior_subset hx, fun hf => hf.2 hx⟩⟩
  obtain ⟨hv₁F₂, hv₂F₂⟩ := IsLineWithEnds.ends_mem hF₂_line
  have hv₁_cl_r : v₁ ∈ closure r :=
    closure_mono hF₂_r (IsLineWithEnds.subset_closure_sdiff_pair hF₂_line hv₁F₂)
  have hv₁_int : v₁ ∈ interior Δ_out :=
    hint_out_eq ▸ hCU_sub_int (C.V_subset_U hv₁C)
  obtain ⟨q_r, hq_int, hq_r⟩ := mem_closure_iff.mp hv₁_cl_r (interior Δ_out) isOpen_interior hv₁_int
  have hdis_r_fr_out : Disjoint r (frontier Δ_out) := by
    rw [hfr_out]
    exact disjoint_left.mpr fun x hxr hxbd => region_subset hr hxr (hbd_out_U hxbd)
  have hr_sub_Δ : r ⊆ Δ_out :=
    subset_of_disjoint_frontier (region_isPreconnected hr) hΔ_cl hdis_r_fr_out hq_r
      (interior_subset hq_int)
  have hr_sub_int : r ⊆ Δ_out \ subBd Δ_out :=
    fun x hxr => ⟨hr_sub_Δ hxr, disjoint_left.mp (hfr_out ▸ hdis_r_fr_out) hxr⟩
  have hF₂_sub_int : F₂ ⊆ Δ_out \ subBd Δ_out := by
    intro x hx
    by_cases hx12 : x ∈ ({v₁, v₂} : Set S)
    · rcases hx12 with rfl | rfl
      · exact hCU_sub_int (C.V_subset_U hv₁C)
      · exact hCU_sub_int (C.V_subset_U hv₂C)
    · exact hr_sub_int (hF₂_r ⟨hx, hx12⟩)
  -- The three lines `F₂`, `P₁.U`, `P₂.U` between `v₁` and `v₂`.
  have hL₁ : IsLineWithEnds P₁.U v₁ v₂ := isLine_of_isPathBetween hP₁ hv12
  have hL₂ : IsLineWithEnds P₂.U v₁ v₂ := isLine_of_isPathBetween hP₂ hv12
  have hI_12 : P₁.U ∩ P₂.U = {v₁, v₂} := by
    rw [U_inter_of_disjoint hP₁H hP₂H hE12, hV12]
  have hI_F1 : F₂ ∩ P₁.U = {v₁, v₂} := by
    apply subset_antisymm
    · rintro x ⟨hxF, hxP⟩
      by_contra hx12
      exact region_subset hr (hF₂_r ⟨hxF, hx12⟩) (hP₁H.U_subset hxP)
    · rintro x (rfl | rfl)
      · exact ⟨hv₁F₂, (IsLineWithEnds.ends_mem hL₁).1⟩
      · exact ⟨hv₂F₂, (IsLineWithEnds.ends_mem hL₁).2⟩
  have hI_2F : P₂.U ∩ F₂ = {v₁, v₂} := by
    apply subset_antisymm
    · rintro x ⟨hxP, hxF⟩
      by_contra hx12
      exact region_subset hr (hF₂_r ⟨hxF, hx12⟩) (hP₂H.U_subset hxP)
    · rintro x (rfl | rfl)
      · exact ⟨(IsLineWithEnds.ends_mem hL₂).1, hv₁F₂⟩
      · exact ⟨(IsLineWithEnds.ends_mem hL₂).2, hv₂F₂⟩
  have hO_c₂ : IsOArc (F₂ ∪ P₂.U) :=
    isOArc_union hF₂_line hL₂ (by rw [Set.inter_comm, hI_2F])
  have hO_c₁ : IsOArc (F₂ ∪ P₁.U) :=
    isOArc_union hF₂_line hL₁ hI_F1.subset
  have hU_c₂_out : F₂ ∪ P₂.U ⊆ Δ_out :=
    union_subset (hF₂_sub_int.trans sdiff_subset)
      ((hP₂C.U_subset.trans hCU_sub_int).trans sdiff_subset)
  have hU_c₁_out : F₂ ∪ P₁.U ⊆ Δ_out :=
    union_subset (hF₂_sub_int.trans sdiff_subset)
      ((hP₁C.U_subset.trans hCU_sub_int).trans sdiff_subset)
  obtain ⟨D_c₂, ⟨sub_c₂, d_c₂, b_c₂, -⟩, _⟩ := disc_oArc Δ_out (F₂ ∪ P₂.U) hΔ_out hU_c₂_out hO_c₂
  obtain ⟨D_c₁, ⟨sub_c₁, d_c₁, b_c₁, -⟩, uniq_c₁⟩ :=
    disc_oArc Δ_out (F₂ ∪ P₁.U) hΔ_out hU_c₁_out hO_c₁
  have f_c₂ : frontier D_c₂ = P₂.U ∪ F₂ := by
    rw [IsClosedDisc.frontier_eq_discBd hS d_c₂, b_c₂, Set.union_comm]
  have f_c₁ : frontier D_c₁ = F₂ ∪ P₁.U := by
    rw [IsClosedDisc.frontier_eq_discBd hS d_c₁, b_c₁]
  have f_Λ : frontier (closure Λ) = P₁.U ∪ P₂.U := by
    rw [← subBd_eq_frontier, hbd_cl, hCU_eq]
  have hnot_F₂_in : ¬ F₂ ⊆ closure Λ := by
    intro hsub
    obtain ⟨p, hp⟩ := IsLineWithEnds.nonempty_sdiff_pair hF₂_line
    have hpr : p ∈ r := hF₂_r hp
    have hp_cl : p ∈ closure Λ := hsub hp.1
    rw [← hdiff] at hdis_rΛ
    by_cases hpC : p ∈ C.U
    · exact region_subset hr hpr (hCs.U_subset hpC)
    · exact disjoint_left.mp hdis_rΛ hpr ⟨hp_cl, hpC⟩
  -- Symmetric helper once we know `P.U ⊆ D_big` for `(P, P', D_big) ∈ {(P₁, P₂, D_c₂), (P₂, P₁,
  -- D_c₁)}`.
  have henlarge : ∀ (P P' : Drawing S) (D_big : Set S),
      P.IsSubdrawing C → P'.IsSubdrawing C →
      P.IsPathBetween v₁ v₂ → Disjoint P.E P'.E →
      C.U = P.U ∪ P'.U → ¬ P.U ⊆ closure r →
      D_big ⊆ Δ_out → IsClosedDisc D_big → discBd D_big = F₂ ∪ P'.U →
      P.U ⊆ D_big →
      ∃ (C' : Drawing S) (Λ' : Set S),
        C'.IsSubdrawing H ∧ C'.IsCircuit ∧ C'.U ⊆ Δ_out \ subBd Δ_out ∧
        IsOpenDisc Λ' ∧ closure Λ' ⊆ Δ_out \ subBd Δ_out ∧ IsClosedDisc (closure Λ') ∧
        subBd Λ' = C'.U ∧ subBd (closure Λ') = C'.U ∧ closure Λ' \ C'.U = Λ' ∧
        Λ ⊆ Λ' ∧ closure Λ ⊆ closure Λ' ∧
        {e ∈ H.E | e ⊆ Λ}.ncard < {e ∈ H.E | e ⊆ Λ'}.ncard := by
    exact disc_on_other_side_gives_larger_zone (S := S) hS (H := H) (C := C) (Δ_out := Δ_out) (Λ
      := Λ) hΔ_out hC hCs hΛ_open hΛ_cl hbd_cl hdiff hcl_sub r v₁ v₂ F₂ P₂ hr hdis_rΛ hv12 hv₁C
      hv₂C hF₂_r hCU_sub_cl hCU_sub_int hfr_out hF₂_sub_int hI_2F
  by_cases h₁ : P₁.U ⊆ D_c₂
  · exact henlarge P₁ P₂ D_c₂ hP₁C hP₂C hP₁ hE12 hCU_eq hnot_P₁_r sub_c₂ d_c₂ b_c₂ h₁
  by_cases h₂ : P₂.U ⊆ D_c₁
  · exact henlarge P₂ P₁ D_c₁ hP₂C hP₁C hP₂ hE12.symm (by rw [hCU_eq, Set.union_comm])
      hnot_P₂_r sub_c₁ d_c₁ b_c₁ h₂
  exfalso
  obtain ⟨dU, hbdU, hneU⟩ :=
    theta_disc_union hS hF₂_line hL₁ hL₂ hI_F1 hI_12 hI_2F
      hΛ_cl d_c₂ d_c₁ f_Λ f_c₂ f_c₁ hnot_F₂_in h₁ h₂
  have heq := uniq_c₁ _ (union_subset (hcl_sub.trans sdiff_subset) sub_c₂) dU (hbdU.trans b_c₁)
  exact hneU heq

/-! ## 2. Proof of (9.3) (pages 44–45) -/

/-- Graph Minors XIV, (9.3) (page 44), proving `GM16.GM14Theorem93Statement`:
"Let $H$ be a 2-cell rigid drawing in $\Sigma$, and let $\mathscr{T}$ be a respectful tangle
in $H$ of order $\theta$, with metric $d$. Let $z \in A(H)$, and let $\kappa$ be an integer
with $2 \le \kappa \le \theta - 6$. Then there is a $(\kappa + 5)$-zone $\Lambda$ around $z$
such that $H \cap (\Sigma - \Lambda)$ is rigid and $x \subseteq \Lambda$ for every $x \in
A(H)$ with $d(z, x) < \kappa$." -/
theorem theorem_9_3_proof : GM16.GM14Theorem93Statement.{w} := by
  intro S _ _ H θ κ T d z hS hConn hRig hMetric hz hκ2 hκθ
  have : ConnectedSpace S := hConn
  obtain ⟨C₁, Λ₁, hC₁H, hC₁, hbd₁, hbd_cl₁, hdiff₁, hZone₁, hsub₁⟩ :=
    full_of_9_2 hS hConn H θ κ T d z hMetric hz hκ2 (by omega)
  obtain ⟨C₂, Λ₂, hC₂H, hC₂, hbd₂, hbd_cl₂, hdiff₂, hZone₂, hsub₂⟩ :=
    full_of_9_2 hS hConn H θ (κ + 3) T d z hMetric hz (by omega) (by omega)
  have hcl₁_sub_Λ₂ : closure Λ₁ ⊆ Λ₂ :=
    closure_zone_subset hS hZone₁ fun x hx hle => hsub₂ x hx (by omega)
  have hcl₁_sub_int₂ : closure Λ₁ ⊆ closure Λ₂ \ subBd (closure Λ₂) := by
    rw [hbd_cl₂, hdiff₂]
    exact hcl₁_sub_Λ₂
  let Valid : Drawing S → Set S → Prop := fun C Λ =>
    C.IsSubdrawing H ∧ C.IsCircuit ∧
    IsOpenDisc Λ ∧ IsClosedDisc (closure Λ) ∧
    subBd Λ = C.U ∧ subBd (closure Λ) = C.U ∧ closure Λ \ C.U = Λ ∧
    closure Λ ⊆ closure Λ₂ \ subBd (closure Λ₂) ∧ Λ₁ ⊆ Λ
  have hValid₁ : Valid C₁ Λ₁ :=
    ⟨hC₁H, hC₁, hZone₁.isOpenDisc, hZone₁.isClosedDisc_closure,
      hbd₁, hbd_cl₁, hdiff₁, hcl₁_sub_int₂, Subset.rfl⟩
  let S_k : Set ℕ := {k | ∃ C Λ, Valid C Λ ∧ H.E.ncard - {e ∈ H.E | e ⊆ Λ}.ncard = k}
  have hS_ne : S_k.Nonempty := ⟨_, C₁, Λ₁, hValid₁, rfl⟩
  obtain ⟨C, Λ, hV, hk_eq⟩ := Nat.sInf_mem hS_ne
  obtain ⟨hCH, hC, hΛ_open, hΛ_cl, hbd, hbd_cl, hdiff, hcl_sub, hΛ₁_sub⟩ := hV
  have hZone₂_eq : closure Λ₂ \ subBd (closure Λ₂) = Λ₂ := by rw [hbd_cl₂, hdiff₂]
  have hZone : IsLambdaZoneAround H d (κ + 5) z Λ := by
    have h := zone_of_closedDisc_subset hS (hZone₂_eq.symm ▸ hZone₂)
      hZone₂.isClosedDisc_closure hΛ_cl (hcl_sub.trans sdiff_subset) hC hCH hbd_cl
      (by rw [hbd_cl, hdiff]; exact hZone₁.z_subset.trans hΛ₁_sub)
    rwa [hbd_cl, hdiff] at h
  refine ⟨Λ, hZone, ?_, fun x hx hlt => (hsub₁ x hx hlt).trans hΛ₁_sub⟩
  by_contra hnot_rig
  obtain ⟨C', Λ', hC'H, hC', _, hOpenΛ', hclΛ'_sub, hclΛ'_disc, hbdΛ', hbd_clΛ',
    hdiffΛ', hΛ_sub_Λ', _, hlt_ncard⟩ :=
    enlarge_disc_past_disconnected_region hS hRig hZone₂.isClosedDisc_closure
      (hbd_cl₂ ▸ hC₂H.U_subset) hC hCH hΛ_open hΛ_cl hbd hbd_cl hdiff hcl_sub hnot_rig
  have hV' : Valid C' Λ' :=
    ⟨hC'H, hC', hOpenΛ', hclΛ'_disc, hbdΛ', hbd_clΛ', hdiffΛ', hclΛ'_sub,
      hΛ₁_sub.trans hΛ_sub_Λ'⟩
  have hle_H : {e ∈ H.E | e ⊆ Λ'}.ncard ≤ H.E.ncard :=
    Set.ncard_le_ncard (fun _ h => h.1) H.finite_edges
  have hmin : sInf S_k ≤ H.E.ncard - {e ∈ H.E | e ⊆ Λ'}.ncard :=
    Nat.sInf_le ⟨C', Λ', hV', rfl⟩
  omega

/-! ## 3. Regional Distance along a Nest and Claim (1) of (9.5) -/

/-- If `D ⊆ S` is closed, `frontier D ⊆ H.U`, `X ⊆ D \ frontier D` is nonempty, `Y` is nonempty,
and `Disjoint (D \ frontier D) Y`, then `regionalDistance H D Y + 1 ≤ regionalDistance H X Y`. -/
private theorem regionalDistance_add_one_le [ConnectedSpace S] (hS : IsClosedSurface S)
    {H : Drawing S} {X D Y : Set S}
    (hD : IsClosed D) (hfr : frontier D ⊆ H.U)
    (hX : X ⊆ D \ frontier D) (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (hdis : Disjoint (D \ frontier D) Y) :
    regionalDistance H D Y + 1 ≤ regionalDistance H X Y := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hspec := regionalDistance_spec hS H hXne hYne
  generalize hk : regionalDistance H X Y = k at hspec ⊢
  obtain ⟨v_seq, r_seq, hv0, hvlast, hsteps⟩ := hspec
  rcases k with _ | m
  · exfalso
    have h0 : Fin.last 0 = (0 : Fin 1) := rfl
    rw [h0] at hvlast
    exact disjoint_left.mp hdis (hX hv0) hvlast
  · have hint_eq : D \ frontier D = interior D := by
      ext x
      exact ⟨fun ⟨hx, hnf⟩ => by_contra fun hni => hnf ⟨subset_closure hx, hni⟩,
        fun hx => ⟨interior_subset hx, fun hf => hf.2 hx⟩⟩
    have hv0_int : v_seq 0 ∈ interior D := hint_eq ▸ hX hv0
    have hr0_R : r_seq 0 ∈ H.R := (hsteps 0).1
    have hv0_r0 : v_seq 0 ∈ closure (r_seq 0) := (hsteps 0).2.1
    have hv1_r0 : v_seq 1 ∈ closure (r_seq 0) := (hsteps 0).2.2
    obtain ⟨q, hq_int, hq_r0⟩ := mem_closure_iff.mp hv0_r0 (interior D) isOpen_interior hv0_int
    have hdis_r0_fr : Disjoint (r_seq 0) (frontier D) :=
      disjoint_left.mpr fun x hxr hxfr => region_subset hr0_R hxr (hfr hxfr)
    have hr0_D : r_seq 0 ⊆ D :=
      subset_of_disjoint_frontier (region_isPreconnected hr0_R) hD hdis_r0_fr hq_r0
        (interior_subset hq_int)
    have hv1_D : v_seq 1 ∈ D := hD.closure_subset_iff.mpr hr0_D hv1_r0
    have hchain' : IsRegionChain H D Y (fun i : Fin (m + 1) => v_seq i.succ)
        (fun i : Fin m => r_seq i.succ) := by
      refine ⟨hv1_D, ?_, fun i => hsteps i.succ⟩
      simpa [Fin.last] using hvlast
    have hle := regionalDistance_le hchain'
    omega

/-- In a disc nest `C : Fin s → Drawing S` (`0 < s`), for every `h : Fin s`, the regional distance
between `(C 0).U` and `(C h).U` is at least `h.1`. -/
private theorem nest_regionalDistance_ge [T2Space S] [ConnectedSpace S] (hS : IsClosedSurface S)
    {s : ℕ} {H C_in C_out : Drawing S} {Δ_out : Set S} {C : Fin s → Drawing S}
    (hs : 0 < s) (hΔ_out : IsClosedDisc Δ_out) (hC : IsDiscNest H Δ_out C_in C_out C)
    (h : Fin s) :
    h.1 ≤ regionalDistance H (C ⟨0, hs⟩).U (C h).U := by
  have hYne : (C h).U.Nonempty := IsOArc.nonempty (isOArc_of_isCircuit (hC.1 h).2.1)
  have hstep : ∀ k : ℕ, (hk : k ≤ h.1) →
      k ≤ regionalDistance H (discIns Δ_out (C ⟨h.1 - k, by omega⟩)) (C h).U := by
    intro k
    induction k with
    | zero => intro _; exact Nat.zero_le _
    | succ k ih =>
      intro hk
      let j₀ : Fin s := ⟨h.1 - (k + 1), by omega⟩
      let j₁ : Fin s := ⟨h.1 - k, by omega⟩
      have hj₀₁ : j₀ < j₁ := by change h.1 - (k + 1) < h.1 - k; omega
      have hp₀ := hC.disc_props hS hΔ_out j₀
      have hp₁ := hC.disc_props hS hΔ_out j₁
      have hsub_diff : discIns Δ_out (C j₀) ⊆ discIns Δ_out (C j₁) \ frontier (discIns Δ_out
        (C j₁)) := by
        rw [hp₁.2.2.2.1]
        exact (hC.discIns_subset_diff hS hΔ_out hj₀₁).2
      have hdis_Y : Disjoint (discIns Δ_out (C j₁) \ frontier (discIns Δ_out (C j₁))) (C h).U := by
        rw [hp₁.2.2.2.1]
        by_cases hj₁h : j₁ = h
        · rw [hj₁h]
          exact disjoint_sdiff_left
        · have hj₁_ne : h.1 - k ≠ h.1 := fun heq => hj₁h (Fin.ext heq)
          have hj₁_lt_h : j₁ < h := by change h.1 - k < h.1; omega
          exact disjoint_of_subset_left sdiff_subset (hC.discIns_subset_diff hS hΔ_out hj₁_lt_h).1
      have hXne : (discIns Δ_out (C j₀)).Nonempty := IsClosedDisc.nonempty hp₀.2.1
      have hfr_U : frontier (discIns Δ_out (C j₁)) ⊆ H.U :=
        hp₁.2.2.2.1 ▸ (hC.1 j₁).1.U_subset
      have hadd : regionalDistance H (discIns Δ_out (C j₁)) (C h).U + 1 ≤
          regionalDistance H (discIns Δ_out (C j₀)) (C h).U :=
        regionalDistance_add_one_le hS hp₁.2.2.2.2.1 hfr_U hsub_diff hXne hYne hdis_Y
      have hih : k ≤ regionalDistance H (discIns Δ_out (C j₁)) (C h).U := ih (by omega)
      change k + 1 ≤ regionalDistance H (discIns Δ_out (C j₀)) (C h).U
      omega
  have h0_eq : (⟨h.1 - h.1, by omega⟩ : Fin s) = ⟨0, hs⟩ := by ext; simp
  have hle_D0 : h.1 ≤ regionalDistance H (discIns Δ_out (C ⟨0, hs⟩)) (C h).U := by
    have := hstep h.1 le_rfl
    rwa [h0_eq] at this
  have hp0 := hC.disc_props hS hΔ_out ⟨0, hs⟩
  have hC0ne : (C ⟨0, hs⟩).U.Nonempty := IsOArc.nonempty (isOArc_of_isCircuit (hC.1 ⟨0, hs⟩).2.1)
  obtain ⟨v_seq, r_seq, hc⟩ := regionalDistance_spec hS H hC0ne hYne
  have hc' : IsRegionChain H (discIns Δ_out (C ⟨0, hs⟩)) (C h).U v_seq r_seq :=
    ⟨hp0.2.2.2.2.2 hc.1, hc.2.1, hc.2.2⟩
  exact hle_D0.trans (regionalDistance_le hc')

/-- For any point `p ∈ x ∩ closure r` where `x ∈ A(H)` and `r ∈ R(H)`, either `x = r` or there is a
vertex `v ∈ V(H)` with `v ∈ closure x` and `v ∈ closure r` (and if `r₁, r₂ ∈ R(H)` both contain `p`
in their closures, the same `v` belongs to `closure r₁ ∩ closure r₂`). -/
private theorem eq_or_exists_vertex_of_mem_closure_region
    (hS : IsClosedSurface S) {H : Drawing S} {r x : Set S} {p : S}
    (hr : r ∈ H.R) (hx : x ∈ H.A) (hpx : p ∈ x) (hpr : p ∈ closure r) :
    x = r ∨ (x ⊆ closure r ∧ ∃ v ∈ H.V, v ∈ closure x ∧ v ∈ closure r) := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  rcases hx with (⟨v, hv, rfl⟩ | he) | hs
  · have hvp : p = v := mem_singleton_iff.mp hpx
    subst hvp
    exact Or.inr ⟨singleton_subset_iff.mpr hpr, p, hv, subset_closure (mem_singleton p), hpr⟩
  · have her : x ⊆ closure r := edge_subset_closure_of_incident hS he hr ⟨p, hpx, hpr⟩
    have hcl_er : closure x ⊆ closure r := isClosed_closure.closure_subset_iff.mpr her
    have hex_v : ∃ v ∈ H.V, v ∈ closure x := by
      rcases H.edge_cond x he with ⟨u, v, _, hcap, _⟩ | ⟨u, hcap, _⟩
      · have hu : u ∈ closure x ∩ H.V := by rw [hcap]; exact Or.inl rfl
        exact ⟨u, hu.2, hu.1⟩
      · have hu : u ∈ closure x ∩ H.V := by rw [hcap]; exact rfl
        exact ⟨u, hu.2, hu.1⟩
    obtain ⟨v, hvH, hve⟩ := hex_v
    exact Or.inr ⟨her, v, hvH, hve, hcl_er hve⟩
  · obtain ⟨q, hqs, hqr⟩ := mem_closure_iff.mp hpr x (region_isOpen hs) hpx
    exact Or.inl (region_eq_of_mem hs hr hqs hqr)

/-- Two regions `r₁, r₂ ∈ R(H)` whose closures share a point `p` have tangle distance `≤ 2`. -/
private theorem tangleMetric_regions_le_two_of_inter_closures [T2Space S]
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {H : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    (hMetric : HasTangleMetric H θ T d) (hE : H.E.Nonempty)
    {r₁ r₂ : Set S} (hr₁ : r₁ ∈ H.R) (hr₂ : r₂ ∈ H.R)
    {p : S} (hp₁ : p ∈ closure r₁) (hp₂ : p ∈ closure r₂) :
    d r₁ r₂ ≤ 2 := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have h91 := GM11.gm15_theorem_9_1 H θ T d hS hConn hMetric
  have hrefl := h91.2.1
  have hsymm := h91.2.2.2.1
  have htri := h91.2.2.2.2.1
  have hv_reg := h91.2.2.2.2.2.1
  obtain ⟨x, hxA, hpx⟩ := exists_atom_mem_of_point H p
  rcases eq_or_exists_vertex_of_mem_closure_region hS hr₁ hxA hpx hp₁ with rfl | ⟨_, v, hvH, hvx,
    hvr₁⟩
  · obtain ⟨q, hqx, hqr₂⟩ := mem_closure_iff.mp hp₂ x (region_isOpen hr₁) hpx
    have heq : r₂ = x := region_eq_of_mem hr₂ hr₁ hqr₂ hqx
    subst heq
    rw [hrefl r₂ (Or.inr hr₁)]
    exact Nat.zero_le 2
  · rcases eq_or_exists_vertex_of_mem_closure_region hS hr₂ hxA hpx hp₂ with rfl | ⟨hsub₂, _⟩
    · obtain ⟨q, hqx, hqr₁⟩ := mem_closure_iff.mp hp₁ x (region_isOpen hr₂) hpx
      have heq : r₁ = x := region_eq_of_mem hr₁ hr₂ hqr₁ hqx
      subst heq
      rw [hrefl r₁ (Or.inr hr₂)]
      exact Nat.zero_le 2
    · have hvr₂ : v ∈ closure r₂ := isClosed_closure.closure_subset_iff.mpr hsub₂ hvx
      have hvA : ({v} : Set S) ∈ H.A := Or.inl (Or.inl ⟨v, hvH, rfl⟩)
      have h1 : d r₁ {v} ≤ 1 := by
        rw [hsymm r₁ (Or.inr hr₁) {v} hvA]
        exact hv_reg hE v hvH r₁ hr₁ hvr₁
      have h2 : d {v} r₂ ≤ 1 := hv_reg hE v hvH r₂ hr₂ hvr₂
      have h3 := htri r₁ (Or.inr hr₁) {v} hvA r₂ (Or.inr hr₂)
      omega

/-- Claim (1) in the proof of Graph Minors XIV, (9.5) (pages 45–46):
"There are $\beta + 1$ mutually disjoint circuits $C_1, \dots, C_{\beta + 1}$ of $H \cap
\bar{\Lambda}_1$, bounding closed discs $\Delta_1, \dots, \Delta_{\beta + 1} \subseteq
\bar{\Lambda}_1$, respectively, such that $\bar{\Lambda}_2 \subseteq \Delta_1 \subseteq
\Delta_2 \subseteq \dots \subseteq \Delta_{\beta + 1} \subseteq \bar{\Lambda}_1$." -/
private theorem lemma_9_5_claim_1 [T2Space S]
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {H : Drawing S} {θ beta : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {z : Set S}
    (hMetric : HasTangleMetric H θ T d) (hz : z ∈ H.A)
    (hbeta : 4 ≤ beta) (hθ : 16 * beta + 17 ≤ θ) :
    ∃ (C_in C_out : Drawing S) (Λ₁ Λ₂ : Set S) (C₀ : Fin (beta + 1) → Drawing S),
      C_in.IsSubdrawing H ∧ C_in.IsCircuit ∧
      subBd Λ₂ = C_in.U ∧ subBd (closure Λ₂) = C_in.U ∧ closure Λ₂ \ C_in.U = Λ₂ ∧
      IsLambdaZoneAround H d (beta + 2) z Λ₂ ∧
      (∀ x ∈ H.A, d z x < beta → x ⊆ Λ₂) ∧
      C_out.IsSubdrawing H ∧ C_out.IsCircuit ∧
      subBd Λ₁ = C_out.U ∧ subBd (closure Λ₁) = C_out.U ∧ closure Λ₁ \ C_out.U = Λ₁ ∧
      IsLambdaZoneAround H d (3 * beta + 3) z Λ₁ ∧
      (∀ x ∈ H.A, d z x < 3 * beta + 1 → x ⊆ Λ₁) ∧
      closure Λ₂ ⊆ Λ₁ ∧
      IsDiscNest H (closure Λ₁) C_in C_out C₀ ∧
      discIns (closure Λ₁) (C₀ ⟨0, Nat.succ_pos beta⟩) = closure Λ₂ := by
  have h91 := GM11.gm15_theorem_9_1 H θ T d hS hConn hMetric
  have hsymm := h91.2.2.2.1
  have htri := h91.2.2.2.2.1
  have hv_reg := h91.2.2.2.2.2.1
  have hE : H.E.Nonempty := edgeSet_nonempty_of_isTangle hMetric.1.2.1 (by omega)
  obtain ⟨C_in, Λ₂, hCinH, hCin, hbd₂, hbd_cl₂, hdiff₂, hZone₂, hsub₂⟩ :=
    full_of_9_2 hS hConn H θ beta T d z hMetric hz (by omega) (by omega)
  obtain ⟨C_out, Λ₁, hCoutH, hCout, hbd₁, hbd_cl₁, hdiff₁, hZone₁, hsub₁⟩ :=
    full_of_9_2 hS hConn H θ (3 * beta + 1) T d z hMetric hz (by omega) (by omega)
  have hcl₂_sub_Λ₁ : closure Λ₂ ⊆ Λ₁ :=
    closure_zone_subset hS hZone₂ fun x hx hle => hsub₁ x hx (by omega)
  have hcl₂_sub_int₁ : closure Λ₂ ⊆ closure Λ₁ \ subBd (closure Λ₁) := by
    rw [hbd_cl₁, hdiff₁]
    exact hcl₂_sub_Λ₁
  -- Show `beta ≤ regionalDistance H (closure Λ₂) (subBd (closure Λ₁))`.
  have hdist_ge : beta ≤ regionalDistance H (closure Λ₂) (subBd (closure Λ₁)) := by
    have hcl₂_ne : (closure Λ₂).Nonempty := IsClosedDisc.nonempty hZone₂.isClosedDisc_closure
    have hbd₁_ne : (subBd (closure Λ₁)).Nonempty := by
      rw [hbd_cl₁]
      exact IsOArc.nonempty (isOArc_of_isCircuit hCout)
    have hspec := regionalDistance_spec hS H hcl₂_ne hbd₁_ne
    generalize hk : regionalDistance H (closure Λ₂) (subBd (closure Λ₁)) = k at hspec ⊢
    obtain ⟨v_seq, r_seq, hv0, hvlast, hsteps⟩ := hspec
    rcases k with _ | m
    · exfalso
      have h0 : Fin.last 0 = (0 : Fin 1) := rfl
      rw [h0] at hvlast
      exact (hcl₂_sub_int₁ hv0).2 hvlast
    · -- First region `r_seq 0` has `d z (r_seq 0) ≤ beta + 3`.
      have hr0_le : d z (r_seq 0) ≤ beta + 3 := by
        have hr0_R : r_seq 0 ∈ H.R := (hsteps 0).1
        have hv0_r0 : v_seq 0 ∈ closure (r_seq 0) := (hsteps 0).2.1
        obtain ⟨x₀, hx₀A, hv0_x₀⟩ := exists_atom_mem_of_point H (v_seq 0)
        have hx₀_cl₂ : x₀ ⊆ closure Λ₂ :=
          atom_subset_closure_of_inter_nonempty hS hCinH hZone₂.isClosedDisc_closure
            hbd_cl₂ hdiff₂ hx₀A ⟨v_seq 0, hv0_x₀, hv0⟩
        rcases eq_or_exists_vertex_of_mem_closure_region hS hr0_R hx₀A hv0_x₀ hv0_r0 with
          rfl | ⟨_, v, hvH, hv_x₀, hv_r0⟩
        · have hle := hZone₂.dist_le (r_seq 0) hx₀A hx₀_cl₂
          omega
        · have hv_cl₂ : ({v} : Set S) ⊆ closure Λ₂ :=
            singleton_subset_iff.mpr (isClosed_closure.closure_subset_iff.mpr hx₀_cl₂ hv_x₀)
          have hvA : ({v} : Set S) ∈ H.A := Or.inl (Or.inl ⟨v, hvH, rfl⟩)
          have h1 := hZone₂.dist_le {v} hvA hv_cl₂
          have h2 := hv_reg hE v hvH (r_seq 0) hr0_R hv_r0
          have h3 := htri z hz {v} hvA (r_seq 0) (Or.inr hr0_R)
          omega
      -- Induction: `d z (r_seq ⟨j, hj⟩) ≤ beta + 3 + 2 * j`.
      have hind_r : ∀ j : ℕ, (hj : j < m + 1) → d z (r_seq ⟨j, hj⟩) ≤ beta + 3 + 2 * j := by
        intro j
        induction j with
        | zero => intro _; simpa using hr0_le
        | succ j ih =>
          intro hj
          have hj' : j < m + 1 := Nat.lt_of_succ_lt hj
          have hih := ih hj'
          have hr_j : r_seq ⟨j, hj'⟩ ∈ H.R := (hsteps ⟨j, hj'⟩).1
          have hr_j1 : r_seq ⟨j + 1, hj⟩ ∈ H.R := (hsteps ⟨j + 1, hj⟩).1
          have hp_j : v_seq (⟨j, hj'⟩ : Fin (m + 1)).succ ∈ closure (r_seq ⟨j, hj'⟩) :=
            (hsteps ⟨j, hj'⟩).2.2
          have hp_j1 : v_seq (⟨j + 1, hj⟩ : Fin (m + 1)).castSucc ∈ closure (r_seq ⟨j + 1, hj⟩) :=
            (hsteps ⟨j + 1, hj⟩).2.1
          have heq_idx : (⟨j, hj'⟩ : Fin (m + 1)).succ = (⟨j + 1, hj⟩ : Fin (m + 1)).castSucc := rfl
          rw [← heq_idx] at hp_j1
          have hstep_le :=
            tangleMetric_regions_le_two_of_inter_closures hS hConn hMetric hE hr_j hr_j1 hp_j hp_j1
          have htri_j := htri z hz (r_seq ⟨j, hj'⟩) (Or.inr hr_j) (r_seq ⟨j + 1, hj⟩) (Or.inr hr_j1)
          omega
      -- Last region `r_seq ⟨m, _⟩` has `3 * beta ≤ d z (r_seq ⟨m, _⟩)`.
      let i_last : Fin (m + 1) := ⟨m, Nat.lt_succ_self m⟩
      have hr_last_R : r_seq i_last ∈ H.R := (hsteps i_last).1
      have hv_last_r : v_seq (Fin.last (m + 1)) ∈ closure (r_seq i_last) := (hsteps i_last).2.2
      have hv_last_CU : v_seq (Fin.last (m + 1)) ∈ C_out.U := hbd_cl₁ ▸ hvlast
      obtain ⟨x_l, hx_lA, hv_xl⟩ := exists_atom_mem_of_point H (v_seq (Fin.last (m + 1)))
      rcases eq_or_exists_vertex_of_mem_closure_region hS hr_last_R hx_lA hv_xl hv_last_r with
        rfl | ⟨_, v_l, hv_lH, hv_l_xl, hv_l_r⟩
      · exact absurd (hCoutH.U_subset hv_last_CU) (region_subset hr_last_R hv_xl)
      · have hv_l_CU : v_l ∈ C_out.U := by
          rcases hx_lA with (⟨w, _, rfl⟩ | he) | hs
          · have hvw : v_l = w :=
              mem_singleton_iff.mp ((isClosed_singleton (x := w)).closure_eq ▸ hv_l_xl)
            have hpw : v_seq (Fin.last (m + 1)) = w := mem_singleton_iff.mp hv_xl
            exact hvw ▸ hpw ▸ hv_last_CU
          · have hp_not_V : v_seq (Fin.last (m + 1)) ∉ C_out.V :=
              fun hV => (he.2.1 hv_xl).2 (hCoutH.1 hV)
            obtain ⟨f, hfC, hpf⟩ := C_out.exists_edge_of_mem hv_last_CU hp_not_V
            have heq : x_l = f := H.edge_eq_of_mem he (hCoutH.2 hfC) hv_xl hpf
            exact C_out.closure_subset_U hfC (heq ▸ hv_l_xl)
          · exact absurd (hCoutH.U_subset hv_last_CU) (region_subset hs hv_xl)
        have hv_l_not_Λ₁ : ¬ ({v_l} : Set S) ⊆ Λ₁ := by
          intro hsub
          exact (hdiff₁ ▸ hsub (mem_singleton v_l)).2 hv_l_CU
        have hv_lA : ({v_l} : Set S) ∈ H.A := Or.inl (Or.inl ⟨v_l, hv_lH, rfl⟩)
        have hge_vl : 3 * beta + 1 ≤ d z {v_l} := by
          by_contra hlt
          exact hv_l_not_Λ₁ (hsub₁ {v_l} hv_lA (by omega))
        have hle_rv : d (r_seq i_last) {v_l} ≤ 1 := by
          rw [hsymm (r_seq i_last) (Or.inr hr_last_R) {v_l} hv_lA]
          exact hv_reg hE v_l hv_lH (r_seq i_last) hr_last_R hv_l_r
        have htri_last := htri z hz (r_seq i_last) (Or.inr hr_last_R) {v_l} hv_lA
        have hle_last : d z (r_seq i_last) ≤ beta + 3 + 2 * m := hind_r m (Nat.lt_succ_self m)
        omega
  -- Apply `theorem_5_5_aux` with `m = beta - 1`.
  have hdist_ge' : (beta - 1) + 1 ≤ regionalDistance H (closure Λ₂) (subBd (closure Λ₁)) := by
    omega
  obtain ⟨C_mid, Λ_mid, hmid_props, hmid_nest⟩ :=
    theorem_5_5_aux hS H hZone₁.isClosedDisc_closure (beta - 1) hcl₂_sub_int₁
      (IsClosedDisc.nonempty hZone₂.isClosedDisc_closure)
      (IsClosedDisc.isPreconnected hZone₂.isClosedDisc_closure) hdist_ge'
  -- Assemble `C₀ : Fin (beta + 1) → Drawing S` and `Δ₀ : Fin (beta + 1) → Set S`.
  let C₀ : Fin (beta + 1) → Drawing S := fun j =>
    if hj0 : j.1 = 0 then C_in
    else if hjb : j.1 - 1 < beta - 1 then C_mid ⟨j.1 - 1, hjb⟩
    else C_out
  let Δ_seq : Fin (beta + 1) → Set S := fun j =>
    if hj0 : j.1 = 0 then closure Λ₂
    else if hjb : j.1 - 1 < beta - 1 then closure (Λ_mid ⟨j.1 - 1, hjb⟩)
    else closure Λ₁
  let Λ_seq : Fin (beta + 1) → Set S := fun j =>
    if hj0 : j.1 = 0 then Λ₂
    else if hjb : j.1 - 1 < beta - 1 then Λ_mid ⟨j.1 - 1, hjb⟩
    else Λ₁
  have hCinU_sub : C_in.U ⊆ closure Λ₂ := by
    rw [← hbd_cl₂, subBd_eq_frontier]
    exact hZone₂.isClosedDisc_closure.isCompact.isClosed.frontier_subset
  have hCoutU_sub : C_out.U ⊆ closure Λ₁ := by
    rw [← hbd_cl₁, subBd_eq_frontier]
    exact hZone₁.isClosedDisc_closure.isCompact.isClosed.frontier_subset
  have hseq_props : ∀ j : Fin (beta + 1),
      (C₀ j).IsSubdrawing H ∧ (C₀ j).IsCircuit ∧ (C₀ j).U ⊆ closure Λ₁ ∧
      IsClosedDisc (Δ_seq j) ∧ Δ_seq j ⊆ closure Λ₁ ∧
      subBd (Δ_seq j) = (C₀ j).U ∧ Δ_seq j \ (C₀ j).U = Λ_seq j ∧
      discIns (closure Λ₁) (C₀ j) = Δ_seq j := by
    intro j
    have hmain : (C₀ j).IsSubdrawing H ∧ (C₀ j).IsCircuit ∧ (C₀ j).U ⊆ closure Λ₁ ∧
        IsClosedDisc (Δ_seq j) ∧ Δ_seq j ⊆ closure Λ₁ ∧
        subBd (Δ_seq j) = (C₀ j).U ∧ Δ_seq j \ (C₀ j).U = Λ_seq j := by
      dsimp only [C₀, Δ_seq, Λ_seq]
      split_ifs with hj0 hjb
      · exact ⟨hCinH, hCin, hCinU_sub.trans (hcl₂_sub_int₁.trans sdiff_subset),
          hZone₂.isClosedDisc_closure, hcl₂_sub_int₁.trans sdiff_subset, hbd_cl₂, hdiff₂⟩
      · obtain ⟨h1, h2, h3, _, h5, h6, _, h8, h9, _⟩ := hmid_props ⟨j.1 - 1, hjb⟩
        exact ⟨h1, h2, h3.trans sdiff_subset, h6, h5.trans sdiff_subset, h8, h9⟩
      · exact ⟨hCoutH, hCout, hCoutU_sub, hZone₁.isClosedDisc_closure, Subset.rfl, hbd_cl₁, hdiff₁⟩
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hmain
    obtain ⟨_, huniq⟩ := discIns_spec hZone₁.isClosedDisc_closure h2 h3
    have hdiscIns_eq : discIns (closure Λ₁) (C₀ j) = Δ_seq j :=
      (huniq (Δ_seq j) h5 h4 ((IsClosedDisc.subBd_eq_discBd hS h4).symm.trans h6)).symm
    exact ⟨h1, h2, h3, h4, h5, h6, h7, hdiscIns_eq⟩
  have hnest_strict : ∀ j₁ j₂ : Fin (beta + 1), j₁ < j₂ → Δ_seq j₁ ⊆ Λ_seq j₂ := by
    intro j₁ j₂ hj12
    dsimp only [Δ_seq, Λ_seq]
    split_ifs with h10 h20 h2b h1b h20' h2b'
    · omega
    · exact (hmid_props ⟨j₂.1 - 1, h2b⟩).2.2.2.2.2.2.2.2.2
    · exact hcl₂_sub_Λ₁
    · omega
    · exact hmid_nest ⟨j₁.1 - 1, h1b⟩ ⟨j₂.1 - 1, h2b'⟩ (by change j₁.1 - 1 < j₂.1 - 1; omega)
    · rw [← hdiff₁, ← hbd_cl₁]
      exact (hmid_props ⟨j₁.1 - 1, h1b⟩).2.2.2.2.1
    · omega
    · omega
    · omega
  have hdisj_U : Pairwise (fun j₁ j₂ : Fin (beta + 1) => Disjoint (C₀ j₁).U (C₀ j₂).U) := by
    have key : ∀ j₁ j₂ : Fin (beta + 1), j₁ < j₂ → Disjoint (C₀ j₁).U (C₀ j₂).U := by
      intro j₁ j₂ hj12
      have hp₁ := hseq_props j₁
      have hp₂ := hseq_props j₂
      have hCU₁_sub_Δ₁ : (C₀ j₁).U ⊆ Δ_seq j₁ := by
        rw [← hp₁.2.2.2.2.2.1, subBd_eq_frontier]
        exact hp₁.2.2.2.1.isCompact.isClosed.frontier_subset
      have hsub_Λ₂ : (C₀ j₁).U ⊆ Λ_seq j₂ := hCU₁_sub_Δ₁.trans (hnest_strict j₁ j₂ hj12)
      refine disjoint_left.mpr fun x hx₁ hx₂ => ?_
      have hx_in : x ∈ Λ_seq j₂ := hsub_Λ₂ hx₁
      rw [← hp₂.2.2.2.2.2.2.1] at hx_in
      exact hx_in.2 hx₂
    intro j₁ j₂ hj12
    rcases lt_or_gt_of_ne hj12 with h | h
    · exact key j₁ j₂ h
    · exact (key j₂ j₁ h).symm
  have hC₀_nest : IsDiscNest H (closure Λ₁) C_in C_out C₀ := by
    refine ⟨fun j => ⟨(hseq_props j).1, (hseq_props j).2.1, (hseq_props j).2.2.1⟩,
      fun j₁ j₂ hj12 => disjoint_of_subset (C₀ j₁).V_subset_U (C₀ j₂).V_subset_U (hdisj_U hj12),
      fun j₁ j₂ hj12 => ?_, fun hs => ⟨?_, ?_⟩⟩
    · change discIns (closure Λ₁) (C₀ j₁) ⊆ discIns (closure Λ₁) (C₀ j₂)
      rw [(hseq_props j₁).2.2.2.2.2.2.2, (hseq_props j₂).2.2.2.2.2.2.2]
      rcases eq_or_lt_of_le hj12 with rfl | hlt
      · exact Subset.rfl
      · exact (hnest_strict j₁ j₂ hlt).trans
          ((hseq_props j₂).2.2.2.2.2.2.1 ▸ sdiff_subset)
    · simp [C₀]
    · dsimp only [C₀]
      split_ifs with h1 h2
      · omega
      · omega
      · rfl
  have hdiscIns_0 : discIns (closure Λ₁) (C₀ ⟨0, Nat.succ_pos beta⟩) = closure Λ₂ := by
    rw [(hseq_props ⟨0, Nat.succ_pos beta⟩).2.2.2.2.2.2.2]
    simp [Δ_seq]
  exact ⟨C_in, C_out, Λ₁, Λ₂, C₀, hCinH, hCin, hbd₂, hbd_cl₂, hdiff₂, hZone₂, hsub₂,
    hCoutH, hCout, hbd₁, hbd_cl₁, hdiff₁, hZone₁, hsub₁, hcl₂_sub_Λ₁, hC₀_nest, hdiscIns_0⟩

/-! ## 4. Claim (2) of (9.5): Menger Paths Between `bd(Λ₂)` and `bd(Λ₁)` -/

/-- If `C` is a subdrawing of `H`, every vertex of `H` in `C.U` belongs to `C.V`. -/
private theorem mem_subdrawing_V_of_mem_U {H C : Drawing S} (hCH : C.IsSubdrawing H) {v : S}
    (hvH : v ∈ H.V) (hvU : v ∈ C.U) : v ∈ C.V := by
  by_contra hvC
  obtain ⟨e, heC, hve⟩ := C.exists_edge_of_mem hvU hvC
  exact ((hCH.2 heC).2.1 hve).2 hvH

/-- Every walk in `H.toHypergraph.skeleton` lifts to a `GraphWalk H.toGraph` with the same vertex
support. -/
private theorem lift_skeleton_walk {H : Drawing S} {u v : S} (hu : u ∈ H.V)
    (w : H.toHypergraph.skeleton.Walk u v) :
    ∃ W : GraphWalk H.toGraph u v, W.support = w.support := by
  induction w with
  | nil => exact ⟨.nil hu, rfl⟩
  | @cons u x v hadj rest ih =>
    obtain ⟨hux, e, ⟨heE, huV, hue⟩, ⟨_, hxV, hxe⟩⟩ := hadj
    obtain ⟨W', hW'⟩ := ih hxV
    obtain ⟨a, b, hl⟩ := (H.toGraph.edge_mem_iff_exists_isLink e).mp heE
    have hcap := hl.2.2.2
    have hu_ab : u = a ∨ u = b := by
      have : u ∈ ({a, b} : Set S) := hcap ▸ ⟨hue, huV⟩
      simpa using this
    have hx_ab : x = a ∨ x = b := by
      have : x ∈ ({a, b} : Set S) := hcap ▸ ⟨hxe, hxV⟩
      simpa using this
    have hl_ux : H.toGraph.IsLink e u x := by
      rcases hu_ab with rfl | rfl <;> rcases hx_ab with rfl | rfl
      · exact (hux rfl).elim
      · exact hl
      · exact hl.symm
      · exact (hux rfl).elim
    exact ⟨.cons hl_ux W', congrArg (u :: ·) hW'⟩

/-- If a simple walk `W` in `H` starts at `u ∈ closure Λ₂` and ends at `v ∉ closure Λ₂` (where
`C_in` is a circuit of `H` with `subBd (closure Λ₂) = C_in.U` and `closure Λ₂ \ C_in.U = Λ₂`),
then `W` has a suffix `W₁` starting at some `a ∈ C_in.V` with `W₁.support ⊆ W.support`. -/
private theorem exists_suffix_from_inner_circuit
    (hS : IsClosedSurface S) {H C_in : Drawing S} {Λ₂ : Set S}
    (hCinH : C_in.IsSubdrawing H)
    (hOD₂ : IsOpenDisc Λ₂) (hCD₂ : IsClosedDisc (closure Λ₂))
    (hbd_cl₂ : subBd (closure Λ₂) = C_in.U) (hdiff₂ : closure Λ₂ \ C_in.U = Λ₂)
    {u v : S} (W : GraphWalk H.toGraph u v) (hWs : W.IsSimple)
    (hu : u ∈ closure Λ₂) (hv : v ∉ closure Λ₂) :
    ∃ a ∈ C_in.V, ∃ W₁ : GraphWalk H.toGraph a v,
      W₁.IsSimple ∧ ∀ x ∈ W₁.support, x ∈ W.support := by
  induction W with
  | nil _ => exact (hv hu).elim
  | @cons u w v e hl rest ih =>
    have hr_s : rest.IsSimple := (List.nodup_cons.mp hWs).2
    by_cases huC : u ∈ C_in.U
    · exact ⟨u, mem_subdrawing_V_of_mem_U hCinH hl.2.1 huC, .cons hl rest, hWs, fun _ hx => hx⟩
    · have hu_Λ₂ : u ∈ Λ₂ := hdiff₂ ▸ ⟨hu, huC⟩
      have hu_cl_e : u ∈ closure e := by
        have : u ∈ closure e ∩ H.V := hl.2.2.2 ▸ Or.inl rfl
        exact this.1
      obtain ⟨q, hq_Λ₂, hqe⟩ := mem_closure_iff.mp hu_cl_e Λ₂ hOD₂.1 hu_Λ₂
      have he_Λ₂ : e ⊆ Λ₂ :=
        atom_subset_open_of_inter_nonempty hS hCinH hCD₂ hbd_cl₂ hdiff₂
          (Or.inl (Or.inr hl.1)) ⟨q, hqe, hq_Λ₂⟩
      have hw_cl_e : w ∈ closure e := by
        have : w ∈ closure e ∩ H.V := hl.2.2.2 ▸ Or.inr rfl
        exact this.1
      have hw_cl₂ : w ∈ closure Λ₂ := closure_mono he_Λ₂ hw_cl_e
      obtain ⟨a, haC, W₁, hW₁s, hsupp⟩ := ih hr_s hw_cl₂ hv
      exact ⟨a, haC, W₁, hW₁s, fun x hx => List.mem_cons_of_mem _ (hsupp x hx)⟩

/-- If a simple walk `W₂` in `H` from `a` to `b` satisfies `∀ x ∈ W₂.support, x ≠ b → x ∈ Λ₁`,
then every edge of `W₂` is a subset of `Λ₁`, and if `a ≠ b` then `b ∈ closure Λ₁`. -/
private theorem edges_subset_and_end_mem_closure_of_before_end
    (hS : IsClosedSurface S) {H C_out : Drawing S} {Λ₁ : Set S}
    (hCoutH : C_out.IsSubdrawing H)
    (hOD₁ : IsOpenDisc Λ₁) (hCD₁ : IsClosedDisc (closure Λ₁))
    (hbd_cl₁ : subBd (closure Λ₁) = C_out.U) (hdiff₁ : closure Λ₁ \ C_out.U = Λ₁)
    {a b : S} (W₂ : GraphWalk H.toGraph a b) (hW₂s : W₂.IsSimple)
    (hbefore : ∀ x ∈ W₂.support, x ≠ b → x ∈ Λ₁) :
    (∀ e ∈ W₂.edges, e ⊆ Λ₁) ∧ (a ≠ b → b ∈ closure Λ₁) := by
  induction W₂ with
  | nil _ => exact ⟨nofun, fun hne => (hne rfl).elim⟩
  | @cons a w b e hl rest ih =>
    have ha_not : a ∉ rest.support := (List.nodup_cons.mp hW₂s).1
    have hr_s : rest.IsSimple := (List.nodup_cons.mp hW₂s).2
    have hab : a ≠ b := fun h => ha_not (h ▸ rest.end_mem_support)
    have ha_Λ₁ : a ∈ Λ₁ := hbefore a (List.Mem.head _) hab
    have ha_cl_e : a ∈ closure e := by
      have : a ∈ closure e ∩ H.V := hl.2.2.2 ▸ Or.inl rfl
      exact this.1
    obtain ⟨q, hq_Λ₁, hqe⟩ := mem_closure_iff.mp ha_cl_e Λ₁ hOD₁.1 ha_Λ₁
    have he_Λ₁ : e ⊆ Λ₁ :=
      atom_subset_open_of_inter_nonempty hS hCoutH hCD₁ hbd_cl₁ hdiff₁
        (Or.inl (Or.inr hl.1)) ⟨q, hqe, hq_Λ₁⟩
    obtain ⟨hed, hend⟩ := ih hr_s (fun x hx hxb => hbefore x (List.mem_cons_of_mem _ hx) hxb)
    refine ⟨fun f hf => ?_, fun _ => ?_⟩
    · rcases List.mem_cons.mp hf with rfl | hfr
      · exact he_Λ₁
      · exact hed f hfr
    · by_cases hwb : w = b
      · subst hwb
        have hw_cl_e : w ∈ closure e := by
          have : w ∈ closure e ∩ H.V := hl.2.2.2 ▸ Or.inr rfl
          exact this.1
        exact closure_mono he_Λ₁ hw_cl_e
      · exact hend hwb

private theorem path_separator_partitions_the_drawing
    {H : Drawing S} (Z₁ X : Set S)
    {A B : Hypergraph S (Set S)}
    (hA : A ≤ H.toHypergraph) (hB : B ≤ H.toHypergraph)
    (hAV : A.vertexSet = sepCompLeft H.toHypergraph.skeleton H.V X Z₁ ∪ X)
    (hBV : B.vertexSet = sepCompRight H.toHypergraph.skeleton H.V X Z₁ ∪ X)
    (hBE : B.edgeSet = H.E \ A.edgeSet) : H.toHypergraph.IsSeparation A B := by
  refine (isSeparation_iff_of_le hA hB).mpr ⟨?_, ?_, ?_⟩
  · refine Subset.antisymm (union_subset hA.vertexSet_subset hB.vertexSet_subset) ?_
    intro v hv
    rw [hAV, hBV]
    rcases subset_sepComp_union H.toHypergraph.skeleton Z₁ hv with (h | h) | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl (Or.inr h)
  · rw [hBE]
    ext e
    constructor
    · exact fun h => h.elim (fun he => hA.edgeSet_subset he) And.left
    · exact fun he => (em (e ∈ A.edgeSet)).imp_right fun hn => ⟨he, hn⟩
  · rw [hBE]
    exact (disjoint_left.mpr fun _ h₁ h₂ => h₂.2 h₁ : Disjoint A.edgeSet (H.E \ A.edgeSet)).inter_eq

private theorem inner_zone_regions_are_on_first_tangle_side
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    (hS : IsClosedSurface S)
    {H : Drawing S}
    {C_in : Drawing S}
    {beta : ℕ}
    {d : Set S → Set S → ℕ}
    {z : Set S}
    {Λ₂ : Set S}
    (hCinH : C_in.IsSubdrawing H)
    (hbd_cl₂ : subBd (closure Λ₂) = C_in.U)
    (hdiff₂ : closure Λ₂ \ C_in.U = Λ₂)
    (hZone₂ : IsLambdaZoneAround H d (beta + 2) z Λ₂)
    (A : Hypergraph S (Set S))
    (he_E₁_of_cl₂ : ∀ e ∈ H.E, e ⊆ closure Λ₂ → e ∈ A.edgeSet)
    (K : Drawing S)
    (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K)
    (hrf : RegionFacts (PaintingOrDrawing.drawing H) K) :
    ∀ r ∈ K.R, (r ∩ Λ₂).Nonempty → r ∈ (PaintingOrDrawing.regionsIncludingEdge K A) := by
  let Z_A := PaintingOrDrawing.regionsIncludingEdge K A
  intro r hr ⟨y, hyr, hy_Λ₂⟩
  obtain ⟨e, heH, her⟩ := hrf.1 r hr
  have he_cl₂ : e ⊆ closure Λ₂ := by
    by_cases hmeet : (e ∩ closure Λ₂).Nonempty
    · exact atom_subset_closure_of_inter_nonempty hS hCinH hZone₂.isClosedDisc_closure
        hbd_cl₂ hdiff₂ (Or.inl (Or.inr heH)) hmeet
    · have hdis_r_CU : Disjoint r C_in.U := by
        refine disjoint_left.mpr fun x hxr hxCU => ?_
        have hx_not_KV : x ∉ K.V := fun hxV => (region_subset hr hxr) (K.V_subset_U hxV)
        have hx_not_HV : x ∉ H.V := fun hxV => hx_not_KV (hK.2.1.2.1 hxV)
        have hx_not_CV : x ∉ C_in.V := fun hxV => hx_not_HV (hCinH.1 hxV)
        obtain ⟨f, hfC, hxf⟩ := C_in.exists_edge_of_mem hxCU hx_not_CV
        have hfH : f ∈ H.E := hCinH.2 hfC
        obtain ⟨hf_pre, hf_disjV, hf_U, _⟩ := (PaintingOrDrawing.drawing H).edge_props hfH
        have hf_off_KU : ∀ z ∈ f, z ∉ K.U := fun z hzf hzKU => by
          have hz_in : z ∈ (PaintingOrDrawing.drawing H).U ∩ K.U := ⟨hf_U hzf, hzKU⟩
          rw [hK.2.1.1] at hz_in
          exact disjoint_left.mp hf_disjV hzf hz_in
        have hr_eq : r = connectedComponentIn (univ \ K.U) x :=
          region_eq_of_mem hr ((mem_R_iff K).mpr ⟨x, fun hxKU => region_subset hr hxr hxKU,
            rfl⟩)
            hxr (mem_connectedComponentIn ⟨mem_univ x, fun hxKU => region_subset hr hxr hxKU⟩)
        have hfr : f ⊆ r := by
          rw [hr_eq]
          exact hf_pre.subset_connectedComponentIn hxf fun z hzf => ⟨mem_univ z,
            hf_off_KU z hzf⟩
        have hfe : f = e := hrf.2.1 r hr f hfH e heH hfr her
        subst hfe
        exact hmeet ⟨x, hxf, hZone₂.isClosedDisc_closure.isCompact.isClosed.frontier_subset
          (subBd_eq_frontier (closure Λ₂) ▸ hbd_cl₂ ▸ hxCU)⟩
      have hdis_fr : Disjoint r (frontier (closure Λ₂)) := by
        rwa [← subBd_eq_frontier, hbd_cl₂]
      have hr_cl₂ : r ⊆ closure Λ₂ :=
        subset_of_disjoint_frontier (region_isPreconnected hr) isClosed_closure
          hdis_fr hyr (subset_closure hy_Λ₂)
      exact her.trans hr_cl₂
  exact ⟨hr, e, he_E₁_of_cl₂ e heH he_cl₂, her⟩

private theorem first_tangle_side_boundary_avoids_inner_zone
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    (hS : IsClosedSurface S)
    {H : Drawing S}
    {beta : ℕ}
    {d : Set S → Set S → ℕ}
    {z : Set S}
    {Λ₂ : Set S}
    (hZone₂ : IsLambdaZoneAround H d (beta + 2) z Λ₂)
    (K : Drawing S)
    (A : Hypergraph S (Set S))
    (hNs : (boundaryDrawing K (PaintingOrDrawing.regionsIncludingEdge K A)).IsSubdrawing K)
    (hr_in_ZA : ∀ r ∈ K.R, (r ∩ Λ₂).Nonempty → r ∈ (PaintingOrDrawing.regionsIncludingEdge K A)) :
    Disjoint (boundaryDrawing K (PaintingOrDrawing.regionsIncludingEdge K A)).U Λ₂ := by
  let Z_A := PaintingOrDrawing.regionsIncludingEdge K A
  let N := boundaryDrawing K Z_A
  rw [N.U_eq]
  refine disjoint_union_left.mpr ⟨disjoint_left.mpr fun v hvN hv_Λ₂ => ?_,
    disjoint_iUnion₂_left.mpr fun f hfN => disjoint_left.mpr fun x hxf hx_Λ₂ => ?_⟩
  · obtain ⟨-, r₂, ⟨hr₂R, hr₂not⟩, hinc⟩ := (mem_boundaryDrawing_V (Γ := K) hS).mp hvN
    obtain ⟨q, hq_Λ₂, hqr₂⟩ := mem_closure_iff.mp hinc.2.2 Λ₂ hZone₂.isOpenDisc.1 hv_Λ₂
    exact hr₂not (hr_in_ZA r₂ hr₂R ⟨q, hqr₂, hq_Λ₂⟩)
  · obtain ⟨-, r₂, ⟨hr₂R, hr₂not⟩, hinc⟩ := (mem_boundaryDrawing_E (Γ := K)).mp hfN
    have hfr₂ : f ⊆ closure r₂ :=
      edge_subset_closure_of_incident hS (hNs.2 hfN) hr₂R hinc.2.2
    have hx_r₂ : x ∈ closure r₂ := isClosed_closure.closure_subset_iff.mpr hfr₂ hxf
    obtain ⟨q, hq_Λ₂, hqr₂⟩ := mem_closure_iff.mp hx_r₂ Λ₂ hZone₂.isOpenDisc.1 hx_Λ₂
    exact hr₂not (hr_in_ZA r₂ hr₂R ⟨q, hqr₂, hq_Λ₂⟩)

private theorem disjoint_skeleton_paths_restrict_to_annulus
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    (hS : IsClosedSurface S)
    {H : Drawing S}
    {C_in : Drawing S}
    {C_out : Drawing S}
    {beta : ℕ}
    {d : Set S → Set S → ℕ}
    {z : Set S}
    {Λ₁ : Set S}
    {Λ₂ : Set S}
    (hCinH : C_in.IsSubdrawing H)
    (hbd_cl₂ : subBd (closure Λ₂) = C_in.U)
    (hdiff₂ : closure Λ₂ \ C_in.U = Λ₂)
    (hZone₂ : IsLambdaZoneAround H d (beta + 2) z Λ₂)
    (hCoutH : C_out.IsSubdrawing H)
    (hbd_cl₁ : subBd (closure Λ₁) = C_out.U)
    (hdiff₁ : closure Λ₁ \ C_out.U = Λ₁)
    (hZone₁ : IsLambdaZoneAround H d (3 * beta + 3) z Λ₁)
    (hcl₂_sub_Λ₁ : closure Λ₂ ⊆ Λ₁)
    (P_skel : Fin beta → PathFromTo H.toHypergraph.skeleton (H.V ∩ closure Λ₂) (H.V \ Λ₁)) :
    ∀ (i : Fin beta), ∃ (a b : S) (W₂ : GraphWalk H.toGraph a b),
      a ∈ C_in.V ∧ b ∈ C_out.V ∧ W₂.IsSimple ∧ (walkDrawing H W₂).U ⊆ closure Λ₁ ∧
        ∀ x ∈ W₂.support, x ∈ (P_skel i).walk.support := by
  let Z₁ := H.V ∩ closure Λ₂
  let Z₂ := H.V \ Λ₁
  intro i
  obtain ⟨W₀, hW₀_supp⟩ := lift_skeleton_walk (P_skel i).first_mem.1 (P_skel i).walk
  have hW₀s : W₀.IsSimple := by
    change W₀.support.Nodup
    rw [hW₀_supp]
    exact (P_skel i).isPath.support_nodup
  have hu₀_cl₂ : (P_skel i).first ∈ closure Λ₂ := (P_skel i).first_mem.2
  have hv₀_not_Λ₁ : (P_skel i).last ∉ Λ₁ := (P_skel i).last_mem.2
  have hv₀_not_cl₂ : (P_skel i).last ∉ closure Λ₂ :=
    fun h => hv₀_not_Λ₁ (hcl₂_sub_Λ₁ h)
  obtain ⟨a, haC, W₁, hW₁s, hW₁_supp⟩ :=
    exists_suffix_from_inner_circuit hS hCinH hZone₂.isOpenDisc
      hZone₂.isClosedDisc_closure hbd_cl₂ hdiff₂ W₀ hW₀s hu₀_cl₂ hv₀_not_cl₂
  have hhit_out : ∃ x ∈ W₁.support, x ∈ H.V \ Λ₁ :=
    ⟨(P_skel i).last, W₁.end_mem_support, (P_skel i).last_mem⟩
  obtain ⟨b, hb_out, W₂, W_rest, hsplit₁, hW₂_first⟩ := exists_first_hit_split W₁ hhit_out
  have hW₂s : W₂.IsSimple := (GM09.isSimple_of_append (hsplit₁ ▸ hW₁s)).1
  have ha_Λ₁ : a ∈ Λ₁ := hcl₂_sub_Λ₁
    (hZone₂.isClosedDisc_closure.isCompact.isClosed.frontier_subset
    (subBd_eq_frontier (closure Λ₂) ▸ hbd_cl₂ ▸ C_in.V_subset_U haC))
  have hab : a ≠ b := fun h => hb_out.2 (h ▸ ha_Λ₁)
  have hbefore : ∀ x ∈ W₂.support, x ≠ b → x ∈ Λ₁ := by
    intro x hx hxb
    by_contra hx_not
    exact hxb (hW₂_first x hx ⟨mem_V_of_mem_support W₂ hx, hx_not⟩)
  obtain ⟨hed_Λ₁, hb_cl₁⟩ :=
    edges_subset_and_end_mem_closure_of_before_end hS hCoutH hZone₁.isOpenDisc
      hZone₁.isClosedDisc_closure hbd_cl₁ hdiff₁ W₂ hW₂s hbefore
  have hb_CU : b ∈ C_out.U := by
    by_contra hb_not_CU
    exact hb_out.2 (hdiff₁ ▸ ⟨hb_cl₁ hab, hb_not_CU⟩)
  have hbC : b ∈ C_out.V := mem_subdrawing_V_of_mem_U hCoutH hb_out.1 hb_CU
  have hW₂_U : (walkDrawing H W₂).U ⊆ closure Λ₁ := by
    intro z hz
    rcases walk_U_cases hz with hz_supp | ⟨e, he, hze⟩
    · by_cases hzb : z = b
      · exact hzb ▸ hb_cl₁ hab
      · exact subset_closure (hbefore z hz_supp hzb)
    · exact subset_closure (hed_Λ₁ e he hze)
  have hW₂_supp : ∀ x ∈ W₂.support, x ∈ (P_skel i).walk.support := by
    intro x hx
    rw [← hW₀_supp]
    exact hW₁_supp x (hsplit₁ ▸ (GraphWalk.mem_support_append W₂ W_rest).mpr (Or.inl hx))
  exact ⟨a, b, W₂, haC, hbC, hW₂s, hW₂_U, hW₂_supp⟩

/-- Claim (2) in the proof of Graph Minors XIV, (9.5) (page 46):
"There are $\beta$ mutually disjoint paths $P_1, \dots, P_\beta$ of $H \cap \bar{\Lambda}_1$
from $bd(\Lambda_2)$ to $bd(\Lambda_1)$." -/
private theorem lemma_9_5_claim_2 [T2Space S]
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {H C_in C_out : Drawing S} {θ beta : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {z Λ₁ Λ₂ : Set S}
    (hMetric : HasTangleMetric H θ T d) (hz : z ∈ H.A)
    (hbeta : 4 ≤ beta) (hθ : 16 * beta + 17 ≤ θ)
    (hCinH : C_in.IsSubdrawing H) (hCin : C_in.IsCircuit)
    (hbd_cl₂ : subBd (closure Λ₂) = C_in.U) (hdiff₂ : closure Λ₂ \ C_in.U = Λ₂)
    (hZone₂ : IsLambdaZoneAround H d (beta + 2) z Λ₂)
    (hsub₂ : ∀ x ∈ H.A, d z x < beta → x ⊆ Λ₂)
    (hCoutH : C_out.IsSubdrawing H) (_hCout : C_out.IsCircuit)
    (hbd_cl₁ : subBd (closure Λ₁) = C_out.U) (hdiff₁ : closure Λ₁ \ C_out.U = Λ₁)
    (hZone₁ : IsLambdaZoneAround H d (3 * beta + 3) z Λ₁)
    (hcl₂_sub_Λ₁ : closure Λ₂ ⊆ Λ₁) :
    ∃ P₀ : Fin beta → Drawing S, IsDiscPaths H (closure Λ₁) C_in C_out P₀ := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  let Z₁ : Set S := H.V ∩ closure Λ₂
  let Z₂ : Set S := H.V \ Λ₁
  have hZ₁_sub : Z₁ ⊆ H.toHypergraph.vertexSet := inter_subset_left
  have hZ₂_sub : Z₂ ⊆ H.toHypergraph.vertexSet := sdiff_subset
  by_cases hpaths : HasDisjointPaths H.toHypergraph.skeleton Z₁ Z₂ beta
  · -- Case 1: Menger gives `beta` disjoint paths in `H.toHypergraph.skeleton` from `Z₁` to `Z₂`.
    obtain ⟨P_skel, hP_disj⟩ := hpaths
    have hex_sub : ∀ i : Fin beta, ∃ (a b : S) (W₂ : GraphWalk H.toGraph a b),
        a ∈ C_in.V ∧ b ∈ C_out.V ∧ W₂.IsSimple ∧
        (walkDrawing H W₂).U ⊆ closure Λ₁ ∧
        ∀ x ∈ W₂.support, x ∈ (P_skel i).walk.support := by
      exact disjoint_skeleton_paths_restrict_to_annulus (S := S) hS (H := H) (C_in := C_in) (C_out
        := C_out) (beta := beta) (d := d) (z := z) (Λ₁ := Λ₁) (Λ₂ := Λ₂) hCinH hbd_cl₂ hdiff₂
        hZone₂ hCoutH hbd_cl₁ hdiff₁ hZone₁ hcl₂_sub_Λ₁ P_skel
    choose a b W₂ haC hbC hW₂s hW₂_U hW₂_supp using hex_sub
    refine ⟨fun i => walkDrawing H (W₂ i),
      fun i => ⟨walkDrawing_isSubdrawing H (W₂ i), hW₂_U i,
        ⟨a i, haC i, b i, hbC i, walkDrawing_isPathBetween H (hW₂s i)⟩⟩,
      fun i₁ i₂ hne => ?_⟩
    change Disjoint (walkDrawing H (W₂ i₁)).V (walkDrawing H (W₂ i₂)).V
    rw [walkDrawing_V, walkDrawing_V]
    exact disjoint_left.mpr fun x hx₁ hx₂ =>
      disjoint_left.mp (hP_disj hne) (hW₂_supp i₁ x hx₁) (hW₂_supp i₂ x hx₂)
  · -- Case 2: Menger gives a vertex separator `X ⊆ H.V` of `Z₁` and `Z₂` with `|X| < beta`.
    exfalso
    obtain ⟨X, hsep_X, hX_lt⟩ :=
      exists_separates_lt_of_not_hasDisjointPaths H.toHypergraph hZ₁_sub hZ₂_sub hpaths
    let C₁ := sepCompLeft H.toHypergraph.skeleton H.toHypergraph.vertexSet X Z₁
    let C₂ := sepCompRight H.toHypergraph.skeleton H.toHypergraph.vertexSet X Z₁
    have hC₁_sub : C₁ ⊆ H.V := sepCompLeft_subset _ _ _ _
    have hC₂_sub : C₂ ⊆ H.V := sepCompRight_subset _ _ _ _
    have hX_sub : X ⊆ H.V := hsep_X.1
    have hZ₁_C₁X : Z₁ ⊆ C₁ ∪ X := subset_sepCompLeft_union H.toHypergraph.skeleton hZ₁_sub
    have hZ₂_C₂X : Z₂ ⊆ C₂ ∪ X := subset_sepCompRight_union hZ₂_sub hsep_X
    have hC₁_Λ₁ : ∀ u ∈ C₁, u ∈ Λ₁ := by
      intro u hu
      by_contra hu_not
      have hu_Z₂ : u ∈ Z₂ := ⟨hC₁_sub hu, hu_not⟩
      rcases hZ₂_C₂X hu_Z₂ with huC₂ | huX
      · exact disjoint_left.mp (disjoint_sepCompLeft_sepCompRight _ _ _ _) hu huC₂
      · exact disjoint_left.mp (disjoint_sepCompLeft_sep _ _ _ _) hu huX
    let E₁ : Set (Set S) := {e ∈ H.E | e ⊆ closure Λ₁ ∧ H.toHypergraph.ends e ⊆ C₁ ∪ X}
    have hE₁_of_C₁ : ∀ e ∈ H.E, ∀ u ∈ H.toHypergraph.ends e, u ∈ C₁ → e ∈ E₁ := by
      intro e he u hu_end huC₁
      have hu_Λ₁ : u ∈ Λ₁ := hC₁_Λ₁ u huC₁
      obtain ⟨q, hq_Λ₁, hqe⟩ := mem_closure_iff.mp hu_end.2.2 Λ₁ hZone₁.isOpenDisc.1 hu_Λ₁
      have he_Λ₁ : e ⊆ Λ₁ :=
        atom_subset_open_of_inter_nonempty hS hCoutH
          hZone₁.isClosedDisc_closure hbd_cl₁ hdiff₁ (Or.inl (Or.inr he)) ⟨q, hqe, hq_Λ₁⟩
      refine ⟨he, he_Λ₁.trans subset_closure, fun v hv_end => ?_⟩
      have hvV : v ∈ H.V := hv_end.2.1
      by_cases huv : u = v
      · exact Or.inl (huv ▸ huC₁)
      · have hadj : H.toHypergraph.skeleton.Adj u v := ⟨huv, e, hu_end, hv_end⟩
        rcases subset_sepComp_union H.toHypergraph.skeleton Z₁ hvV with (hv1 | hv2) | hvX
        · exact Or.inl hv1
        · exact (not_adj_sepCompLeft_sepCompRight huC₁ hv2 hadj).elim
        · exact Or.inr hvX
    have hE₂_ends : ∀ e ∈ H.E \ E₁, H.toHypergraph.ends e ⊆ C₂ ∪ X := by
      intro e ⟨he, he_not⟩ v hv_end
      have hvV : v ∈ H.V := hv_end.2.1
      rcases subset_sepComp_union H.toHypergraph.skeleton Z₁ hvV with (hv1 | hv2) | hvX
      · exact (he_not (hE₁_of_C₁ e he v hv_end hv1)).elim
      · exact Or.inl hv2
      · exact Or.inr hvX
    let A : Hypergraph S (Set S) :=
      { vertexSet := C₁ ∪ X
        edgeSet := E₁
        Inc := fun e v => e ∈ E₁ ∧ H.toHypergraph.Inc e v
        vertex_mem_of_inc := fun _ _ ⟨he, hv⟩ => he.2.2 hv
        edge_mem_of_inc := fun _ _ h => h.1
        vertexSet_finite := H.finite_V.subset (union_subset hC₁_sub hX_sub)
        edgeSet_finite := H.finite_edges.subset fun _ h => h.1 }
    let B : Hypergraph S (Set S) :=
      { vertexSet := C₂ ∪ X
        edgeSet := H.E \ E₁
        Inc := fun e v => e ∈ H.E \ E₁ ∧ H.toHypergraph.Inc e v
        vertex_mem_of_inc := fun e _ ⟨he, hv⟩ => hE₂_ends e he hv
        edge_mem_of_inc := fun _ _ h => h.1
        vertexSet_finite := H.finite_V.subset (union_subset hC₂_sub hX_sub)
        edgeSet_finite := H.finite_edges.subset sdiff_subset }
    have hsep_AB : H.toHypergraph.IsSeparation A B := by
      have hA : A ≤ H.toHypergraph :=
        ⟨union_subset hC₁_sub hX_sub, fun _ h => h.1, fun e he => by
          ext v
          exact ⟨fun h => ⟨he, h⟩, fun h => h.2⟩⟩
      have hB : B ≤ H.toHypergraph :=
        ⟨union_subset hC₂_sub hX_sub, sdiff_subset, fun e he => by
          ext v
          exact ⟨fun h => ⟨he, h⟩, fun h => h.2⟩⟩
      exact path_separator_partitions_the_drawing Z₁ X hA hB rfl rfl rfl
    have hinter_AB : (A ∩ B).vertexSet = X := by
      change (C₁ ∪ X) ∩ (C₂ ∪ X) = X
      ext v
      simp only [mem_inter_iff, mem_union]
      constructor
      · rintro ⟨h1 | hX1, h2 | hX2⟩
        · exact (disjoint_left.mp (disjoint_sepCompLeft_sepCompRight _ _ _ _) h1 h2).elim
        · exact hX2
        · exact hX1
        · exact hX1
      · intro hv
        exact ⟨Or.inr hv, Or.inr hv⟩
    have hord_AB : separationOrder A B = X.ncard := by
      unfold Hypergraph.separationOrder
      rw [hinter_AB]
    -- Every edge `e ∈ H.E` with `e ⊆ closure Λ₂` belongs to `E₁ = A.edgeSet`.
    have he_E₁_of_cl₂ : ∀ e ∈ H.E, e ⊆ closure Λ₂ → e ∈ E₁ := by
      intro e he he_cl₂
      refine ⟨he, he_cl₂.trans (hcl₂_sub_Λ₁.trans subset_closure), fun v hv_end => ?_⟩
      exact hZ₁_C₁X ⟨hv_end.2.1, isClosed_closure.closure_subset_iff.mpr he_cl₂ hv_end.2.2⟩
    -- Pick an edge `e₀ ∈ C_in.E`.
    have hCinE_ne : C_in.E.Nonempty := by
      obtain ⟨_, W_C, _, hpos, _, hCE⟩ := hCin
      cases W_C with
      | nil _ => exact absurd hpos (Nat.lt_irrefl 0)
      | @cons _ _ _ f _ _ => exact ⟨f, by rw [hCE]; exact List.mem_cons_self⟩
    obtain ⟨e₀, he₀C⟩ := hCinE_ne
    have he₀H : e₀ ∈ H.E := hCinH.2 he₀C
    have he₀_CU : e₀ ⊆ C_in.U := fun x hx => (he₀C.2.1 hx).1
    have he₀_cl₂ : e₀ ⊆ closure Λ₂ :=
      he₀_CU.trans (hbd_cl₂ ▸ subBd_eq_frontier (closure Λ₂) ▸
        hZone₂.isClosedDisc_closure.isCompact.isClosed.frontier_subset)
    have he₀_E₁ : e₀ ∈ A.edgeSet := he_E₁_of_cl₂ e₀ he₀H he₀_cl₂
    have hAE_ne_z : A.edgeSet ≠ {z} := by
      intro heq
      have he₀z : e₀ = z := mem_singleton_iff.mp (heq ▸ he₀_E₁)
      obtain ⟨p, hp⟩ := he₀C.1
      have hp_Λ₂ : p ∈ Λ₂ := hZone₂.z_subset (he₀z ▸ hp)
      exact (hdiff₂ ▸ hp_Λ₂).2 (he₀_CU hp)
    have hE : H.E.Nonempty := ⟨e₀, he₀H⟩
    -- By `(7.3)` (`theorem_7_3_proof`), `(B, A) ∉ T`, so `(A, B) ∈ T`.
    have hBA_not_T : (B, A) ∉ T := by
      intro hBA
      obtain ⟨e, heA, hdist_ge⟩ :=
        theorem_7_3_proof H θ T d B A z hS hConn hE hMetric hz hBA hAE_ne_z
      have hle_e : d z e ≤ 3 * beta + 3 := hZone₁.dist_le e (Or.inl (Or.inr heA.1)) heA.2.1
      have hord_BA : separationOrder B A = X.ncard := by
        rw [GM10.separationOrder_comm, hord_AB]
      omega
    have hAB_T : (A, B) ∈ T := by
      rcases hMetric.1.2.1.isPretangle.axiom1 hsep_AB (by omega) with hAB | hBA
      · exact hAB
      · exact (hBA_not_T hBA).elim
    -- Unpack radial drawing `K` and derived slope `ins`, and apply XI (6.3).
    rcases hMetric with ⟨hResp, K, ins, hK, hd, hd_eq⟩
    have hrf := GM11.regionFacts_of_radial ⟨hK.1, hK.2.1⟩ hS hK.2.2 hE
    have hT_eq := (GM11.theorem_6_3_proof S hS hConn (PaintingOrDrawing.drawing H) K θ T ins
      hResp.1 hE hResp.2.1.isPretangle hResp.2.2 hK hd).2
    have hsm : IsSmall K ins (2 * θ) H.V θ (PaintingOrDrawing.regionsIncludingEdge K A) := by
      have hmem : (A, B) ∈ inducedPretangle (PaintingOrDrawing.drawing H) K θ ins :=
        hT_eq ▸ hAB_T
      exact hmem.2.2
    let Z_A := PaintingOrDrawing.regionsIncludingEdge K A
    let N := boundaryDrawing K Z_A
    have hNs : N.IsSubdrawing K := Drawing.span_isSubdrawing K _ _
    -- Every region `r ∈ K.R` meeting `Λ₂` belongs to `Z_A`.
    have hr_in_ZA : ∀ r ∈ K.R, (r ∩ Λ₂).Nonempty → r ∈ Z_A := by
      exact inner_zone_regions_are_on_first_tangle_side (S := S) hS (H := H) (C_in := C_in) (beta
        := beta) (d := d) (z := z) (Λ₂ := Λ₂) hCinH hbd_cl₂ hdiff₂ hZone₂ A he_E₁_of_cl₂ K hK
        hrf
    -- Hence `N.U` is disjoint from `Λ₂`.
    have hdis_NU_Λ₂ : Disjoint N.U Λ₂ := by
      exact first_tangle_side_boundary_avoids_inner_zone (S := S) hS (H := H) (beta := beta) (d :=
        d) (z := z) (Λ₂ := Λ₂) hZone₂ K A hNs hr_in_ZA
    -- Choose a point `y₀ ∈ Λ₂ \ K.U` and its region `r₀ ∈ Z_A`.
    obtain ⟨y₀, hy₀_Λ₂, hy₀_not_KU⟩ :=
      exists_notMem_U hS hZone₂.isOpenDisc.1 (IsOpenDisc.nonempty hZone₂.isOpenDisc)
    let r₀ := connectedComponentIn (univ \ K.U) y₀
    have hr₀R : r₀ ∈ K.R := (mem_R_iff K).mpr ⟨y₀, hy₀_not_KU, rfl⟩
    have hy₀_r₀ : y₀ ∈ r₀ := mem_connectedComponentIn ⟨mem_univ y₀, hy₀_not_KU⟩
    have hr₀_ZA : r₀ ∈ Z_A := hr_in_ZA r₀ hr₀R ⟨y₀, hy₀_r₀, hy₀_Λ₂⟩
    obtain ⟨D, hD, hDsN, hDlen, hr₀_D⟩ := hsm.2 r₀ hr₀_ZA
    have hDsK : D.IsSubdrawing K := hDsN.trans hNs
    obtain ⟨hDdisc, hDbd, -⟩ := hd D hD hDsK hDlen
    have hdis_Λ₂_frD : Disjoint Λ₂ (frontier (ins D)) := by
      rw [← subBd_eq_frontier, hDbd]
      exact (disjoint_of_subset_left hDsN.U_subset hdis_NU_Λ₂).symm
    have hΛ₂_in_D : Λ₂ ⊆ ins D :=
      subset_of_disjoint_frontier hZone₂.isOpenDisc.isPathConnected.isConnected.isPreconnected
        hDdisc.isCompact.isClosed hdis_Λ₂_frD hy₀_Λ₂ (hr₀_D hy₀_r₀)
    have hcl₂_in_D : closure Λ₂ ⊆ ins D :=
      hDdisc.isCompact.isClosed.closure_subset_iff.mpr hΛ₂_in_D
    -- Bound `d z e₀ ≤ (D.V ∩ H.V).ncard ≤ X.ncard < beta`.
    obtain ⟨p_z, hp_z⟩ := atom_nonempty hz
    have hz_D : (z ∩ ins D).Nonempty := ⟨p_z, hp_z, hΛ₂_in_D (hZone₂.z_subset hp_z)⟩
    have he₀A : e₀ ∈ H.A := Or.inl (Or.inr he₀H)
    obtain ⟨p_e, hp_e⟩ := he₀C.1
    have he₀_D : (e₀ ∩ ins D).Nonempty := ⟨p_e, hp_e, hcl₂_in_D (he₀_cl₂ hp_e)⟩
    have hDV_sub_X : D.V ∩ H.V ⊆ X := by
      rintro v ⟨hvD, hvH⟩
      rw [← hinter_AB]
      exact GM11.boundary_vertex hS hrf hsep_AB hvH (hDsN.1 hvD)
    have hcard_le : (D.V ∩ H.V).ncard ≤ X.ncard :=
      ncard_le_ncard hDV_sub_X (H.finite_V.subset hX_sub)
    have hd_le : d z e₀ ≤ X.ncard := by
      rw [hd_eq z hz e₀ he₀A]
      exact (tangleMetric_le_of_circuit hS hK hd hD hDsK hDlen hz he₀A hz_D he₀_D).2.trans hcard_le
    have he₀_sub_Λ₂ : e₀ ⊆ Λ₂ := hsub₂ e₀ he₀A (by omega)
    exact (hdiff₂ ▸ he₀_sub_Λ₂ hp_e).2 (he₀_CU hp_e)

/-! ## 5. Splitting Uncrossed Paths and Proof of (9.5) -/

private theorem no_self_loop_in_simple_walk {α β : Type*} {G : Graph α β} {a b x : α} {f : β}
    (W : GraphWalk G a b) (hnd : W.IsSimple) (hf : f ∈ W.edges) (hlink : G.IsLink f x x) :
    False := by
  induction W with
  | nil _ => simp at hf
  | @cons u w _ e₀ hl₀ r₀ ih =>
    rcases List.mem_cons.mp hf with rfl | hfr₀
    · have huv : u = x := by rcases hl₀.left_eq_or_eq hlink with h | h <;> exact h
      have hwv : w = x := by rcases hl₀.symm.left_eq_or_eq hlink with h | h <;> exact h
      exact (List.nodup_cons.mp hnd).1 ((huv.trans hwv.symm) ▸ r₀.start_mem_support)
    · exact ih (List.nodup_cons.mp hnd).2 hfr₀

/-- If `P` is a path of `H` from `a` to `b ∉ Δ` (where `C` is a circuit of `H` bounding the closed
disc `Δ` with `subBd Δ = C.U` and `Λ = Δ \ C.U`) such that `Drawing.inf H C P` is a path, then
splitting `P` at its first vertex `v ∈ C.V` yields:
- an inner path `P_in` of `H` from `a` to `v` with `P_in.U ∩ (H.U ∩ C.U) = {v}`, and
- an outer path `P_out` of `H` from `v` to `b` with `Disjoint P_out.U Λ`,
both with vertex sets contained in `P.V`. -/
private theorem split_uncrossed_path_at_circuit [T2Space S]
    (hS : IsClosedSurface S) {H C P : Drawing S} {Δ : Set S} {a b : S}
    (hCH : C.IsSubdrawing H) (hΔ : IsClosedDisc Δ) (hbd : subBd Δ = C.U)
    (hPH : P.IsSubdrawing H) (hP : P.IsPathBetween a b) (hb_not_Δ : b ∉ Δ)
    (hinf : IsDrawingPath (Drawing.inf H C P)) :
    ∃ v ∈ C.V, ∃ P_in P_out : Drawing S,
      P_in.IsPathBetween a v ∧ P_in.IsSubdrawing H ∧ P_in.V ⊆ P.V ∧
      P_in.U ∩ (H.U ∩ C.U) = {v} ∧
      P_out.IsPathBetween v b ∧ P_out.IsSubdrawing H ∧ P_out.V ⊆ P.V ∧
      Disjoint P_out.U (Δ \ C.U) := by
  obtain ⟨W₀, hW₀s, hVP, hEP⟩ := hP
  obtain ⟨W, hsW, heW⟩ := hPH.exists_walk_up W₀
  have hWs : W.IsSimple := by change W.support.Nodup; rw [hsW]; exact hW₀s
  have hP_eq : P = walkDrawing H W := by
    apply Drawing.ext_of_V_E
    · rw [hVP, walkDrawing_V, hsW]
    · rw [hEP, walkDrawing_E, heW]
  have hne_W : ∃ x ∈ W.support, x ∈ C.V := by
    obtain ⟨x, _, WI, _, hVI, _⟩ := hinf
    have hxI : x ∈ (Drawing.inf H C P).V := by rw [hVI]; exact WI.start_mem_support
    rw [Drawing.inf_V hCH hPH, hVP, ← hsW] at hxI
    exact ⟨x, hxI.2, hxI.1⟩
  obtain ⟨v, hvC, W_in, W_out, hsplit, hW_in_first⟩ := exists_first_hit_split W hne_W
  have hsp := GM09.isSimple_of_append (hsplit ▸ hWs)
  let P_in := walkDrawing H W_in
  let P_out := walkDrawing H W_out
  have hPin_V : P_in.V ⊆ P.V := by
    intro x hx
    rw [hP_eq, hsplit, walkDrawing_V, mem_ofPred_eq, GraphWalk.mem_support_append]
    rw [walkDrawing_V, mem_ofPred_eq] at hx
    exact Or.inl hx
  have hPout_V : P_out.V ⊆ P.V := by
    intro x hx
    rw [hP_eq, hsplit, walkDrawing_V, mem_ofPred_eq, GraphWalk.mem_support_append]
    rw [walkDrawing_V, mem_ofPred_eq] at hx
    exact Or.inr hx
  have hW_in_no_edge : ∀ f ∈ W_in.edges, f ∉ C.E := by
    intro f hf hfC
    obtain ⟨x, y, hxyH⟩ := (H.toGraph.edge_mem_iff_exists_isLink f).mp (hCH.2 hfC)
    have hxyC : C.toGraph.IsLink f x y := (hCH.isLink_iff hfC).mpr hxyH
    have hx_s : x ∈ W_in.support := W_in.left_mem_support_of_mem_edges hf hxyH
    have hy_s : y ∈ W_in.support := W_in.left_mem_support_of_mem_edges hf hxyH.symm
    have hxv : x = v := hW_in_first x hx_s hxyC.2.1
    have hyv : y = v := hW_in_first y hy_s hxyC.2.2.1
    exact no_self_loop_in_simple_walk W_in hsp.1 hf ((hxv.trans hyv.symm) ▸ hxyH)
  have hdisjE_in : Disjoint P_in.E C.E := by
    rw [walkDrawing_E]
    exact disjoint_left.mpr hW_in_no_edge
  have hPin_inter : P_in.U ∩ (H.U ∩ C.U) = {v} := by
    rw [inter_eq_right.mpr hCH.U_subset,
      U_inter_of_disjoint (walkDrawing_isSubdrawing H W_in) hCH hdisjE_in, walkDrawing_V]
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq, mem_singleton_iff]
    refine ⟨fun ⟨hx₁, hxC⟩ => hW_in_first x hx₁ hxC, ?_⟩
    rintro rfl
    exact ⟨W_in.end_mem_support, hvC⟩
  -- Show `Disjoint P_out.U (Δ \ C.U)` using `walk_subset_disc_or_exists_outer_detour`.
  have hPout_disj : Disjoint P_out.U (Δ \ C.U) := by
    let Λ := Δ \ C.U
    let Δ_ext := univ \ Λ
    have hΛ_eq_int : Λ = interior Δ := by
      change Δ \ C.U = interior Δ
      rw [← hbd, subBd_eq_frontier]
      ext x
      exact ⟨fun ⟨hx, hnf⟩ => by_contra fun hni => hnf ⟨subset_closure hx, hni⟩,
        fun hx => ⟨interior_subset hx, fun hf => hf.2 hx⟩⟩
    have hΛ_open : IsOpen Λ := hΛ_eq_int ▸ isOpen_interior
    have hΔ_ext_closed : IsClosed Δ_ext := isClosed_univ.sdiff hΛ_open
    have hfr_ext : frontier Δ_ext = C.U := by
      change frontier (univ \ (Δ \ C.U)) = C.U
      rw [← compl_eq_univ_sdiff, frontier_compl, ← subBd_eq_frontier, ← hbd]
      exact (IsClosedDisc.isOpenDisc_diff_subBd hS hΔ).2.2
    have hb_ext : b ∈ Δ_ext \ C.U := by
      refine ⟨⟨mem_univ b, fun hbΛ => hb_not_Δ hbΛ.1⟩, fun hbCU => hb_not_Δ ?_⟩
      exact hΔ.isCompact.isClosed.frontier_subset (subBd_eq_frontier Δ ▸ hbd ▸ hbCU)
    rcases walk_subset_disc_or_exists_outer_detour hCH hΔ_ext_closed hfr_ext W_out hsp.2 hvC hb_ext
      with hsub_ext | ⟨u₁, hu₁C, u₂, hu₂C, hu12, W_pre, W_sub, W_post, hout_eq, hVC, hEC, _⟩
    · exact disjoint_left.mpr fun x hxP hxΛ => (hsub_ext hxP).2 hxΛ
    · exfalso
      let W_A := W_in.append W_pre
      let W_B := W_post
      have hW_eq : W = W_A.append (W_sub.append W_B) := by
        rw [hsplit, hout_eq, GraphWalk.append_assoc]
      let P_A := walkDrawing H W_A
      let P_sub := walkDrawing H W_sub
      let P_B := walkDrawing H W_B
      let I := Drawing.inf H C P
      have hsub_CU : P_sub.U ∩ C.U = {u₁, u₂} := by
        rw [U_inter_of_disjoint (walkDrawing_isSubdrawing H W_sub) hCH hEC, hVC]
      have hI_U : I.U = C.U ∩ P.U := Drawing.inf_U hCH hPH
      have hP_U : P.U = P_A.U ∪ (P_sub.U ∪ P_B.U) := by
        rw [hP_eq, hW_eq, walkDrawing_append_U H W_A (W_sub.append W_B),
          walkDrawing_append_U H W_sub W_B]
      have hu₁_PA : u₁ ∈ P_A.U :=
        (walkDrawing H W_A).V_subset_U (by rw [walkDrawing_V]; exact W_A.end_mem_support)
      have hu₂_PB : u₂ ∈ P_B.U :=
        (walkDrawing H W_B).V_subset_U (by rw [walkDrawing_V]; exact W_B.start_mem_support)
      have hI_sub : I.U ⊆ P_A.U ∪ P_B.U := by
        intro x hxI
        rw [hI_U, hP_U] at hxI
        rcases hxI with ⟨hxC, hxA | hx_sub | hxB⟩
        · exact Or.inl hxA
        · have hx12 : x ∈ ({u₁, u₂} : Set S) := hsub_CU ▸ ⟨hx_sub, hxC⟩
          rcases hx12 with rfl | rfl
          · exact Or.inl hu₁_PA
          · exact Or.inr hu₂_PB
        · exact Or.inr hxB
      have hu₁_I : u₁ ∈ I.U := by
        rw [hI_U, hP_U]
        exact ⟨C.V_subset_U hu₁C, Or.inl hu₁_PA⟩
      have hu₂_I : u₂ ∈ I.U := by
        rw [hI_U, hP_U]
        exact ⟨C.V_subset_U hu₂C, Or.inr (Or.inr hu₂_PB)⟩
      obtain ⟨z, _, hzA, hzB⟩ :=
        isPreconnected_closed_iff.mp hinf.isPreconnected_U P_A.U P_B.U P_A.isClosed_U
          P_B.isClosed_U hI_sub ⟨u₁, hu₁_I, hu₁_PA⟩ ⟨u₂, hu₂_I, hu₂_PB⟩
      have hA_inter : P_A.U ∩ (walkDrawing H (W_sub.append W_B)).U = {u₁} :=
        walkDrawing_append_U_inter W_A (W_sub.append W_B) (hW_eq ▸ hWs)
      have hB_inter : (walkDrawing H (W_A.append W_sub)).U ∩ P_B.U = {u₂} :=
        walkDrawing_append_U_inter (W_A.append W_sub) W_B
          (by rw [GraphWalk.append_assoc, ← hW_eq]; exact hWs)
      have hzu₁ : z = u₁ := by
        have hz_in : z ∈ P_A.U ∩ (walkDrawing H (W_sub.append W_B)).U := by
          rw [walkDrawing_append_U H W_sub W_B]
          exact ⟨hzA, Or.inr hzB⟩
        rwa [hA_inter, mem_singleton_iff] at hz_in
      have hzu₂ : z = u₂ := by
        have hz_in : z ∈ (walkDrawing H (W_A.append W_sub)).U ∩ P_B.U := by
          rw [walkDrawing_append_U H W_A W_sub]
          exact ⟨Or.inl hzA, hzB⟩
        rwa [hB_inter, mem_singleton_iff] at hz_in
      exact hu12 (hzu₁.symm.trans hzu₂)
  exact ⟨v, hvC, P_in, P_out,
    walkDrawing_isPathBetween H hsp.1, walkDrawing_isSubdrawing H W_in, hPin_V, hPin_inter,
    walkDrawing_isPathBetween H hsp.2, walkDrawing_isSubdrawing H W_out, hPout_V, hPout_disj⟩

private theorem optimal_circuit_gives_rigid_cleared_zone
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    (H : Drawing S)
    (beta : ℕ)
    (d : Set S → Set S → ℕ)
    (z : Set S)
    (hS : IsClosedSurface S)
    (hRig : IsRigid H)
    (hbeta : 4 ≤ beta)
    [this : ConnectedSpace S]
    (C_in : Drawing S)
    (C_out : Drawing S)
    (Λ₁ : Set S)
    (C₀ : Fin (beta + 1) → Drawing S)
    (hZone₁ : IsLambdaZoneAround H d (3 * beta + 3) z Λ₁)
    (hbd_disc₁ : discBd (closure Λ₁) = C_out.U)
    (h : Fin (beta + 1))
    (hh : h.val = beta / 2 + 1)
    (C : Fin (beta + 1) → Drawing S)
    (P : Fin beta → Drawing S)
    (hC : IsDiscNest H (closure Λ₁) C_in C_out C)
    (hmono : ∀ (j : Fin (beta + 1)), discIns (closure Λ₁) (C₀ j) ⊆ discIns (closure Λ₁) (C j))
    (hP : IsDiscPaths H (closure Λ₁) C_in C_out P)
    (hk_eq : sInf ({k | ∃ C P, IsDiscNest H (closure Λ₁) C_in C_out C ∧ (∀ (j : Fin (beta + 1)),
      discIns (closure Λ₁) (C₀ j) ⊆ discIns (closure Λ₁) (C j)) ∧ IsDiscPaths H (closure Λ₁) C_in
      C_out P ∧ (∀ (j : Fin (beta + 1)) (i : Fin beta), IsDrawingPath (Drawing.inf H (C j) (P i)))
      ∧ k = H.E.ncard - {e | e ∈ H.E ∧ e ⊆ discIns (closure Λ₁) (C h) \ (C h).U}.ncard}) =
      H.E.ncard - {e | e ∈ H.E ∧ e ⊆ discIns (closure Λ₁) (C h) \ (C h).U}.ncard)
    (hp_h : discIns (closure Λ₁) (C h) ⊆ closure Λ₁ ∧ IsClosedDisc (discIns (closure Λ₁) (C h)) ∧
      discBd (discIns (closure Λ₁) (C h)) = (C h).U ∧ frontier (discIns (closure Λ₁) (C h)) = (C
      h).U ∧ IsClosed (discIns (closure Λ₁) (C h)) ∧ (C h).U ⊆ discIns (closure Λ₁) (C h))
    (hbd_Δ_h : subBd (discIns (closure Λ₁) (C h)) = (C h).U)
    (hOD_h' : IsOpenDisc ((discIns (closure Λ₁) (C h)) \ (C h).U))
    (hcl_Λ_h' : closure ((discIns (closure Λ₁) (C h)) \ (C h).U) = (discIns (closure Λ₁) (C h)))
    (hbd_Λ_h' : subBd ((discIns (closure Λ₁) (C h)) \ (C h).U) = (C h).U) :
    IsRigid (clearedSubdrawing H ((discIns (closure Λ₁) (C h)) \ (C h).U)) := by
  let S_cost := {k | ∃ C P, IsDiscNest H (closure Λ₁) C_in C_out C ∧ (∀ (j : Fin (beta + 1)),
    discIns (closure Λ₁) (C₀ j) ⊆ discIns (closure Λ₁) (C j)) ∧ IsDiscPaths H (closure Λ₁) C_in
    C_out P ∧ (∀ (j : Fin (beta + 1)) (i : Fin beta), IsDrawingPath (Drawing.inf H (C j) (P i))) ∧
    k = H.E.ncard - {e | e ∈ H.E ∧ e ⊆ discIns (closure Λ₁) (C h) \ (C h).U}.ncard}
  let Δ_h := discIns (closure Λ₁) (C h)
  let Λ_h := Δ_h \ (C h).U
  by_contra hnot_rig
  let h_next : Fin (beta + 1) := ⟨beta / 2 + 2, by omega⟩
  have hh_lt_next : h < h_next := by
    change h.val < beta / 2 + 2
    omega
  let Δ_next := discIns (closure Λ₁) (C h_next)
  have hp_next := hC.disc_props hS hZone₁.isClosedDisc_closure h_next
  have hbd_Δ_next : subBd Δ_next = (C h_next).U := by
    rw [subBd_eq_frontier, hp_next.2.2.2.1]
  have hcl_h_sub_next : closure Λ_h ⊆ Δ_next \ subBd Δ_next := by
    rw [hcl_Λ_h', hbd_Δ_next]
    exact (hC.discIns_subset_diff hS hZone₁.isClosedDisc_closure hh_lt_next).2
  have hCD_h : IsClosedDisc (closure Λ_h) := hcl_Λ_h' ▸ hp_h.2.1
  have hbd_cl_h : subBd (closure Λ_h) = (C h).U := hcl_Λ_h' ▸ hbd_Δ_h
  have hdiff_h : closure Λ_h \ (C h).U = Λ_h := by rw [hcl_Λ_h']
  obtain ⟨C'_h, Λ'_h, hC'H, hC'circ, _, hOD', hcl'_sub, hCD', hbd', hbd_cl', hdiff',
    hΛ_sub, _, hncard_lt⟩ :=
    enlarge_disc_past_disconnected_region hS hRig hp_next.2.1
      (hbd_Δ_next ▸ (hC.1 h_next).1.U_subset) (hC.1 h).2.1 (hC.1 h).1 hOD_h'
      hCD_h hbd_Λ_h' hbd_cl_h hdiff_h hcl_h_sub_next hnot_rig
  have hcl'_sub_₁ : closure Λ'_h ⊆ closure Λ₁ :=
    (hcl'_sub.trans sdiff_subset).trans hp_next.1
  have hC'_U_sub_cl' : C'_h.U ⊆ closure Λ'_h := by
    rw [← hbd_cl', subBd_eq_frontier]
    exact hCD'.isCompact.isClosed.frontier_subset
  have hC'_U_sub_₁ : C'_h.U ⊆ closure Λ₁ := hC'_U_sub_cl'.trans hcl'_sub_₁
  obtain ⟨_, huniq_C'⟩ := discIns_spec hZone₁.isClosedDisc_closure hC'circ hC'_U_sub_₁
  have hdiscIns_C' : discIns (closure Λ₁) C'_h = closure Λ'_h :=
    (huniq_C' (closure Λ'_h) hcl'_sub_₁ hCD'
      ((IsClosedDisc.subBd_eq_discBd hS hCD').symm.trans hbd_cl')).symm
  let C_new : Fin (beta + 1) → Drawing S := Function.update C h C'_h
  have hC_new_strict : ∀ j₁ j₂ : Fin (beta + 1), j₁ < j₂ →
      discIns (closure Λ₁) (C_new j₁) ⊆ discIns (closure Λ₁) (C_new j₂) \ (C_new j₂).U := by
    intro j₁ j₂ hj12
    by_cases hj₁h : j₁ = h
    · subst j₁
      have hj₂_ne_h : j₂ ≠ h := hj12.ne'
      simp only [C_new, Function.update_self, Function.update_of_ne hj₂_ne_h, hdiscIns_C']
      have hnext_le_j₂ : h_next ≤ j₂ := by
        change beta / 2 + 2 ≤ j₂.val
        change h.val < j₂.val at hj12
        omega
      rcases eq_or_lt_of_le hnext_le_j₂ with rfl | hlt_j₂
      · rwa [← hbd_Δ_next]
      · exact (hcl'_sub.trans sdiff_subset).trans
          (hC.discIns_subset_diff hS hZone₁.isClosedDisc_closure hlt_j₂).2
    · by_cases hj₂h : j₂ = h
      · subst j₂
        simp only [C_new, Function.update_self, Function.update_of_ne hj₁h, hdiscIns_C', hdiff']
        exact (hC.discIns_subset_diff hS hZone₁.isClosedDisc_closure hj12).2.trans hΛ_sub
      · simp only [C_new, Function.update_of_ne hj₁h, Function.update_of_ne hj₂h]
        exact (hC.discIns_subset_diff hS hZone₁.isClosedDisc_closure hj12).2
  have hC_new_U_sub : ∀ j : Fin (beta + 1), (C_new j).U ⊆ discIns (closure Λ₁) (C_new j) := by
    intro j
    by_cases hjh : j = h
    · subst j
      simp only [C_new, Function.update_self, hdiscIns_C']
      exact hC'_U_sub_cl'
    · simp only [C_new, Function.update_of_ne hjh]
      exact (hC.disc_props hS hZone₁.isClosedDisc_closure j).2.2.2.2.2
  have hC_new_nest : IsDiscNest H (closure Λ₁) C_in C_out C_new := by
    refine ⟨fun j => ?_, fun j₁ j₂ hj12 => ?_, fun j₁ j₂ hj12 => ?_, fun hs => ⟨?_, ?_⟩⟩
    · by_cases hjh : j = h
      · subst j
        simp only [C_new, Function.update_self]
        exact ⟨hC'H, hC'circ, hC'_U_sub_₁⟩
      · simp only [C_new, Function.update_of_ne hjh]
        exact hC.1 j
    · have key : ∀ a b : Fin (beta + 1), a < b → Disjoint (C_new a).V (C_new b).V := by
        intro a b hab
        refine disjoint_of_subset (C_new a).V_subset_U (C_new b).V_subset_U ?_
        refine disjoint_left.mpr fun x hxa hxb => ?_
        exact (hC_new_strict a b hab (hC_new_U_sub a hxa)).2 hxb
      rcases lt_or_gt_of_ne hj12 with hlt | hgt
      · exact key j₁ j₂ hlt
      · exact (key j₂ j₁ hgt).symm
    · rcases eq_or_lt_of_le hj12 with rfl | hlt
      · exact Subset.rfl
      · exact (hC_new_strict j₁ j₂ hlt).trans sdiff_subset
    · have h0_ne : (⟨0, hs⟩ : Fin (beta + 1)) ≠ h := by
        intro heq
        have : 0 = h.val := congrArg Fin.val heq
        omega
      simp only [C_new, Function.update_of_ne h0_ne]
      exact (hC.2.2.2 hs).1
    · have hlast_ne : (⟨beta + 1 - 1, Nat.sub_lt hs zero_lt_one⟩ : Fin (beta + 1)) ≠ h := by
        intro heq
        have : beta + 1 - 1 = h.val := congrArg Fin.val heq
        omega
      simp only [C_new, Function.update_of_ne hlast_ne]
      exact (hC.2.2.2 hs).2
  have hmono_new : ∀ j : Fin (beta + 1),
      discIns (closure Λ₁) (C₀ j) ⊆ discIns (closure Λ₁) (C_new j) := by
    intro j
    by_cases hjh : j = h
    · subst j
      simp only [C_new, Function.update_self, hdiscIns_C']
      refine (hmono h).trans ?_
      have hs : closure (discIns (closure Λ₁) (C h) \ (C h).U) ⊆ closure Λ'_h :=
        closure_mono hΛ_sub
      rw [hcl_Λ_h'] at hs
      exact hs
    · simp only [C_new, Function.update_of_ne hjh]
      exact hmono j
  obtain ⟨C'', P'', hC'', hmono'', hP'', hinf''⟩ :=
    planar_nest_uncrossing_mono hS hZone₁.isClosedDisc_closure hbd_disc₁ C_new hC_new_nest ⟨P, hP⟩
  have hcl'_sub_C'' : closure Λ'_h ⊆ discIns (closure Λ₁) (C'' h) := by
    have := hmono'' h
    simpa [C_new, hdiscIns_C'] using this
  have hp''_h := hC''.disc_props hS hZone₁.isClosedDisc_closure h
  have hint_C'' : interior (discIns (closure Λ₁) (C'' h)) =
      discIns (closure Λ₁) (C'' h) \ (C'' h).U := by
    rw [← hp''_h.2.2.2.1]
    ext x
    exact ⟨fun hx => ⟨interior_subset hx, fun hf => hf.2 hx⟩,
      fun ⟨hx, hnf⟩ => by_contra fun hni => hnf ⟨subset_closure hx, hni⟩⟩
  have hΛ'_sub_C'' : Λ'_h ⊆ discIns (closure Λ₁) (C'' h) \ (C'' h).U := by
    rw [← hint_C'', ← hOD'.1.interior_eq]
    exact interior_mono (subset_closure.trans hcl'_sub_C'')
  let E_old := {e ∈ H.E | e ⊆ Λ_h}
  let E_new := {e ∈ H.E | e ⊆ discIns (closure Λ₁) (C'' h) \ (C'' h).U}
  have hcard_lt : E_old.ncard < E_new.ncard :=
    lt_of_lt_of_le hncard_lt (ncard_le_ncard
      (fun e ⟨heH, he_sub⟩ => ⟨heH, he_sub.trans hΛ'_sub_C''⟩)
      (H.finite_edges.subset fun _ h => h.1))
  have hnew_le_H : E_new.ncard ≤ H.E.ncard :=
    ncard_le_ncard (fun _ h => h.1) H.finite_edges
  have hmem_new : H.E.ncard - E_new.ncard ∈ S_cost :=
    ⟨C'', P'', hC'', fun j => (hmono_new j).trans (hmono'' j), hP'', hinf'', rfl⟩
  have hle_sInf : sInf S_cost ≤ H.E.ncard - E_new.ncard := Nat.sInf_le hmem_new
  change sInf S_cost = H.E.ncard - E_old.ncard at hk_eq
  omega

/-- **Graph Minors XIV, (9.5)** (pages 45–47), proving `GM16.GM14Theorem95Statement`:
"Let $H$ be a 2-cell, rigid drawing in $\Sigma$, let $z \in A(H)$, and let $\mathscr{T}$ be a
respectful tangle in $H$ of order $\theta$. Let $\beta \ge 4$ be an even integer with
$\theta \ge 16\beta + 17$. Then there is a battlefield around $z$ of size $\beta$." -/
theorem theorem_9_5_proof :
    GM16.GM14Theorem95Statement.{w} := by
  intro S _ _ H θ beta T d z hS hConn hRig hMetric hz hbeta heven hθ
  have : ConnectedSpace S := hConn
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  -- Step 1: Claim (1) gives `C_in`, `C_out`, `Λ₁`, `Λ₂`, and the initial nest `C₀`.
  obtain ⟨C_in, C_out, Λ₁, Λ₂, C₀, hCinH, hCin, hbd₂, hbd_cl₂, hdiff₂, hZone₂, hsub₂,
    hCoutH, hCout, hbd₁, hbd_cl₁, hdiff₁, hZone₁, hsub₁, hcl₂_sub_Λ₁, hC₀_nest, hdiscIns_0⟩ :=
    lemma_9_5_claim_1 hS hConn hMetric hz hbeta hθ
  -- Step 2: Claim (2) gives `beta` disjoint paths `P₀` between `C_in.V` and `C_out.V` in `closure
  -- Λ₁`.
  obtain ⟨P₀, hP₀⟩ :=
    lemma_9_5_claim_2 hS hConn hMetric hz hbeta hθ hCinH hCin hbd_cl₂ hdiff₂ hZone₂ hsub₂
      hCoutH hCout hbd_cl₁ hdiff₁ hZone₁ hcl₂_sub_Λ₁
  -- Step 3: Claim (3) and choosing `(C, P)` maximizing `Δ_h` (`h = beta / 2 + 1` in 0-indexed `Fin
  -- (beta + 1)`).
  have hbd_disc₁ : discBd (closure Λ₁) = C_out.U := by
    rw [← IsClosedDisc.subBd_eq_discBd hS hZone₁.isClosedDisc_closure, hbd_cl₁]
  let h : Fin (beta + 1) := ⟨beta / 2 + 1, by omega⟩
  let S_cost : Set ℕ := {k : ℕ | ∃ (C : Fin (beta + 1) → Drawing S) (P : Fin beta → Drawing S),
    IsDiscNest H (closure Λ₁) C_in C_out C ∧
    (∀ j : Fin (beta + 1), discIns (closure Λ₁) (C₀ j) ⊆ discIns (closure Λ₁) (C j)) ∧
    IsDiscPaths H (closure Λ₁) C_in C_out P ∧
    (∀ (j : Fin (beta + 1)) (i : Fin beta), IsDrawingPath (Drawing.inf H (C j) (P i))) ∧
    k = H.E.ncard - {e ∈ H.E | e ⊆ discIns (closure Λ₁) (C h) \ (C h).U}.ncard}
  have hScost_ne : S_cost.Nonempty := by
    obtain ⟨C, P, hC, hmono, hP, hinf⟩ :=
      planar_nest_uncrossing_mono hS hZone₁.isClosedDisc_closure hbd_disc₁ C₀ hC₀_nest ⟨P₀, hP₀⟩
    exact ⟨_, C, P, hC, hmono, hP, hinf, rfl⟩
  obtain ⟨C, P, hC, hmono, hP, hinf, hk_eq⟩ := Nat.sInf_mem hScost_ne
  let Δ_h := discIns (closure Λ₁) (C h)
  let Λ_h := Δ_h \ (C h).U
  have hp_h := hC.disc_props hS hZone₁.isClosedDisc_closure h
  have hbd_Δ_h : subBd Δ_h = (C h).U := by
    rw [subBd_eq_frontier, hp_h.2.2.2.1]
  obtain ⟨hOD_h, hcl_Λ_h, hbd_Λ_h⟩ := IsClosedDisc.isOpenDisc_diff_subBd hS hp_h.2.1
  have hOD_h' : IsOpenDisc Λ_h := by
    change IsOpenDisc (Δ_h \ (C h).U)
    rwa [← hbd_Δ_h]
  have hcl_Λ_h' : closure Λ_h = Δ_h := by
    change closure (Δ_h \ (C h).U) = Δ_h
    rwa [← hbd_Δ_h]
  have hbd_Λ_h' : subBd Λ_h = (C h).U := by
    change subBd (Δ_h \ (C h).U) = (C h).U
    rw [← hbd_Δ_h, hbd_Λ_h, hbd_Δ_h]
  -- Step 4: Claim (4) (`IsRigid (clearedSubdrawing H Λ_h)`).
  have hRig_h : IsRigid (clearedSubdrawing H Λ_h) := by
    exact optimal_circuit_gives_rigid_cleared_zone (S := S) H beta d z hS hRig hbeta C_in C_out
      Λ₁ C₀ hZone₁ hbd_disc₁ h rfl C P hC hmono hP hk_eq hp_h hbd_Δ_h hOD_h' hcl_Λ_h' hbd_Λ_h'
  -- Step 5: Assemble the battlefield `(Λ_h, C 0, range v)`.
  have h0_pos : 0 < beta + 1 := Nat.succ_pos beta
  let i₀ : Fin (beta + 1) := ⟨0, h0_pos⟩
  let i_last : Fin (beta + 1) := ⟨beta, Nat.lt_succ_self beta⟩
  have hC0_eq : C i₀ = C_in := (hC.2.2.2 h0_pos).1
  have hClast_eq : C i_last = C_out := (hC.2.2.2 h0_pos).2
  let Δ₀ := discIns (closure Λ₁) (C i₀)
  let Λ₀ := Δ₀ \ (C i₀).U
  have hp_0 := hC.disc_props hS hZone₁.isClosedDisc_closure i₀
  have hbd_Δ₀ : subBd Δ₀ = (C i₀).U := by rw [subBd_eq_frontier, hp_0.2.2.2.1]
  obtain ⟨hOD_0, _, hbd_Λ₀⟩ := IsClosedDisc.isOpenDisc_diff_subBd hS hp_0.2.1
  have hbd_Λ₀' : subBd Λ₀ = (C i₀).U := by
    change subBd (Δ₀ \ (C i₀).U) = (C i₀).U
    rw [← hbd_Δ₀, hbd_Λ₀, hbd_Δ₀]
  have hcl₂_sub_Δ₀ : closure Λ₂ ⊆ Δ₀ := hdiscIns_0 ▸ hmono i₀
  have hΛ₂_sub_Λ₀ : Λ₂ ⊆ Λ₀ := by
    have hint_0 : interior Δ₀ = Λ₀ := by
      change interior Δ₀ = Δ₀ \ (C i₀).U
      rw [← hp_0.2.2.2.1]
      ext x
      exact ⟨fun hx => ⟨interior_subset hx, fun hf => hf.2 hx⟩,
        fun ⟨hx, hnf⟩ => by_contra fun hni => hnf ⟨subset_closure hx, hni⟩⟩
    rw [← hint_0, ← hZone₂.isOpenDisc.1.interior_eq]
    exact interior_mono (subset_closure.trans hcl₂_sub_Δ₀)
  have hi₀_lt_h : i₀ < h := by change 0 < beta / 2 + 1; omega
  have hΔ₀_sub_Λ_h : Δ₀ ⊆ Λ_h :=
    (hC.discIns_subset_diff hS hZone₁.isClosedDisc_closure hi₀_lt_h).2
  have hC0U_sub_Λ_h : (C i₀).U ⊆ Λ_h := hp_0.2.2.2.2.2.trans hΔ₀_sub_Λ_h
  have hΛ₀_sub_Λ_h : Λ₀ ⊆ Λ_h := sdiff_subset.trans hΔ₀_sub_Λ_h
  have hz_sub_Λ_h : z ⊆ Λ_h := hZone₂.z_subset.trans (hΛ₂_sub_Λ₀.trans hΛ₀_sub_Λ_h)
  have hh_lt_last : h < i_last := by
    obtain ⟨m, rfl⟩ := heven
    change (m + m) / 2 + 1 < m + m
    omega
  have hΔ_h_sub_Λ₁ : Δ_h ⊆ Λ₁ := by
    have hsub := (hC.discIns_subset_diff hS hZone₁.isClosedDisc_closure hh_lt_last).2
    have hlast_eq : discIns (closure Λ₁) (C i_last) = closure Λ₁ := by
      rw [hClast_eq]
      obtain ⟨_, huniq⟩ := discIns_spec hZone₁.isClosedDisc_closure hCout
        (hbd_cl₁ ▸ subBd_eq_frontier (closure Λ₁) ▸
          hZone₁.isClosedDisc_closure.isCompact.isClosed.frontier_subset)
      exact (huniq (closure Λ₁) Subset.rfl hZone₁.isClosedDisc_closure hbd_disc₁).symm
    rwa [hlast_eq, hClast_eq, hdiff₁] at hsub
  have hZone_h : IsLambdaZoneAround H d (3 * beta + 3) z Λ_h :=
    ⟨hZone₁.z_mem, hOD_h', hz_sub_Λ_h, hbd_Λ_h' ▸ isOArc_of_isCircuit (hC.1 h).2.1,
      hcl_Λ_h' ▸ hp_h.2.1, hbd_Λ_h' ▸ (hC.1 h).1.U_subset,
      fun x hx hsub => hZone₁.dist_le x hx ((hcl_Λ_h' ▸ hsub).trans hp_h.1),
      hZone₁.two_le_of_edge⟩
  -- Split each path `P k` at `(C h).V`.
  have hex_split : ∀ k : Fin beta, ∃ a_k ∈ (C i₀).V, ∃ v_k ∈ (C h).V, ∃ b_k ∈ C_out.V,
      ∃ P_in P_out : Drawing S,
        P_in.IsPathBetween a_k v_k ∧ P_in.IsSubdrawing H ∧ P_in.V ⊆ (P k).V ∧
        P_in.U ∩ (H.U ∩ subBd Λ_h) = {v_k} ∧
        P_out.IsPathBetween v_k b_k ∧ P_out.IsSubdrawing H ∧ P_out.V ⊆ (P k).V ∧
        Disjoint P_out.U Λ_h := by
    intro k
    obtain ⟨hPkH, _, a_k, ha_k, b_k, hb_k, hPk_path⟩ := hP.1 k
    have ha_k' : a_k ∈ (C i₀).V := hC0_eq.symm ▸ ha_k
    have hb_k_not_Δ_h : b_k ∉ Δ_h := by
      intro hb_in
      have hb_Λ₁ : b_k ∈ Λ₁ := hΔ_h_sub_Λ₁ hb_in
      exact (hdiff₁ ▸ hb_Λ₁).2 (C_out.V_subset_U hb_k)
    obtain ⟨v_k, hv_kC, P_in, P_out, hPin_p, hPin_H, hPin_V, hPin_inter,
      hPout_p, hPout_H, hPout_V, hPout_disj⟩ :=
      split_uncrossed_path_at_circuit hS (hC.1 h).1 hp_h.2.1 hbd_Δ_h hPkH hPk_path
        hb_k_not_Δ_h (hinf h k)
    rw [← hbd_Λ_h'] at hPin_inter
    exact ⟨a_k, ha_k', v_k, hv_kC, b_k, hb_k, P_in, P_out,
      hPin_p, hPin_H, hPin_V, hPin_inter, hPout_p, hPout_H, hPout_V, hPout_disj⟩
  choose a_v ha_v v_v hv_v b_v hb_v P_in P_out hPin_p hPin_H hPin_V hPin_inter
    hPout_p hPout_H hPout_V hPout_disj using hex_split
  -- Obtain cleared tangle `(T', d')` on `clearedSubdrawing H Λ_h` by `(3.2)` (`theorem_3_2_proof`).
  obtain ⟨T', d', hCleared, _⟩ :=
    theorem_3_2_proof hS hConn (by omega) hMetric hZone_h
  -- Apply `(7.8)` (`theorem_7_8_proof`) to prove `IsFreeSet ... (range v_v)`.
  have hFree_X : IsFreeSet (clearedSubdrawing H Λ_h).toHypergraph T'
      (θ - 4 * (3 * beta + 3) - 2) (range v_v) := by
    let idx_78 : Fin (beta / 2) → Fin (beta + 1) := fun i =>
      ⟨beta / 2 + 1 + i.1, by obtain ⟨m, rfl⟩ := heven; have := i.2; omega⟩
    let C_78 : Fin (beta / 2) → Drawing S := fun i => C (idx_78 i)
    let Δ_78 : Fin (beta / 2) → Set S := fun i => discIns (closure Λ₁) (C_78 i)
    have hv_C : ∀ i : Fin (beta / 2),
        (C_78 i).IsCircuit ∧ (C_78 i).IsSubdrawing H ∧ IsClosedDisc (Δ_78 i) ∧
        subBd (Δ_78 i) = (C_78 i).U ∧ Δ_h ⊆ Δ_78 i ∧ Δ_78 i ⊆ closure Λ₁ := by
      intro i
      have hp_i := hC.disc_props hS hZone₁.isClosedDisc_closure (idx_78 i)
      have hh_le_i : h ≤ idx_78 i := by change beta / 2 + 1 ≤ beta / 2 + 1 + i.1; omega
      exact ⟨(hC.1 (idx_78 i)).2.1, (hC.1 (idx_78 i)).1, hp_i.2.1,
        by rw [subBd_eq_frontier, hp_i.2.2.2.1], hC.2.2.1 hh_le_i, hp_i.1⟩
    have hv_dis : Pairwise (fun i₁ i₂ : Fin (beta / 2) => Disjoint (C_78 i₁).V (C_78 i₂).V) := by
      intro i₁ i₂ hne
      have hne' : idx_78 i₁ ≠ idx_78 i₂ := fun heq => hne (Fin.ext (by
        have := congrArg Fin.val heq; dsimp [idx_78] at this; omega))
      exact hC.2.1 hne'
    have hZone₁_mono : IsLambdaZoneAround H d (θ - beta - 4 * (3 * beta + 3) - 2) z
        (closure Λ₁ \ subBd (closure Λ₁)) := by
      rw [hbd_cl₁, hdiff₁]
      obtain ⟨hz_m, hOD₁, hz_s, hOA₁, hCD₁, hbd_s₁, hdist₁, _⟩ := hZone₁
      exact ⟨hz_m, hOD₁, hz_s, hOA₁, hCD₁, hbd_s₁,
        fun x hx hsub => (hdist₁ x hx hsub).trans (by omega),
        fun _ => by omega⟩
    have hCleared' : IsClearedTangle H T d θ (3 * beta + 3) (Δ_h \ subBd Δ_h) T' d' := by
      rwa [hbd_Δ_h]
    have hZone_h' : IsLambdaZoneAround H d (3 * beta + 3) z (Δ_h \ subBd Δ_h) := by
      rwa [hbd_Δ_h]
    have hFree := theorem_7_8_proof hS hConn hbeta heven (by omega) hMetric hCleared'
      hCout hCoutH hZone₁.isClosedDisc_closure hbd_cl₁
      (hC.1 h).2.1 (hC.1 h).1 hp_h.2.1 hbd_Δ_h
      ⟨by rwa [hbd_Δ_h], by rw [hbd_cl₁, hdiff₁]; exact hΔ_h_sub_Λ₁⟩
      hZone₁_mono hZone_h'
      (fun x hx hlt => by rw [hbd_cl₁, hdiff₁]; exact hsub₁ x hx (by omega))
      hv_C hv_dis
      (fun k => ⟨hPout_p k, hPout_H k, hv_v k, hb_v k, by rw [hbd_Δ_h]; exact hPout_disj k⟩)
      (fun k₁ k₂ hne => disjoint_of_subset (hPout_V k₁) (hPout_V k₂) (hP.2 hne))
    rwa [hbd_Δ_h] at hFree
  -- Regional distance bound `(iv)`.
  have hdist_iv : 1 + beta / 2 ≤ regionalDistance H (C i₀).U (subBd Λ_h) := by
    rw [hbd_Λ_h']
    have hle := nest_regionalDistance_ge hS h0_pos hZone₁.isClosedDisc_closure hC h
    change beta / 2 + 1 ≤ regionalDistance H (C i₀).U (C h).U at hle
    omega
  have hOD_0' : IsOpenDisc Λ₀ := by
    change IsOpenDisc (Δ₀ \ (C i₀).U)
    rwa [← hbd_Δ₀]
  refine ⟨Λ_h, C i₀, range v_v, ?_⟩
  refine ⟨⟨hbeta, heven, by omega, hz⟩, hZone_h, hRig_h, ⟨?_, T', d', hCleared, hFree_X⟩,
    ⟨(hC.1 i₀).2.1, (hC.1 i₀).1, hC0U_sub_Λ_h, P_in,
      fun k => ⟨a_v k, ha_v k, v_v k, mem_range_self k, hPin_p k, hPin_H k, hPin_inter k⟩,
      fun k₁ k₂ hne => disjoint_of_subset (hPin_V k₁) (hPin_V k₂) (hP.2 hne)⟩,
    hdist_iv,
    ⟨Λ₀, hOD_0', hΛ₀_sub_Λ_h, hbd_Λ₀', fun x hx hlt => (hsub₂ x hx hlt).trans hΛ₂_sub_Λ₀⟩⟩
  rintro x ⟨k, rfl⟩
  rw [hbd_Λ_h']
  exact ⟨(hC.1 h).1.1 (hv_v k), (C h).V_subset_U (hv_v k)⟩

end GraphMinor.GM14
