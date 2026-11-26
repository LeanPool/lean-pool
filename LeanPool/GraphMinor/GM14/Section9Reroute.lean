/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Section9a
public import LeanPool.GraphMinor.GM14.Section9b
public import LeanPool.GraphMinor.GM14.Form84
import LeanPool.GraphMinor.GM14.BridgeFacts
import LeanPool.GraphMinor.GM14.Section5
import LeanPool.GraphMinor.GM14.Section6b
import LeanPool.GraphMinor.GM14.Section8
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM11.RadialBasics
import LeanPool.GraphMinor.GM14.DiscArrangement

/-!
# Graph Minors XIV, Section 9: Cylinder Rerouting Lemmas for (9.6)

This file proves the cylinder rerouting steps used in the proof of Graph Minors XIV, (9.6)
(pages 48–49) of N. Robertson and P. D. Seymour, *Graph Minors. XIV. Extending an embedding*,
J. Combin. Theory Ser. B **65** (1995) 23–50:

- `isRigidIn_cylinder_9_6`: by (6.1) (`theorem_6_1`), `H' = H.interSet (Δ \ discInt Δ₂)` is a
  rigid drawing in the closed cylinder `Δ \ discInt Δ₂`.
- `circuits_cylinder_9_6`: `C₁ = H'.interSet (subBd Λ)` and `C₂` are circuit subdrawings of `H'`
  bounding `E₁ = closure Λ` and `E₂ = closure Λ_C₂`.
- `regionalDistance_cylinder_9_6`: the regional distance `regionalDistance H' C₂.U C₁.U` in `H'`
  is at least `π + 4`.
-/

@[expose] public section

namespace GraphMinor.GM14

open Set Function Topology Graph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10
  GraphMinor.GM11 Hypergraph

universe u v w

variable {S : Type w} [TopologicalSpace S]

/-! ## 1. Boundary Normality and Rigidity of `H' = H.interSet (Δ \ discInt Δ₂)` -/

/-- If `subBd D` is `α`-normal for a 3-segregation `S_seg` of `G'` compatible with `H`, then
`subBd D ∩ H.U ⊆ H.V`. -/
theorem subBd_inter_U_subset_V_of_normal {α : Type u} {β : Type v}
    {G' : Graph α β} {H : Drawing S} {η' : SpanEmbedding H G'}
    {S_seg : Set (Society α β)} {α_disc : Society α β → Set S} {α_pt : α → S}
    {D : Set S}
    (hSeg : IsThreeSegregation G' S_seg)
    (hArr : IsSurfaceArrangement S_seg α_disc α_pt)
    (hComp : IsCompatibleWith G' H η' S_seg α_disc α_pt)
    (hNorm : IsArrangementNormal S_seg α_disc α_pt (subBd D)) :
    subBd D ∩ H.U ⊆ H.V := by
  rintro x ⟨hxbd, hxU⟩
  by_contra hxnotV
  obtain ⟨e, he, hxe⟩ := H.exists_edge_of_mem hxU hxnotV
  have he_G' : η'.eMap e ∈ E(G') := η'.imageGraph_le.edgeSet_mono (η'.bijOn_e.mapsTo he)
  have he_union : η'.eMap e ∈ E(subgraphSUnion G' ((fun S₁ : Society α β => S₁.G) '' S_seg)) :=
    hSeg.1.union_eq.symm ▸ he_G'
  simp only [subgraphSUnion, edgeSet_restrict, mem_inter_iff, mem_iUnion, mem_image,
    exists_prop] at he_union
  obtain ⟨_, ⟨S₀, hS₀, rfl⟩, he_S₀⟩ := he_union.2
  have he_disc : e ⊆ α_disc S₀ := (hComp.inter_E_iff S₀ hS₀ e he).mpr he_S₀
  obtain ⟨y, hy_bar, rfl⟩ := hNorm S₀ hS₀ ⟨hxbd, he_disc hxe⟩
  have hx_bd_S₀ : α_pt y ∈ H.U ∩ subBd (α_disc S₀) :=
    ⟨hxU, (hArr.isClosedDisc S₀ hS₀).2 y hy_bar⟩
  rw [hComp.bd_inter_eq S₀ hS₀] at hx_bd_S₀
  exact hxnotV hx_bd_S₀.1

private theorem frontier_sdiff_subset (A B : Set S) :
    frontier (A \ B) ⊆ frontier A ∪ frontier B := by
  have h1 : A \ B = A ∩ Bᶜ := rfl
  rw [h1]
  refine (frontier_inter_subset A Bᶜ).trans ?_
  rintro x (⟨hx1, _⟩ | ⟨_, hx2⟩)
  · exact Or.inl hx1
  · rw [frontier_compl] at hx2
    exact Or.inr hx2

/-- For closed discs `Δ₂ ⊆ Δ \ subBd Δ` on a closed surface `S`, the cylinder `Δ \ discInt Δ₂` is
closed, `subBd (Δ \ discInt Δ₂) = subBd Δ ∪ subBd Δ₂`, and `Disjoint (subBd Δ) (subBd Δ₂)`. -/
theorem cylinder_closed_and_subBd [T2Space S] (hS : IsClosedSurface S)
    {Δ Δ₂ : Set S} (hΔ : IsClosedDisc Δ) (hΔ₂ : IsClosedDisc Δ₂)
    (hΔ₂_sub : Δ₂ ⊆ Δ \ subBd Δ) :
    IsClosed (Δ \ discInt Δ₂) ∧
    subBd (Δ \ discInt Δ₂) = subBd Δ ∪ subBd Δ₂ ∧
    Disjoint (subBd Δ) (subBd Δ₂) := by
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  have hcl_Cyl : IsClosed (Δ \ discInt Δ₂) :=
    hΔ.isClosed.sdiff (hΔ₂.isOpen_discInt hman)
  have hbd_Δ : subBd Δ = discBd Δ := IsClosedDisc.subBd_eq_discBd hS hΔ
  have hbd_Δ₂ : subBd Δ₂ = discBd Δ₂ := IsClosedDisc.subBd_eq_discBd hS hΔ₂
  have hbd₂_sub : subBd Δ₂ ⊆ Δ₂ := fun x hx => Surface.discBd_subset Δ₂ (hbd_Δ₂ ▸ hx)
  have hdisj_bd : Disjoint (subBd Δ) (subBd Δ₂) :=
    disjoint_left.mpr fun x hxΔ hxΔ₂ => (hΔ₂_sub (hbd₂_sub hxΔ₂)).2 hxΔ
  obtain ⟨hOD₂, hcl_int₂, hbd_int₂⟩ := IsClosedDisc.isOpenDisc_diff_subBd hS hΔ₂
  have hdiscInt_eq : discInt Δ₂ = Δ₂ \ subBd Δ₂ := by
    rw [discInt, hbd_Δ₂]
  have hfr_int₂ : frontier (discInt Δ₂) = subBd Δ₂ := by
    rw [hdiscInt_eq, ← subBd_eq_frontier, hbd_int₂]
  have hsubBd_eq : subBd (Δ \ discInt Δ₂) = subBd Δ ∪ subBd Δ₂ := by
    rw [subBd_eq_frontier, subBd_eq_frontier Δ]
    apply Subset.antisymm
    · intro x hx
      have hx_diff := frontier_sdiff_subset Δ (discInt Δ₂) hx
      rw [hfr_int₂] at hx_diff
      exact hx_diff
    · rintro x (hxΔ | hxΔ₂)
      · have hx_in_Δ : x ∈ Δ := hΔ.isClosed.closure_eq ▸ hxΔ.1
        have hx_not_Δ₂ : x ∉ Δ₂ := fun h => (hΔ₂_sub h).2 ((subBd_eq_frontier Δ).symm ▸ hxΔ)
        have hx_in_Cyl : x ∈ Δ \ discInt Δ₂ := ⟨hx_in_Δ, fun h => hx_not_Δ₂ h.1⟩
        refine ⟨subset_closure hx_in_Cyl, fun hx_int => ?_⟩
        exact hxΔ.2 (interior_mono sdiff_subset hx_int)
      · have hx_in_Δ₂ : x ∈ Δ₂ := hbd₂_sub hxΔ₂
        have hx_in_Cyl : x ∈ Δ \ discInt Δ₂ :=
          ⟨(hΔ₂_sub hx_in_Δ₂).1, fun h => h.2 (hbd_Δ₂ ▸ hxΔ₂)⟩
        refine ⟨subset_closure hx_in_Cyl, fun hx_int => ?_⟩
        have hx_cl_int₂ : x ∈ closure (discInt Δ₂) := by
          rw [hdiscInt_eq, hcl_int₂]
          exact hx_in_Δ₂
        obtain ⟨y, hy_int, hy_int₂⟩ :=
          mem_closure_iff.mp hx_cl_int₂ (interior (Δ \ discInt Δ₂)) isOpen_interior hx_int
        exact (interior_subset hy_int).2 hy_int₂
  exact ⟨hcl_Cyl, hsubBd_eq, hdisj_bd⟩

/-- By (6.1) (`theorem_6_1_proof`), `H' = H.interSet (Δ \ discInt Δ₂)` is a rigid drawing in the
closed
cylinder `Δ \ discInt Δ₂` when `H ∩ closure (univ \ Δ)` has a circuit `C_out` and `H` has a circuit
`C` with `C.U ⊆ Δ₂`. -/
theorem isRigidIn_cylinder_9_6 [T2Space S] [ConnectedSpace S] {α : Type u} {β : Type v}
    (hS : IsClosedSurface S)
    {G' : Graph α β} {H C C_out : Drawing S} {η' : SpanEmbedding H G'}
    {S_seg : Set (Society α β)} {α_disc : Society α β → Set S} {α_pt : α → S}
    {Δ Δ₂ : Set S}
    (hRig : IsRigid H)
    (hSeg : IsThreeSegregation G' S_seg)
    (hArr : IsSurfaceArrangement S_seg α_disc α_pt)
    (hComp : IsCompatibleWith G' H η' S_seg α_disc α_pt)
    (hΔ : IsClosedDisc Δ) (hΔ₂ : IsClosedDisc Δ₂)
    (hΔ₂_sub : Δ₂ ⊆ Δ \ subBd Δ)
    (hNorm_Δ : IsArrangementNormal S_seg α_disc α_pt (subBd Δ))
    (hNorm_Δ₂ : IsArrangementNormal S_seg α_disc α_pt (subBd Δ₂))
    (hCout_cir : C_out.IsCircuit)
    (hCout_sub : C_out.IsSubdrawing (H.interSet (closure (univ \ Δ))))
    (hC_cir : C.IsCircuit) (hC_sub : C.IsSubdrawing H) (hCU_sub : C.U ⊆ Δ₂) :
    IsRigidIn (H.interSet (Δ \ discInt Δ₂)) (Δ \ discInt Δ₂) := by
  let Cyl := Δ \ discInt Δ₂
  obtain ⟨hcl_Cyl, hbd_Cyl, hdisj_bd⟩ := cylinder_closed_and_subBd hS hΔ hΔ₂ hΔ₂_sub
  have hbd_Δ_HV : subBd Δ ∩ H.U ⊆ H.V :=
    subBd_inter_U_subset_V_of_normal hSeg hArr hComp hNorm_Δ
  have hbd_Δ₂_HV : subBd Δ₂ ∩ H.U ⊆ H.V :=
    subBd_inter_U_subset_V_of_normal hSeg hArr hComp hNorm_Δ₂
  have hbd_Cyl_HV : subBd Cyl ∩ H.U ⊆ H.V := by
    rw [hbd_Cyl, union_inter_distrib_right]
    exact union_subset hbd_Δ_HV hbd_Δ₂_HV
  have hbd_Δ_eq : subBd Δ = discBd Δ := IsClosedDisc.subBd_eq_discBd hS hΔ
  have hbd_Δ₂_eq : subBd Δ₂ = discBd Δ₂ := IsClosedDisc.subBd_eq_discBd hS hΔ₂
  obtain ⟨hOD₂, hcl_int₂, hbd_int₂⟩ := IsClosedDisc.isOpenDisc_diff_subBd hS hΔ₂
  have hdiscInt_eq : discInt Δ₂ = Δ₂ \ subBd Δ₂ := by rw [discInt, hbd_Δ₂_eq]
  refine theorem_6_1_proof hRig hcl_Cyl hbd_Cyl_HV ?_ ?_
  · intro D hD hD_bd hD_not
    by_cases hD_sub_Δ : D ⊆ Δ
    · have hD_not_compl : ¬ (D ⊆ univ \ discInt Δ₂) := fun hsub =>
        hD_not (fun x hx => ⟨hD_sub_Δ hx, (hsub hx).2⟩)
      have hD_bd_compl : subBd D ⊆ univ \ discInt Δ₂ :=
        hD_bd.trans (fun x hx => ⟨mem_univ x, hx.2⟩)
      have hO_int₂ : IsOArc (subBd (discInt Δ₂)) := by
        rw [hdiscInt_eq, hbd_int₂, hbd_Δ₂_eq]
        exact hΔ₂.isOArc_discBd
      have hcl_int₂_disc : IsClosedDisc (closure (discInt Δ₂)) := by
        rw [hdiscInt_eq, hcl_int₂]
        exact hΔ₂
      obtain ⟨Δ', hΔ'_disc, hΔ'_sub_D, hΔ'_inter_compl, hΔ'_bd_compl⟩ :=
        subsurf_compl_openDisc hS (hdiscInt_eq ▸ hOD₂) hO_int₂ hcl_int₂_disc
          hD hD_bd_compl hD_not_compl
      have hΔ'_sub_Δ : Δ' ⊆ Δ := hΔ'_sub_D.trans hD_sub_Δ
      have hbd_compl_eq : subBd (univ \ discInt Δ₂) = subBd Δ₂ := by
        rw [subBd_eq_frontier, ← compl_eq_univ_sdiff, frontier_compl,
          hdiscInt_eq, ← subBd_eq_frontier, hbd_int₂]
      refine ⟨Δ', hΔ'_disc, hΔ'_sub_D, ?_, ?_⟩
      · rw [← hΔ'_inter_compl]
        ext x
        exact ⟨fun ⟨hxΔ', hxΔ, hxnot⟩ => ⟨hxΔ', mem_univ x, hxnot⟩,
          fun ⟨hxΔ', _, hxnot⟩ => ⟨hxΔ', hΔ'_sub_Δ hxΔ', hxnot⟩⟩
      · rw [hbd_Cyl]
        exact (hbd_compl_eq ▸ hΔ'_bd_compl).trans subset_union_right
    · obtain ⟨Δ', hΔ'_disc, hΔ'_sub_D, hΔ'_inter_Δ, hΔ'_bd_Δ⟩ :=
        subsurf_closedDisc hS hΔ hD (hD_bd.trans sdiff_subset) hD_sub_Δ
      refine ⟨Δ', hΔ'_disc, hΔ'_sub_D, ?_, ?_⟩
      · apply Subset.antisymm
        · intro x ⟨hxΔ', hxΔ, _⟩
          exact hΔ'_inter_Δ ▸ ⟨hxΔ', hxΔ⟩
        · intro x hx_bd'
          have hx_in : x ∈ Δ' ∩ Δ := hΔ'_inter_Δ.symm ▸ hx_bd'
          have hx_bdΔ : x ∈ subBd Δ := hΔ'_bd_Δ hx_bd'
          exact ⟨hx_in.1, hx_in.2, fun hx_int₂ => (hΔ₂_sub hx_int₂.1).2 hx_bdΔ⟩
      · rw [hbd_Cyl]
        exact hΔ'_bd_Δ.trans subset_union_left
  · intro Δ' hΔ' hΔ'_inter hΔ'_bd
    rw [hbd_Cyl] at hΔ'_bd
    have hO_Δ' : IsOArc (subBd Δ') :=
      IsClosedDisc.subBd_eq_discBd hS hΔ' ▸ hΔ'.isOArc_discBd
    have hconn_bd' : IsPreconnected (subBd Δ') := IsOArc.isPreconnected hO_Δ'
    have hcl_bdΔ : IsClosed (subBd Δ) := isClosed_closure.inter isClosed_closure
    have hcl_bdΔ₂ : IsClosed (subBd Δ₂) := isClosed_closure.inter isClosed_closure
    rcases subset_or_subset_of_closed hconn_bd' hcl_bdΔ hcl_bdΔ₂ hΔ'_bd
        (fun x _ hx1 hx2 => disjoint_left.mp hdisj_bd hx1 hx2) with hsub_Δ | hsub_Δ₂
    · have hbd_eq : subBd Δ' = subBd Δ :=
        eq_of_oArc_subset hO_Δ' (hbd_Δ_eq ▸ hΔ.isOArc_discBd) hsub_Δ
      have hdiscBd_eq : discBd Δ' = discBd Δ := by
        rw [← IsClosedDisc.subBd_eq_discBd hS hΔ', ← hbd_Δ_eq, hbd_eq]
      have hne_Δ' : Δ' ≠ Δ := by
        intro hEq
        subst hEq
        obtain ⟨p₀, hp₀⟩ := IsOArc.nonempty (hbd_Δ₂_eq ▸ hΔ₂.isOArc_discBd)
        have hp₀_Δ₂ : p₀ ∈ Δ₂ := Surface.discBd_subset Δ₂ (hbd_Δ₂_eq ▸ hp₀)
        have hp₀_Cyl : p₀ ∈ Cyl :=
          ⟨(hΔ₂_sub hp₀_Δ₂).1, fun h => h.2 (hbd_Δ₂_eq ▸ hp₀)⟩
        have hp₀_bdΔ : p₀ ∈ subBd Δ' := hΔ'_inter ▸ ⟨(hΔ₂_sub hp₀_Δ₂).1, hp₀_Cyl⟩
        exact disjoint_left.mp hdisj_bd (hbd_eq ▸ hp₀_bdΔ) hp₀
      have hcov : Δ' ∪ Δ = univ := cover_of_discBd_eq hS hΔ' hΔ hdiscBd_eq hne_Δ'
      have hcompl_sub : univ \ Δ ⊆ Δ' :=
        fun x ⟨hxU, hxnot⟩ => (hcov.symm ▸ hxU).resolve_right hxnot
      have hcl_sub : closure (univ \ Δ) ⊆ Δ' := hΔ'.isClosed.closure_subset_iff.mpr hcompl_sub
      refine ⟨C_out, hCout_cir, hCout_sub.trans (H.span_isSubdrawing _ _), ?_⟩
      intro x hx
      exact hcl_sub (interSet_U_subset isClosed_closure (hCout_sub.U_subset hx))
    · have hbd_eq : subBd Δ' = subBd Δ₂ :=
        eq_of_oArc_subset hO_Δ' (hbd_Δ₂_eq ▸ hΔ₂.isOArc_discBd) hsub_Δ₂
      have hdiscBd_eq : discBd Δ' = discBd Δ₂ := by
        rw [← IsClosedDisc.subBd_eq_discBd hS hΔ', ← hbd_Δ₂_eq, hbd_eq]
      by_cases hEq : Δ' = Δ₂
      · exact ⟨C, hC_cir, hC_sub, hEq ▸ hCU_sub⟩
      · exfalso
        have hcov : Δ' ∪ Δ₂ = univ := cover_of_discBd_eq hS hΔ' hΔ₂ hdiscBd_eq hEq
        obtain ⟨p₁, hp₁⟩ := IsOArc.nonempty (hbd_Δ_eq ▸ hΔ.isOArc_discBd)
        have hp₁_Δ : p₁ ∈ Δ := Surface.discBd_subset Δ (hbd_Δ_eq ▸ hp₁)
        have hp₁_not_Δ₂ : p₁ ∉ Δ₂ := fun h => (hΔ₂_sub h).2 hp₁
        have hp₁_Δ' : p₁ ∈ Δ' := (hcov.symm ▸ mem_univ p₁).resolve_right hp₁_not_Δ₂
        have hp₁_Cyl : p₁ ∈ Cyl := ⟨hp₁_Δ, fun h => hp₁_not_Δ₂ h.1⟩
        have hp₁_bdΔ₂ : p₁ ∈ subBd Δ₂ := hbd_eq ▸ hΔ'_inter ▸ ⟨hp₁_Δ', hp₁_Cyl⟩
        exact disjoint_left.mp hdisj_bd hp₁ hp₁_bdΔ₂

/-! ## 2. Circuits `C₁ = H'.interSet (subBd Λ)` and `C₂` of `H'` -/

/-- For a closed subset `K`, `(H.interSet K).V = H.V ∩ K` and `(H.interSet K).E = {e ∈ H.E | e ⊆
K}`. -/
theorem interSet_V_and_E_of_isClosed [T2Space S] (H : Drawing S) {K : Set S} (hK : IsClosed K) :
    (H.interSet K).V = H.V ∩ K ∧ (H.interSet K).E = {e ∈ H.E | e ⊆ K} :=
  ⟨H.interSet_V_of_isClosed hK, H.interSet_E K⟩

/-- In the cylinder `Cyl = Δ \ discInt Δ₂`, `C₁ = H'.interSet (subBd Λ)` and `C₂` are circuit
subdrawings of `H' = H.interSet Cyl` with `discBd (closure Λ) = C₁.U`,
`discBd (closure Λ_C₂) = C₂.U`, and `C₁.V = (clearedSubdrawing H Λ).V ∩ subBd Λ`. -/
theorem circuits_cylinder_9_6 [T2Space S] [ConnectedSpace S] (hS : IsClosedSurface S)
    {H C₂ : Drawing S} {d : Set S → Set S → ℕ} {k : ℕ} {z Λ Λ_C₂ Δ Δ₂ : Set S}
    (hZone : IsLambdaZoneAround H d k z Λ)
    (hΔ : IsClosedDisc Δ) (hΔ₂ : IsClosedDisc Δ₂)
    (hclΛ_sub_Δ : closure Λ ⊆ Δ)
    (hC₂_sub : C₂.IsSubdrawing H) (hC₂_cir : C₂.IsCircuit)
    (hcl_C₂_sub : closure Λ_C₂ ⊆ Λ)
    (hcl_C₂_disc : IsClosedDisc (closure Λ_C₂))
    (hbd_cl_C₂ : subBd (closure Λ_C₂) = C₂.U)
    (hΔ₂_sub_cl_C₂ : Δ₂ ⊆ closure Λ_C₂) :
    let Cyl := Δ \ discInt Δ₂
    let H' := H.interSet Cyl
    let C₁ := H'.interSet (subBd Λ)
    C₁.IsCircuit ∧ C₁.IsSubdrawing H' ∧
    C₂.IsCircuit ∧ C₂.IsSubdrawing H' ∧
    discBd (closure Λ) = C₁.U ∧
    discBd (closure Λ_C₂) = C₂.U ∧
    closure Λ \ C₁.U = Λ ∧
    closure Λ_C₂ ⊆ closure Λ \ C₁.U ∧
    C₁.V = H.V ∩ subBd Λ ∧
    C₁.V = (clearedSubdrawing H Λ).V ∩ subBd Λ := by
  intro Cyl H' C₁
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  have hcl_Cyl : IsClosed Cyl := hΔ.isClosed.sdiff (hΔ₂.isOpen_discInt hman)
  have hcl_bdΛ : IsClosed (subBd Λ) := isClosed_closure.inter isClosed_closure
  obtain ⟨hdisL, hclL⟩ := isOpen_disjoint_subBd_and_closure_eq hZone.isOpenDisc.1
  have hbdΛ_sub_Cyl : subBd Λ ⊆ Cyl := by
    intro x hx
    refine ⟨hclΛ_sub_Δ hx.1, fun hx_int₂ => ?_⟩
    have hx_Λ : x ∈ Λ := hcl_C₂_sub (hΔ₂_sub_cl_C₂ hx_int₂.1)
    exact disjoint_left.mp hdisL hx_Λ hx
  have hC₁_eq : C₁ = H.interSet (subBd Λ) :=
    interSet_interSet_of_subset H hbdΛ_sub_Cyl
  obtain ⟨C₀, hC₀_cir, hC₀_sub, hC₀_U⟩ :=
    exists_circuit_of_oArc hZone.isOArc_bd hZone.bd_subset_U
  obtain ⟨hV_Hbd, hE_Hbd⟩ := interSet_V_and_E_of_isClosed H hcl_bdΛ
  have hInter_eq_C₀ : H.interSet (subBd Λ) = C₀ := by
    refine Drawing.ext_VE ?_ ?_
    · rw [hV_Hbd]
      ext x
      simp only [mem_inter_iff]
      refine ⟨fun ⟨hxV, hxbd⟩ => ?_, fun hxC => ⟨hC₀_sub.1 hxC, hC₀_U ▸ C₀.V_subset_U hxC⟩⟩
      by_contra hxnot
      obtain ⟨e, heC, hxe⟩ := C₀.exists_edge_of_mem (hC₀_U.symm ▸ hxbd) hxnot
      exact ((hC₀_sub.2 heC).2.1 hxe).2 hxV
    · rw [hE_Hbd]
      ext e
      simp only [mem_ofPred_eq]
      refine ⟨fun ⟨heH, hebd⟩ => ?_,
        fun heC => ⟨hC₀_sub.2 heC, hC₀_U ▸ subset_closure.trans (C₀.closure_subset_U heC)⟩⟩
      obtain ⟨x, hxe⟩ := heH.1
      have hxnotV : x ∉ C₀.V := fun hxC => (heH.2.1 hxe).2 (hC₀_sub.1 hxC)
      obtain ⟨f, hfC, hxf⟩ := C₀.exists_edge_of_mem (hC₀_U.symm ▸ hebd hxe) hxnotV
      have hef : e = f := arcComponent_eq heH (hC₀_sub.2 hfC) hxe hxf
      exact hef ▸ hfC
  have hC₁_cir : C₁.IsCircuit := hC₁_eq ▸ hInter_eq_C₀ ▸ hC₀_cir
  have hC₁_sub : C₁.IsSubdrawing H' := H'.span_isSubdrawing _ _
  have hC₁_U : C₁.U = subBd Λ := by
    rw [hC₁_eq, hInter_eq_C₀, hC₀_U]
  have hdiscBd_clΛ : discBd (closure Λ) = C₁.U := by
    rw [← IsClosedDisc.subBd_eq_discBd hS hZone.isClosedDisc_closure,
      subBd_closure_eq_subBd_of_isOpenDisc hS hZone.isOpenDisc hZone.isOArc_bd
        hZone.isClosedDisc_closure, hC₁_U]
  have hdiscBd_clC₂ : discBd (closure Λ_C₂) = C₂.U := by
    rw [← IsClosedDisc.subBd_eq_discBd hS hcl_C₂_disc, hbd_cl_C₂]
  have hdiff_clΛ : closure Λ \ C₁.U = Λ := by
    rw [hC₁_U]
    ext y
    exact ⟨fun ⟨hycl, hynot⟩ => (hclL ▸ hycl).resolve_right hynot,
      fun hy => ⟨subset_closure hy, disjoint_left.mp hdisL hy⟩⟩
  -- Show `C₂.U ⊆ Cyl`, hence `C₂.IsSubdrawing H'`
  have hC₂U_sub_Cyl : C₂.U ⊆ Cyl := by
    intro x hx
    have hx_clC₂ : x ∈ closure Λ_C₂ := by
      rw [← hbd_cl_C₂] at hx
      simpa only [closure_closure] using hx.1
    refine ⟨hclΛ_sub_Δ (subset_closure (hcl_C₂_sub hx_clC₂)), fun hx_int₂ => ?_⟩
    have hx_in_int_clC₂ : x ∈ discInt (closure Λ_C₂) :=
      discInt_mono hman hΔ₂ hΔ₂_sub_cl_C₂ hx_int₂
    exact hx_in_int_clC₂.2 (hdiscBd_clC₂ ▸ hx)
  obtain ⟨hV_H', hE_H'⟩ := interSet_V_and_E_of_isClosed H hcl_Cyl
  have hC₂_sub_H' : C₂.IsSubdrawing H' := by
    refine ⟨fun v hv => ?_, fun e he => ?_⟩
    · rw [hV_H']
      exact ⟨hC₂_sub.1 hv, hC₂U_sub_Cyl (C₂.V_subset_U hv)⟩
    · rw [hE_H']
      exact ⟨hC₂_sub.2 he,
        subset_closure.trans ((C₂.closure_subset_U he).trans hC₂U_sub_Cyl)⟩
  have hC₁_V : C₁.V = H.V ∩ subBd Λ := by
    rw [hC₁_eq, hV_Hbd]
  obtain ⟨hV_cl, _⟩ := clearedSubdrawing_V_and_E hZone
  have hC₁_V_cl : C₁.V = (clearedSubdrawing H Λ).V ∩ subBd Λ := by
    rw [hC₁_V, hV_cl]
    ext x
    simp only [mem_inter_iff, mem_sdiff]
    exact ⟨fun ⟨hxV, hxbd⟩ => ⟨⟨hxV, disjoint_left.mp hdisL.symm hxbd⟩, hxbd⟩,
      fun ⟨⟨hxV, _⟩, hxbd⟩ => ⟨hxV, hxbd⟩⟩
  exact ⟨hC₁_cir, hC₁_sub, hC₂_cir, hC₂_sub_H', hdiscBd_clΛ, hdiscBd_clC₂,
    hdiff_clΛ, hdiff_clΛ.symm ▸ hcl_C₂_sub, hC₁_V, hC₁_V_cl⟩

/-! ## 3. Regional Distance `π + 4 ≤ regionalDistance H' C₂.U C₁.U` -/

/-- Any region `r' ∈ H'.R` that meets `Λ` and is not contained in `E₂ = closure Λ_C₂` lies in
`Λ \ E₂` and belongs to `H.R`. -/
private theorem mem_R_and_subset_of_region_in_annulus [T2Space S]
    {H C₁ C₂ : Drawing S} {Cyl Λ E₂ r' : Set S}
    (hCyl_cl : IsClosed Cyl)
    (hEdges_Cyl : ∀ e ∈ H.E, (e ∩ Cyl).Nonempty → e ⊆ Cyl)
    (hΛ_open : IsOpenDisc Λ) (hE₂_disc : IsClosedDisc E₂)
    (hΛ_sub_Δ : Λ ⊆ Cyl ∪ E₂)
    (hC₁_sub : C₁.IsSubdrawing (H.interSet Cyl)) (hC₁_U : C₁.U = subBd Λ)
    (hC₂_sub : C₂.IsSubdrawing (H.interSet Cyl)) (hC₂_U : C₂.U = subBd E₂)
    (hr' : r' ∈ (H.interSet Cyl).R)
    (hmeet_Λ : (r' ∩ Λ).Nonempty)
    (hnot_E₂ : ¬ (r' ⊆ E₂)) :
    r' ⊆ Λ \ E₂ ∧ r' ∈ H.R := by
  let H' := H.interSet Cyl
  obtain ⟨_, hU_H'⟩ := interSet_V_and_U_of_edges hCyl_cl hEdges_Cyl
  have hr'_conn : IsPreconnected r' := region_isPreconnected hr'
  have hr'_disj_U' : Disjoint r' H'.U :=
    disjoint_left.mpr fun x hxr => region_subset hr' hxr
  have hfr_Λ : frontier Λ = C₁.U := by rw [← subBd_eq_frontier, hC₁_U]
  have hfr_E₂ : frontier E₂ = C₂.U := by rw [← subBd_eq_frontier, hC₂_U]
  have hr'_disj_frΛ : Disjoint r' (frontier Λ) := by
    rw [hfr_Λ]
    exact hr'_disj_U'.mono_right hC₁_sub.U_subset
  have hr'_disj_frE₂ : Disjoint r' (frontier E₂) := by
    rw [hfr_E₂]
    exact hr'_disj_U'.mono_right hC₂_sub.U_subset
  obtain ⟨x₀, hx₀r', hx₀Λ⟩ := hmeet_Λ
  have hr'_sub_clΛ : r' ⊆ closure Λ :=
    subset_of_disjoint_frontier hr'_conn isClosed_closure
      (hr'_disj_frΛ.mono_right frontier_closure_subset) hx₀r' (subset_closure hx₀Λ)
  obtain ⟨hdisL, hclL⟩ := isOpen_disjoint_subBd_and_closure_eq hΛ_open.1
  have hr'_sub_Λ : r' ⊆ Λ := by
    intro x hxr
    have hx_cl : x ∈ closure Λ := hr'_sub_clΛ hxr
    rw [hclL] at hx_cl
    exact hx_cl.resolve_right fun hx_bd =>
      disjoint_left.mp hr'_disj_frΛ hxr (hfr_Λ ▸ hC₁_U.symm ▸ hx_bd)
  have hr'_disj_E₂ : Disjoint r' E₂ :=
    (subset_or_disjoint_of_frontier hE₂_disc.isClosed hr'_conn hr'_disj_frE₂).resolve_left hnot_E₂
  have hr'_sub_ann : r' ⊆ Λ \ E₂ :=
    fun x hxr => ⟨hr'_sub_Λ hxr, disjoint_left.mp hr'_disj_E₂ hxr⟩
  -- Show `r' ∈ H.R` using the open set `O₁ = (Λ \ E₂) \ H.U`.
  let U_ann := Λ \ E₂
  have hU_ann_open : IsOpen U_ann := hΛ_open.1.sdiff hE₂_disc.isClosed
  have hU_ann_sub_Cyl : U_ann ⊆ Cyl := by
    intro x ⟨hxΛ, hxnotE₂⟩
    exact (hΛ_sub_Δ hxΛ).resolve_right hxnotE₂
  have hfr_ann_sub : frontier U_ann ⊆ C₁.U ∪ C₂.U := by
    intro x hx
    have hx_diff := frontier_sdiff_subset Λ E₂ hx
    rwa [hfr_Λ, hfr_E₂] at hx_diff
  have hfr_ann_H' : frontier U_ann ⊆ H'.U :=
    hfr_ann_sub.trans (union_subset hC₁_sub.U_subset hC₂_sub.U_subset)
  have hfr_ann_H : frontier U_ann ⊆ H.U :=
    hfr_ann_H'.trans (hU_H' ▸ inter_subset_left)
  obtain ⟨p, hp_not_U', rfl⟩ := (mem_R_iff H').mp hr'
  have hp_ann : p ∈ U_ann :=
    hr'_sub_ann (mem_connectedComponentIn ⟨mem_univ p, hp_not_U'⟩)
  have hp_not_U : p ∉ H.U := fun hpU =>
    hp_not_U' (hU_H'.symm ▸ ⟨hpU, hU_ann_sub_Cyl hp_ann⟩)
  refine ⟨hr'_sub_ann, (mem_R_iff H).mpr ⟨p, hp_not_U, ?_⟩⟩
  apply Subset.antisymm
  · refine isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn ⟨mem_univ p, hp_not_U'⟩) ?_
    intro x hxr
    have hx_ann : x ∈ U_ann := hr'_sub_ann hxr
    have hx_not_U' : x ∉ H'.U := (connectedComponentIn_subset _ _ hxr).2
    exact ⟨mem_univ x, fun hxU => hx_not_U' (hU_H'.symm ▸ ⟨hxU, hU_ann_sub_Cyl hx_ann⟩)⟩
  · have hcompH_disj : Disjoint (connectedComponentIn (univ \ H.U) p) (frontier U_ann) :=
      disjoint_left.mpr fun x hx hfr =>
        (connectedComponentIn_subset _ _ hx).2 (hfr_ann_H hfr)
    have hcompH_sub_cl : connectedComponentIn (univ \ H.U) p ⊆ closure U_ann :=
      subset_of_disjoint_frontier isPreconnected_connectedComponentIn isClosed_closure
        (hcompH_disj.mono_right frontier_closure_subset)
        (mem_connectedComponentIn ⟨mem_univ p, hp_not_U⟩) (subset_closure hp_ann)
    have hcompH_sub_ann : connectedComponentIn (univ \ H.U) p ⊆ U_ann := by
      intro x hx
      have hx_cl : x ∈ closure U_ann := hcompH_sub_cl hx
      rw [closure_eq_interior_union_frontier, hU_ann_open.interior_eq] at hx_cl
      exact hx_cl.resolve_right (disjoint_left.mp hcompH_disj hx)
    refine isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn ⟨mem_univ p, hp_not_U⟩) ?_
    intro x hx
    have hx_not_U : x ∉ H.U := (connectedComponentIn_subset _ _ hx).2
    exact ⟨mem_univ x, fun hxU' => hx_not_U (hU_H' ▸ hxU').1⟩

/-- Every region chain in `H' = H.interSet Cyl` from `E₂` to `univ \ Λ` has length at least
`regionalDistance H E₂ C₁.U`. -/
private theorem regionalDistance_le_of_chain_in_cylinder [T2Space S]
    {H C₁ C₂ : Drawing S} {Cyl Λ E₂ : Set S}
    (hCyl_cl : IsClosed Cyl)
    (hEdges_Cyl : ∀ e ∈ H.E, (e ∩ Cyl).Nonempty → e ⊆ Cyl)
    (hΛ_open : IsOpenDisc Λ) (hE₂_disc : IsClosedDisc E₂)
    (hE₂_sub_Λ : E₂ ⊆ Λ)
    (hΛ_sub_Cyl : Λ ⊆ Cyl ∪ E₂)
    (hC₁_sub : C₁.IsSubdrawing (H.interSet Cyl)) (hC₁_U : C₁.U = subBd Λ)
    (hC₂_sub : C₂.IsSubdrawing (H.interSet Cyl)) (hC₂_U : C₂.U = subBd E₂) :
    ∀ (k : ℕ) (v_seq : Fin (k + 1) → S) (r_seq : Fin k → Set S),
      IsRegionChain (H.interSet Cyl) E₂ (univ \ Λ) v_seq r_seq →
      regionalDistance H E₂ C₁.U ≤ k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro v_seq r_seq ⟨hv0, hvlast, hsteps⟩
    rcases k with _ | m
    · exfalso
      have h0 : Fin.last 0 = (0 : Fin 1) := rfl
      rw [h0] at hvlast
      exact hvlast.2 (hE₂_sub_Λ hv0)
    · by_cases hv1 : v_seq 1 ∈ E₂
      · let v' : Fin (m + 1) → S := fun i => v_seq i.succ
        let r' : Fin m → Set S := fun i => r_seq i.succ
        have hc' : IsRegionChain (H.interSet Cyl) E₂ (univ \ Λ) v' r' :=
          ⟨hv1, hvlast, fun i => hsteps i.succ⟩
        exact (ih m (Nat.lt_succ_self m) v' r' hc').trans (Nat.le_succ m)
      · by_cases hvm : v_seq (Fin.castSucc (Fin.last m)) ∈ univ \ Λ
        · let v' : Fin (m + 1) → S := fun i => v_seq i.castSucc
          let r' : Fin m → Set S := fun i => r_seq i.castSucc
          have hc' : IsRegionChain (H.interSet Cyl) E₂ (univ \ Λ) v' r' :=
            ⟨hv0, hvm, fun i => hsteps i.castSucc⟩
          exact (ih m (Nat.lt_succ_self m) v' r' hc').trans (Nat.le_succ m)
        · by_cases hex_E₂ : ∃ i : Fin (m + 1), v_seq i.succ ∈ E₂
          · obtain ⟨i, hi_E₂⟩ := hex_E₂
            have hi_pos : 0 < i.1 := by
              by_contra h0
              have hi0 : i.succ = 1 := Fin.ext (by simp [Nat.eq_zero_of_not_pos h0])
              exact hv1 (hi0 ▸ hi_E₂)
            let k' := m - i.1
            have hk'_lt : k' < m + 1 := by omega
            let v' : Fin (k' + 1) → S := fun j => v_seq ⟨i.1 + 1 + j.1, by omega⟩
            let r' : Fin k' → Set S := fun j => r_seq ⟨i.1 + 1 + j.1, by omega⟩
            have hc' : IsRegionChain (H.interSet Cyl) E₂ (univ \ Λ) v' r' := by
              refine ⟨?_, ?_, fun j => ?_⟩
              · change v_seq ⟨i.1 + 1 + 0, _⟩ ∈ E₂
                have h_idx : (⟨i.1 + 1 + 0, by omega⟩ : Fin (m + 2)) = i.succ :=
                  Fin.ext (by simp)
                rwa [h_idx]
              · change v_seq ⟨i.1 + 1 + k', _⟩ ∈ univ \ Λ
                have h_idx : (⟨i.1 + 1 + k', by omega⟩ : Fin (m + 2)) = Fin.last (m + 1) :=
                  Fin.ext (by simp [k']; omega)
                rwa [h_idx]
              · have h_step := hsteps ⟨i.1 + 1 + j.1, by omega⟩
                exact h_step
            exact (ih k' hk'_lt v' r' hc').trans (by omega)
          · by_cases hex_out : ∃ i : Fin (m + 1), v_seq i.castSucc ∈ univ \ Λ
            · obtain ⟨i, hi_out⟩ := hex_out
              have hi_pos : 0 < i.1 := by
                by_contra h0
                have hi0 : i.castSucc = 0 := Fin.ext (by simp [Nat.eq_zero_of_not_pos h0])
                exact (hi0 ▸ hi_out).2 (hE₂_sub_Λ hv0)
              have hi_lt : i.1 < m + 1 := i.2
              let v' : Fin (i.1 + 1) → S := fun j => v_seq ⟨j.1, by omega⟩
              let r' : Fin i.1 → Set S := fun j => r_seq ⟨j.1, by omega⟩
              have hc' : IsRegionChain (H.interSet Cyl) E₂ (univ \ Λ) v' r' := by
                refine ⟨hv0, ?_, fun j => hsteps ⟨j.1, by omega⟩⟩
                change v_seq ⟨i.1, _⟩ ∈ univ \ Λ
                exact hi_out
              exact (ih i.1 hi_lt v' r' hc').trans (by omega)
            · push Not at hex_E₂ hex_out
              have hr_in_H : ∀ i : Fin (m + 1), r_seq i ⊆ Λ \ E₂ ∧ r_seq i ∈ H.R := by
                intro i
                have hvi_Λ : v_seq i.castSucc ∈ Λ := by
                  by_contra hnot
                  exact hex_out i ⟨mem_univ _, hnot⟩
                have hvi_cl : v_seq i.castSucc ∈ closure (r_seq i) := (hsteps i).2.1
                have hmeet_Λ : (r_seq i ∩ Λ).Nonempty := by
                  obtain ⟨y, hyΛ, hyr⟩ :=
                    mem_closure_iff.mp hvi_cl Λ hΛ_open.1 hvi_Λ
                  exact ⟨y, hyr, hyΛ⟩
                have hnot_E₂ : ¬ (r_seq i ⊆ E₂) := fun hsub =>
                  hex_E₂ i (hE₂_disc.isClosed.closure_subset_iff.mpr hsub (hsteps i).2.2)
                exact mem_R_and_subset_of_region_in_annulus hCyl_cl hEdges_Cyl
                  hΛ_open hE₂_disc hΛ_sub_Cyl hC₁_sub hC₁_U hC₂_sub hC₂_U
                  (hsteps i).1 hmeet_Λ hnot_E₂
              have hvlast_C₁ : v_seq (Fin.last (m + 1)) ∈ C₁.U := by
                have hlast_cl : v_seq (Fin.last (m + 1)) ∈ closure (r_seq (Fin.last m)) :=
                  (hsteps (Fin.last m)).2.2
                have hr_sub_Λ : r_seq (Fin.last m) ⊆ Λ :=
                  (hr_in_H (Fin.last m)).1.trans sdiff_subset
                have hlast_clΛ : v_seq (Fin.last (m + 1)) ∈ closure Λ :=
                  closure_mono hr_sub_Λ hlast_cl
                obtain ⟨_, hclL⟩ := isOpen_disjoint_subBd_and_closure_eq hΛ_open.1
                rw [hclL] at hlast_clΛ
                rw [hC₁_U]
                exact hlast_clΛ.resolve_left hvlast.2
              have hc_H : IsRegionChain H E₂ C₁.U v_seq r_seq :=
                ⟨hv0, hvlast_C₁, fun i => ⟨(hr_in_H i).2, (hsteps i).2.1, (hsteps i).2.2⟩⟩
              exact regionalDistance_le hc_H

/-- In `H' = H.interSet (Δ \ discInt Δ₂)`, the regional distance `regionalDistance H' C₂.U C₁.U`
is at least `π + 4`. -/
theorem regionalDistance_cylinder_9_6 [T2Space S] [ConnectedSpace S] {α : Type u} {β : Type v}
    (hS : IsClosedSurface S)
    {G' : Graph α β} {H C₁ C₂ : Drawing S} {η' : SpanEmbedding H G'}
    {S_seg : Set (Society α β)} {α_disc : Society α β → Set S} {α_pt : α → S}
    {Λ Λ_C₂ Δ Δ₂ : Set S} {π beta : ℕ}
    (hSeg : IsThreeSegregation G' S_seg)
    (hArr : IsSurfaceArrangement S_seg α_disc α_pt)
    (hComp : IsCompatibleWith G' H η' S_seg α_disc α_pt)
    (hΔ : IsClosedDisc Δ) (hΔ₂ : IsClosedDisc Δ₂)
    (hNorm_Δ : IsArrangementNormal S_seg α_disc α_pt (subBd Δ))
    (hNorm_Δ₂ : IsArrangementNormal S_seg α_disc α_pt (subBd Δ₂))
    (hΛ_open : IsOpenDisc Λ) (hclΛ_sub_Δ : closure Λ ⊆ Δ)
    (hcl_C₂_sub : closure Λ_C₂ ⊆ Λ) (hcl_C₂_disc : IsClosedDisc (closure Λ_C₂))
    (hbd_cl_C₂ : subBd (closure Λ_C₂) = C₂.U)
    (hΔ₂_sub_cl_C₂ : Δ₂ ⊆ closure Λ_C₂)
    (hC₁_cir : C₁.IsCircuit) (hC₁_sub : C₁.IsSubdrawing (H.interSet (Δ \ discInt Δ₂)))
    (hC₁_U : C₁.U = subBd Λ)
    (hC₂_cir : C₂.IsCircuit) (hC₂_sub : C₂.IsSubdrawing (H.interSet (Δ \ discInt Δ₂)))
    (hbeta : 2 * π + 8 ≤ beta)
    (hdist : beta / 2 ≤ regionalDistance H (closure Λ_C₂) (subBd Λ)) :
    π + 4 ≤ regionalDistance (H.interSet (Δ \ discInt Δ₂)) C₂.U C₁.U := by
  let Cyl := Δ \ discInt Δ₂
  let H' := H.interSet Cyl
  let E₂ := closure Λ_C₂
  have hΔ₂_sub : Δ₂ ⊆ Δ \ subBd Δ := by
    have hΛ_sub_int : Λ ⊆ Δ \ subBd Δ := by
      intro x hxΛ
      refine ⟨hclΛ_sub_Δ (subset_closure hxΛ), fun hx_bd => ?_⟩
      obtain ⟨y, hyΛ, hyn⟩ := mem_closure_iff.mp hx_bd.2 Λ hΛ_open.1 hxΛ
      exact hyn.2 (hclΛ_sub_Δ (subset_closure hyΛ))
    exact hΔ₂_sub_cl_C₂.trans (hcl_C₂_sub.trans hΛ_sub_int)
  obtain ⟨hcl_Cyl, hbd_Cyl, _⟩ := cylinder_closed_and_subBd hS hΔ hΔ₂ hΔ₂_sub
  have hbd_Cyl_HV : subBd Cyl ∩ H.U ⊆ H.V := by
    rw [hbd_Cyl, union_inter_distrib_right]
    exact union_subset
      (subBd_inter_U_subset_V_of_normal hSeg hArr hComp hNorm_Δ)
      (subBd_inter_U_subset_V_of_normal hSeg hArr hComp hNorm_Δ₂)
  have hEdges_Cyl : ∀ e ∈ H.E, (e ∩ Cyl).Nonempty → e ⊆ Cyl :=
    fun e he hne => edge_subset_of_inter_nonempty hcl_Cyl hbd_Cyl_HV he hne
  have hΛ_sub_Cyl : Λ ⊆ Cyl ∪ E₂ := by
    intro x hx
    by_cases hxE₂ : x ∈ E₂
    · exact Or.inr hxE₂
    · refine Or.inl ⟨hclΛ_sub_Δ (subset_closure hx), fun hx_int₂ => ?_⟩
      exact hxE₂ (hΔ₂_sub_cl_C₂ hx_int₂.1)
  have hC₂_ne : C₂.U.Nonempty := IsOArc.nonempty (isOArc_of_isCircuit hC₂_cir)
  have hC₁_ne : C₁.U.Nonempty := IsOArc.nonempty (isOArc_of_isCircuit hC₁_cir)
  obtain ⟨v_seq, r_seq, hc⟩ := regionalDistance_spec hS H' hC₂_ne hC₁_ne
  have hv0_E₂ : v_seq 0 ∈ E₂ := by
    have hv0_bd : v_seq 0 ∈ subBd E₂ := hbd_cl_C₂.symm ▸ hc.1
    simpa only [E₂, closure_closure] using hv0_bd.1
  obtain ⟨hdisL, _⟩ := isOpen_disjoint_subBd_and_closure_eq hΛ_open.1
  have hvlast_out : v_seq (Fin.last (regionalDistance H' C₂.U C₁.U)) ∈ univ \ Λ := by
    have hv_bd : v_seq (Fin.last _) ∈ subBd Λ := hC₁_U ▸ hc.2.1
    exact ⟨mem_univ _, disjoint_right.mp hdisL hv_bd⟩
  have hc' : IsRegionChain H' E₂ (univ \ Λ) v_seq r_seq := ⟨hv0_E₂, hvlast_out, hc.2.2⟩
  have hle := regionalDistance_le_of_chain_in_cylinder hcl_Cyl hEdges_Cyl hΛ_open hcl_C₂_disc
    hcl_C₂_sub hΛ_sub_Cyl hC₁_sub hC₁_U hC₂_sub hbd_cl_C₂.symm
    (regionalDistance H' C₂.U C₁.U) v_seq r_seq hc'
  rw [← hC₁_U] at hdist
  change π + 4 ≤ regionalDistance H' C₂.U C₁.U
  omega

/-! ## 4. Truncating the Battlefield Paths to Cylinder Paths from `X_bf` to `C₂.V` -/

/-- Along a simple walk `W` in `H.toGraph` starting at `a ∈ closure Λ` and ending at `v`, if no
vertex `x ≠ v` of `W` is in `subBd Λ` and every edge of `W` is disjoint from `subBd Λ`, then every
vertex of `W` lies in `closure Λ` and every edge of `W` lies in `Λ`. -/
private theorem walk_in_closure_and_edges_in_open {H : Drawing S} {Λ : Set S}
    (hΛ_open : IsOpen Λ) {a v : S} (W : GraphWalk H.toGraph a v)
    (hW : W.IsSimple) (ha : a ∈ closure Λ)
    (hV_bd : ∀ x ∈ W.support, x ∈ subBd Λ → x = v)
    (hE_bd : ∀ e ∈ W.edges, Disjoint e (subBd Λ)) :
    (∀ x ∈ W.support, x ∈ closure Λ) ∧ (∀ e ∈ W.edges, e ⊆ Λ) := by
  obtain ⟨_, hclL⟩ := isOpen_disjoint_subBd_and_closure_eq hΛ_open
  induction W with
  | nil _ =>
    exact ⟨fun x hx => (List.mem_singleton.mp hx) ▸ ha, fun _ he => False.elim
      (List.not_mem_nil he)⟩
  | @cons a c v e hl r ih =>
    have ha_not_r : a ∉ r.support := (List.nodup_cons.mp hW).1
    have ha_ne_v : a ≠ v := fun h => ha_not_r (h ▸ r.end_mem_support)
    have ha_not_bd : a ∉ subBd Λ := fun hbd => ha_ne_v (hV_bd a List.mem_cons_self hbd)
    have ha_Λ : a ∈ Λ := (hclL ▸ ha).resolve_right ha_not_bd
    have he_H : e ∈ H.E := hl.1
    have ha_cl_e : a ∈ closure e := by
      have : a ∈ closure e ∩ H.V := hl.2.2.2 ▸ Or.inl rfl
      exact this.1
    have hc_cl_e : c ∈ closure e := by
      have : c ∈ closure e ∩ H.V := hl.2.2.2 ▸ Or.inr rfl
      exact this.1
    obtain ⟨p, hpΛ, hpe⟩ := mem_closure_iff.mp ha_cl_e Λ hΛ_open ha_Λ
    have hdis_fr : Disjoint e (frontier Λ) := by
      rw [← subBd_eq_frontier]
      exact hE_bd e List.mem_cons_self
    have he_sub_cl : e ⊆ closure Λ :=
      subset_of_disjoint_frontier he_H.2.2.1.isConnected.isPreconnected isClosed_closure
        (hdis_fr.mono_right frontier_closure_subset) hpe (subset_closure hpΛ)
    have he_sub_Λ : e ⊆ Λ := fun y hye =>
      (hclL ▸ he_sub_cl hye).resolve_right
        (disjoint_left.mp (hE_bd e List.mem_cons_self) hye)
    have hc_cl_Λ : c ∈ closure Λ := closure_mono he_sub_Λ hc_cl_e
    obtain ⟨ihV, ihE⟩ := ih hW.of_cons hc_cl_Λ
      (fun x hx => hV_bd x (List.mem_cons_of_mem a hx))
      (fun f hf => hE_bd f (List.mem_cons_of_mem e hf))
    refine ⟨fun x hx => ?_, fun f hf => ?_⟩
    · rcases List.mem_cons.mp hx with rfl | hxr
      · exact ha
      · exact ihV x hxr
    · rcases List.mem_cons.mp hf with rfl | hfr
      · exact he_sub_Λ
      · exact ihE f hfr

/-- Any simple walk `W` in `H.toGraph` from `a ∉ closure Λ_C₂` to `b ∈ closure Λ_C₂` has a simple
prefix `W'` from `a` to some `y ∈ C₂.V` such that no vertex of `W'` lies in `Λ_C₂` and every edge
of `W'` lies in `univ \ closure Λ_C₂`. -/
private theorem exists_prefix_to_C₂ {H C₂ : Drawing S} {Λ_C₂ : Set S}
    (hC₂_sub : C₂.IsSubdrawing H) (hOpen_C₂ : IsOpen Λ_C₂)
    (hbd_cl_C₂ : subBd (closure Λ_C₂) = C₂.U) (hdiff_C₂ : closure Λ_C₂ \ C₂.U = Λ_C₂)
    {a b : S} (W : GraphWalk H.toGraph a b) (hW : W.IsSimple)
    (ha : a ∉ closure Λ_C₂) (hb : b ∈ closure Λ_C₂) :
    ∃ (y : S) (W' : GraphWalk H.toGraph a y),
      y ∈ C₂.V ∧ W'.IsSimple ∧
      (∀ x ∈ W'.support, x ∈ W.support ∧ x ∉ Λ_C₂) ∧
      (∀ e ∈ W'.edges, e ∈ W.edges ∧ e ⊆ univ \ closure Λ_C₂) := by
  induction W with
  | nil _ => exact absurd hb ha
  | @cons a c _ e hl r ih =>
    have he_H : e ∈ H.E := hl.1
    have hc_V : c ∈ H.V := hl.2.2.1
    have ha_cl_e : a ∈ closure e := by
      have : a ∈ closure e ∩ H.V := hl.2.2.2 ▸ Or.inl rfl
      exact this.1
    have hc_cl_e : c ∈ closure e := by
      have : c ∈ closure e ∩ H.V := hl.2.2.2 ▸ Or.inr rfl
      exact this.1
    have hdis_C₂ : Disjoint e C₂.U := by
      refine disjoint_left.mpr fun p hpe hpC₂ => ?_
      have hp_not_V : p ∉ C₂.V := fun hpV => (he_H.2.1 hpe).2 (hC₂_sub.1 hpV)
      obtain ⟨f, hfC₂, hpf⟩ := C₂.exists_edge_of_mem hpC₂ hp_not_V
      have hef : e = f := arcComponent_eq he_H (hC₂_sub.2 hfC₂) hpe hpf
      have ha_C₂ : a ∈ C₂.U := C₂.closure_subset_U (hef ▸ hfC₂) ha_cl_e
      have ha_cl : a ∈ closure Λ_C₂ := by
        rw [← hbd_cl_C₂] at ha_C₂
        simpa only [closure_closure] using ha_C₂.1
      exact ha ha_cl
    obtain ⟨z, hzc, hze⟩ :=
      mem_closure_iff.mp ha_cl_e (closure Λ_C₂)ᶜ isClosed_closure.isOpen_compl ha
    have he_cov : e ⊆ Λ_C₂ ∪ (closure Λ_C₂)ᶜ := by
      intro p hpe
      by_cases hp_cl : p ∈ closure Λ_C₂
      · exact Or.inl (hdiff_C₂ ▸ ⟨hp_cl, disjoint_left.mp hdis_C₂ hpe⟩)
      · exact Or.inr hp_cl
    have hdis_open : Disjoint Λ_C₂ (closure Λ_C₂)ᶜ :=
      disjoint_left.mpr fun p hpΛ hpc => hpc (subset_closure hpΛ)
    have he_sub_compl : e ⊆ (closure Λ_C₂)ᶜ :=
      he_H.2.2.1.isConnected.isPreconnected.subset_right_of_subset_union
        hOpen_C₂ isClosed_closure.isOpen_compl hdis_open he_cov ⟨z, hze, hzc⟩
    have he_sub_sdiff : e ⊆ univ \ closure Λ_C₂ := fun p hpe => ⟨mem_univ p, he_sub_compl hpe⟩
    have hc_not_Λ : c ∉ Λ_C₂ := fun hcΛ => by
      obtain ⟨w, hwΛ, hwe⟩ := mem_closure_iff.mp hc_cl_e Λ_C₂ hOpen_C₂ hcΛ
      exact he_sub_compl hwe (subset_closure hwΛ)
    by_cases hc : c ∈ closure Λ_C₂
    · have hc_C₂U : c ∈ C₂.U := by
        by_contra hnot
        exact hc_not_Λ (hdiff_C₂ ▸ ⟨hc, hnot⟩)
      have hc_C₂V : c ∈ C₂.V := by
        by_contra hnot
        obtain ⟨f, hfC₂, hcf⟩ := C₂.exists_edge_of_mem hc_C₂U hnot
        exact ((hC₂_sub.2 hfC₂).2.1 hcf).2 hc_V
      let W' : GraphWalk H.toGraph a c := GraphWalk.cons hl (GraphWalk.nil hc_V)
      have ha_ne_c : a ≠ c := fun hEq => ha (hEq ▸ hc)
      have hW'_simple : W'.IsSimple :=
        List.nodup_cons.mpr ⟨fun ha_in => ha_ne_c (List.mem_singleton.mp ha_in),
          List.nodup_singleton c⟩
      refine ⟨c, W', hc_C₂V, hW'_simple, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact ⟨List.mem_cons_self, fun haΛ => ha (subset_closure haΛ)⟩
        · rcases List.mem_singleton.mp hx' with rfl
          exact ⟨List.mem_cons_of_mem a r.start_mem_support, hc_not_Λ⟩
      · intro f hf
        rcases List.mem_singleton.mp hf with rfl
        exact ⟨List.mem_cons_self, he_sub_sdiff⟩
    · obtain ⟨y, W₀, hy, hW₀, hsupp₀, hedges₀⟩ := ih hW.of_cons hc hb
      let W' : GraphWalk H.toGraph a y := GraphWalk.cons hl W₀
      have ha_not_W₀ : a ∉ W₀.support :=
        fun ha₀ => (List.nodup_cons.mp hW).1 (hsupp₀ a ha₀).1
      have hW'_simple : W'.IsSimple := List.nodup_cons.mpr ⟨ha_not_W₀, hW₀⟩
      refine ⟨y, W', hy, hW'_simple, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx₀
        · exact ⟨List.mem_cons_self, fun haΛ => ha (subset_closure haΛ)⟩
        · exact ⟨List.mem_cons_of_mem a (hsupp₀ x hx₀).1, (hsupp₀ x hx₀).2⟩
      · intro f hf
        rcases List.mem_cons.mp hf with rfl | hf₀
        · exact ⟨List.mem_cons_self, he_sub_sdiff⟩
        · exact ⟨List.mem_cons_of_mem e (hedges₀ f hf₀).1, (hedges₀ f hf₀).2⟩

/-- From the `beta` disjoint battlefield paths `P_bf` in `H` between `C.V` and `X_bf`
(`2 * π + 8 ≤ beta`), construct `2 * π + 8` vertex-disjoint graph paths `P` in
`(H.interSet (Δ \ discInt Δ₂)).toGraph` from `X_bf` to `C₂.V` meeting `C₁.V` only at their start
vertices. -/
theorem exists_cylinder_paths_9_6 [T2Space S] (hS : IsClosedSurface S)
    {H C C₁ C₂ : Drawing S} {Λ Λ_C₂ Δ Δ₂ X_bf : Set S} {π beta : ℕ}
    (hΛ_open : IsOpenDisc Λ) (hclΛ_sub_Δ : closure Λ ⊆ Δ)
    (hΔ : IsClosedDisc Δ) (hΔ₂ : IsClosedDisc Δ₂)
    (hOpen_C₂ : IsOpenDisc Λ_C₂) (hcl_C₂_sub : closure Λ_C₂ ⊆ Λ)
    (hbd_cl_C₂ : subBd (closure Λ_C₂) = C₂.U)
    (hdiff_C₂ : closure Λ_C₂ \ C₂.U = Λ_C₂)
    (hΔ₂_sub_cl_C₂ : Δ₂ ⊆ closure Λ_C₂)
    (hC_sub_Δ₂ : C.U ⊆ Δ₂)
    (hC₁_V : C₁.V = H.V ∩ subBd Λ)
    (hC₂_sub : C₂.IsSubdrawing H)
    (hX_bf_sub : X_bf ⊆ H.V ∩ subBd Λ)
    (hbeta : 2 * π + 8 ≤ beta)
    (P_bf : Fin beta → Drawing S)
    (hP_bf : ∀ k, ∃ u ∈ C.V, ∃ v ∈ X_bf,
      (P_bf k).IsPathBetween u v ∧ (P_bf k).IsSubdrawing H ∧
      (P_bf k).U ∩ (H.U ∩ subBd Λ) = {v})
    (hDisj_bf : Pairwise (fun i j => Disjoint (P_bf i).V (P_bf j).V)) :
    let H' := H.interSet (Δ \ discInt Δ₂)
    X_bf ⊆ C₁.V ∧
    ∃ P : Fin (2 * π + 8) → Graph S (Set S),
      (∀ i, ∃ x ∈ X_bf, ∃ y ∈ C₂.V,
        IsGraphPathWithEnds H'.toGraph (P i) x y ∧ V(P i) ∩ C₁.V = {x}) ∧
      Pairwise (fun i j => Disjoint V(P i) V(P j)) := by
  intro H'
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  have hcl_Cyl : IsClosed (Δ \ discInt Δ₂) := hΔ.isClosed.sdiff (hΔ₂.isOpen_discInt hman)
  obtain ⟨hV_H', hE_H'⟩ := interSet_V_and_E_of_isClosed H hcl_Cyl
  obtain ⟨hdisL, _⟩ := isOpen_disjoint_subBd_and_closure_eq hΛ_open.1
  have hdiscInt_sub_Λ_C₂ : discInt Δ₂ ⊆ Λ_C₂ := by
    intro x hx
    rw [← hdiff_C₂]
    refine ⟨hΔ₂_sub_cl_C₂ hx.1, fun hxC₂ => ?_⟩
    rw [← hbd_cl_C₂] at hxC₂
    obtain ⟨y, hyint, hynot⟩ :=
      mem_closure_iff.mp hxC₂.2 (discInt Δ₂) (hΔ₂.isOpen_discInt hman) hx
    exact hynot.2 (hΔ₂_sub_cl_C₂ hyint.1)
  have hstep : ∀ i : Fin (2 * π + 8),
      let k : Fin beta := ⟨i.1, by omega⟩
      ∃ x ∈ X_bf, ∃ y ∈ C₂.V, ∃ P_i : Graph S (Set S),
        IsGraphPathWithEnds H'.toGraph P_i x y ∧
        V(P_i) ∩ C₁.V = {x} ∧
        V(P_i) ⊆ (P_bf k).V := by
    intro i
    let k : Fin beta := ⟨i.1, by omega⟩
    obtain ⟨u, huC, v, hvX, ⟨W₀, hW₀_simple, hV_P, hE_P⟩, hP_sub, hP_bd⟩ := hP_bf k
    obtain ⟨W₁, hW₁_supp, hW₁_edges⟩ := hP_sub.exists_walk_up W₀
    have hW₁_simple : W₁.IsSimple := by
      unfold GraphWalk.IsSimple
      rw [hW₁_supp]
      exact hW₀_simple
    have hu_cl_Λ : u ∈ closure Λ :=
      subset_closure (hcl_C₂_sub (hΔ₂_sub_cl_C₂ (hC_sub_Δ₂ (C.V_subset_U huC))))
    have hV_bd : ∀ x ∈ W₁.support, x ∈ subBd Λ → x = v := by
      intro x hx hx_bd
      have hx_PV : x ∈ (P_bf k).V := by
        rw [hV_P, mem_ofPred_eq, ← hW₁_supp]
        exact hx
      have hx_inter : x ∈ (P_bf k).U ∩ (H.U ∩ subBd Λ) :=
        ⟨(P_bf k).V_subset_U hx_PV, H.V_subset_U (hP_sub.1 hx_PV), hx_bd⟩
      rw [hP_bd, mem_singleton_iff] at hx_inter
      exact hx_inter
    have hE_bd : ∀ e ∈ W₁.edges, Disjoint e (subBd Λ) := by
      intro e he
      have he_PE : e ∈ (P_bf k).E := by
        rw [hE_P, mem_ofPred_eq, ← hW₁_edges]
        exact he
      refine disjoint_left.mpr fun x hxe hx_bd => ?_
      have hx_inter : x ∈ (P_bf k).U ∩ (H.U ∩ subBd Λ) :=
        ⟨(P_bf k).closure_subset_U he_PE (subset_closure hxe),
          ((hP_sub.2 he_PE).2.1 hxe).1, hx_bd⟩
      rw [hP_bd, mem_singleton_iff] at hx_inter
      exact ((hP_sub.2 he_PE).2.1 hxe).2 (hx_inter ▸ (hX_bf_sub hvX).1)
    obtain ⟨hW₁_in_cl, hW₁_edges_Λ⟩ :=
      walk_in_closure_and_edges_in_open hΛ_open.1 W₁ hW₁_simple hu_cl_Λ hV_bd hE_bd
    let W₂ : GraphWalk H.toGraph v u := W₁.reverse
    have hW₂_simple : W₂.IsSimple := hW₁_simple.reverse
    have hv_not_clC₂ : v ∉ closure Λ_C₂ := fun hv_cl =>
      disjoint_left.mp hdisL (hcl_C₂_sub hv_cl) (hX_bf_sub hvX).2
    have hu_clC₂ : u ∈ closure Λ_C₂ := hΔ₂_sub_cl_C₂ (hC_sub_Δ₂ (C.V_subset_U huC))
    obtain ⟨y, W₃, hyC₂, hW₃_simple, hW₃_supp, hW₃_edges⟩ :=
      exists_prefix_to_C₂ hC₂_sub hOpen_C₂.1 hbd_cl_C₂ hdiff_C₂ W₂ hW₂_simple hv_not_clC₂ hu_clC₂
    have hW₃_V_H' : ∀ x ∈ W₃.support, x ∈ H'.V := by
      intro x hx
      obtain ⟨hx_W₂, hx_not_ΛC₂⟩ := hW₃_supp x hx
      have hx_W₁ : x ∈ W₁.support := by
        rw [GraphWalk.support_reverse, List.mem_reverse] at hx_W₂
        exact hx_W₂
      rw [hV_H']
      exact ⟨W₃.mem_vertexSet_of_mem_support hx,
        hclΛ_sub_Δ (hW₁_in_cl x hx_W₁), fun hx_int => hx_not_ΛC₂ (hdiscInt_sub_Λ_C₂ hx_int)⟩
    have hW₃_E_H' : ∀ e ∈ W₃.edges, e ∈ H'.E := by
      intro e he
      obtain ⟨he_W₂, he_not_clC₂⟩ := hW₃_edges e he
      have he_W₁ : e ∈ W₁.edges := by
        rw [GraphWalk.edges_reverse, List.mem_reverse] at he_W₂
        exact he_W₂
      rw [hE_H']
      refine ⟨walk_edges_subset_edgeSet W₃ e he, fun p hpe => ?_⟩
      exact ⟨hclΛ_sub_Δ (subset_closure (hW₁_edges_Λ e he_W₁ hpe)),
        fun hp_int => (he_not_clC₂ hpe).2 (hΔ₂_sub_cl_C₂ hp_int.1)⟩
    obtain ⟨W₄, hW₄_supp, _⟩ := (H.span_isSubdrawing _ _).exists_walk_down W₃ hW₃_V_H' hW₃_E_H'
    have hW₄_simple : W₄.IsSimple := by
      unfold GraphWalk.IsSimple
      rw [hW₄_supp]
      exact hW₃_simple
    let P_i : Graph S (Set S) := walkSubgraph W₄
    have hPath_i : IsGraphPathWithEnds H'.toGraph P_i v y :=
      isGraphPathWithEnds_walkSubgraph hW₄_simple
    have hVP_sub : V(P_i) ⊆ (P_bf k).V := by
      intro x hx
      rw [vertexSet_walkSubgraph, mem_ofPred_eq, hW₄_supp] at hx
      have hx_W₂ : x ∈ W₂.support := (hW₃_supp x hx).1
      rw [GraphWalk.support_reverse, List.mem_reverse, hW₁_supp] at hx_W₂
      rw [hV_P]
      exact hx_W₂
    have hVP_inter : V(P_i) ∩ C₁.V = {v} := by
      ext x
      simp only [mem_inter_iff, mem_singleton_iff]
      refine ⟨fun ⟨hxP, hxC₁⟩ => ?_, fun hEq => ?_⟩
      · have hx_W₃ : x ∈ W₃.support := by
          rw [vertexSet_walkSubgraph, mem_ofPred_eq, hW₄_supp] at hxP
          exact hxP
        have hx_W₁ : x ∈ W₁.support := by
          have hx_W₂ := (hW₃_supp x hx_W₃).1
          rwa [GraphWalk.support_reverse, List.mem_reverse] at hx_W₂
        exact hV_bd x hx_W₁ (hC₁_V ▸ hxC₁).2
      · subst hEq
        exact ⟨hPath_i.left_mem, hC₁_V.symm ▸ hX_bf_sub hvX⟩
    exact ⟨v, hvX, y, hyC₂, P_i, hPath_i, hVP_inter, hVP_sub⟩
  choose x hx y hy P hPath hInter hSub using hstep
  refine ⟨hC₁_V.symm ▸ hX_bf_sub, P, fun i => ⟨x i, hx i, y i, hy i, hPath i, hInter i⟩, ?_⟩
  intro i j hij
  have hk_ne : (⟨i.1, by omega⟩ : Fin beta) ≠ ⟨j.1, by omega⟩ :=
    fun h => hij (Fin.ext (Fin.mk.inj_iff.mp h))
  exact (hDisj_bf hk_ne).mono (hSub i) (hSub j)

/-! ## 5. Cylinder Society Composition and 3-Segregation for (9.6) -/

/-- Given nested closed discs `Δ₂ ⊆ Δ \ subBd Δ` on a closed surface `S`, there are inverse
continuous maps `c : ℂ → S` and `c' : S → ℂ` between `closedBall 0 2` and `Δ` such that
`c '' closedBall 0 1 = Δ₂`, `c '' sphere 0 2 = discBd Δ`, and `c '' sphere 0 1 = discBd Δ₂`. -/
private theorem exists_collar_coords (hS : IsClosedSurface S)
    {Δ Δ₂ : Set S} (hΔ : IsClosedDisc Δ) (hΔ₂ : IsClosedDisc Δ₂)
    (hin : Δ₂ ⊆ Δ \ subBd Δ) :
    ∃ (c : ℂ → S) (c' : S → ℂ),
      ContinuousOn c (Metric.closedBall 0 2) ∧ ContinuousOn c' Δ ∧
      MapsTo c (Metric.closedBall 0 2) Δ ∧ MapsTo c' Δ (Metric.closedBall 0 2) ∧
      LeftInvOn c' c (Metric.closedBall 0 2) ∧ RightInvOn c' c Δ ∧
      c '' Metric.closedBall 0 1 = Δ₂ ∧
      c '' Metric.sphere 0 2 = discBd Δ ∧
      c '' Metric.sphere 0 1 = discBd Δ₂ := by
  have hin' : Δ₂ ⊆ Δ \ discBd Δ := IsClosedDisc.subBd_eq_discBd hS hΔ ▸ hin
  obtain ⟨p⟩ := hΔ₂.isOArc_discBd
  obtain ⟨c, c', hc, hc', hmc, hmc', hleft, hright, hΔ₂_eq, hbdΔ_eq, hp_eq⟩ :=
    exists_disc_collar hΔ₂ hΔ hin' p
  refine ⟨c, c', hc, hc', hmc, hmc', hleft, hright, hΔ₂_eq, hbdΔ_eq, ?_⟩
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    let w : Circle := ⟨z, by simpa [Submonoid.unitSphere] using hz⟩
    have hcw : c z = (p w).1 := hp_eq w
    rw [hcw]
    exact (p w).2
  · intro hx
    let w : Circle := p.symm ⟨x, hx⟩
    refine ⟨w.1, mem_sphere_zero_iff_norm.mpr (Circle.norm_coe w), ?_⟩
    rw [hp_eq w, Homeomorph.apply_symm_apply]

/-- Given collar coordinates `(c, c')` for `Δ₂ ⊆ Δ \ subBd Δ` on a closed surface `S`, a boundary
point `p ∈ subBd Δ ∪ subBd Δ₂`, an open neighborhood `U_open` of `p`, and `ε > 0`, there is a
closed disc `D ⊆ (Δ \ discInt Δ₂) ∩ U_open` such that `p ∈ subBd D` and
`∀ x ∈ D, dist (c' x) (c' p) < ε`. -/
private theorem exists_small_collar_disc (hS : IsClosedSurface S)
    {Δ Δ₂ U_open : Set S} {c : ℂ → S} {c' : S → ℂ} {p : S} {ε : ℝ}
    (hΔ : IsClosedDisc Δ) (hΔ₂ : IsClosedDisc Δ₂)
    (hc : ContinuousOn c (Metric.closedBall 0 2))
    (hc' : ContinuousOn c' Δ)
    (hmc : MapsTo c (Metric.closedBall 0 2) Δ)
    (hmc' : MapsTo c' Δ (Metric.closedBall 0 2))
    (hleft : LeftInvOn c' c (Metric.closedBall 0 2))
    (hright : RightInvOn c' c Δ)
    (hΔ₂_eq : c '' Metric.closedBall 0 1 = Δ₂)
    (hbdΔ_eq : c '' Metric.sphere 0 2 = discBd Δ)
    (hbdΔ₂_eq : c '' Metric.sphere 0 1 = discBd Δ₂)
    (hp : p ∈ subBd Δ ∪ subBd Δ₂)
    (hU_open : IsOpen U_open) (hp_U : p ∈ U_open) (hε : 0 < ε) :
    ∃ D : Set S, IsClosedDisc D ∧ D ⊆ (Δ \ discInt Δ₂) ∩ U_open ∧ p ∈ subBd D ∧
      ∀ x ∈ D, dist (c' x) (c' p) < ε := by
  classical
  have hp_Δ : p ∈ Δ := by
    rcases hp with hp1 | hp2
    · exact Surface.discBd_subset Δ (IsClosedDisc.subBd_eq_discBd hS hΔ ▸ hp1)
    · have hp_Δ₂ : p ∈ Δ₂ := Surface.discBd_subset Δ₂ (IsClosedDisc.subBd_eq_discBd hS hΔ₂ ▸ hp2)
      rw [← hΔ₂_eq] at hp_Δ₂
      obtain ⟨z, hz, rfl⟩ := hp_Δ₂
      exact hmc (Metric.closedBall_subset_closedBall (by norm_num) hz)
  have hz₀_ball : c' p ∈ Metric.closedBall (0 : ℂ) 2 := hmc' hp_Δ
  have hc_z₀ : c (c' p) = p := hright hp_Δ
  obtain ⟨V_open, hV_open, hp_V, hV_sub⟩ :=
    continuousOn_iff.mp hc (c' p) hz₀_ball U_open hU_open (hc_z₀.symm ▸ hp_U)
  obtain ⟨δ, hδ_pos, hδ_V⟩ := Metric.isOpen_iff.mp hV_open (c' p) hp_V
  have hδ_U : ∀ z ∈ Metric.closedBall (0 : ℂ) 2, dist z (c' p) < δ → c z ∈ U_open :=
    fun z hz hdist => hV_sub ⟨hδ_V hdist, hz⟩
  let r : ℝ := min (1 / 4) (min (δ / 4) (ε / 4))
  have hr_pos : 0 < r := by positivity
  have hr_le_quarter : r ≤ 1 / 4 := min_le_left _ _
  have hr_lt_δ : 2 * r < δ := by
    have : r ≤ δ / 4 := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hr_lt_ε : 2 * r < ε := by
    have : r ≤ ε / 4 := (min_le_right _ _).trans (min_le_right _ _)
    linarith
  let w₀ : ℂ :=
    if p ∈ subBd Δ then ((1 - r / 2 : ℝ) : ℂ) * c' p else ((1 + r : ℝ) : ℂ) * c' p
  have hw₀_props : dist (c' p) w₀ = r ∧
      ∀ z ∈ Metric.closedBall w₀ r, 1 ≤ ‖z‖ ∧ ‖z‖ ≤ 2 := by
    by_cases hp1 : p ∈ subBd Δ
    · have hp_bd : p ∈ discBd Δ := IsClosedDisc.subBd_eq_discBd hS hΔ ▸ hp1
      rw [← hbdΔ_eq] at hp_bd
      obtain ⟨u, hu_sph, hu_eq⟩ := hp_bd
      have hc'p_eq : c' p = u := by
        rw [← hu_eq]
        exact hleft (Metric.sphere_subset_closedBall hu_sph)
      have hz₀_norm : ‖c' p‖ = 2 := hc'p_eq ▸ mem_sphere_zero_iff_norm.mp hu_sph
      have hw₀_eq : w₀ = ((1 - r / 2 : ℝ) : ℂ) * c' p := by simp [w₀, hp1]
      have hw₀_dist : dist (c' p) w₀ = r := by
        have hdiff : c' p - w₀ = ((r / 2 : ℝ) : ℂ) * c' p := by
          rw [hw₀_eq]; push_cast; ring
        rw [dist_eq_norm, hdiff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by linarith), hz₀_norm]
        ring
      have hw₀_norm : ‖w₀‖ = 2 - r := by
        rw [hw₀_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by linarith), hz₀_norm]
        ring
      refine ⟨hw₀_dist, fun z hz => ?_⟩
      have hz_w₀ : ‖z - w₀‖ ≤ r := dist_eq_norm z w₀ ▸ Metric.mem_closedBall.mp hz
      have h_upper : ‖z‖ ≤ 2 := by
        calc ‖z‖ = ‖(z - w₀) + w₀‖ := by ring_nf
          _ ≤ ‖z - w₀‖ + ‖w₀‖ := norm_add_le _ _
          _ ≤ r + (2 - r) := by linarith
          _ = 2 := by ring
      have h_lower : 1 ≤ ‖z‖ := by
        have h1 : ‖w₀‖ ≤ ‖z‖ + ‖w₀ - z‖ := by
          calc ‖w₀‖ = ‖z + (w₀ - z)‖ := by ring_nf
            _ ≤ ‖z‖ + ‖w₀ - z‖ := norm_add_le _ _
        rw [norm_sub_rev] at h1
        linarith
      exact ⟨h_lower, h_upper⟩
    · have hp2 : p ∈ subBd Δ₂ := hp.resolve_left hp1
      have hp_bd : p ∈ discBd Δ₂ := IsClosedDisc.subBd_eq_discBd hS hΔ₂ ▸ hp2
      rw [← hbdΔ₂_eq] at hp_bd
      obtain ⟨u, hu_sph, hu_eq⟩ := hp_bd
      have hc'p_eq : c' p = u := by
        rw [← hu_eq]
        exact hleft (Metric.closedBall_subset_closedBall (by norm_num)
          (Metric.sphere_subset_closedBall hu_sph))
      have hz₀_norm : ‖c' p‖ = 1 := hc'p_eq ▸ mem_sphere_zero_iff_norm.mp hu_sph
      have hw₀_eq : w₀ = ((1 + r : ℝ) : ℂ) * c' p := by simp [w₀, hp1]
      have hw₀_dist : dist (c' p) w₀ = r := by
        have hdiff : w₀ - c' p = (r : ℂ) * c' p := by
          rw [hw₀_eq]; push_cast; ring
        rw [dist_comm, dist_eq_norm, hdiff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hr_pos, hz₀_norm, mul_one]
      have hw₀_norm : ‖w₀‖ = 1 + r := by
        rw [hw₀_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by linarith), hz₀_norm, mul_one]
      refine ⟨hw₀_dist, fun z hz => ?_⟩
      have hz_w₀ : ‖z - w₀‖ ≤ r := dist_eq_norm z w₀ ▸ Metric.mem_closedBall.mp hz
      have h_upper : ‖z‖ ≤ 2 := by
        calc ‖z‖ = ‖(z - w₀) + w₀‖ := by ring_nf
          _ ≤ ‖z - w₀‖ + ‖w₀‖ := norm_add_le _ _
          _ ≤ r + (1 + r) := by linarith
          _ ≤ 2 := by linarith
      have h_lower : 1 ≤ ‖z‖ := by
        have h1 : ‖w₀‖ ≤ ‖z‖ + ‖w₀ - z‖ := by
          calc ‖w₀‖ = ‖z + (w₀ - z)‖ := by ring_nf
            _ ≤ ‖z‖ + ‖w₀ - z‖ := norm_add_le _ _
        rw [norm_sub_rev] at h1
        linarith
      exact ⟨h_lower, h_upper⟩
  obtain ⟨hw₀_dist, hB_ann⟩ := hw₀_props
  have hB_sub : Metric.closedBall w₀ r ⊆ Metric.closedBall (0 : ℂ) 2 :=
    fun z hz => mem_closedBall_zero_iff.mpr (hB_ann z hz).2
  have hB_dist : ∀ z ∈ Metric.closedBall w₀ r, dist z (c' p) < min δ ε := by
    intro z hz
    have hz_w₀ : dist z w₀ ≤ r := Metric.mem_closedBall.mp hz
    have htri : dist z (c' p) ≤ dist z w₀ + dist w₀ (c' p) := dist_triangle z w₀ (c' p)
    rw [dist_comm w₀ (c' p), hw₀_dist] at htri
    exact lt_min (by linarith) (by linarith)
  have hB_int_ne : (interior (Metric.closedBall w₀ r)).Nonempty := by
    rw [interior_closedBall w₀ hr_pos.ne']
    exact ⟨w₀, Metric.mem_ball_self hr_pos⟩
  obtain ⟨hB_disc, hB_bd⟩ :=
    isClosedDisc_of_convex (convex_closedBall w₀ r) hB_int_ne
      Metric.isBounded_closedBall Metric.isClosed_closedBall
  rw [frontier_closedBall w₀ hr_pos.ne'] at hB_bd
  obtain ⟨hD_disc, hD_bd⟩ :=
    hB_disc.image (hc.mono hB_sub) (hc'.mono (hmc.mono_left hB_sub).image_subset)
      (hleft.mono hB_sub)
  rw [hB_bd] at hD_bd
  refine ⟨c '' Metric.closedBall w₀ r, hD_disc, ?_, ?_, ?_⟩
  · rintro x ⟨z, hz, rfl⟩
    refine ⟨⟨hmc (hB_sub hz), ?_⟩,
      hδ_U z (hB_sub hz) (lt_of_lt_of_le (hB_dist z hz) (min_le_left _ _))⟩
    rintro ⟨hcz_Δ₂, hcz_not_bd⟩
    rw [← hΔ₂_eq] at hcz_Δ₂
    obtain ⟨u, hu, hu_eq⟩ := hcz_Δ₂
    have hu_z : u = z := by
      have h1 := congrArg c' hu_eq
      rwa [hleft (Metric.closedBall_subset_closedBall (by norm_num) hu),
        hleft (hB_sub hz)] at h1
    subst hu_z
    have hz_norm1 : ‖u‖ = 1 :=
      le_antisymm (mem_closedBall_zero_iff.mp hu) (hB_ann u hz).1
    apply hcz_not_bd
    rw [← hbdΔ₂_eq]
    exact ⟨u, mem_sphere_zero_iff_norm.mpr hz_norm1, rfl⟩
  · rw [IsClosedDisc.subBd_eq_discBd hS hD_disc, hD_bd]
    exact ⟨c' p, Metric.mem_sphere.mpr hw₀_dist, hc_z₀⟩
  · rintro x ⟨z, hz, rfl⟩
    rw [hleft (hB_sub hz)]
    exact lt_of_lt_of_le (hB_dist z hz) (min_le_right _ _)

/-- Disjointness of edges and vertex intersection for disjoint families of bridges `B_J` and
`B_rem`. -/
private theorem bridge_sUnion_disjoint_and_inter {α : Type u} {β : Type v}
    {G_amb H_sub G' J : Graph α β} {B_J B_rem : Set (Graph α β)}
    (hH_le : H_sub ≤ G_amb)
    (hB_J : ∀ B ∈ B_J, IsBridge G_amb H_sub B)
    (hB_rem : ∀ B ∈ B_rem, IsBridge G_amb H_sub B)
    (hDisj_B : Disjoint B_J B_rem)
    (hJ_eq : J = subgraphSUnion G_amb B_J)
    (hG'_eq : G' = subgraphSUnion G_amb {H_sub, subgraphSUnion G_amb B_rem}) :
    Disjoint E(G') E(J) ∧ V(G') ∩ V(J) ⊆ V(H_sub) := by
  let U_rem := subgraphSUnion G_amb B_rem
  have hU_rem_le : U_rem ≤ G_amb := subgraphSUnion_le fun B hB => (hB_rem B hB).2.1
  have hPair_le : ∀ Q ∈ ({H_sub, U_rem} : Set (Graph α β)), Q ≤ G_amb := by
    rintro Q (rfl | rfl)
    · exact hH_le
    · exact hU_rem_le
  have hBJ_le : ∀ B ∈ B_J, B ≤ G_amb := fun B hB => (hB_J B hB).2.1
  have hBrem_le : ∀ B ∈ B_rem, B ≤ G_amb := fun B hB => (hB_rem B hB).2.1
  refine ⟨?_, ?_⟩
  · refine Set.disjoint_left.mpr fun e heG' heJ => ?_
    rw [hJ_eq, edgeSet_subgraphSUnion hBJ_le] at heJ
    obtain ⟨B₁, hB₁, heB₁⟩ := mem_iUnion₂.mp heJ
    rw [hG'_eq, edgeSet_subgraphSUnion hPair_le] at heG'
    obtain ⟨Q, rfl | rfl, heQ⟩ := mem_iUnion₂.mp heG'
    · exact Set.disjoint_left.mp (isBridge_disjoint_edgeSet (hB_J B₁ hB₁)) heB₁ heQ
    · rw [edgeSet_subgraphSUnion hBrem_le] at heQ
      obtain ⟨B₂, hB₂, heB₂⟩ := mem_iUnion₂.mp heQ
      have hEq : B₁ = B₂ := (isBridge_eq_of_inter (hB_J B₁ hB₁) (hB_rem B₂ hB₂)).2 e ⟨heB₁, heB₂⟩
      exact Set.disjoint_left.mp hDisj_B hB₁ (hEq ▸ hB₂)
  · rintro v ⟨hvG', hvJ⟩
    by_contra hv_not_H
    rw [hJ_eq, vertexSet_subgraphSUnion] at hvJ
    obtain ⟨B₁, hB₁, hvB₁⟩ := mem_iUnion₂.mp hvJ
    rw [hG'_eq, vertexSet_subgraphSUnion] at hvG'
    obtain ⟨Q, rfl | rfl, hvQ⟩ := mem_iUnion₂.mp hvG'
    · exact hv_not_H hvQ
    · rw [vertexSet_subgraphSUnion] at hvQ
      obtain ⟨B₂, hB₂, hvB₂⟩ := mem_iUnion₂.mp hvQ
      have hEq : B₁ = B₂ :=
        (isBridge_eq_of_inter (hB_J B₁ hB₁) (hB_rem B₂ hB₂)).1 v ⟨hvB₁, hvB₂⟩ hv_not_H
      exact Set.disjoint_left.mp hDisj_B hB₁ (hEq ▸ hB₂)

/-- Dichotomy for discs of `S_seg` with respect to the cylinder `Δ \ discInt Δ₂` when both `subBd Δ`
and `subBd Δ₂` are `α`-normal. -/
private theorem disc_subset_cyl_iff [T2Space S] {α : Type u} {β : Type v}
    (hS : IsClosedSurface S)
    {S_seg : Set (Society α β)} {α_disc : Society α β → Set S} {α_pt : α → S}
    (hArr : IsSurfaceArrangement S_seg α_disc α_pt)
    {Δ Δ₂ : Set S} (hΔ : IsClosedDisc Δ) (hΔ₂ : IsClosedDisc Δ₂)
    (hNorm_Δ : IsArrangementNormal S_seg α_disc α_pt (subBd Δ))
    (hNorm_Δ₂ : IsArrangementNormal S_seg α_disc α_pt (subBd Δ₂))
    {A : Society α β} (hA : A ∈ S_seg) :
    (α_disc A ⊆ Δ \ discInt Δ₂ ↔ (α_disc A ⊆ Δ ∧ ¬ α_disc A ⊆ Δ₂)) ∧
    (¬ α_disc A ⊆ Δ \ discInt Δ₂ →
      α_disc A ∩ (Δ \ discInt Δ₂) ⊆ (subBd Δ ∪ subBd Δ₂) ∧
      α_disc A ∩ (Δ \ discInt Δ₂) ⊆ α_pt '' A.Ω.bar) := by
  obtain ⟨hD, hD_bd⟩ := hArr.isClosedDisc A hA
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro hsub_cyl
    refine ⟨hsub_cyl.trans sdiff_subset, fun hsub_Δ₂ => ?_⟩
    obtain ⟨x, hx_int⟩ := hD.nonempty_discInt
    have hx_D : x ∈ α_disc A := hx_int.1
    have hx_not_bdD : x ∉ subBd (α_disc A) := by
      rw [IsClosedDisc.subBd_eq_discBd hS hD]
      exact hx_int.2
    have hx_bdΔ₂ : x ∈ subBd Δ₂ := by
      rw [IsClosedDisc.subBd_eq_discBd hS hΔ₂]
      by_contra hx_not_bd₂
      exact (hsub_cyl hx_D).2 ⟨hsub_Δ₂ hx_D, hx_not_bd₂⟩
    obtain ⟨v, hv, rfl⟩ := hNorm_Δ₂ A hA ⟨hx_bdΔ₂, hx_D⟩
    exact hx_not_bdD (hD_bd v hv)
  · rintro ⟨hsub_Δ, hnot_Δ₂⟩ x hxD
    obtain ⟨hinter_bd₂, _⟩ :=
      inter_disc_subset_subBd_of_not_subset hS hArr hΔ₂ hNorm_Δ₂ hA hnot_Δ₂
    refine ⟨hsub_Δ hxD, fun hx_int₂ => ?_⟩
    have hx_bd₂ : x ∈ discBd Δ₂ :=
      IsClosedDisc.subBd_eq_discBd hS hΔ₂ ▸ hinter_bd₂ ⟨hxD, hx_int₂.1⟩
    exact hx_int₂.2 hx_bd₂
  · intro hnot_cyl
    by_cases hsub_Δ : α_disc A ⊆ Δ
    · have hsub_Δ₂ : α_disc A ⊆ Δ₂ := by
        by_contra hnot_Δ₂
        apply hnot_cyl
        intro x hxD
        obtain ⟨hinter_bd₂, _⟩ :=
          inter_disc_subset_subBd_of_not_subset hS hArr hΔ₂ hNorm_Δ₂ hA hnot_Δ₂
        refine ⟨hsub_Δ hxD, fun hx_int₂ => ?_⟩
        have hx_bd₂ : x ∈ discBd Δ₂ :=
          IsClosedDisc.subBd_eq_discBd hS hΔ₂ ▸ hinter_bd₂ ⟨hxD, hx_int₂.1⟩
        exact hx_int₂.2 hx_bd₂
      have hinter_bd₂ : α_disc A ∩ (Δ \ discInt Δ₂) ⊆ subBd Δ₂ := by
        rintro x ⟨hxD, _, hx_not_int₂⟩
        rw [IsClosedDisc.subBd_eq_discBd hS hΔ₂]
        by_contra hx_not_bd₂
        exact hx_not_int₂ ⟨hsub_Δ₂ hxD, hx_not_bd₂⟩
      refine ⟨fun x hx => Or.inr (hinter_bd₂ hx), fun x hx => ?_⟩
      exact hNorm_Δ₂ A hA ⟨hinter_bd₂ hx, hx.1⟩
    · obtain ⟨hinter_bd, hinter_bar⟩ :=
        inter_disc_subset_subBd_of_not_subset hS hArr hΔ hNorm_Δ hA hsub_Δ
      refine ⟨fun x hx => Or.inl (hinter_bd ⟨hx.1, hx.2.1⟩),
        fun x hx => hinter_bar ⟨hx.1, hx.2.1⟩⟩

private theorem inner_society_boundary_matches_cylindrical_pullback
    {S : Type w}
    [TopologicalSpace S]
    {α : Type u}
    {β : Type v}
    (hS : IsClosedSurface S)
    {G_amb : Graph α β}
    {G' : Graph α β}
    {J : Graph α β}
    {H : Drawing S}
    {η : SpanEmbedding H G_amb}
    {η' : SpanEmbedding H G'}
    {S_seg : Set (Society α β)}
    {α_disc : Society α β → Set S}
    {α_pt : α → S}
    {Δ : Set S}
    {Δ₂ : Set S}
    (hInter_V : V(G') ∩ V(J) ⊆ V(η.imageGraph))
    (hη'_v : ∀ v ∈ H.V, η'.vMap v = η.vMap v)
    (hSeg : IsThreeSegregation G' S_seg)
    (hComp : IsCompatibleWith G' H η' S_seg α_disc α_pt)
    (hΔ₂ : IsClosedDisc Δ₂)
    (hVJ_Δ₂ : ∀ v ∈ H.V, η.vMap v ∈ V(J) → v ∈ Δ₂ \ subBd Δ₂)
    (hP_le : ∀ (X : Set S), arrangementPullbackGraph G' S_seg α_disc α_pt X ≤ G')
    (Ω₂ : CyclicPerm α)
    (hPull₂ : IsPullbackPerm S_seg α_pt (subBd Δ₂) Ω₂)
    (G₂ : Graph α β)
    (hG₂ : G₂ = subgraphUnion G_amb J (arrangementPullbackGraph G' S_seg α_disc α_pt Δ₂))
    (hΩ₂_sub_G₂ : Ω₂.bar ⊆ V(G₂))
    (hΩ₂_sub_PCyl : Ω₂.bar ⊆ V((arrangementPullbackGraph G' S_seg α_disc α_pt (Δ \ discInt Δ₂))))
    (S₂ : Society α β)
    (hS₂G : S₂.G = G₂) (hS₂Ω : S₂.Ω = Ω₂)
    (hA_iff : ∀ {A : Society α β}, A ∈ S_seg → (α_disc A ⊆ Δ ↔ α_disc A ⊆ Δ₂ ∨ α_disc A ⊆ (Δ \
      discInt Δ₂)) ∧ ¬(α_disc A ⊆ Δ₂ ∧ α_disc A ⊆ (Δ \ discInt Δ₂)))
    (hseg_in_bar : ∀ {A : Society α β}, A ∈ S_seg → ∀ {x : α}, x ∈ V(A.G) → x ∈
      segregationVertices S_seg → x ∈ A.Ω.bar)
    (hbar_pt_in_disc : ∀ {A : Society α β}, A ∈ S_seg → ∀ {x : α}, x ∈ A.Ω.bar → α_pt x ∈ α_disc
      A) :
    S₂.Ω.bar = V(S₂.G) ∩ V((arrangementPullbackGraph G' S_seg α_disc α_pt (Δ \ discInt Δ₂))) := by
  let Cyl := Δ \ discInt Δ₂
  let P_Δ₂ := arrangementPullbackGraph G' S_seg α_disc α_pt Δ₂
  let P_Cyl := arrangementPullbackGraph G' S_seg α_disc α_pt Cyl
  rw [hS₂G, hS₂Ω]
  refine Subset.antisymm (subset_inter hΩ₂_sub_G₂ hΩ₂_sub_PCyl) ?_
  rintro x ⟨hx_G₂, hx_Cyl⟩
  change x ∈ V(G₂) at hx_G₂
  rw [hG₂, vertexSet_subgraphUnion] at hx_G₂
  have hx_PCyl' : (∃ A ∈ S_seg, α_disc A ⊆ Cyl ∧ x ∈ V(A.G)) ∨
      (x ∈ segregationVertices S_seg ∧ α_pt x ∈ Cyl) := by
    simp only [arrangementPullbackGraph, vertexSet_restrict, vertexSet_induce,
      mem_inter_iff, mem_union, mem_iUnion, mem_sep_iff] at hx_Cyl
    rcases hx_Cyl.1 with ⟨A, ⟨hA, hA_Cyl⟩, hxA⟩ | h2
    · exact Or.inl ⟨A, hA, hA_Cyl, hxA⟩
    · exact Or.inr h2
  rcases hx_G₂ with hx_J | hx_PΔ₂
  · exfalso
    have hx_G' : x ∈ V(G') := (hP_le Cyl).vertexSet_mono hx_Cyl
    obtain ⟨v, hvH, rfl⟩ := η.bijOn_v.surjOn (hInter_V ⟨hx_G', hx_J⟩)
    have hv_int₂ : v ∈ discInt Δ₂ := by
      rw [discInt, ← IsClosedDisc.subBd_eq_discBd hS hΔ₂]
      exact hVJ_Δ₂ v hvH hx_J
    have hv_Cyl : v ∈ Cyl := by
      rcases hx_PCyl' with ⟨A, hA, hA_Cyl, hvA⟩ | ⟨hv_seg, hv_pt_Cyl⟩
      · rw [← hη'_v v hvH, ← hComp.inter_V_iff A hA v hvH] at hvA
        exact hA_Cyl hvA
      · have hpt : α_pt (η'.vMap v) = v := hComp.pt_eq v hvH (hη'_v v hvH ▸ hv_seg)
        rwa [← hη'_v v hvH, hpt] at hv_pt_Cyl
    exact hv_Cyl.2 hv_int₂
  · have hx_PΔ₂' : (∃ A ∈ S_seg, α_disc A ⊆ Δ₂ ∧ x ∈ V(A.G)) ∨
        (x ∈ segregationVertices S_seg ∧ α_pt x ∈ Δ₂) := by
      simp only [arrangementPullbackGraph, vertexSet_restrict, vertexSet_induce,
        mem_inter_iff, mem_union, mem_iUnion, mem_sep_iff] at hx_PΔ₂
      rcases hx_PΔ₂.1 with ⟨A, ⟨hA, hA_Δ₂⟩, hxA⟩ | h2
      · exact Or.inl ⟨A, hA, hA_Δ₂, hxA⟩
      · exact Or.inr h2
    have hx_seg_both : x ∈ segregationVertices S_seg ∧ α_pt x ∈ Δ₂ ∧ α_pt x ∈ Cyl := by
      rcases hx_PΔ₂' with ⟨A₁, hA₁, hA₁_Δ₂, hxA₁⟩ | ⟨hx_seg, hx_Δ₂⟩ <;>
        rcases hx_PCyl' with ⟨A₂, hA₂, hA₂_Cyl, hxA₂⟩ | ⟨hx_seg', hx_Cyl'⟩
      · have hne : A₁ ≠ A₂ := fun hEq => (hA_iff hA₁).2 ⟨hA₁_Δ₂, hEq ▸ hA₂_Cyl⟩
        have hbars := hSeg.1.vertex_inter_subset A₁ hA₁ A₂ hA₂ hne ⟨hxA₁, hxA₂⟩
        exact ⟨mem_biUnion hA₁ hbars.1,
          hA₁_Δ₂ (hbar_pt_in_disc hA₁ hbars.1),
          hA₂_Cyl (hbar_pt_in_disc hA₂ hbars.2)⟩
      · have hbar₁ := hseg_in_bar hA₁ hxA₁ hx_seg'
        exact ⟨hx_seg', hA₁_Δ₂ (hbar_pt_in_disc hA₁ hbar₁), hx_Cyl'⟩
      · have hbar₂ := hseg_in_bar hA₂ hxA₂ hx_seg
        exact ⟨hx_seg, hx_Δ₂, hA₂_Cyl (hbar_pt_in_disc hA₂ hbar₂)⟩
      · exact ⟨hx_seg, hx_Δ₂, hx_Cyl'⟩
    change x ∈ Ω₂.bar
    rw [hPull₂.1]
    refine ⟨hx_seg_both.1, ?_⟩
    rw [IsClosedDisc.subBd_eq_discBd hS hΔ₂]
    by_contra hx_not_bd₂
    exact hx_seg_both.2.2.2 ⟨hx_seg_both.2.1, hx_not_bd₂⟩

private theorem cylinder_and_inner_disc_cover_pullback_vertices
    {S : Type w}
    [TopologicalSpace S]
    {α : Type u}
    {β : Type v}
    {G' : Graph α β}
    {S_seg : Set (Society α β)}
    {α_disc : Society α β → Set S}
    {α_pt : α → S}
    {Δ : Set S}
    {Δ₂ : Set S}
    (hin : Δ₂ ⊆ Δ \ subBd Δ)
    (hΔ_union : Δ = Δ₂ ∪ (Δ \ discInt Δ₂))
    (hA_iff : ∀ {A : Society α β}, A ∈ S_seg → (α_disc A ⊆ Δ ↔ α_disc A ⊆ Δ₂ ∨ α_disc A ⊆ (Δ \
      discInt Δ₂)) ∧ ¬(α_disc A ⊆ Δ₂ ∧ α_disc A ⊆ (Δ \ discInt Δ₂))) :
    V((arrangementPullbackGraph G' S_seg α_disc α_pt Δ)) = V((arrangementPullbackGraph G' S_seg
      α_disc α_pt Δ₂)) ∪ V((arrangementPullbackGraph G' S_seg α_disc α_pt (Δ \ discInt Δ₂))) := by
  let Cyl := Δ \ discInt Δ₂
  let P_Δ := arrangementPullbackGraph G' S_seg α_disc α_pt Δ
  let P_Δ₂ := arrangementPullbackGraph G' S_seg α_disc α_pt Δ₂
  let P_Cyl := arrangementPullbackGraph G' S_seg α_disc α_pt Cyl
  ext x
  simp only [arrangementPullbackGraph, vertexSet_restrict, vertexSet_induce,
    mem_union, mem_inter_iff, mem_iUnion, mem_sep_iff]
  constructor
  · rintro ⟨(⟨A, ⟨hA, hA_Δ⟩, hxA⟩ | ⟨hx_seg, hx_Δ⟩), hxG'⟩
    · rcases (hA_iff hA).1.mp hA_Δ with hA_Δ₂ | hA_Cyl
      · exact Or.inl ⟨Or.inl ⟨A, ⟨hA, hA_Δ₂⟩, hxA⟩, hxG'⟩
      · exact Or.inr ⟨Or.inl ⟨A, ⟨hA, hA_Cyl⟩, hxA⟩, hxG'⟩
    · rw [hΔ_union] at hx_Δ
      rcases hx_Δ with hx_Δ₂ | hx_Cyl
      · exact Or.inl ⟨Or.inr ⟨hx_seg, hx_Δ₂⟩, hxG'⟩
      · exact Or.inr ⟨Or.inr ⟨hx_seg, hx_Cyl⟩, hxG'⟩
  · rintro (⟨(⟨A, ⟨hA, hA_Δ₂⟩, hxA⟩ | ⟨hx_seg, hx_Δ₂⟩), hxG'⟩ |
            ⟨(⟨A, ⟨hA, hA_Cyl⟩, hxA⟩ | ⟨hx_seg, hx_Cyl⟩), hxG'⟩)
    · exact ⟨Or.inl ⟨A, ⟨hA, (hA_iff hA).1.mpr (Or.inl hA_Δ₂)⟩, hxA⟩, hxG'⟩
    · exact ⟨Or.inr ⟨hx_seg, (hin hx_Δ₂).1⟩, hxG'⟩
    · exact ⟨Or.inl ⟨A, ⟨hA, (hA_iff hA).1.mpr (Or.inr hA_Cyl)⟩, hxA⟩, hxG'⟩
    · exact ⟨Or.inr ⟨hx_seg, hx_Cyl.1⟩, hxG'⟩

private theorem cylinder_and_inner_disc_cover_pullback_edges
    {S : Type w} [TopologicalSpace S]
    {α : Type u}
    {β : Type v}
    {G' : Graph α β}
    {S_seg : Set (Society α β)}
    {α_disc : Society α β → Set S}
    {α_pt : α → S}
    {Δ : Set S}
    {Δ₂ : Set S}
    (hA_iff : ∀ {A : Society α β}, A ∈ S_seg → (α_disc A ⊆ Δ ↔ α_disc A ⊆ Δ₂ ∨ α_disc A ⊆ (Δ \
      discInt Δ₂)) ∧ ¬(α_disc A ⊆ Δ₂ ∧ α_disc A ⊆ (Δ \ discInt Δ₂)))
    (hEP_eq : ∀ (X : Set S), E(arrangementPullbackGraph G' S_seg α_disc α_pt X) = ⋃ A ∈ {A | A ∈
      S_seg ∧ α_disc A ⊆ X}, E(A.G)) :
    E((arrangementPullbackGraph G' S_seg α_disc α_pt Δ)) = E((arrangementPullbackGraph G' S_seg
      α_disc α_pt Δ₂)) ∪ E((arrangementPullbackGraph G' S_seg α_disc α_pt (Δ \ discInt Δ₂))) := by
  let Cyl := Δ \ discInt Δ₂
  let P_Δ := arrangementPullbackGraph G' S_seg α_disc α_pt Δ
  let P_Δ₂ := arrangementPullbackGraph G' S_seg α_disc α_pt Δ₂
  let P_Cyl := arrangementPullbackGraph G' S_seg α_disc α_pt Cyl
  rw [hEP_eq Δ, hEP_eq Δ₂, hEP_eq Cyl]
  ext e
  simp only [mem_union, mem_iUnion, mem_sep_iff]
  constructor
  · rintro ⟨A, ⟨hA, hA_Δ⟩, heA⟩
    rcases (hA_iff hA).1.mp hA_Δ with hA_Δ₂ | hA_Cyl
    · exact Or.inl ⟨A, ⟨hA, hA_Δ₂⟩, heA⟩
    · exact Or.inr ⟨A, ⟨hA, hA_Cyl⟩, heA⟩
  · rintro (⟨A, ⟨hA, hA_Δ₂⟩, heA⟩ | ⟨A, ⟨hA, hA_Cyl⟩, heA⟩)
    · exact ⟨A, ⟨hA, (hA_iff hA).1.mpr (Or.inl hA_Δ₂)⟩, heA⟩
    · exact ⟨A, ⟨hA, (hA_iff hA).1.mpr (Or.inr hA_Cyl)⟩, heA⟩

private theorem cylindrical_and_inner_disc_pullback_edges_disjoint
    {S : Type w} [TopologicalSpace S]
    {α : Type u}
    {β : Type v}
    {G' : Graph α β}
    {S_seg : Set (Society α β)}
    {α_disc : Society α β → Set S}
    {α_pt : α → S}
    {Δ : Set S}
    {Δ₂ : Set S}
    (hSeg : IsThreeSegregation G' S_seg)
    (hA_iff : ∀ {A : Society α β}, A ∈ S_seg → (α_disc A ⊆ Δ ↔ α_disc A ⊆ Δ₂ ∨ α_disc A ⊆ (Δ \
      discInt Δ₂)) ∧ ¬(α_disc A ⊆ Δ₂ ∧ α_disc A ⊆ (Δ \ discInt Δ₂)))
    (hEP_eq : ∀ (X : Set S), E(arrangementPullbackGraph G' S_seg α_disc α_pt X) = ⋃ A ∈ {A | A ∈
      S_seg ∧ α_disc A ⊆ X}, E(A.G)) :
    Disjoint E((arrangementPullbackGraph G' S_seg α_disc α_pt Δ₂)) E((arrangementPullbackGraph G'
      S_seg α_disc α_pt (Δ \ discInt Δ₂))) := by
  let Cyl := Δ \ discInt Δ₂
  let P_Δ₂ := arrangementPullbackGraph G' S_seg α_disc α_pt Δ₂
  let P_Cyl := arrangementPullbackGraph G' S_seg α_disc α_pt Cyl
  rw [hEP_eq Δ₂, hEP_eq Cyl]
  refine Set.disjoint_left.mpr fun e he₁ he₂ => ?_
  obtain ⟨A₁, ⟨hA₁, hA₁_Δ₂⟩, heA₁⟩ := mem_iUnion₂.mp he₁
  obtain ⟨A₂, ⟨hA₂, hA₂_Cyl⟩, heA₂⟩ := mem_iUnion₂.mp he₂
  have hne : A₁ ≠ A₂ := fun hEq => (hA_iff hA₁).2 ⟨hA₁_Δ₂, hEq ▸ hA₂_Cyl⟩
  exact Set.disjoint_left.mp (hSeg.1.edge_disjoint A₁ hA₁ A₂ hA₂ hne) heA₁ heA₂

/-- Construction of the inner society `S₂`, the cylinder neighborhood `N`, the society composition
`localSociety.IsComposition S₂ N`, and the span embedding `η_1 : SpanEmbedding H' N.G` for Graph
Minors
XIV, (9.6) (page 49). -/
private theorem cylinder_composition_9_6 [T2Space S] {α : Type u} {β : Type v}
    (hS : IsClosedSurface S)
    {G_amb G' J : Graph α β}
    {H : Drawing S} {η : SpanEmbedding H G_amb} {η' : SpanEmbedding H G'}
    {S_seg : Set (Society α β)} {α_disc : Society α β → Set S} {α_pt : α → S}
    {Δ Δ₂ : Set S} {localSociety : Society α β}
    (hV_fin : V(G_amb).Finite) (hE_fin : E(G_amb).Finite)
    (hJ_le : J ≤ G_amb) (hG'_le : G' ≤ G_amb)
    (hDisj_E : Disjoint E(G') E(J)) (hInter_V : V(G') ∩ V(J) ⊆ V(η.imageGraph))
    (hη'_v : ∀ v ∈ H.V, η'.vMap v = η.vMap v)
    (hSeg : IsThreeSegregation G' S_seg)
    (hArr : IsSurfaceArrangement S_seg α_disc α_pt)
    (hComp : IsCompatibleWith G' H η' S_seg α_disc α_pt)
    (hΔ : IsClosedDisc Δ) (hΔ₂ : IsClosedDisc Δ₂)
    (hin : Δ₂ ⊆ Δ \ subBd Δ)
    (hNorm_Δ : IsArrangementNormal S_seg α_disc α_pt (subBd Δ))
    (hNorm_Δ₂ : IsArrangementNormal S_seg α_disc α_pt (subBd Δ₂))
    (hVJ_Δ₂ : ∀ v ∈ H.V, η.vMap v ∈ V(J) → v ∈ Δ₂ \ subBd Δ₂)
    (hsoc_star_G : localSociety.G = subgraphUnion G_amb J (arrangementPullbackGraph G' S_seg α_disc
      α_pt Δ))
    (hsoc_star_Ω : IsPullbackPerm S_seg α_pt (subBd Δ) localSociety.Ω) :
    ∃ (S₂ : Society α β) (N : Neighborhood α β)
      (η_1 : SpanEmbedding (H.interSet (Δ \ discInt Δ₂)) N.G),
      S₂.G = subgraphUnion G_amb J (arrangementPullbackGraph G' S_seg α_disc α_pt Δ₂) ∧
      IsPullbackPerm S_seg α_pt (subBd Δ₂) S₂.Ω ∧
      N.G = arrangementPullbackGraph G' S_seg α_disc α_pt (Δ \ discInt Δ₂) ∧
      N.Ω = localSociety.Ω ∧
      N.Ω₀ = S₂.Ω ∧
      localSociety.IsComposition S₂ N ∧
      (∀ v ∈ (H.interSet (Δ \ discInt Δ₂)).V, η_1.vMap v = η'.vMap v) ∧
      (∀ e ∈ (H.interSet (Δ \ discInt Δ₂)).E, η_1.eMap e = η'.eMap e) ∧
      (H.interSet (Δ \ discInt Δ₂)).V = H.V ∩ (Δ \ discInt Δ₂) ∧
      (H.interSet (Δ \ discInt Δ₂)).U = H.U ∩ (Δ \ discInt Δ₂) ∧
      (H.interSet (Δ \ discInt Δ₂)).E = {e ∈ H.E | e ⊆ Δ \ discInt Δ₂} := by
  classical
  let Cyl := Δ \ discInt Δ₂
  let P_Δ := arrangementPullbackGraph G' S_seg α_disc α_pt Δ
  let P_Δ₂ := arrangementPullbackGraph G' S_seg α_disc α_pt Δ₂
  let P_Cyl := arrangementPullbackGraph G' S_seg α_disc α_pt Cyl
  obtain ⟨hCyl_cl, hCyl_bd, _⟩ :=
    cylinder_closed_and_subBd hS hΔ hΔ₂ hin
  have hbd_sub_Cyl : subBd Δ ∪ subBd Δ₂ ⊆ Cyl := by
    rw [← hCyl_bd]
    exact fun x hx => hCyl_cl.closure_subset_iff.mpr Subset.rfl hx.1
  have hbdΔ_sub_Cyl : subBd Δ ⊆ Cyl := subset_union_left.trans hbd_sub_Cyl
  have hbdΔ₂_sub_Cyl : subBd Δ₂ ⊆ Cyl := subset_union_right.trans hbd_sub_Cyl
  have hP_le : ∀ X : Set S, arrangementPullbackGraph G' S_seg α_disc α_pt X ≤ G' :=
    fun X => Graph.restrict_le.trans (G'.induce_le inter_subset_right)
  have hP_Δ_le_amb : P_Δ ≤ G_amb := (hP_le Δ).trans hG'_le
  have hP_Δ₂_le_amb : P_Δ₂ ≤ G_amb := (hP_le Δ₂).trans hG'_le
  have hP_Cyl_le_amb : P_Cyl ≤ G_amb := (hP_le Cyl).trans hG'_le
  have hseg_sub_G' : segregationVertices S_seg ⊆ V(G') := by
    intro x hx
    obtain ⟨A, hA, hx_bar⟩ := mem_iUnion₂.mp hx
    exact (hSeg.1.le A hA).vertexSet_mono (A.bar_subset hx_bar)
  have hbar_sub_pull : ∀ {F X : Set S} {Ω : CyclicPerm α},
      IsPullbackPerm S_seg α_pt F Ω → F ⊆ X →
      Ω.bar ⊆ V(arrangementPullbackGraph G' S_seg α_disc α_pt X) := by
    intro F X Ω hPull hFX x hx
    rw [hPull.1] at hx
    simp only [arrangementPullbackGraph, vertexSet_restrict, vertexSet_induce, mem_inter_iff,
      mem_union, mem_sep_iff]
    exact ⟨Or.inr ⟨hx.1, hFX hx.2⟩, hseg_sub_G' hx.1⟩
  have hF₂_OArc : IsOArc (subBd Δ₂) :=
    IsClosedDisc.subBd_eq_discBd hS hΔ₂ ▸ hΔ₂.isOArc_discBd
  obtain ⟨Ω₂, hPull₂⟩ := exists_pullbackPerm hSeg.1 hArr hF₂_OArc
  let G₂ := subgraphUnion G_amb J P_Δ₂
  have hG₂_le_amb : G₂ ≤ G_amb := subgraphUnion_le hJ_le hP_Δ₂_le_amb
  have hbdΔ₂_sub_Δ₂ : subBd Δ₂ ⊆ Δ₂ :=
    IsClosedDisc.subBd_eq_discBd hS hΔ₂ ▸ Surface.discBd_subset Δ₂
  have hΩ₂_sub_PΔ₂ : Ω₂.bar ⊆ V(P_Δ₂) := hbar_sub_pull hPull₂ hbdΔ₂_sub_Δ₂
  have hΩ₂_sub_G₂ : Ω₂.bar ⊆ V(G₂) :=
    hΩ₂_sub_PΔ₂.trans (le_subgraphUnion_right hJ_le hP_Δ₂_le_amb).vertexSet_mono
  have hΩ₂_sub_PCyl : Ω₂.bar ⊆ V(P_Cyl) :=
    hbar_sub_pull hPull₂ hbdΔ₂_sub_Cyl
  have hΩ_star_sub_PCyl : localSociety.Ω.bar ⊆ V(P_Cyl) :=
    hbar_sub_pull hsoc_star_Ω hbdΔ_sub_Cyl
  let S₂ : Society α β :=
    ⟨G₂, Ω₂, hV_fin.subset hG₂_le_amb.vertexSet_mono,
      hE_fin.subset hG₂_le_amb.edgeSet_mono, hΩ₂_sub_G₂⟩
  let N : Neighborhood α β :=
    ⟨P_Cyl, localSociety.Ω, Ω₂, hV_fin.subset hP_Cyl_le_amb.vertexSet_mono,
      hE_fin.subset hP_Cyl_le_amb.edgeSet_mono, hΩ_star_sub_PCyl, hΩ₂_sub_PCyl⟩
  -- Decomposition of `Δ` into `Δ₂` and `Cyl`
  have hΔ_union : Δ = Δ₂ ∪ Cyl := by
    ext p
    refine ⟨fun hp => ?_, fun h => h.elim (fun h₂ => (hin h₂).1) (fun hc => hc.1)⟩
    by_cases hp_int : p ∈ discInt Δ₂
    · exact Or.inl hp_int.1
    · exact Or.inr ⟨hp, hp_int⟩
  have hA_iff : ∀ {A : Society α β}, A ∈ S_seg →
      (α_disc A ⊆ Δ ↔ (α_disc A ⊆ Δ₂ ∨ α_disc A ⊆ Cyl)) ∧
      ¬ (α_disc A ⊆ Δ₂ ∧ α_disc A ⊆ Cyl) := by
    intro A hA
    obtain ⟨hcyl_iff, _⟩ := disc_subset_cyl_iff hS hArr hΔ hΔ₂ hNorm_Δ hNorm_Δ₂ hA
    refine ⟨⟨fun hsub_Δ => ?_, fun h => h.elim (fun h₂ => h₂.trans fun _ hx => (hin hx).1)
      (fun hc => (hcyl_iff.mp hc).1)⟩, fun ⟨h₂, hc⟩ => (hcyl_iff.mp hc).2 h₂⟩
    by_cases h₂ : α_disc A ⊆ Δ₂
    · exact Or.inl h₂
    · exact Or.inr (hcyl_iff.mpr ⟨hsub_Δ, h₂⟩)
  have hVP_union : V(P_Δ) = V(P_Δ₂) ∪ V(P_Cyl) := by
    exact cylinder_and_inner_disc_cover_pullback_vertices (S := S) (α := α) (β := β) (G' := G')
      (S_seg := S_seg) (α_disc := α_disc) (α_pt := α_pt) (Δ := Δ) (Δ₂ := Δ₂) hin hΔ_union hA_iff
  have hEP_eq : ∀ X : Set S,
      E(arrangementPullbackGraph G' S_seg α_disc α_pt X) =
        ⋃ A ∈ {A ∈ S_seg | α_disc A ⊆ X}, E(A.G) := by
    intro X
    ext e
    simp only [arrangementPullbackGraph, edgeSet_restrict, mem_inter_iff, edgeSet_induce]
    refine ⟨fun h => h.2, fun he => ⟨?_, he⟩⟩
    obtain ⟨A, ⟨hA, hA_X⟩, heA⟩ := mem_iUnion₂.mp he
    obtain ⟨u, v, huv⟩ := A.G.exists_isLink_of_mem_edgeSet heA
    have huv_G' : G'.IsLink e u v := huv.mono (hSeg.1.le A hA)
    exact ⟨u, v, huv_G',
      ⟨Or.inl (mem_iUnion₂.mpr ⟨A, ⟨hA, hA_X⟩, huv.left_mem⟩), huv_G'.left_mem⟩,
      ⟨Or.inl (mem_iUnion₂.mpr ⟨A, ⟨hA, hA_X⟩, huv.right_mem⟩), huv_G'.right_mem⟩⟩
  have hEP_union : E(P_Δ) = E(P_Δ₂) ∪ E(P_Cyl) := by
    exact cylinder_and_inner_disc_cover_pullback_edges (S := S) (α := α) (β := β) (G' := G')
      (S_seg := S_seg) (α_disc := α_disc) (α_pt := α_pt) (Δ := Δ) (Δ₂ := Δ₂) hA_iff hEP_eq
  have hEP_disj : Disjoint E(P_Δ₂) E(P_Cyl) := by
    exact cylindrical_and_inner_disc_pullback_edges_disjoint (S := S) (α := α) (β := β) (G' := G')
      (S_seg := S_seg) (α_disc := α_disc) (α_pt := α_pt) (Δ := Δ) (Δ₂ := Δ₂) hSeg hA_iff hEP_eq
  have hstar_le_amb : localSociety.G ≤ G_amb := by
    rw [hsoc_star_G]
    exact subgraphUnion_le hJ_le hP_Δ_le_amb
  have hV_sep_union : V(S₂.G) ∪ V(P_Cyl) = V(localSociety.G) := by
    change V(G₂) ∪ V(P_Cyl) = V(localSociety.G)
    rw [hsoc_star_G, vertexSet_subgraphUnion, vertexSet_subgraphUnion, hVP_union, Set.union_assoc]
  have hE_sep_union : E(S₂.G) ∪ E(P_Cyl) = E(localSociety.G) := by
    change E(G₂) ∪ E(P_Cyl) = E(localSociety.G)
    rw [hsoc_star_G, edgeSet_subgraphUnion hJ_le hP_Δ_le_amb,
      edgeSet_subgraphUnion hJ_le hP_Δ₂_le_amb, hEP_union, Set.union_assoc]
  have hE_sep_disj : Disjoint E(S₂.G) E(P_Cyl) := by
    change Disjoint E(G₂) E(P_Cyl)
    rw [edgeSet_subgraphUnion hJ_le hP_Δ₂_le_amb]
    refine Disjoint.union_left ?_ hEP_disj
    exact Disjoint.mono_right (hP_le Cyl).edgeSet_mono hDisj_E.symm
  have hS₂_le_star : S₂.G ≤ localSociety.G :=
    ⟨hV_sep_union ▸ subset_union_left, fun _ _ _ hlink =>
      (hstar_le_amb.isLink_iff (hE_sep_union ▸ Or.inl hlink.edge_mem)).mpr
        (hlink.mono hG₂_le_amb)⟩
  have hPCyl_le_star : P_Cyl ≤ localSociety.G :=
    ⟨hV_sep_union ▸ subset_union_right, fun _ _ _ hlink =>
      (hstar_le_amb.isLink_iff (hE_sep_union ▸ Or.inr hlink.edge_mem)).mpr
        (hlink.mono hP_Cyl_le_amb)⟩
  have hseg_in_bar : ∀ {A : Society α β}, A ∈ S_seg →
      ∀ {x : α}, x ∈ V(A.G) → x ∈ segregationVertices S_seg → x ∈ A.Ω.bar := by
    intro A hA x hxA hx_seg
    obtain ⟨A', hA', hx_bar'⟩ := mem_iUnion₂.mp hx_seg
    by_cases hEq : A = A'
    · subst hEq; exact hx_bar'
    · exact (hSeg.1.vertex_inter_subset A hA A' hA' hEq ⟨hxA, A'.bar_subset hx_bar'⟩).1
  have hbar_pt_in_disc : ∀ {A : Society α β}, A ∈ S_seg →
      ∀ {x : α}, x ∈ A.Ω.bar → α_pt x ∈ α_disc A := by
    intro A hA x hx_bar
    obtain ⟨hD, hD_bd⟩ := hArr.isClosedDisc A hA
    exact hD.isClosed.closure_subset_iff.mpr Subset.rfl (hD_bd x hx_bar).1
  have hV_inter_eq : S₂.Ω.bar = V(S₂.G) ∩ V(P_Cyl) := by
    exact inner_society_boundary_matches_cylindrical_pullback (S := S) (α := α) (β := β) hS (G_amb
      := G_amb) (G' := G') (J := J) (H := H) (η := η) (η' := η') (S_seg := S_seg) (α_disc :=
      α_disc) (α_pt := α_pt) (Δ := Δ) (Δ₂ := Δ₂) hInter_V hη'_v hSeg hComp hΔ₂ hVJ_Δ₂ hP_le Ω₂
      hPull₂ G₂ rfl hΩ₂_sub_G₂ hΩ₂_sub_PCyl S₂ rfl rfl hA_iff hseg_in_bar hbar_pt_in_disc
  have hComp_soc : localSociety.IsComposition S₂ N :=
    ⟨⟨⟨hS₂_le_star, hPCyl_le_star, hV_sep_union, hE_sep_union, hE_sep_disj⟩, hΩ_star_sub_PCyl⟩,
      rfl, rfl, hV_inter_eq⟩
  -- Construct `η_1 : SpanEmbedding (H.interSet Cyl) P_Cyl`
  have hEdges_Cyl : ∀ e ∈ H.E, (e ∩ Cyl).Nonempty →
      ∃ A ∈ S_seg, α_disc A ⊆ Cyl ∧ η'.eMap e ∈ E(A.G) ∧ e ⊆ Cyl := by
    rintro e he ⟨p, hpe, hpCyl⟩
    have he_G' : η'.eMap e ∈ E(G') := η'.imageGraph_le.edgeSet_mono (η'.bijOn_e.mapsTo he)
    have he_u : η'.eMap e ∈ E(subgraphSUnion G' ((fun A : Society α β => A.G) '' S_seg)) := by
      rw [hSeg.1.union_eq]; exact he_G'
    rw [edgeSet_subgraphSUnion (by rintro _ ⟨A, hA, rfl⟩; exact hSeg.1.le A hA)] at he_u
    obtain ⟨_, ⟨A, hA, rfl⟩, heA⟩ := mem_iUnion₂.mp he_u
    have he_disc : e ⊆ α_disc A := (hComp.inter_E_iff A hA e he).mpr heA
    have hA_sub : α_disc A ⊆ Cyl := by
      by_contra hnot
      obtain ⟨_, hbar⟩ :=
        disc_subset_cyl_iff hS hArr hΔ hΔ₂ hNorm_Δ hNorm_Δ₂ hA
      obtain ⟨y, hy_bar, rfl⟩ := (hbar hnot).2 ⟨he_disc hpe, hpCyl⟩
      have hx_bdA : α_pt y ∈ H.U ∩ subBd (α_disc A) :=
        ⟨(he.2.1 hpe).1, (hArr.isClosedDisc A hA).2 y hy_bar⟩
      rw [hComp.bd_inter_eq A hA] at hx_bdA
      exact (he.2.1 hpe).2 hx_bdA.1
    exact ⟨A, hA, hA_sub, heA, he_disc.trans hA_sub⟩
  obtain ⟨hV_HCyl, hU_HCyl⟩ :=
    interSet_V_and_U_of_edges hCyl_cl (fun e he hne => (hEdges_Cyl e he hne).choose_spec.2.2.2)
  have hE_HCyl : (H.interSet Cyl).E = {e ∈ H.E | e ⊆ Cyl} := by
    change (H.span _ _).E = _
    rw [H.span_E]
    ext e
    simp only [mem_inter_iff, mem_ofPred_eq]
    tauto
  have hHV_Cyl_mem_P : ∀ v ∈ H.V, v ∈ Cyl → η'.vMap v ∈ V(P_Cyl) := by
    intro v hvH hvCyl
    have hv_G' : η'.vMap v ∈ V(G') := η'.imageGraph_le.vertexSet_mono (η'.bijOn_v.mapsTo hvH)
    have hv_u : η'.vMap v ∈ V(subgraphSUnion G' ((fun A : Society α β => A.G) '' S_seg)) := by
      rw [hSeg.1.union_eq]; exact hv_G'
    rw [vertexSet_subgraphSUnion] at hv_u
    obtain ⟨_, ⟨A, hA, rfl⟩, hvA⟩ := mem_iUnion₂.mp hv_u
    have hv_disc : v ∈ α_disc A := (hComp.inter_V_iff A hA v hvH).mpr hvA
    change η'.vMap v ∈ V(arrangementPullbackGraph G' S_seg α_disc α_pt Cyl)
    rw [arrangementPullbackGraph, vertexSet_restrict, vertexSet_induce]
    by_cases hA_sub : α_disc A ⊆ Cyl
    · exact ⟨Or.inl (mem_iUnion₂.mpr ⟨A, ⟨hA, hA_sub⟩, hvA⟩), hv_G'⟩
    · obtain ⟨_, hbar⟩ :=
        disc_subset_cyl_iff hS hArr hΔ hΔ₂ hNorm_Δ hNorm_Δ₂ hA
      obtain ⟨y, hy_bar, rfl⟩ := (hbar hA_sub).2 ⟨hv_disc, hvCyl⟩
      have hv_bdA : α_pt y ∈ H.U ∩ subBd (α_disc A) :=
        ⟨H.V_subset_U hvH, (hArr.isClosedDisc A hA).2 y hy_bar⟩
      rw [hComp.bd_inter_eq A hA] at hv_bdA
      have hv_seg : η'.vMap (α_pt y) ∈ segregationVertices S_seg := mem_biUnion hA hv_bdA.2
      have hpt_eq : α_pt (η'.vMap (α_pt y)) = α_pt y := hComp.pt_eq (α_pt y) hvH hv_seg
      exact ⟨Or.inr ⟨hv_seg, hpt_eq.symm ▸ hvCyl⟩, hv_G'⟩
  let η_1₀ : SpanEmbedding (H.interSet Cyl) G' :=
    restrictSpan η' (H.V ∩ Cyl) {e | e ∈ H.E ∧ e ⊆ Cyl}
  have hle_PCyl : η_1₀.imageGraph ≤ P_Cyl := by
    refine ⟨?_, fun b x y hlink => ?_⟩
    · rw [← η_1₀.bijOn_v.image_eq, hV_HCyl]
      rintro _ ⟨v, ⟨hvH, hvCyl⟩, rfl⟩
      exact hHV_Cyl_mem_P v hvH hvCyl
    · have hb_im : b ∈ E(η_1₀.imageGraph) := hlink.edge_mem
      rw [← η_1₀.bijOn_e.image_eq, hE_HCyl] at hb_im
      obtain ⟨e, ⟨heH, he_sub⟩, rfl⟩ := hb_im
      obtain ⟨p, hp⟩ := heH.1
      obtain ⟨A, hA, hA_sub, heA, _⟩ := hEdges_Cyl e heH ⟨p, hp, he_sub hp⟩
      have hb_PCyl : η'.eMap e ∈ E(P_Cyl) := by
        rw [hEP_eq Cyl]
        exact mem_iUnion₂.mpr ⟨A, ⟨hA, hA_sub⟩, heA⟩
      exact ((hP_le Cyl).isLink_iff hb_PCyl).mpr (hlink.mono η_1₀.imageGraph_le)
  let η_1 : SpanEmbedding (H.interSet Cyl) N.G :=
    { η_1₀ with imageGraph_le := hle_PCyl }
  exact ⟨S₂, N, η_1, rfl, hPull₂, rfl, rfl, rfl, hComp_soc,
    fun _ _ => rfl, fun _ _ => rfl, hV_HCyl, hU_HCyl, hE_HCyl⟩

/-- A graph with a single vertex `u` and no edges. -/
private abbrev oneVertexGraph {α : Type u} {β : Type v} (u : α) : Graph α β where
  vertexSet := {u}
  edgeSet := ∅
  IsLink _ _ _ := False
  isLink_symm _ _ := ⟨fun _ _ h => h.elim⟩
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h := h.elim
  edge_mem_iff_exists_isLink _ := ⟨False.elim, fun ⟨_, _, h⟩ => h.elim⟩
  left_mem_of_isLink _ _ _ h := h.elim

/-- The cyclic permutation on a singleton `{u}`. -/
private abbrev singletonCyclicPerm {α : Type u} (u : α) : CyclicPerm α where
  bar := {u}
  toFun := id
  finite_bar := finite_singleton u
  bijOn := bijOn_id {u}
  single_orbit x hx y hy := by
    rw [mem_singleton_iff] at hx hy
    subst hx hy
    exact ⟨0, rfl⟩

/-- The trivial 1-vertex society `({u}, ∅)` with cyclic permutation `{u}`. -/
private abbrev oneVertexSociety {α : Type u} {β : Type v} (u : α) : Society α β where
  G := oneVertexGraph u
  Ω := singletonCyclicPerm u
  finite_V := finite_singleton u
  finite_E := finite_empty
  bar_subset := Subset.rfl

@[simp]
private theorem oneVertexSociety_V {α : Type u} {β : Type v} (u : α) :
    V((oneVertexSociety u : Society α β).G) = {u} := rfl

@[simp]
private theorem oneVertexSociety_E {α : Type u} {β : Type v} (u : α) :
    E((oneVertexSociety u : Society α β).G) = ∅ := rfl

@[simp]
private theorem oneVertexSociety_bar {α : Type u} {β : Type v} (u : α) :
    (oneVertexSociety u : Society α β).Ω.bar = {u} := rfl

private theorem oneVertexSociety_inj {α : Type u} {β : Type v} :
    Function.Injective (oneVertexSociety : α → Society α β) := by
  intro u v h
  have hV : V((oneVertexSociety u : Society α β).G) = V((oneVertexSociety v : Society α β).G) := by
    rw [h]
  rw [oneVertexSociety_V, oneVertexSociety_V] at hV
  exact Set.singleton_eq_singleton_iff.mp hV

/-- If `F` is a finite set and `g : γ → ℝ` is positive on `F`, there is `ε > 0` with `ε < g x` for
all `x ∈ F`. -/
private theorem exists_pos_lt_of_finite {γ : Type*} {F : Set γ} (hF : F.Finite)
    {g : γ → ℝ} (hg : ∀ x ∈ F, 0 < g x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ F, ε < g x := by
  induction F, hF using Set.Finite.induction_on with
  | empty => exact ⟨1, zero_lt_one, fun _ h => h.elim⟩
  | @insert a s _ _ ih =>
    obtain ⟨ε, hε, hlt⟩ := ih (fun x hx => hg x (mem_insert_of_mem a hx))
    have hga : 0 < g a := hg a (mem_insert a s)
    refine ⟨min ε (g a / 2), lt_min hε (half_pos hga), ?_⟩
    rintro x (rfl | hxs)
    · exact lt_of_le_of_lt (min_le_right _ _) (half_lt_self hga)
    · exact lt_of_le_of_lt (min_le_left _ _) (hlt x hxs)

private theorem cylindrical_cells_and_orphans_form_three_segregation
    {S : Type w}
    [TopologicalSpace S]
    {α : Type u}
    {β : Type v}
    {G' : Graph α β}
    {S_seg : Set (Society α β)}
    {α_disc : Society α β → Set S}
    {α_pt : α → S}
    {Δ : Set S}
    {Δ₂ : Set S}
    {N : Neighborhood α β}
    (hSeg : IsThreeSegregation G' S_seg)
    (hN_G : N.G = arrangementPullbackGraph G' S_seg α_disc α_pt (Δ \ discInt Δ₂))
    (Cyl : Set S)
    (hCyl : Cyl = Δ \ discInt Δ₂)
    (Orphans : Set α)
    (hOrphans : Orphans = {u ∈ segregationVertices S_seg | α_pt u ∈ Cyl} \
      ⋃ A ∈ {A | A ∈ S_seg ∧ α_disc A ⊆ Cyl}, V(A.G))
    (hOrphans_fin : Orphans.Finite)
    (hScyl_fin : ({A | A ∈ S_seg ∧ α_disc A ⊆ Cyl}).Finite)
    (hEP_Cyl : E(N.G) = ⋃ A ∈ ({A | A ∈ S_seg ∧ α_disc A ⊆ Cyl}), E(A.G))
    (hSeg1_le : ∀ S₀ ∈ (({A | A ∈ S_seg ∧ α_disc A ⊆ Cyl}) ∪ (oneVertexSociety '' Orphans)), S₀.G
      ≤ N.G) :
    IsThreeSegregation N.G (({A | A ∈ S_seg ∧ α_disc A ⊆ Cyl}) ∪ (oneVertexSociety '' Orphans))
      := by
  subst Orphans
  subst Cyl
  let Cyl := Δ \ discInt Δ₂
  let S_seg_cyl := {A | A ∈ S_seg ∧ α_disc A ⊆ Cyl}
  let Orphans := {u ∈ segregationVertices S_seg | α_pt u ∈ Cyl} \ ⋃ A ∈ S_seg_cyl, V(A.G)
  let S_seg_orph : Set (Society α β) := oneVertexSociety '' Orphans
  let S_seg_1 := S_seg_cyl ∪ S_seg_orph
  refine ⟨⟨hScyl_fin.union (hOrphans_fin.image _), hSeg1_le, ?_, ?_, ?_⟩, ?_⟩
  · have hFam_le : ∀ K ∈ (fun S₀ : Society α β => S₀.G) '' S_seg_1, K ≤ N.G := by
      rintro _ ⟨S₀, hS₀, rfl⟩
      exact hSeg1_le S₀ hS₀
    refine (Compatible.of_le_le (subgraphSUnion_le hFam_le) le_rfl).ext ?_ ?_
    · rw [vertexSet_subgraphSUnion]
      refine Subset.antisymm (iUnion₂_subset fun K hK => (hFam_le K hK).vertexSet_mono) ?_
      intro v hv
      rw [hN_G, arrangementPullbackGraph, vertexSet_restrict, vertexSet_induce] at hv
      rcases hv.1 with hv_cyl | hv_seg_cyl
      · obtain ⟨A, hA, hvA⟩ := mem_iUnion₂.mp hv_cyl
        exact mem_iUnion₂.mpr ⟨A.G, ⟨A, Or.inl hA, rfl⟩, hvA⟩
      · by_cases hv_in : v ∈ ⋃ A ∈ S_seg_cyl, V(A.G)
        · obtain ⟨A, hA, hvA⟩ := mem_iUnion₂.mp hv_in
          exact mem_iUnion₂.mpr ⟨A.G, ⟨A, Or.inl hA, rfl⟩, hvA⟩
        · have hv_orph : v ∈ Orphans := ⟨hv_seg_cyl, hv_in⟩
          exact mem_iUnion₂.mpr ⟨(oneVertexSociety v).G,
            ⟨oneVertexSociety v, Or.inr ⟨v, hv_orph, rfl⟩, rfl⟩, by simp⟩
    · rw [edgeSet_subgraphSUnion hFam_le]
      refine Subset.antisymm (iUnion₂_subset fun K hK => (hFam_le K hK).edgeSet_mono) ?_
      intro e he
      rw [hEP_Cyl] at he
      obtain ⟨A, hA, heA⟩ := mem_iUnion₂.mp he
      exact mem_iUnion₂.mpr ⟨A.G, ⟨A, Or.inl hA, rfl⟩, heA⟩
  · rintro S₁ (hA₁ | ⟨u₁, hu₁, rfl⟩) S₂ (hA₂ | ⟨u₂, hu₂, rfl⟩) hne
    · exact hSeg.1.vertex_inter_subset S₁ hA₁.1 S₂ hA₂.1 hne
    · rintro x ⟨hx₁, hx₂⟩
      rw [oneVertexSociety_V, mem_singleton_iff] at hx₂
      subst hx₂
      exact (hu₂.2 (mem_iUnion₂.mpr ⟨S₁, hA₁, hx₁⟩)).elim
    · rintro x ⟨hx₁, hx₂⟩
      rw [oneVertexSociety_V, mem_singleton_iff] at hx₁
      subst hx₁
      exact (hu₁.2 (mem_iUnion₂.mpr ⟨S₂, hA₂, hx₂⟩)).elim
    · rintro x ⟨hx₁, hx₂⟩
      rw [oneVertexSociety_V, mem_singleton_iff] at hx₁ hx₂
      exact (hne (congrArg oneVertexSociety (hx₁.symm.trans hx₂))).elim
  · rintro S₁ (hA₁ | ⟨u₁, _, rfl⟩) S₂ (hA₂ | ⟨u₂, _, rfl⟩) hne
    · exact hSeg.1.edge_disjoint S₁ hA₁.1 S₂ hA₂.1 hne
    · rw [oneVertexSociety_E]; exact disjoint_bot_right
    · rw [oneVertexSociety_E]; exact disjoint_bot_left
    · rw [oneVertexSociety_E]; exact disjoint_bot_left
  · rintro S₀ (hA | ⟨u, _, rfl⟩)
    · exact hSeg.2 S₀ hA.1
    · rw [oneVertexSociety_bar, ncard_singleton]
      omega

private theorem cylindrical_cells_and_orphans_form_arrangement
    {S : Type w}
    [TopologicalSpace S]
    {α : Type u}
    {β : Type v}
    (hS : IsClosedSurface S)
    {S_seg : Set (Society α β)}
    {α_disc : Society α β → Set S}
    {α_pt : α → S}
    (hArr : IsSurfaceArrangement S_seg α_disc α_pt)
    (Cyl : Set S)
    (H' : Drawing S)
    (Orphans : Set α)
    (c' : S → ℂ)
    (ε : ℝ)
    (D_orph : α → Set S)
    (hD_orph : ∀ u ∈ Orphans, IsClosedDisc (D_orph u) ∧ D_orph u ⊆ Cyl ∩ (fun u => ((⋃ A ∈ ({A | A
      ∈ S_seg ∧ α_disc A ⊆ Cyl}), α_disc A) ∪ H'.V \ {α_pt u})ᶜ) u ∧ α_pt u ∈ subBd (D_orph u) ∧ ∀
      x ∈ D_orph u, dist (c' x) (c' (α_pt u)) < ε)
    (α_disc_1 : Society α β → Set S)
    (hα_disc_1_cyl : ∀ {A : Society α β}, A ∈ ({A | A ∈ S_seg ∧ α_disc A ⊆ Cyl}) → α_disc_1 A =
      α_disc A)
    (hα_disc_1_orph : ∀ {u : α}, u ∈ Orphans → α_disc_1 (oneVertexSociety u) = D_orph u)
    (hD_orph_disj : ∀ {u₁ u₂ : α}, u₁ ∈ Orphans → u₂ ∈ Orphans → u₁ ≠ u₂ → Disjoint (D_orph u₁)
      (D_orph u₂))
    (hseg1_sub_seg : segregationVertices (({A | A ∈ S_seg ∧ α_disc A ⊆ Cyl}) ∪ (oneVertexSociety
      '' Orphans)) ⊆ segregationVertices S_seg) :
    IsSurfaceArrangement (({A | A ∈ S_seg ∧ α_disc A ⊆ Cyl}) ∪ (oneVertexSociety '' Orphans))
      α_disc_1 α_pt := by
  let S_seg_cyl := {A | A ∈ S_seg ∧ α_disc A ⊆ Cyl}
  let S_seg_orph : Set (Society α β) := oneVertexSociety '' Orphans
  let S_seg_1 := S_seg_cyl ∪ S_seg_orph
  let K_cyl := ⋃ A ∈ S_seg_cyl, α_disc A
  let U_open := fun u => (K_cyl ∪ H'.V \ {α_pt u})ᶜ
  refine ⟨?_, ?_, ?_, hArr.injOn_pts.mono hseg1_sub_seg, ?_⟩
  · rintro S₀ (hA | ⟨u, hu, rfl⟩)
    · rw [hα_disc_1_cyl hA]
      exact hArr.isClosedDisc S₀ hA.1
    · rw [hα_disc_1_orph hu]
      refine ⟨(hD_orph u hu).1, ?_⟩
      intro x hx
      simp only [mem_singleton_iff] at hx
      rw [hx]
      exact (hD_orph u hu).2.2.1
  · rintro S₁ (hA₁ | ⟨u₁, hu₁, rfl⟩) S₂ (hA₂ | ⟨u₂, hu₂, rfl⟩) hne
    · rw [hα_disc_1_cyl hA₁, hα_disc_1_cyl hA₂]
      exact hArr.inter_discs S₁ hA₁.1 S₂ hA₂.1 hne
    · rw [hα_disc_1_cyl hA₁, hα_disc_1_orph hu₂]
      rintro x ⟨hx₁, hx₂⟩
      have hx_U : x ∈ U_open u₂ := ((hD_orph u₂ hu₂).2.1 hx₂).2
      exact (hx_U (Or.inl (mem_iUnion₂.mpr ⟨S₁, hA₁, hx₁⟩))).elim
    · rw [hα_disc_1_orph hu₁, hα_disc_1_cyl hA₂]
      rintro x ⟨hx₁, hx₂⟩
      have hx_U : x ∈ U_open u₁ := ((hD_orph u₁ hu₁).2.1 hx₁).2
      exact (hx_U (Or.inl (mem_iUnion₂.mpr ⟨S₂, hA₂, hx₂⟩))).elim
    · rw [hα_disc_1_orph hu₁, hα_disc_1_orph hu₂]
      have hu_ne : u₁ ≠ u₂ := fun hEq => hne (congrArg oneVertexSociety hEq)
      rintro x ⟨hx₁, hx₂⟩
      exact (Set.disjoint_left.mp (hD_orph_disj hu₁ hu₂ hu_ne) hx₁ hx₂).elim
  · rintro S₀ _ x ⟨_, hx_bd⟩
    exact (hx_bd (hS.2.2 x)).elim
  · rintro S₀ (hA | ⟨u, hu, rfl⟩)
    · rw [hα_disc_1_cyl hA]
      exact hArr.natural_order S₀ hA.1
    · rw [hα_disc_1_orph hu]
      have hD_u : IsClosedDisc (D_orph u) := (hD_orph u hu).1
      have hF_OArc : IsOArc (subBd (D_orph u)) :=
        IsClosedDisc.subBd_eq_discBd hS hD_u ▸ hD_u.isOArc_discBd
      obtain ⟨φ⟩ := id hF_OArc
      refine ⟨hF_OArc, φ, ?_, ?_⟩
      · intro v hv
        simp only [mem_singleton_iff] at hv
        rw [hv]
        exact (hD_orph u hu).2.2.1
      · intro v₁ v₂ v₃ hcw
        have hv₁ : v₁ ∈ (oneVertexSociety u : Society α β).Ω.bar := hcw.2.1 v₁ (by simp)
        have hv₂ : v₂ ∈ (oneVertexSociety u : Society α β).Ω.bar := hcw.2.1 v₂ (by simp)
        simp only [mem_singleton_iff] at hv₁ hv₂
        exact False.elim ((List.nodup_cons.mp hcw.1).1 (by simp [hv₁, hv₂]))

private theorem cylindrical_arrangement_is_compatible
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    {α : Type u}
    {β : Type v}
    (hS : IsClosedSurface S)
    {G' : Graph α β}
    {H : Drawing S}
    {η' : SpanEmbedding H G'}
    {S_seg : Set (Society α β)}
    {α_disc : Society α β → Set S}
    {α_pt : α → S}
    {Δ : Set S}
    {Δ₂ : Set S}
    {N : Neighborhood α β}
    {η_1 : SpanEmbedding (H.interSet (Δ \ discInt Δ₂)) N.G}
    (hSeg : IsThreeSegregation G' S_seg)
    (hArr : IsSurfaceArrangement S_seg α_disc α_pt)
    (hComp : IsCompatibleWith G' H η' S_seg α_disc α_pt)
    (hΔ : IsClosedDisc Δ)
    (hΔ₂ : IsClosedDisc Δ₂)
    (hNorm_Δ : IsArrangementNormal S_seg α_disc α_pt (subBd Δ))
    (hNorm_Δ₂ : IsArrangementNormal S_seg α_disc α_pt (subBd Δ₂))
    (hη_1_v : ∀ v ∈ (H.interSet (Δ \ discInt Δ₂)).V, η_1.vMap v = η'.vMap v)
    (hη_1_e : ∀ e ∈ (H.interSet (Δ \ discInt Δ₂)).E, η_1.eMap e = η'.eMap e)
    (hV_H' : (H.interSet (Δ \ discInt Δ₂)).V = H.V ∩ (Δ \ discInt Δ₂))
    (hU_H' : (H.interSet (Δ \ discInt Δ₂)).U = H.U ∩ (Δ \ discInt Δ₂))
    (hE_H' : (H.interSet (Δ \ discInt Δ₂)).E = {e | e ∈ H.E ∧ e ⊆ Δ \ discInt Δ₂})
    (Orphans : Set α)
    (hOrphans : Orphans = {u ∈ segregationVertices S_seg | α_pt u ∈ (Δ \ discInt Δ₂)} \
      ⋃ A ∈ {A | A ∈ S_seg ∧ α_disc A ⊆ (Δ \ discInt Δ₂)}, V(A.G))
    (c' : S → ℂ)
    (ε : ℝ)
    (D_orph : α → Set S)
    (hD_orph : ∀ u ∈ Orphans, IsClosedDisc (D_orph u) ∧ D_orph u ⊆ (Δ \ discInt Δ₂) ∩ (fun u =>
      ((⋃ A ∈ ({A | A
      ∈ S_seg ∧ α_disc A ⊆ (Δ \ discInt Δ₂)}), α_disc A) ∪ (H.interSet
        (Δ \ discInt Δ₂)).V \ {α_pt u})ᶜ) u ∧ α_pt u ∈ subBd (D_orph u) ∧ ∀
      x ∈ D_orph u, dist (c' x) (c' (α_pt u)) < ε)
    (α_disc_1 : Society α β → Set S)
    (hα_disc_1_cyl : ∀ {A : Society α β}, A ∈ ({A | A ∈ S_seg ∧ α_disc A ⊆ (Δ \ discInt Δ₂)})
      → α_disc_1 A =
      α_disc A)
    (hα_disc_1_orph : ∀ {u : α}, u ∈ Orphans → α_disc_1 (oneVertexSociety u) = D_orph u)
    (hseg1_sub_seg : segregationVertices (({A | A ∈ S_seg ∧ α_disc A ⊆ (Δ \ discInt Δ₂)}) ∪
      (oneVertexSociety
      '' Orphans)) ⊆ segregationVertices S_seg) :
    IsCompatibleWith N.G (H.interSet (Δ \ discInt Δ₂)) η_1 (({A | A ∈ S_seg ∧ α_disc A ⊆
      (Δ \ discInt Δ₂)}) ∪ (oneVertexSociety ''
      Orphans)) α_disc_1 α_pt := by
  subst Orphans
  let Cyl := Δ \ discInt Δ₂
  let H' := H.interSet Cyl
  let S_seg_cyl := {A | A ∈ S_seg ∧ α_disc A ⊆ (Δ \ discInt Δ₂)}
  let Orphans := {u ∈ segregationVertices S_seg | α_pt u ∈ Cyl} \ ⋃ A ∈ S_seg_cyl, V(A.G)
  let S_seg_orph : Set (Society α β) := oneVertexSociety '' Orphans
  let S_seg_1 := S_seg_cyl ∪ S_seg_orph
  let K_cyl := ⋃ A ∈ S_seg_cyl, α_disc A
  let U_open := fun u => (K_cyl ∪ H'.V \ {α_pt u})ᶜ
  have hEdges_in_K : ∀ e ∈ H'.E, e ⊆ K_cyl := by
    intro e he
    rw [hE_H'] at he
    obtain ⟨p, hp⟩ := he.1.1
    have he_G' : η'.eMap e ∈ E(G') := η'.imageGraph_le.edgeSet_mono (η'.bijOn_e.mapsTo he.1)
    have he_u : η'.eMap e ∈ E(subgraphSUnion G' ((fun A : Society α β => A.G) '' S_seg)) := by
      rw [hSeg.1.union_eq]; exact he_G'
    rw [edgeSet_subgraphSUnion (by rintro _ ⟨A, hA, rfl⟩; exact hSeg.1.le A hA)] at he_u
    obtain ⟨_, ⟨A, hA, rfl⟩, heA⟩ := mem_iUnion₂.mp he_u
    have he_disc : e ⊆ α_disc A := (hComp.inter_E_iff A hA e he.1).mpr heA
    have hA_sub : α_disc A ⊆ (Δ \ discInt Δ₂) := by
      by_contra hnot
      obtain ⟨_, hbar⟩ :=
        disc_subset_cyl_iff hS hArr hΔ hΔ₂ hNorm_Δ hNorm_Δ₂ hA
      obtain ⟨y, hy_bar, rfl⟩ := (hbar hnot).2 ⟨he_disc hp, he.2 hp⟩
      have hx_bdA : α_pt y ∈ H.U ∩ subBd (α_disc A) :=
        ⟨(he.1.2.1 hp).1, (hArr.isClosedDisc A hA).2 y hy_bar⟩
      rw [hComp.bd_inter_eq A hA] at hx_bdA
      exact (he.1.2.1 hp).2 hx_bdA.1
    exact he_disc.trans (subset_biUnion_of_mem ⟨hA, hA_sub⟩)
  have hOrph_pt_vMap : ∀ {u : α}, u ∈ Orphans → ∀ {v : S}, v ∈ H'.V →
      (v = α_pt u ↔ η_1.vMap v = u) := by
    intro u hu v hv
    rw [hη_1_v v hv]
    rw [hV_H'] at hv
    constructor
    · rintro rfl
      obtain ⟨B, hB, hu_barB⟩ := mem_iUnion₂.mp hu.1.1
      have hbdB : α_pt u ∈ H.U ∩ subBd (α_disc B) :=
        ⟨H.V_subset_U hv.1, (hArr.isClosedDisc B hB).2 u hu_barB⟩
      rw [hComp.bd_inter_eq B hB] at hbdB
      have hv_seg : η'.vMap (α_pt u) ∈ segregationVertices S_seg := mem_biUnion hB hbdB.2
      have hpt_eq : α_pt (η'.vMap (α_pt u)) = α_pt u := hComp.pt_eq (α_pt u) hv.1 hv_seg
      exact hArr.injOn_pts hv_seg hu.1.1 hpt_eq
    · rintro rfl
      exact (hComp.pt_eq v hv.1 hu.1.1).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv hv_seg1
    rw [hη_1_v v hv]
    rw [hV_H'] at hv
    exact hComp.pt_eq v hv.1 (hseg1_sub_seg (hη_1_v v (hV_H'.symm ▸ hv) ▸ hv_seg1))
  · rintro S₀ (hA | ⟨u, hu, rfl⟩)
    · rw [hα_disc_1_cyl hA]
      ext x
      simp only [mem_inter_iff, mem_sep_iff]
      constructor
      · rintro ⟨hxU', hx_bd⟩
        rw [hU_H'] at hxU'
        have hx_in : x ∈ H.U ∩ subBd (α_disc S₀) := ⟨hxU'.1, hx_bd⟩
        rw [hComp.bd_inter_eq S₀ hA.1] at hx_in
        have hxV' : x ∈ H'.V := hV_H'.symm ▸ ⟨hx_in.1, hxU'.2⟩
        exact ⟨hxV', (hη_1_v x hxV').symm ▸ hx_in.2⟩
      · rintro ⟨hxV', hx_bar⟩
        rw [hη_1_v x hxV'] at hx_bar
        rw [hV_H'] at hxV'
        have hx_in : x ∈ H.U ∩ subBd (α_disc S₀) := by
          rw [hComp.bd_inter_eq S₀ hA.1]
          exact ⟨hxV'.1, hx_bar⟩
        exact ⟨hU_H'.symm ▸ ⟨hx_in.1, hxV'.2⟩, hx_in.2⟩
    · rw [hα_disc_1_orph hu, oneVertexSociety_bar]
      have hD_u : IsClosedDisc (D_orph u) := (hD_orph u hu).1
      have hbd_sub_D : subBd (D_orph u) ⊆ D_orph u :=
        fun x hx => hD_u.isClosed.closure_subset_iff.mpr Subset.rfl hx.1
      ext x
      simp only [mem_inter_iff, mem_sep_iff, mem_singleton_iff]
      constructor
      · rintro ⟨hxU', hx_bd⟩
        have hx_D : x ∈ D_orph u := hbd_sub_D hx_bd
        have hx_Uopen : x ∈ U_open u := ((hD_orph u hu).2.1 hx_D).2
        have hxV' : x ∈ H'.V := by
          by_contra hx_not_V'
          rw [hU_H'] at hxU'
          have hx_not_HV : x ∉ H.V := fun hxHV => hx_not_V' (hV_H'.symm ▸ ⟨hxHV, hxU'.2⟩)
          obtain ⟨e, heH, hxe⟩ := H.exists_edge_of_mem hxU'.1 hx_not_HV
          have heH' : e ∈ H'.E := by
            rw [hE_H']
            refine ⟨heH, ?_⟩
            have he_G' : η'.eMap e ∈ E(G') :=
              η'.imageGraph_le.edgeSet_mono (η'.bijOn_e.mapsTo heH)
            have he_u : η'.eMap e ∈
                E(subgraphSUnion G' ((fun A : Society α β => A.G) '' S_seg)) := by
              rw [hSeg.1.union_eq]; exact he_G'
            rw [edgeSet_subgraphSUnion
              (by rintro _ ⟨A, hA, rfl⟩; exact hSeg.1.le A hA)] at he_u
            obtain ⟨_, ⟨A, hA, rfl⟩, heA⟩ := mem_iUnion₂.mp he_u
            have he_disc : e ⊆ α_disc A := (hComp.inter_E_iff A hA e heH).mpr heA
            have hA_sub : α_disc A ⊆ (Δ \ discInt Δ₂) := by
              by_contra hnot
              obtain ⟨_, hbar⟩ :=
                disc_subset_cyl_iff hS hArr hΔ hΔ₂ hNorm_Δ hNorm_Δ₂ hA
              obtain ⟨y, hy_bar, rfl⟩ := (hbar hnot).2 ⟨he_disc hxe, hxU'.2⟩
              have hx_bdA : α_pt y ∈ H.U ∩ subBd (α_disc A) :=
                ⟨hxU'.1, (hArr.isClosedDisc A hA).2 y hy_bar⟩
              rw [hComp.bd_inter_eq A hA] at hx_bdA
              exact hx_not_HV hx_bdA.1
            exact he_disc.trans hA_sub
          exact hx_Uopen (Or.inl (hEdges_in_K e heH' hxe))
        have hx_eq : x = α_pt u := by
          by_contra hne
          exact hx_Uopen (Or.inr ⟨hxV', hne⟩)
        exact ⟨hxV', (hOrph_pt_vMap hu hxV').mp hx_eq⟩
      · rintro ⟨hxV', hx_bar⟩
        have hx_eq : x = α_pt u := (hOrph_pt_vMap hu hxV').mpr hx_bar
        exact ⟨H'.V_subset_U hxV', hx_eq ▸ (hD_orph u hu).2.2.1⟩
  · rintro S₀ (hA | ⟨u, hu, rfl⟩) v hv
    · rw [hα_disc_1_cyl hA, hη_1_v v hv]
      rw [hV_H'] at hv
      exact hComp.inter_V_iff S₀ hA.1 v hv.1
    · rw [hα_disc_1_orph hu, oneVertexSociety_V, mem_singleton_iff, ← hOrph_pt_vMap hu hv]
      constructor
      · intro hv_D
        have hv_U : v ∈ U_open u := ((hD_orph u hu).2.1 hv_D).2
        by_contra hne
        exact hv_U (Or.inr ⟨hv, hne⟩)
      · rintro rfl
        have hD_u : IsClosedDisc (D_orph u) := (hD_orph u hu).1
        exact hD_u.isClosed.closure_subset_iff.mpr Subset.rfl (hD_orph u hu).2.2.1.1
  · rintro S₀ (hA | ⟨u, hu, rfl⟩) e he
    · rw [hα_disc_1_cyl hA, hη_1_e e he]
      rw [hE_H'] at he
      exact hComp.inter_E_iff S₀ hA.1 e he.1
    · rw [hα_disc_1_orph hu, oneVertexSociety_E]
      simp only [mem_empty_iff_false, iff_false]
      intro hsub
      have he_H : e ∈ H.E := (hE_H' ▸ he).1
      obtain ⟨p, hp⟩ := he_H.1
      have hp_U : p ∈ U_open u := ((hD_orph u hu).2.1 (hsub hp)).2
      exact hp_U (Or.inl (hEdges_in_K e he hp))

private theorem small_orphan_discs_are_pairwise_disjoint
    {S : Type w}
    [TopologicalSpace S]
    {α : Type u}
    {α_pt : α → S}
    (Cyl : Set S)
    (Orphans : Set α)
    (c' : S → ℂ)
    (ε : ℝ)
    (hε_lt : ∀ x ∈ ({p : α × α | p.1 ∈ Orphans ∧ p.2 ∈ Orphans ∧ p.1 ≠ p.2}), ε < dist (c'
      (α_pt x.1)) (c'
      (α_pt x.2)) / 2)
    (U_open : α → Set S)
    (D_orph : α → Set S)
    (hD_orph : ∀ u ∈ Orphans, IsClosedDisc (D_orph u) ∧ D_orph u ⊆ Cyl ∩ U_open u ∧ α_pt u ∈ subBd
      (D_orph u) ∧ ∀ x ∈ D_orph u, dist (c' x) (c' (α_pt u)) < ε) :
    ∀ {u₁ u₂ : α}, u₁ ∈ Orphans → u₂ ∈ Orphans → u₁ ≠ u₂ → Disjoint (D_orph u₁) (D_orph u₂) := by
  let Pairs : Set (α × α) := {p | p.1 ∈ Orphans ∧ p.2 ∈ Orphans ∧ p.1 ≠ p.2}
  intro u₁ u₂ hu₁ hu₂ hne
  refine Set.disjoint_left.mpr fun x hx₁ hx₂ => ?_
  have hd₁ : dist (c' x) (c' (α_pt u₁)) < ε := (hD_orph u₁ hu₁).2.2.2 x hx₁
  have hd₂ : dist (c' x) (c' (α_pt u₂)) < ε := (hD_orph u₂ hu₂).2.2.2 x hx₂
  have hpair : ε < dist (c' (α_pt u₁)) (c' (α_pt u₂)) / 2 :=
    hε_lt (u₁, u₂) ⟨hu₁, hu₂, hne⟩
  have htri : dist (c' (α_pt u₁)) (c' (α_pt u₂)) ≤
      dist (c' (α_pt u₁)) (c' x) + dist (c' x) (c' (α_pt u₂)) :=
    dist_triangle _ _ _
  rw [dist_comm (c' (α_pt u₁)) (c' x)] at htri
  linarith

/-- Construction of the 3-segregation `S_seg_1` of `N.G` and its compatible surface arrangement
`(α_disc_1, α_pt)` in the cylinder `Δ \ discInt Δ₂` for Graph Minors XIV, (9.6) (page 49). -/
private theorem cylinder_segregation_9_6 [T2Space S] {α : Type u} {β : Type v}
    (hS : IsClosedSurface S)
    {G' : Graph α β} {H : Drawing S} {η' : SpanEmbedding H G'}
    {S_seg : Set (Society α β)} {α_disc : Society α β → Set S} {α_pt : α → S}
    {Δ Δ₂ : Set S} {N : Neighborhood α β}
    {η_1 : SpanEmbedding (H.interSet (Δ \ discInt Δ₂)) N.G}
    (hSeg : IsThreeSegregation G' S_seg)
    (hArr : IsSurfaceArrangement S_seg α_disc α_pt)
    (hComp : IsCompatibleWith G' H η' S_seg α_disc α_pt)
    (hΔ : IsClosedDisc Δ) (hΔ₂ : IsClosedDisc Δ₂)
    (hin : Δ₂ ⊆ Δ \ subBd Δ)
    (hNorm_Δ : IsArrangementNormal S_seg α_disc α_pt (subBd Δ))
    (hNorm_Δ₂ : IsArrangementNormal S_seg α_disc α_pt (subBd Δ₂))
    (hN_G : N.G = arrangementPullbackGraph G' S_seg α_disc α_pt (Δ \ discInt Δ₂))
    (hPull_Ω : IsPullbackPerm S_seg α_pt (subBd Δ) N.Ω)
    (hPull_Ω₀ : IsPullbackPerm S_seg α_pt (subBd Δ₂) N.Ω₀)
    (hη_1_v : ∀ v ∈ (H.interSet (Δ \ discInt Δ₂)).V, η_1.vMap v = η'.vMap v)
    (hη_1_e : ∀ e ∈ (H.interSet (Δ \ discInt Δ₂)).E, η_1.eMap e = η'.eMap e)
    (hV_H' : (H.interSet (Δ \ discInt Δ₂)).V = H.V ∩ (Δ \ discInt Δ₂))
    (hU_H' : (H.interSet (Δ \ discInt Δ₂)).U = H.U ∩ (Δ \ discInt Δ₂))
    (hE_H' : (H.interSet (Δ \ discInt Δ₂)).E = {e ∈ H.E | e ⊆ Δ \ discInt Δ₂}) :
    ∃ (S_seg_1 : Set (Society α β)) (α_disc_1 : Society α β → Set S),
      IsThreeSegregation N.G S_seg_1 ∧
      IsSurfaceArrangement S_seg_1 α_disc_1 α_pt ∧
      IsCompatibleWith N.G (H.interSet (Δ \ discInt Δ₂)) η_1 S_seg_1 α_disc_1 α_pt ∧
      (∀ S₀ ∈ S_seg_1, α_disc_1 S₀ ⊆ Δ \ discInt Δ₂) ∧
      IsPullbackPerm S_seg_1 α_pt (discBd Δ) N.Ω ∧
      IsPullbackPerm S_seg_1 α_pt (discBd Δ₂) N.Ω₀ := by
  classical
  let Cyl := Δ \ discInt Δ₂
  let H' := H.interSet Cyl
  let S_seg_cyl : Set (Society α β) := {A ∈ S_seg | α_disc A ⊆ Cyl}
  let Orphans : Set α :=
    {u ∈ segregationVertices S_seg | α_pt u ∈ Cyl} \ ⋃ A ∈ S_seg_cyl, V(A.G)
  let S_seg_orph : Set (Society α β) := (oneVertexSociety : α → Society α β) '' Orphans
  let S_seg_1 : Set (Society α β) := S_seg_cyl ∪ S_seg_orph
  have hseg_sub_G' : segregationVertices S_seg ⊆ V(G') := by
    intro x hx
    obtain ⟨A, hA, hx_bar⟩ := mem_iUnion₂.mp hx
    exact (hSeg.1.le A hA).vertexSet_mono (A.bar_subset hx_bar)
  have hbar_pt_in_disc : ∀ {A : Society α β}, A ∈ S_seg →
      ∀ {x : α}, x ∈ A.Ω.bar → α_pt x ∈ α_disc A := by
    intro A hA x hx_bar
    obtain ⟨hD, hD_bd⟩ := hArr.isClosedDisc A hA
    exact hD.isClosed.closure_subset_iff.mpr Subset.rfl (hD_bd x hx_bar).1
  have hOrphans_bd : ∀ u ∈ Orphans, α_pt u ∈ subBd Δ ∪ subBd Δ₂ := by
    rintro u ⟨⟨hu_seg, hu_Cyl⟩, hu_not_cyl⟩
    obtain ⟨A, hA, hu_bar⟩ := mem_iUnion₂.mp hu_seg
    have hA_not_cyl : ¬ (α_disc A ⊆ Cyl) := fun hsub =>
      hu_not_cyl (mem_iUnion₂.mpr ⟨A, ⟨hA, hsub⟩, A.bar_subset hu_bar⟩)
    obtain ⟨_, hbar⟩ := disc_subset_cyl_iff hS hArr hΔ hΔ₂ hNorm_Δ hNorm_Δ₂ hA
    exact (hbar hA_not_cyl).1 ⟨hbar_pt_in_disc hA hu_bar, hu_Cyl⟩
  have hOrphans_not_in_K : ∀ u ∈ Orphans, ∀ A ∈ S_seg_cyl, α_pt u ∉ α_disc A := by
    rintro u ⟨⟨hu_seg, _⟩, hu_not_cyl⟩ A ⟨hA, hA_Cyl⟩ hpt_in_A
    obtain ⟨B, hB, hu_barB⟩ := mem_iUnion₂.mp hu_seg
    have hAB_ne : B ≠ A := fun hEq =>
      hu_not_cyl (mem_iUnion₂.mpr ⟨A, ⟨hA, hA_Cyl⟩, hEq ▸ B.bar_subset hu_barB⟩)
    have hpt_inter : α_pt u ∈ α_disc B ∩ α_disc A := ⟨hbar_pt_in_disc hB hu_barB, hpt_in_A⟩
    obtain ⟨w, ⟨hwB, hwA⟩, hw_eq⟩ := hArr.inter_discs B hB A hA hAB_ne hpt_inter
    have hwu : w = u := hArr.injOn_pts (mem_biUnion hB hwB) hu_seg hw_eq
    exact hu_not_cyl (mem_iUnion₂.mpr ⟨A, ⟨hA, hA_Cyl⟩, hwu ▸ A.bar_subset hwA⟩)
  have hOrphans_fin : Orphans.Finite := by
    refine (N.Ω.finite_bar.union N.Ω₀.finite_bar).subset ?_
    intro u hu
    rcases hOrphans_bd u hu with hbd₁ | hbd₂
    · exact Or.inl (hPull_Ω.1.symm ▸ ⟨hu.1.1, hbd₁⟩)
    · exact Or.inr (hPull_Ω₀.1.symm ▸ ⟨hu.1.1, hbd₂⟩)
  have hDisj_cyl_orph : Disjoint S_seg_cyl S_seg_orph := by
    refine Set.disjoint_left.mpr ?_
    rintro A hA ⟨u, hu_orph, rfl⟩
    have hu_in_A : u ∈ V((oneVertexSociety u : Society α β).G) := mem_singleton u
    exact hu_orph.2 (mem_iUnion₂.mpr ⟨oneVertexSociety u, hA, hu_in_A⟩)
  -- Construct small discs `D_orph u` for `u ∈ Orphans`
  obtain ⟨c, c', hc, hc', hmc, hmc', hleft, hright, hΔ₂_eq, hbdΔ_eq, hbdΔ₂_eq⟩ :=
    exists_collar_coords hS hΔ hΔ₂ hin
  let Pairs : Set (α × α) := {p : α × α | p.1 ∈ Orphans ∧ p.2 ∈ Orphans ∧ p.1 ≠ p.2}
  have hPairs_fin : Pairs.Finite :=
    (hOrphans_fin.prod hOrphans_fin).subset fun _ hp => ⟨hp.1, hp.2.1⟩
  have hPairs_pos : ∀ p ∈ Pairs, 0 < dist (c' (α_pt p.1)) (c' (α_pt p.2)) / 2 := by
    rintro ⟨u, v⟩ ⟨hu, hv, huv⟩
    refine half_pos (dist_pos.mpr fun hEq => huv ?_)
    have hpt_eq : α_pt u = α_pt v := by
      have h1 := congrArg c hEq
      rwa [hright hu.1.2.1, hright hv.1.2.1] at h1
    exact hArr.injOn_pts hu.1.1 hv.1.1 hpt_eq
  obtain ⟨ε, hε_pos, hε_lt⟩ := exists_pos_lt_of_finite hPairs_fin hPairs_pos
  let K_cyl : Set S := ⋃ A ∈ S_seg_cyl, α_disc A
  have hScyl_fin : S_seg_cyl.Finite := hSeg.1.finite.subset fun _ h => h.1
  have hK_cl : IsClosed K_cyl :=
    hScyl_fin.isClosed_biUnion fun A hA => (hArr.isClosedDisc A hA.1).1.isClosed
  have hH'V_fin : H'.V.Finite := H.finite_V.subset (hV_H' ▸ inter_subset_left)
  let U_open : α → Set S := fun u => (K_cyl ∪ (H'.V \ {α_pt u}))ᶜ
  have hU_open : ∀ u, IsOpen (U_open u) := fun u =>
    (hK_cl.union ((hH'V_fin.subset sdiff_subset).isClosed)).isOpen_compl
  have hu_in_U : ∀ u ∈ Orphans, α_pt u ∈ U_open u := by
    rintro u hu (hK | ⟨_, hne⟩)
    · obtain ⟨A, hA, huA⟩ := mem_iUnion₂.mp hK
      exact hOrphans_not_in_K u hu A hA huA
    · exact hne rfl
  have hex_D : ∀ u : α, ∃ D : Set S,
      u ∈ Orphans →
        IsClosedDisc D ∧ D ⊆ Cyl ∩ U_open u ∧ α_pt u ∈ subBd D ∧
        ∀ x ∈ D, dist (c' x) (c' (α_pt u)) < ε := by
    intro u
    by_cases hu : u ∈ Orphans
    · obtain ⟨D, hD⟩ := exists_small_collar_disc hS hΔ hΔ₂ hc hc' hmc hmc' hleft hright
        hΔ₂_eq hbdΔ_eq hbdΔ₂_eq (hOrphans_bd u hu) (hU_open u) (hu_in_U u hu) hε_pos
      exact ⟨D, fun _ => hD⟩
    · exact ⟨∅, fun h => (hu h).elim⟩
  choose D_orph hD_orph using hex_D
  let α_disc_1 : Society α β → Set S := fun S₀ =>
    if h : ∃ u ∈ Orphans, S₀ = oneVertexSociety u then D_orph h.choose else α_disc S₀
  have hα_disc_1_cyl : ∀ {A : Society α β}, A ∈ S_seg_cyl → α_disc_1 A = α_disc A := by
    intro A hA
    have hnot : ¬ ∃ u ∈ Orphans, A = oneVertexSociety u := by
      rintro ⟨u, hu, rfl⟩
      exact Set.disjoint_left.mp hDisj_cyl_orph hA ⟨u, hu, rfl⟩
    simp [α_disc_1, hnot]
  have hα_disc_1_orph : ∀ {u : α}, u ∈ Orphans → α_disc_1 (oneVertexSociety u) = D_orph u := by
    intro u hu
    have hex : ∃ v ∈ Orphans, (oneVertexSociety u : Society α β) = oneVertexSociety v :=
      ⟨u, hu, rfl⟩
    have hchoose : hex.choose = u := oneVertexSociety_inj hex.choose_spec.2.symm
    dsimp only [α_disc_1]
    rw [dite_eq_left_of_eq_true (eq_true hex), hchoose]
  have hD_orph_disj : ∀ {u₁ u₂ : α}, u₁ ∈ Orphans → u₂ ∈ Orphans → u₁ ≠ u₂ →
      Disjoint (D_orph u₁) (D_orph u₂) := by
    exact small_orphan_discs_are_pairwise_disjoint (S := S) (α := α) (α_pt := α_pt) Cyl Orphans c'
      ε hε_lt U_open D_orph hD_orph
  -- Helper facts about `N.G` and `segregationVertices S_seg_1`
  have hEP_Cyl : E(N.G) = ⋃ A ∈ S_seg_cyl, E(A.G) := by
    rw [hN_G]
    ext e
    simp only [arrangementPullbackGraph, edgeSet_restrict, mem_inter_iff, edgeSet_induce]
    refine ⟨fun h => h.2, fun he => ⟨?_, he⟩⟩
    obtain ⟨A, hA, heA⟩ := mem_iUnion₂.mp he
    obtain ⟨u, v, huv⟩ := A.G.exists_isLink_of_mem_edgeSet heA
    have huv_G' : G'.IsLink e u v := huv.mono (hSeg.1.le A hA.1)
    exact ⟨u, v, huv_G',
      ⟨Or.inl (mem_iUnion₂.mpr ⟨A, hA, huv.left_mem⟩), huv_G'.left_mem⟩,
      ⟨Or.inl (mem_iUnion₂.mpr ⟨A, hA, huv.right_mem⟩), huv_G'.right_mem⟩⟩
  have hNG_le_G' : N.G ≤ G' :=
    hN_G ▸ Graph.restrict_le.trans (G'.induce_le inter_subset_right)
  have hSeg1_le : ∀ S₀ ∈ S_seg_1, S₀.G ≤ N.G := by
    rintro S₀ (hA | ⟨u, hu, rfl⟩)
    · refine ⟨?_, fun e x y hlink => ?_⟩
      · intro v hv
        rw [hN_G, arrangementPullbackGraph, vertexSet_restrict, vertexSet_induce]
        exact ⟨Or.inl (mem_iUnion₂.mpr ⟨S₀, hA, hv⟩), (hSeg.1.le S₀ hA.1).vertexSet_mono hv⟩
      · have he : e ∈ E(N.G) := hEP_Cyl ▸ mem_iUnion₂.mpr ⟨S₀, hA, hlink.edge_mem⟩
        exact (hNG_le_G'.isLink_iff he).mpr (hlink.mono (hSeg.1.le S₀ hA.1))
    · refine ⟨?_, fun _ _ _ h => h.elim⟩
      rintro x (rfl : x = u)
      rw [hN_G, arrangementPullbackGraph, vertexSet_restrict, vertexSet_induce]
      exact ⟨Or.inr hu.1, hseg_sub_G' hu.1.1⟩
  have hseg_in_bar : ∀ {A : Society α β}, A ∈ S_seg →
      ∀ {x : α}, x ∈ V(A.G) → x ∈ segregationVertices S_seg → x ∈ A.Ω.bar := by
    intro A hA x hxA hx_seg
    obtain ⟨A', hA', hx_bar'⟩ := mem_iUnion₂.mp hx_seg
    by_cases hEq : A = A'
    · subst hEq; exact hx_bar'
    · exact (hSeg.1.vertex_inter_subset A hA A' hA' hEq ⟨hxA, A'.bar_subset hx_bar'⟩).1
  have hseg1_sub_seg : segregationVertices S_seg_1 ⊆ segregationVertices S_seg := by
    intro v hv
    obtain ⟨S₀, hS₀, hv_bar⟩ := mem_iUnion₂.mp hv
    rcases hS₀ with hA | ⟨u, hu, rfl⟩
    · exact mem_biUnion hA.1 hv_bar
    · change v ∈ ({u} : Set α) at hv_bar
      rw [mem_singleton_iff] at hv_bar
      exact hv_bar ▸ hu.1.1
  have hseg1_cyl_iff : ∀ {v : α}, α_pt v ∈ Cyl →
      (v ∈ segregationVertices S_seg_1 ↔ v ∈ segregationVertices S_seg) := by
    intro v hvCyl
    refine ⟨fun hv1 => hseg1_sub_seg hv1, fun hv_seg => ?_⟩
    by_cases hv_in : v ∈ ⋃ A ∈ S_seg_cyl, V(A.G)
    · obtain ⟨A, hA, hvA⟩ := mem_iUnion₂.mp hv_in
      exact mem_biUnion (Or.inl hA) (hseg_in_bar hA.1 hvA hv_seg)
    · have hv_orph : v ∈ Orphans := ⟨⟨hv_seg, hvCyl⟩, hv_in⟩
      exact mem_biUnion (Or.inr ⟨v, hv_orph, rfl⟩) (by simp)
  have hcylSeg : IsThreeSegregation N.G S_seg_1 := by
    exact cylindrical_cells_and_orphans_form_three_segregation (S := S) (α := α) (β := β) (G' :=
      G') (S_seg := S_seg) (α_disc := α_disc) (α_pt := α_pt) (Δ := Δ) (Δ₂ := Δ₂) (N := N) hSeg
      hN_G Cyl rfl Orphans rfl hOrphans_fin hScyl_fin hEP_Cyl hSeg1_le
  have hcylArr : IsSurfaceArrangement S_seg_1 α_disc_1 α_pt := by
    exact cylindrical_cells_and_orphans_form_arrangement (S := S) (α := α) (β := β) hS (S_seg :=
      S_seg) (α_disc := α_disc) (α_pt := α_pt) hArr Cyl H' Orphans c' ε D_orph hD_orph α_disc_1
      hα_disc_1_cyl hα_disc_1_orph hD_orph_disj hseg1_sub_seg
  have hcylComp : IsCompatibleWith N.G H' η_1 S_seg_1 α_disc_1 α_pt := by
    exact cylindrical_arrangement_is_compatible (S := S) (α := α) (β := β) hS (G' := G') (H := H)
      (η' := η') (S_seg := S_seg) (α_disc := α_disc) (α_pt := α_pt) (Δ := Δ) (Δ₂ := Δ₂) (N := N)
      (η_1 := η_1) hSeg hArr hComp hΔ hΔ₂ hNorm_Δ hNorm_Δ₂ hη_1_v hη_1_e hV_H' hU_H' hE_H'
      Orphans rfl c' ε D_orph hD_orph α_disc_1 hα_disc_1_cyl hα_disc_1_orph hseg1_sub_seg
  refine ⟨S_seg_1, α_disc_1, hcylSeg, hcylArr, hcylComp, ?_, ?_, ?_⟩
  · -- 4. `∀ S₀ ∈ S_seg_1, α_disc_1 S₀ ⊆ Cyl`
    rintro S₀ (hA | ⟨u, hu, rfl⟩)
    · rw [hα_disc_1_cyl hA]
      exact hA.2
    · rw [hα_disc_1_orph hu]
      exact fun x hx => ((hD_orph u hu).2.1 hx).1
  · -- 5. `IsPullbackPerm S_seg_1 α_pt (discBd Δ) N.Ω`
    obtain ⟨hCyl_cl, hCyl_bd, _⟩ := cylinder_closed_and_subBd hS hΔ hΔ₂ hin
    have hbdΔ_sub_Cyl : subBd Δ ⊆ Cyl := by
      intro x hx
      have hx_bd : x ∈ subBd Cyl := hCyl_bd.symm ▸ Or.inl hx
      exact hCyl_cl.closure_subset_iff.mpr Subset.rfl hx_bd.1
    rw [← IsClosedDisc.subBd_eq_discBd hS hΔ]
    refine ⟨?_, hPull_Ω.2⟩
    rw [hPull_Ω.1]
    ext v
    simp only [mem_sep_iff]
    exact ⟨fun ⟨hv, hbd⟩ => ⟨(hseg1_cyl_iff (hbdΔ_sub_Cyl hbd)).mpr hv, hbd⟩,
      fun ⟨hv, hbd⟩ => ⟨(hseg1_cyl_iff (hbdΔ_sub_Cyl hbd)).mp hv, hbd⟩⟩
  · -- 6. `IsPullbackPerm S_seg_1 α_pt (discBd Δ₂) N.Ω₀`
    obtain ⟨hCyl_cl, hCyl_bd, _⟩ := cylinder_closed_and_subBd hS hΔ hΔ₂ hin
    have hbdΔ₂_sub_Cyl : subBd Δ₂ ⊆ Cyl := by
      intro x hx
      have hx_bd : x ∈ subBd Cyl := hCyl_bd.symm ▸ Or.inr hx
      exact hCyl_cl.closure_subset_iff.mpr Subset.rfl hx_bd.1
    rw [← IsClosedDisc.subBd_eq_discBd hS hΔ₂]
    refine ⟨?_, hPull_Ω₀.2⟩
    rw [hPull_Ω₀.1]
    ext v
    simp only [mem_sep_iff]
    exact ⟨fun ⟨hv, hbd⟩ => ⟨(hseg1_cyl_iff (hbdΔ₂_sub_Cyl hbd)).mpr hv, hbd⟩,
      fun ⟨hv, hbd⟩ => ⟨(hseg1_cyl_iff (hbdΔ₂_sub_Cyl hbd)).mp hv, hbd⟩⟩

/-! ## 6. Assembling the Cylinder Rerouting Step of (9.6) from (8.4) -/

private theorem inner_society_is_subgraph_of_replaced_graph
    {S : Type w}
    {α : Type u}
    {β : Type v}
    {G_amb : Graph α β}
    {G : Graph α β}
    {G' : Graph α β}
    {J : Graph α β}
    {S_seg : Set (Society α β)}
    {α_disc : Society α β → Set S}
    {α_pt : α → S}
    (hG_eq : G = subgraphUnion G_amb G' J)
    {Δ : Set S}
    {localSociety : Society α β}
    (hsoc_star_G : localSociety.G = subgraphUnion G_amb J (arrangementPullbackGraph G' S_seg α_disc
      α_pt Δ))
    (hJ_le : J ≤ G_amb)
    (hG'_le : G' ≤ G_amb)
    (hP_Δ_le_G' : arrangementPullbackGraph G' S_seg α_disc α_pt Δ ≤ G')
    (hP_Δ_le_amb : arrangementPullbackGraph G' S_seg α_disc α_pt Δ ≤ G_amb)
    (hstar_le_amb : localSociety.G ≤ G_amb)
    (hG_le_amb : G ≤ G_amb) :
    localSociety.G ≤ G := by
  refine ⟨?_, fun e x y hlink => ?_⟩
  · intro x hx
    rw [hsoc_star_G, vertexSet_subgraphUnion] at hx
    rw [hG_eq, vertexSet_subgraphUnion]
    exact hx.elim Or.inr (fun hxP => Or.inl (hP_Δ_le_G'.vertexSet_mono hxP))
  · have he_G : e ∈ E(G) := by
      have he_star := hlink.edge_mem
      rw [hsoc_star_G, edgeSet_subgraphUnion hJ_le hP_Δ_le_amb] at he_star
      rw [hG_eq, edgeSet_subgraphUnion hG'_le hJ_le]
      exact he_star.elim Or.inr (fun heP => Or.inl (hP_Δ_le_G'.edgeSet_mono heP))
    exact (hG_le_amb.isLink_iff he_G).mpr (hlink.mono hstar_le_amb)

private theorem rerouted_crooked_transaction_extends_to_replacement_society
    {α : Type u}
    {β : Type v}
    {clearedSociety : Society α β}
    (S_G0 : Society α β)
    (P_set : Set (Graph α β))
    (hΩ : clearedSociety.Ω = S_G0.Ω)
    (hCr_G0 : S_G0.IsCrookedTransaction P_set)
    (hOmegaPath_iff : ∀ p ∈ P_set, ∀ (u v : α), clearedSociety.IsOmegaPathWithEnds p u v ↔
      S_G0.IsOmegaPathWithEnds p u v)
    (hEnds_eq_G0 : clearedSociety.transactionEnds P_set = S_G0.transactionEnds P_set) :
    clearedSociety.IsCrookedTransaction P_set := by
  obtain ⟨⟨A, B, ⟨hDisj_paths, hPairwise⟩, hFence, hAB⟩, hNoPeriph⟩ := hCr_G0
  refine ⟨⟨A, B, ⟨fun p hp => ?_, hPairwise⟩, hΩ.symm ▸ hFence, fun p hp => ?_⟩, fun p hp hPer
    => ?_⟩
  · obtain ⟨u, v, huv⟩ := hDisj_paths p hp
    exact ⟨u, v, (hOmegaPath_iff p hp u v).mpr huv⟩
  · obtain ⟨u, hu, v, hv, huv⟩ := hAB p hp
    exact ⟨u, hu, v, hv, (hOmegaPath_iff p hp u v).mpr huv⟩
  · obtain ⟨_, u, v, huv, hDisj_int⟩ := hPer
    exact hNoPeriph p hp ⟨hp, u, v, (hOmegaPath_iff p hp u v).mp huv, hEnds_eq_G0 ▸ hΩ ▸ hDisj_int⟩

private theorem rerouted_path_meets_cleared_drawing_only_at_ends
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    {α : Type u}
    {β : Type v}
    {G_amb : Graph α β}
    {G' : Graph α β}
    {J : Graph α β}
    {H : Drawing S}
    {η : SpanEmbedding H G_amb}
    {η' : SpanEmbedding H G'}
    {beta : ℕ}
    {d : Set S → Set S → ℕ}
    {z : Set S}
    {S_seg : Set (Society α β)}
    {α_disc : Society α β → Set S}
    {α_pt : α → S}
    (hη'_v : ∀ v ∈ H.V, η'.vMap v = η.vMap v)
    (hJ_dist : ∀ v ∈ H.V, η.vMap v ∈ V(J) → d z {v} < beta)
    (hComp : IsCompatibleWith G' H η' S_seg α_disc α_pt)
    {Λ : Set S}
    {Δ : Set S}
    {clearedEmbedding : SpanEmbedding (clearedSubdrawing H Λ) G_amb}
    {clearedSociety : Society α β}
    {localSociety : Society α β}
    (hη_Λ_v : ∀ v ∈ (clearedSubdrawing H Λ).V, clearedEmbedding.vMap v = η.vMap v)
    (hsoc_star_G : localSociety.G = subgraphUnion G_amb J (arrangementPullbackGraph G' S_seg α_disc
      α_pt Δ))
    {Λ_C₂ : Set S}
    {Δ₂ : Set S}
    (hcl_C₂_sub : closure Λ_C₂ ⊆ Λ)
    (hΔ₂_sub_cl_C₂ : Δ₂ ⊆ closure Λ_C₂)
    (Δ₀ : Set S)
    (hΔ₀_sub_Λ : Δ₀ ⊆ Λ)
    (hΔ₀_atoms : ∀ x ∈ H.A, d z x < beta → x ⊆ Δ₀)
    (hdiff_E₁ : closure Λ \ ((H.interSet (Δ \ discInt Δ₂)).interSet (subBd Λ)).U = Λ)
    (N : Neighborhood α β)
    (η_1 : SpanEmbedding (H.interSet (Δ \ discInt Δ₂)) N.G)
    (hη_1_v : ∀ v ∈ (H.interSet (Δ \ discInt Δ₂)).V, η_1.vMap v = η'.vMap v)
    (hV_H' : (H.interSet (Δ \ discInt Δ₂)).V = H.V ∩ (Δ \ discInt Δ₂))
    (hCleared_V_sub : (clearedSubdrawing H Λ).V ⊆ H.V ∩ (univ \ Λ))
    (p : Graph α β)
    (a' : α)
    (b' : α)
    (hp_a'b' : clearedSociety.IsOmegaPathWithEnds p a' b')
    (a : α)
    (b : α)
    (hv_H' : ∀ v ∈ (H.interSet (Δ \ discInt Δ₂)).V, η_1.vMap v ∈ V(p) → η_1.vMap v = a ∨ η_1.vMap
      v = b ∨ v ∈ closure Λ \ ((H.interSet (Δ \ discInt Δ₂)).interSet (subBd Λ)).U)
    (hp_le_star : p ≤ localSociety.G)
    (ha'_ab : a' = a ∨ a' = b)
    (hb'_ab : b' = a ∨ b' = b)
    (hpair_eq : ({a', b'} : Set α) = {a, b})
    (hbar_sub_img : clearedSociety.Ω.bar ⊆ V(clearedEmbedding.imageGraph)) :
    V(p) ∩ V(clearedEmbedding.imageGraph) = {a', b'} := by
  refine Subset.antisymm ?_ ?_
  · rintro w ⟨hw_p, hw_img⟩
    obtain ⟨v, hv_cl, rfl⟩ := clearedEmbedding.bijOn_v.surjOn hw_img
    obtain ⟨hvH, hv_not_Λ⟩ := hCleared_V_sub hv_cl
    have hw_star : clearedEmbedding.vMap v ∈ V(localSociety.G) := hp_le_star.vertexSet_mono hw_p
    rw [hη_Λ_v v hv_cl, hsoc_star_G, vertexSet_subgraphUnion] at hw_star
    have hv_Δ : v ∈ Δ := by
      rcases hw_star with hw_J | hw_PΔ
      · exfalso
        have hv_atom : ({v} : Set S) ∈ H.A := Or.inl (Or.inl ⟨v, hvH, rfl⟩)
        have hv_in_Λ : v ∈ Λ :=
          hΔ₀_sub_Λ (hΔ₀_atoms {v} hv_atom (hJ_dist v hvH hw_J) (mem_singleton v))
        exact hv_not_Λ.2 hv_in_Λ
      · rw [← hη'_v v hvH] at hw_PΔ
        simp only [arrangementPullbackGraph, vertexSet_restrict, vertexSet_induce,
          mem_inter_iff, mem_union, mem_iUnion, mem_sep_iff] at hw_PΔ
        rcases hw_PΔ.1 with ⟨A, ⟨hA, hA_Δ⟩, hvA⟩ | ⟨hv_seg, hv_pt_Δ⟩
        · exact hA_Δ ((hComp.inter_V_iff A hA v hvH).mpr hvA)
        · rwa [hComp.pt_eq v hvH hv_seg] at hv_pt_Δ
    have hv_not_int₂ : v ∉ discInt Δ₂ :=
      fun hv_int₂ => hv_not_Λ.2 (hcl_C₂_sub (hΔ₂_sub_cl_C₂ hv_int₂.1))
    have hv_H'V : v ∈ (H.interSet (Δ \ discInt Δ₂)).V := hV_H'.symm ▸ ⟨hvH, hv_Δ, hv_not_int₂⟩
    have hw_vMap1 : η_1.vMap v = clearedEmbedding.vMap v := by
      rw [hη_1_v v hv_H'V, hη'_v v hvH, hη_Λ_v v hv_cl]
    have hv_res := hv_H' v hv_H'V (hw_vMap1.symm ▸ hw_p)
    rw [hw_vMap1, hdiff_E₁] at hv_res
    rw [hpair_eq]
    rcases hv_res with h1 | h2 | hv_Λ
    · exact Or.inl h1
    · exact Or.inr h2
    · exact (hv_not_Λ.2 hv_Λ).elim
  · rintro w (rfl | rfl)
    · exact ⟨hp_a'b'.1.left_mem, hbar_sub_img hp_a'b'.2.2.1⟩
    · exact ⟨hp_a'b'.1.right_mem, hbar_sub_img hp_a'b'.2.2.2⟩

private theorem rerouted_path_avoids_cleared_drawing_edges
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    {α : Type u}
    {β : Type v}
    {G_amb : Graph α β}
    {G' : Graph α β}
    {J : Graph α β}
    {B_rem : Set (Graph α β)}
    {H : Drawing S}
    {η : SpanEmbedding H G_amb}
    {η' : SpanEmbedding H G'}
    {S_seg : Set (Society α β)}
    {α_disc : Society α β → Set S}
    {α_pt : α → S}
    (hG'_eq : G' = subgraphSUnion G_amb {η.imageGraph, subgraphSUnion G_amb B_rem})
    (hη'_e : ∀ e ∈ H.E, η'.eMap e = η.eMap e)
    (hComp : IsCompatibleWith G' H η' S_seg α_disc α_pt)
    {Λ : Set S}
    {Δ : Set S}
    {clearedEmbedding : SpanEmbedding (clearedSubdrawing H Λ) G_amb}
    {localSociety : Society α β}
    (hη_Λ_e : ∀ e ∈ (clearedSubdrawing H Λ).E, clearedEmbedding.eMap e = η.eMap e)
    (hsoc_star_G : localSociety.G = subgraphUnion G_amb J (arrangementPullbackGraph G' S_seg α_disc
      α_pt Δ))
    {Λ_C₂ : Set S}
    {Δ₂ : Set S}
    (hcl_C₂_sub : closure Λ_C₂ ⊆ Λ)
    (hΔ₂_sub_cl_C₂ : Δ₂ ⊆ closure Λ_C₂)
    (hdiff_E₁ : closure Λ \ ((H.interSet (Δ \ discInt Δ₂)).interSet (subBd Λ)).U = Λ)
    (hJ_le : J ≤ G_amb)
    (hBrem_le : subgraphSUnion G_amb B_rem ≤ G_amb)
    (hDisj_E : Disjoint E(G') E(J))
    (N : Neighborhood α β)
    (η_1 : SpanEmbedding (H.interSet (Δ \ discInt Δ₂)) N.G)
    (hη_1_e : ∀ e ∈ (H.interSet (Δ \ discInt Δ₂)).E, η_1.eMap e = η'.eMap e)
    (hE_H' : (H.interSet (Δ \ discInt Δ₂)).E = {e | e ∈ H.E ∧ e ⊆ Δ \ discInt Δ₂})
    (hP_Δ_le_amb : arrangementPullbackGraph G' S_seg α_disc α_pt Δ ≤ G_amb)
    (hCleared_E_sub : (clearedSubdrawing H Λ).E ⊆ {e | e ∈ H.E ∧ e ⊆ univ \ Λ})
    (p : Graph α β)
    (he_H' : ∀ e ∈ (H.interSet (Δ \ discInt Δ₂)).E, η_1.eMap e ∈ E(p) → e ⊆ closure Λ \
      ((H.interSet (Δ \ discInt Δ₂)).interSet (subBd Λ)).U)
    (hp_le_star : p ≤ localSociety.G) :
    Disjoint E(p) E(clearedEmbedding.imageGraph) := by
  refine Set.disjoint_left.mpr fun b_edge hb_p hb_img => ?_
  obtain ⟨e, he_cl, rfl⟩ := clearedEmbedding.bijOn_e.surjOn hb_img
  obtain ⟨heH, he_not_Λ⟩ := hCleared_E_sub he_cl
  have hb_star : clearedEmbedding.eMap e ∈ E(localSociety.G) := hp_le_star.edgeSet_mono hb_p
  rw [hη_Λ_e e he_cl, hsoc_star_G, edgeSet_subgraphUnion hJ_le hP_Δ_le_amb] at hb_star
  have he_Δ : e ⊆ Δ := by
    rcases hb_star with hb_J | hb_PΔ
    · exfalso
      have hη_le_G' : η.imageGraph ≤ G' := by
        rw [hG'_eq]
        refine le_subgraphSUnion ?_ (Or.inl rfl)
        rintro K (rfl | rfl)
        · exact η.imageGraph_le
        · exact hBrem_le
      exact Set.disjoint_left.mp hDisj_E
        (hη_le_G'.edgeSet_mono (η.bijOn_e.mapsTo heH)) hb_J
    · rw [← hη'_e e heH] at hb_PΔ
      simp only [arrangementPullbackGraph, edgeSet_restrict, mem_inter_iff,
        mem_iUnion, mem_sep_iff] at hb_PΔ
      obtain ⟨A, ⟨hA, hA_Δ⟩, heA⟩ := hb_PΔ.2
      exact ((hComp.inter_E_iff A hA e heH).mpr heA).trans hA_Δ
  have he_Cyl : e ⊆ Δ \ discInt Δ₂ := by
    intro x hxe
    refine ⟨he_Δ hxe, fun hx_int₂ => ?_⟩
    exact (he_not_Λ hxe).2 (hcl_C₂_sub (hΔ₂_sub_cl_C₂ hx_int₂.1))
  have he_H'E : e ∈ (H.interSet (Δ \ discInt Δ₂)).E := hE_H'.symm ▸ ⟨heH, he_Cyl⟩
  have hb_eMap1 : η_1.eMap e = clearedEmbedding.eMap e := by
    rw [hη_1_e e he_H'E, hη'_e e heH, hη_Λ_e e he_cl]
  have he_sub_Λ : e ⊆ Λ := hdiff_E₁ ▸ he_H' e he_H'E (hb_eMap1.symm ▸ hb_p)
  obtain ⟨x₀, hx₀⟩ := heH.1
  exact (he_not_Λ hx₀).2 (he_sub_Λ hx₀)

/-- The cylinder rerouting step of Graph Minors XIV, (9.6) (pages 48–49), proved from (8.4)
(`Theorem84DiscStatement`). -/
theorem cylinder_reroute_9_6 [T2Space S] {α : Type u} {β : Type v}
    {G_amb G G' J : Graph α β} {B_J B_rem : Set (Graph α β)}
    {H : Drawing S} {η : SpanEmbedding H G_amb} {η' : SpanEmbedding H G'}
    {θ π beta : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {z : Set S}
    {S_seg : Set (Society α β)} {α_disc : Society α β → Set S} {α_pt : α → S}
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    (hV_fin : V(G_amb).Finite) (hE_fin : E(G_amb).Finite)
    (hRig : IsRigid H)
    (hπ1 : π ≠ 1) (hπ3 : π ≠ 3) (hbeta : 2 * π + 8 ≤ beta)
    (hB_J : ∀ B ∈ B_J, IsBridge G_amb η.imageGraph B)
    (hB_rem : ∀ B ∈ B_rem, IsBridge G_amb η.imageGraph B)
    (hDisj_B : Disjoint B_J B_rem)
    (hJ_eq : J = subgraphSUnion G_amb B_J)
    (hG'_eq : G' = subgraphSUnion G_amb {η.imageGraph, subgraphSUnion G_amb B_rem})
    (hG_eq : G = subgraphUnion G_amb G' J)
    (hη'_v : ∀ v ∈ H.V, η'.vMap v = η.vMap v)
    (hη'_e : ∀ e ∈ H.E, η'.eMap e = η.eMap e)
    (hJ_dist : ∀ v ∈ H.V, η.vMap v ∈ V(J) → d z {v} < beta)
    (hSeg : IsThreeSegregation G' S_seg)
    (hArr : IsSurfaceArrangement S_seg α_disc α_pt)
    (hComp : IsCompatibleWith G' H η' S_seg α_disc α_pt)
    {Λ Δ : Set S} {C C_out : Drawing S} {X_bf : Set S}
    {clearedEmbedding : SpanEmbedding (clearedSubdrawing H Λ) G_amb}
    {clearedSociety localSociety : Society α β} {inv_v : α → S}
    (hBf : IsBattlefield H T d θ beta z Λ C X_bf)
    (hΔ_disc : IsClosedDisc Δ)
    (hNorm_Δ : IsArrangementNormal S_seg α_disc α_pt (subBd Δ))
    (hclΛ_sub_Δ : closure Λ ⊆ Δ)
    (hCout_cir : C_out.IsCircuit)
    (hCout_sub : C_out.IsSubdrawing (H.interSet (closure (univ \ Δ))))
    (hη_Λ_v : ∀ v ∈ (clearedSubdrawing H Λ).V, clearedEmbedding.vMap v = η.vMap v)
    (hη_Λ_e : ∀ e ∈ (clearedSubdrawing H Λ).E, clearedEmbedding.eMap e = η.eMap e)
    (hsoc_Λ_G : clearedSociety.G = G)
    (hsoc_Λ_bar : clearedSociety.Ω.bar = clearedEmbedding.vMap '' ((clearedSubdrawing H Λ).V ∩
      subBd Λ))
    (hinv_v_prop : ∀ x ∈ clearedSociety.Ω.bar,
      inv_v x ∈ (clearedSubdrawing H Λ).V ∩ subBd Λ ∧ clearedEmbedding.vMap (inv_v x) = x)
    (hΩ_Λ_nat : IsNaturalOrderFrom inv_v clearedSociety.Ω (subBd Λ))
    (hsoc_star_G : localSociety.G = subgraphUnion G_amb J (arrangementPullbackGraph G' S_seg α_disc
      α_pt Δ))
    (hsoc_star_Ω : IsPullbackPerm S_seg α_pt (subBd Δ) localSociety.Ω)
    (hCr_star : ∃ P_set : Set (Graph α β), localSociety.IsCrookedTransaction P_set ∧ π
      ≤ P_set.ncard)
    {C₂ : Drawing S} {Λ_C₂ F₂ Δ₂ : Set S}
    (hC₂H : C₂.IsSubdrawing H) (hC₂ : C₂.IsCircuit)
    (hOpen_C₂ : IsOpenDisc Λ_C₂) (hcl_C₂_sub : closure Λ_C₂ ⊆ Λ)
    (hcl_C₂_disc : IsClosedDisc (closure Λ_C₂))
    (hbd_cl_C₂ : subBd (closure Λ_C₂) = C₂.U)
    (hdiff_C₂ : closure Λ_C₂ \ C₂.U = Λ_C₂)
    (hdist_C₂ : beta / 2 ≤ regionalDistance H (closure Λ_C₂) (subBd Λ))
    (hF₂_norm : IsArrangementNormal S_seg α_disc α_pt F₂)
    (hΔ₂_disc : IsClosedDisc Δ₂) (hbd_Δ₂ : subBd Δ₂ = F₂)
    (hΔ₂_sub_cl_C₂ : Δ₂ ⊆ closure Λ_C₂)
    (hD₀_sub_Δ₂ : discIns (closure Λ) C ⊆ Δ₂)
    (hΔ₂_atoms : ∀ x ∈ H.A, d z x < beta → x ⊆ Δ₂ \ subBd Δ₂) :
    ∃ P_set : Set (Graph α β),
      clearedSociety.IsCrookedTransaction P_set ∧
      π ≤ P_set.ncard ∧
      clearedSociety.transactionEnds P_set ⊆ clearedEmbedding.vMap '' X_bf ∧
      ∀ P ∈ P_set, ∀ a b : α,
        clearedSociety.IsOmegaPathWithEnds P a b →
        IsHPathWithEnds G_amb clearedEmbedding.imageGraph P a b := by
  have : ConnectedSpace S := hConn
  have hZone : IsLambdaZoneAround H d (3 * beta + 3) z Λ := hBf.isZone
  obtain ⟨hC_cir, hC_sub, hCU_sub_Λ, P_bf, hP_bf, hDisj_bf⟩ := hBf.circuit_and_paths
  obtain ⟨hX_bf_sub, _, _, _, _, _⟩ := hBf.isFree_X
  obtain ⟨Δ₀, _, hΔ₀_sub_Λ, _, hΔ₀_atoms⟩ := hBf.openDisc_includes
  have hNorm_Δ₂ : IsArrangementNormal S_seg α_disc α_pt (subBd Δ₂) := hbd_Δ₂ ▸ hF₂_norm
  have hΔ₂_sub_diff : Δ₂ ⊆ Δ \ subBd Δ := by
    have hΛ_sub_int : Λ ⊆ Δ \ subBd Δ := by
      intro x hxΛ
      refine ⟨hclΛ_sub_Δ (subset_closure hxΛ), fun hx_bd => ?_⟩
      obtain ⟨y, hyΛ, hyn⟩ := mem_closure_iff.mp hx_bd.2 Λ hZone.isOpenDisc.1 hxΛ
      exact hyn.2 (hclΛ_sub_Δ (subset_closure hyΛ))
    exact hΔ₂_sub_cl_C₂.trans (hcl_C₂_sub.trans hΛ_sub_int)
  have hCU_sub_Δ₂ : C.U ⊆ Δ₂ := by
    obtain ⟨⟨_, _, hD₀_bd⟩, _⟩ :=
      discIns_spec hZone.isClosedDisc_closure hC_cir (hCU_sub_Λ.trans subset_closure)
    exact (hD₀_bd ▸ Surface.discBd_subset (discIns (closure Λ) C)).trans hD₀_sub_Δ₂
  -- Step 1: Rigidity of `H' = H.interSet (Δ \ discInt Δ₂)`
  have hRig_H' : IsRigidIn (H.interSet (Δ \ discInt Δ₂)) (Δ \ discInt Δ₂) :=
    isRigidIn_cylinder_9_6 hS hRig hSeg hArr hComp hΔ_disc hΔ₂_disc hΔ₂_sub_diff
      hNorm_Δ hNorm_Δ₂ hCout_cir hCout_sub hC_cir hC_sub hCU_sub_Δ₂
  -- Step 2: Circuits `C₁` and `C₂` of `H'`
  obtain ⟨hC₁_cir, hC₁_sub, hC₂_cir, hC₂_sub, hbd_E₁, hbd_E₂,
      hdiff_E₁, hE₂_sub_diff, hC₁_V_eq, hC₁_V_cleared⟩ :=
    circuits_cylinder_9_6 hS hZone hΔ_disc hΔ₂_disc hclΛ_sub_Δ
      hC₂H hC₂ hcl_C₂_sub hcl_C₂_disc hbd_cl_C₂ hΔ₂_sub_cl_C₂
  -- Step 3: Regional distance in `H'`
  have hC₁_U_eq : ((H.interSet (Δ \ discInt Δ₂)).interSet (subBd Λ)).U = subBd Λ := by
    rw [← hbd_E₁]
    exact discBd_closure_eq_subBd hS hZone.isOpenDisc hZone.isOArc_bd hZone.isClosedDisc_closure
  have hDist_H' : π + 4 ≤
      regionalDistance (H.interSet (Δ \ discInt Δ₂)) C₂.U ((H.interSet (Δ \ discInt Δ₂)).interSet
        (subBd Λ)).U :=
    regionalDistance_cylinder_9_6 hS hSeg hArr hComp hΔ_disc hΔ₂_disc hNorm_Δ hNorm_Δ₂
      hZone.isOpenDisc hclΛ_sub_Δ hcl_C₂_sub hcl_C₂_disc hbd_cl_C₂ hΔ₂_sub_cl_C₂
      hC₁_cir hC₁_sub hC₁_U_eq hC₂_cir hC₂_sub hbeta hdist_C₂
  -- Step 4: Paths `P` in `H'.toGraph` from `X_bf` to `C₂.V`
  obtain ⟨hX_bf_C₁, P, hP_paths, hP_disj⟩ :=
    exists_cylinder_paths_9_6 hS hZone.isOpenDisc hclΛ_sub_Δ hΔ_disc hΔ₂_disc
      hOpen_C₂ hcl_C₂_sub hbd_cl_C₂ hdiff_C₂ hΔ₂_sub_cl_C₂ hCU_sub_Δ₂
      hC₁_V_eq hC₂H hX_bf_sub hbeta P_bf hP_bf hDisj_bf
  -- Step 5: Society composition `localSociety.IsComposition S₂ N` and 3-segregation `S_seg_1`
  have hJ_le : J ≤ G_amb := hJ_eq ▸ subgraphSUnion_le fun B hB => (hB_J B hB).2.1
  have hBrem_le : subgraphSUnion G_amb B_rem ≤ G_amb :=
    subgraphSUnion_le fun B hB => (hB_rem B hB).2.1
  have hG'_le : G' ≤ G_amb := by
    rw [hG'_eq]
    refine subgraphSUnion_le ?_
    rintro K (rfl | rfl)
    · exact η.imageGraph_le
    · exact hBrem_le
  obtain ⟨hDisj_E, hInter_V⟩ :=
    bridge_sUnion_disjoint_and_inter η.imageGraph_le hB_J hB_rem hDisj_B hJ_eq hG'_eq
  have hVJ_Δ₂ : ∀ v ∈ H.V, η.vMap v ∈ V(J) → v ∈ Δ₂ \ subBd Δ₂ := by
    intro v hvH hvJ
    have hv_atom : ({v} : Set S) ∈ H.A := Or.inl (Or.inl ⟨v, hvH, rfl⟩)
    exact hΔ₂_atoms {v} hv_atom (hJ_dist v hvH hvJ) (mem_singleton v)
  obtain ⟨S₂, N, η_1, _, hPull_S₂, hN_G, hN_Ω, hN_Ω₀, hComp_soc,
      hη_1_v, hη_1_e, hV_H', hU_H', hE_H'⟩ :=
    cylinder_composition_9_6 hS hV_fin hE_fin hJ_le hG'_le hDisj_E hInter_V hη'_v
      hSeg hArr hComp hΔ_disc hΔ₂_disc hΔ₂_sub_diff hNorm_Δ hNorm_Δ₂ hVJ_Δ₂
      hsoc_star_G hsoc_star_Ω
  obtain ⟨S_seg_1, α_disc_1, hSeg_1, hArr_1, hComp_1, hDisc_1_sub, hPull_1_Δ, hPull_1_Δ₂⟩ :=
    cylinder_segregation_9_6 hS hSeg hArr hComp hΔ_disc hΔ₂_disc hΔ₂_sub_diff
      hNorm_Δ hNorm_Δ₂ hN_G (hN_Ω ▸ hsoc_star_Ω) (hN_Ω₀ ▸ hPull_S₂)
      hη_1_v hη_1_e hV_H' hU_H' hE_H'
  -- Step 6: Construct `S_G0 = (localSociety.G, clearedSociety.Ω)` and apply
  -- `GraphMinor.GM14.theorem_8_4_proof.{u, v, w}`
  let H' := H.interSet (Δ \ discInt Δ₂)
  let C₁ := H'.interSet (subBd Λ)
  have hC₁_vMap_eq : ∀ v ∈ C₁.V, η_1.vMap v = clearedEmbedding.vMap v := by
    intro v hv
    have hv_H' : v ∈ H'.V := hC₁_sub.1 hv
    have hv_cl : v ∈ (clearedSubdrawing H Λ).V := (hC₁_V_cleared ▸ hv).1
    rw [hη_1_v v hv_H', hη'_v v (hV_H' ▸ hv_H').1, ← hη_Λ_v v hv_cl]
  have hbar_G0_eq : clearedSociety.Ω.bar = η_1.vMap '' C₁.V := by
    rw [hsoc_Λ_bar, ← hC₁_V_cleared]
    exact image_congr fun v hv => (hC₁_vMap_eq v hv).symm
  have hPCyl_le_star : N.G ≤ localSociety.G := hComp_soc.1.1.2.1
  have hbar_sub_star : clearedSociety.Ω.bar ⊆ V(localSociety.G) := by
    rw [hbar_G0_eq]
    rintro _ ⟨v, hvC₁, rfl⟩
    exact hPCyl_le_star.vertexSet_mono
      (η_1.imageGraph_le.vertexSet_mono (η_1.bijOn_v.mapsTo (hC₁_sub.1 hvC₁)))
  let S_G0 : Society α β :=
    ⟨localSociety.G, clearedSociety.Ω, localSociety.finite_V, localSociety.finite_E, hbar_sub_star⟩
  have hinv_v_C₁ : ∀ v ∈ C₁.V, inv_v (η_1.vMap v) = v := by
    intro v hv
    rw [hC₁_vMap_eq v hv]
    have hv_cl : v ∈ (clearedSubdrawing H Λ).V ∩ subBd Λ := hC₁_V_cleared ▸ hv
    have hx_bar : clearedEmbedding.vMap v ∈ clearedSociety.Ω.bar := hsoc_Λ_bar ▸ mem_image_of_mem
      clearedEmbedding.vMap hv_cl
    obtain ⟨hinv_in, hinv_eq⟩ := hinv_v_prop (clearedEmbedding.vMap v) hx_bar
    exact clearedEmbedding.bijOn_v.injOn hinv_in.1 hv_cl.1 hinv_eq
  have hbd_E₁_eq_subBd : discBd (closure Λ) = subBd Λ :=
    discBd_closure_eq_subBd hS hZone.isOpenDisc hZone.isOArc_bd hZone.isClosedDisc_closure
  have hNat_E₁ : IsNaturalOrderFrom inv_v S_G0.Ω (discBd (closure Λ)) :=
    hbd_E₁_eq_subBd.symm ▸ hΩ_Λ_nat
  obtain ⟨P_set, hCr_G0, hCard_P, hEnds_G0, hPaths_G0⟩ :=
    GraphMinor.GM14.theorem_8_4_proof.{u, v, w} P η_1 hS hΔ_disc hΔ₂_disc
      hZone.isClosedDisc_closure hcl_C₂_disc
      hΔ₂_sub_cl_C₂ hE₂_sub_diff hclΛ_sub_Δ hRig_H'
      ⟨hC₁_cir, hC₁_sub⟩ ⟨hC₂_cir, hC₂_sub⟩ hbd_E₁ hbd_E₂
      hπ1 hπ3 hDist_H' hX_bf_C₁ hP_paths hP_disj
      hSeg_1 hArr_1 hComp_1 hDisc_1_sub hPull_1_Δ hPull_1_Δ₂
      hComp_soc (rfl : S_G0.G = localSociety.G) hbar_G0_eq hinv_v_C₁ hNat_E₁ hCr_star
  -- Step 7: Transfer `P_set` from `S_G0` to `clearedSociety` and verify `IsHPathWithEnds`
  have hP_Δ_le_G' : arrangementPullbackGraph G' S_seg α_disc α_pt Δ ≤ G' :=
    Graph.restrict_le.trans (G'.induce_le inter_subset_right)
  have hP_Δ_le_amb : arrangementPullbackGraph G' S_seg α_disc α_pt Δ ≤ G_amb :=
    hP_Δ_le_G'.trans hG'_le
  have hstar_le_amb : localSociety.G ≤ G_amb :=
    hsoc_star_G ▸ subgraphUnion_le hJ_le hP_Δ_le_amb
  have hG_le_amb : G ≤ G_amb := hG_eq ▸ subgraphUnion_le hG'_le hJ_le
  have hstar_le_G : localSociety.G ≤ G := by
    exact inner_society_is_subgraph_of_replaced_graph (S := S) (α := α) (β := β) (G_amb := G_amb)
      (G := G) (G' := G') (J := J) (S_seg := S_seg) (α_disc := α_disc) (α_pt := α_pt) hG_eq (Δ :=
      Δ) (localSociety := localSociety) hsoc_star_G hJ_le hG'_le hP_Δ_le_G' hP_Δ_le_amb hstar_le_amb
      hG_le_amb
  have hG0_le_soc_Λ : S_G0.G ≤ clearedSociety.G := hsoc_Λ_G ▸ hstar_le_G
  have hOmegaPath_iff : ∀ p ∈ P_set, ∀ u v : α,
      clearedSociety.IsOmegaPathWithEnds p u v ↔ S_G0.IsOmegaPathWithEnds p u v := by
    intro p hp u v
    obtain ⟨a₀, b₀, hp₀, _, _⟩ := hPaths_G0 p hp
    have hp_le_G0 : p ≤ S_G0.G := hp₀.1.le
    exact ⟨fun ⟨hpath, hne, hu, hv⟩ => ⟨hpath.of_le hp_le_G0, hne, hu, hv⟩,
      fun ⟨hpath, hne, hu, hv⟩ => ⟨hpath.mono hG0_le_soc_Λ, hne, hu, hv⟩⟩
  have hEnds_eq_G0 : clearedSociety.transactionEnds P_set = S_G0.transactionEnds P_set := by
    ext v
    simp only [Society.transactionEnds, mem_ofPred_eq]
    exact ⟨fun ⟨p, hp, b, h⟩ => ⟨p, hp, b, (hOmegaPath_iff p hp v b).mp h⟩,
      fun ⟨p, hp, b, h⟩ => ⟨p, hp, b, (hOmegaPath_iff p hp v b).mpr h⟩⟩
  have hCr_Λ : clearedSociety.IsCrookedTransaction P_set := by
    exact rerouted_crooked_transaction_extends_to_replacement_society (α := α) (β := β)
      (clearedSociety :=
      clearedSociety) S_G0 P_set rfl hCr_G0 hOmegaPath_iff hEnds_eq_G0
  have hEnds_sub_Λ : clearedSociety.transactionEnds P_set ⊆ clearedEmbedding.vMap '' X_bf := by
    rw [hEnds_eq_G0]
    refine hEnds_G0.trans ?_
    rintro _ ⟨v, hvX, rfl⟩
    exact ⟨v, hvX, (hC₁_vMap_eq v (hX_bf_C₁ hvX)).symm⟩
  -- Prove `IsHPathWithEnds G_amb clearedEmbedding.imageGraph p a' b'` for every `p ∈ P_set`
  have hCleared_V_sub : (clearedSubdrawing H Λ).V ⊆ H.V ∩ (univ \ Λ) := by
    have hcl_compl : IsClosed (univ \ Λ) := isClosed_univ.sdiff hZone.isOpenDisc.1
    rintro x (⟨hx, _⟩ | hx)
    · exact hx
    · obtain ⟨e, he, hxe, hxV⟩ := mem_iUnion₂.mp hx
      exact ⟨hxV, hcl_compl.closure_subset_iff.mpr he.1.2 hxe⟩
  have hCleared_E_sub : (clearedSubdrawing H Λ).E ⊆ {e ∈ H.E | e ⊆ univ \ Λ} := by
    intro e he
    change e ∈ (H.span _ _).E at he
    rw [H.span_E] at he
    exact ⟨he.2, he.1.2⟩
  refine ⟨P_set, hCr_Λ, hCard_P, hEnds_sub_Λ, ?_⟩
  intro p hp a' b' hp_a'b'
  obtain ⟨a, b, hp_ab, hv_H', he_H'⟩ := hPaths_G0 p hp
  have hp_le_star : p ≤ localSociety.G := hp_ab.1.le
  -- Show `{a', b'} = {a, b}` using `a', b' ∈ clearedSociety.Ω.bar = η_1.vMap '' C₁.V`
  have hbar_in_ab : ∀ x ∈ clearedSociety.Ω.bar, x ∈ V(p) → x = a ∨ x = b := by
    intro x hx_bar hx_Vp
    rw [hbar_G0_eq] at hx_bar
    obtain ⟨v, hvC₁, rfl⟩ := hx_bar
    have hv_H'V : v ∈ H'.V := hC₁_sub.1 hvC₁
    have hv_not_diff : v ∉ closure Λ \ C₁.U := fun h => h.2 (C₁.V_subset_U hvC₁)
    rcases hv_H' v hv_H'V hx_Vp with h1 | h2 | h3
    · exact Or.inl h1
    · exact Or.inr h2
    · exact (hv_not_diff h3).elim
  have ha'_ab : a' = a ∨ a' = b := hbar_in_ab a' hp_a'b'.2.2.1 hp_a'b'.1.left_mem
  have hb'_ab : b' = a ∨ b' = b := hbar_in_ab b' hp_a'b'.2.2.2 hp_a'b'.1.right_mem
  have hpair_eq : ({a', b'} : Set α) = {a, b} := by
    have hne' : a' ≠ b' := hp_a'b'.2.1
    rcases ha'_ab with rfl | rfl <;> rcases hb'_ab with rfl | rfl
    · exact (hne' rfl).elim
    · rfl
    · exact Set.pair_comm _ _
    · exact (hne' rfl).elim
  have hbar_sub_img : clearedSociety.Ω.bar ⊆ V(clearedEmbedding.imageGraph) := by
    rw [hsoc_Λ_bar]
    rintro _ ⟨v, hv, rfl⟩
    exact clearedEmbedding.bijOn_v.mapsTo hv.1
  have hpath_vertices : V(p) ∩ V(clearedEmbedding.imageGraph) = {a', b'} := by
    exact rerouted_path_meets_cleared_drawing_only_at_ends (S := S) (α := α) (β := β) (G_amb :=
      G_amb) (G' := G') (J := J) (H := H) (η := η) (η' := η') (beta := beta) (d := d) (z := z)
      (S_seg := S_seg) (α_disc := α_disc) (α_pt := α_pt) hη'_v hJ_dist hComp (Λ := Λ) (Δ := Δ)
      (clearedEmbedding := clearedEmbedding) (clearedSociety := clearedSociety) (localSociety
        := localSociety) hη_Λ_v hsoc_star_G (Λ_C₂ := Λ_C₂) (Δ₂
      := Δ₂) hcl_C₂_sub hΔ₂_sub_cl_C₂ Δ₀ hΔ₀_sub_Λ hΔ₀_atoms hdiff_E₁ N η_1 hη_1_v hV_H'
      hCleared_V_sub p a' b' hp_a'b' a b hv_H' hp_le_star ha'_ab hb'_ab hpair_eq hbar_sub_img
  have hpath_edges : Disjoint E(p) E(clearedEmbedding.imageGraph) := by
    exact rerouted_path_avoids_cleared_drawing_edges (S := S) (α := α) (β := β) (G_amb := G_amb)
      (G' := G') (J := J) (B_rem := B_rem) (H := H) (η := η) (η' := η') (S_seg := S_seg) (α_disc
      := α_disc) (α_pt := α_pt) hG'_eq hη'_e hComp (Λ := Λ) (Δ := Δ) (clearedEmbedding
        := clearedEmbedding) (localSociety :=
      localSociety) hη_Λ_e hsoc_star_G (Λ_C₂ := Λ_C₂) (Δ₂ := Δ₂) hcl_C₂_sub hΔ₂_sub_cl_C₂ hdiff_E₁
      hJ_le hBrem_le hDisj_E N η_1 hη_1_e hE_H' hP_Δ_le_amb hCleared_E_sub p he_H' hp_le_star
  refine ⟨clearedEmbedding.imageGraph_le, hp_a'b'.1.mono (hsoc_Λ_G ▸ hG_le_amb), hp_a'b'.2.1,
    hbar_sub_img hp_a'b'.2.2.1, hbar_sub_img hp_a'b'.2.2.2, hpath_vertices, hpath_edges⟩

end GraphMinor.GM14
