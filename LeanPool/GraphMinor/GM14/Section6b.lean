/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Section6a
import LeanPool.GraphMinor.GM11.ThreeCircuits
import LeanPool.GraphMinor.Surface.PushOff
import LeanPool.GraphMinor.Surface.SurfaceGraph

/-!
# Graph Minors XIV, Section 6 (Part 2): Clearing an Open Disc in a Rigid Drawing ((6.3))

This file formalizes result (6.3) (pages 33–34) of N. Robertson and P. D. Seymour,
*Graph Minors. XIV. Extending an embedding*, J. Combin. Theory Ser. B **65** (1995) 23–50:

- `theorem_6_3`: Graph Minors XIV, (6.3) (page 33), showing that if `H` is a rigid drawing in `Σ`,
  `Λ ⊆ Σ` is an open disc whose closure is a closed disc and whose boundary `bd(Λ) = U(C)` is a
  circuit `C` of `H`, and `closure r ∩ closure Λ` is preconnected for every region `r ∈ H.R`
  disjoint from `Λ`, then `clearedSubdrawing H Λ = H ∩ (Σ - Λ)` is a rigid drawing in `Σ`.
-/

@[expose] public section

namespace GraphMinor.GM14

open Set Function Topology Graph Hypergraph unitInterval
open GraphMinor.Surface GraphMinor.GM11

universe u

variable {S : Type u} [TopologicalSpace S]

/-! ## 1. Pushing an Arc off a Closed Disc -/

local notation "𝕀" => unitInterval

/-- Given a closed disc `D` in a closed surface `S`, a line `L ⊆ subBd D` with ends `a, b`, and a
closed set `Y ⊆ S` with `Y ∩ D ⊆ subBd D`, `a ∈ Y`, `b ∈ Y`, and `Y ∩ L ⊆ {a, b}`, there is a
homeomorphism `h : S ≃ₜ S` fixing `Y` pointwise such that `h '' L ∩ D ⊆ {a, b}`. -/
private theorem push_arc_of_fixed_boundary (hS : IsClosedSurface S) {D L Y : Set S} {a b : S}
    (hD : IsClosedDisc D) (hL : IsLineWithEnds L a b) (hLD : L ⊆ subBd D)
    (hY : IsClosed Y) (hYD : Y ∩ D ⊆ subBd D) (haY : a ∈ Y) (hbY : b ∈ Y) (hYL : Y ∩ L ⊆ {a, b}) :
    ∃ h : S ≃ₜ S, (∀ y ∈ Y, h y = y) ∧ h '' L ∩ D ⊆ {a, b} := by
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  have hint : ∀ x : S, IsInteriorPoint x := hS.2.2
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hint x).isManifoldPoint
  have hbd_eq : subBd D = discBd D := IsClosedDisc.subBd_eq_discBd hS hD
  have hLD' : L ⊆ discBd D := hbd_eq ▸ hLD
  obtain ⟨u, v, huv, hr, h0, h1, hun⟩ := exists_arcs_of_line hD.isOArc_discBd hL hLD'
  subst h0 h1 hr
  have hvu : IsTwoArcs v u := huv.symm
  have hun' : range v ∪ range u = discBd D := by rw [Set.union_comm, hun]
  have hv0 : v 0 ∈ Y := huv.zero ▸ haY
  have hv1 : v 1 ∈ Y := huv.one ▸ hbY
  have hYD' : Y ∩ D ⊆ range v := by
    intro x hx
    have hx_bd : x ∈ range v ∪ range u := hun' ▸ hbd_eq ▸ hYD hx
    rcases hx_bd with hxv | hxu
    · exact hxv
    · rcases hYL ⟨hx.1, hxu⟩ with rfl | rfl
      · exact ⟨0, huv.zero⟩
      · exact ⟨1, huv.one⟩
  have hC : IsClosed (range u) := (isCompact_range huv.arc_left.1).isClosed
  have hCv : range u ∩ range v ⊆ {v 0, v 1} := by
    rintro x ⟨⟨s, rfl⟩, ⟨t, hst⟩⟩
    rcases huv.meet s t hst.symm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl huv.zero.symm
    · exact Or.inr huv.one.symm
  obtain ⟨h, hhY, hhL⟩ :=
    push_side hman hD (fun x _ => hint x) hvu hun' hY hYD' hv0 hv1 hC hCv
  refine ⟨h, hhY, ?_⟩
  rwa [huv.zero, huv.one] at hhL

/-! ## 2. Subdrawing Outside an Open Disc Bounded by a Circuit -/

/-- If `S'` is closed and every edge of `H` meeting `S'` is contained in `S'`, then
`(H.interSet S').V = H.V ∩ S'` and `(H.interSet S').U = H.U ∩ S'`. -/
theorem interSet_V_and_U_of_edges [T2Space S] {H : Drawing S} {S' : Set S}
    (hS'_cl : IsClosed S') (hEdges : ∀ e ∈ H.E, (e ∩ S').Nonempty → e ⊆ S') :
    (H.interSet S').V = H.V ∩ S' ∧ (H.interSet S').U = H.U ∩ S' := by
  have hE : (H.interSet S').E = {e | e ∈ H.E ∧ e ⊆ S'} := by
    change (H.span _ _).E = _
    rw [H.span_E]
    ext e
    simp only [mem_inter_iff, mem_ofPred_eq]
    tauto
  have hV : (H.interSet S').V = H.V ∩ S' := by
    apply subset_antisymm
    · rintro x (⟨hx, _⟩ | hx)
      · exact hx
      · obtain ⟨e, he, hxe, hxV⟩ := mem_iUnion₂.mp hx
        exact ⟨hxV, hS'_cl.closure_subset_iff.mpr he.1.2 hxe⟩
    · exact fun x hx => Or.inl ⟨hx, hx.1⟩
  refine ⟨hV, subset_antisymm ?_ ?_⟩
  · rw [(H.interSet S').U_eq, hV, hE]
    refine union_subset (fun x hx => ⟨H.V_subset_U hx.1, hx.2⟩) (iUnion₂_subset fun e he x hx => ?_)
    exact ⟨H.closure_subset_U he.1 hx, hS'_cl.closure_subset_iff.mpr he.2 hx⟩
  · rintro x ⟨hxU, hxS'⟩
    by_cases hxV : x ∈ H.V
    · exact (H.interSet S').V_subset_U (hV.symm ▸ ⟨hxV, hxS'⟩)
    · obtain ⟨e, he, hxe⟩ := H.exists_edge_of_mem hxU hxV
      have heS' : e ⊆ S' := hEdges e he ⟨x, hxe, hxS'⟩
      have he' : e ∈ (H.interSet S').E := hE.symm ▸ ⟨he, heS'⟩
      exact (H.interSet S').closure_subset_U he' (subset_closure hxe)

/-- If `S'` is closed and every edge of `H` meeting `S'` is contained in `S'`, then for `F ⊆ S'`
and `Δ ⊆ S'`, `IsDial (H.interSet S') F Δ ↔ IsDial H F Δ`. -/
theorem isDial_interSet_iff_of_edges [T2Space S] {H : Drawing S} {S' F Δ : Set S}
    (hS'_cl : IsClosed S') (hEdges : ∀ e ∈ H.E, (e ∩ S').Nonempty → e ⊆ S')
    (hF : F ⊆ S') (hΔ : Δ ⊆ S') :
    IsDial (H.interSet S') F Δ ↔ IsDial H F Δ := by
  obtain ⟨hV, hU⟩ := interSet_V_and_U_of_edges hS'_cl hEdges
  have hΔU : Δ ∩ (H.interSet S').U = Δ ∩ H.U := by
    rw [hU]
    ext x
    exact ⟨fun ⟨hxΔ, hxU, _⟩ => ⟨hxΔ, hxU⟩, fun ⟨hxΔ, hxU⟩ => ⟨hxΔ, hxU, hΔ hxΔ⟩⟩
  have hFV : F ∩ (H.interSet S').V = F ∩ H.V := by
    rw [hV]
    ext x
    exact ⟨fun ⟨hxF, hxV, _⟩ => ⟨hxF, hxV⟩, fun ⟨hxF, hxV⟩ => ⟨hxF, hxV, hF hxF⟩⟩
  have hinter : (H.interSet S').interSet Δ = H.interSet Δ :=
    interSet_interSet_of_subset H hΔ
  unfold IsDial
  rw [hΔU, hFV, hinter]

/-- Every edge of `H` is either contained in `Λ` or contained in `univ \ Λ` when `Λ` is an open
disc whose boundary `subBd Λ` is an `O`-arc in `H.U`. -/
theorem edge_subset_or_subset_compl_of_openDisc [T2Space S] {H : Drawing S} {Λ e : Set S}
    (hΛ_open : IsOpenDisc Λ) (hΛ_bd : IsOArc (subBd Λ)) (hbd_U : subBd Λ ⊆ H.U) (he : e ∈ H.E) :
    e ⊆ Λ ∨ e ⊆ univ \ Λ := by
  obtain ⟨hdisL, hclL⟩ := isOpen_disjoint_subBd_and_closure_eq hΛ_open.1
  rcases edge_subset_or_disjoint_of_isOArc hΛ_bd hbd_U he with hsub | hdis
  · exact Or.inr fun x hx => ⟨mem_univ _, fun hxΛ => disjoint_left.mp hdisL hxΛ (hsub hx)⟩
  · have hcov : e ⊆ Λ ∪ (closure Λ)ᶜ := by
      intro x hx
      by_cases hxcl : x ∈ closure Λ
      · rw [hclL] at hxcl
        exact Or.inl (hxcl.resolve_right (disjoint_left.mp hdis hx))
      · exact Or.inr hxcl
    have hdisO : Disjoint Λ (closure Λ)ᶜ :=
      disjoint_left.mpr fun x hx hxc => hxc (subset_closure hx)
    by_cases hmeet : (e ∩ Λ).Nonempty
    · obtain ⟨x, hxe, hxΛ⟩ := hmeet
      exact Or.inl ((he.2.2.1.isConnected.isPreconnected).subset_left_of_subset_union
        hΛ_open.1 isClosed_closure.isOpen_compl hdisO hcov ⟨x, hxe, hxΛ⟩)
    · refine Or.inr fun x hxe => ⟨mem_univ _, fun hxΛ => hmeet ⟨x, hxe, hxΛ⟩⟩

/-- Basic properties of `H' = clearedSubdrawing H Λ` when `Λ` is an open disc with `subBd Λ = C.U`
for a circuit `C` of `H`. -/
theorem clearedSubdrawing_props_of_circuit [T2Space S] {H C : Drawing S} {Λ : Set S}
    (hΛ_open : IsOpenDisc Λ) (hC : C.IsCircuit) (hCs : C.IsSubdrawing H) (hbd : subBd Λ = C.U) :
    (clearedSubdrawing H Λ).V = H.V \ Λ ∧
    (clearedSubdrawing H Λ).E = {e ∈ H.E | e ⊆ univ \ Λ} ∧
    (clearedSubdrawing H Λ).U = H.U \ Λ ∧
    C.IsSubdrawing (clearedSubdrawing H Λ) ∧
    Λ ∈ (clearedSubdrawing H Λ).R ∧
    (∀ r' ∈ (clearedSubdrawing H Λ).R, r' = Λ ∨ (r' ∈ H.R ∧ Disjoint r' Λ)) ∧
    (∀ r ∈ H.R, Disjoint r Λ → r ∈ (clearedSubdrawing H Λ).R) := by
  have hS'_cl : IsClosed (univ \ Λ) := by
    rw [← compl_eq_univ_sdiff]
    exact hΛ_open.1.isClosed_compl
  have hO : IsOArc (subBd Λ) := hbd ▸ isOArc_of_isCircuit hC
  have hbd_U : subBd Λ ⊆ H.U := hbd ▸ hCs.U_subset
  have hEdges : ∀ e ∈ H.E, (e ∩ (univ \ Λ)).Nonempty → e ⊆ univ \ Λ := by
    rintro e he ⟨x, hxe, hx⟩
    rcases edge_subset_or_subset_compl_of_openDisc hΛ_open hO hbd_U he with heΛ | hec
    · exact absurd (heΛ hxe) hx.2
    · exact hec
  obtain ⟨hV, hU⟩ := interSet_V_and_U_of_edges hS'_cl hEdges
  have hV' : (clearedSubdrawing H Λ).V = H.V \ Λ := by
    change (H.interSet (univ \ Λ)).V = _
    rw [hV]
    ext x
    simp only [mem_inter_iff, mem_sdiff, mem_univ, true_and]
  have hU' : (clearedSubdrawing H Λ).U = H.U \ Λ := by
    change (H.interSet (univ \ Λ)).U = _
    rw [hU]
    ext x
    simp only [mem_inter_iff, mem_sdiff, mem_univ, true_and]
  have hE' : (clearedSubdrawing H Λ).E = {e ∈ H.E | e ⊆ univ \ Λ} := by
    change (H.span _ _).E = _
    rw [H.span_E]
    ext e
    simp only [mem_inter_iff, mem_ofPred_eq]
    tauto
  obtain ⟨hdisL, hclL⟩ := isOpen_disjoint_subBd_and_closure_eq hΛ_open.1
  have hCU_dis : Disjoint C.U Λ := hbd ▸ hdisL.symm
  have hC_sub' : C.IsSubdrawing (clearedSubdrawing H Λ) := by
    refine ⟨?_, ?_⟩
    · rw [hV']
      exact fun v hv => ⟨hCs.1 hv, disjoint_left.mp hCU_dis (C.V_subset_U hv)⟩
    · rw [hE']
      exact fun e he => ⟨hCs.2 he, fun x hx =>
        ⟨mem_univ _, disjoint_left.mp hCU_dis (C.closure_subset_U he (subset_closure hx))⟩⟩
  let O₂ : Set S := univ \ (H.U ∪ closure Λ)
  have hO₂ : IsOpen O₂ := isOpen_univ.sdiff (H.isClosed_U.union isClosed_closure)
  have hdisO : Disjoint Λ O₂ :=
    disjoint_left.mpr fun x hx hxO => hxO.2 (Or.inr (subset_closure hx))
  have hcompl : univ \ (clearedSubdrawing H Λ).U = Λ ∪ O₂ := by
    rw [hU']
    ext x
    constructor
    · rintro ⟨_, hx⟩
      by_cases hxΛ : x ∈ Λ
      · exact Or.inl hxΛ
      · refine Or.inr ⟨mem_univ _, ?_⟩
        rintro (hxU | hxcl)
        · exact hx ⟨hxU, hxΛ⟩
        · rw [hclL] at hxcl
          exact hx ⟨hbd_U (hxcl.resolve_left hxΛ), hxΛ⟩
    · rintro (hxΛ | ⟨_, hx⟩)
      · exact ⟨mem_univ _, fun h => h.2 hxΛ⟩
      · exact ⟨mem_univ _, fun h => hx (Or.inl h.1)⟩
  have hΛ_R : Λ ∈ (clearedSubdrawing H Λ).R := by
    obtain ⟨φ⟩ := hΛ_open.2
    have h0 : (0 : EuclideanPlane) ∈ OpenUnitDisc := by simp [OpenUnitDisc]
    let x₀ : S := (φ ⟨0, h0⟩).1
    have hx₀Λ : x₀ ∈ Λ := (φ ⟨0, h0⟩).2
    have hx₀_mem : x₀ ∈ univ \ (clearedSubdrawing H Λ).U := hcompl ▸ Or.inl hx₀Λ
    refine (mem_R_iff (clearedSubdrawing H Λ)).mpr ⟨x₀, hx₀_mem.2, subset_antisymm ?_ ?_⟩
    · refine hΛ_open.isPathConnected.isConnected.isPreconnected.subset_connectedComponentIn
        hx₀Λ ?_
      rw [hcompl]
      exact subset_union_left
    · have hcov' : connectedComponentIn (univ \ (clearedSubdrawing H Λ).U) x₀ ⊆ Λ ∪ O₂ := by
        rw [← hcompl]
        exact connectedComponentIn_subset _ _
      exact isPreconnected_connectedComponentIn.subset_left_of_subset_union
        hΛ_open.1 hO₂ hdisO hcov' ⟨x₀, mem_connectedComponentIn hx₀_mem, hx₀Λ⟩
  have hR_or : ∀ r' ∈ (clearedSubdrawing H Λ).R, r' = Λ ∨ (r' ∈ H.R ∧ Disjoint r' Λ) := by
    intro r' hr'
    obtain ⟨x, hxU', rfl⟩ := (mem_R_iff (clearedSubdrawing H Λ)).mp hr'
    have hx_mem : x ∈ univ \ (clearedSubdrawing H Λ).U := ⟨mem_univ _, hxU'⟩
    have hcov' : connectedComponentIn (univ \ (clearedSubdrawing H Λ).U) x ⊆ Λ ∪ O₂ := by
      rw [← hcompl]
      exact connectedComponentIn_subset _ _
    rcases hcompl ▸ hx_mem with hxΛ | hxO₂
    · refine Or.inl (subset_antisymm ?_ ?_)
      · exact isPreconnected_connectedComponentIn.subset_left_of_subset_union
          hΛ_open.1 hO₂ hdisO hcov' ⟨x, mem_connectedComponentIn hx_mem, hxΛ⟩
      · refine hΛ_open.isPathConnected.isConnected.isPreconnected.subset_connectedComponentIn
          hxΛ ?_
        rw [hcompl]
        exact subset_union_left
    · refine Or.inr ?_
      have hxHU : x ∉ H.U := fun h => hxO₂.2 (Or.inl h)
      have hsubO₂ : connectedComponentIn (univ \ (clearedSubdrawing H Λ).U) x ⊆ O₂ :=
        isPreconnected_connectedComponentIn.subset_right_of_subset_union
          hΛ_open.1 hO₂ hdisO hcov' ⟨x, mem_connectedComponentIn hx_mem, hxO₂⟩
      have heq_comp : connectedComponentIn (univ \ (clearedSubdrawing H Λ).U) x =
          connectedComponentIn (univ \ H.U) x := by
        apply subset_antisymm
        · refine isPreconnected_connectedComponentIn.subset_connectedComponentIn
            (mem_connectedComponentIn hx_mem) ?_
          exact hsubO₂.trans fun y hy => ⟨mem_univ _, fun h => hy.2 (Or.inl h)⟩
        · have hcovH : connectedComponentIn (univ \ H.U) x ⊆ Λ ∪ O₂ := by
            intro y hy
            have hyU : y ∉ H.U := (connectedComponentIn_subset _ _ hy).2
            by_cases hycl : y ∈ closure Λ
            · rw [hclL] at hycl
              exact Or.inl (hycl.resolve_right fun hbd' => hyU (hbd_U hbd'))
            · exact Or.inr ⟨mem_univ _, fun h => h.elim hyU hycl⟩
          have hsubO₂' : connectedComponentIn (univ \ H.U) x ⊆ O₂ :=
            isPreconnected_connectedComponentIn.subset_right_of_subset_union
              hΛ_open.1 hO₂ hdisO hcovH
              ⟨x, mem_connectedComponentIn ⟨mem_univ _, hxHU⟩, hxO₂⟩
          refine isPreconnected_connectedComponentIn.subset_connectedComponentIn
            (mem_connectedComponentIn ⟨mem_univ _, hxHU⟩) ?_
          rw [hcompl]
          exact hsubO₂'.trans subset_union_right
      exact ⟨(mem_R_iff H).mpr ⟨x, hxHU, heq_comp⟩, hdisO.symm.mono_left hsubO₂⟩
  have hR_in : ∀ r ∈ H.R, Disjoint r Λ → r ∈ (clearedSubdrawing H Λ).R := by
    intro r hr hdis_r
    obtain ⟨x, hxHU, rfl⟩ := (mem_R_iff H).mp hr
    have hxr : x ∈ connectedComponentIn (univ \ H.U) x :=
      mem_connectedComponentIn ⟨mem_univ _, hxHU⟩
    have hxΛ : x ∉ Λ := disjoint_left.mp hdis_r hxr
    have hxU' : x ∉ (clearedSubdrawing H Λ).U := by
      rw [hU']
      exact fun h => hxHU h.1
    have hr' : connectedComponentIn (univ \ (clearedSubdrawing H Λ).U) x ∈
        (clearedSubdrawing H Λ).R :=
      (mem_R_iff (clearedSubdrawing H Λ)).mpr ⟨x, hxU', rfl⟩
    rcases hR_or _ hr' with heq | ⟨hr_H, _⟩
    · exact absurd (heq ▸ mem_connectedComponentIn ⟨mem_univ _, hxU'⟩) hxΛ
    · have heq : connectedComponentIn (univ \ H.U) x =
          connectedComponentIn (univ \ (clearedSubdrawing H Λ).U) x :=
        region_eq_of_mem hr hr_H hxr (mem_connectedComponentIn ⟨mem_univ _, hxU'⟩)
      exact heq ▸ hr'
  exact ⟨hV', hE', hU', hC_sub', hΛ_R, hR_or, hR_in⟩

/-- By (6.1), `clearedSubdrawing H Λ` is rigid in `univ \ Λ`. -/
theorem isRigidIn_clearedSubdrawing [T2Space S] (hS : IsClosedSurface S) {H C : Drawing S}
    {Λ : Set S} (hRig : IsRigid H) (hΛ_open : IsOpenDisc Λ) (hΛ_cl : IsClosedDisc (closure Λ))
    (hC : C.IsCircuit) (hCs : C.IsSubdrawing H) (hbd : subBd Λ = C.U) :
    IsRigidIn (clearedSubdrawing H Λ) (univ \ Λ) := by
  have hS'_cl : IsClosed (univ \ Λ) := by
    rw [← compl_eq_univ_sdiff]
    exact hΛ_open.1.isClosed_compl
  have hO : IsOArc (subBd Λ) := hbd ▸ isOArc_of_isCircuit hC
  have hbd_U : subBd Λ ⊆ H.U := hbd ▸ hCs.U_subset
  have hEdges : ∀ e ∈ H.E, (e ∩ (univ \ Λ)).Nonempty → e ⊆ univ \ Λ := by
    rintro e he ⟨x, hxe, hx⟩
    rcases edge_subset_or_subset_compl_of_openDisc hΛ_open hO hbd_U he with heΛ | hec
    · exact absurd (heΛ hxe) hx.2
    · exact hec
  obtain ⟨hV, hU⟩ := interSet_V_and_U_of_edges hS'_cl hEdges
  intro F hFS' hF_oArc hFU' hFV_card'
  have hFU : F ∩ H.U = F ∩ (clearedSubdrawing H Λ).U := by
    change F ∩ H.U = F ∩ (H.interSet (univ \ Λ)).U
    rw [hU]
    ext x
    exact ⟨fun ⟨hxF, hxU⟩ => ⟨hxF, hxU, hFS' hxF⟩, fun ⟨hxF, hxU, _⟩ => ⟨hxF, hxU⟩⟩
  have hFV : F ∩ H.V = F ∩ (clearedSubdrawing H Λ).V := by
    change F ∩ H.V = F ∩ (H.interSet (univ \ Λ)).V
    rw [hV]
    ext x
    exact ⟨fun ⟨hxF, hxV⟩ => ⟨hxF, hxV, hFS' hxF⟩, fun ⟨hxF, hxV, _⟩ => ⟨hxF, hxV⟩⟩
  have hFU_sub : F ∩ H.U ⊆ H.V := by
    rw [hFU]
    exact hFU'.trans (H.spanV_subset _ _)
  have hFV_card : (F ∩ H.V).ncard ≤ 2 := by
    rwa [hFV]
  obtain ⟨Δ, hDial⟩ := hRig F hF_oArc hFU_sub hFV_card
  have hΔ_sub : Δ ⊆ univ \ Λ := by
    by_contra hnot
    obtain ⟨Δ', hΔ'_disc, hΔ'_sub, hΔ'_inter, _⟩ :=
      subsurf_compl_openDisc hS hΛ_open hO hΛ_cl hDial.1 (hDial.2.1 ▸ hFS') hnot
    have hCU_Δ : C.U ⊆ Δ := by
      intro x hxC
      have hx_bd : x ∈ subBd Λ := hbd.symm ▸ hxC
      have hx_cl : x ∈ closure Λ := hx_bd.1
      -- In `subsurf_compl_openDisc`, `closure Λ ⊆ Δ`.
      have hmeet : (Λ ∩ Δ).Nonempty := by
        by_contra h
        apply hnot
        exact fun y hy => ⟨mem_univ y, fun hyΛ => h ⟨y, hyΛ, hy⟩⟩
      obtain ⟨z, hzΛ, hzΔ⟩ := hmeet
      have hdis : Disjoint Λ (frontier Δ) := by
        rw [← subBd_eq_frontier]
        exact disjoint_left.mpr fun y hyΛ hybd => (hFS' (hDial.2.1 ▸ hybd)).2 hyΛ
      have hΛ_sub : Λ ⊆ Δ :=
        subset_of_disjoint_frontier hΛ_open.isPathConnected.isConnected.isPreconnected
          hDial.1.isClosed hdis hzΛ hzΔ
      exact hDial.1.isClosed.closure_subset_iff.mpr hΛ_sub hx_cl
    exact no_circuit_in_dial hDial hFU_sub hC hCs hCU_Δ
  exact ⟨Δ, hΔ_sub, (isDial_interSet_iff_of_edges hS'_cl hEdges hFS' hΔ_sub).mpr hDial⟩

/-! ## 3. Circuit Path Selection and Corner Uniqueness Along `P` -/

/-- If a circuit `C` splits at `v₁ ≠ v₂` into paths `P₁, P₂`, and `K ⊆ C.U` is preconnected with
`v₁ ∈ K` and `v₂ ∈ K`, then either `P₁.U ⊆ K` or `P₂.U ⊆ K`. -/
theorem path_subset_of_isPreconnected_inter_circuit [T2Space S] {C P₁ P₂ : Drawing S}
    {v₁ v₂ : S} {K : Set S}
    (hP₁ : P₁.IsPathBetween v₁ v₂) (hP₂ : P₂.IsPathBetween v₁ v₂)
    (hP₁s : P₁.IsSubdrawing C) (hP₂s : P₂.IsSubdrawing C)
    (hv12 : v₁ ≠ v₂) (hV_inter : P₁.V ∩ P₂.V = {v₁, v₂})
    (hE_disj : Disjoint P₁.E P₂.E) (hU_union : P₁.U ∪ P₂.U = C.U)
    (hK_conn : IsPreconnected K) (hK_sub : K ⊆ C.U) (hv₁K : v₁ ∈ K) (hv₂K : v₂ ∈ K) :
    P₁.U ⊆ K ∨ P₂.U ⊆ K := by
  by_contra hnot
  rw [not_or, Set.not_subset, Set.not_subset] at hnot
  obtain ⟨⟨p, hp₁, hpK⟩, ⟨q, hq₂, hqK⟩⟩ := hnot
  obtain ⟨f₁, hf₁0, hf₁1⟩ := isLine_of_isPathBetween hP₁ hv12
  obtain ⟨f₂, hf₂0, hf₂1⟩ := isLine_of_isPathBetween hP₂ hv12
  have hU_inter : P₁.U ∩ P₂.U = {v₁, v₂} := by
    rw [U_inter_of_disjoint hP₁s hP₂s hE_disj, hV_inter]
  let t₁ : I := f₁.symm ⟨p, hp₁⟩
  let t₂ : I := f₂.symm ⟨q, hq₂⟩
  have ht₁_val : (f₁ t₁).1 = p := by simp [t₁]
  have ht₂_val : (f₂ t₂).1 = q := by simp [t₂]
  have ht₁_0 : t₁ ≠ 0 := fun h => hpK (by rw [← ht₁_val, h, hf₁0]; exact hv₁K)
  have ht₁_1 : t₁ ≠ 1 := fun h => hpK (by rw [← ht₁_val, h, hf₁1]; exact hv₂K)
  have ht₂_0 : t₂ ≠ 0 := fun h => hqK (by rw [← ht₂_val, h, hf₂0]; exact hv₁K)
  have ht₂_1 : t₂ ≠ 1 := fun h => hqK (by rw [← ht₂_val, h, hf₂1]; exact hv₂K)
  let A : Set S := (fun s : I => (f₁ s).1) '' Iic t₁ ∪ (fun s : I => (f₂ s).1) '' Iic t₂
  let B : Set S := (fun s : I => (f₁ s).1) '' Ici t₁ ∪ (fun s : I => (f₂ s).1) '' Ici t₂
  have hA_cl : IsClosed A :=
    ((isClosed_Iic.isCompact.image (by fun_prop)).union
      (isClosed_Iic.isCompact.image (by fun_prop))).isClosed
  have hB_cl : IsClosed B :=
    ((isClosed_Ici.isCompact.image (by fun_prop)).union
      (isClosed_Ici.isCompact.image (by fun_prop))).isClosed
  have hAB : C.U ⊆ A ∪ B := by
    rw [← hU_union]
    rintro x (hx₁ | hx₂)
    · obtain ⟨s, hs⟩ := f₁.surjective ⟨x, hx₁⟩
      have hxs : (f₁ s).1 = x := congrArg Subtype.val hs
      rcases le_total s t₁ with h | h
      · exact Or.inl (Or.inl ⟨s, h, hxs⟩)
      · exact Or.inr (Or.inl ⟨s, h, hxs⟩)
    · obtain ⟨s, hs⟩ := f₂.surjective ⟨x, hx₂⟩
      have hxs : (f₂ s).1 = x := congrArg Subtype.val hs
      rcases le_total s t₂ with h | h
      · exact Or.inl (Or.inr ⟨s, h, hxs⟩)
      · exact Or.inr (Or.inr ⟨s, h, hxs⟩)
  have hv₁A : v₁ ∈ A := Or.inl ⟨0, unitInterval.nonneg', hf₁0⟩
  have hv₂B : v₂ ∈ B := Or.inl ⟨1, unitInterval.le_one', hf₁1⟩
  obtain ⟨x, hxK, hxA, hxB⟩ := isPreconnected_closed_iff.mp hK_conn A B hA_cl hB_cl
    (hK_sub.trans hAB) ⟨v₁, hv₁K, hv₁A⟩ ⟨v₂, hv₂K, hv₂B⟩
  have hx_pq : x = p ∨ x = q := by
    rcases hxA with ⟨s₁, hs₁, rfl⟩ | ⟨s₂, hs₂, rfl⟩ <;>
      rcases hxB with ⟨s₁', hs₁', heq⟩ | ⟨s₂', hs₂', heq⟩
    · have hs : s₁ = s₁' := f₁.injective (Subtype.ext heq.symm)
      subst hs
      have hst : s₁ = t₁ := le_antisymm hs₁ hs₁'
      subst hst
      exact Or.inl ht₁_val
    · exfalso
      have heq' : (f₂ s₂').1 = (f₁ s₁).1 := heq
      have hmem : (f₁ s₁).1 ∈ P₁.U ∩ P₂.U := ⟨(f₁ s₁).2, heq' ▸ (f₂ s₂').2⟩
      rw [hU_inter] at hmem
      rcases hmem with h1 | h2
      · have hs0' : s₂' = 0 := f₂.injective (Subtype.ext ((heq'.trans h1).trans hf₂0.symm))
        exact ht₂_0 (le_antisymm (hs0' ▸ hs₂') unitInterval.nonneg')
      · have hs1 : s₁ = 1 := f₁.injective (Subtype.ext (h2.trans hf₁1.symm))
        exact ht₁_1 (le_antisymm unitInterval.le_one' (hs1 ▸ hs₁))
    · exfalso
      have heq' : (f₁ s₁').1 = (f₂ s₂).1 := heq
      have hmem : (f₂ s₂).1 ∈ P₁.U ∩ P₂.U := ⟨heq' ▸ (f₁ s₁').2, (f₂ s₂).2⟩
      rw [hU_inter] at hmem
      rcases hmem with h1 | h2
      · have hs0' : s₁' = 0 := f₁.injective (Subtype.ext ((heq'.trans h1).trans hf₁0.symm))
        exact ht₁_0 (le_antisymm (hs0' ▸ hs₁') unitInterval.nonneg')
      · have hs1 : s₂ = 1 := f₂.injective (Subtype.ext (h2.trans hf₂1.symm))
        exact ht₂_1 (le_antisymm unitInterval.le_one' (hs1 ▸ hs₂))
    · have hs : s₂ = s₂' := f₂.injective (Subtype.ext heq.symm)
      subst hs
      have hst : s₂ = t₂ := le_antisymm hs₂ hs₂'
      subst hst
      exact Or.inr ht₂_val
  rcases hx_pq with rfl | rfl
  · exact hpK hxK
  · exact hqK hxK

/-- At any vertex `w` of a circuit `C` of `H'` that has at least two vertices (`v₁, v₂ ∈ C.V`,
`v₁ ≠ v₂`), there are at least two half-edges of `H'` at `w`. -/
theorem two_le_card_halfEdges_of_circuit [T2Space S] {H' C : Drawing S}
    {γ : Set S → I → S} (hγ : EdgePar H' γ) (hC : C.IsCircuit) (hCs : C.IsSubdrawing H')
    {w v₁ v₂ : S} (hw : w ∈ C.V) (hv₁ : v₁ ∈ C.V) (hv₂ : v₂ ∈ C.V) (hv12 : v₁ ≠ v₂) :
    2 ≤ Nat.card (halfEdges H' γ w) := by
  have hex_other : ∃ v ∈ C.V, v ≠ w := by
    by_cases h : v₁ = w
    · exact ⟨v₂, hv₂, h ▸ hv12.symm⟩
    · exact ⟨v₁, hv₁, h⟩
  obtain ⟨v, hvC, hvw⟩ := hex_other
  obtain ⟨W, ⟨hnd, hed⟩, hpos, hV, hE⟩ := exists_walk_at hC hw
  cases W with
  | nil _ => simp at hpos
  | @cons _ u _ e₁ h₁ r =>
    have hr : r.IsSimple := hnd
    have huw : u ≠ w := by
      rintro rfl
      have h0 := support_of_length_zero hr.length_eq_zero
      have hv_sup : v ∈ (GraphWalk.cons h₁ r).support := by
        rw [hV] at hvC
        exact hvC
      simp only [GraphWalk.support_cons, h0.1, List.mem_cons, List.not_mem_nil, or_false,
        or_self] at hv_sup
      exact hvw hv_sup
    obtain ⟨e₂, he₂_r, hw_e₂⟩ := exists_edge_at_end r huw
    have he₁C : e₁ ∈ C.E := by rw [hE]; exact List.mem_cons_self
    have he₂C : e₂ ∈ C.E := by rw [hE]; exact List.mem_cons_of_mem _ he₂_r
    have he12 : e₁ ≠ e₂ := fun h => (List.nodup_cons.mp hed).1 (h ▸ he₂_r)
    have hw_e₁ : w ∈ closure e₁ := by
      have : w ∈ closure e₁ ∩ C.V := by rw [h₁.2.2.2]; simp
      exact this.1
    have hwH' : w ∈ H'.V := hCs.1 hw
    have he₁H' : e₁ ∈ H'.E := hCs.2 he₁C
    have he₂H' : e₂ ∈ H'.E := hCs.2 he₂C
    obtain ⟨b₁, hb₁⟩ := exists_end_eq hγ he₁H' hwH' hw_e₁
    obtain ⟨b₂, hb₂⟩ := exists_end_eq hγ he₂H' hwH' hw_e₂
    have hk₁ : (e₁, b₁) ∈ halfEdges H' γ w := ⟨he₁H', hb₁⟩
    have hk₂ : (e₂, b₂) ∈ halfEdges H' γ w := ⟨he₂H', hb₂⟩
    have hk12 : ((e₁, b₁) : Set S × Bool) ≠ (e₂, b₂) := fun h => he12 (congrArg Prod.fst h)
    have hfin := finite_halfEdges H' γ w
    rw [Nat.card_coe_set_eq]
    have hsub : ({(e₁, b₁), (e₂, b₂)} : Set (Set S × Bool)) ⊆ halfEdges H' γ w := by
      rintro x (rfl | rfl)
      · exact hk₁
      · exact hk₂
    have hcard_pair : ({(e₁, b₁), (e₂, b₂)} : Set (Set S × Bool)).ncard = 2 :=
      ncard_pair hk12
    linarith [ncard_le_ncard hsub hfin]

/-- At any internal vertex `w ∈ P.V \ {v₁, v₂}` of the path `P` of `C` with `P.U ⊆ closure r`,
every edge of `H'` incident with `w` belongs to `P.E`, and the only regions of `H'` with `w` in
their closure are `Λ` and `r`. -/
theorem internal_vertex_edges_and_regions [T2Space S] (hS : IsClosedSurface S)
    {H' C P P' : Drawing S} {Λ r : Set S} {v₁ v₂ w : S}
    (hRig' : IsRigidIn H' (univ \ Λ)) (hΛ_open : IsOpenDisc Λ)
    (hC : C.IsCircuit) (hC_sub' : C.IsSubdrawing H') (hbd : subBd Λ = C.U)
    (hE'_sub : ∀ e ∈ H'.E, e ⊆ univ \ Λ) (hΛ_R : Λ ∈ H'.R)
    (hv₁C : v₁ ∈ C.V) (hv₂C : v₂ ∈ C.V) (hv12 : v₁ ≠ v₂)
    (hPs : P.IsSubdrawing C) (hP's : P'.IsSubdrawing C)
    (hV_inter : P.V ∩ P'.V = {v₁, v₂}) (hsup : C.sup P P' = C)
    (hr_R' : r ∈ H'.R) (hr_sub : r ⊆ univ \ Λ) (hPU_r : P.U ⊆ closure r)
    (hwP : w ∈ P.V) (hw1 : w ≠ v₁) (hw2 : w ≠ v₂) :
    (∀ e ∈ H'.E, w ∈ closure e → e ∈ P.E) ∧
    (∀ s ∈ H'.R, w ∈ closure s → s = Λ ∨ s = r) := by
  have hwC : w ∈ C.V := hPs.1 hwP
  have hwH' : w ∈ H'.V := hC_sub'.1 hwC
  have hw_not_P' : w ∉ P'.V := by
    intro hwP'
    have hmem : w ∈ P.V ∩ P'.V := ⟨hwP, hwP'⟩
    rw [hV_inter] at hmem
    rcases hmem with rfl | rfl
    · exact hw1 rfl
    · exact hw2 rfl
  have hCE_union : C.E = P.E ∪ P'.E := by
    rw [← hsup, Drawing.sup_E hPs hP's]
  have hC_to_P : ∀ e ∈ C.E, w ∈ closure e → e ∈ P.E := by
    intro e heC hwe
    rcases (hCE_union ▸ heC) with heP | heP'
    · exact heP
    · have hmem : w ∈ closure e ∩ C.V := ⟨hwe, hwC⟩
      rw [← hP's.closure_inter_V heP'] at hmem
      exact absurd hmem.2 hw_not_P'
  obtain ⟨_, hclL⟩ := isOpen_disjoint_subBd_and_closure_eq hΛ_open.1
  have hΛ_to_P : ∀ e ∈ H'.E, w ∈ closure e → e ⊆ closure Λ → e ∈ P.E := by
    intro e heH' hwe he_cl
    have he_CU : e ⊆ C.U := by
      intro x hxe
      have hx_cl : x ∈ closure Λ := he_cl hxe
      have hx_not_Λ : x ∉ Λ := (hE'_sub e heH' hxe).2
      rw [← hbd]
      exact (hclL ▸ hx_cl).resolve_left hx_not_Λ
    have heC : e ∈ C.E := by
      by_contra he_not_C
      obtain ⟨p, hp⟩ := heH'.1
      exact disjoint_left.mp (edge_disjoint_U hC_sub' heH' he_not_C) hp (he_CU hp)
    exact hC_to_P e heC hwe
  have : Nonempty S := ⟨w⟩
  obtain ⟨γ, hγ⟩ := exists_edgePar H'
  have h2 : 2 ≤ Nat.card (halfEdges H' γ w) :=
    two_le_card_halfEdges_of_circuit hγ hC hC_sub' hwC hv₁C hv₂C hv12
  obtain ⟨next, ρ, P_sec, W_sec, Q_sec, τ, hsec⟩ :=
    exists_sectors hS H' hγ hwH' h2
  have hcor := hsec.corners
  have : Finite (halfEdges H' γ w) := (finite_halfEdges H' γ w).to_subtype
  have hsurj : Function.Surjective next := Finite.injective_iff_surjective.mp hcor.inj
  have hw_clΛ : w ∈ closure Λ := by
    have hwCU : w ∈ C.U := C.V_subset_U hwC
    rw [← hbd] at hwCU
    exact hwCU.1
  obtain ⟨j, hj_ρ⟩ := hcor.all Λ hΛ_R hw_clΛ
  have hj_ρ' : ρ j = Λ := hj_ρ.symm
  obtain ⟨j_prev, hj_prev⟩ := hsurj j
  have hw_cl_edge : ∀ k : halfEdges H' γ w, w ∈ closure k.1.1 := by
    intro k
    have h := end_mem_closure hγ k.2.1 k.1.2
    rwa [k.2.2] at h
  have hnext_j_P : (next j).1.1 ∈ P.E := by
    refine hΛ_to_P (next j).1.1 (next j).2.1 (hw_cl_edge (next j)) ?_
    rw [← hj_ρ']
    exact hcor.left j
  have hj_P : j.1.1 ∈ P.E := by
    refine hΛ_to_P j.1.1 j.2.1 (hw_cl_edge j) ?_
    have h := hcor.right j_prev
    rwa [hj_prev, hj_ρ'] at h
  have hr_ne_Λ : r ≠ Λ := by
    intro hrΛ
    obtain ⟨p, hp⟩ := region_nonempty hr_R'
    exact (hr_sub hp).2 (hrΛ ▸ hp)
  have hρ_next : ρ (next j) = r := by
    have hsub_r : (next j).1.1 ⊆ closure r :=
      (subset_closure.trans (P.closure_subset_U hnext_j_P)).trans hPU_r
    rcases hcor.sides j r hr_R' hsub_r with h | h
    · exact absurd (h.trans hj_ρ') hr_ne_Λ
    · exact h.symm
  have hρ_prev : ρ j_prev = r := by
    have hsub_r : (next j_prev).1.1 ⊆ closure r := by
      rw [hj_prev]
      exact (subset_closure.trans (P.closure_subset_U hj_P)).trans hPU_r
    rcases hcor.sides j_prev r hr_R' hsub_r with h | h
    · exact h.symm
    · rw [hj_prev, hj_ρ'] at h
      exact absurd h hr_ne_Λ
  have hwS' : w ∈ univ \ Λ := by
    refine ⟨mem_univ w, fun hwΛ => ?_⟩
    have hw_bd : w ∈ subBd Λ := hbd.symm ▸ C.V_subset_U hwC
    exact disjoint_left.mp (isOpen_disjoint_subBd_and_closure_eq hΛ_open.1).1 hwΛ hw_bd
  have hnext_eq_prev : next j = j_prev := by
    by_contra hne
    exact corner_regions_ne_in hS hRig' hwH' hwS' hsec (hρ_next ▸ hr_sub) hne
      (hρ_next.trans hρ_prev.symm)
  have hnext_next : next (next j) = j := by
    rw [hnext_eq_prev, hj_prev]
  have hall_two : ∀ k : halfEdges H' γ w, k = j ∨ k = next j := by
    intro k
    induction hcor.reach j k with
    | refl => exact Or.inl rfl
    | tail _ hyz ih =>
      rcases ih with rfl | rfl
      · exact Or.inr hyz
      · exact Or.inl (hyz.trans hnext_next)
  refine ⟨fun e heH' hwe => ?_, fun s hsR' hws => ?_⟩
  · obtain ⟨b, hb⟩ := exists_end_eq hγ heH' hwH' hwe
    let k : halfEdges H' γ w := ⟨(e, b), heH', hb⟩
    rcases hall_two k with hk | hk
    · have : e = j.1.1 := congrArg (fun x : halfEdges H' γ w => x.1.1) hk
      exact this ▸ hj_P
    · have : e = (next j).1.1 := congrArg (fun x : halfEdges H' γ w => x.1.1) hk
      exact this ▸ hnext_j_P
  · obtain ⟨k, rfl⟩ := hcor.all s hsR' hws
    rcases hall_two k with rfl | rfl
    · exact Or.inl hj_ρ'
    · exact Or.inr hρ_next

/-- If `F' ⊆ univ \ Λ` is an `O`-arc with `F' ∩ H'.U = {v₁, v₂}` and `F' \ {v₁, v₂} ⊆ r`
(`r ∈ H'.R`, `r ⊆ univ \ Λ`), then any dial `Δ' ⊆ univ \ Λ` for `F', H'` satisfies
`Δ' ∩ H'.U ⊆ F'`. -/
theorem dial_inter_sub_of_pushed [T2Space S] (hS : IsClosedSurface S) {H' C : Drawing S}
    {Λ r F' Δ' : Set S} {v₁ v₂ : S}
    (hRig' : IsRigidIn H' (univ \ Λ)) (hΛ_open : IsOpenDisc Λ)
    (hC : C.IsCircuit) (hC_sub' : C.IsSubdrawing H') (hbd : subBd Λ = C.U)
    (hv₁C : v₁ ∈ C.V) (hv₂C : v₂ ∈ C.V) (hv12 : v₁ ≠ v₂)
    (hr_R' : r ∈ H'.R) (hr_sub : r ⊆ univ \ Λ)
    (hF'_r : F' \ {v₁, v₂} ⊆ r) (hF'_V : F' ∩ H'.V = {v₁, v₂})
    (hDial' : IsDial H' F' Δ') :
    Δ' ∩ H'.U ⊆ F' := by
  rcases hDial'.2.2 with h1 | ⟨x, y, hxy, hFV_xy, hQ⟩
  · exact h1
  · exfalso
    let Q : Drawing S := H'.interSet Δ'
    have hQs : Q.IsSubdrawing H' := Drawing.span_isSubdrawing H' _ _
    have hFU'_sub : F' ∩ H'.U ⊆ H'.V := by
      rintro z ⟨hzF', hzU'⟩
      by_cases hz : z ∈ ({v₁, v₂} : Set S)
      · rcases hz with rfl | rfl
        · exact hC_sub'.1 hv₁C
        · exact hC_sub'.1 hv₂C
      · exact absurd hzU' (region_subset hr_R' (hF'_r ⟨hzF', hz⟩))
    have hEdgesΔ' : ∀ e ∈ H'.E, (e ∩ Δ').Nonempty → e ⊆ Δ' :=
      fun e he hne => edge_subset_of_inter_nonempty hDial'.1.isClosed (hDial'.2.1 ▸ hFU'_sub) he hne
    obtain ⟨_, hQU_eq⟩ := interSet_V_and_U_of_edges hDial'.1.isClosed hEdgesΔ'
    have hΔ'U : Δ' ∩ H'.U = Q.U := by
      change Δ' ∩ H'.U = (H'.interSet Δ').U
      rw [inter_comm, ← hQU_eq]
    have hbdΔ' : discBd Δ' = F' :=
      (IsClosedDisc.subBd_eq_discBd hS hDial'.1).symm.trans hDial'.2.1
    have hQU_sub : Q.U ⊆ Δ' := by
      rw [← hΔ'U]
      exact inter_subset_left
    have hQU_bd : Q.U ∩ discBd Δ' = {x, y} := by
      rw [hbdΔ', ← hΔ'U, ← hFV_xy]
      ext z
      refine ⟨fun ⟨⟨_, hzU⟩, hzF'⟩ => ⟨hzF', hFU'_sub ⟨hzF', hzU⟩⟩,
        fun ⟨hzF', hzV'⟩ => ⟨⟨hDial'.1.isClosed.closure_eq ▸ (hDial'.2.1 ▸ hzF').1,
          H'.V_subset_U hzV'⟩, hzF'⟩⟩
    have hQU_line : IsLineWithEnds Q.U x y := by
      obtain ⟨f, hf0, hf1⟩ := isLine_of_isPathBetween hQ hxy
      exact ⟨f, hf0, hf1⟩
    obtain ⟨A₁, A₂, D₁, D₂, _, hcompA, _, _, hD_union, _, hbd₁, hbd₂, hcompD⟩ :=
      disc_iArc Δ' Q.U x y hDial'.1 hQU_sub hxy hQU_line hQU_bd
    have hxy_eq : ({x, y} : Set S) = {v₁, v₂} := hFV_xy.symm.trans hF'_V
    have hsub_r : ∀ D_i A_i, D_i \ Q.U ∈ componentsIn (Δ' \ Q.U) →
        A_i ∈ componentsIn (discBd Δ' \ {x, y}) → discBd D_i = A_i ∪ Q.U → D_i \ Q.U ⊆ r := by
      intro D_i A_i hDi_mem hAi_mem hbd_i
      obtain ⟨p, hp, hDi_eq⟩ := hDi_mem
      obtain ⟨a, ha, hAi_eq⟩ := hAi_mem
      have ha_Ai : a ∈ A_i := hAi_eq ▸ mem_connectedComponentIn ha
      have ha_bd : a ∈ discBd Δ' \ {x, y} := ha
      have ha_r : a ∈ r := by
        rw [hbdΔ', hxy_eq] at ha_bd
        exact hF'_r ha_bd
      have ha_Di : a ∈ D_i \ Q.U := by
        refine ⟨Surface.discBd_subset D_i (hbd_i ▸ Or.inl ha_Ai), fun haQ => ?_⟩
        exact ha_bd.2 (hQU_bd ▸ ⟨haQ, ha_bd.1⟩)
      have hpre : IsPreconnected (D_i \ Q.U) := hDi_eq ▸ isPreconnected_connectedComponentIn
      have hdis : Disjoint (D_i \ Q.U) H'.U := by
        refine disjoint_left.mpr fun z hz hzU => hz.2 ?_
        have hzΔ' : z ∈ Δ' := (connectedComponentIn_subset (Δ' \ Q.U) p (hDi_eq ▸ hz)).1
        exact hΔ'U ▸ ⟨hzΔ', hzU⟩
      exact subset_region hr_R' hpre hdis ha_Di ha_r
    have hD₁_r : D₁ \ Q.U ⊆ r :=
      hsub_r D₁ A₁ (hcompD ▸ Or.inl rfl) (hcompA ▸ Or.inl rfl) hbd₁
    have hD₂_r : D₂ \ Q.U ⊆ r :=
      hsub_r D₂ A₂ (hcompD ▸ Or.inr rfl) (hcompA ▸ Or.inr rfl) hbd₂
    have hΔ'_diff_r : Δ' \ H'.U ⊆ r := by
      rw [show Δ' \ H'.U = Δ' \ Q.U by ext z; simp [← hΔ'U], ← hD_union, union_sdiff_distrib]
      exact union_subset hD₁_r hD₂_r
    obtain ⟨W_Q, _, _, hEQ⟩ := hQ
    obtain ⟨e, heW, hxe⟩ := exists_edge_at_end W_Q.reverse hxy.symm
    rw [GraphWalk.edges_reverse, List.mem_reverse] at heW
    have heQ : e ∈ Q.E := by rw [hEQ]; exact heW
    have heH' : e ∈ H'.E := hQs.2 heQ
    have hx_v12 : x ∈ ({v₁, v₂} : Set S) := by
      rw [← hxy_eq]
      exact Or.inl rfl
    have hxC : x ∈ C.V := by
      rcases hx_v12 with rfl | rfl
      · exact hv₁C
      · exact hv₂C
    have hxH' : x ∈ H'.V := hC_sub'.1 hxC
    have hxS' : x ∈ univ \ Λ := by
      refine ⟨mem_univ x, fun hxΛ => ?_⟩
      have hx_bd : x ∈ subBd Λ := hbd.symm ▸ C.V_subset_U hxC
      exact disjoint_left.mp (isOpen_disjoint_subBd_and_closure_eq hΛ_open.1).1 hxΛ hx_bd
    have : Nonempty S := ⟨x⟩
    obtain ⟨γ, hγ⟩ := exists_edgePar H'
    have h2 : 2 ≤ Nat.card (halfEdges H' γ x) :=
      two_le_card_halfEdges_of_circuit hγ hC hC_sub' hxC hv₁C hv₂C hv12
    obtain ⟨next, ρ, P_sec, W_sec, Q_sec, τ, hsec⟩ :=
      exists_sectors hS H' hγ hxH' h2
    have hcor := hsec.corners
    have : Finite (halfEdges H' γ x) := (finite_halfEdges H' γ x).to_subtype
    have hsurj : Function.Surjective next := Finite.injective_iff_surjective.mp hcor.inj
    obtain ⟨b, hb⟩ := exists_end_eq hγ heH' hxH' hxe
    obtain ⟨k', hk'⟩ := hsurj ⟨(e, b), heH', hb⟩
    have hk'_edge : (next k').1.1 = e := congrArg (fun k : halfEdges H' γ x => k.1.1) hk'
    let U_open : Set S := Δ' \ subBd Δ'
    have hU_open : IsOpen U_open := ((IsClosedDisc.isOpenDisc_diff_subBd hS hDial'.1).1).1
    obtain ⟨p₀, hp₀⟩ := heH'.1
    have hp₀_U : p₀ ∈ U_open := by
      refine ⟨hQU_sub (Q.closure_subset_U heQ (subset_closure hp₀)), fun hp_bd => ?_⟩
      have hp_xy : p₀ ∈ ({x, y} : Set S) :=
        hQU_bd ▸ ⟨Q.closure_subset_U heQ (subset_closure hp₀),
          (IsClosedDisc.subBd_eq_discBd hS hDial'.1) ▸ hp_bd⟩
      have hpV' : p₀ ∈ H'.V := (hFV_xy ▸ hp_xy).2
      exact (heH'.2.1 hp₀).2 hpV'
    have hρ_eq_r : ∀ l : halfEdges H' γ x, p₀ ∈ closure (ρ l) → ρ l = r := by
      intro l hpl
      obtain ⟨z, hzU, hzl⟩ := mem_closure_iff.mp hpl U_open hU_open hp₀_U
      have hz_not_U : z ∉ H'.U := region_subset (hcor.region l) hzl
      have hzr : z ∈ r := hΔ'_diff_r ⟨hzU.1, hz_not_U⟩
      exact region_eq_of_mem (hcor.region l) hr_R' hzl hzr
    have hρ1 : ρ k' = r := hρ_eq_r k' (hcor.left k' (hk'_edge.symm ▸ hp₀))
    have hρ2 : ρ (next k') = r := hρ_eq_r (next k') (hcor.right k' (hk'_edge.symm ▸ hp₀))
    exact corner_regions_ne_in hS hRig' hxH' hxS' hsec (hρ1 ▸ hr_sub) (hsec.next_ne k').symm
      (hρ1.trans hρ2.symm)

/-! ## 4. Constructing the Exterior Disc `Δ₂` and Proof of (6.3) -/

/-- A line in a T2 space is closed. -/
private theorem isClosed_of_isLineWithEnds [T2Space S] {L : Set S} {a b : S}
    (hL : IsLineWithEnds L a b) : IsClosed L := by
  obtain ⟨f, _, _⟩ := hL
  have h : L = range (fun t : I => (f t).1) := by
    ext x
    exact ⟨fun hx => ⟨f.symm ⟨x, hx⟩, by simp⟩, fun ⟨t, ht⟩ => ht ▸ (f t).2⟩
  rw [h]
  exact (isCompact_range (continuous_subtype_val.comp f.continuous)).isClosed

private theorem push_path_into_adjacent_region [T2Space S] [ConnectedSpace S]
  (hS : IsClosedSurface S)
    {H' C P P' : Drawing S} {Λ r F₂ : Set S} {v₁ v₂ : S}
    (hRig' : IsRigidIn H' (univ \ Λ)) (hΛ_open : IsOpenDisc Λ) (hΛ_cl : IsClosedDisc (closure Λ))
    (hC : C.IsCircuit) (hC_sub' : C.IsSubdrawing H') (hbd : subBd Λ = C.U)
    (hE'_sub : ∀ e ∈ H'.E, e ⊆ univ \ Λ) (hΛ_R : Λ ∈ H'.R)
    (hv₁C : v₁ ∈ C.V) (hv₂C : v₂ ∈ C.V) (hv12 : v₁ ≠ v₂)
    (hPs : P.IsSubdrawing C) (hP's : P'.IsSubdrawing C)
    (hV_inter : P.V ∩ P'.V = {v₁, v₂}) (hsup : C.sup P P' = C)
    (hr_R' : r ∈ H'.R) (hr_sub : r ⊆ univ \ Λ) (hPU_r : P.U ⊆ closure r)
    (hF₂_line : IsLineWithEnds F₂ v₁ v₂) (hF₂_r : F₂ \ {v₁, v₂} ⊆ r)
    (hL_line : IsLineWithEnds P.U v₁ v₂) (hsubBd_cl : subBd (closure Λ) = C.U)
    (hL_cl : P.U ⊆ closure Λ) :
    let L : Set S := P.U
    let Z_edges : Set S := (H'.V \ L) ∪ ⋃ e ∈ H'.E \ P.E, closure e
    let K_reg : Set S := ⋃ s ∈ H'.R \ {r, Λ}, closure s
    let Y : Set S := Z_edges ∪ K_reg ∪ F₂
    Disjoint r (closure Λ) ∧ ∃ h : S ≃ₜ S,
      (∀ x ∈ Y, h x = x) ∧ (h '' L) \ {v₁, v₂} ⊆ r := by
  intro L Z_edges K_reg Y
  have : CompactSpace S := hS.1
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨hv₁F₂, hv₂F₂⟩ := IsLineWithEnds.ends_mem hF₂_line
  have hL_bd : L ⊆ subBd (closure Λ) := hsubBd_cl.symm ▸ hPs.U_subset
  obtain ⟨hdisL, hclL⟩ := isOpen_disjoint_subBd_and_closure_eq hΛ_open.1
  have hr_ne_Λ : r ≠ Λ := by
    intro hrΛ
    obtain ⟨p, hp⟩ := region_nonempty hr_R'
    exact (hr_sub hp).2 (hrΛ ▸ hp)
  have hdis_r_clΛ : Disjoint r (closure Λ) := by
    have hdis_rΛ : Disjoint r Λ := disjoint_left.mpr fun x hxr hxΛ => (hr_sub hxr).2 hxΛ
    rw [hclL, disjoint_union_right, hbd]
    exact ⟨hdis_rΛ, disjoint_left.mpr fun x hxr hxC => region_subset hr_R' hxr
      (hC_sub'.U_subset hxC)⟩
  have hZ_cl : IsClosed Z_edges :=
    (H'.finite_V.subset sdiff_subset).isClosed.union
      ((H'.finite_edges.subset sdiff_subset).isClosed_biUnion fun _ _ => isClosed_closure)
  have hK_cl : IsClosed K_reg :=
    ((finite_R hS H').subset sdiff_subset).isClosed_biUnion
      fun _ _ => isClosed_closure
  have hY_cl : IsClosed Y := (hZ_cl.union hK_cl).union (isClosed_of_isLineWithEnds hF₂_line)
  have hv₁Y : v₁ ∈ Y := Or.inr hv₁F₂
  have hv₂Y : v₂ ∈ Y := Or.inr hv₂F₂
  have hP_H' : P.IsSubdrawing H' := hPs.trans hC_sub'
  have hYL : Y ∩ L ⊆ {v₁, v₂} := by
    rintro x ⟨hxY, hxL⟩
    by_contra hx_not
    have hx1 : x ≠ v₁ := fun h => hx_not (Or.inl h)
    have hx2 : x ≠ v₂ := fun h => hx_not (Or.inr h)
    rcases hxY with (hxZ | hxK) | hxF₂
    · rcases hxZ with hxV | hxE
      · exact hxV.2 hxL
      · obtain ⟨e, ⟨heH', he_not_P⟩, hxe⟩ := mem_iUnion₂.mp hxE
        by_cases hxPV : x ∈ P.V
        · exact he_not_P ((internal_vertex_edges_and_regions hS hRig' hΛ_open hC hC_sub' hbd
            hE'_sub hΛ_R hv₁C hv₂C hv12 hPs hP's hV_inter hsup hr_R' hr_sub hPU_r hxPV hx1 hx2).1
            e heH' hxe)
        · obtain ⟨e₀, he₀P, hxe₀⟩ := P.exists_edge_of_mem hxL hxPV
          have he₀H' : e₀ ∈ H'.E := hP_H'.2 he₀P
          have hx_not_V' : x ∉ H'.V := (he₀H'.2.1 hxe₀).2
          have hxe' : x ∈ e := (H'.closure_diff_V heH').symm ▸ ⟨hxe, hx_not_V'⟩
          exact he_not_P (H'.edge_eq_of_mem heH' he₀H' hxe' hxe₀ ▸ he₀P)
    · obtain ⟨s, ⟨hsR', hs_not⟩, hxs⟩ := mem_iUnion₂.mp hxK
      by_cases hxPV : x ∈ P.V
      · rcases (internal_vertex_edges_and_regions hS hRig' hΛ_open hC hC_sub' hbd hE'_sub hΛ_R
          hv₁C hv₂C hv12 hPs hP's hV_inter hsup hr_R' hr_sub hPU_r hxPV hx1 hx2).2 s hsR' hxs
          with rfl | rfl
        · exact hs_not (Or.inr rfl)
        · exact hs_not (Or.inl rfl)
      · obtain ⟨e₀, he₀P, hxe₀⟩ := P.exists_edge_of_mem hxL hxPV
        have he₀H' : e₀ ∈ H'.E := hP_H'.2 he₀P
        have he₀_s : e₀ ⊆ closure s :=
          edge_subset_closure_of_incident hS he₀H' hsR' ⟨x, hxe₀, hxs⟩
        have he₀_r : e₀ ⊆ closure r :=
          (subset_closure.trans (P.closure_subset_U he₀P)).trans hPU_r
        have he₀_Λ : e₀ ⊆ closure Λ :=
          (subset_closure.trans (P.closure_subset_U he₀P)).trans hL_cl
        rcases region_incident_two hS he₀H' hr_R' hΛ_R hsR'
          he₀_r he₀_Λ he₀_s with h | h | h
        · exact hr_ne_Λ h
        · exact hs_not (Or.inl h.symm)
        · exact hs_not (Or.inr h.symm)
    · exact region_subset hr_R' (hF₂_r ⟨hxF₂, hx_not⟩) (hP_H'.U_subset hxL)
  have hY_dis_Λ : Disjoint Y Λ := by
    refine disjoint_left.mpr fun x hxY hxΛ => ?_
    rcases hxY with (hxZ | hxK) | hxF₂
    · have hxU' : x ∈ H'.U := by
        rcases hxZ with ⟨hxV, _⟩ | hxE
        · exact H'.V_subset_U hxV
        · obtain ⟨e, ⟨heH', _⟩, hxe⟩ := mem_iUnion₂.mp hxE
          exact H'.closure_subset_U heH' hxe
      exact region_subset hΛ_R hxΛ hxU'
    · obtain ⟨s, ⟨hsR', hs_not⟩, hxs⟩ := mem_iUnion₂.mp hxK
      have hs_ne : s ≠ Λ := fun h => hs_not (Or.inr h)
      have hdis_sΛ : Disjoint s Λ :=
        disjoint_left.mpr fun z hzs hzΛ => hs_ne (region_eq_of_mem hsR' hΛ_R hzs hzΛ)
      exact disjoint_left.mp (hdis_sΛ.closure_left hΛ_open.1) hxs hxΛ
    · by_cases hx12 : x ∈ ({v₁, v₂} : Set S)
      · have hxC : x ∈ C.U := by
          rcases hx12 with rfl | rfl
          · exact C.V_subset_U hv₁C
          · exact C.V_subset_U hv₂C
        exact disjoint_left.mp hdisL hxΛ (hbd.symm ▸ hxC)
      · exact disjoint_left.mp hdis_r_clΛ (hF₂_r ⟨hxF₂, hx12⟩) (subset_closure hxΛ)
  have hYD : Y ∩ closure Λ ⊆ subBd (closure Λ) := by
    rintro x ⟨hxY, hx_cl⟩
    rw [hsubBd_cl, ← hbd]
    exact (hclL ▸ hx_cl).resolve_left (disjoint_left.mp hY_dis_Λ hxY)
  obtain ⟨h, hhY, hhL⟩ := push_arc_of_fixed_boundary hS hΛ_cl hL_line hL_bd hY_cl hYD hv₁Y hv₂Y hYL
  have h_compl_r : univ \ (Y ∪ closure Λ) ⊆ r := by
    rintro y ⟨_, hy_not⟩
    have hyY : y ∉ Y := fun h => hy_not (Or.inl h)
    have hy_clΛ : y ∉ closure Λ := fun h => hy_not (Or.inr h)
    have hyU' : y ∉ H'.U := by
      intro hyU'
      by_cases hyV' : y ∈ H'.V
      · by_cases hyL : y ∈ L
        · exact hy_clΛ (hL_cl hyL)
        · exact hyY (Or.inl (Or.inl (Or.inl ⟨hyV', hyL⟩)))
      · obtain ⟨e, heH', hye⟩ := H'.exists_edge_of_mem hyU' hyV'
        by_cases heP : e ∈ P.E
        · exact hy_clΛ (hL_cl (P.closure_subset_U heP (subset_closure hye)))
        · exact hyY (Or.inl (Or.inl (Or.inr (mem_iUnion₂.mpr ⟨e, ⟨heH', heP⟩,
            subset_closure hye⟩))))
    obtain ⟨s, hsR', hys⟩ := exists_region_of_notMem hyU'
    by_cases hs_r : s = r
    · exact hs_r ▸ hys
    · by_cases hs_Λ : s = Λ
      · exact absurd (subset_closure (hs_Λ ▸ hys)) hy_clΛ
      · exact absurd (Or.inl (Or.inr (mem_iUnion₂.mpr ⟨s, ⟨hsR', fun h => h.elim hs_r hs_Λ⟩,
          subset_closure hys⟩))) hyY
  have hhL_r : (h '' L) \ {v₁, v₂} ⊆ r := by
    rintro y ⟨⟨x, hxL, rfl⟩, hy12⟩
    refine h_compl_r ⟨mem_univ _, ?_⟩
    rintro (hyY | hy_clΛ)
    · have hhx : h (h x) = h x := hhY (h x) hyY
      have hx_eq : h x = x := h.injective hhx
      have hxY : x ∈ Y := hx_eq ▸ hyY
      exact hy12 (hx_eq.symm ▸ hYL ⟨hxY, hxL⟩)
    · exact hy12 (hhL ⟨⟨x, hxL, rfl⟩, hy_clΛ⟩)
  exact ⟨hdis_r_clΛ, h, hhY, hhL_r⟩

private theorem frontier_of_pushed_cycle [T2Space S] {H' C P P' : Drawing S}
    {Λ r F₂ : Set S} {v₁ v₂ : S}
    (hC_sub' : C.IsSubdrawing H') (hPs : P.IsSubdrawing C) (hP's : P'.IsSubdrawing C)
    (hV_inter : P.V ∩ P'.V = {v₁, v₂}) (hE_disj : Disjoint P.E P'.E) (hsup : C.sup P P' = C)
    (hsubBd_cl : subBd (closure Λ) = C.U)
    (hv₁F₂ : v₁ ∈ F₂) (hv₂F₂ : v₂ ∈ F₂)
    (h : S ≃ₜ S) :
    let L : Set S := P.U
    let Y : Set S := ((H'.V \ L) ∪ ⋃ e ∈ H'.E \ P.E, closure e) ∪
      (⋃ s ∈ H'.R \ {r, Λ}, closure s) ∪ F₂
    (∀ x ∈ Y, h x = x) → frontier (h '' closure Λ) = h '' L ∪ P'.U := by
  intro L Y hhY
  have hv₁Y : v₁ ∈ Y := Or.inr hv₁F₂
  have hv₂Y : v₂ ∈ Y := Or.inr hv₂F₂
  have hP_H' : P.IsSubdrawing H' := hPs.trans hC_sub'
  have hP'U_Y : P'.U ⊆ Y := by
    rw [P'.U_eq]
    refine union_subset (fun x hx => ?_) (iUnion₂_subset fun e heP' x hxe => ?_)
    · by_cases hxL : x ∈ L
      · have hxV_P : x ∈ P.V := by
          by_contra hx_not_PV
          obtain ⟨e₀, he₀P, hxe₀⟩ := P.exists_edge_of_mem hxL hx_not_PV
          exact ((hP_H'.2 he₀P).2.1 hxe₀).2 (hC_sub'.1 (hP's.1 hx))
        have hx12 : x ∈ ({v₁, v₂} : Set S) := hV_inter ▸ ⟨hxV_P, hx⟩
        rcases hx12 with rfl | rfl
        · exact hv₁Y
        · exact hv₂Y
      · exact Or.inl (Or.inl (Or.inl ⟨hC_sub'.1 (hP's.1 hx), hxL⟩))
    · have he_not_P : e ∉ P.E := disjoint_right.mp hE_disj heP'
      exact Or.inl (Or.inl (Or.inr (mem_iUnion₂.mpr ⟨e, ⟨hC_sub'.2 (hP's.2 heP'), he_not_P⟩, hxe⟩)))
  have hCU_union : C.U = L ∪ P'.U := by
    rw [← hsup, Drawing.sup_U hPs hP's]
  let D_pushed : Set S := h '' (closure Λ)
  have hfr_D_pushed : frontier D_pushed = h '' L ∪ P'.U := by
    rw [← h.image_frontier, ← subBd_eq_frontier, hsubBd_cl, hCU_union, image_union]
    congr 1
    ext x
    exact ⟨fun ⟨y, hy, hyx⟩ => hyx ▸ (hhY y (hP'U_Y hy)).symm ▸ hy,
      fun hx => ⟨x, hx, hhY x (hP'U_Y hx)⟩⟩
  exact hfr_D_pushed

/-- Given the path `P` of `C` between `v₁` and `v₂` with `P.U ⊆ closure r` (`r ∈ H'.R`,
`r ⊆ univ \ Λ`) and an arc `F₂` between `v₁` and `v₂` with `F₂ \ {v₁, v₂} ⊆ r`, pushing `P.U` into
`r` and applying rigidity of `H'` in `univ \ Λ` produces a closed disc `Δ₂` bounded by `F₂ ∪ P.U`
with `Δ₂ ∩ closure Λ = P.U` and `Δ₂ ∩ H'.U = P.U`. -/
theorem exists_pushed_disc_of_arc [T2Space S] [ConnectedSpace S] (hS : IsClosedSurface S)
    {H' C P P' : Drawing S} {Λ r F₂ : Set S} {v₁ v₂ : S}
    (hRig' : IsRigidIn H' (univ \ Λ)) (hΛ_open : IsOpenDisc Λ) (hΛ_cl : IsClosedDisc (closure Λ))
    (hC : C.IsCircuit) (hC_sub' : C.IsSubdrawing H') (hbd : subBd Λ = C.U)
    (hE'_sub : ∀ e ∈ H'.E, e ⊆ univ \ Λ) (hΛ_R : Λ ∈ H'.R)
    (hv₁C : v₁ ∈ C.V) (hv₂C : v₂ ∈ C.V) (hv12 : v₁ ≠ v₂)
    (hP : P.IsPathBetween v₁ v₂) (hPs : P.IsSubdrawing C) (hP's : P'.IsSubdrawing C)
    (hV_inter : P.V ∩ P'.V = {v₁, v₂}) (hE_disj : Disjoint P.E P'.E) (hsup : C.sup P P' = C)
    (hr_R' : r ∈ H'.R) (hr_sub : r ⊆ univ \ Λ) (hPU_r : P.U ⊆ closure r)
    (hF₂_line : IsLineWithEnds F₂ v₁ v₂) (hF₂_r : F₂ \ {v₁, v₂} ⊆ r) :
    ∃ Δ₂ : Set S, IsClosedDisc Δ₂ ∧ subBd Δ₂ = F₂ ∪ P.U ∧
      Δ₂ ∩ closure Λ = P.U ∧ Δ₂ ∩ H'.U = P.U := by
  have : CompactSpace S := hS.1
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  let L : Set S := P.U
  obtain ⟨f_L, hfL0, hfL1⟩ := isLine_of_isPathBetween hP hv12
  have hL_line : IsLineWithEnds L v₁ v₂ := ⟨f_L, hfL0, hfL1⟩
  obtain ⟨hv₁L, hv₂L⟩ := IsLineWithEnds.ends_mem hL_line
  obtain ⟨hv₁F₂, hv₂F₂⟩ := IsLineWithEnds.ends_mem hF₂_line
  have hO_bd : IsOArc (subBd Λ) := hbd ▸ isOArc_of_isCircuit hC
  have hsubBd_cl : subBd (closure Λ) = C.U :=
    (subBd_closure_eq_subBd_of_isOpenDisc hS hΛ_open hO_bd hΛ_cl).trans hbd
  have hL_cl : L ⊆ closure Λ := hPs.U_subset.trans (hbd ▸ fun _ h => h.1)
  obtain ⟨hdisL, _⟩ := isOpen_disjoint_subBd_and_closure_eq hΛ_open.1
  let Z_edges : Set S := (H'.V \ L) ∪ ⋃ e ∈ H'.E \ P.E, closure e
  let K_reg : Set S := ⋃ s ∈ H'.R \ {r, Λ}, closure s
  let Y : Set S := Z_edges ∪ K_reg ∪ F₂
  have hv₁Y : v₁ ∈ Y := Or.inr hv₁F₂
  have hv₂Y : v₂ ∈ Y := Or.inr hv₂F₂
  have hP_H' : P.IsSubdrawing H' := hPs.trans hC_sub'
  obtain ⟨hdis_r_clΛ, h, hhY, hhL_r⟩ :=
    push_path_into_adjacent_region hS hRig' hΛ_open hΛ_cl hC hC_sub' hbd hE'_sub hΛ_R
      hv₁C hv₂C hv12 hPs hP's hV_inter hsup hr_R' hr_sub hPU_r hF₂_line hF₂_r
      hL_line hsubBd_cl hL_cl
  have hh_v₁ : h v₁ = v₁ := hhY v₁ hv₁Y
  have hh_v₂ : h v₂ = v₂ := hhY v₂ hv₂Y
  let F' : Set S := F₂ ∪ h '' L
  have hF₂_img : h '' F₂ = F₂ := by
    ext x
    exact ⟨fun ⟨y, hy, hyx⟩ => hyx ▸ (hhY y (Or.inr hy)).symm ▸ hy,
      fun hx => ⟨x, hx, hhY x (Or.inr hx)⟩⟩
  have hF'_img : F' = h '' (F₂ ∪ L) := by
    change F₂ ∪ h '' L = _
    rw [image_union, hF₂_img]
  have hF₂L_inter : F₂ ∩ L ⊆ {v₁, v₂} := by
    rintro x ⟨hxF₂, hxL⟩
    by_contra hx12
    exact region_subset hr_R' (hF₂_r ⟨hxF₂, hx12⟩) (hP_H'.U_subset hxL)
  have hF'_oArc : IsOArc F' := by
    rw [hF'_img]
    exact (isOArc_union hF₂_line hL_line hF₂L_inter).image h.continuous.continuousOn
      h.symm.continuous.continuousOn (fun x _ => h.symm_apply_apply x)
  have hF'_r : F' \ {v₁, v₂} ⊆ r := by
    rintro x ⟨hxF₂ | hxL', hx12⟩
    · exact hF₂_r ⟨hxF₂, hx12⟩
    · exact hhL_r ⟨hxL', hx12⟩
  have hv₁_S' : v₁ ∈ univ \ Λ :=
    ⟨mem_univ v₁, fun hv₁Λ => disjoint_left.mp hdisL hv₁Λ (hbd.symm ▸ C.V_subset_U hv₁C)⟩
  have hv₂_S' : v₂ ∈ univ \ Λ :=
    ⟨mem_univ v₂, fun hv₂Λ => disjoint_left.mp hdisL hv₂Λ (hbd.symm ▸ C.V_subset_U hv₂C)⟩
  have hF'_sub : F' ⊆ univ \ Λ := by
    intro x hxF'
    by_cases hx12 : x ∈ ({v₁, v₂} : Set S)
    · rcases hx12 with rfl | rfl
      · exact hv₁_S'
      · exact hv₂_S'
    · exact hr_sub (hF'_r ⟨hxF', hx12⟩)
  have hv₁F' : v₁ ∈ F' := Or.inl hv₁F₂
  have hv₂F' : v₂ ∈ F' := Or.inl hv₂F₂
  have hF'_U : F' ∩ H'.U = {v₁, v₂} := by
    apply subset_antisymm
    · rintro x ⟨hxF', hxU'⟩
      by_contra hx12
      exact region_subset hr_R' (hF'_r ⟨hxF', hx12⟩) hxU'
    · rintro x (rfl | rfl)
      · exact ⟨hv₁F', H'.V_subset_U (hC_sub'.1 hv₁C)⟩
      · exact ⟨hv₂F', H'.V_subset_U (hC_sub'.1 hv₂C)⟩
  have hF'_V : F' ∩ H'.V = {v₁, v₂} := by
    apply subset_antisymm
    · exact (inter_subset_inter_right F' H'.V_subset_U).trans (hF'_U.subset)
    · rintro x (rfl | rfl)
      · exact ⟨hv₁F', hC_sub'.1 hv₁C⟩
      · exact ⟨hv₂F', hC_sub'.1 hv₂C⟩
  have hFU'_sub : F' ∩ H'.U ⊆ H'.V := by
    rw [hF'_U, ← hF'_V]
    exact inter_subset_right
  have hFV'_card : (F' ∩ H'.V).ncard ≤ 2 := by
    rw [hF'_V, ncard_pair hv12]
  obtain ⟨Δ', hΔ'_sub, hDial'⟩ := hRig' F' hF'_sub hF'_oArc hFU'_sub hFV'_card
  have hF'_sub_Δ' : F' ⊆ Δ' := by
    intro x hx
    have hx_bd : x ∈ subBd Δ' := hDial'.2.1.symm ▸ hx
    exact hDial'.1.isClosed.closure_eq ▸ hx_bd.1
  have hΔ'U_sub : Δ' ∩ H'.U ⊆ F' :=
    dial_inter_sub_of_pushed hS hRig' hΛ_open hC hC_sub' hbd hv₁C hv₂C hv12 hr_R' hr_sub
      hF'_r hF'_V hDial'
  have hΔ'U_eq : Δ' ∩ H'.U = {v₁, v₂} := by
    apply subset_antisymm
    · intro x hx
      exact hF'_U ▸ ⟨hΔ'U_sub hx, hx.2⟩
    · rintro x (rfl | rfl)
      · exact ⟨hF'_sub_Δ' hv₁F', H'.V_subset_U (hC_sub'.1 hv₁C)⟩
      · exact ⟨hF'_sub_Δ' hv₂F', H'.V_subset_U (hC_sub'.1 hv₂C)⟩
  -- Next show `Δ' \ subBd Δ' ⊆ r` and `Δ' ∩ h '' (closure Λ) = h '' L`.
  let U_open : Set S := Δ' \ subBd Δ'
  have hU_open_disc : IsOpenDisc U_open := (IsClosedDisc.isOpenDisc_diff_subBd hS hDial'.1).1
  have hU_open_cl : closure U_open = Δ' := ((IsClosedDisc.isOpenDisc_diff_subBd hS hDial'.1).2).1
  have hU_dis_U' : Disjoint U_open H'.U := by
    refine disjoint_left.mpr fun x hxU_open hxU' => hxU_open.2 ?_
    rw [hDial'.2.1]
    exact hΔ'U_sub ⟨hxU_open.1, hxU'⟩
  obtain ⟨f₂, hf₂0, hf₂1⟩ := hF₂_line
  let mid : I := ⟨1 / 2, by norm_num, by norm_num⟩
  let p₂ : S := (f₂ mid).1
  have hp₂_F₂ : p₂ ∈ F₂ \ {v₁, v₂} := by
    refine ⟨(f₂ mid).2, ?_⟩
    rintro (h1 | h2)
    · have : mid = 0 := f₂.injective (Subtype.ext (h1.trans hf₂0.symm))
      exact absurd (congrArg Subtype.val this) (by norm_num [mid])
    · have : mid = 1 := f₂.injective (Subtype.ext (h2.trans hf₂1.symm))
      exact absurd (congrArg Subtype.val this) (by norm_num [mid])
  have hp₂_r : p₂ ∈ r := hF₂_r hp₂_F₂
  have hp₂_cl : p₂ ∈ closure U_open := by
    rw [hU_open_cl]
    exact hF'_sub_Δ' (Or.inl hp₂_F₂.1)
  obtain ⟨z₀, hz₀_r, hz₀_U⟩ := mem_closure_iff.mp hp₂_cl r (region_isOpen hr_R') hp₂_r
  have hU_sub_r : U_open ⊆ r :=
    subset_region hr_R' hU_open_disc.isPathConnected.isConnected.isPreconnected hU_dis_U'
      hz₀_U hz₀_r
  let D_pushed : Set S := h '' (closure Λ)
  have hD_pushed_cl : IsClosed D_pushed := h.isClosedMap _ isClosed_closure
  have hfr_D_pushed : frontier D_pushed = h '' L ∪ P'.U :=
    frontier_of_pushed_cycle hC_sub' hPs hP's hV_inter hE_disj hsup hsubBd_cl hv₁F₂ hv₂F₂ h hhY
  have hU_dis_fr : Disjoint U_open (frontier D_pushed) := by
    rw [hfr_D_pushed, disjoint_union_right]
    refine ⟨disjoint_left.mpr fun x hxU hxL' => hxU.2 (hDial'.2.1 ▸ Or.inr hxL'), ?_⟩
    exact disjoint_left.mpr fun x hxU hxP' =>
      region_subset hr_R' (hU_sub_r hxU) (hC_sub'.U_subset (hP's.U_subset hxP'))
  have hU_dis_Dp : Disjoint U_open D_pushed := by
    rcases subset_or_disjoint_of_frontier hD_pushed_cl
      hU_open_disc.isPathConnected.isConnected.isPreconnected hU_dis_fr with hsub | hdis
    · exfalso
      have hΔ'_Dp : Δ' ⊆ D_pushed := hU_open_cl ▸ hD_pushed_cl.closure_subset_iff.mpr hsub
      have hp₂_Dp : p₂ ∈ D_pushed := hΔ'_Dp (hF'_sub_Δ' (Or.inl hp₂_F₂.1))
      obtain ⟨w, hw_cl, hwp₂⟩ := hp₂_Dp
      have hw_eq : w = p₂ := h.injective (hwp₂.trans (hhY p₂ (Or.inr hp₂_F₂.1)).symm)
      exact disjoint_left.mp hdis_r_clΛ hp₂_r (hw_eq ▸ hw_cl)
    · exact hdis
  have hΔ'_inter_Dp : Δ' ∩ D_pushed = h '' L := by
    apply subset_antisymm
    · rintro x ⟨hxΔ', hxDp⟩
      by_cases hx_bd : x ∈ subBd Δ'
      · rw [hDial'.2.1] at hx_bd
        rcases hx_bd with hxF₂ | hxL'
        · obtain ⟨w, hw_cl, hwx⟩ := hxDp
          have hhw : h x = x := hhY x (Or.inr hxF₂)
          have hw_eq : w = x := h.injective (hwx.trans hhw.symm)
          rw [← hw_eq] at hxF₂ ⊢
          by_cases hw12 : w ∈ ({v₁, v₂} : Set S)
          · rcases mem_insert_iff.mp hw12 with hw1 | hw2
            · rw [hw1]
              exact ⟨v₁, hv₁L, hh_v₁⟩
            · rw [mem_singleton_iff.mp hw2]
              exact ⟨v₂, hv₂L, hh_v₂⟩
          · exact absurd hw_cl (disjoint_left.mp hdis_r_clΛ (hF₂_r ⟨hxF₂, hw12⟩))
        · exact hxL'
      · exact absurd hxDp (disjoint_left.mp hU_dis_Dp ⟨hxΔ', hx_bd⟩)
    · rintro x ⟨w, hwL, rfl⟩
      exact ⟨hF'_sub_Δ' (Or.inr ⟨w, hwL, rfl⟩), ⟨w, hL_cl hwL, rfl⟩⟩
  let Δ₂ : Set S := h.symm '' Δ'
  have hΔ₂_disc : IsClosedDisc Δ₂ :=
    (hDial'.1.image h.symm.continuous.continuousOn h.continuous.continuousOn
      (fun x _ => h.apply_symm_apply x)).1
  have hΔ₂_bd : subBd Δ₂ = F₂ ∪ L := by
    rw [subBd_eq_frontier, ← h.symm.image_frontier, ← subBd_eq_frontier, hDial'.2.1,
      hF'_img, ← image_comp, h.symm_comp_self, image_id]
  have hΔ₂_clΛ : Δ₂ ∩ closure Λ = L := by
    have h1 : closure Λ = h.symm '' D_pushed := by
      change closure Λ = h.symm '' (h '' (closure Λ))
      rw [← image_comp, h.symm_comp_self, image_id]
    have h2 : L = h.symm '' (h '' L) := by
      rw [← image_comp, h.symm_comp_self, image_id]
    rw [h1, h2, ← image_inter h.symm.injective, hΔ'_inter_Dp]
  have hΔ₂_U' : Δ₂ ∩ H'.U = L := by
    apply subset_antisymm
    · rintro x ⟨⟨y, hyΔ', rfl⟩, hxU'⟩
      by_contra hxL
      have hxY : h.symm y ∈ Y := by
        by_cases hxV' : h.symm y ∈ H'.V
        · exact Or.inl (Or.inl (Or.inl ⟨hxV', hxL⟩))
        · obtain ⟨e, heH', hxe⟩ := H'.exists_edge_of_mem hxU' hxV'
          have he_not_P : e ∉ P.E := fun heP =>
            hxL (P.closure_subset_U heP (subset_closure hxe))
          exact Or.inl (Or.inl (Or.inr (mem_iUnion₂.mpr ⟨e, ⟨heH', he_not_P⟩, subset_closure hxe⟩)))
      have hy_eq : h (h.symm y) = h.symm y := hhY (h.symm y) hxY
      rw [h.apply_symm_apply] at hy_eq
      rw [← hy_eq] at hxU' hxL
      have hy12 : y ∈ ({v₁, v₂} : Set S) := hΔ'U_eq ▸ ⟨hyΔ', hxU'⟩
      rcases mem_insert_iff.mp hy12 with hy1 | hy2
      · exact hxL (hy1 ▸ hv₁L)
      · exact hxL (mem_singleton_iff.mp hy2 ▸ hv₂L)
    · intro x hxL
      exact ⟨⟨h x, hF'_sub_Δ' (Or.inr ⟨x, hxL, rfl⟩), h.symm_apply_apply x⟩, hP_H'.U_subset hxL⟩
  exact ⟨Δ₂, hΔ₂_disc, hΔ₂_bd, hΔ₂_clΛ, hΔ₂_U'⟩

end GraphMinor.GM14
