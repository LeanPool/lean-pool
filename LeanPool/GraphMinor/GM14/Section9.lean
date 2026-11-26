/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Section9a
public import LeanPool.GraphMinor.GM14.Section9b
public import LeanPool.GraphMinor.GM14.Section9Reroute
public import LeanPool.GraphMinor.GM14.Section8
public import LeanPool.GraphMinor.GM15.Cited
import LeanPool.GraphMinor.GM14.Section5
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM10.Section12

import LeanPool.GraphMinor.GM09.Bridge

import LeanPool.GraphMinor.GM12.Section710

/-!
# Graph Minors XIV, Section 9: Constant Radius Discs and Battlefields

This file completes the formalization of Section 9 ("Constant Radius Discs", pages 43–49) of
N. Robertson and P. D. Seymour, *Graph Minors. XIV. Extending an embedding*, J. Combin. Theory
Ser. B **65** (1995) 23–50, re-exporting `GraphMinor.GM14.Section9a` (`(9.1)`, `(9.2)`, `(9.4)`) and
`GraphMinor.GM14.Section9b` (`(9.3)`, `(9.5)`) and proving:

- `theorem_9_6` (Graph Minors XIV, (9.6), pages 47–49): existence of a `(3β + 3)`-zone `Λ` and an
  `α`-normal closed disc `Δ ⊇ Λ` around `z ∈ A(H)` such that either `(G, Ω₀)` has a crooked
  transaction of cardinality `≥ π` whose ends are free in the cleared tangle `T'` and whose paths
  are
  `H ∩ (Σ - Λ)`-paths in `G`, or `(α⁻¹(Δ) ∪ J, α⁻¹(bd(Δ)))` has no crooked transaction of
  cardinality `≥ π`.
-/

@[expose] public section

namespace GraphMinor.GM14

open Set Function Topology Graph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM10
  GraphMinor.GM11 Hypergraph

universe u v w

variable {S : Type w} [TopologicalSpace S]

/-- Any vertex `v ∈ H.V` on `subBd Λ` for an open set `Λ` belongs to `(clearedSubdrawing H Λ).V`. -/
theorem mem_clearedSubdrawing_V_of_mem_subBd [T1Space S] {H : Drawing S} {Λ : Set S}
    (hOpen : IsOpen Λ) {v : S} (hvH : v ∈ H.V) (hvBd : v ∈ subBd Λ) :
    v ∈ (clearedSubdrawing H Λ).V := by
  have hv_not_Λ : v ∉ Λ := fun hvΛ => by
    rw [subBd_eq_frontier] at hvBd
    exact hvBd.2 (hOpen.interior_eq.symm ▸ hvΛ)
  exact Or.inl ⟨⟨hvH, mem_univ v, hv_not_Λ⟩, hvH⟩

/-- If `Λ` is open, `Λ ⊆ Δ`, and `x ⊆ Λ`, then `x ⊆ Δ \ subBd Δ`. -/
theorem subset_diff_subBd_of_subset_open {Λ Δ x : Set S}
    (hOpen : IsOpen Λ) (hΛ_sub : Λ ⊆ Δ) (hx_sub : x ⊆ Λ) :
    x ⊆ Δ \ subBd Δ := by
  intro p hp
  have hpΛ : p ∈ Λ := hx_sub hp
  refine ⟨hΛ_sub hpΛ, fun hpBd => ?_⟩
  rw [subBd_eq_frontier] at hpBd
  exact hpBd.2 (interior_maximal hΛ_sub hOpen hpΛ)

/-- If `G' ≤ G_amb`, `J ≤ G_amb`, `IsGraphSegregation G' S_seg`, `IsClosed Δ`, and
`IsPullbackPerm S_seg α_pt (subBd Δ) Ω_star`, then
`Ω_star.bar ⊆ V(subgraphUnion G_amb J (arrangementPullbackGraph G' S_seg α_disc α_pt Δ))`. -/
theorem pullback_bar_subset_subgraphUnion {α : Type u} {β : Type v}
    {G_amb G' J : Graph α β} {S_seg : Set (Society α β)}
    {α_disc : Society α β → Set S} {α_pt : α → S} {Δ : Set S} {Ω_star : CyclicPerm α}
    (hG'_le : G' ≤ G_amb) (hJ_le : J ≤ G_amb)
    (hSeg : IsGraphSegregation G' S_seg) (hClosed : IsClosed Δ)
    (hPull : IsPullbackPerm S_seg α_pt (subBd Δ) Ω_star) :
    Ω_star.bar ⊆ V(subgraphUnion G_amb J (arrangementPullbackGraph G' S_seg α_disc α_pt Δ)) := by
  intro x hx
  rw [hPull.1] at hx
  obtain ⟨hx_seg, hx_bd⟩ := hx
  obtain ⟨S₀, hS₀_in, hx_bar₀⟩ := mem_iUnion₂.mp hx_seg
  have hx_G' : x ∈ V(G') := (hSeg.le S₀ hS₀_in).vertexSet_mono (S₀.bar_subset hx_bar₀)
  have hx_Δ : α_pt x ∈ Δ := by
    have hcl : α_pt x ∈ closure Δ := hx_bd.1
    rwa [hClosed.closure_eq] at hcl
  have hx_pull : x ∈ V(arrangementPullbackGraph G' S_seg α_disc α_pt Δ) := by
    simp only [arrangementPullbackGraph, vertexSet_restrict, vertexSet_induce, mem_inter_iff,
      mem_union, mem_ofPred_eq]
    exact ⟨Or.inr ⟨hx_seg, hx_Δ⟩, hx_G'⟩
  have hPull_le : arrangementPullbackGraph G' S_seg α_disc α_pt Δ ≤ G_amb :=
    (Graph.restrict_le.trans (G'.induce_le inter_subset_right)).trans hG'_le
  exact (le_subgraphUnion_right hJ_le hPull_le).vertexSet_mono hx_pull

/-- First part of the proof of Graph Minors XIV, (9.6) (page 48):
Given a battlefield `(Λ, C, X_bf)` around `z` of size `β`, let `D₀ = discIns (closure Λ) C` be the
closed disc bounded by `U(C)`. By (5.5) (`theorem_5_5_step_of_isPreconnected`), there is a circuit
`C₂` of `H` in `Λ` bounding a closed disc `closure Λ_C₂ ⊆ Λ` with `D₀ ⊆ Λ_C₂` and
`regionalDistance H (closure Λ_C₂) (subBd Λ) ≥ β / 2`; and by (7.7) (`theorem_7_7_proof`), there is
an
`α`-normal `O`-arc `F₂ ⊆ closure Λ_C₂` bounding a closed disc `Δ₂ ⊆ closure Λ_C₂` with `D₀ ⊆ Δ₂`
and `x ⊆ Δ₂ \ subBd Δ₂` for every `x ∈ A(H)` with `d(z, x) < β`. -/
theorem exists_nested_discs_9_6 [T2Space S] {α : Type u} {β : Type v}
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {G' : Graph α β} {H : Drawing S} {η' : SpanEmbedding H G'}
    {θ beta : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {z Λ : Set S} {C : Drawing S} {X_bf : Set S}
    {S_seg : Set (Society α β)} {α_disc : Society α β → Set S} {α_pt : α → S}
    (hMetric : HasTangleMetric H θ T d)
    (hBf : IsBattlefield H T d θ beta z Λ C X_bf)
    (hSeg : IsThreeSegregation G' S_seg)
    (hLoc : IsTangleLocal G' H η' T S_seg)
    (hArr : IsSurfaceArrangement S_seg α_disc α_pt)
    (hComp : IsCompatibleWith G' H η' S_seg α_disc α_pt) :
    ∃ (C₂ : Drawing S) (Λ_C₂ F₂ Δ₂ : Set S),
      C₂.IsSubdrawing H ∧ C₂.IsCircuit ∧
      IsOpenDisc Λ_C₂ ∧ closure Λ_C₂ ⊆ Λ ∧ IsClosedDisc (closure Λ_C₂) ∧
      subBd (closure Λ_C₂) = C₂.U ∧ closure Λ_C₂ \ C₂.U = Λ_C₂ ∧
      beta / 2 ≤ regionalDistance H (closure Λ_C₂) (subBd Λ) ∧
      IsOArc F₂ ∧ F₂ ⊆ closure Λ_C₂ ∧ IsArrangementNormal S_seg α_disc α_pt F₂ ∧
      IsClosedDisc Δ₂ ∧ subBd Δ₂ = F₂ ∧ Δ₂ ⊆ closure Λ_C₂ ∧
      discIns (closure Λ) C ⊆ Δ₂ ∧
      ∀ x ∈ H.A, d z x < beta → x ⊆ Δ₂ \ subBd Δ₂ := by
  have : ConnectedSpace S := hConn
  obtain ⟨hbeta4, _, hθ_bf, hz⟩ := hBf.params_valid
  have hZone : IsLambdaZoneAround H d (3 * beta + 3) z Λ := hBf.isZone
  obtain ⟨hC, hCs, hCU_sub_Λ, _⟩ := hBf.circuit_and_paths
  have hdist_ge : 1 + beta / 2 ≤ regionalDistance H C.U (subBd Λ) := hBf.regionalDistance_ge
  obtain ⟨Δ₀, hOD₀, hΔ₀_sub_Λ, hbd_Δ₀, hΔ₀_atoms⟩ := hBf.openDisc_includes
  have hbd_clΛ : subBd (closure Λ) = subBd Λ := by
    rw [IsClosedDisc.subBd_eq_discBd hS hZone.isClosedDisc_closure,
      discBd_closure_eq_subBd hS hZone.isOpenDisc hZone.isOArc_bd hZone.isClosedDisc_closure]
  obtain ⟨hdisL, hclL⟩ := isOpen_disjoint_subBd_and_closure_eq hZone.isOpenDisc.1
  have hdiffΛ : closure Λ \ subBd (closure Λ) = Λ := by
    rw [hbd_clΛ]
    ext y
    exact ⟨fun ⟨hycl, hynot⟩ => (hclL ▸ hycl).resolve_right hynot,
      fun hy => ⟨subset_closure hy, disjoint_left.mp hdisL hy⟩⟩
  have hCU_oArc : IsOArc C.U := isOArc_of_isCircuit hC
  -- Apply (5.5) (`theorem_5_5_step_of_isPreconnected`) to `Z = C.U` in `closure Λ`.
  obtain ⟨C₂, Λ_C₂, hC₂H, hC₂, hC₂U_sub, hOpen_C₂, hcl_C₂_sub, hcl_C₂_disc,
    hbd_C₂, hbd_cl_C₂, hdiff_C₂, hCU_sub_Λ_C₂, hdist_C₂⟩ :=
    theorem_5_5_step_of_isPreconnected hS H hZone.isClosedDisc_closure
      (hdiffΛ.symm ▸ hCU_sub_Λ) (IsOArc.nonempty hCU_oArc) (IsOArc.isPreconnected hCU_oArc)
      (k := 1 + beta / 2) (by omega) (hbd_clΛ.symm ▸ hdist_ge)
  rw [hdiffΛ] at hcl_C₂_sub
  rw [hbd_clΛ] at hdist_C₂
  -- Show `D₀ = discIns (closure Λ) C` satisfies `D₀ ⊆ Λ_C₂` and `D₀ \ C.U = Δ₀`.
  let D₀ := discIns (closure Λ) C
  have hCU_sub_clΛ : C.U ⊆ closure Λ := hCU_sub_Λ.trans subset_closure
  obtain ⟨⟨hD₀_sub_clΛ, hD₀_disc, hD₀_bd⟩, hD₀_uniq⟩ :=
    discIns_spec hZone.isClosedDisc_closure hC hCU_sub_clΛ
  have hbd_D₀ : subBd D₀ = C.U := by
    rw [IsClosedDisc.subBd_eq_discBd hS hD₀_disc, hD₀_bd]
  obtain ⟨D₀', ⟨hD₀'_sub, hD₀'_disc, hD₀'_bd, -⟩, -⟩ :=
    disc_oArc (closure Λ_C₂) C.U hcl_C₂_disc (hCU_sub_Λ_C₂.trans subset_closure) hCU_oArc
  have hD₀'_eq : D₀' = D₀ :=
    hD₀_uniq D₀' (hD₀'_sub.trans (hcl_C₂_sub.trans subset_closure)) hD₀'_disc hD₀'_bd
  have hD₀_sub_cl_C₂ : D₀ ⊆ closure Λ_C₂ := hD₀'_eq ▸ hD₀'_sub
  have hD₀_sub_Λ_C₂ : D₀ ⊆ Λ_C₂ := by
    rw [← hdiff_C₂]
    intro x hxD
    refine ⟨hD₀_sub_cl_C₂ hxD, fun hxC₂ => ?_⟩
    have hx_fr_C₂ : x ∈ frontier (closure Λ_C₂) := by
      rwa [← subBd_eq_frontier, hbd_cl_C₂]
    have hx_fr_D₀ : x ∈ frontier D₀ :=
      ⟨subset_closure hxD, fun hxi => hx_fr_C₂.2 (interior_mono hD₀_sub_cl_C₂ hxi)⟩
    rw [← subBd_eq_frontier, hbd_D₀] at hx_fr_D₀
    exact (hdiff_C₂ ▸ hCU_sub_Λ_C₂ hx_fr_D₀).2 hxC₂
  -- Show `Δ₀ = D₀ \ C.U`.
  obtain ⟨p₀, hp₀⟩ := hOD₀.isPathConnected.isConnected.nonempty
  obtain ⟨hdis₀, hcl₀⟩ := isOpen_disjoint_subBd_and_closure_eq hOD₀.1
  have hΔ₀_sub_diff : Δ₀ ⊆ closure Λ \ C.U := fun x hx =>
    ⟨subset_closure (hΔ₀_sub_Λ hx), disjoint_left.mp (hbd_Δ₀ ▸ hdis₀) hx⟩
  let K := connectedComponentIn (closure Λ \ C.U) p₀
  have hΔ₀_sub_K : Δ₀ ⊆ K :=
    hOD₀.isPathConnected.isConnected.isPreconnected.subset_connectedComponentIn hp₀ hΔ₀_sub_diff
  have hK_sub_diff : K ⊆ closure Λ \ C.U := connectedComponentIn_subset (closure Λ \ C.U) p₀
  have hK_dis_fr : Disjoint K (frontier Δ₀) := by
    rw [← subBd_eq_frontier, hbd_Δ₀]
    exact disjoint_of_subset_left hK_sub_diff disjoint_sdiff_left
  have hK_sub_cl₀ : K ⊆ closure Δ₀ :=
    subset_of_disjoint_frontier isPreconnected_connectedComponentIn isClosed_closure
      (hK_dis_fr.mono_right frontier_closure_subset)
      (mem_connectedComponentIn (hΔ₀_sub_diff hp₀)) (subset_closure hp₀)
  have hK_sub_Δ₀ : K ⊆ Δ₀ := fun x hx =>
    ((hbd_Δ₀ ▸ hcl₀) ▸ hK_sub_cl₀ hx).resolve_right (hK_sub_diff hx).2
  have hK_eq_Δ₀ : K = Δ₀ := subset_antisymm hK_sub_Δ₀ hΔ₀_sub_K
  have hΔ₀_comp : Δ₀ ∈ componentsIn (closure Λ \ C.U) := ⟨p₀, hΔ₀_sub_diff hp₀, hK_eq_Δ₀⟩
  have hdis_Δ₀_bd : Disjoint Δ₀ (discBd (closure Λ)) := by
    rw [← IsClosedDisc.subBd_eq_discBd hS hZone.isClosedDisc_closure, hbd_clΛ]
    exact disjoint_of_subset_left hΔ₀_sub_Λ hdisL
  have hD₀_eq_choose : D₀ = (disc_oArc (closure Λ) C.U hZone.isClosedDisc_closure hCU_sub_clΛ
    hCU_oArc).choose := by
    simp only [D₀, discIns, hZone.isClosedDisc_closure, hCU_sub_clΛ, hCU_oArc, and_self, dite_true]
  have hΔ₀_eq_D₀_diff : Δ₀ = D₀ \ subBd D₀ := by
    rw [hbd_D₀, hD₀_eq_choose]
    exact (disc_oArc (closure Λ) C.U hZone.isClosedDisc_closure hCU_sub_clΛ
      hCU_oArc).choose_spec.1.2.2.2.2.2
      Δ₀ hΔ₀_comp hdis_Δ₀_bd
  have hdisj_C₂_C : Disjoint C₂.V C.V := by
    refine disjoint_left.mpr fun v hv₂ hv => ?_
    have hv_Λ_C₂ : v ∈ Λ_C₂ := hCU_sub_Λ_C₂ (C.V_subset_U hv)
    exact (hdiff_C₂ ▸ hv_Λ_C₂).2 (C₂.V_subset_U hv₂)
  have hrefl := (GM11.gm15_theorem_9_1 H θ T d hS hConn hMetric).2.1 z hz
  -- Apply (7.7) (`theorem_7_7_proof`) to `Δ₁ = closure Λ_C₂` and `Δ₂ = D₀`.
  obtain ⟨F₂, Δ₂, hF₂_O, hF₂_sub, hF₂_norm, hΔ₂_disc, hbd_Δ₂, hΔ₂_sub_cl_C₂, hD₀_sub_Δ₂⟩ :=
    theorem_7_7_proof hS hConn (by omega) hMetric hz hcl_C₂_disc hD₀_disc
      (hΔ₀_eq_D₀_diff ▸ hΔ₀_atoms z hz (by omega))
      (by rwa [hbd_cl_C₂, hdiff_C₂])
      (fun x hx hx_sub => (hZone.dist_le x hx (hx_sub.trans (hcl_C₂_sub.trans
        subset_closure))).trans (by omega))
      (fun x hx hle => hΔ₀_eq_D₀_diff ▸ hΔ₀_atoms x hx (by omega))
      hC₂ hC₂H hbd_cl_C₂ hC hCs hbd_D₀ hdisj_C₂_C hSeg hLoc hArr hComp
  refine ⟨C₂, Λ_C₂, F₂, Δ₂, hC₂H, hC₂, hOpen_C₂, hcl_C₂_sub, hcl_C₂_disc,
    hbd_cl_C₂, hdiff_C₂, by omega, hF₂_O, hF₂_sub, hF₂_norm, hΔ₂_disc, hbd_Δ₂,
    hΔ₂_sub_cl_C₂, hD₀_sub_Δ₂, fun x hx hlt => ?_⟩
  exact subset_diff_subBd_of_subset_open hOD₀.1
    ((hΔ₀_eq_D₀_diff.trans_subset sdiff_subset).trans hD₀_sub_Δ₂) (hΔ₀_atoms x hx hlt)

/-- **Graph Minors XIV, (9.6)** (pages 47–49):
"Let $H$ be a 2-cell, rigid drawing in $\Sigma$, let $z \in A(H)$, and let $\mathscr{T}$ be a
respectful tangle in $H$ of order $\theta$, with metric $d$. Let $\pi \ge 0$ with $\pi \ne 1, 3$,
let $\beta \ge 2\pi + 8$ be even, and let $\theta \ge 16\beta + 17$. Let $H$ be a subgraph of $G$,
let $J$ be the union of some bridges of $H$ in $G$ such that $d(z, v) < \beta$ for each ... $v \in
V(H
\cap J)$, and let $G'$ be the union of $H$ and all the other bridges of $H$ in $G$. Let
$\mathscr{S}$ be a $\mathscr{T}$-local 3-segregation of $G'$, and let $\alpha$ be an arrangement of
$\mathscr{S}$ in $\Sigma$ compatible with $H$. Then there is a $(3\beta + 3)$-zone $\Lambda$ around
$z$, and a closed disc $\Delta \subseteq \Sigma$ with $bd(\Delta)$ $\alpha$-normal and with
$\Lambda \subseteq \Delta$, with the following properties:
(i) $d(z, x) \le 3\beta + 6$ for all $x \in A(H)$ with $x \cap \Delta \ne \emptyset$
(ii) $x \subseteq \Delta - bd(\Delta)$ for all $x \in A(H)$ with $d(z, x) < \beta$
(iii) $H \cap \overline{\Sigma - \Delta}$ has a circuit, and $H \cap (\Sigma - \Lambda)$ is a rigid
drawing in $\Sigma$
(iv) one of the following alternatives holds:
(a) there is a crooked transaction $\mathscr{P}$ of cardinality $\ge \pi$ in $(G, \Omega_0)$ (where
$\Omega_0$ is a natural order of $V(H) \cap bd(\Lambda)$ from $bd(\Lambda)$), such that
$V(\mathscr{P})$ is free with respect to the tangle of order $\theta - 4(3\beta + 3) - 2$ obtained
from $\mathscr{T}$ by clearing $\Lambda$, and each $P \in \mathscr{P}$ meets $H \cap (\Sigma -
\Lambda)$ in precisely the ends of $P$
(b) there is no crooked transaction of cardinality $\ge \pi$ in $(\alpha^{-1}(\Delta) \cup J,
\alpha^{-1}(bd(\Delta)))$." -/
theorem theorem_9_6_proof [T2Space S] {α : Type u} {β : Type v}
    (G_amb G G' J : Graph α β) (B_J B_rem : Set (Graph α β))
    (H : Drawing S) (η : SpanEmbedding H G_amb) (η' : SpanEmbedding H G')
    (θ π beta : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ)
    (z : Set S)
    (S_seg : Set (Society α β)) (α_disc : Society α β → Set S) (α_pt : α → S)
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    (hV_fin : V(G_amb).Finite) (hE_fin : E(G_amb).Finite)
    (hRig : IsRigid H) (hMetric : HasTangleMetric H θ T d) (hz : z ∈ H.A)
    (hπ1 : π ≠ 1) (hπ3 : π ≠ 3) (hbeta : 2 * π + 8 ≤ beta) (heven : Even beta)
    (hθ : 16 * beta + 17 ≤ θ)
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
    (hLoc : IsTangleLocal G' H η' T S_seg)
    (hArr : IsSurfaceArrangement S_seg α_disc α_pt)
    (hComp : IsCompatibleWith G' H η' S_seg α_disc α_pt) :
    ∃ (Λ Δ : Set S)
      (T₁ : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d₁ : Set S → Set S → ℕ)
      (clearedEmbedding : SpanEmbedding (clearedSubdrawing H Λ) G_amb)
      (clearedSociety localSociety : Society α β),
      IsLambdaZoneAround H d (3 * beta + 3) z Λ ∧
      IsClearedTangle H T d θ (3 * beta + 3) Λ T₁ d₁ ∧
      IsClosedDisc Δ ∧
      IsArrangementNormal S_seg α_disc α_pt (subBd Δ) ∧
      Λ ⊆ Δ ∧
      (∀ x ∈ H.A, (x ∩ Δ).Nonempty → d z x ≤ 3 * beta + 6) ∧
      (∀ x ∈ H.A, d z x < beta → x ⊆ Δ \ subBd Δ) ∧
      (∃ C : Drawing S, C.IsCircuit ∧ C.IsSubdrawing (H.interSet (closure (univ \ Δ)))) ∧
      IsRigid (clearedSubdrawing H Λ) ∧
      (∀ v ∈ (clearedSubdrawing H Λ).V, clearedEmbedding.vMap v = η.vMap v) ∧
      (∀ e ∈ (clearedSubdrawing H Λ).E, clearedEmbedding.eMap e = η.eMap e) ∧
      clearedSociety.G = G ∧
      clearedSociety.Ω.bar = clearedEmbedding.vMap '' ((clearedSubdrawing H Λ).V ∩ subBd Λ) ∧
      (∃ inv_v : α → S,
        (∀ x ∈ clearedSociety.Ω.bar, inv_v x ∈ (clearedSubdrawing H Λ).V ∩ subBd Λ
          ∧ clearedEmbedding.vMap (inv_v x) = x)
          ∧
        IsNaturalOrderFrom inv_v clearedSociety.Ω (subBd Λ)) ∧
      localSociety.G = subgraphUnion G_amb J (arrangementPullbackGraph G' S_seg α_disc α_pt Δ) ∧
      IsPullbackPerm S_seg α_pt (subBd Δ) localSociety.Ω ∧
      ((∃ (P_set : Set (Graph α β)) (X : Set S),
          clearedSociety.IsCrookedTransaction P_set ∧
          π ≤ P_set.ncard ∧
          (∀ P ∈ P_set, ∀ a b : α,
            clearedSociety.IsOmegaPathWithEnds P a b →
            IsHPathWithEnds G_amb clearedEmbedding.imageGraph P a b) ∧
          X ⊆ (clearedSubdrawing H Λ).V ∩ subBd Λ ∧
          clearedSociety.transactionEnds P_set = clearedEmbedding.vMap '' X ∧
          IsFreeSet (clearedSubdrawing H Λ).toHypergraph T₁ (θ - 4 * (3 * beta + 3) - 2) X) ∨
       (∀ P_set : Set (Graph α β), localSociety.IsCrookedTransaction P_set → ¬ π ≤ P_set.ncard))
         := by
  have : ConnectedSpace S := hConn
  -- Step 1: By (9.5) (`theorem_9_5_proof`), obtain a battlefield `(Λ, C, X_bf)` around `z` of size
  -- `beta`.
  obtain ⟨Λ, C, X_bf0, hBf0⟩ :=
    theorem_9_5_proof H θ beta T d z hS hConn hRig hMetric hz (by omega) heven hθ
  obtain ⟨X_bf, _, hBf⟩ := hBf0.normalize
  have hZone : IsLambdaZoneAround H d (3 * beta + 3) z Λ := hBf.isZone
  have hRig_Λ : IsRigid (clearedSubdrawing H Λ) := hBf.isRigid_cleared
  obtain ⟨hX_bf_sub, _, T₁, d₁, hCleared, hFree_X_bf⟩ := hBf.isFree_X
  obtain ⟨Δ₀, _, hΔ₀_sub_Λ, _, hΔ₀_atoms⟩ := hBf.openDisc_includes
  -- Step 2: By (9.4) (`theorem_9_4_proof`), obtain `F`, `Δ`, `C_out` with `closure Λ ⊆ Δ`.
  have hΛ_le3 : ∀ x ∈ H.A, d z x ≤ 3 → x ⊆ Λ :=
    fun x hx hle => (hΔ₀_atoms x hx (by omega)).trans hΔ₀_sub_Λ
  obtain ⟨F, Δ, C_out, hFO, hFnorm, hΔ_disc, hbdΔ, hclΛ_sub_Δ, hCout_cir, hCout_sub, _, hΔ_dist⟩ :=
    theorem_9_4_proof hS hConn hMetric hz (by omega : 1 ≤ 3 * beta + 3)
      (by omega : 3 * beta + 3 + 7 ≤ θ)
      hZone hΛ_le3 hSeg hLoc hArr hComp
  have hNorm_Δ : IsArrangementNormal S_seg α_disc α_pt (subBd Δ) := hbdΔ ▸ hFnorm
  have hΛ_sub_Δ : Λ ⊆ Δ := subset_closure.trans hclΛ_sub_Δ
  have hΔ_lt_beta : ∀ x ∈ H.A, d z x < beta → x ⊆ Δ \ subBd Δ :=
    fun x hx hlt => subset_diff_subBd_of_subset_open hZone.isOpenDisc.1 hΛ_sub_Δ
      ((hΔ₀_atoms x hx hlt).trans hΔ₀_sub_Λ)
  -- Step 3: Construct `clearedEmbedding`, `clearedSociety`, and `localSociety`.
  let clearedEmbedding : SpanEmbedding (clearedSubdrawing H Λ) G_amb := restrictCleared η Λ
  obtain ⟨Ω_Λ, inv_v, hΩ_Λ_bar, hinv_v_prop, hΩ_Λ_nat⟩ :=
    exists_natural_order_spanEmbedding_subBd clearedEmbedding hZone.isOArc_bd
  have hJ_le : J ≤ G_amb := by
    rw [hJ_eq]
    exact subgraphSUnion_le fun B hB => (hB_J B hB).2.1
  have hBrem_le : subgraphSUnion G_amb B_rem ≤ G_amb :=
    subgraphSUnion_le fun B hB => (hB_rem B hB).2.1
  have hG'_le : G' ≤ G_amb := by
    rw [hG'_eq]
    refine subgraphSUnion_le ?_
    rintro K (rfl | rfl)
    · exact η.imageGraph_le
    · exact hBrem_le
  have hη_le_G' : η.imageGraph ≤ G' := by
    rw [hG'_eq]
    refine le_subgraphSUnion ?_ (Or.inl rfl)
    rintro K (rfl | rfl)
    · exact η.imageGraph_le
    · exact hBrem_le
  have hG_le : G ≤ G_amb := by
    rw [hG_eq]
    exact subgraphUnion_le hG'_le hJ_le
  have hG'_le_G : G' ≤ G := by
    rw [hG_eq]
    exact le_subgraphUnion_left hG'_le hJ_le
  have hΩ_Λ_sub_G : Ω_Λ.bar ⊆ V(G) := by
    rw [hΩ_Λ_bar]
    rintro x ⟨v, hv, rfl⟩
    have hv_img : clearedEmbedding.vMap v ∈ V(clearedEmbedding.imageGraph)
      := clearedEmbedding.bijOn_v.mapsTo hv.1
    have h_le : clearedEmbedding.imageGraph ≤ G :=
      ((restrictCleared_imageGraph_le η Λ).trans hη_le_G').trans hG'_le_G
    exact h_le.vertexSet_mono hv_img
  let clearedSociety : Society α β :=
    ⟨G, Ω_Λ, hV_fin.subset hG_le.vertexSet_mono, hE_fin.subset hG_le.edgeSet_mono, hΩ_Λ_sub_G⟩
  obtain ⟨Ω_star, hPull_star⟩ := exists_pullbackPerm hSeg.1 hArr (hbdΔ ▸ hFO)
  let G_star : Graph α β := subgraphUnion G_amb J (arrangementPullbackGraph G' S_seg α_disc α_pt Δ)
  have hPull_le_G_amb : arrangementPullbackGraph G' S_seg α_disc α_pt Δ ≤ G_amb :=
    (Graph.restrict_le.trans (G'.induce_le inter_subset_right)).trans hG'_le
  have hG_star_le : G_star ≤ G_amb := subgraphUnion_le hJ_le hPull_le_G_amb
  have hΩ_star_sub : Ω_star.bar ⊆ V(G_star) :=
    pullback_bar_subset_subgraphUnion hG'_le hJ_le hSeg.1
      hΔ_disc.isCompact.isClosed hPull_star
  let localSociety : Society α β :=
    ⟨G_star, Ω_star, hV_fin.subset hG_star_le.vertexSet_mono,
      hE_fin.subset hG_star_le.edgeSet_mono, hΩ_star_sub⟩
  refine ⟨Λ, Δ, T₁, d₁, clearedEmbedding, clearedSociety, localSociety,
    hZone, hCleared, hΔ_disc, hNorm_Δ, hΛ_sub_Δ, hΔ_dist, hΔ_lt_beta,
    ⟨C_out, hCout_cir, hCout_sub⟩, hRig_Λ,
    fun _ _ => rfl, fun _ _ => rfl, rfl, hΩ_Λ_bar, ⟨inv_v, hinv_v_prop, hΩ_Λ_nat⟩,
    rfl, hPull_star, ?_⟩
  -- Step 4: Verify alternative (iv)(a) or (iv)(b).
  by_cases h_no_cr : ∀ P_set : Set (Graph α β), localSociety.IsCrookedTransaction P_set → ¬ π
    ≤ P_set.ncard
  · exact Or.inr h_no_cr
  · left
    push Not at h_no_cr
    obtain ⟨P_star, hCr_star, hCard_star⟩ := h_no_cr
    by_cases hπ0 : π = 0
    · subst hπ0
      refine ⟨∅, ∅, empty_isCrookedTransaction clearedSociety, Nat.zero_le _,
        fun _ h => False.elim h, empty_subset _, ?_,
        hFree_X_bf.subset hCleared.hasMetric.1.2.1 (empty_subset X_bf)⟩
      rw [transactionEnds_empty, image_empty]
    · obtain ⟨C₂, Λ_C₂, F₂, Δ₂, hC₂H, hC₂, hOpen_C₂, hcl_C₂_sub, hcl_C₂_disc,
          hbd_cl_C₂, hdiff_C₂, hdist_C₂, _, _, hF₂_norm, hΔ₂_disc, hbd_Δ₂,
          hΔ₂_sub_cl_C₂, hD₀_sub_Δ₂, hΔ₂_atoms⟩ :=
        exists_nested_discs_9_6 hS hConn hMetric hBf hSeg hLoc hArr hComp
      obtain ⟨P_set, hCr_Λ, hCard_Λ, hEnds_sub, hHPath⟩ :=
        cylinder_reroute_9_6 hS hConn hV_fin hE_fin hRig hπ1 hπ3 hbeta
          hB_J hB_rem hDisj_B hJ_eq hG'_eq hG_eq hη'_v hη'_e hJ_dist hSeg hArr hComp
          hBf hΔ_disc hNorm_Δ hclΛ_sub_Δ hCout_cir hCout_sub
          (fun _ _ => rfl) (fun _ _ => rfl) (rfl : clearedSociety.G = G) hΩ_Λ_bar hinv_v_prop
            hΩ_Λ_nat
          (rfl : localSociety.G = _) hPull_star ⟨P_star, hCr_star, hCard_star⟩
          hC₂H hC₂ hOpen_C₂ hcl_C₂_sub hcl_C₂_disc hbd_cl_C₂ hdiff_C₂ hdist_C₂
          hF₂_norm hΔ₂_disc hbd_Δ₂ hΔ₂_sub_cl_C₂ hD₀_sub_Δ₂ hΔ₂_atoms
      let X : Set S := {v ∈ X_bf | clearedEmbedding.vMap v ∈ clearedSociety.transactionEnds P_set}
      have hX_sub_bf : X ⊆ X_bf := fun _ hv => hv.1
      have hX_sub_cleared : X ⊆ (clearedSubdrawing H Λ).V ∩ subBd Λ := by
        intro v hv
        have hv_bf := hX_bf_sub (hX_sub_bf hv)
        exact ⟨mem_clearedSubdrawing_V_of_mem_subBd hZone.isOpenDisc.1 hv_bf.1 hv_bf.2, hv_bf.2⟩
      have hEnds_eq : clearedSociety.transactionEnds P_set = clearedEmbedding.vMap '' X := by
        ext y
        simp only [X, mem_image, mem_sep_iff]
        constructor
        · intro hy
          obtain ⟨v, hv_bf, rfl⟩ := hEnds_sub hy
          exact ⟨v, ⟨hv_bf, hy⟩, rfl⟩
        · rintro ⟨v, ⟨_, hy⟩, rfl⟩
          exact hy
      have hFree_X : IsFreeSet (clearedSubdrawing H Λ).toHypergraph T₁ (θ - 4 *
        (3 * beta + 3) - 2) X :=
        hFree_X_bf.subset hCleared.hasMetric.1.2.1 hX_sub_bf
      exact ⟨P_set, X, hCr_Λ, hCard_Λ, hHPath, hX_sub_cleared, hEnds_eq, hFree_X⟩

end GraphMinor.GM14
