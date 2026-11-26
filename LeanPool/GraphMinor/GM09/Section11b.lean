/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Defs
public import LeanPool.GraphMinor.GM09.Section11a
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM09.Section2d
import LeanPool.GraphMinor.GM09.Section3a

/-!
# Graph Minors IX, Section 11 (Part 2): Prominences, Lawns, the Wall, and Parks ((11.1)–(11.5))

This file formalizes (11.1), (11.2), (11.3), (11.4), and (11.5) from Section 11 of
N. Robertson and P. D. Seymour, *Graph Minors. IX. Disjoint crossed paths*,
J. Combin. Theory Ser. B **49** (1990) 40–77 (pages 67–70).
-/

@[expose] public section

namespace GraphMinor.GM09

open Set Topology Graph GraphMinor.Surface GraphMinor.GM06

universe u v w

variable {α : Type u} {β : Type v}

/-! ## Basic topological and drawing lemmas -/

theorem isClosed_subBd {S : Type w} [TopologicalSpace S] (X : Set S) :
    IsClosed (subBd X) :=
  isClosed_closure.inter isClosed_closure

theorem subBd_subset_of_isClosed {S : Type w} [TopologicalSpace S] {X : Set S}
    (hX : IsClosed X) : subBd X ⊆ X := by
  intro x hx
  rw [← hX.closure_eq]
  exact hx.1

theorem disjoint_interior_subBd {S : Type w} [TopologicalSpace S] (X : Set S) :
    Disjoint (interior X) (subBd X) := by
  rw [disjoint_left]
  intro x hx_int hx_bd
  have hx_compl : x ∈ (interior X)ᶜ := by
    rw [← closure_compl, compl_eq_univ_sdiff]
    exact hx_bd.2
  exact hx_compl hx_int

theorem isCompact_of_isClosedDisc {S : Type w} [TopologicalSpace S] {Δ : Set S}
    (hΔ : IsClosedDisc Δ) : IsCompact Δ := by
  obtain ⟨e⟩ := hΔ
  have h1 : CompactSpace ClosedUnitDisc :=
    isCompact_iff_compactSpace.mp
      (Metric.isCompact_of_isClosed_isBounded Metric.isClosed_closedBall
        Metric.isBounded_closedBall)
  have h2 : CompactSpace Δ := e.compactSpace
  exact isCompact_iff_compactSpace.mpr h2

theorem isClosed_of_isClosedDisc {S : Type w} [TopologicalSpace S] [T2Space S] {Δ : Set S}
    (hΔ : IsClosedDisc Δ) : IsClosed Δ :=
  (isCompact_of_isClosedDisc hΔ).isClosed

theorem IsSimpleGraph.mono {G H : Graph α β} (hG : IsSimpleGraph G) (hHG : H ≤ G) :
    IsSimpleGraph H :=
  ⟨fun e he v hl => hG.1 e (hHG.edgeSet_mono he) v (hl.mono hHG),
   fun e₁ he₁ e₂ he₂ u v hl₁ hl₂ =>
     hG.2 e₁ (hHG.edgeSet_mono he₁) e₂ (hHG.edgeSet_mono he₂) u v (hl₁.mono hHG) (hl₂.mono hHG)⟩

theorem IsSimpleGraph.ne_of_isLink {G : Graph α β} (hG : IsSimpleGraph G)
    {e : β} {u v : α} (hl : G.IsLink e u v) : u ≠ v := by
  rintro rfl
  exact hG.1 e hl.edge_mem u hl

theorem graphDrawingVertexSet_eq_singleton {S : Type w} [TopologicalSpace S]
    {G : Graph α β} (Γ : GraphDrawing G S) {v : α} (hv : v ∈ V(G)) :
    graphDrawingVertexSet Γ v = {(Γ.iso.vertexEquiv ⟨v, hv⟩).1} := by
  ext x
  simp [graphDrawingVertexSet, hv, eq_comm]

theorem graphDrawingVertexSet_nonempty {S : Type w} [TopologicalSpace S]
    {G : Graph α β} (Γ : GraphDrawing G S) {v : α} (hv : v ∈ V(G)) :
    (graphDrawingVertexSet Γ v).Nonempty := by
  rw [graphDrawingVertexSet_eq_singleton Γ hv]
  exact singleton_nonempty _

theorem graphDrawingVertexSet_inj {S : Type w} [TopologicalSpace S]
    {G : Graph α β} (Γ : GraphDrawing G S) {u v : α} {x : S}
    (hu : x ∈ graphDrawingVertexSet Γ u) (hv : x ∈ graphDrawingVertexSet Γ v) :
    u = v := by
  rcases hu with ⟨huG, rfl⟩
  rcases hv with ⟨hvG, hveq⟩
  have hsub : Γ.iso.vertexEquiv ⟨v, hvG⟩ = Γ.iso.vertexEquiv ⟨u, huG⟩ :=
    Subtype.ext hveq
  exact congrArg Subtype.val (Γ.iso.vertexEquiv.injective hsub).symm

theorem graphDrawingEdgeSet_eq {S : Type w} [TopologicalSpace S]
    {G : Graph α β} (Γ : GraphDrawing G S) {e : β} (he : e ∈ E(G)) :
    graphDrawingEdgeSet Γ e = (Γ.iso.edgeEquiv ⟨e, he⟩).1 := by
  ext x
  simp [graphDrawingEdgeSet, he]

theorem graphDrawingEdgeSet_nonempty {S : Type w} [TopologicalSpace S]
    {G : Graph α β} (Γ : GraphDrawing G S) {e : β} (he : e ∈ E(G)) :
    (graphDrawingEdgeSet Γ e).Nonempty := by
  rw [graphDrawingEdgeSet_eq Γ he]
  have hmem : (Γ.iso.edgeEquiv ⟨e, he⟩).1 ∈ Γ.drawing.E := (Γ.iso.edgeEquiv ⟨e, he⟩).2
  rcases hmem with ⟨hnonempty, _, _⟩
  exact hnonempty

theorem graphDrawingVertexSet_subset_closure_edge {S : Type w} [TopologicalSpace S]
    {G : Graph α β} (Γ : GraphDrawing G S) {e : β} {u v : α} (hl : G.IsLink e u v) :
    graphDrawingVertexSet Γ u ⊆ closure (graphDrawingEdgeSet Γ e) := by
  have hu : u ∈ V(G) := hl.left_mem
  have hv : v ∈ V(G) := hl.right_mem
  have he : e ∈ E(G) := hl.edge_mem
  rw [graphDrawingVertexSet_eq_singleton Γ hu, graphDrawingEdgeSet_eq Γ he, singleton_subset_iff]
  have hlink := (Γ.iso.isLink_iff ⟨e, he⟩ ⟨u, hu⟩ ⟨v, hv⟩).mp hl
  have hmem : (Γ.iso.vertexEquiv ⟨u, hu⟩).1 ∈
      ({(Γ.iso.vertexEquiv ⟨u, hu⟩).1, (Γ.iso.vertexEquiv ⟨v, hv⟩).1} : Set S) :=
    mem_insert _ _
  rw [← hlink.2.2.2] at hmem
  exact hmem.1

theorem graphDrawingVertexSet_subset_subgraphU_of_mem {S : Type w} [TopologicalSpace S]
    {G P : Graph α β} (Γ : GraphDrawing G S) {v : α} (hv : v ∈ V(P)) :
    graphDrawingVertexSet Γ v ⊆ graphDrawingSubgraphU Γ P :=
  (subset_biUnion_of_mem (u := fun u => graphDrawingVertexSet Γ u) hv).trans subset_union_left

theorem graphDrawingEdgeSet_subset_subgraphU_of_mem {S : Type w} [TopologicalSpace S]
    {G P : Graph α β} (Γ : GraphDrawing G S) {e : β} (he : e ∈ E(P)) :
    graphDrawingEdgeSet Γ e ⊆ graphDrawingSubgraphU Γ P :=
  subset_closure.trans
    ((subset_biUnion_of_mem (u := fun f => closure (graphDrawingEdgeSet Γ f)) he).trans
      subset_union_right)

theorem mem_vertexSet_of_graphDrawingVertexSet_subset_subgraphU {S : Type w} [TopologicalSpace S]
    {G P : Graph α β} (Γ : GraphDrawing G S) (hPG : P ≤ G) {v : α} (hv : v ∈ V(G))
    (hsub : graphDrawingVertexSet Γ v ⊆ graphDrawingSubgraphU Γ P) :
    v ∈ V(P) := by
  let x := (Γ.iso.vertexEquiv ⟨v, hv⟩).1
  have hx_v : x ∈ graphDrawingVertexSet Γ v := ⟨hv, rfl⟩
  have hx_V : x ∈ Γ.drawing.V := (Γ.iso.vertexEquiv ⟨v, hv⟩).2
  rcases hsub hx_v with hx_vert | hx_edge
  · obtain ⟨u, huP, hxu⟩ := mem_iUnion₂.mp hx_vert
    exact (graphDrawingVertexSet_inj Γ hx_v hxu) ▸ huP
  · obtain ⟨e, heP, hxe⟩ := mem_iUnion₂.mp hx_edge
    obtain ⟨a, b, habP⟩ := P.exists_isLink_of_mem_edgeSet heP
    have habG : G.IsLink e a b := habP.mono hPG
    have haG : a ∈ V(G) := habG.left_mem
    have hbG : b ∈ V(G) := habG.right_mem
    have heG : e ∈ E(G) := habG.edge_mem
    rw [graphDrawingEdgeSet_eq Γ heG] at hxe
    have hlink := (Γ.iso.isLink_iff ⟨e, heG⟩ ⟨a, haG⟩ ⟨b, hbG⟩).mp habG
    have hx_inter : x ∈ closure (Γ.iso.edgeEquiv ⟨e, heG⟩).1 ∩ Γ.drawing.V := ⟨hxe, hx_V⟩
    rw [hlink.2.2.2] at hx_inter
    rcases hx_inter with hx_a | hx_b
    · have hva : v = a := graphDrawingVertexSet_inj Γ hx_v ⟨haG, hx_a.symm⟩
      exact hva ▸ habP.left_mem
    · have hvb : v = b := graphDrawingVertexSet_inj Γ hx_v ⟨hbG, Set.mem_singleton_iff.mp hx_b ▸
      rfl⟩
      exact hvb ▸ habP.right_mem

/-! ## Regular presentations and parks (Section 11, pages 67–68) -/

/-- Plane-topological properties of a presentation `P_pres = (Σ, Γ, Δ, Δ₀)` of a simple rural
neighborhood `(G, Ω, Ω₀)` used in Section 11 (pages 67–68):
- `(11.1)`: the intersection of two distinct lawns consists of images of common ends of the two
  corresponding prominences;
- existence of path discs `Δ(P)` and containing lawns for paths `P` of length `≤ 2` with distinct
  ends in `ΩBar₀` and no internal vertex in `ΩBar₀`;
- `wallDisc P_pres` is a closed disc;
- every edge of `G` is internal, external, or a wall edge;
- every prominence `P` with lawn `L` is drawn in `wall P_pres` with `L ∩ wall P_pres ⊆ Γ(P)`, and
  `wall P_pres` is contained in `bd(Δ₀)` together with the images of all prominences;
- any internal edge incident with the middle vertex of a prominence `P₁` is drawn in its lawn `L₁`.
-/
structure IsRegularPresentation {N : Neighborhood α β} (P_pres : Presentation N) : Prop where
  /-- (11.1): every element of `L ∩ L'` for distinct lawns `L, L'` is the image under `Γ` of a
  common end of the two corresponding prominences. -/
  lawn_inter_subset_common_ends :
    ∀ ⦃P P' : Graph α β⦄ ⦃L L' : Set EuclideanPlane⦄,
      IsProminenceWithDisc P_pres P L →
      IsProminenceWithDisc P_pres P' L' →
      L ≠ L' →
      ∀ ⦃x : EuclideanPlane⦄, x ∈ L ∩ L' →
        ∃ v ∈ pathEnds N.G P ∩ pathEnds N.G P', x ∈ graphDrawingVertexSet P_pres.Γ v
  /-- Every path `P` of `G` with distinct ends in `ΩBar₀`, no internal vertex in `ΩBar₀`, and at
  most
  two edges has a path disc `Δ(P)` contained in some lawn `L`. -/
  exists_lawn_of_short_path :
    ∀ ⦃P : Graph α β⦄ ⦃a b : α⦄,
      IsGraphPathWithEnds N.G P a b →
      a ≠ b → a ∈ N.Ω₀.bar → b ∈ N.Ω₀.bar →
      Disjoint (V(P) \ {a, b}) N.Ω₀.bar →
      E(P).ncard ≤ 2 →
      ∃ D L : Set EuclideanPlane, IsPathDisc P_pres P D ∧ IsLawn P_pres L ∧ D ⊆ L
  /-- The union `wallDisc P_pres` of `Δ₀` with all lawns is a closed disc. -/
  isClosedDisc_wallDisc : IsClosedDisc (wallDisc P_pres)
  /-- Every edge of `G` is internal, external, or a wall edge. -/
  edge_trichotomy :
    ∀ e ∈ E(N.G), IsInternalEdge P_pres e ∨ IsExternalEdge P_pres e ∨ IsWallEdge P_pres e
  /-- Every prominence `P` with lawn `L` is drawn in the wall, and `L ∩ wall` is contained in the
  drawing of `P`. -/
  prominence_U_subset_wall :
    ∀ ⦃P : Graph α β⦄ ⦃L : Set EuclideanPlane⦄,
      IsProminenceWithDisc P_pres P L →
      graphDrawingSubgraphU P_pres.Γ P ⊆ wall P_pres ∧
        L ∩ wall P_pres ⊆ graphDrawingSubgraphU P_pres.Γ P
  /-- Every point of the wall lies either in `bd(Δ₀)` or in the drawing of some prominence. -/
  wall_subset :
    wall P_pres ⊆ subBd P_pres.Δ₀ ∪
      ⋃ (P : Graph α β) (_ : IsProminence P_pres P), graphDrawingSubgraphU P_pres.Γ P
  /-- Any internal edge incident with an internal (middle) vertex of a prominence `P₁` is drawn in
  its lawn `L₁`. -/
  internal_edge_subset_lawn_of_middle :
    ∀ ⦃P₁ : Graph α β⦄ ⦃L₁ : Set EuclideanPlane⦄ ⦃v₁ : α⦄ ⦃e : β⦄,
      IsProminenceWithDisc P_pres P₁ L₁ →
      v₁ ∈ pathInternalVerts N.G P₁ →
      IsInternalEdge P_pres e →
      N.G.Inc e v₁ →
      graphDrawingEdgeSet P_pres.Γ e ⊆ L₁

/-- Plane-topological properties of a park `N_star = (G*, Ω*, Ω₀)` of `N` under `P_pres` used in
(11.4) (pages 68–69). -/
structure IsRegularParkOf {N : Neighborhood α β}
    (P_pres : Presentation N) (N_star : Neighborhood α β) : Prop where
  /-- `P_pres` is a regular presentation. -/
  isRegularPresentation : IsRegularPresentation P_pres
  /-- `N_star` is the park of `N` under `P_pres`. -/
  isParkOf : IsParkOf P_pres N_star
  /-- For any fence `(A*, B*)` of `Ω*`, there exist a fence `(A, B)` of `Ω₀` and `Z ⊆ ΩBar₀` with
  `|Z| ≤ 2` satisfying conditions (i)–(iii) on page 68. -/
  exists_fence_and_Z :
    ∀ ⦃A_star B_star : Set α⦄,
      N_star.Ω.IsFence A_star B_star →
      ∃ A B Z : Set α,
        N_star.Ω₀.IsFence A B ∧
        Z ⊆ N_star.Ω₀.bar ∧
        Z.ncard ≤ 2 ∧
        A_star ∩ N_star.Ω₀.bar ⊆ A ∧
        B_star ∩ N_star.Ω₀.bar ⊆ B ∧
        ∀ L : Set EuclideanPlane, IsLawn P_pres L →
          {v ∈ V(N_star.G) | graphDrawingVertexSet P_pres.Γ v ⊆ subBd L} ⊆ A ∪ A_star ∪ Z ∨
            {v ∈ V(N_star.G) | graphDrawingVertexSet P_pres.Γ v ⊆ subBd L} ⊆ B ∪ B_star ∪ Z
  /-- Any path `P'` of `G*` with distinct ends in `ΩBar₀ ∪ ΩBar*` and no internal vertex in `ΩBar₀ ∪
  ΩBar*`
  is drawn completely in some lawn `L`, so both of its ends are drawn in `bd(L)`. -/
  exists_lawn_of_park_path :
    ∀ ⦃P' : Graph α β⦄ ⦃x y : α⦄,
      IsGraphPathWithEnds N_star.G P' x y →
      x ≠ y →
      x ∈ N_star.Ω₀.bar ∪ N_star.Ω.bar →
      y ∈ N_star.Ω₀.bar ∪ N_star.Ω.bar →
      Disjoint (V(P') \ {x, y}) (N_star.Ω₀.bar ∪ N_star.Ω.bar) →
      ∃ L : Set EuclideanPlane, IsLawn P_pres L ∧
        graphDrawingVertexSet P_pres.Γ x ⊆ subBd L ∧
        graphDrawingVertexSet P_pres.Γ y ⊆ subBd L

/-- `N_star` is a regular park if it is the park of some rural neighborhood `N` under a regular
presentation `P_pres`. -/
def Neighborhood.IsRegularPark (N_star : Neighborhood α β) : Prop :=
  ∃ (N : Neighborhood α β) (P_pres : Presentation N), IsRegularParkOf P_pres N_star

/-! ## Helper lemmas on prominences, short paths, and triangles -/

theorem lawn_subset_wallDisc {N : Neighborhood α β} {P_pres : Presentation N}
    {L : Set EuclideanPlane} (hL : IsLawn P_pres L) :
    L ⊆ wallDisc P_pres :=
  (subset_biUnion_of_mem (u := fun X : Set EuclideanPlane => X) hL).trans subset_union_right

theorem wallDisc_subset_Δ {N : Neighborhood α β} (P_pres : Presentation N) :
    wallDisc P_pres ⊆ P_pres.Δ := by
  refine union_subset P_pres.Δ₀_subset_Δ (iUnion₂_subset ?_)
  rintro L ⟨P, hPL⟩
  exact hPL.1.2.2.1

theorem wall_subset_wallDisc {N : Neighborhood α β} {P_pres : Presentation N}
    (hreg : IsRegularPresentation P_pres) :
    wall P_pres ⊆ wallDisc P_pres :=
  subBd_subset_of_isClosed (isClosed_of_isClosedDisc hreg.isClosedDisc_wallDisc)

theorem not_isWallEdge_of_isExternalEdge {N : Neighborhood α β} {P_pres : Presentation N}
    (hreg : IsRegularPresentation P_pres) {e : β}
    (he_ext : IsExternalEdge P_pres e) (he_wall : IsWallEdge P_pres e) : False := by
  obtain ⟨x, hx⟩ := graphDrawingEdgeSet_nonempty P_pres.Γ he_ext.1
  exact (he_ext.2 hx).2 (wall_subset_wallDisc hreg (he_wall.2 hx))

theorem not_isInternalEdge_of_isExternalEdge {N : Neighborhood α β} {P_pres : Presentation N}
    {e : β} (he_int : IsInternalEdge P_pres e) (he_ext : IsExternalEdge P_pres e) : False := by
  obtain ⟨x, hx⟩ := graphDrawingEdgeSet_nonempty P_pres.Γ he_int.1
  exact (he_ext.2 hx).2 (interior_subset (he_int.2 hx))

theorem not_isInternalEdge_of_isWallEdge {N : Neighborhood α β} {P_pres : Presentation N}
    {e : β} (he_int : IsInternalEdge P_pres e) (he_wall : IsWallEdge P_pres e) : False := by
  obtain ⟨x, hx⟩ := graphDrawingEdgeSet_nonempty P_pres.Γ he_int.1
  exact disjoint_left.mp (disjoint_interior_subBd (wallDisc P_pres)) (he_int.2 hx) (he_wall.2 hx)

theorem short_path_U_subset_wallDisc {N : Neighborhood α β} {P_pres : Presentation N}
    (hreg : IsRegularPresentation P_pres) {P : Graph α β} {a b : α}
    (hP : IsGraphPathWithEnds N.G P a b) (hab : a ≠ b)
    (ha : a ∈ N.Ω₀.bar) (hb : b ∈ N.Ω₀.bar)
    (hdisj : Disjoint (V(P) \ {a, b}) N.Ω₀.bar) (hcard : E(P).ncard ≤ 2) :
    graphDrawingSubgraphU P_pres.Γ P ⊆ wallDisc P_pres := by
  obtain ⟨D, L, hD, hL, hDL⟩ := hreg.exists_lawn_of_short_path hP hab ha hb hdisj hcard
  exact hD.2.2.2.2.1.trans
    ((subBd_subset_of_isClosed (isClosed_of_isClosedDisc hD.2.1)).trans
      (hDL.trans (lawn_subset_wallDisc hL)))

theorem short_path_not_isExternalEdge {N : Neighborhood α β} {P_pres : Presentation N}
    (hreg : IsRegularPresentation P_pres) {P : Graph α β} {a b : α}
    (hP : IsGraphPathWithEnds N.G P a b) (hab : a ≠ b)
    (ha : a ∈ N.Ω₀.bar) (hb : b ∈ N.Ω₀.bar)
    (hdisj : Disjoint (V(P) \ {a, b}) N.Ω₀.bar) (hcard : E(P).ncard ≤ 2)
    {e : β} (heP : e ∈ E(P)) (he_ext : IsExternalEdge P_pres e) : False := by
  have hsub := (graphDrawingEdgeSet_subset_subgraphU_of_mem P_pres.Γ heP).trans
    (short_path_U_subset_wallDisc hreg hP hab ha hb hdisj hcard)
  obtain ⟨x, hx⟩ := graphDrawingEdgeSet_nonempty P_pres.Γ he_ext.1
  exact (he_ext.2 hx).2 (hsub hx)

theorem exists_prominence_middle_of_mem_wall_of_not_mem_bar₀
    {N : Neighborhood α β} {P_pres : Presentation N}
    (hreg : IsRegularPresentation P_pres) {v : α} (hv : v ∈ V(N.G))
    (hv_wall : graphDrawingVertexSet P_pres.Γ v ⊆ wall P_pres) (hv_not_bar₀ : v ∉ N.Ω₀.bar) :
    ∃ P₁ : Graph α β, IsProminence P_pres P₁ ∧ v ∈ pathInternalVerts N.G P₁ := by
  let x := (P_pres.Γ.iso.vertexEquiv ⟨v, hv⟩).1
  have hxv : x ∈ graphDrawingVertexSet P_pres.Γ v := ⟨hv, rfl⟩
  have hwall_sub := hreg.wall_subset (hv_wall hxv)
  rcases hwall_sub with hx_bd₀ | hx_prom
  · exfalso
    apply hv_not_bar₀
    rw [← P_pres.mem_bd_Δ₀_iff v hv, graphDrawingVertexSet_eq_singleton P_pres.Γ hv,
      singleton_subset_iff]
    exact hx_bd₀
  · obtain ⟨P₁, hP₁, hxP₁⟩ := mem_iUnion₂.mp hx_prom
    obtain ⟨L₁, hP₁L₁⟩ := hP₁
    obtain ⟨a, b, hP₁_path, _, ha_bar, hb_bar, _⟩ := hP₁L₁.1.1
    have hv_sub : graphDrawingVertexSet P_pres.Γ v ⊆ graphDrawingSubgraphU P_pres.Γ P₁ := by
      rw [graphDrawingVertexSet_eq_singleton P_pres.Γ hv, singleton_subset_iff]
      exact hxP₁
    have hvP₁ : v ∈ V(P₁) :=
      mem_vertexSet_of_graphDrawingVertexSet_subset_subgraphU P_pres.Γ hP₁_path.le hv hv_sub
    refine ⟨P₁, ⟨L₁, hP₁L₁⟩, ?_⟩
    rw [hP₁_path.pathInternalVerts_eq]
    refine ⟨hvP₁, ?_⟩
    rintro (rfl | rfl)
    · exact hv_not_bar₀ ha_bar
    · exact hv_not_bar₀ hb_bar

/-- If `v₁` is an internal vertex of a path `P₁` with `E(P₁).ncard ≤ 2`, then `P₁` has length 2
with middle vertex `v₁`, ends `a, b`, `V(P₁) = {a, v₁, b}`, and two edges joining `v₁` to `a` and
`b`. -/
theorem path_of_internal_of_ncard_le_two {G P₁ : Graph α β} {a b v₁ : α}
    (hP₁ : IsGraphPathWithEnds G P₁ a b) (hcard : E(P₁).ncard ≤ 2)
    (hv₁ : v₁ ∈ pathInternalVerts G P₁) :
    v₁ ≠ a ∧ v₁ ≠ b ∧ V(P₁) = {a, v₁, b} ∧
      ∃ e₁ ∈ E(P₁), ∃ e₂ ∈ E(P₁), P₁.IsLink e₁ a v₁ ∧ P₁.IsLink e₂ v₁ b := by
  classical
  rw [hP₁.pathInternalVerts_eq] at hv₁
  rcases hv₁ with ⟨hv₁P, hv₁_not_ab⟩
  have hv₁a : v₁ ≠ a := fun h => hv₁_not_ab (Or.inl h)
  have hv₁b : v₁ ≠ b := fun h => hv₁_not_ab (Or.inr h)
  rcases hP₁ with ⟨_, W, hW, hVP₁, hEP₁⟩
  cases W with
  | nil _ =>
    rw [hVP₁] at hv₁P
    simp only [GraphWalk.support_nil, mem_ofPred_eq, List.mem_singleton] at hv₁P
    exact (hv₁a hv₁P).elim
  | @cons _ w₁ _ e₁ hl₁ W₁ =>
    cases W₁ with
    | nil _ =>
      rw [hVP₁] at hv₁P
      simp only [GraphWalk.support_cons, GraphWalk.support_nil, mem_ofPred_eq,
        List.mem_cons, List.not_mem_nil, or_false] at hv₁P
      rcases hv₁P with rfl | rfl
      · exact (hv₁a rfl).elim
      · exact (hv₁b rfl).elim
    | @cons _ w₂ _ e₂ hl₂ W₂ =>
      cases W₂ with
      | nil _ =>
        have hv₁_eq : v₁ = w₁ := by
          rw [hVP₁] at hv₁P
          simp only [GraphWalk.support_cons, GraphWalk.support_nil, mem_ofPred_eq,
            List.mem_cons, List.not_mem_nil, or_false] at hv₁P
          rcases hv₁P with rfl | rfl | rfl
          · exact (hv₁a rfl).elim
          · rfl
          · exact (hv₁b rfl).elim
        subst hv₁_eq
        refine ⟨hv₁a, hv₁b, ?_, e₁, ?_, e₂, ?_, hl₁, hl₂⟩
        · rw [hVP₁]
          ext z
          simp [GraphWalk.support_cons, GraphWalk.support_nil]
        · rw [hEP₁]
          simp [GraphWalk.edges_cons]
        · rw [hEP₁]
          simp [GraphWalk.edges_cons]
      | @cons _ w₃ _ e₃ hl₃ W₃ =>
        exfalso
        have hnd_E : ([e₁, e₂, e₃] ++ W₃.edges).Nodup := hW.edges_nodup
        have hnd₃ : ([e₁, e₂, e₃] : List β).Nodup := (List.nodup_append.mp hnd_E).1
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
          not_false_eq_true, List.nodup_nil, and_true] at hnd₃
        rcases hnd₃ with ⟨⟨he₁₂, he₁₃⟩, he₂₃⟩
        have hsub : ({e₁, e₂, e₃} : Set β) ⊆ E(P₁) := by
          rw [hEP₁]
          rintro f (rfl | rfl | rfl) <;> simp [GraphWalk.edges_cons]
        have hfin : E(P₁).Finite := by
          rw [hEP₁]
          exact (GraphWalk.cons hl₁ (GraphWalk.cons hl₂ (GraphWalk.cons hl₃
            W₃))).edges.toFinset.finite_toSet.subset
            fun f hf => List.mem_toFinset.mpr hf
        have h3 : ({e₁, e₂, e₃} : Set β).ncard = 3 := by
          rw [ncard_insert_of_notMem, ncard_pair he₂₃]
          simp [he₁₂, he₁₃]
        have hle := ncard_le_ncard hsub hfin
        omega

/-- Construct the 2-edge path in `G` formed by two incident edges `e₁` (linking `a` and `v`) and
`e₂` (linking `v` and `b`) with `a, v, b` pairwise distinct. -/
theorem isGraphPathWithEnds_two_edges {G : Graph α β} {e₁ e₂ : β} {a v b : α}
    (hl₁ : G.IsLink e₁ a v) (hl₂ : G.IsLink e₂ v b)
    (hav : a ≠ v) (hvb : v ≠ b) (hab : a ≠ b) :
    IsGraphPathWithEnds G (subgraphUnion G (singleEdgeSubgraph G e₁) (singleEdgeSubgraph G e₂)) a b
      ∧
      V(subgraphUnion G (singleEdgeSubgraph G e₁) (singleEdgeSubgraph G e₂)) = {a, v, b} ∧
      V(subgraphUnion G (singleEdgeSubgraph G e₁) (singleEdgeSubgraph G e₂)) \ {a, b} = {v} ∧
      E(subgraphUnion G (singleEdgeSubgraph G e₁) (singleEdgeSubgraph G e₂)) = {e₁, e₂} ∧
      E(subgraphUnion G (singleEdgeSubgraph G e₁) (singleEdgeSubgraph G e₂)).ncard ≤ 2 := by
  have hP₁ : IsGraphPathWithEnds G (singleEdgeSubgraph G e₁) a v :=
    (isGraphPathWithEnds_singleEdgeSubgraph hav hl₁).mono (singleEdgeSubgraph_le G e₁)
  have hP₂ : IsGraphPathWithEnds G (singleEdgeSubgraph G e₂) v b :=
    (isGraphPathWithEnds_singleEdgeSubgraph hvb hl₂).mono (singleEdgeSubgraph_le G e₂)
  have hV₁ : V(singleEdgeSubgraph G e₁) = {a, v} := vertexSet_singleEdgeSubgraph_eq_pair hl₁
  have hV₂ : V(singleEdgeSubgraph G e₂) = {v, b} := vertexSet_singleEdgeSubgraph_eq_pair hl₂
  have hinter : V(singleEdgeSubgraph G e₁) ∩ V(singleEdgeSubgraph G e₂) = {v} := by
    rw [hV₁, hV₂]
    ext z
    simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨h₁, h₂⟩
      rcases h₁ with rfl | rfl
      · rcases h₂ with h | h
        · exact (hav h).elim
        · exact (hab h).elim
      · rfl
    · rintro rfl
      exact ⟨Or.inr rfl, Or.inl rfl⟩
  have hpath : IsGraphPathWithEnds G
      (subgraphUnion G (singleEdgeSubgraph G e₁) (singleEdgeSubgraph G e₂)) a b :=
    hP₁.subgraphUnion hP₂ hinter
  have hVP : V(subgraphUnion G (singleEdgeSubgraph G e₁) (singleEdgeSubgraph G e₂)) = {a, v, b}
    := by
    rw [vertexSet_subgraphUnion, hV₁, hV₂]
    ext z
    simp only [mem_union, mem_insert_iff, mem_singleton_iff]
    tauto
  have hVP_diff :
      V(subgraphUnion G (singleEdgeSubgraph G e₁) (singleEdgeSubgraph G e₂)) \ {a, b} = {v} := by
    rw [hVP]
    ext z
    simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨h₁, hnot⟩
      rcases h₁ with rfl | rfl | rfl
      · exact (hnot (Or.inl rfl)).elim
      · rfl
      · exact (hnot (Or.inr rfl)).elim
    · rintro rfl
      exact ⟨Or.inr (Or.inl rfl), by rintro (h | h); exacts [hav h.symm, hvb h]⟩
  have hEP : E(subgraphUnion G (singleEdgeSubgraph G e₁) (singleEdgeSubgraph G e₂)) = {e₁, e₂} := by
    rw [edgeSet_subgraphUnion (singleEdgeSubgraph_le G e₁) (singleEdgeSubgraph_le G e₂),
      edgeSet_singleEdgeSubgraph hl₁.edge_mem, edgeSet_singleEdgeSubgraph hl₂.edge_mem]
    ext f
    simp [or_comm]
  have hcard : E(subgraphUnion G (singleEdgeSubgraph G e₁) (singleEdgeSubgraph G e₂)).ncard ≤ 2
    := by
    rw [hEP]
    exact (ncard_insert_le e₁ {e₂}).trans (by simp)
  exact ⟨hpath, hVP, hVP_diff, hEP, hcard⟩

/-! ## Proof of (11.1) and (11.2) -/

/-- **Graph Minors IX, (11.1)** (page 67):
"If $L, L'$ are distinct lawns then every element of $L \cap L'$ is the image under $\Gamma$
of a common end of the two corresponding prominences." -/
theorem theorem_11_1_proof {N : Neighborhood α β} {P_pres : Presentation N}
    (hreg : IsRegularPresentation P_pres)
    {P P' : Graph α β} {L L' : Set EuclideanPlane}
    (hL : IsProminenceWithDisc P_pres P L)
    (hL' : IsProminenceWithDisc P_pres P' L')
    (hne : L ≠ L') {x : EuclideanPlane} (hx : x ∈ L ∩ L') :
    ∃ v ∈ pathEnds N.G P ∩ pathEnds N.G P', x ∈ graphDrawingVertexSet P_pres.Γ v :=
  hreg.lawn_inter_subset_common_ends hL hL' hne hx

/-- Helper for (11.2): if `e` is an external edge linking `v₁` and `v₂`, `v₁` is drawn in the wall,
and `v₁ ∉ ΩBar₀`, then `v₂ ∉ ΩBar₀`. -/
private theorem not_mem_bar₀_of_external_link_wall
    {N : Neighborhood α β} {P_pres : Presentation N}
    (hreg : IsRegularPresentation P_pres) (hsimple : IsSimpleGraph N.G)
    {e : β} {v₁ v₂ : α} (he : IsExternalEdge P_pres e) (hl : N.G.IsLink e v₁ v₂)
    (hv₁_wall : graphDrawingVertexSet P_pres.Γ v₁ ⊆ wall P_pres)
    (hv₁_not_bar₀ : v₁ ∉ N.Ω₀.bar) :
    v₂ ∉ N.Ω₀.bar := by
  have hv₁₂ : v₁ ≠ v₂ := hsimple.ne_of_isLink hl
  -- Choose a prominence `P₁` whose middle vertex is `v₁`.
  obtain ⟨P₁, ⟨L₁, hP₁L₁⟩, hv₁_mid⟩ :=
    exists_prominence_middle_of_mem_wall_of_not_mem_bar₀ hreg hl.left_mem hv₁_wall hv₁_not_bar₀
  obtain ⟨a, b, hP₁_path, _, ha_bar, _, _⟩ := hP₁L₁.1.1
  obtain ⟨hv₁a, _, _, e₁, he₁P₁, _, _, hl₁_P₁, _⟩ :=
    path_of_internal_of_ncard_le_two hP₁_path hP₁L₁.2.1 hv₁_mid
  have hl₁ : N.G.IsLink e₁ a v₁ := hl₁_P₁.mono hP₁_path.le
  -- Every edge of `P₁` is a wall edge, hence distinct from the external edge `e`.
  have hP₁_wall : ∀ f ∈ E(P₁), IsWallEdge P_pres f := fun f hf =>
    ⟨hP₁_path.le.edgeSet_mono hf,
     (graphDrawingEdgeSet_subset_subgraphU_of_mem P_pres.Γ hf).trans
       (hreg.prominence_U_subset_wall hP₁L₁).1⟩
  -- Since `N.G` is simple and `e` is not a wall edge, `v₂` is not an end of `P₁`.
  have hv₂a : v₂ ≠ a := by
    rintro rfl
    have he_eq : e = e₁ := hsimple.2 e he.1 e₁ hl₁.edge_mem v₁ v₂ hl hl₁.symm
    exact not_isWallEdge_of_isExternalEdge hreg he (he_eq ▸ hP₁_wall e₁ he₁P₁)
  -- Let `P'` be the 2-edge path formed by `e₁` and `e`.
  obtain ⟨hP'_path, _, hVP'_diff, hEP', hP'_card⟩ :=
    isGraphPathWithEnds_two_edges hl₁ hl hv₁a.symm hv₁₂ hv₂a.symm
  intro hv₂_bar₀
  have hdisj' : Disjoint (V(subgraphUnion N.G (singleEdgeSubgraph N.G e₁)
    (singleEdgeSubgraph N.G e)) \ {a, v₂})
      N.Ω₀.bar := by
    rw [hVP'_diff, disjoint_singleton_left]
    exact hv₁_not_bar₀
  have he_in_P' : e ∈ E(subgraphUnion N.G (singleEdgeSubgraph N.G e₁) (singleEdgeSubgraph N.G e))
    := by
    rw [hEP']
    exact mem_insert_of_mem _ (mem_singleton e)
  exact short_path_not_isExternalEdge hreg hP'_path hv₂a.symm ha_bar hv₂_bar₀ hdisj' hP'_card
    he_in_P' he

/-- **Graph Minors IX, (11.2)** (pages 67–68):
"If $e$ is an external edge of $G$ with both ends drawn in the wall, then its ends are both
middle vertices of prominences." -/
theorem theorem_11_2_proof {N : Neighborhood α β} {P_pres : Presentation N}
    (hreg : IsRegularPresentation P_pres) (hsimple : IsSimpleGraph N.G)
    {e : β} {u v : α} (he : IsExternalEdge P_pres e) (hl : N.G.IsLink e u v)
    (hu_wall : graphDrawingVertexSet P_pres.Γ u ⊆ wall P_pres)
    (hv_wall : graphDrawingVertexSet P_pres.Γ v ⊆ wall P_pres) :
    (∃ P₁ : Graph α β, IsProminence P_pres P₁ ∧ u ∈ pathInternalVerts N.G P₁) ∧
      (∃ P₂ : Graph α β, IsProminence P_pres P₂ ∧ v ∈ pathInternalVerts N.G P₂) := by
  have huv : u ≠ v := hsimple.ne_of_isLink hl
  -- Let `P` be the 1-edge path formed by `e`. Not both ends of `P` are in `ΩBar₀`.
  have hnot_both : ¬ (u ∈ N.Ω₀.bar ∧ v ∈ N.Ω₀.bar) := by
    rintro ⟨hu_bar, hv_bar⟩
    have hP : IsGraphPathWithEnds N.G (singleEdgeSubgraph N.G e) u v :=
      (isGraphPathWithEnds_singleEdgeSubgraph huv hl).mono (singleEdgeSubgraph_le N.G e)
    have hdisj : Disjoint (V(singleEdgeSubgraph N.G e) \ {u, v}) N.Ω₀.bar := by
      rw [vertexSet_singleEdgeSubgraph_eq_pair hl, sdiff_self]
      exact empty_disjoint _
    have hcard : E(singleEdgeSubgraph N.G e).ncard ≤ 2 := by
      rw [edgeSet_singleEdgeSubgraph he.1]
      simp
    have heP : e ∈ E(singleEdgeSubgraph N.G e) := by
      rw [edgeSet_singleEdgeSubgraph he.1]
      exact mem_singleton e
    exact short_path_not_isExternalEdge hreg hP huv hu_bar hv_bar hdisj hcard heP he
  have hu_not_bar₀ : u ∉ N.Ω₀.bar := by
    by_contra hu_bar
    have hv_not_bar₀ : v ∉ N.Ω₀.bar := fun hv_bar => hnot_both ⟨hu_bar, hv_bar⟩
    exact not_mem_bar₀_of_external_link_wall hreg hsimple he hl.symm hv_wall hv_not_bar₀ hu_bar
  have hv_not_bar₀ : v ∉ N.Ω₀.bar :=
    not_mem_bar₀_of_external_link_wall hreg hsimple he hl hu_wall hu_not_bar₀
  exact ⟨exists_prominence_middle_of_mem_wall_of_not_mem_bar₀ hreg hl.left_mem hu_wall hu_not_bar₀,
    exists_prominence_middle_of_mem_wall_of_not_mem_bar₀ hreg hl.right_mem hv_wall hv_not_bar₀⟩

/-! ## Triangles and Proof of (11.3) -/

/-- Every triangle `T` in `G` has 3 distinct vertices `{x₁, x₂, x₃}` and 3 distinct edges
`{f₁, f₂, f₃}` linking `(x₂, x₃)`, `(x₁, x₃)`, and `(x₁, x₂)` respectively. -/
theorem IsTriangle.exists_verts_and_edges {G T : Graph α β} (hT : IsTriangle G T) :
    ∃ x₁ x₂ x₃ : α, ∃ f₁ f₂ f₃ : β,
      x₁ ≠ x₂ ∧ x₂ ≠ x₃ ∧ x₁ ≠ x₃ ∧
      f₁ ≠ f₂ ∧ f₂ ≠ f₃ ∧ f₁ ≠ f₃ ∧
      V(T) = {x₁, x₂, x₃} ∧ E(T) = {f₁, f₂, f₃} ∧
      T.IsLink f₁ x₂ x₃ ∧ T.IsLink f₂ x₁ x₃ ∧ T.IsLink f₃ x₁ x₂ := by
  classical
  rcases hT with ⟨⟨_, x₁, W, hW_closed, hW_pos, hVT, hET⟩, hcard⟩
  have hfinE : E(T).Finite := by
    rw [hET]
    exact W.edges.toFinset.finite_toSet.subset fun e he => List.mem_toFinset.mpr he
  cases W with
  | nil _ =>
    simp [GraphWalk.length] at hW_pos
  | @cons _ x₂ _ f₃ hl₃ W₁ =>
    cases W₁ with
    | nil _ =>
      exfalso
      have hET_eq : E(T) = {f₃} := by
        rw [hET]; ext e; simp [GraphWalk.edges_cons, GraphWalk.edges_nil]
      rw [hET_eq, ncard_singleton] at hcard
      omega
    | @cons _ x₃ _ f₁ hl₁ W₂ =>
      cases W₂ with
      | nil _ =>
        exfalso
        have hET_eq : E(T) = {f₃, f₁} := by
          rw [hET]; ext e; simp [GraphWalk.edges_cons, GraphWalk.edges_nil]
        have hle : E(T).ncard ≤ 2 := by
          rw [hET_eq]
          exact (ncard_insert_le f₃ {f₁}).trans (by simp)
        omega
      | @cons _ x₄ _ f₂ hl₂ W₃ =>
        cases W₃ with
        | nil _ =>
          have hnd_V : ([x₂, x₃, x₁] : List α).Nodup := hW_closed.1
          simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
            not_false_eq_true, List.nodup_nil, and_true] at hnd_V
          rcases hnd_V with ⟨⟨hx₂₃, hx₂₁⟩, hx₃₁⟩
          have hnd_E : ([f₃, f₁, f₂] : List β).Nodup := hW_closed.2
          simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
            not_false_eq_true, List.nodup_nil, and_true] at hnd_E
          rcases hnd_E with ⟨⟨hf₃₁, hf₃₂⟩, hf₁₂⟩
          have hET_eq : E(T) = {f₁, f₂, f₃} := by
            rw [hET]; ext e
            simp only [GraphWalk.edges_cons, GraphWalk.edges_nil, mem_ofPred_eq,
              List.mem_cons, List.not_mem_nil, or_false, mem_insert_iff, mem_singleton_iff]
            tauto
          refine ⟨x₁, x₂, x₃, f₁, f₂, f₃, Ne.symm hx₂₁, hx₂₃, Ne.symm hx₃₁,
            hf₁₂, Ne.symm hf₃₂, Ne.symm hf₃₁, ?_, hET_eq, hl₁, hl₂.symm, hl₃⟩
          rw [hVT]
          ext z
          simp only [GraphWalk.support_cons, GraphWalk.support_nil, mem_ofPred_eq,
            List.mem_cons, List.not_mem_nil, or_false, mem_insert_iff, mem_singleton_iff]
          tauto
        | @cons _ x₅ _ f₄ hl₄ W₄ =>
          exfalso
          have hnd_E : ([f₃, f₁, f₂, f₄] ++ W₄.edges).Nodup := hW_closed.2
          have hnd₄ : ([f₃, f₁, f₂, f₄] : List β).Nodup := (List.nodup_append.mp hnd_E).1
          simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
            not_false_eq_true, List.nodup_nil, and_true] at hnd₄
          rcases hnd₄ with ⟨⟨hf₃₁, hf₃₂, hf₃₄⟩, ⟨hf₁₂, hf₁₄⟩, hf₂₄⟩
          have hsub : ({f₃, f₁, f₂, f₄} : Set β) ⊆ E(T) := by
            rw [hET]
            rintro e (rfl | rfl | rfl | rfl) <;> simp [GraphWalk.edges_cons]
          have h4 : ({f₃, f₁, f₂, f₄} : Set β).ncard = 4 := by
            rw [ncard_insert_of_notMem, ncard_insert_of_notMem, ncard_pair hf₂₄]
            · simp [hf₁₂, hf₁₄]
            · simp [hf₃₁, hf₃₂, hf₃₄]
          have hle := ncard_le_ncard hsub hfinE
          omega

/-- Given a triangle `T` in `G` and two distinct edges `e₂, e₃ ∈ E(T)`, we can label the vertices
`v₁, v₂, v₃` and the third edge `e₁` of `T` so that `e₃` links `v₁, v₂`, `e₂` links `v₁, v₃`, and
`e₁` links `v₂, v₃`. -/
theorem IsTriangle.exists_verts_of_two_edges {G T : Graph α β} (hT : IsTriangle G T)
    {e₂ e₃ : β} (he₂ : e₂ ∈ E(T)) (he₃ : e₃ ∈ E(T)) (he₂₃ : e₂ ≠ e₃) :
    ∃ v₁ v₂ v₃ : α, ∃ e₁ : β,
      v₁ ≠ v₂ ∧ v₂ ≠ v₃ ∧ v₁ ≠ v₃ ∧
      e₁ ≠ e₂ ∧ e₂ ≠ e₃ ∧ e₁ ≠ e₃ ∧
      V(T) = {v₁, v₂, v₃} ∧ E(T) = {e₁, e₂, e₃} ∧
      T.IsLink e₁ v₂ v₃ ∧ T.IsLink e₂ v₁ v₃ ∧ T.IsLink e₃ v₁ v₂ := by
  obtain ⟨x₁, x₂, x₃, f₁, f₂, f₃, hx₁₂, hx₂₃, hx₁₃, hf₁₂, hf₂₃, hf₁₃, hVT, hET, hl₁, hl₂, hl₃⟩ :=
    hT.exists_verts_and_edges
  have he₂_mem : e₂ = f₁ ∨ e₂ = f₂ ∨ e₂ = f₃ := by
    rwa [hET, mem_insert_iff, mem_insert_iff, mem_singleton_iff] at he₂
  have he₃_mem : e₃ = f₁ ∨ e₃ = f₂ ∨ e₃ = f₃ := by
    rwa [hET, mem_insert_iff, mem_insert_iff, mem_singleton_iff] at he₃
  rcases he₂_mem with rfl | rfl | rfl <;> rcases he₃_mem with rfl | rfl | rfl
  · exact (he₂₃ rfl).elim
  · refine ⟨x₃, x₁, x₂, f₃, hx₁₃.symm, hx₁₂, hx₂₃.symm, hf₁₃.symm, hf₁₂, hf₂₃.symm,
      ?_, ?_, hl₃, hl₁.symm, hl₂.symm⟩
    · rw [hVT]; ext z; simp; tauto
    · rw [hET]; ext e; simp; tauto
  · refine ⟨x₂, x₁, x₃, f₂, hx₁₂.symm, hx₁₃, hx₂₃, hf₁₂.symm, hf₁₃, hf₂₃,
      ?_, ?_, hl₂, hl₁, hl₃.symm⟩
    · rw [hVT]; ext z; simp; tauto
    · rw [hET]; ext e; simp; tauto
  · refine ⟨x₃, x₂, x₁, f₃, hx₂₃.symm, hx₁₂.symm, hx₁₃.symm, hf₂₃.symm, hf₁₂.symm, hf₁₃.symm,
      ?_, ?_, hl₃.symm, hl₂.symm, hl₁.symm⟩
    · rw [hVT]; ext z; simp; tauto
    · rw [hET]; ext e; simp; tauto
  · exact (he₂₃ rfl).elim
  · refine ⟨x₁, x₂, x₃, f₁, hx₁₂, hx₂₃, hx₁₃, hf₁₂, hf₂₃, hf₁₃, hVT, hET, hl₁, hl₂, hl₃⟩
  · refine ⟨x₂, x₃, x₁, f₂, hx₂₃, hx₁₃.symm, hx₁₂.symm, hf₂₃, hf₁₃.symm, hf₁₂.symm,
      ?_, ?_, hl₂.symm, hl₃.symm, hl₁⟩
    · rw [hVT]; ext z; simp; tauto
    · rw [hET]; ext e; simp; tauto
  · refine ⟨x₁, x₃, x₂, f₁, hx₁₃, hx₂₃.symm, hx₁₂, hf₁₃, hf₂₃.symm, hf₁₂,
      ?_, ?_, hl₁.symm, hl₃, hl₂⟩
    · rw [hVT]; ext z; simp; tauto
    · rw [hET]; ext e; simp; tauto
  · exact (he₂₃ rfl).elim

/-- Any vertex `w` drawn in `closure (wallDisc P_pres)` and incident with an external edge is drawn
in the wall. -/
private theorem mem_wall_of_mem_closure_wallDisc_of_inc_external
    {N : Neighborhood α β} {P_pres : Presentation N} {w : α} {f : β}
    (hw_cl : graphDrawingVertexSet P_pres.Γ w ⊆ closure (wallDisc P_pres))
    (hf : IsExternalEdge P_pres f) (hinc : N.G.Inc f w) :
    graphDrawingVertexSet P_pres.Γ w ⊆ wall P_pres := by
  obtain ⟨u, hl⟩ := hinc
  have hw_ext : graphDrawingVertexSet P_pres.Γ w ⊆ closure (Set.univ \ wallDisc P_pres) :=
    (graphDrawingVertexSet_subset_closure_edge P_pres.Γ hl).trans
      (closure_mono (hf.2.trans fun _ hx => ⟨trivial, hx.2⟩))
  exact subset_inter hw_cl hw_ext

/-- Any vertex `w` incident with both an internal edge and an external edge is drawn in the wall. -/
private theorem mem_wall_of_inc_internal_of_inc_external
    {N : Neighborhood α β} {P_pres : Presentation N} {w : α} {interiorSeamEdge e_ext : β}
    (he_int : IsInternalEdge P_pres interiorSeamEdge) (hinc_int : N.G.Inc interiorSeamEdge w)
    (he_ext : IsExternalEdge P_pres e_ext) (hinc_ext : N.G.Inc e_ext w) :
    graphDrawingVertexSet P_pres.Γ w ⊆ wall P_pres := by
  obtain ⟨u, hl⟩ := hinc_int
  have hw_cl : graphDrawingVertexSet P_pres.Γ w ⊆ closure (wallDisc P_pres) :=
    (graphDrawingVertexSet_subset_closure_edge P_pres.Γ hl).trans
      (closure_mono (he_int.2.trans interior_subset))
  exact mem_wall_of_mem_closure_wallDisc_of_inc_external hw_cl he_ext hinc_ext

/-- If `u` is the middle vertex of a prominence `P₁` and `e₂` is an internal edge linking `u` to a
vertex `w ∈ V(P₁)` in a simple graph `N.G`, we get a contradiction. -/
private theorem false_of_prominence_middle_internal_link
    {N : Neighborhood α β} {P_pres : Presentation N}
    (hreg : IsRegularPresentation P_pres) (hsimple : IsSimpleGraph N.G)
    {P₁ : Graph α β} {L₁ : Set EuclideanPlane} (hP₁L₁ : IsProminenceWithDisc P_pres P₁ L₁)
    {u w : α} {e₂ : β} (hu_mid : u ∈ pathInternalVerts N.G P₁)
    (hl₂ : N.G.IsLink e₂ u w) (he₂ : IsInternalEdge P_pres e₂) (hwP₁ : w ∈ V(P₁)) : False := by
  obtain ⟨a, b, hP₁_path, _, _, _, _⟩ := hP₁L₁.1.1
  obtain ⟨_, _, hVP₁, f₁, hf₁P₁, f₂, hf₂P₁, hlf₁, hlf₂⟩ :=
    path_of_internal_of_ncard_le_two hP₁_path hP₁L₁.2.1 hu_mid
  have huw : u ≠ w := hsimple.ne_of_isLink hl₂
  rw [hVP₁, mem_insert_iff, mem_insert_iff, mem_singleton_iff] at hwP₁
  have hex_f : ∃ f ∈ E(P₁), N.G.IsLink f u w := by
    rcases hwP₁ with rfl | rfl | rfl
    · exact ⟨f₁, hf₁P₁, hlf₁.symm.mono hP₁_path.le⟩
    · exact (huw rfl).elim
    · exact ⟨f₂, hf₂P₁, hlf₂.mono hP₁_path.le⟩
  obtain ⟨f, hfP₁, hlf⟩ := hex_f
  have he₂_eq : e₂ = f := hsimple.2 e₂ he₂.1 f (hP₁_path.le.edgeSet_mono hfP₁) u w hl₂ hlf
  have hf_wall : IsWallEdge P_pres f :=
    ⟨hP₁_path.le.edgeSet_mono hfP₁,
     (graphDrawingEdgeSet_subset_subgraphU_of_mem P_pres.Γ hfP₁).trans
       (hreg.prominence_U_subset_wall hP₁L₁).1⟩
  exact not_isInternalEdge_of_isWallEdge he₂ (he₂_eq ▸ hf_wall)

/-- **Graph Minors IX, (11.3)** (page 68):
"No triangle in $G$ has an internal edge and an external edge." -/
theorem theorem_11_3_proof {N : Neighborhood α β} {P_pres : Presentation N}
    (hreg : IsRegularPresentation P_pres) (hsimple : IsSimpleGraph N.G)
    {T : Graph α β} (hT : IsTriangle N.G T)
    {e₂ e₃ : β} (he₂T : e₂ ∈ E(T)) (he₃T : e₃ ∈ E(T))
    (he₂ : IsInternalEdge P_pres e₂) (he₃ : IsExternalEdge P_pres e₃) : False := by
  have he₂₃ : e₂ ≠ e₃ := fun h => not_isInternalEdge_of_isExternalEdge he₂ (h ▸ he₃)
  obtain ⟨v₁, v₂, v₃, e₁, hv₁₂, hv₂₃, hv₁₃, _, _, _, _, _, hl₁T, hl₂T, hl₃T⟩ :=
    hT.exists_verts_of_two_edges he₂T he₃T he₂₃
  have hl₁ : N.G.IsLink e₁ v₂ v₃ := hl₁T.mono hT.1.1
  have hl₂ : N.G.IsLink e₂ v₁ v₃ := hl₂T.mono hT.1.1
  have hl₃ : N.G.IsLink e₃ v₁ v₂ := hl₃T.mono hT.1.1
  -- `v₁` is incident with both the internal edge `e₂` and the external edge `e₃`, so `v₁` is in the
  -- wall.
  have hv₁_wall : graphDrawingVertexSet P_pres.Γ v₁ ⊆ wall P_pres :=
    mem_wall_of_inc_internal_of_inc_external he₂ ⟨v₃, hl₂⟩ he₃ ⟨v₂, hl₃⟩
  by_cases hv₂_wall : graphDrawingVertexSet P_pres.Γ v₂ ⊆ wall P_pres
  · -- Case 1: Both ends `v₁, v₂` of `e₃` are drawn in the wall.
    obtain ⟨⟨P₁, ⟨L₁, hP₁L₁⟩, hv₁_mid⟩, ⟨P₂, ⟨L₂, hP₂L₂⟩, hv₂_mid⟩⟩ :=
      theorem_11_2_proof hreg hsimple he₃ hl₃ hv₁_wall hv₂_wall
    have he₂_L₁ : graphDrawingEdgeSet P_pres.Γ e₂ ⊆ L₁ :=
      hreg.internal_edge_subset_lawn_of_middle hP₁L₁ hv₁_mid he₂ ⟨v₃, hl₂⟩
    have hv₃_L₁ : graphDrawingVertexSet P_pres.Γ v₃ ⊆ L₁ :=
      (graphDrawingVertexSet_subset_closure_edge P_pres.Γ hl₂.symm).trans
        ((closure_mono he₂_L₁).trans (isClosed_of_isClosedDisc hP₁L₁.1.2.1).closure_eq.subset)
    have hv₃_P₁ : v₃ ∈ V(P₁) := by
      rcases hreg.edge_trichotomy e₁ hl₁.edge_mem with he₁_int | he₁_ext | he₁_wall
      · -- If `e₁` is internal, `v₃` is also drawn in `L₂`; since `L₁ ≠ L₂`, `v₃` is a common end.
        have he₁_L₂ : graphDrawingEdgeSet P_pres.Γ e₁ ⊆ L₂ :=
          hreg.internal_edge_subset_lawn_of_middle hP₂L₂ hv₂_mid he₁_int ⟨v₃, hl₁⟩
        have hv₃_L₂ : graphDrawingVertexSet P_pres.Γ v₃ ⊆ L₂ :=
          (graphDrawingVertexSet_subset_closure_edge P_pres.Γ hl₁.symm).trans
            ((closure_mono he₁_L₂).trans (isClosed_of_isClosedDisc hP₂L₂.1.2.1).closure_eq.subset)
        have hL₁₂ : L₁ ≠ L₂ := by
          intro hL_eq
          obtain ⟨a₂, b₂, hP₂_path, _, ha₂_bar, hb₂_bar, _⟩ := hP₂L₂.1.1
          obtain ⟨_, _, hVP₂, _, _, _, _, _, _⟩ :=
            path_of_internal_of_ncard_le_two hP₂_path hP₂L₂.2.1 hv₂_mid
          obtain ⟨a₁, b₁, hP₁_path, _, _, _, hdisj₁⟩ := hP₁L₁.1.1
          rw [hP₁_path.pathInternalVerts_eq] at hv₁_mid
          have hv₁_not_bar₀ : v₁ ∉ N.Ω₀.bar := disjoint_left.mp hdisj₁ hv₁_mid
          have hv₁_L₁ : graphDrawingVertexSet P_pres.Γ v₁ ⊆ L₁ :=
            (graphDrawingVertexSet_subset_closure_edge P_pres.Γ hl₂).trans
              ((closure_mono he₂_L₁).trans (isClosed_of_isClosedDisc hP₁L₁.1.2.1).closure_eq.subset)
          have hv₁_U₂ : graphDrawingVertexSet P_pres.Γ v₁ ⊆ graphDrawingSubgraphU P_pres.Γ P₂ :=
            (subset_inter (hL_eq ▸ hv₁_L₁) hv₁_wall).trans (hreg.prominence_U_subset_wall hP₂L₂).2
          have hv₁P₂ : v₁ ∈ V(P₂) :=
            mem_vertexSet_of_graphDrawingVertexSet_subset_subgraphU P_pres.Γ hP₂_path.le
              hl₂.left_mem hv₁_U₂
          rw [hVP₂, mem_insert_iff, mem_insert_iff, mem_singleton_iff] at hv₁P₂
          rcases hv₁P₂ with rfl | rfl | rfl
          · exact hv₁_not_bar₀ ha₂_bar
          · exact hv₁₂ rfl
          · exact hv₁_not_bar₀ hb₂_bar
        let x₃ := (P_pres.Γ.iso.vertexEquiv ⟨v₃, hl₂.right_mem⟩).1
        have hx₃ : x₃ ∈ graphDrawingVertexSet P_pres.Γ v₃ := ⟨hl₂.right_mem, rfl⟩
        obtain ⟨u, hu_ends, hx₃_u⟩ :=
          theorem_11_1_proof hreg hP₁L₁ hP₂L₂ hL₁₂ ⟨hv₃_L₁ hx₃, hv₃_L₂ hx₃⟩
        have hv₃_eq : v₃ = u := graphDrawingVertexSet_inj P_pres.Γ hx₃ hx₃_u
        obtain ⟨a₁, b₁, hP₁_path, _, _, _, _⟩ := hP₁L₁.1.1
        have hu_P₁ : u ∈ V(P₁) := by
          have hu_P₁' := hu_ends.1
          rw [hP₁_path.pathEnds_eq] at hu_P₁'
          rcases hu_P₁' with rfl | rfl
          · exact hP₁_path.left_mem
          · exact hP₁_path.right_mem
        exact hv₃_eq ▸ hu_P₁
      · -- If `e₁` is external, `v₃` is drawn in the wall, hence in `L₁ ∩ wall ⊆ Γ(P₁)`.
        have hv₃_wall : graphDrawingVertexSet P_pres.Γ v₃ ⊆ wall P_pres :=
          mem_wall_of_inc_internal_of_inc_external he₂ ⟨v₁, hl₂.symm⟩ he₁_ext ⟨v₂, hl₁.symm⟩
        obtain ⟨a₁, b₁, hP₁_path, _, _, _, _⟩ := hP₁L₁.1.1
        exact mem_vertexSet_of_graphDrawingVertexSet_subset_subgraphU P_pres.Γ hP₁_path.le
          hl₂.right_mem
          ((subset_inter hv₃_L₁ hv₃_wall).trans (hreg.prominence_U_subset_wall hP₁L₁).2)
      · -- If `e₁` is a wall edge, `v₃` is drawn in the wall, hence in `L₁ ∩ wall ⊆ Γ(P₁)`.
        have hv₃_wall : graphDrawingVertexSet P_pres.Γ v₃ ⊆ wall P_pres :=
          (graphDrawingVertexSet_subset_closure_edge P_pres.Γ hl₁.symm).trans
            ((closure_mono he₁_wall.2).trans (isClosed_subBd _).closure_eq.subset)
        obtain ⟨a₁, b₁, hP₁_path, _, _, _, _⟩ := hP₁L₁.1.1
        exact mem_vertexSet_of_graphDrawingVertexSet_subset_subgraphU P_pres.Γ hP₁_path.le
          hl₂.right_mem
          ((subset_inter hv₃_L₁ hv₃_wall).trans (hreg.prominence_U_subset_wall hP₁L₁).2)
    exact false_of_prominence_middle_internal_link hreg hsimple hP₁L₁ hv₁_mid hl₂ he₂ hv₃_P₁
  · -- Case 2: `v₂` is not drawn in the wall.
    -- Then `e₁` must also be external (otherwise `v₂` would lie in `closure wallDisc` and hence in
    -- `wall`).
    have he₁ : IsExternalEdge P_pres e₁ := by
      rcases hreg.edge_trichotomy e₁ hl₁.edge_mem with he₁_int | he₁_ext | he₁_wall
      · exfalso
        exact hv₂_wall
          (mem_wall_of_inc_internal_of_inc_external he₁_int ⟨v₃, hl₁⟩ he₃ ⟨v₁, hl₃.symm⟩)
      · exact he₁_ext
      · exfalso
        have hv₂_cl : graphDrawingVertexSet P_pres.Γ v₂ ⊆ closure (wallDisc P_pres) :=
          (graphDrawingVertexSet_subset_closure_edge P_pres.Γ hl₁).trans
            (closure_mono (he₁_wall.2.trans (wall_subset_wallDisc hreg)))
        exact hv₂_wall (mem_wall_of_mem_closure_wallDisc_of_inc_external hv₂_cl he₃ ⟨v₁, hl₃.symm⟩)
    -- Since `e₂` is internal and `e₁` is external, `v₃` is drawn in the wall.
    have hv₃_wall : graphDrawingVertexSet P_pres.Γ v₃ ⊆ wall P_pres :=
      mem_wall_of_inc_internal_of_inc_external he₂ ⟨v₁, hl₂.symm⟩ he₁ ⟨v₂, hl₁.symm⟩
    -- Also `v₂ ∉ ΩBar₀` since `v₂` is not drawn in the wall.
    have hv₂_not_bar₀ : v₂ ∉ N.Ω₀.bar := by
      intro hv₂_bar₀
      have hv₂_bd₀ : graphDrawingVertexSet P_pres.Γ v₂ ⊆ subBd P_pres.Δ₀ :=
        (P_pres.mem_bd_Δ₀_iff v₂ hl₃.right_mem).mpr hv₂_bar₀
      have hv₂_cl : graphDrawingVertexSet P_pres.Γ v₂ ⊆ closure (wallDisc P_pres) :=
        hv₂_bd₀.trans (inter_subset_left.trans (closure_mono subset_union_left))
      exact hv₂_wall (mem_wall_of_mem_closure_wallDisc_of_inc_external hv₂_cl he₃ ⟨v₁, hl₃.symm⟩)
    -- Consider the 2-edge path `T \ e₂` formed by `e₃` and `e₁`; not both `v₁, v₃` are in `ΩBar₀`.
    obtain ⟨hP_path, _, hVP_diff, hEP, hP_card⟩ :=
      isGraphPathWithEnds_two_edges hl₃ hl₁ hv₁₂ hv₂₃ hv₁₃
    have hnot_both : ¬ (v₁ ∈ N.Ω₀.bar ∧ v₃ ∈ N.Ω₀.bar) := by
      rintro ⟨hv₁_bar, hv₃_bar⟩
      have hdisj : Disjoint (V(subgraphUnion N.G (singleEdgeSubgraph N.G e₃)
        (singleEdgeSubgraph N.G e₁)) \ {v₁, v₃})
          N.Ω₀.bar := by
        rw [hVP_diff, disjoint_singleton_left]
        exact hv₂_not_bar₀
      have he₃_in : e₃ ∈ E(subgraphUnion N.G (singleEdgeSubgraph N.G e₃)
        (singleEdgeSubgraph N.G e₁)) := by
        rw [hEP]
        exact mem_insert e₃ {e₁}
      exact short_path_not_isExternalEdge hreg hP_path hv₁₃ hv₁_bar hv₃_bar hdisj hP_card he₃_in he₃
    by_cases hv₁_bar₀ : v₁ ∈ N.Ω₀.bar
    · -- `v₃ ∉ ΩBar₀`, so `v₃` is the middle vertex of a prominence `P₃`.
      have hv₃_not_bar₀ : v₃ ∉ N.Ω₀.bar := fun hv₃_bar₀ => hnot_both ⟨hv₁_bar₀, hv₃_bar₀⟩
      obtain ⟨P₃, ⟨L₃, hP₃L₃⟩, hv₃_mid⟩ :=
        exists_prominence_middle_of_mem_wall_of_not_mem_bar₀ hreg hl₂.right_mem hv₃_wall
          hv₃_not_bar₀
      have he₂_L₃ : graphDrawingEdgeSet P_pres.Γ e₂ ⊆ L₃ :=
        hreg.internal_edge_subset_lawn_of_middle hP₃L₃ hv₃_mid he₂ ⟨v₁, hl₂.symm⟩
      have hv₁_L₃ : graphDrawingVertexSet P_pres.Γ v₁ ⊆ L₃ :=
        (graphDrawingVertexSet_subset_closure_edge P_pres.Γ hl₂).trans
          ((closure_mono he₂_L₃).trans (isClosed_of_isClosedDisc hP₃L₃.1.2.1).closure_eq.subset)
      obtain ⟨a₃, b₃, hP₃_path, _, _, _, _⟩ := hP₃L₃.1.1
      have hv₁_P₃ : v₁ ∈ V(P₃) :=
        mem_vertexSet_of_graphDrawingVertexSet_subset_subgraphU P_pres.Γ hP₃_path.le hl₂.left_mem
          ((subset_inter hv₁_L₃ hv₁_wall).trans (hreg.prominence_U_subset_wall hP₃L₃).2)
      exact false_of_prominence_middle_internal_link hreg hsimple hP₃L₃ hv₃_mid hl₂.symm he₂ hv₁_P₃
    · -- `v₁ ∉ ΩBar₀`, so `v₁` is the middle vertex of a prominence `P₁`.
      obtain ⟨P₁, ⟨L₁, hP₁L₁⟩, hv₁_mid⟩ :=
        exists_prominence_middle_of_mem_wall_of_not_mem_bar₀ hreg hl₂.left_mem hv₁_wall hv₁_bar₀
      have he₂_L₁ : graphDrawingEdgeSet P_pres.Γ e₂ ⊆ L₁ :=
        hreg.internal_edge_subset_lawn_of_middle hP₁L₁ hv₁_mid he₂ ⟨v₃, hl₂⟩
      have hv₃_L₁ : graphDrawingVertexSet P_pres.Γ v₃ ⊆ L₁ :=
        (graphDrawingVertexSet_subset_closure_edge P_pres.Γ hl₂.symm).trans
          ((closure_mono he₂_L₁).trans (isClosed_of_isClosedDisc hP₁L₁.1.2.1).closure_eq.subset)
      obtain ⟨a₁, b₁, hP₁_path, _, _, _, _⟩ := hP₁L₁.1.1
      have hv₃_P₁ : v₃ ∈ V(P₁) :=
        mem_vertexSet_of_graphDrawingVertexSet_subset_subgraphU P_pres.Γ hP₁_path.le hl₂.right_mem
          ((subset_inter hv₃_L₁ hv₃_wall).trans (hreg.prominence_U_subset_wall hP₁L₁).2)
      exact false_of_prominence_middle_internal_link hreg hsimple hP₁L₁ hv₁_mid hl₂ he₂ hv₃_P₁

/-! ## Proof of (11.4) -/

/-- If `(G₁, G₂)` is a separation of `G` and `W` is a simple walk in `G` from `a` to `b` with no
internal vertex in `V(G₁) ∩ V(G₂)`, then `W` lies entirely in `G₁` or entirely in `G₂`. -/
private theorem walk_subset_or_subset_of_isGraphSeparation {G G₁ G₂ : Graph α β}
    (hsep : IsGraphSeparation G G₁ G₂) {a b : α} (W : GraphWalk G a b) (hW : W.IsSimple)
    (hint : ∀ z ∈ W.support, z ≠ a → z ≠ b → z ∉ V(G₁) ∩ V(G₂)) :
    ((∀ v ∈ W.support, v ∈ V(G₁)) ∧ (∀ e ∈ W.edges, e ∈ E(G₁))) ∨
      ((∀ v ∈ W.support, v ∈ V(G₂)) ∧ (∀ e ∈ W.edges, e ∈ E(G₂))) := by
  induction W with
  | @nil u hu =>
    have hu_union : u ∈ V(G₁) ∪ V(G₂) := by
      rw [hsep.2.2.1]
      exact hu
    rcases hu_union with hu₁ | hu₂
    · left
      exact ⟨by intro v hv; simp only [GraphWalk.support_nil, List.mem_singleton] at hv; exact hv ▸
        hu₁,
        by simp⟩
    · right
      exact ⟨by intro v hv; simp only [GraphWalk.support_nil, List.mem_singleton] at hv; exact hv ▸
        hu₂,
        by simp⟩
  | @cons u w b e hl W' ih =>
    cases W' with
    | nil _ =>
      have he_union : e ∈ E(G₁) ∪ E(G₂) := by
        rw [hsep.2.2.2.1]
        exact hl.edge_mem
      rcases he_union with he₁ | he₂
      · left
        have hl₁ : G₁.IsLink e u w := (hsep.1.isLink_iff he₁).mpr hl
        refine ⟨?_, ?_⟩
        · intro v hv
          simp only [GraphWalk.support_cons, GraphWalk.support_nil, List.mem_cons,
            List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl
          · exact hl₁.left_mem
          · exact hl₁.right_mem
        · intro f hf
          simp only [GraphWalk.edges_cons, GraphWalk.edges_nil, List.mem_singleton] at hf
          exact hf ▸ he₁
      · right
        have hl₂ : G₂.IsLink e u w := (hsep.2.1.isLink_iff he₂).mpr hl
        refine ⟨?_, ?_⟩
        · intro v hv
          simp only [GraphWalk.support_cons, GraphWalk.support_nil, List.mem_cons,
            List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl
          · exact hl₂.left_mem
          · exact hl₂.right_mem
        · intro f hf
          simp only [GraphWalk.edges_cons, GraphWalk.edges_nil, List.mem_singleton] at hf
          exact hf ▸ he₂
    | @cons _ u' _ e' hl' W'' =>
      have hnd : (u :: w :: W''.support).Nodup := hW
      obtain ⟨hu_not, hW'⟩ := List.nodup_cons.mp hnd
      obtain ⟨hw_not_W'', _⟩ := List.nodup_cons.mp hW'
      have hwu : w ≠ u := fun h => hu_not (h ▸ List.mem_cons_self)
      have hwb : w ≠ b := fun h => hw_not_W'' (h ▸ W''.end_mem_support)
      have hw_not_inter : w ∉ V(G₁) ∩ V(G₂) :=
        hint w (List.mem_cons_of_mem u List.mem_cons_self) hwu hwb
      have hint' : ∀ z ∈ (GraphWalk.cons hl' W'').support, z ≠ w → z ≠ b → z ∉ V(G₁) ∩ V(G₂) := by
        intro z hz hzw hzb
        exact hint z (List.mem_cons_of_mem u hz) (fun hzu => hu_not (hzu ▸ hz)) hzb
      rcases ih hW' hint' with ⟨hV₁, hE₁⟩ | ⟨hV₂, hE₂⟩
      · left
        have hw₁ : w ∈ V(G₁) := hV₁ w List.mem_cons_self
        have hw_not_₂ : w ∉ V(G₂) := fun hw₂ => hw_not_inter ⟨hw₁, hw₂⟩
        have he₁ : e ∈ E(G₁) := by
          have he_union : e ∈ E(G₁) ∪ E(G₂) := by rw [hsep.2.2.2.1]; exact hl.edge_mem
          rcases he_union with he₁ | he₂
          · exact he₁
          · exact (hw_not_₂ ((hsep.2.1.isLink_iff he₂).mpr hl).right_mem).elim
        have hu₁ : u ∈ V(G₁) := ((hsep.1.isLink_iff he₁).mpr hl).left_mem
        refine ⟨?_, ?_⟩
        · intro v hv
          rcases List.mem_cons.mp hv with rfl | hv'
          · exact hu₁
          · exact hV₁ v hv'
        · intro f hf
          rcases List.mem_cons.mp hf with rfl | hf'
          · exact he₁
          · exact hE₁ f hf'
      · right
        have hw₂ : w ∈ V(G₂) := hV₂ w List.mem_cons_self
        have hw_not_₁ : w ∉ V(G₁) := fun hw₁ => hw_not_inter ⟨hw₁, hw₂⟩
        have he₂ : e ∈ E(G₂) := by
          have he_union : e ∈ E(G₁) ∪ E(G₂) := by rw [hsep.2.2.2.1]; exact hl.edge_mem
          rcases he_union with he₁ | he₂
          · exact (hw_not_₁ ((hsep.1.isLink_iff he₁).mpr hl).right_mem).elim
          · exact he₂
        have hu₂ : u ∈ V(G₂) := ((hsep.2.1.isLink_iff he₂).mpr hl).left_mem
        refine ⟨?_, ?_⟩
        · intro v hv
          rcases List.mem_cons.mp hv with rfl | hv'
          · exact hu₂
          · exact hV₂ v hv'
        · intro f hf
          rcases List.mem_cons.mp hf with rfl | hf'
          · exact he₂
          · exact hE₂ f hf'

/-- If `(G₁, G₂)` is a separation of `G` and `P` is a path in `G` with ends `x, y` and no internal
vertex in `V(G₁) ∩ V(G₂)`, then `P ≤ G₁` or `P ≤ G₂`. -/
theorem le_or_le_of_isGraphPathWithEnds {G G₁ G₂ P : Graph α β}
    (hsep : IsGraphSeparation G G₁ G₂) {x y : α} (hP : IsGraphPathWithEnds G P x y)
    (hdisj : Disjoint (V(P) \ {x, y}) (V(G₁) ∩ V(G₂))) :
    P ≤ G₁ ∨ P ≤ G₂ := by
  rcases hP with ⟨hPG, W, hW, hVP, hEP⟩
  obtain ⟨W_G, hs, he⟩ := exists_walk_up_of_le hPG W
  have hW_G : W_G.IsSimple := by unfold GraphWalk.IsSimple; rw [hs]; exact hW
  have hint : ∀ z ∈ W_G.support, z ≠ x → z ≠ y → z ∉ V(G₁) ∩ V(G₂) := by
    intro z hz hzx hzy
    rw [hs] at hz
    have hzP : z ∈ V(P) \ {x, y} := by
      rw [hVP]
      exact ⟨hz, by simp [hzx, hzy]⟩
    exact disjoint_left.mp hdisj hzP
  rcases walk_subset_or_subset_of_isGraphSeparation hsep W_G hW_G hint with ⟨hV₁, hE₁⟩ | ⟨hV₂, hE₂⟩
  · left
    rw [(Compatible.of_le_le hPG hsep.1).le_iff, hVP, hEP]
    exact ⟨fun v hv => hV₁ v (hs.symm ▸ hv), fun f hf => hE₁ f (he.symm ▸ hf)⟩
  · right
    rw [(Compatible.of_le_le hPG hsep.2.1).le_iff, hVP, hEP]
    exact ⟨fun v hv => hV₂ v (hs.symm ▸ hv), fun f hf => hE₂ f (he.symm ▸ hf)⟩

/-- **Graph Minors IX, (11.4)** (pages 68–69):
"If $(G_0 \cup G^*, \Omega^*)$ is the composition of a park $(G^*, \Omega^*, \Omega_0)$ with
a society $(G_0, \Omega_0)$, and $(G_0, \Omega_0)$ has no transaction of cardinality $> p$,
then $(G_0 \cup G^*, \Omega^*)$ has no transaction of cardinality $> p + 2$." -/
theorem theorem_11_4_proof {S S₀ : Society α β} {N_star : Neighborhood α β} {p : ℕ}
    (hpark : N_star.IsRegularPark)
    (hcomp : S.IsComposition S₀ N_star)
    (hno : ∀ Q_set : Set (Graph α β), S₀.IsTransaction Q_set → Q_set.ncard ≤ p)
    {P_set : Set (Graph α β)} (hP_set : S.IsTransaction P_set) :
    P_set.ncard ≤ p + 2 := by
  obtain ⟨N, P_pres, hreg⟩ := hpark
  obtain ⟨⟨hsep, hbar_sub⟩, hΩ_eq, hΩ₀_eq, hbar₀_inter⟩ := hcomp
  obtain ⟨A_star, B_star, hdisj_P_set, hfence_star, hends_P_set⟩ := hP_set
  have hfence_star' : N_star.Ω.IsFence A_star B_star := hΩ_eq.symm ▸ hfence_star
  obtain ⟨A, B, Z, hfence₀, hZ_sub, hZ_card, hA_sub, hB_sub, hlawn⟩ :=
    hreg.exists_fence_and_Z hfence_star'
  have hfence_S₀ : S₀.Ω.IsFence A B := hΩ₀_eq ▸ hfence₀
  have hAB_disj : Disjoint (A ∪ A_star) (B ∪ B_star) := by
    rw [disjoint_union_left, disjoint_union_right, disjoint_union_right]
    refine ⟨⟨hfence₀.2.2.1, ?_⟩, ⟨?_, hfence_star.2.2.1⟩⟩
    · rw [disjoint_left]
      intro z hzA hzB_star
      exact disjoint_left.mp hfence₀.2.2.1 hzA (hB_sub ⟨hzB_star, hfence₀.1 hzA⟩)
    · rw [disjoint_left]
      intro z hzA_star hzB
      exact disjoint_left.mp hfence₀.2.2.1 (hA_sub ⟨hzA_star, hfence₀.2.1 hzB⟩) hzB
  -- Prove the paper's subpath claim: every path `P` of `S.G` from `A ∪ A*` to `B ∪ B*` avoiding `Z`
  -- contains a subpath `P' ≤ P` in `G₀` from `A` to `B`.
  have hclaim : ∀ P : Graph α β, ∀ u ∈ A ∪ A_star, ∀ v ∈ B ∪ B_star,
      IsGraphPathWithEnds S.G P u v → Disjoint V(P) Z →
      ∃ P' ≤ P, ∃ x ∈ A, ∃ y ∈ B, S₀.IsOmegaPathWithEnds P' x y := by
    intro P u hu v hv hP hPZ
    obtain ⟨x, hx, y, hy, P', hP'P, hP'_ft, hx_inter, hy_inter⟩ :=
      hP.exists_isFromToPathWithEnds hu hv
    have hxy : x ≠ y := fun h => disjoint_left.mp hAB_disj hx (h ▸ hy)
    have hP'Z : Disjoint V(P') Z := Disjoint.mono_left hP'P.vertexSet_mono hPZ
    -- No internal vertex of `P'` is in `A ∪ A* ∪ B ∪ B* = ΩBar₀ ∪ ΩBar*`.
    have hdisj_int_all : Disjoint (V(P') \ {x, y}) (N_star.Ω₀.bar ∪ N_star.Ω.bar) := by
      rw [disjoint_left]
      rintro z ⟨hzP', hzx⟩ (hz_bar₀ | hz_bar)
      · rw [← hfence₀.2.2.2.1] at hz_bar₀
        rcases hz_bar₀ with hzA | hzB
        · have hz_eq : z = x := by
            have hz_in : z ∈ V(P') ∩ (A ∪ A_star) := ⟨hzP', Or.inl hzA⟩
            rwa [hx_inter, mem_singleton_iff] at hz_in
          exact hzx (Or.inl hz_eq)
        · have hz_eq : z = y := by
            have hz_in : z ∈ V(P') ∩ (B ∪ B_star) := ⟨hzP', Or.inl hzB⟩
            rwa [hy_inter, mem_singleton_iff] at hz_in
          exact hzx (Or.inr hz_eq)
      · rw [← hfence_star'.2.2.2.1] at hz_bar
        rcases hz_bar with hzA_star | hzB_star
        · have hz_eq : z = x := by
            have hz_in : z ∈ V(P') ∩ (A ∪ A_star) := ⟨hzP', Or.inr hzA_star⟩
            rwa [hx_inter, mem_singleton_iff] at hz_in
          exact hzx (Or.inl hz_eq)
        · have hz_eq : z = y := by
            have hz_in : z ∈ V(P') ∩ (B ∪ B_star) := ⟨hzP', Or.inr hzB_star⟩
            rwa [hy_inter, mem_singleton_iff] at hz_in
          exact hzx (Or.inr hz_eq)
    have hdisj_int_inter : Disjoint (V(P') \ {x, y}) (V(S₀.G) ∩ V(N_star.G)) := by
      rw [← hbar₀_inter, ← hΩ₀_eq]
      exact hdisj_int_all.mono_right subset_union_left
    rcases le_or_le_of_isGraphPathWithEnds hsep hP'_ft hdisj_int_inter with hP'_G₀ | hP'_star
    · -- `P' ≤ S₀.G`: its ends `x, y` lie in `A` and `B`.
      have hx_G₀ : x ∈ V(S₀.G) := hP'_G₀.vertexSet_mono hP'_ft.left_mem
      have hy_G₀ : y ∈ V(S₀.G) := hP'_G₀.vertexSet_mono hP'_ft.right_mem
      have hx_A : x ∈ A := by
        rcases hx with hxA | hxA_star
        · exact hxA
        · apply hA_sub
          refine ⟨hxA_star, ?_⟩
          rw [hΩ₀_eq, hbar₀_inter]
          exact ⟨hx_G₀, hbar_sub (hfence_star.1 hxA_star)⟩
      have hy_B : y ∈ B := by
        rcases hy with hyB | hyB_star
        · exact hyB
        · apply hB_sub
          refine ⟨hyB_star, ?_⟩
          rw [hΩ₀_eq, hbar₀_inter]
          exact ⟨hy_G₀, hbar_sub (hfence_star.2.1 hyB_star)⟩
      exact ⟨P', hP'P, x, hx_A, y, hy_B, hP'_ft.of_le hP'_G₀, hxy,
        hfence_S₀.1 hx_A, hfence_S₀.2.1 hy_B⟩
    · -- `P' ≤ N_star.G`: `P'` is drawn in some lawn `L`, contradicting (iii).
      exfalso
      have hx_bars : x ∈ N_star.Ω₀.bar ∪ N_star.Ω.bar := by
        rcases hx with hxA | hxA_star
        · exact Or.inl (hfence₀.1 hxA)
        · exact Or.inr (hfence_star'.1 hxA_star)
      have hy_bars : y ∈ N_star.Ω₀.bar ∪ N_star.Ω.bar := by
        rcases hy with hyB | hyB_star
        · exact Or.inl (hfence₀.2.1 hyB)
        · exact Or.inr (hfence_star'.2.1 hyB_star)
      obtain ⟨L, hL, hx_bdL, hy_bdL⟩ :=
        hreg.exists_lawn_of_park_path (hP'_ft.of_le hP'_star) hxy hx_bars hy_bars hdisj_int_all
      have hx_Vstar : x ∈ V(N_star.G) := hP'_star.vertexSet_mono hP'_ft.left_mem
      have hy_Vstar : y ∈ V(N_star.G) := hP'_star.vertexSet_mono hP'_ft.right_mem
      have hx_not_Z : x ∉ Z := disjoint_left.mp hP'Z hP'_ft.left_mem
      have hy_not_Z : y ∉ Z := disjoint_left.mp hP'Z hP'_ft.right_mem
      rcases hlawn L hL with hL_A | hL_B
      · have hy_in : y ∈ A ∪ A_star ∪ Z := hL_A ⟨hy_Vstar, hy_bdL⟩
        rcases hy_in with hy_AA | hy_Z
        · exact disjoint_left.mp hAB_disj hy_AA hy
        · exact hy_not_Z hy_Z
      · have hx_in : x ∈ B ∪ B_star ∪ Z := hL_B ⟨hx_Vstar, hx_bdL⟩
        rcases hx_in with hx_BB | hx_Z
        · exact disjoint_left.mp hAB_disj hx hx_BB
        · exact hx_not_Z hx_Z
  -- Restrict `P_set` to `P_set₀ := {P ∈ P_set | Disjoint V(P) Z}`.
  let P_set₀ : Set (Graph α β) := {P ∈ P_set | Disjoint V(P) Z}
  let P_hit : Set (Graph α β) := {P ∈ P_set | ¬ Disjoint V(P) Z}
  have hZ_fin : Z.Finite := N_star.Ω₀.finite_bar.subset hZ_sub
  -- `P_hit.ncard ≤ Z.ncard ≤ 2` since members of `P_set` are pairwise vertex-disjoint.
  have hhit_le : P_hit.ncard ≤ Z.ncard := by
    rcases P_hit.eq_empty_or_nonempty with h_empty | ⟨P₀, hP₀⟩
    · rw [h_empty, ncard_empty]
      exact Nat.zero_le _
    · have hex_z : ∀ P : P_hit, ∃ z ∈ Z, z ∈ V(P.1) := by
        rintro ⟨P, _, hnot_disj⟩
        obtain ⟨z, hzP, hzZ⟩ := not_disjoint_iff.mp hnot_disj
        exact ⟨z, hzZ, hzP⟩
      choose z_of hz_Z hz_V using hex_z
      classical
      let g : Graph α β → α := fun P => if h : P ∈ P_hit then z_of ⟨P, h⟩ else z_of ⟨P₀, hP₀⟩
      have hmaps : MapsTo g P_hit Z := by
        intro P hP
        simp only [g, hP, ↓reduceDIte]
        exact hz_Z ⟨P, hP⟩
      have hinj : InjOn g P_hit := by
        intro P₁ hP₁ P₂ hP₂ heq
        simp only [g, hP₁, hP₂, ↓reduceDIte] at heq
        by_contra hne
        have hdisj₁₂ := hdisj_P_set.2 hP₁.1 hP₂.1 hne
        exact disjoint_left.mp hdisj₁₂ (hz_V ⟨P₁, hP₁⟩) (heq ▸ hz_V ⟨P₂, hP₂⟩)
      exact ncard_le_ncard_of_injOn g hmaps hinj hZ_fin
  -- For each `P ∈ P_set₀`, choose a subpath `P' ≤ P` in `G₀` from `A` to `B`.
  have hex_sub : ∀ P : P_set₀, ∃ P' ≤ P.1, ∃ x ∈ A, ∃ y ∈ B, S₀.IsOmegaPathWithEnds P' x y := by
    rintro ⟨P, hP_in, hPZ⟩
    obtain ⟨u, huA, v, hvB, hP_omega⟩ := hends_P_set P hP_in
    exact hclaim P u (Or.inr huA) v (Or.inr hvB) hP_omega.1 hPZ
  choose sub_of hsub_le x_of hx_A y_of hy_B hsub_omega using hex_sub
  classical
  let φ : Graph α β → Graph α β := fun P => if h : P ∈ P_set₀ then sub_of ⟨P, h⟩ else P
  let P_set' : Set (Graph α β) := φ '' P_set₀
  have hφ_inj : InjOn φ P_set₀ := by
    intro P₁ hP₁ P₂ hP₂ heq
    simp only [φ, hP₁, hP₂, ↓reduceDIte] at heq
    by_contra hne
    have hdisj₁₂ := hdisj_P_set.2 hP₁.1 hP₂.1 hne
    have hx₁ : x_of ⟨P₁, hP₁⟩ ∈ V(P₁) :=
      (hsub_le ⟨P₁, hP₁⟩).vertexSet_mono (hsub_omega ⟨P₁, hP₁⟩).1.left_mem
    have hx₂ : x_of ⟨P₁, hP₁⟩ ∈ V(P₂) := by
      have hmem : x_of ⟨P₁, hP₁⟩ ∈ V(sub_of ⟨P₂, hP₂⟩) :=
        heq ▸ (hsub_omega ⟨P₁, hP₁⟩).1.left_mem
      exact (hsub_le ⟨P₂, hP₂⟩).vertexSet_mono hmem
    exact disjoint_left.mp hdisj₁₂ hx₁ hx₂
  have hP_set'_trans : S₀.IsTransaction P_set' := by
    refine ⟨A, B, ⟨?_, ?_⟩, hfence_S₀, ?_⟩
    · rintro Q ⟨P, hP, rfl⟩
      simp only [φ, hP, ↓reduceDIte]
      exact ⟨x_of ⟨P, hP⟩, y_of ⟨P, hP⟩, hsub_omega ⟨P, hP⟩⟩
    · rintro Q₁ ⟨P₁, hP₁, rfl⟩ Q₂ ⟨P₂, hP₂, rfl⟩ hne
      have hP₁₂ : P₁ ≠ P₂ := fun h => hne (congrArg φ h)
      have hdisj₁₂ := hdisj_P_set.2 hP₁.1 hP₂.1 hP₁₂
      simp only [φ, hP₁, hP₂, ↓reduceDIte]
      exact Disjoint.mono (hsub_le ⟨P₁, hP₁⟩).vertexSet_mono (hsub_le ⟨P₂,
        hP₂⟩).vertexSet_mono hdisj₁₂
    · rintro Q ⟨P, hP, rfl⟩
      simp only [φ, hP, ↓reduceDIte]
      exact ⟨x_of ⟨P, hP⟩, hx_A ⟨P, hP⟩, y_of ⟨P, hP⟩, hy_B ⟨P, hP⟩, hsub_omega ⟨P, hP⟩⟩
  have hcard_P_set₀ : P_set₀.ncard ≤ p := by
    rw [← hφ_inj.ncard_image]
    exact hno P_set' hP_set'_trans
  have hP_union : P_set = P_set₀ ∪ P_hit := by
    ext P
    simp only [P_set₀, P_hit, mem_union, mem_sep_iff]
    exact ⟨fun h => by by_cases hd : Disjoint V(P) Z; exacts [Or.inl ⟨h, hd⟩, Or.inr ⟨h, hd⟩],
      by rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h⟩
  calc
    P_set.ncard = (P_set₀ ∪ P_hit).ncard := by rw [← hP_union]
    _ ≤ P_set₀.ncard + P_hit.ncard := ncard_union_le P_set₀ P_hit
    _ ≤ p + 2 := Nat.add_le_add hcard_P_set₀ (hhit_le.trans hZ_card)

/-! ## Outer park neighborhood and Proof of (11.5) -/

/-- The vertices of `N.G` drawn in the wall or in the complement in `Δ` of `wallDisc P_pres`
(Graph Minors IX, Section 11, page 69). -/
def outerParkVerts {N : Neighborhood α β} (P_pres : Presentation N) : Set α :=
  {v ∈ V(N.G) | graphDrawingVertexSet P_pres.Γ v ⊆ wall P_pres ∪ (P_pres.Δ \ wallDisc P_pres)}

/-- The wall edges and external edges of `N.G` with respect to `P_pres`
(Graph Minors IX, Section 11, page 69). -/
def outerParkEdges {N : Neighborhood α β} (P_pres : Presentation N) : Set β :=
  {e ∈ E(N.G) | IsWallEdge P_pres e ∨ IsExternalEdge P_pres e}

/-- The subgraph `G₂` of `N.G` consisting of `outerParkVerts P_pres` and `outerParkEdges P_pres`
(Graph Minors IX, Section 11, page 69). -/
def outerParkGraph {N : Neighborhood α β} (P_pres : Presentation N) : Graph α β :=
  (N.G.induce (outerParkVerts P_pres)).restrict (outerParkEdges P_pres)

@[simp]
theorem vertexSet_outerParkGraph {N : Neighborhood α β} (P_pres : Presentation N) :
    V(outerParkGraph P_pres) = outerParkVerts P_pres := rfl

theorem outerParkGraph_le {N : Neighborhood α β} (P_pres : Presentation N) :
    outerParkGraph P_pres ≤ N.G :=
  restrict_le.trans (N.G.induce_le fun _ hv => hv.1)

theorem mem_outerParkVerts_of_inc_outerParkEdges {N : Neighborhood α β} (P_pres : Presentation N)
    {e : β} (he : e ∈ outerParkEdges P_pres) {u : α} (hinc : N.G.Inc e u) :
    u ∈ outerParkVerts P_pres := by
  refine ⟨hinc.vertex_mem, ?_⟩
  obtain ⟨v, hl⟩ := hinc
  rcases he.2 with he_wall | he_ext
  · have hu_wall : graphDrawingVertexSet P_pres.Γ u ⊆ wall P_pres :=
      (graphDrawingVertexSet_subset_closure_edge P_pres.Γ hl).trans
        ((closure_mono he_wall.2).trans (isClosed_subBd _).closure_eq.subset)
    exact hu_wall.trans subset_union_left
  · intro x hx
    have hx_cl : x ∈ closure (P_pres.Δ \ wallDisc P_pres) :=
      (graphDrawingVertexSet_subset_closure_edge P_pres.Γ hl).trans (closure_mono he_ext.2) hx
    have hx_Δ : x ∈ P_pres.Δ := by
      have hcl_Δ : closure (P_pres.Δ \ wallDisc P_pres) ⊆ P_pres.Δ :=
        (closure_mono sdiff_subset).trans (isClosed_of_isClosedDisc
          P_pres.isClosedDisc_Δ).closure_eq.subset
      exact hcl_Δ hx_cl
    by_cases hx_wd : x ∈ wallDisc P_pres
    · left
      have hsub_compl : P_pres.Δ \ wallDisc P_pres ⊆ Set.univ \ wallDisc P_pres :=
        fun _ hy => ⟨trivial, hy.2⟩
      exact ⟨subset_closure hx_wd, closure_mono hsub_compl hx_cl⟩
    · right
      exact ⟨hx_Δ, hx_wd⟩

@[simp]
theorem edgeSet_outerParkGraph {N : Neighborhood α β} (P_pres : Presentation N) :
    E(outerParkGraph P_pres) = outerParkEdges P_pres := by
  unfold outerParkGraph
  rw [edgeSet_restrict, inter_eq_right]
  intro e he
  obtain ⟨u, v, hl⟩ := N.G.exists_isLink_of_mem_edgeSet he.1
  exact ⟨u, v, hl, mem_outerParkVerts_of_inc_outerParkEdges P_pres he ⟨v, hl⟩,
    mem_outerParkVerts_of_inc_outerParkEdges P_pres he ⟨u, hl.symm⟩⟩

theorem bar_subset_outerParkVerts {N : Neighborhood α β} (P_pres : Presentation N) :
    N.Ω.bar ⊆ outerParkVerts P_pres := by
  intro v hv_bar
  have hvG : v ∈ V(N.G) := N.bar_subset hv_bar
  refine ⟨hvG, ?_⟩
  have hv_bd : graphDrawingVertexSet P_pres.Γ v ⊆ subBd P_pres.Δ :=
    (P_pres.mem_bd_Δ_iff v hvG).mpr hv_bar
  intro x hx
  have hx_bd : x ∈ subBd P_pres.Δ := hv_bd hx
  have hx_Δ : x ∈ P_pres.Δ := subBd_subset_of_isClosed (isClosed_of_isClosedDisc
    P_pres.isClosedDisc_Δ) hx_bd
  by_cases hx_wd : x ∈ wallDisc P_pres
  · left
    have hcompl : Set.univ \ P_pres.Δ ⊆ Set.univ \ wallDisc P_pres :=
      sdiff_subset_sdiff_right (wallDisc_subset_Δ P_pres)
    exact ⟨subset_closure hx_wd, closure_mono hcompl hx_bd.2⟩
  · right
    exact ⟨hx_Δ, hx_wd⟩

/-- The outer neighborhood `(G₂, Ω, Ω*)` of `N` with respect to a park `N_star` under `P_pres`
(Graph Minors IX, Section 11, page 69). -/
def outerParkNeighborhood {N N_star : Neighborhood α β} (P_pres : Presentation N)
    (hpark : IsParkOf P_pres N_star) : Neighborhood α β where
  G := outerParkGraph P_pres
  Ω := N.Ω
  Ω₀ := N_star.Ω
  finite_V := N.finite_V.subset (outerParkGraph_le P_pres).vertexSet_mono
  finite_E := N.finite_E.subset (outerParkGraph_le P_pres).edgeSet_mono
  bar_subset := bar_subset_outerParkVerts P_pres
  bar₀_subset := by
    rw [vertexSet_outerParkGraph, hpark.2.2.2.2.2.1]
    intro v hv
    exact ⟨hv.1, hv.2.trans subset_union_left⟩

/-- Any short path (`≤ 2` edges) of `N.G` with distinct ends in `ΩBar₀` and no internal vertex in
`ΩBar₀` is a subgraph of the park `N_star.G`. -/
private theorem short_path_le_park {N N_star : Neighborhood α β} {P_pres : Presentation N}
    (hreg : IsRegularPresentation P_pres) (hpark : IsParkOf P_pres N_star)
    {P : Graph α β} {a b : α} (hP : IsGraphPathWithEnds N.G P a b)
    (hab : a ≠ b) (ha : a ∈ N.Ω₀.bar) (hb : b ∈ N.Ω₀.bar)
    (hdisj : Disjoint (V(P) \ {a, b}) N.Ω₀.bar) (hcard : E(P).ncard ≤ 2) :
    P ≤ N_star.G := by
  have hU_sub := short_path_U_subset_wallDisc hreg hP hab ha hb hdisj hcard
  rw [(Compatible.of_le_le hP.le hpark.2.2.2.2.1).le_iff, hpark.2.2.1, hpark.2.2.2.1]
  refine ⟨fun v hv => ⟨hP.le.vertexSet_mono hv, ?_⟩, fun e he => ⟨hP.le.edgeSet_mono he, ?_⟩⟩
  · exact (graphDrawingVertexSet_subset_subgraphU_of_mem P_pres.Γ hv).trans hU_sub
  · exact (graphDrawingEdgeSet_subset_subgraphU_of_mem P_pres.Γ he).trans hU_sub

private theorem triangle_in_park_or_exterior (S : Society α β) (hsimple : IsSimpleGraph S.G)
    {H₁ : Society α β} {H₂ : Neighborhood α β} (composition : S.IsComposition H₁ H₂)
    {P_pres : Presentation H₂} {N_star : Neighborhood α β}
    (hreg : IsRegularPresentation P_pres) (hpark : IsParkOf P_pres N_star)
    {G₁ : Graph α β} (hG₁_le_G : G₁ ≤ S.G) (hH₁_le_G₁ : H₁.G ≤ G₁)
    (hGstar_le_G₁ : N_star.G ≤ G₁) :
    let N₂ := outerParkNeighborhood P_pres hpark
    ∀ T : Graph α β, IsTriangle S.G T → T ≤ G₁ ∨ T ≤ N₂.G := by
  intro N₂
  obtain ⟨⟨hsep_H, _⟩, _, hΩ₀_H₂, hbar₀_inter⟩ := composition
  have hsimple_H₂ : IsSimpleGraph H₂.G := hsimple.mono hsep_H.2.1
  have hN₂_le_G : N₂.G ≤ S.G := (outerParkGraph_le P_pres).trans hsep_H.2.1
  intro T hT
  obtain ⟨v₁, v₂, v₃, e₁, e₂, e₃, hv₁₂, hv₂₃, hv₁₃, _, _, _, hVT, hET, hl₁T, hl₂T, hl₃T⟩ :=
    hT.exists_verts_and_edges
  -- Every vertex of `T` is incident with an edge of `T`.
  have hV_of_E : ∀ H : Graph α β, H ≤ S.G → E(T) ⊆ E(H) → T ≤ H := by
    intro H hHG hEH
    rw [(Compatible.of_le_le hT.1.1 hHG).le_iff]
    refine ⟨?_, hEH⟩
    rw [hVT]
    have hl₁H : H.IsLink e₁ v₂ v₃ := (hHG.isLink_iff (hEH (by rw [hET]; simp))).mpr
      (hl₁T.mono hT.1.1)
    have hl₂H : H.IsLink e₂ v₁ v₃ := (hHG.isLink_iff (hEH (by rw [hET]; simp))).mpr
      (hl₂T.mono hT.1.1)
    rintro v (rfl | rfl | rfl)
    · exact hl₂H.left_mem
    · exact hl₁H.left_mem
    · exact hl₁H.right_mem
  by_cases hT_H₂ : T ≤ H₂.G
  · -- Case 1: `T ≤ H₂.G`. By (11.3), `T` cannot have both an internal edge and an external edge.
    have hT_H₂' : IsTriangle H₂.G T := ⟨⟨hT_H₂, hT.1.2⟩, hT.2⟩
    by_cases hex_int : ∃ e ∈ E(T), IsInternalEdge P_pres e
    · left
      obtain ⟨interiorSeamEdge, he_int_T, he_int⟩ := hex_int
      apply hV_of_E G₁ hG₁_le_G
      intro e heT
      have heH₂ : e ∈ E(H₂.G) := hT_H₂.edgeSet_mono heT
      have he_Gstar : e ∈ E(N_star.G) := by
        rw [hpark.2.2.2.1]
        refine ⟨heH₂, ?_⟩
        rcases hreg.edge_trichotomy e heH₂ with h_int | h_ext | h_wall
        · exact h_int.2.trans interior_subset
        · exact (theorem_11_3_proof hreg hsimple_H₂ hT_H₂' he_int_T heT he_int h_ext).elim
        · exact h_wall.2.trans (wall_subset_wallDisc hreg)
      exact hGstar_le_G₁.edgeSet_mono he_Gstar
    · right
      push Not at hex_int
      apply hV_of_E N₂.G hN₂_le_G
      intro e heT
      have heH₂ : e ∈ E(H₂.G) := hT_H₂.edgeSet_mono heT
      change e ∈ E(outerParkGraph P_pres)
      rw [edgeSet_outerParkGraph]
      refine ⟨heH₂, ?_⟩
      rcases hreg.edge_trichotomy e heH₂ with h_int | h_ext | h_wall
      · exact (hex_int e heT h_int).elim
      · exact Or.inr h_ext
      · exact Or.inl h_wall
  · -- Case 2: `¬ (T ≤ H₂.G)`. Then some edge of `T` is in `E(H₁.G)`, and `T ≤ G₁`.
    left
    have hex_E₁ : ∃ e ∈ E(T), e ∈ E(H₁.G) := by
      by_contra! hnot_E₁
      apply hT_H₂
      apply hV_of_E H₂.G hsep_H.2.1
      intro e heT
      have he_union : e ∈ E(H₁.G) ∪ E(H₂.G) := by
        rw [hsep_H.2.2.2.1]
        exact hT.1.1.edgeSet_mono heT
      exact he_union.resolve_left (hnot_E₁ e heT)
    -- Helper: any single edge `f ∈ E(H₂.G)` with both ends in `V(H₁.G)` belongs to `E(N_star.G)`.
    have hsingle_in_Gstar : ∀ f u w, H₂.G.IsLink f u w → u ∈ V(H₁.G) → w ∈ V(H₁.G) →
        f ∈ E(N_star.G) := by
      intro f u w hlf hu₁ hw₁
      have huw : u ≠ w := hsimple_H₂.ne_of_isLink hlf
      have hu_bar₀ : u ∈ H₂.Ω₀.bar := by
        rw [hΩ₀_H₂, hbar₀_inter]; exact ⟨hu₁, hlf.left_mem⟩
      have hw_bar₀ : w ∈ H₂.Ω₀.bar := by
        rw [hΩ₀_H₂, hbar₀_inter]; exact ⟨hw₁, hlf.right_mem⟩
      have hP : IsGraphPathWithEnds H₂.G (singleEdgeSubgraph H₂.G f) u w :=
        (isGraphPathWithEnds_singleEdgeSubgraph huw hlf).mono (singleEdgeSubgraph_le H₂.G f)
      have hdisj : Disjoint (V(singleEdgeSubgraph H₂.G f) \ {u, w}) H₂.Ω₀.bar := by
        rw [vertexSet_singleEdgeSubgraph_eq_pair hlf, sdiff_self]
        exact empty_disjoint _
      have hcard : E(singleEdgeSubgraph H₂.G f).ncard ≤ 2 := by
        rw [edgeSet_singleEdgeSubgraph hlf.edge_mem]; simp
      have hle_Gstar := short_path_le_park hreg hpark hP huw hu_bar₀ hw_bar₀ hdisj hcard
      apply hle_Gstar.edgeSet_mono
      rw [edgeSet_singleEdgeSubgraph hlf.edge_mem]
      exact mem_singleton f
    -- Helper: if one edge `f₃` of `T` (linking `u₁, u₂`) is in `E(H₁.G)` and the other two edges
    -- `f₁` (linking `u₂, u₃`) and `f₂` (linking `u₁, u₃`) are in `E(T)`, then `f₁, f₂ ∈ E(G₁)`.
    have htwo_other_edges : ∀ u₁ u₂ u₃ : α, ∀ f₁ f₂ f₃ : β,
        u₁ ≠ u₂ → u₂ ≠ u₃ → u₁ ≠ u₃ →
        S.G.IsLink f₁ u₂ u₃ → S.G.IsLink f₂ u₁ u₃ → S.G.IsLink f₃ u₁ u₂ →
        f₃ ∈ E(H₁.G) → f₁ ∈ E(G₁) ∧ f₂ ∈ E(G₁) := by
      intro u₁ u₂ u₃ f₁ f₂ f₃ hu₁₂ hu₂₃ hu₁₃ hlf₁ hlf₂ hlf₃ hf₃_H₁
      have hlf₃_H₁ : H₁.G.IsLink f₃ u₁ u₂ := (hsep_H.1.isLink_iff hf₃_H₁).mpr hlf₃
      have hu₁_H₁ : u₁ ∈ V(H₁.G) := hlf₃_H₁.left_mem
      have hu₂_H₁ : u₂ ∈ V(H₁.G) := hlf₃_H₁.right_mem
      have hf₁_union : f₁ ∈ E(H₁.G) ∪ E(H₂.G) := by rw [hsep_H.2.2.2.1]; exact hlf₁.edge_mem
      have hf₂_union : f₂ ∈ E(H₁.G) ∪ E(H₂.G) := by rw [hsep_H.2.2.2.1]; exact hlf₂.edge_mem
      rcases hf₁_union with hf₁_H₁ | hf₁_H₂ <;> rcases hf₂_union with hf₂_H₁ | hf₂_H₂
      · exact ⟨hH₁_le_G₁.edgeSet_mono hf₁_H₁, hH₁_le_G₁.edgeSet_mono hf₂_H₁⟩
      · have hu₃_H₁ : u₃ ∈ V(H₁.G) := ((hsep_H.1.isLink_iff hf₁_H₁).mpr hlf₁).right_mem
        have hlf₂_H₂ : H₂.G.IsLink f₂ u₁ u₃ := (hsep_H.2.1.isLink_iff hf₂_H₂).mpr hlf₂
        exact ⟨hH₁_le_G₁.edgeSet_mono hf₁_H₁,
          hGstar_le_G₁.edgeSet_mono (hsingle_in_Gstar f₂ u₁ u₃ hlf₂_H₂ hu₁_H₁ hu₃_H₁)⟩
      · have hu₃_H₁ : u₃ ∈ V(H₁.G) := ((hsep_H.1.isLink_iff hf₂_H₁).mpr hlf₂).right_mem
        have hlf₁_H₂ : H₂.G.IsLink f₁ u₂ u₃ := (hsep_H.2.1.isLink_iff hf₁_H₂).mpr hlf₁
        exact ⟨hGstar_le_G₁.edgeSet_mono (hsingle_in_Gstar f₁ u₂ u₃ hlf₁_H₂ hu₂_H₁ hu₃_H₁),
          hH₁_le_G₁.edgeSet_mono hf₂_H₁⟩
      · have hlf₁_H₂ : H₂.G.IsLink f₁ u₂ u₃ := (hsep_H.2.1.isLink_iff hf₁_H₂).mpr hlf₁
        have hlf₂_H₂ : H₂.G.IsLink f₂ u₁ u₃ := (hsep_H.2.1.isLink_iff hf₂_H₂).mpr hlf₂
        by_cases hu₃_bar₀ : u₃ ∈ H₂.Ω₀.bar
        · have hu₃_H₁ : u₃ ∈ V(H₁.G) := by
            rw [hΩ₀_H₂, hbar₀_inter] at hu₃_bar₀; exact hu₃_bar₀.1
          exact ⟨hGstar_le_G₁.edgeSet_mono (hsingle_in_Gstar f₁ u₂ u₃ hlf₁_H₂ hu₂_H₁ hu₃_H₁),
            hGstar_le_G₁.edgeSet_mono (hsingle_in_Gstar f₂ u₁ u₃ hlf₂_H₂ hu₁_H₁ hu₃_H₁)⟩
        · -- `f₂` and `f₁` form a 2-edge path `P` in `H₂.G` with ends `u₁, u₂ ∈ ΩBar₀` and middle
          -- `u₃ ∉ ΩBar₀`.
          have hu₁_bar₀ : u₁ ∈ H₂.Ω₀.bar := by
            rw [hΩ₀_H₂, hbar₀_inter]; exact ⟨hu₁_H₁, hlf₂_H₂.left_mem⟩
          have hu₂_bar₀ : u₂ ∈ H₂.Ω₀.bar := by
            rw [hΩ₀_H₂, hbar₀_inter]; exact ⟨hu₂_H₁, hlf₁_H₂.left_mem⟩
          obtain ⟨hP_path, _, hVP_diff, hEP, hP_card⟩ :=
            isGraphPathWithEnds_two_edges hlf₂_H₂ hlf₁_H₂.symm hu₁₃ hu₂₃.symm hu₁₂
          have hdisj : Disjoint (V(subgraphUnion H₂.G (singleEdgeSubgraph H₂.G f₂)
            (singleEdgeSubgraph H₂.G f₁)) \ {u₁, u₂})
              H₂.Ω₀.bar := by
            rw [hVP_diff, disjoint_singleton_left]; exact hu₃_bar₀
          have hle_Gstar := short_path_le_park hreg hpark hP_path hu₁₂ hu₁_bar₀ hu₂_bar₀ hdisj
            hP_card
          have hf₁_Gstar : f₁ ∈ E(N_star.G) :=
            hle_Gstar.edgeSet_mono (by rw [hEP]; exact mem_insert_of_mem _ (mem_singleton f₁))
          have hf₂_Gstar : f₂ ∈ E(N_star.G) :=
            hle_Gstar.edgeSet_mono (by rw [hEP]; exact mem_insert f₂ {f₁})
          exact ⟨hGstar_le_G₁.edgeSet_mono hf₁_Gstar, hGstar_le_G₁.edgeSet_mono hf₂_Gstar⟩
    apply hV_of_E G₁ hG₁_le_G
    have hl₁ : S.G.IsLink e₁ v₂ v₃ := hl₁T.mono hT.1.1
    have hl₂ : S.G.IsLink e₂ v₁ v₃ := hl₂T.mono hT.1.1
    have hl₃ : S.G.IsLink e₃ v₁ v₂ := hl₃T.mono hT.1.1
    obtain ⟨e, heT, he_H₁⟩ := hex_E₁
    rw [hET] at heT ⊢
    rcases heT with h_eq | h_eq | h_eq
    · subst e
      have h23 := htwo_other_edges v₂ v₃ v₁ e₂ e₃ e₁ hv₂₃ hv₁₃.symm hv₁₂.symm hl₂.symm hl₃.symm hl₁
        he_H₁
      rintro f (rfl | rfl | rfl)
      · exact hH₁_le_G₁.edgeSet_mono he_H₁
      · exact h23.1
      · exact h23.2
    · subst e
      have h13 := htwo_other_edges v₁ v₃ v₂ e₁ e₃ e₂ hv₁₃ hv₂₃.symm hv₁₂ hl₁.symm hl₃ hl₂ he_H₁
      rintro f (rfl | rfl | rfl)
      · exact h13.1
      · exact hH₁_le_G₁.edgeSet_mono he_H₁
      · exact h13.2
    · subst e
      have h12 := htwo_other_edges v₁ v₂ v₃ e₁ e₂ e₃ hv₁₂ hv₂₃ hv₁₃ hl₁ hl₂ hl₃ he_H₁
      rintro f (rfl | rfl | rfl)
      · exact h12.1
      · exact h12.2
      · exact hH₁_le_G₁.edgeSet_mono he_H₁

/-- The argument of (11.5) of Graph Minors IX (pages 69-70), given a regular park of the rural part
`H₂` of a composition of `S`: the new society is the old one together with the park, and the new
rural neighborhood is the part of `H₂` outside the wall. -/
theorem composition_of_regular_park (S : Society α β) (hsimple : IsSimpleGraph S.G) {p : ℕ}
    {H₁ : Society α β} {H₂ : Neighborhood α β} (hcomp : S.IsComposition H₁ H₂)
    (hH₁_no : ∀ P_set : Set (Graph α β), H₁.IsTransaction P_set → P_set.ncard ≤ p)
    {P_pres : Presentation H₂} {N_star : Neighborhood α β}
    (hreg_park : IsRegularParkOf P_pres N_star)
    (hN₂_rural : (outerParkNeighborhood P_pres hreg_park.isParkOf).IsRural) :
    ∃ (S₁ : Society α β) (N₂ : Neighborhood α β),
      N₂.IsRural ∧
      N₂.Ω = S.Ω ∧
      N₂.Ω₀ = S₁.Ω ∧
      S₁.G ≤ S.G ∧
      N₂.G ≤ S.G ∧
      subgraphUnion S.G S₁.G N₂.G = S.G ∧
      V(subgraphInter S.G S₁.G N₂.G) = S₁.Ω.bar ∧
      (∀ Q_set : Set (Graph α β), S₁.IsTransaction Q_set → Q_set.ncard ≤ p + 2) ∧
      (∀ T : Graph α β, IsTriangle S.G T → T ≤ S₁.G ∨ T ≤ N₂.G) := by
  have composition := hcomp
  obtain ⟨⟨hsep_H, hbar_H₂⟩, hΩ_H₂, hΩ₀_H₂, hbar₀_inter⟩ := hcomp
  have hreg : IsRegularPresentation P_pres := hreg_park.isRegularPresentation
  have hpark : IsParkOf P_pres N_star := hreg_park.isParkOf
  have hGstar_le_H₂ : N_star.G ≤ H₂.G := hpark.2.2.2.2.1
  have hGstar_le_G : N_star.G ≤ S.G := hGstar_le_H₂.trans hsep_H.2.1
  -- Construct `S₁ = (H₁ ∪ G*, Ω*)` and `N₂ = outerParkNeighborhood P_pres hpark`.
  let G₁ : Graph α β := subgraphUnion S.G H₁.G N_star.G
  have hG₁_le_G : G₁ ≤ S.G := subgraphUnion_le hsep_H.1 hGstar_le_G
  have hH₁_le_G₁ : H₁.G ≤ G₁ := le_subgraphUnion_left hsep_H.1 hGstar_le_G
  have hGstar_le_G₁ : N_star.G ≤ G₁ := le_subgraphUnion_right hsep_H.1 hGstar_le_G
  let S₁ : Society α β := {
    G := G₁
    Ω := N_star.Ω
    finite_V := S.finite_V.subset hG₁_le_G.vertexSet_mono
    finite_E := S.finite_E.subset hG₁_le_G.edgeSet_mono
    bar_subset := N_star.bar_subset.trans hGstar_le_G₁.vertexSet_mono
  }
  let N₂ : Neighborhood α β := outerParkNeighborhood P_pres hpark
  have hN₂_le_H₂ : N₂.G ≤ H₂.G := outerParkGraph_le P_pres
  have hN₂_le_G : N₂.G ≤ S.G := hN₂_le_H₂.trans hsep_H.2.1
  -- Show that `H₂.Ω₀.bar ⊆ V(N_star.G)`.
  have hbar₀_sub_Gstar : H₂.Ω₀.bar ⊆ V(N_star.G) := by
    intro v hv_bar₀
    have hvH₂ : v ∈ V(H₂.G) := H₂.bar₀_subset hv_bar₀
    rw [hpark.2.2.1]
    refine ⟨hvH₂, ?_⟩
    have hv_bd₀ : graphDrawingVertexSet P_pres.Γ v ⊆ subBd P_pres.Δ₀ :=
      (P_pres.mem_bd_Δ₀_iff v hvH₂).mpr hv_bar₀
    have hbd₀_sub : subBd P_pres.Δ₀ ⊆ P_pres.Δ₀ := by
      rcases P_pres.agrees_Δ₀ with ⟨hΔ₀_empty, _⟩ | ⟨hΔ₀_disc, _⟩
      · rw [hΔ₀_empty, subBd, closure_empty, empty_inter]
      · exact subBd_subset_of_isClosed (isClosed_of_isClosedDisc hΔ₀_disc)
    exact hv_bd₀.trans (hbd₀_sub.trans subset_union_left)
  -- Show that `S₁` is the composition of `H₁` with the park `N_star`.
  have hcomp_S₁ : S₁.IsComposition H₁ N_star := by
    refine ⟨⟨⟨hH₁_le_G₁, hGstar_le_G₁, rfl, ?_, ?_⟩, N_star.bar_subset⟩,
      rfl, hpark.2.1.trans hΩ₀_H₂, ?_⟩
    · exact (edgeSet_subgraphUnion hsep_H.1 hGstar_le_G).symm
    · exact hsep_H.2.2.2.2.mono_right hGstar_le_H₂.edgeSet_mono
    · refine subset_antisymm ?_ ?_
      · intro v hv_bar
        refine ⟨H₁.bar_subset hv_bar, hbar₀_sub_Gstar (hΩ₀_H₂.symm ▸ hv_bar)⟩
      · intro v ⟨hvH₁, hvGstar⟩
        rw [hbar₀_inter]
        exact ⟨hvH₁, hGstar_le_H₂.vertexSet_mono hvGstar⟩
  -- Show `G* ∪ G₂ = H₂`.
  have hV_Gstar_union_G₂ : V(N_star.G) ∪ V(N₂.G) = V(H₂.G) := by
    refine subset_antisymm (union_subset hGstar_le_H₂.vertexSet_mono hN₂_le_H₂.vertexSet_mono) ?_
    intro v hvH₂
    let x := (P_pres.Γ.iso.vertexEquiv ⟨v, hvH₂⟩).1
    have hxv : graphDrawingVertexSet P_pres.Γ v = {x} := graphDrawingVertexSet_eq_singleton
      P_pres.Γ hvH₂
    by_cases hx_wd : x ∈ wallDisc P_pres
    · left
      rw [hpark.2.2.1]
      exact ⟨hvH₂, by rw [hxv, singleton_subset_iff]; exact hx_wd⟩
    · right
      change v ∈ outerParkVerts P_pres
      have hx_V : x ∈ P_pres.Γ.drawing.V := (P_pres.Γ.iso.vertexEquiv ⟨v, hvH₂⟩).2
      have hx_U : x ∈ P_pres.Γ.drawing.U := P_pres.Γ.drawing.V_subset_U hx_V
      have hx_Δ : x ∈ P_pres.Δ := (P_pres.U_subset hx_U).1
      exact ⟨hvH₂, by rw [hxv, singleton_subset_iff]; exact Or.inr ⟨hx_Δ, hx_wd⟩⟩
  have hE_Gstar_union_G₂ : E(N_star.G) ∪ E(N₂.G) = E(H₂.G) := by
    refine subset_antisymm (union_subset hGstar_le_H₂.edgeSet_mono hN₂_le_H₂.edgeSet_mono) ?_
    intro e heH₂
    rcases hreg.edge_trichotomy e heH₂ with he_int | he_ext | he_wall
    · left
      rw [hpark.2.2.2.1]
      exact ⟨heH₂, he_int.2.trans interior_subset⟩
    · right
      change e ∈ E(outerParkGraph P_pres)
      rw [edgeSet_outerParkGraph]
      exact ⟨heH₂, Or.inr he_ext⟩
    · right
      change e ∈ E(outerParkGraph P_pres)
      rw [edgeSet_outerParkGraph]
      exact ⟨heH₂, Or.inl he_wall⟩
  refine ⟨S₁, N₂, hN₂_rural, hΩ_H₂, rfl, hG₁_le_G, hN₂_le_G, ?_, ?_, ?_, ?_⟩
  · -- (i.a) `G₁ ∪ G₂ = G`
    refine (Compatible.of_le_le (subgraphUnion_le hG₁_le_G hN₂_le_G) le_rfl).ext ?_ ?_
    · rw [vertexSet_subgraphUnion, show V(S₁.G) = V(H₁.G) ∪ V(N_star.G) from rfl,
        union_assoc, hV_Gstar_union_G₂, hsep_H.2.2.1]
    · rw [edgeSet_subgraphUnion hG₁_le_G hN₂_le_G,
        show E(S₁.G) = E(H₁.G) ∪ E(N_star.G) from edgeSet_subgraphUnion hsep_H.1 hGstar_le_G,
        union_assoc, hE_Gstar_union_G₂, hsep_H.2.2.2.1]
  · -- (i.b) `V(G₁ ∩ G₂) = ΩBar₁`
    change (V(H₁.G) ∪ V(N_star.G)) ∩ outerParkVerts P_pres = N_star.Ω.bar
    have hGstar_inter : V(N_star.G) ∩ outerParkVerts P_pres = N_star.Ω.bar := by
      rw [hpark.2.2.1, hpark.2.2.2.2.2.1]
      ext v
      simp only [outerParkVerts, mem_inter_iff, mem_sep_iff]
      constructor
      · rintro ⟨⟨hvH₂, hv_wd⟩, _, hv_out⟩
        refine ⟨hvH₂, fun x hx => ?_⟩
        rcases hv_out hx with hx_wall | ⟨_, hx_not_wd⟩
        · exact hx_wall
        · exact (hx_not_wd (hv_wd hx)).elim
      · rintro ⟨hvH₂, hv_wall⟩
        exact ⟨⟨hvH₂, hv_wall.trans (wall_subset_wallDisc hreg)⟩,
          hvH₂, hv_wall.trans subset_union_left⟩
    have hH₁_inter : V(H₁.G) ∩ outerParkVerts P_pres ⊆ V(N_star.G) ∩ outerParkVerts P_pres := by
      rintro v ⟨hvH₁, hv_out⟩
      have hv_bar₀ : v ∈ H₂.Ω₀.bar := by
        rw [hΩ₀_H₂, hbar₀_inter]
        exact ⟨hvH₁, hv_out.1⟩
      exact ⟨hbar₀_sub_Gstar hv_bar₀, hv_out⟩
    rw [union_inter_distrib_right, union_eq_right.mpr hH₁_inter, hGstar_inter]
  · -- (ii) `(G₁, Ω₁)` has no transaction of cardinality `> p + 2`, by (11.4).
    intro Q_set hQ_set
    exact theorem_11_4_proof ⟨H₂, P_pres, hreg_park⟩ hcomp_S₁ hH₁_no hQ_set
  · exact triangle_in_park_or_exterior S hsimple composition hreg hpark
      hG₁_le_G hH₁_le_G₁ hGstar_le_G₁

end GraphMinor.GM09
