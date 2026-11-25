/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Defs

import LeanPool.GraphMinor.GM09.Basic

/-!
# Bridges of a subgraph

A component of the complement of a subgraph gives a bridge. These lemmas show that bridges cover
the vertices and edges of the ambient graph outside the subgraph and give their intersection
properties.
-/

public section

namespace GraphMinor.GM14

open Set Graph GM06 GM09 Surface

universe u v

/-- For any component `C` of `deleteVertices G V(H_sub)`, the subgraph `B` formed by `C` and its
attachment edges to `V(H_sub)` is a bridge (`IsBridge G H_sub B`). -/
theorem isBridge_of_component {α : Type u} {β : Type v}
    {G H_sub C : Graph α β} (hH : H_sub ≤ G)
    (hC : C ∈ graphComponents (deleteVertices G V(H_sub))) :
    let V_B := V(C) ∪ {v ∈ V(H_sub) | ∃ e ∈ E(G), ∃ u ∈ V(C), G.IsLink e u v}
    let E_B := E(C) ∪ {e ∈ E(G) | ∃ u ∈ V(C), ∃ v ∈ V(H_sub), G.IsLink e u v}
    let B := (G.induce V_B).restrict E_B
    IsBridge G H_sub B ∧ V(B) = V_B ∧ E(B) = E_B := by
  intro V_B E_B B
  have hC_del : C ≤ deleteVertices G V(H_sub) := hC.1
  have hdel_G : deleteVertices G V(H_sub) ≤ G := deleteVertices_le G V(H_sub)
  have hC_G : C ≤ G := hC_del.trans hdel_G
  have hVB_sub : V_B ⊆ V(G) := by
    rintro v (hvC | ⟨hvH, _⟩)
    · exact hC_G.vertexSet_mono hvC
    · exact hH.vertexSet_mono hvH
  have hB_le : B ≤ G := restrict_le.trans (G.induce_le hVB_sub)
  have hVB_eq : V(B) = V_B := by
    simp [B]
  have hEB_eq : E(B) = E_B := by
    ext e
    simp only [B, edgeSet_restrict, mem_inter_iff, edgeSet_induce]
    refine ⟨fun h => h.2, fun he => ⟨?_, he⟩⟩
    rcases he with heC | ⟨heG, u, huC, v, hvH, hlink⟩
    · obtain ⟨x, y, hxy⟩ := C.exists_isLink_of_mem_edgeSet heC
      exact ⟨x, y, hxy.mono hC_G, Or.inl hxy.left_mem, Or.inl hxy.right_mem⟩
    · exact ⟨u, v, hlink, Or.inl huC, Or.inr ⟨hvH, e, heG, u, huC, hlink⟩⟩
  refine ⟨⟨hH, hB_le, Or.inr ⟨C, hC, hVB_eq, hEB_eq⟩⟩, hVB_eq, hEB_eq⟩

/-- Every vertex of `G` outside `V(H_sub)` belongs to a bridge of `H_sub` in `G`. -/
theorem exists_bridge_of_mem_vertexSet {α : Type u} {β : Type v}
    {G H_sub : Graph α β} (hH : H_sub ≤ G) {v : α} (hvG : v ∈ V(G)) (hvH : v ∉ V(H_sub)) :
    ∃ B : Graph α β, IsBridge G H_sub B ∧ v ∈ V(B) := by
  have hv_del : v ∈ V(deleteVertices G V(H_sub)) := ⟨hvG, hvH⟩
  obtain ⟨C, hC, hvC⟩ := exists_graphComponent_of_mem hv_del
  obtain ⟨hB, hVB, _⟩ := isBridge_of_component hH hC
  exact ⟨_, hB, hVB ▸ Or.inl hvC⟩

/-- Every edge of `G` outside `E(H_sub)` belongs to a bridge of `H_sub` in `G`. -/
theorem exists_bridge_of_mem_edgeSet {α : Type u} {β : Type v}
    {G H_sub : Graph α β} (hH : H_sub ≤ G) {e : β} (heG : e ∈ E(G)) (heH : e ∉ E(H_sub)) :
    ∃ B : Graph α β, IsBridge G H_sub B ∧ e ∈ E(B) := by
  obtain ⟨u, v, hlink⟩ := G.exists_isLink_of_mem_edgeSet heG
  by_cases huH : u ∈ V(H_sub)
  · by_cases hvH : v ∈ V(H_sub)
    · let B := (G.induce {u, v}).restrict {e}
      have hsub : ({u, v} : Set α) ⊆ V(G) := by
        rintro x (rfl | rfl)
        · exact hlink.left_mem
        · exact hlink.right_mem
      have hB_le : B ≤ G := restrict_le.trans (G.induce_le hsub)
      have hVB : V(B) = {u, v} := by simp [B]
      have hEB : E(B) = {e} := by
        ext e'
        simp only [B, edgeSet_restrict, mem_inter_iff, edgeSet_induce, mem_singleton_iff]
        refine ⟨fun h => h.2, ?_⟩
        rintro rfl
        exact ⟨⟨u, v, hlink, Or.inl rfl, Or.inr rfl⟩, rfl⟩
      exact ⟨B, ⟨hH, hB_le, Or.inl ⟨e, ⟨heG, heH⟩, u, huH, v, hvH, hlink, hVB, hEB⟩⟩,
        hEB ▸ mem_singleton e⟩
    · have hv_del : v ∈ V(deleteVertices G V(H_sub)) := ⟨hlink.right_mem, hvH⟩
      obtain ⟨C, hC, hvC⟩ := exists_graphComponent_of_mem hv_del
      obtain ⟨hB, _, hEB⟩ := isBridge_of_component hH hC
      refine ⟨_, hB, hEB.symm ▸ Or.inr ⟨heG, v, hvC, u, huH, hlink.symm⟩⟩
  · have hu_del : u ∈ V(deleteVertices G V(H_sub)) := ⟨hlink.left_mem, huH⟩
    obtain ⟨C, hC, huC⟩ := exists_graphComponent_of_mem hu_del
    obtain ⟨hB, _, hEB⟩ := isBridge_of_component hH hC
    by_cases hvH : v ∈ V(H_sub)
    · exact ⟨_, hB, hEB.symm ▸ Or.inr ⟨heG, u, huC, v, hvH, hlink⟩⟩
    · have hlink_del : (deleteVertices G V(H_sub)).IsLink e u v :=
        (deleteVertices_isLink G V(H_sub)).mpr ⟨hlink, huH, hvH⟩
      have hvC : v ∈ V(C) := (mem_graphComponent_iff_of_isLink hC hlink_del).mp huC
      have heC : e ∈ E(C) :=
        (isClosedSubgraph_of_isGraphComponent hC).closed ⟨v, hlink_del⟩ huC
      exact ⟨_, hB, hEB.symm ▸ Or.inl heC⟩

private theorem bridge_edge_with_ends_in_subgraph {α : Type u} {β : Type v}
    {G H_sub B : Graph α β} (hB : IsBridge G H_sub B) {e : β} {x y : α}
    (hxy : G.IsLink e x y) (hx : x ∈ V(H_sub)) (hy : y ∈ V(H_sub)) (heB : e ∈ E(B)) :
    e ∉ E(H_sub) ∧ V(B) = {x, y} ∧ E(B) = {e} := by
  rcases hB.2.2 with ⟨e₀, he₀, u, _, v, _, huv, hVB, hEB⟩ | ⟨C, hC, _, hEB⟩
  · rw [hEB, mem_singleton_iff] at heB
    subst heB
    refine ⟨he₀.2, ?_, hEB⟩
    rw [hVB]
    rcases huv.eq_and_eq_or_eq_and_eq hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact Set.pair_comm u v
  · have hC_del : C ≤ deleteVertices G V(H_sub) := hC.1
    rw [hEB] at heB
    rcases heB with heC | ⟨_, u, huC, v, _, huv⟩
    · obtain ⟨u, v, huv_C⟩ := C.exists_isLink_of_mem_edgeSet heC
      have huv_G : G.IsLink e u v := huv_C.mono (hC_del.trans (deleteVertices_le G V(H_sub)))
      have hu_not_H : u ∉ V(H_sub) := (hC_del.vertexSet_mono huv_C.left_mem).2
      rcases huv_G.eq_and_eq_or_eq_and_eq hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact (hu_not_H hx).elim
      · exact (hu_not_H hy).elim
    · have hu_not_H : u ∉ V(H_sub) := (hC_del.vertexSet_mono huC).2
      rcases huv.eq_and_eq_or_eq_and_eq hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact (hu_not_H hx).elim
      · exact (hu_not_H hy).elim

/-- Every bridge `B` of `H_sub` in `G` is edge-disjoint from `H_sub`. -/
theorem isBridge_disjoint_edgeSet {α : Type u} {β : Type v}
    {G H_sub B : Graph α β} (hB : IsBridge G H_sub B) :
    Disjoint E(B) E(H_sub) := by
  refine Set.disjoint_left.mpr fun e heB heH => ?_
  obtain ⟨x, y, hxy⟩ := H_sub.exists_isLink_of_mem_edgeSet heH
  exact (bridge_edge_with_ends_in_subgraph hB (hxy.mono hB.1) hxy.left_mem hxy.right_mem heB).1 heH

/-- Two bridges `B₁, B₂` of `H_sub` in `G` that share a vertex outside `V(H_sub)` or share an edge
are equal (`B₁ = B₂`). -/
theorem isBridge_eq_of_inter {α : Type u} {β : Type v}
    {G H_sub B₁ B₂ : Graph α β} (hB₁ : IsBridge G H_sub B₁) (hB₂ : IsBridge G H_sub B₂) :
    (∀ v ∈ V(B₁) ∩ V(B₂), v ∉ V(H_sub) → B₁ = B₂) ∧
    (∀ e ∈ E(B₁) ∩ E(B₂), B₁ = B₂) := by
  have hcomp_of_vertex : ∀ {B : Graph α β} {v : α},
      IsBridge G H_sub B → v ∈ V(B) → v ∉ V(H_sub) →
      ∃ C ∈ graphComponents (deleteVertices G V(H_sub)),
        v ∈ V(C) ∧
        V(B) = V(C) ∪ {w ∈ V(H_sub) | ∃ e ∈ E(G), ∃ x ∈ V(C), G.IsLink e x w} ∧
        E(B) = E(C) ∪ {e ∈ E(G) | ∃ x ∈ V(C), ∃ w ∈ V(H_sub), G.IsLink e x w} := by
    intro B v hB hvB hv_not_H
    rcases hB.2.2 with ⟨e, _, w₁, hw₁, w₂, hw₂, _, hVB, _⟩ | ⟨C, hC, hVB, hEB⟩
    · rw [hVB] at hvB
      rcases hvB with rfl | rfl
      · exact (hv_not_H hw₁).elim
      · exact (hv_not_H hw₂).elim
    · rw [hVB] at hvB
      rcases hvB with hvC | ⟨hvH, _⟩
      · exact ⟨C, hC, hvC, hVB, hEB⟩
      · exact (hv_not_H hvH).elim
  have h_eq_of_vertex : ∀ v ∈ V(B₁) ∩ V(B₂), v ∉ V(H_sub) → B₁ = B₂ := by
    rintro v ⟨hv₁, hv₂⟩ hv_not_H
    obtain ⟨C₁, hC₁, hvC₁, hVB₁, hEB₁⟩ := hcomp_of_vertex hB₁ hv₁ hv_not_H
    obtain ⟨C₂, hC₂, hvC₂, hVB₂, hEB₂⟩ := hcomp_of_vertex hB₂ hv₂ hv_not_H
    have hC_eq : C₁ = C₂ := isGraphComponent_eq_of_mem_inter hC₁ hC₂ ⟨v, hvC₁, hvC₂⟩
    refine (Compatible.of_le_le hB₁.2.1 hB₂.2.1).ext ?_ ?_
    · rw [hVB₁, hVB₂, hC_eq]
    · rw [hEB₁, hEB₂, hC_eq]
  refine ⟨h_eq_of_vertex, ?_⟩
  rintro e ⟨he₁, he₂⟩
  obtain ⟨x, y, hxy₁⟩ := B₁.exists_isLink_of_mem_edgeSet he₁
  have hxy_G : G.IsLink e x y := hxy₁.mono hB₁.2.1
  have hxy₂ : B₂.IsLink e x y := (hB₂.2.1.isLink_iff he₂).mpr hxy_G
  by_cases hxH : x ∈ V(H_sub)
  · by_cases hyH : y ∈ V(H_sub)
    · obtain ⟨_, hVB₁, hEB₁⟩ :=
        bridge_edge_with_ends_in_subgraph hB₁ hxy_G hxH hyH he₁
      obtain ⟨_, hVB₂, hEB₂⟩ := bridge_edge_with_ends_in_subgraph hB₂ hxy_G hxH hyH he₂
      exact (Compatible.of_le_le hB₁.2.1 hB₂.2.1).ext
        (hVB₁.trans hVB₂.symm) (hEB₁.trans hEB₂.symm)
    · exact h_eq_of_vertex y ⟨hxy₁.right_mem, hxy₂.right_mem⟩ hyH
  · exact h_eq_of_vertex x ⟨hxy₁.left_mem, hxy₂.left_mem⟩ hxH

/-- Two bridges that share a vertex outside the subgraph or share an edge have equal vertex sets. -/
theorem isBridge_vertexSet_eq_of_inter {α : Type u} {β : Type v}
    {G H_sub B₁ B₂ : Graph α β} (hB₁ : IsBridge G H_sub B₁) (hB₂ : IsBridge G H_sub B₂) :
    (∀ v ∈ V(B₁) ∩ V(B₂), v ∉ V(H_sub) → V(B₁) = V(B₂)) ∧
    (∀ e ∈ E(B₁) ∩ E(B₂), V(B₁) = V(B₂)) := by
  obtain ⟨hvertex, hedge⟩ := isBridge_eq_of_inter hB₁ hB₂
  exact ⟨fun v hv hvH => congrArg Graph.vertexSet (hvertex v hv hvH),
    fun e he => congrArg Graph.vertexSet (hedge e he)⟩

/-- If `C` is a connected component of `deleteVertices G V(H_sub)` and `u', v' ∈ V(H_sub)` are
distinct vertices linked in `G` by edges `e₁, e₂` to vertices `x₁, x₂ ∈ V(C)`, then there is an
`H_sub`-path `P` in `G` with ends `u'` and `v'`. -/
theorem exists_isHPathWithEnds_of_component_attachments {α : Type u} {β : Type v}
    {G H_sub C : Graph α β}
    (hH : H_sub ≤ G) (hC : C ∈ graphComponents (deleteVertices G V(H_sub)))
    {u' v' x₁ x₂ : α} {e₁ e₂ : β}
    (hu' : u' ∈ V(H_sub)) (hv' : v' ∈ V(H_sub)) (huv' : u' ≠ v')
    (hx₁ : x₁ ∈ V(C)) (hx₂ : x₂ ∈ V(C))
    (he₁ : G.IsLink e₁ u' x₁) (he₂ : G.IsLink e₂ x₂ v') :
    ∃ P : Graph α β, IsHPathWithEnds G H_sub P u' v' := by
  have hC_del : C ≤ deleteVertices G V(H_sub) := hC.1
  have hdel_G : deleteVertices G V(H_sub) ≤ G := deleteVertices_le G V(H_sub)
  have hC_G : C ≤ G := hC_del.trans hdel_G
  have hVC_disj : ∀ w ∈ V(C), w ∉ V(H_sub) := fun w hw =>
    (hC_del.vertexSet_mono hw).2
  obtain ⟨W₀⟩ := hC.2.1.2 x₁ hx₁ x₂ hx₂
  obtain ⟨W, hW_sim, _, _⟩ := exists_isSimple_subwalk W₀
  obtain ⟨W_G, hWG_sup, hWG_ed⟩ := exists_walk_up_of_le hC_G W
  let W_full : GraphWalk G u' v' :=
    GraphWalk.cons he₁ (W_G.append (GraphWalk.cons he₂ (GraphWalk.nil he₂.right_mem)))
  have hWf_sup : W_full.support = u' :: (W.support ++ [v']) := by
    simp [W_full, GraphWalk.support_append, hWG_sup]
  have hWf_ed : W_full.edges = e₁ :: (W.edges ++ [e₂]) := by
    simp [W_full, GraphWalk.edges_append, hWG_ed]
  have hu'_not_W : u' ∉ W.support := fun h =>
    hVC_disj u' (W.mem_vertexSet_of_mem_support h) hu'
  have hv'_not_W : v' ∉ W.support := fun h =>
    hVC_disj v' (W.mem_vertexSet_of_mem_support h) hv'
  have hWf_sim : W_full.IsSimple := by
    unfold GraphWalk.IsSimple
    rw [hWf_sup, List.nodup_cons]
    refine ⟨?_, ?_⟩
    · simp only [List.mem_append, List.mem_singleton, not_or]
      exact ⟨hu'_not_W, huv'⟩
    · rw [List.nodup_append]
      refine ⟨hW_sim, List.nodup_singleton v', fun z hz w hw hzw => ?_⟩
      simp only [List.mem_singleton] at hw
      subst hw hzw
      exact hv'_not_W hz
  let P := walkSubgraph W_full
  refine ⟨P, hH, isGraphPathWithEnds_walkSubgraph hWf_sim, huv', hu', hv', ?_, ?_⟩
  · rw [vertexSet_walkSubgraph]
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq, hWf_sup, List.mem_cons, List.mem_append,
      List.not_mem_nil, or_false, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨rfl | hzW | rfl, hzH⟩
      · exact Or.inl rfl
      · exact False.elim (hVC_disj z (W.mem_vertexSet_of_mem_support hzW) hzH)
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨Or.inl rfl, hu'⟩
      · exact ⟨Or.inr (Or.inr rfl), hv'⟩
  · rw [edgeSet_walkSubgraph]
    refine Set.disjoint_left.mpr fun e heP heH => ?_
    simp only [mem_ofPred_eq, hWf_ed, List.mem_cons, List.mem_append,
      List.not_mem_nil, or_false] at heP
    rcases heP with rfl | heW | rfl
    · have hlinkH : H_sub.IsLink e u' x₁ := (hH.isLink_iff heH).mpr he₁
      exact hVC_disj x₁ hx₁ hlinkH.right_mem
    · have heC : e ∈ E(C) := walk_edges_subset_edgeSet W e heW
      have he_del : e ∈ E(deleteVertices G V(H_sub)) := hC_del.edgeSet_mono heC
      obtain ⟨w₁, w₂, hlink_del⟩ := exists_isLink_of_mem_edgeSet he_del
      have hlink_G : G.IsLink e w₁ w₂ := hlink_del.mono hdel_G
      have hlink_H : H_sub.IsLink e w₁ w₂ := (hH.isLink_iff heH).mpr hlink_G
      exact hlink_del.left_mem.2 hlink_H.left_mem
    · have hlinkH : H_sub.IsLink e x₂ v' := (hH.isLink_iff heH).mpr he₂
      exact hVC_disj x₂ hx₂ hlinkH.left_mem

/-- If `B` is a bridge of `H_sub` in `G` and `u', v' ∈ V(B) ∩ V(H_sub)` are distinct, then there is
an `H_sub`-path `P` in `G` with ends `u'` and `v'`. -/
theorem exists_isHPathWithEnds_of_isBridge {α : Type u} {β : Type v}
    {G H_sub B : Graph α β}
    (hB : IsBridge G H_sub B) {u' v' : α}
    (hu'B : u' ∈ V(B)) (hv'B : v' ∈ V(B))
    (hu'H : u' ∈ V(H_sub)) (hv'H : v' ∈ V(H_sub)) (huv' : u' ≠ v') :
    ∃ P : Graph α β, IsHPathWithEnds G H_sub P u' v' := by
  rcases hB.2.2 with ⟨e, he, w₁, _, w₂, _, hlink_w, hVB, _⟩ | ⟨C, hC, hVB, _⟩
  · rw [hVB] at hu'B hv'B
    have hlink : G.IsLink e u' v' := by
      rcases hu'B with rfl | rfl <;> rcases hv'B with rfl | rfl
      · exact False.elim (huv' rfl)
      · exact hlink_w
      · exact hlink_w.symm
      · exact False.elim (huv' rfl)
    let W : GraphWalk G u' v' := GraphWalk.cons hlink (GraphWalk.nil hlink.right_mem)
    have hW_sup : W.support = [u', v'] := rfl
    have hW_ed : W.edges = [e] := rfl
    have hW_sim : W.IsSimple := by
      unfold GraphWalk.IsSimple
      rw [hW_sup]
      simp [huv']
    refine ⟨walkSubgraph W, hB.1, isGraphPathWithEnds_walkSubgraph hW_sim, huv', hu'H, hv'H, ?_, ?_⟩
    · rw [vertexSet_walkSubgraph, hW_sup]
      ext z
      simp only [mem_inter_iff, mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false,
        mem_insert_iff, mem_singleton_iff]
      exact ⟨fun h => h.1, fun h => ⟨h, h.elim (fun h₁ => h₁ ▸ hu'H) (fun h₂ => h₂ ▸ hv'H)⟩⟩
    · rw [edgeSet_walkSubgraph, hW_ed]
      refine Set.disjoint_left.mpr fun f hfP hfH => ?_
      simp only [mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false] at hfP
      subst hfP
      exact he.2 hfH
  · rw [hVB] at hu'B hv'B
    have hVC_disj : ∀ w ∈ V(C), w ∉ V(H_sub) := fun w hw => (hC.1.vertexSet_mono hw).2
    have hu'E : ∃ e₁ ∈ E(G), ∃ x₁ ∈ V(C), G.IsLink e₁ x₁ u' := by
      rcases hu'B with hu'C | ⟨_, h⟩
      · exact False.elim (hVC_disj u' hu'C hu'H)
      · exact h
    have hv'E : ∃ e₂ ∈ E(G), ∃ x₂ ∈ V(C), G.IsLink e₂ x₂ v' := by
      rcases hv'B with hv'C | ⟨_, h⟩
      · exact False.elim (hVC_disj v' hv'C hv'H)
      · exact h
    obtain ⟨e₁, _, x₁, hx₁, hlink₁⟩ := hu'E
    obtain ⟨e₂, _, x₂, hx₂, hlink₂⟩ := hv'E
    exact exists_isHPathWithEnds_of_component_attachments hB.1 hC hu'H hv'H huv' hx₁ hx₂
      hlink₁.symm hlink₂

end GraphMinor.GM14
