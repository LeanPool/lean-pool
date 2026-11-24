/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM15.Section7
public import LeanPool.GraphMinor.GM16.ProperArrangement
import LeanPool.GraphMinor.GM16.ProperDiscIntersection
import LeanPool.GraphMinor.GM16.ProperDiscTransport
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM09.Section4b
import LeanPool.GraphMinor.GM10.Section12
import LeanPool.GraphMinor.GM11.OArcCircuit
import LeanPool.GraphMinor.GM11.Section81
import LeanPool.GraphMinor.GM14.Section7b
import LeanPool.GraphMinor.Surface.CircleMove

/-!
# Bridge intersections in the local arrangement assembly

These graph facts supply Claim (1) and Claim (2) of XV (7.7), pages 139–140. Bridges cover vertices
and edges outside the drawn graph, and two bridges that meet outside that graph have the same vertex
set.
-/

public section
namespace GraphMinor.GM16
open Set Function Topology
open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14 GM15
universe u v w
variable {α : Type u} {β : Type v}

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
    simp only [B, edgeSet_restrict, mem_inter_iff, Graph.edgeSet_induce]
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
        simp only [B, edgeSet_restrict, mem_inter_iff, Graph.edgeSet_induce, mem_singleton_iff]
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

/-- Every bridge `B` of `H_sub` in `G` is edge-disjoint from `H_sub`. -/
theorem isBridge_disjoint_edgeSet {α : Type u} {β : Type v}
    {G H_sub B : Graph α β} (hB : IsBridge G H_sub B) :
    Disjoint E(B) E(H_sub) := by
  refine Set.disjoint_left.mpr fun e heB heH => ?_
  obtain ⟨x, y, hxy_H⟩ := H_sub.exists_isLink_of_mem_edgeSet heH
  have hxy_G : G.IsLink e x y := hxy_H.mono hB.1
  rcases hB.2.2 with ⟨e₀, he₀, u, _, v, _, _, _, hEB⟩ | ⟨C, hC, _, hEB⟩
  · rw [hEB, mem_singleton_iff] at heB
    subst heB
    exact he₀.2 heH
  · have hC_del : C ≤ deleteVertices G V(H_sub) := hC.1
    rw [hEB] at heB
    rcases heB with heC | ⟨_, u, huC, v, _, huv⟩
    · obtain ⟨u, v, huv_C⟩ := C.exists_isLink_of_mem_edgeSet heC
      have huv_G : G.IsLink e u v := huv_C.mono (hC_del.trans (deleteVertices_le G V(H_sub)))
      have hu_not_H : u ∉ V(H_sub) := (hC_del.vertexSet_mono huv_C.left_mem).2
      rcases huv_G.eq_and_eq_or_eq_and_eq hxy_G with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hu_not_H hxy_H.left_mem
      · exact hu_not_H hxy_H.right_mem
    · have hu_not_H : u ∉ V(H_sub) := (hC_del.vertexSet_mono huC).2
      rcases huv.eq_and_eq_or_eq_and_eq hxy_G with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hu_not_H hxy_H.left_mem
      · exact hu_not_H hxy_H.right_mem

/-- Two bridges `B₁, B₂` of `H_sub` in `G` that share a vertex outside `V(H_sub)` or share an edge
have the same vertex set `V(B₁) = V(B₂)`. -/
theorem isBridge_vertexSet_eq_of_inter {α : Type u} {β : Type v}
    {G H_sub B₁ B₂ : Graph α β} (hB₁ : IsBridge G H_sub B₁) (hB₂ : IsBridge G H_sub B₂) :
    (∀ v ∈ V(B₁) ∩ V(B₂), v ∉ V(H_sub) → V(B₁) = V(B₂)) ∧
    (∀ e ∈ E(B₁) ∩ E(B₂), V(B₁) = V(B₂)) := by
  have hcomp_of_vertex : ∀ {B : Graph α β} {v : α},
      IsBridge G H_sub B → v ∈ V(B) → v ∉ V(H_sub) →
      ∃ C ∈ graphComponents (deleteVertices G V(H_sub)),
        v ∈ V(C) ∧
        V(B) = V(C) ∪ {w ∈ V(H_sub) | ∃ e ∈ E(G), ∃ x ∈ V(C), G.IsLink e x w} := by
    intro B v hB hvB hv_not_H
    rcases hB.2.2 with ⟨e, _, w₁, hw₁, w₂, hw₂, _, hVB, _⟩ | ⟨C, hC, hVB, _⟩
    · rw [hVB] at hvB
      rcases hvB with rfl | rfl
      · exact (hv_not_H hw₁).elim
      · exact (hv_not_H hw₂).elim
    · rw [hVB] at hvB
      rcases hvB with hvC | ⟨hvH, _⟩
      · exact ⟨C, hC, hvC, hVB⟩
      · exact (hv_not_H hvH).elim
  have hV_eq_of_vertex : ∀ v ∈ V(B₁) ∩ V(B₂), v ∉ V(H_sub) → V(B₁) = V(B₂) := by
    rintro v ⟨hv₁, hv₂⟩ hv_not_H
    obtain ⟨C₁, hC₁, hvC₁, hVB₁⟩ := hcomp_of_vertex hB₁ hv₁ hv_not_H
    obtain ⟨C₂, hC₂, hvC₂, hVB₂⟩ := hcomp_of_vertex hB₂ hv₂ hv_not_H
    have hC_eq : C₁ = C₂ := isGraphComponent_eq_of_mem_inter hC₁ hC₂ ⟨v, hvC₁, hvC₂⟩
    rw [hVB₁, hVB₂, hC_eq]
  refine ⟨hV_eq_of_vertex, ?_⟩
  rintro e ⟨he₁, he₂⟩
  obtain ⟨x, y, hxy₁⟩ := B₁.exists_isLink_of_mem_edgeSet he₁
  have hxy_G : G.IsLink e x y := hxy₁.mono hB₁.2.1
  have hxy₂ : B₂.IsLink e x y := (hB₂.2.1.isLink_iff he₂).mpr hxy_G
  by_cases hxH : x ∈ V(H_sub)
  · by_cases hyH : y ∈ V(H_sub)
    · have h_ends : ∀ {B : Graph α β}, IsBridge G H_sub B → e ∈ E(B) → V(B) = {x, y} := by
        intro B hB heB
        rcases hB.2.2 with ⟨e₀, _, u, _, v, _, huv, hVB, hEB⟩ | ⟨C, hC, _, hEB⟩
        · rw [hEB, mem_singleton_iff] at heB
          subst heB
          rw [hVB]
          rcases huv.eq_and_eq_or_eq_and_eq hxy_G with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rfl
          · exact Set.pair_comm u v
        · have hC_del : C ≤ deleteVertices G V(H_sub) := hC.1
          rw [hEB] at heB
          rcases heB with heC | ⟨_, u, huC, v, _, huv⟩
          · obtain ⟨u, v, huv_C⟩ := C.exists_isLink_of_mem_edgeSet heC
            have huv_G : G.IsLink e u v := huv_C.mono (hC_del.trans (deleteVertices_le G V(H_sub)))
            have hu_not_H : u ∉ V(H_sub) := (hC_del.vertexSet_mono huv_C.left_mem).2
            rcases huv_G.eq_and_eq_or_eq_and_eq hxy_G with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact (hu_not_H hxH).elim
            · exact (hu_not_H hyH).elim
          · have hu_not_H : u ∉ V(H_sub) := (hC_del.vertexSet_mono huC).2
            rcases huv.eq_and_eq_or_eq_and_eq hxy_G with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact (hu_not_H hxH).elim
            · exact (hu_not_H hyH).elim
      rw [h_ends hB₁ he₁, h_ends hB₂ he₂]
    · exact hV_eq_of_vertex y ⟨hxy₁.right_mem, hxy₂.right_mem⟩ hyH
  · exact hV_eq_of_vertex x ⟨hxy₁.left_mem, hxy₂.left_mem⟩ hxH


end GraphMinor.GM16
