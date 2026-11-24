/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Section9
public import LeanPool.GraphMinor.GM14.Section6
public import LeanPool.GraphMinor.GM14.Section10Translation4
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM09.Section3a
import LeanPool.GraphMinor.GM09.Section4b
import LeanPool.GraphMinor.GM11.OArcCircuit
import LeanPool.GraphMinor.GM11.Section81
import LeanPool.GraphMinor.GM14.Section7b
import LeanPool.GraphMinor.GM14.Section8Core
import LeanPool.GraphMinor.Surface.CircleMove
import LeanPool.GraphMinor.Surface.EdgeLens

import LeanPool.GraphMinor.GM09.Bridge

import LeanPool.GraphMinor.GM12.Section710


/-!
# Graph Minors XIV – Section 10: The Main Proof ((10.1), (4.1), and (1.1))

This file formalizes Section 10 ("The Main Proof", pages 49–50), Section 4 ((4.1), page 30), and
Section 1 ((1.1), pages 24–25) of N. Robertson and P. D. Seymour,
*Graph Minors. XIV. Extending an embedding*, J. Combin. Theory Ser. B **65** (1995) 23–50:

- `isHPathWithEnds_mono`, `spanEmbeddingMono`, `isDrawingEye_mono`: monotonicity of `H`-paths,
  span embeddings, and eyes under subgraph inclusion `G₀ ≤ G`.
- `bridge_step_10_1` and `theorem_10_1` ((10.1), pages 49–50): proved by induction on
  `|V(G)| + |E(G)|` using bridges of `H` in `G`, `(9.6)` (`theorem_9_6` with `π = 2`), `(8.1)`
  (`Theorem81Statement`), `(6.1)` (`theorem_6_1`), `(6.5)` (`theorem_6_5`), and `(7.3)`
  (`theorem_7_3`) to glue the modified arrangement `α*` inside `Δ` with `α` outside `Δ`.
- `theorem_4_1` ((4.1), page 30): the main theorem of Graph Minors XIV, proved by setting `β = 12`
  in `theorem_10_1`.
- `theorem_1_1` ((1.1), pages 24–25): the simplified special case for 4-connected graphs and
  subdivisions of simple 3-connected graphs in non-spherical surfaces without boundary of
  representativity `≥ 209`, deduced from `theorem_4_1`.
-/

@[expose] public section

namespace GraphMinor.GM14

open Set Topology Graph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10
  GraphMinor.GM11 Hypergraph

universe u v w

variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-! ## Monotonicity of `H`-Paths, Span Embeddings, and Eyes -/

omit [T2Space S] in
/-- Monotonicity of `IsHPathWithEnds` with respect to ambient graph inclusion `G₀ ≤ G`. -/
theorem isHPathWithEnds_mono {α : Type v} {β : Type w}
    {G₀ G H₀ P : Graph α β} {a b : α} (hG₀ : G₀ ≤ G)
    (hP : IsHPathWithEnds G₀ H₀ P a b) :
    IsHPathWithEnds G H₀ P a b :=
  ⟨hP.1.trans hG₀, ⟨hP.2.1.1.trans hG₀, hP.2.1.2⟩, hP.2.2⟩

/-- Extending a `SpanEmbedding H' G₀` along `G₀ ≤ G` to a `SpanEmbedding H' G`. -/
def spanEmbeddingMono {α : Type v} {β : Type w} {H' : Drawing S} {G₀ G : Graph α β}
    (hG₀ : G₀ ≤ G) (η₀ : SpanEmbedding H' G₀) : SpanEmbedding H' G where
  imageGraph := η₀.imageGraph
  vMap := η₀.vMap
  eMap := η₀.eMap
  imageGraph_le := η₀.imageGraph_le.trans hG₀
  bijOn_v := η₀.bijOn_v
  bijOn_e := η₀.bijOn_e
  inc_iff := η₀.inc_iff

omit [T2Space S] in
/-- If `r` is an eye of `H'` in `G₀ ≤ G` with respect to `T'`, then `r` is also an eye of `H'` in
`G` with respect to `T'`. -/
theorem isDrawingEye_mono {α : Type v} {β : Type w}
    {G₀ G : Graph α β} (hG₀ : G₀ ≤ G) {H' : Drawing S} (η₀ : SpanEmbedding H' G₀)
    {θ' : ℕ} {T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {r : Set S}
    (heye : IsDrawingEye G₀ H' η₀ θ' T' r) :
    IsDrawingEye G H' (spanEmbeddingMono hG₀ η₀) θ' T' r := by
  obtain ⟨hr, C, a, b, c, d, P₁, P₂, hC, hCs, hCU, ha, hb, hc, hd, hnodup, hord, hfree,
    hdisj, hP₁, hP₂⟩ := heye
  exact ⟨hr, C, a, b, c, d, P₁, P₂, hC, hCs, hCU, ha, hb, hc, hd, hnodup, hord, hfree,
    hdisj, isHPathWithEnds_mono hG₀ hP₁, isHPathWithEnds_mono hG₀ hP₂⟩

/-! ## Bridge Decomposition Lemmas -/

/-- If `C` is a connected component of `deleteVertices G V(H_sub)` and `u', v' ∈ V(H_sub)` are
distinct vertices linked in `G` by edges `e₁, e₂` to vertices `x₁, x₂ ∈ V(C)`, then there is an
`H_sub`-path `P` in `G` with ends `u'` and `v'`. -/
theorem exists_isHPathWithEnds_of_component_attachments {α : Type v} {β : Type w}
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
theorem exists_isHPathWithEnds_of_isBridge {α : Type v} {β : Type w}
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

/-- For any component `C` of `deleteVertices G V(H_sub)`, the subgraph `B` formed by `C` and its
attachment edges to `V(H_sub)` is a bridge (`IsBridge G H_sub B`). -/
private theorem isBridge_of_component {α : Type v} {β : Type w}
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
private theorem exists_bridge_of_mem_vertexSet {α : Type v} {β : Type w}
    {G H_sub : Graph α β} (hH : H_sub ≤ G) {v : α} (hvG : v ∈ V(G)) (hvH : v ∉ V(H_sub)) :
    ∃ B : Graph α β, IsBridge G H_sub B ∧ v ∈ V(B) := by
  have hv_del : v ∈ V(deleteVertices G V(H_sub)) := ⟨hvG, hvH⟩
  obtain ⟨C, hC, hvC⟩ := exists_graphComponent_of_mem hv_del
  obtain ⟨hB, hVB, _⟩ := isBridge_of_component hH hC
  exact ⟨_, hB, hVB ▸ Or.inl hvC⟩

/-- Every edge of `G` outside `E(H_sub)` belongs to a bridge of `H_sub` in `G`. -/
private theorem exists_bridge_of_mem_edgeSet {α : Type v} {β : Type w}
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

/-- Every bridge `B` of `H_sub` in `G` is edge-disjoint from `H_sub`. -/
private theorem isBridge_disjoint_edgeSet {α : Type v} {β : Type w}
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
are equal (`B₁ = B₂`). -/
private theorem isBridge_eq_of_inter {α : Type v} {β : Type w}
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
    · have h_ends : ∀ {B : Graph α β}, IsBridge G H_sub B → e ∈ E(B) →
          V(B) = {x, y} ∧ E(B) = {e} := by
        intro B hB heB
        rcases hB.2.2 with ⟨e₀, _, u, _, v, _, huv, hVB, hEB⟩ | ⟨C, hC, _, hEB⟩
        · rw [hEB, mem_singleton_iff] at heB
          subst heB
          refine ⟨?_, hEB⟩
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
      obtain ⟨hVB₁, hEB₁⟩ := h_ends hB₁ he₁
      obtain ⟨hVB₂, hEB₂⟩ := h_ends hB₂ he₂
      exact (Compatible.of_le_le hB₁.2.1 hB₂.2.1).ext (hVB₁.trans hVB₂.symm) (hEB₁.trans hEB₂.symm)
    · exact h_eq_of_vertex y ⟨hxy₁.right_mem, hxy₂.right_mem⟩ hyH
  · exact h_eq_of_vertex x ⟨hxy₁.left_mem, hxy₂.left_mem⟩ hxH

omit [T2Space S] in
/-- If `G₀ ≠ η₀.imageGraph`, there is a bridge `J` of `η₀.imageGraph` in `G₀` and a remaining
union `G' = subgraphSUnion G₀ {η₀.imageGraph, subgraphSUnion G₀ B_rem}` with strictly smaller
`|V(G')| + |E(G')| < |V(G₀)| + |E(G₀)|`. -/
private theorem exists_bridge_decomposition_of_ne {α : Type v} {β : Type w}
    {G₀ : Graph α β} {H : Drawing S} (η₀ : SpanEmbedding H G₀)
    (hV_fin : V(G₀).Finite) (hE_fin : E(G₀).Finite)
    (hne : G₀ ≠ η₀.imageGraph) :
    ∃ (J G' : Graph α β) (B_rem : Set (Graph α β)) (η' : SpanEmbedding H G'),
      IsBridge G₀ η₀.imageGraph J ∧
      (∀ B ∈ B_rem, IsBridge G₀ η₀.imageGraph B) ∧
      J ∉ B_rem ∧
      J = subgraphSUnion G₀ {J} ∧
      G' = subgraphSUnion G₀ {η₀.imageGraph, subgraphSUnion G₀ B_rem} ∧
      G' ≤ G₀ ∧
      G₀ = subgraphUnion G₀ G' J ∧
      Disjoint E(G') E(J) ∧
      V(G') ∩ V(J) ⊆ V(η₀.imageGraph) ∧
      η'.imageGraph = η₀.imageGraph ∧
      (∀ v ∈ H.V, η'.vMap v = η₀.vMap v) ∧
      (∀ e ∈ H.E, η'.eMap e = η₀.eMap e) ∧
      V(G').ncard + E(G').ncard < V(G₀).ncard + E(G₀).ncard := by
  have hex_J : ∃ J : Graph α β, IsBridge G₀ η₀.imageGraph J := by
    by_cases hV_eq : V(G₀) = V(η₀.imageGraph)
    · have hE_ne : E(G₀) ≠ E(η₀.imageGraph) := fun hE_eq =>
        hne ((Compatible.of_le_le le_rfl η₀.imageGraph_le).ext hV_eq hE_eq)
      have hE_notsub : ¬ E(G₀) ⊆ E(η₀.imageGraph) := fun hsub =>
        hE_ne (subset_antisymm hsub η₀.imageGraph_le.edgeSet_mono)
      obtain ⟨e, heG, heH⟩ := Set.not_subset.mp hE_notsub
      obtain ⟨J, hJ, _⟩ := exists_bridge_of_mem_edgeSet η₀.imageGraph_le heG heH
      exact ⟨J, hJ⟩
    · have hV_notsub : ¬ V(G₀) ⊆ V(η₀.imageGraph) := fun hsub =>
        hV_eq (subset_antisymm hsub η₀.imageGraph_le.vertexSet_mono)
      obtain ⟨v, hvG, hvH⟩ := Set.not_subset.mp hV_notsub
      obtain ⟨J, hJ, _⟩ := exists_bridge_of_mem_vertexSet η₀.imageGraph_le hvG hvH
      exact ⟨J, hJ⟩
  obtain ⟨J, hJ⟩ := hex_J
  let B_rem : Set (Graph α β) := {B : Graph α β | IsBridge G₀ η₀.imageGraph B ∧ B ≠ J}
  have hB_rem : ∀ B ∈ B_rem, IsBridge G₀ η₀.imageGraph B := fun _ hB => hB.1
  have hJ_not_rem : J ∉ B_rem := fun h => h.2 rfl
  let U_rem := subgraphSUnion G₀ B_rem
  have hU_rem_le : U_rem ≤ G₀ := subgraphSUnion_le fun _ hB => hB.1.2.1
  have hPair_le : ∀ Q ∈ ({η₀.imageGraph, U_rem} : Set (Graph α β)), Q ≤ G₀ := by
    rintro Q (rfl | rfl)
    · exact η₀.imageGraph_le
    · exact hU_rem_le
  let G' := subgraphSUnion G₀ {η₀.imageGraph, U_rem}
  have hG'_le : G' ≤ G₀ := subgraphSUnion_le hPair_le
  have hH_le_G' : η₀.imageGraph ≤ G' := le_subgraphSUnion hPair_le (Or.inl rfl)
  let η' : SpanEmbedding H G' := {
    imageGraph := η₀.imageGraph
    vMap := η₀.vMap
    eMap := η₀.eMap
    imageGraph_le := hH_le_G'
    bijOn_v := η₀.bijOn_v
    bijOn_e := η₀.bijOn_e
    inc_iff := η₀.inc_iff
  }
  have hJ_sUnion : J = subgraphSUnion G₀ {J} := by
    have h1 : ∀ Q ∈ ({J} : Set (Graph α β)), Q ≤ G₀ := by rintro Q rfl; exact hJ.2.1
    refine (Compatible.of_le_le hJ.2.1 (subgraphSUnion_le h1)).ext ?_ ?_
    · rw [vertexSet_subgraphSUnion]; simp
    · rw [edgeSet_subgraphSUnion h1]; simp
  have hVG' : V(G') = V(η₀.imageGraph) ∪ ⋃ B ∈ B_rem, V(B) := by
    change V(subgraphSUnion G₀ {η₀.imageGraph, U_rem}) = _
    rw [vertexSet_subgraphSUnion]
    ext v
    constructor
    · intro hv
      obtain ⟨Q, rfl | rfl, hvQ⟩ := mem_iUnion₂.mp hv
      · exact Or.inl hvQ
      · rw [vertexSet_subgraphSUnion] at hvQ
        exact Or.inr hvQ
    · rintro (hvH | hvU)
      · exact mem_iUnion₂.mpr ⟨η₀.imageGraph, Or.inl rfl, hvH⟩
      · refine mem_iUnion₂.mpr ⟨U_rem, Or.inr rfl, ?_⟩
        rw [vertexSet_subgraphSUnion]
        exact hvU
  have hle_from_bridge : ∀ B ∈ B_rem, B ≤ G₀ := fun _ hB => hB.1.2.1
  have hEG' : E(G') = E(η₀.imageGraph) ∪ ⋃ B ∈ B_rem, E(B) := by
    change E(subgraphSUnion G₀ {η₀.imageGraph, U_rem}) = _
    rw [edgeSet_subgraphSUnion hPair_le]
    ext e
    constructor
    · intro he
      obtain ⟨Q, rfl | rfl, heQ⟩ := mem_iUnion₂.mp he
      · exact Or.inl heQ
      · rw [edgeSet_subgraphSUnion hle_from_bridge] at heQ
        exact Or.inr heQ
    · rintro (heH | heU)
      · exact mem_iUnion₂.mpr ⟨η₀.imageGraph, Or.inl rfl, heH⟩
      · refine mem_iUnion₂.mpr ⟨U_rem, Or.inr rfl, ?_⟩
        rw [edgeSet_subgraphSUnion hle_from_bridge]
        exact heU
  have hG₀_union : G₀ = subgraphUnion G₀ G' J := by
    refine (Compatible.of_le_le le_rfl (subgraphUnion_le hG'_le hJ.2.1)).ext ?_ ?_
    · ext v
      rw [vertexSet_subgraphUnion, hVG']
      refine ⟨fun hvG => ?_, fun h => ?_⟩
      · by_cases hvH : v ∈ V(η₀.imageGraph)
        · exact Or.inl (Or.inl hvH)
        · obtain ⟨B, hB, hvB⟩ := exists_bridge_of_mem_vertexSet η₀.imageGraph_le hvG hvH
          by_cases hBJ : B = J
          · exact Or.inr (hBJ ▸ hvB)
          · exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨B, ⟨hB, hBJ⟩, hvB⟩))
      · rcases h with hG' | hJ_v
        · exact hG'_le.vertexSet_mono (hVG' ▸ hG')
        · exact hJ.2.1.vertexSet_mono hJ_v
    · ext e
      rw [edgeSet_subgraphUnion hG'_le hJ.2.1, hEG']
      refine ⟨fun heG => ?_, fun h => ?_⟩
      · by_cases heH : e ∈ E(η₀.imageGraph)
        · exact Or.inl (Or.inl heH)
        · obtain ⟨B, hB, heB⟩ := exists_bridge_of_mem_edgeSet η₀.imageGraph_le heG heH
          by_cases hBJ : B = J
          · exact Or.inr (hBJ ▸ heB)
          · exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨B, ⟨hB, hBJ⟩, heB⟩))
      · rcases h with hG' | hJ_e
        · exact hG'_le.edgeSet_mono (hEG' ▸ hG')
        · exact hJ.2.1.edgeSet_mono hJ_e
  have hDisj_E : Disjoint E(G') E(J) := by
    rw [hEG']
    refine Set.disjoint_left.mpr fun e heG' heJ => ?_
    rcases heG' with heH | heRem
    · exact Set.disjoint_left.mp (isBridge_disjoint_edgeSet hJ) heJ heH
    · obtain ⟨B, hB, heB⟩ := mem_iUnion₂.mp heRem
      exact hB.2 ((isBridge_eq_of_inter hB.1 hJ).2 e ⟨heB, heJ⟩)
  have hInter_V : V(G') ∩ V(J) ⊆ V(η₀.imageGraph) := by
    rintro v ⟨hvG', hvJ⟩
    by_contra hv_not_H
    rw [hVG'] at hvG'
    rcases hvG' with hvH | hvRem
    · exact hv_not_H hvH
    · obtain ⟨B, hB, hvB⟩ := mem_iUnion₂.mp hvRem
      exact hB.2 ((isBridge_eq_of_inter hB.1 hJ).1 v ⟨hvB, hvJ⟩ hv_not_H)
  have hcard_lt : V(G').ncard + E(G').ncard < V(G₀).ncard + E(G₀).ncard := by
    have hV_le : V(G').ncard ≤ V(G₀).ncard := ncard_le_ncard hG'_le.vertexSet_mono hV_fin
    have hE_le : E(G').ncard ≤ E(G₀).ncard := ncard_le_ncard hG'_le.edgeSet_mono hE_fin
    rcases hJ.2.2 with ⟨e₀, he₀, _, _, _, _, _, _, hEJ⟩ | ⟨C, hC, hVJ, _⟩
    · have he₀_J : e₀ ∈ E(J) := hEJ ▸ mem_singleton e₀
      have he₀_not_G' : e₀ ∉ E(G') := Set.disjoint_right.mp hDisj_E he₀_J
      have hE_ssub : E(G') ⊂ E(G₀) := ⟨hG'_le.edgeSet_mono, fun hsub => he₀_not_G' (hsub he₀.1)⟩
      have hE_lt : E(G').ncard < E(G₀).ncard := ncard_lt_ncard hE_ssub hE_fin
      omega
    · obtain ⟨v₀, hv₀C⟩ := hC.2.1.1
      have hv₀J : v₀ ∈ V(J) := hVJ ▸ Or.inl hv₀C
      have hv₀_not_H : v₀ ∉ V(η₀.imageGraph) := (hC.1.vertexSet_mono hv₀C).2
      have hv₀_not_G' : v₀ ∉ V(G') := fun hv₀G' => hv₀_not_H (hInter_V ⟨hv₀G', hv₀J⟩)
      have hv₀G₀ : v₀ ∈ V(G₀) := hJ.2.1.vertexSet_mono hv₀J
      have hV_ssub : V(G') ⊂ V(G₀) := ⟨hG'_le.vertexSet_mono, fun hsub => hv₀_not_G' (hsub hv₀G₀)⟩
      have hV_lt : V(G').ncard < V(G₀).ncard := ncard_lt_ncard hV_ssub hV_fin
      omega
  exact ⟨J, G', B_rem, η', hJ, hB_rem, hJ_not_rem, hJ_sUnion, rfl, hG'_le, hG₀_union,
    hDisj_E, hInter_V, rfl, fun _ _ => rfl, fun _ _ => rfl, hcard_lt⟩

/-! ## Converting a Crooked Transaction in `clearedSociety` to an Eye and Rigidity in `Δ` -/

omit [T2Space S] in
/-- If `Ω` is a natural order from `C.U` via `ν : α → S` and `[v₁, v₂, v₃, v₄]` is `Ω`-clockwise,
then `ν v₁, ν v₂, ν v₃, ν v₄` occur in circuit order on `C`. -/
private theorem occurInCircuitOrder_of_isClockwiseSeq {α : Type v}
    {C : Drawing S} {ν : α → S} {Ω : CyclicPerm α} {F : Set S}
    {v₁ v₂ v₃ v₄ : α}
    (hCU : C.U = F)
    (hNat : IsNaturalOrderFrom ν Ω F)
    (hcw : Ω.IsClockwiseSeq [v₁, v₂, v₃, v₄]) :
    OccurInCircuitOrder C (ν v₁) (ν v₂) (ν v₃) (ν v₄) := by
  obtain ⟨_, φ, _, hAgree3⟩ := hNat
  have hpi : 0 < 2 * Real.pi := by positivity
  let pt : ℝ → S := fun t => (φ (Circle.exp t)).1
  have hpt_eq_iff : ∀ t₁ t₂ : ℝ, pt t₁ = pt t₂ ↔ ∃ m : ℤ, t₁ = t₂ + m * (2 * Real.pi) := by
    intro t₁ t₂
    constructor
    · intro h
      have h1 : φ (Circle.exp t₁) = φ (Circle.exp t₂) := Subtype.ext h
      exact Circle.exp_eq_exp.mp (φ.injective h1)
    · rintro ⟨m, rfl⟩
      have h2 : Circle.exp (t₂ + m * (2 * Real.pi)) = Circle.exp t₂ :=
        Circle.exp_eq_exp.mpr ⟨m, rfl⟩
      simp [pt, h2]
  have hpt_inj : ∀ t₀ : ℝ, InjOn pt (Ico t₀ (t₀ + 2 * Real.pi)) := by
    intro t₀ t₁ ht₁ t₂ ht₂ h
    obtain ⟨m, rfl⟩ := (hpt_eq_iff t₁ t₂).mp h
    have hm0 : m = 0 := by
      by_contra hm
      rcases lt_or_gt_of_ne hm with hlt | hgt
      · have hm_le : (m : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hlt
        have : (m : ℝ) * (2 * Real.pi) ≤ -1 * (2 * Real.pi) :=
          mul_le_mul_of_nonneg_right hm_le hpi.le
        linarith [ht₁.1, ht₂.2]
      · have hm_ge : (1 : ℝ) ≤ m := by exact_mod_cast hgt
        have : 1 * (2 * Real.pi) ≤ (m : ℝ) * (2 * Real.pi) :=
          mul_le_mul_of_nonneg_right hm_ge hpi.le
        linarith [ht₁.2, ht₂.1]
    simp [hm0]
  have h123 : Ω.IsClockwise3 v₁ v₂ v₃ :=
    (Ω.mem_interval_of_lt hcw (by decide : 0 < 1) (by decide : 1 < 2) (by decide : 2 < 4)).2
  have h134 : Ω.IsClockwise3 v₁ v₃ v₄ :=
    (Ω.mem_interval_of_lt hcw (by decide : 0 < 2) (by decide : 2 < 3) (by decide : 3 < 4)).2
  obtain ⟨t₀, t₁, t₂, ht01, ht12, ht20, hpt0, hpt1, hpt2⟩ := hAgree3 v₁ v₂ v₃ h123
  obtain ⟨s₀, s₂, s₃, hs02, hs23, hs30, hs₀, hs₂, hs₃⟩ := hAgree3 v₁ v₃ v₄ h134
  obtain ⟨m, hm⟩ := (hpt_eq_iff t₀ s₀).mp (hpt0.trans hs₀.symm)
  let u₂ := s₂ + m * (2 * Real.pi)
  let u₃ := s₃ + m * (2 * Real.pi)
  have hu₂_pt : pt u₂ = ν v₃ := ((hpt_eq_iff u₂ s₂).mpr ⟨m, rfl⟩).trans hs₂
  have hu₃_pt : pt u₃ = ν v₄ := ((hpt_eq_iff u₃ s₃).mpr ⟨m, rfl⟩).trans hs₃
  have ht2_eq_u2 : t₂ = u₂ :=
    hpt_inj t₀ ⟨le_of_lt (ht01.trans ht12), ht20⟩ ⟨by linarith, by linarith⟩
      (hpt2.trans hu₂_pt.symm)
  have ht2_lt_u3 : t₂ < u₃ := by linarith
  have hu3_lt : u₃ < t₀ + 2 * Real.pi := by linarith
  let φ_C : Circle ≃ₜ C.U :=
    (Homeomorph.mulLeft (Circle.exp t₀)).trans (φ.trans (Homeomorph.setCongr hCU.symm))
  refine ⟨φ_C, 0, t₁ - t₀, t₂ - t₀, u₃ - t₀, le_rfl, by linarith, by linarith, by linarith,
    by linarith, ?_, ?_, ?_, ?_⟩
  · change (φ (Circle.exp t₀ * Circle.exp 0)).1 = ν v₁
    rw [← Circle.exp_add, add_zero]
    exact hpt0
  · change (φ (Circle.exp t₀ * Circle.exp (t₁ - t₀))).1 = ν v₂
    rw [← Circle.exp_add, add_sub_cancel]
    exact hpt1
  · change (φ (Circle.exp t₀ * Circle.exp (t₂ - t₀))).1 = ν v₃
    rw [← Circle.exp_add, add_sub_cancel]
    exact hpt2
  · change (φ (Circle.exp t₀ * Circle.exp (u₃ - t₀))).1 = ν v₄
    rw [← Circle.exp_add, add_sub_cancel]
    exact hu₃_pt

/-- For a closed subset `K`, the vertex set of `H.interSet K` is `H.V ∩ K`. -/
private theorem interSet_V_of_isClosed (H : Drawing S) {K : Set S} (hK : IsClosed K) :
    (H.interSet K).V = H.V ∩ K := by
  rw [Drawing.interSet, Drawing.span_V, Drawing.spanV]
  refine Subset.antisymm (union_subset inter_subset_left ?_)
    (fun x hx => Or.inl ⟨hx, hx.1⟩)
  refine iUnion₂_subset fun e he x hx => ⟨hx.2, ?_⟩
  exact hK.closure_subset_iff.mpr he.1.2 hx.1

/-- The edge set of `H.interSet K` is `{e ∈ H.E | e ⊆ K}`. -/
private theorem interSet_E (H : Drawing S) (K : Set S) :
    (H.interSet K).E = {e ∈ H.E | e ⊆ K} := by
  rw [Drawing.interSet, Drawing.span_E]
  ext e
  simp only [mem_inter_iff, mem_ofPred_eq]
  exact ⟨fun h => h.1, fun h => ⟨h, h.1⟩⟩

/-- Outcome `(iv)(a)` of `(9.6)` with `π = 2` produces an eye `IsDrawingEye` of `clearedSubdrawing H
Λ`
in `G₀` with respect to `T₁`. -/
private theorem isDrawingEye_of_crookedTransaction [ConnectedSpace S] {α : Type v} {β : Type w}
    {G₀ : Graph α β} {H : Drawing S} {d : Set S → Set S → ℕ} {θ beta : ℕ}
    {T₁ : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {z Λ : Set S} {clearedEmbedding : SpanEmbedding (clearedSubdrawing H Λ) G₀}
    {clearedSociety : Society α β} {P_set : Set (Graph α β)} {X : Set S}
    (hZone : IsLambdaZoneAround H d (3 * beta + 3) z Λ)
    (hNat : ∃ inv_v : α → S,
      (∀ x ∈ clearedSociety.Ω.bar,
        inv_v x ∈ (clearedSubdrawing H Λ).V ∩ subBd Λ ∧ clearedEmbedding.vMap (inv_v x) = x) ∧
      IsNaturalOrderFrom inv_v clearedSociety.Ω (subBd Λ))
    (hCrooked : clearedSociety.IsCrookedTransaction P_set)
    (hCard : 2 ≤ P_set.ncard)
    (hPaths : ∀ P ∈ P_set, ∀ a b : α,
      clearedSociety.IsOmegaPathWithEnds P a b →
      IsHPathWithEnds G₀ clearedEmbedding.imageGraph P a b)
    (hX_sub : X ⊆ (clearedSubdrawing H Λ).V ∩ subBd Λ)
    (hEnds : clearedSociety.transactionEnds P_set = clearedEmbedding.vMap '' X)
    (hFreeX : IsFreeSet (clearedSubdrawing H Λ).toHypergraph T₁ (θ - 4 * (3 * beta + 3) - 2) X)
    (hT₁ : IsTangle (clearedSubdrawing H Λ).toHypergraph (θ - 4 * (3 * beta + 3) - 2) T₁) :
    IsDrawingEye G₀ (clearedSubdrawing H Λ) clearedEmbedding (θ - 4 * (3 * beta + 3) - 2) T₁ Λ := by
  let H' := clearedSubdrawing H Λ
  obtain ⟨hΛR, _⟩ := clearedSubdrawing_mem_R_and_atom hZone
  obtain ⟨hV_H', hE_H'⟩ := clearedSubdrawing_V_and_E hZone
  have hbd_disj : subBd Λ ⊆ univ \ Λ := fun _ hx =>
    (isClosed_univ.sdiff hZone.isOpenDisc.1).closure_eq ▸ hx.2
  have hcl_bd : IsClosed (subBd Λ) := isClosed_closure.inter isClosed_closure
  have hInter_eq : H'.interSet (subBd Λ) = H.interSet (subBd Λ) := by
    refine Drawing.ext_VE ?_ ?_
    · rw [interSet_V_of_isClosed H' hcl_bd, interSet_V_of_isClosed H hcl_bd, hV_H']
      ext x
      simp only [mem_inter_iff, mem_sdiff]
      exact ⟨fun ⟨⟨hxV, _⟩, hxbd⟩ => ⟨hxV, hxbd⟩,
        fun ⟨hxV, hxbd⟩ => ⟨⟨hxV, (hbd_disj hxbd).2⟩, hxbd⟩⟩
    · rw [interSet_E, interSet_E, hE_H']
      ext e
      simp only [mem_ofPred_eq]
      exact ⟨fun ⟨⟨heE, _⟩, hebd⟩ => ⟨heE, hebd⟩,
        fun ⟨heE, hebd⟩ => ⟨⟨heE, hebd.trans hbd_disj⟩, hebd⟩⟩
  let C_bd := H'.interSet (subBd Λ)
  have hCirc_bd : C_bd.IsCircuit := by
    change (H'.interSet (subBd Λ)).IsCircuit
    rw [hInter_eq]
    obtain ⟨C₀, hC₀, hCH₀, hCU₀⟩ := exists_circuit_of_oArc hZone.isOArc_bd hZone.bd_subset_U
    have hEq_C : H.interSet (subBd Λ) = C₀ := by
      refine Drawing.ext_VE ?_ ?_
      · rw [interSet_V_of_isClosed H hcl_bd]
        ext x
        simp only [mem_inter_iff]
        refine ⟨fun ⟨hxV, hxbd⟩ => ?_, fun hxC => ⟨hCH₀.1 hxC, hCU₀ ▸ C₀.V_subset_U hxC⟩⟩
        by_contra hxnot
        obtain ⟨e, heC, hxe⟩ := C₀.exists_edge_of_mem (hCU₀.symm ▸ hxbd) hxnot
        exact ((hCH₀.2 heC).2.1 hxe).2 hxV
      · rw [interSet_E]
        ext e
        simp only [mem_ofPred_eq]
        refine ⟨fun ⟨heH, hebd⟩ => ?_,
          fun heC => ⟨hCH₀.2 heC, hCU₀ ▸ subset_closure.trans (C₀.closure_subset_U heC)⟩⟩
        obtain ⟨x, hxe⟩ := heH.1
        have hxnotV : x ∉ C₀.V := fun hxC => (heH.2.1 hxe).2 (hCH₀.1 hxC)
        obtain ⟨f, hfC, hxf⟩ := C₀.exists_edge_of_mem (hCU₀.symm ▸ hebd hxe) hxnotV
        have hef : e = f := arcComponent_eq heH (hCH₀.2 hfC) hxe hxf
        exact hef ▸ hfC
    exact hEq_C ▸ hC₀
  have hC_sub : C_bd.IsSubdrawing H' := H'.span_isSubdrawing _ _
  have hC_U : C_bd.U = subBd Λ := by
    have hsub : C_bd.U ⊆ subBd Λ := by
      change (H'.interSet (subBd Λ)).U ⊆ subBd Λ
      rw [(H'.interSet (subBd Λ)).U_eq, interSet_V_of_isClosed H' hcl_bd, interSet_E]
      refine union_subset inter_subset_right ?_
      exact iUnion₂_subset fun e he => hcl_bd.closure_subset_iff.mpr he.2
    exact eq_of_oArc_subset (IsCircuit.isOArc_U hCirc_bd) hZone.isOArc_bd hsub
  -- Extract a crossing pair `P₁, P₂ ∈ P_set` from `hCrooked` and `2 ≤ P_set.ncard`
  have hne_P : P_set.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨P₁, hP₁_in, P₂, hP₂_in, hP12, hCrooked12⟩ :=
     clearedSociety.exists_crooked_pair_of_nonempty hCrooked hne_P
  obtain ⟨A, B, hfence12⟩ := hCrooked12.1
  obtain ⟨a₁, ha₁A, c₁, hc₁B, hP₁_ends⟩ := hfence12.2.2 P₁ (Or.inl rfl)
  obtain ⟨b₁, hb₁A, d₁, hd₁B, hP₂_ends⟩ := hfence12.2.2 P₂ (Or.inr rfl)
  have hdisj_12 : Disjoint V(P₁) V(P₂) := hfence12.1.2 (Or.inl rfl) (Or.inr rfl) hP12
  -- Show `clearedSociety.Ω.Crosses a₁ c₁ b₁ d₁` since `P₁` is not peripheral in `{P₁, P₂}`
  have hcross : clearedSociety.Ω.Crosses a₁ c₁ b₁ d₁ := by
    by_contra hnot_cr
    have hper₁ : clearedSociety.IsPeripheralIn {P₁, P₂} P₁ := by
      by_contra hnot_per
      have hcross_path : clearedSociety.OmegaPathsCross P₁ P₂ := by
        have hEnds12_sub : clearedSociety.transactionEnds {P₁, P₂} ⊆ {a₁, c₁, b₁, d₁} := by
          rintro x ⟨Q, hQ, y, hQ_ends⟩
          rcases hQ with rfl | rfl
          · rcases hP₁_ends.ends_eq clearedSociety hQ_ends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact Or.inl rfl
            · exact Or.inr (Or.inl rfl)
          · rcases hP₂_ends.ends_eq clearedSociety hQ_ends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact Or.inr (Or.inr (Or.inl rfl))
            · exact Or.inr (Or.inr (Or.inr rfl))
        have hnot_disj1 : ¬ Disjoint (clearedSociety.Ω.interval a₁ c₁)
          (clearedSociety.transactionEnds {P₁, P₂}) :=
          fun hd => hnot_per ⟨Or.inl rfl, a₁, c₁, hP₁_ends, Or.inl hd⟩
        have hnot_disj2 : ¬ Disjoint (clearedSociety.Ω.interval c₁ a₁)
          (clearedSociety.transactionEnds {P₁, P₂}) :=
          fun hd => hnot_per ⟨Or.inl rfl, a₁, c₁, hP₁_ends, Or.inr hd⟩
        obtain ⟨u, hu_int, hu_ends⟩ := Set.not_disjoint_iff.mp hnot_disj1
        obtain ⟨v, hv_int, hv_ends⟩ := Set.not_disjoint_iff.mp hnot_disj2
        have hu_bd : u = b₁ ∨ u = d₁ := by
          rcases hEnds12_sub hu_ends with rfl | rfl | rfl | rfl
          · exact (hu_int.1.2 (Or.inl rfl)).elim
          · exact (hu_int.1.2 (Or.inr rfl)).elim
          · exact Or.inl rfl
          · exact Or.inr rfl
        have hv_bd : v = b₁ ∨ v = d₁ := by
          rcases hEnds12_sub hv_ends with rfl | rfl | rfl | rfl
          · exact (hv_int.1.2 (Or.inr rfl)).elim
          · exact (hv_int.1.2 (Or.inl rfl)).elim
          · exact Or.inl rfl
          · exact Or.inr rfl
        have hdisj_int : Disjoint (clearedSociety.Ω.interval a₁ c₁) (clearedSociety.Ω.interval c₁
          a₁) :=
          clearedSociety.Ω.disjoint_interval_swap a₁ c₁
        have huv_ne : u ≠ v := fun h => Set.disjoint_left.mp hdisj_int hu_int (h ▸ hv_int)
        have hcr' : clearedSociety.Ω.Crosses a₁ c₁ b₁ d₁ := by
          rw [clearedSociety.Ω.crosses_iff_interval]
          rcases hu_bd with rfl | rfl <;> rcases hv_bd with rfl | rfl
          · exact (huv_ne rfl).elim
          · exact Or.inl ⟨hu_int, hv_int⟩
          · exact Or.inr ⟨hu_int, hv_int⟩
          · exact (huv_ne rfl).elim
        exact ⟨hdisj_12, a₁, c₁, b₁, d₁, hP₁_ends, hP₂_ends, hcr'⟩
      rcases hcross_path with ⟨_, x₁, y₁, x₂, y₂, hx₁y₁, hx₂y₂, hcr_xy⟩
      rcases hP₁_ends.ends_eq clearedSociety hx₁y₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        rcases hP₂_ends.ends_eq clearedSociety hx₂y₂ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hnot_cr hcr_xy
      · exact hnot_cr hcr_xy.swap_right
      · exact hnot_cr hcr_xy.swap_left
      · exact hnot_cr hcr_xy.swap_left.swap_right
    exact hCrooked12.2 P₁ (Or.inl rfl) hper₁
  -- Map `a₁, b₁, c₁, d₁` via `inv_v`
  obtain ⟨inv_v, hinv_v, hNat_Ω⟩ := hNat
  have hinv_mem_X : ∀ x ∈ clearedSociety.transactionEnds P_set,
      inv_v x ∈ X ∧ clearedEmbedding.vMap (inv_v x) = x ∧ inv_v x ∈ C_bd.V := by
    intro x hx
    have hx_img : x ∈ clearedEmbedding.vMap '' X := hEnds ▸ hx
    obtain ⟨y, hyX, hyx⟩ := hx_img
    rcases hx with ⟨Q, hQ, z, hPath⟩
    obtain ⟨hinv_mem, hinv_eq⟩ := hinv_v x hPath.2.2.1
    have hy_eq : inv_v x = y :=
      clearedEmbedding.bijOn_v.injOn hinv_mem.1 (hX_sub hyX).1 (hinv_eq.trans hyx.symm)
    have hCV : inv_v x ∈ C_bd.V := by
      change inv_v x ∈ (H'.interSet (subBd Λ)).V
      rw [interSet_V_of_isClosed H' hcl_bd]
      exact hinv_mem
    exact ⟨hy_eq ▸ hyX, hinv_eq, hCV⟩
  have ha₁_ends : a₁ ∈ clearedSociety.transactionEnds P_set :=
    hP₁_ends.mem_transactionEnds_left clearedSociety hP₁_in
  have hc₁_ends : c₁ ∈ clearedSociety.transactionEnds P_set :=
    hP₁_ends.mem_transactionEnds_right clearedSociety hP₁_in
  have hb₁_ends : b₁ ∈ clearedSociety.transactionEnds P_set :=
    hP₂_ends.mem_transactionEnds_left clearedSociety hP₂_in
  have hd₁_ends : d₁ ∈ clearedSociety.transactionEnds P_set :=
    hP₂_ends.mem_transactionEnds_right clearedSociety hP₂_in
  have hP₁_H : IsHPathWithEnds G₀ clearedEmbedding.imageGraph P₁ a₁ c₁
    := hPaths P₁ hP₁_in a₁ c₁ hP₁_ends
  have hP₂_H : IsHPathWithEnds G₀ clearedEmbedding.imageGraph P₂ b₁ d₁
    := hPaths P₂ hP₂_in b₁ d₁ hP₂_ends
  have hinv_inj : ∀ x ∈ clearedSociety.Ω.bar, ∀ y ∈ clearedSociety.Ω.bar, inv_v x = inv_v y → x = y
    := by
    intro x hx y hy hxy
    rw [← (hinv_v x hx).2, ← (hinv_v y hy).2, hxy]
  rcases hcross with hcw1 | hcw2
  · let a := inv_v a₁
    let b := inv_v b₁
    let c := inv_v c₁
    let d_v := inv_v d₁
    have hnodup : ([a, b, c, d_v]).Nodup := by
      change ([a₁, b₁, c₁, d₁].map inv_v).Nodup
      refine hcw1.1.map_on ?_
      intro x hx y hy hxy
      exact hinv_inj x (hcw1.2.1 x hx) y (hcw1.2.1 y hy) hxy
    have hord : OccurInCircuitOrder C_bd a b c d_v :=
      occurInCircuitOrder_of_isClockwiseSeq hC_U hNat_Ω hcw1
    have hfree : IsFreeSet H'.toHypergraph T₁ (θ - 4 * (3 * beta + 3) - 2) {a, b, c, d_v} := by
      refine freeSet_subset hT₁ hFreeX ?_
      rintro x (rfl | rfl | rfl | rfl)
      · exact (hinv_mem_X a₁ ha₁_ends).1
      · exact (hinv_mem_X b₁ hb₁_ends).1
      · exact (hinv_mem_X c₁ hc₁_ends).1
      · exact (hinv_mem_X d₁ hd₁_ends).1
    refine ⟨hΛR, C_bd, a, b, c, d_v, P₁, P₂, hCirc_bd, hC_sub, hC_U,
      (hinv_mem_X a₁ ha₁_ends).2.2, (hinv_mem_X b₁ hb₁_ends).2.2,
      (hinv_mem_X c₁ hc₁_ends).2.2, (hinv_mem_X d₁ hd₁_ends).2.2,
      hnodup, hord, hfree, hdisj_12, ?_, ?_⟩
    · rwa [(hinv_mem_X a₁ ha₁_ends).2.1, (hinv_mem_X c₁ hc₁_ends).2.1]
    · rwa [(hinv_mem_X b₁ hb₁_ends).2.1, (hinv_mem_X d₁ hd₁_ends).2.1]
  · let a := inv_v d₁
    let b := inv_v c₁
    let c := inv_v b₁
    let d_v := inv_v a₁
    have hnodup : ([a, b, c, d_v]).Nodup := by
      change ([d₁, c₁, b₁, a₁].map inv_v).Nodup
      refine hcw2.1.map_on ?_
      intro x hx y hy hxy
      exact hinv_inj x (hcw2.2.1 x hx) y (hcw2.2.1 y hy) hxy
    have hord : OccurInCircuitOrder C_bd a b c d_v :=
      occurInCircuitOrder_of_isClockwiseSeq hC_U hNat_Ω hcw2
    have hfree : IsFreeSet H'.toHypergraph T₁ (θ - 4 * (3 * beta + 3) - 2) {a, b, c, d_v} := by
      refine freeSet_subset hT₁ hFreeX ?_
      rintro x (rfl | rfl | rfl | rfl)
      · exact (hinv_mem_X d₁ hd₁_ends).1
      · exact (hinv_mem_X c₁ hc₁_ends).1
      · exact (hinv_mem_X b₁ hb₁_ends).1
      · exact (hinv_mem_X a₁ ha₁_ends).1
    have hP₂_symm : IsHPathWithEnds G₀ clearedEmbedding.imageGraph P₂ d₁ b₁ :=
      ⟨hP₂_H.1, hP₂_H.2.1.symm, hP₂_H.2.2.1.symm, hP₂_H.2.2.2.2.1, hP₂_H.2.2.2.1,
        Set.pair_comm b₁ d₁ ▸ hP₂_H.2.2.2.2.2.1, hP₂_H.2.2.2.2.2.2⟩
    have hP₁_symm : IsHPathWithEnds G₀ clearedEmbedding.imageGraph P₁ c₁ a₁ :=
      ⟨hP₁_H.1, hP₁_H.2.1.symm, hP₁_H.2.2.1.symm, hP₁_H.2.2.2.2.1, hP₁_H.2.2.2.1,
        Set.pair_comm a₁ c₁ ▸ hP₁_H.2.2.2.2.2.1, hP₁_H.2.2.2.2.2.2⟩
    refine ⟨hΛR, C_bd, a, b, c, d_v, P₂, P₁, hCirc_bd, hC_sub, hC_U,
      (hinv_mem_X d₁ hd₁_ends).2.2, (hinv_mem_X c₁ hc₁_ends).2.2,
      (hinv_mem_X b₁ hb₁_ends).2.2, (hinv_mem_X a₁ ha₁_ends).2.2,
      hnodup, hord, hfree, hdisj_12.symm, ?_, ?_⟩
    · rwa [(hinv_mem_X d₁ hd₁_ends).2.1, (hinv_mem_X b₁ hb₁_ends).2.1]
    · rwa [(hinv_mem_X c₁ hc₁_ends).2.1, (hinv_mem_X a₁ ha₁_ends).2.1]

/-- By `(6.1)` (`theorem_6_1_proof`), when `Δ` is an `α`-normal closed disc and `H ∩ closure (Σ \
Δ)`
contains a circuit `C_out`, `H ∩ Δ` is rigid in `Δ` (`IsRigidIn (H.interSet Δ) Δ`). -/
private theorem isRigidIn_of_normal_closedDisc {α : Type v} {β : Type w}
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {G' : Graph α β} {H : Drawing S} {η' : SpanEmbedding H G'}
    {S_seg : Set (Society α β)} {α_disc : Society α β → Set S} {α_pt : α → S}
    {Δ : Set S}
    (hRig : IsRigid H)
    (hSeg : IsThreeSegregation G' S_seg)
    (hArr : IsSurfaceArrangement S_seg α_disc α_pt)
    (hComp : IsCompatibleWith G' H η' S_seg α_disc α_pt)
    (hΔ_disc : IsClosedDisc Δ)
    (hNorm : IsArrangementNormal S_seg α_disc α_pt (subBd Δ))
    (hCout : ∃ C_out : Drawing S,
      C_out.IsCircuit ∧ C_out.IsSubdrawing (H.interSet (closure (univ \ Δ)))) :
    IsRigidIn (H.interSet Δ) Δ := by
  have : ConnectedSpace S := hConn
  have hbd_HV : subBd Δ ∩ H.U ⊆ H.V := by
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
    have hx_bar : x ∈ α_pt '' S₀.Ω.bar := hNorm S₀ hS₀ ⟨hxbd, he_disc hxe⟩
    obtain ⟨y, hy_bar, rfl⟩ := hx_bar
    have hx_bd_S₀ : α_pt y ∈ H.U ∩ subBd (α_disc S₀) :=
      ⟨hxU, (hArr.isClosedDisc S₀ hS₀).2 y hy_bar⟩
    rw [hComp.bd_inter_eq S₀ hS₀] at hx_bd_S₀
    exact hxnotV hx_bd_S₀.1
  refine theorem_6_1_proof hRig hΔ_disc.isClosed hbd_HV
    (fun D hD hD_bd hD_not => subsurf_closedDisc hS hΔ_disc hD hD_bd hD_not) ?_
  intro Δ' hΔ' hΔ'_inter hΔ'_bd
  have hbd_eq : subBd Δ' = subBd Δ :=
    eq_of_oArc_subset (IsClosedDisc.subBd_eq_discBd hS hΔ' ▸ hΔ'.isOArc_discBd)
      (IsClosedDisc.subBd_eq_discBd hS hΔ_disc ▸ hΔ_disc.isOArc_discBd) hΔ'_bd
  have hdiscBd_eq : discBd Δ' = discBd Δ := by
    rw [← IsClosedDisc.subBd_eq_discBd hS hΔ', ← IsClosedDisc.subBd_eq_discBd hS hΔ_disc, hbd_eq]
  have hne_Δ' : Δ' ≠ Δ := by
    intro hEq
    subst hEq
    rw [Set.inter_self] at hΔ'_inter
    obtain ⟨hOD, _, _⟩ := IsClosedDisc.isOpenDisc_diff_subBd hS hΔ_disc
    obtain ⟨φ⟩ := hOD.2
    have h0 : (0 : EuclideanPlane) ∈ OpenUnitDisc := by simp [OpenUnitDisc]
    let p₀ : S := (φ ⟨0, h0⟩).1
    have hp_in : p₀ ∈ Δ' := (φ ⟨0, h0⟩).2.1
    have hp_not : p₀ ∉ subBd Δ' := (φ ⟨0, h0⟩).2.2
    rw [hΔ'_inter] at hp_in
    exact hp_not hp_in
  have hcov : Δ' ∪ Δ = univ := cover_of_discBd_eq hS hΔ' hΔ_disc hdiscBd_eq hne_Δ'
  have hcompl_sub : univ \ Δ ⊆ Δ' := fun x ⟨hxU, hxnot⟩ => (hcov.symm ▸ hxU).resolve_right hxnot
  have hcl_sub : closure (univ \ Δ) ⊆ Δ' := hΔ'.isClosed.closure_subset_iff.mpr hcompl_sub
  obtain ⟨C_out, hCout_cir, hCout_sub⟩ := hCout
  refine ⟨C_out, hCout_cir, hCout_sub.trans (H.span_isSubdrawing _ _), hCout_sub.U_subset.trans ?_⟩
  rw [(H.interSet (closure (univ \ Δ))).U_eq, interSet_V_of_isClosed H isClosed_closure, interSet_E]
  exact (union_subset inter_subset_right
    (iUnion₂_subset fun e he => isClosed_closure.closure_subset_iff.mpr he.2)).trans hcl_sub

/-! ## Base Case and Vertex-Disjoint Bridge Case for (10.1) (pages 49–50) -/

private theorem disjoint_bridge_piece_preserves_three_segregation
    {S : Type u}
    [TopologicalSpace S]
    {α : Type v}
    {β : Type w}
    {G₀ : Graph α β}
    {G' : Graph α β}
    {J : Graph α β}
    {H : Drawing S}
    {η₀ : SpanEmbedding H G₀}
    {S_seg : Set (Society α β)}
    (hJ : IsBridge G₀ η₀.imageGraph J)
    (hG'_le : G' ≤ G₀)
    (hG₀_eq : G₀ = subgraphUnion G₀ G' J)
    (hSeg : IsThreeSegregation G' S_seg)
    (A₀ : Society α β)
    (G_A : Graph α β)
    (hV_GA : V(G_A) = V(A₀.G) ∪ V(J))
    (hE_GA : E(G_A) = E(A₀.G) ∪ E(J))
    (A₀' : Society α β)
    (hA₀G : A₀'.G = G_A)
    (f : Society α β → Society α β)
    (hf_mem : ∀ S₀ ∈ (insert A₀' (S_seg \ {A₀})), f S₀ ∈ S_seg)
    (hf_inj : InjOn f (insert A₀' (S_seg \ {A₀})))
    (hf_surj : SurjOn f (insert A₀' (S_seg \ {A₀})) S_seg)
    (hf_Ω : ∀ S₀ ∈ (insert A₀' (S_seg \ {A₀})), (f S₀).Ω = S₀.Ω)
    (hf_V : ∀ S₀ ∈ (insert A₀' (S_seg \ {A₀})), V(S₀.G) ∩ V(G') = V((f S₀).G))
    (hf_E : ∀ S₀ ∈ (insert A₀' (S_seg \ {A₀})), E(S₀.G) ∩ E(G') = E((f S₀).G))
    (hS_seg_G_le : ∀ S₀ ∈ (insert A₀' (S_seg \ {A₀})), S₀.G ≤ G₀)
    (hS_seg_G_le_img : ∀ Q ∈ (fun S₀ => S₀.G) '' (insert A₀' (S_seg \ {A₀})), Q ≤ G₀)
    (hS_seg_le_img : ∀ Q ∈ (fun S₀ => S₀.G) '' S_seg, Q ≤ G') :
    IsThreeSegregation G₀ (insert A₀' (S_seg \ {A₀})) := by
  let S_seg_G := insert A₀' (S_seg \ {A₀})
  refine ⟨⟨(hSeg.1.finite.subset sdiff_subset).insert A₀', hS_seg_G_le, ?_, ?_, ?_⟩,
    fun S₀ hS₀ => hf_Ω S₀ hS₀ ▸ hSeg.2 (f S₀) (hf_mem S₀ hS₀)⟩
  · have hV_G₀ : V(G₀) = V(G') ∪ V(J) :=
      (congrArg Graph.vertexSet hG₀_eq).trans (vertexSet_subgraphUnion G₀ G' J)
    have hE_G₀ : E(G₀) = E(G') ∪ E(J) :=
      (congrArg Graph.edgeSet hG₀_eq).trans (edgeSet_subgraphUnion hG'_le hJ.2.1)
    refine (Compatible.of_le_le (subgraphSUnion_le hS_seg_G_le_img) le_rfl).ext ?_ ?_
    · rw [vertexSet_subgraphSUnion]
      ext x
      simp only [mem_iUnion, mem_image, exists_prop]
      refine ⟨fun ⟨_, ⟨S₀, hS₀, rfl⟩, hx⟩ => (hS_seg_G_le S₀ hS₀).vertexSet_mono hx,
        fun hxG₀ => ?_⟩
      rcases hV_G₀ ▸ hxG₀ with hxG' | hxJ
      · have hx_u : x ∈ V(subgraphSUnion G' ((fun S₀ : Society α β => S₀.G) '' S_seg)) :=
          hSeg.1.union_eq.symm ▸ hxG'
        rw [vertexSet_subgraphSUnion] at hx_u
        simp only [mem_iUnion, mem_image, exists_prop] at hx_u
        obtain ⟨_, ⟨S₀, hS₀, rfl⟩, hxS₀⟩ := hx_u
        obtain ⟨S₁, hS₁, hEq⟩ := hf_surj hS₀
        exact ⟨S₁.G, ⟨S₁, hS₁, rfl⟩, ((hf_V S₁ hS₁).symm ▸ hEq ▸ hxS₀).1⟩
      · exact ⟨A₀'.G, ⟨A₀', Or.inl rfl, rfl⟩, hA₀G.symm ▸ hV_GA ▸ Or.inr hxJ⟩
    · rw [edgeSet_subgraphSUnion hS_seg_G_le_img]
      ext e
      simp only [mem_iUnion, mem_image, exists_prop]
      refine ⟨fun ⟨_, ⟨S₀, hS₀, rfl⟩, he⟩ => (hS_seg_G_le S₀ hS₀).edgeSet_mono he,
        fun heG₀ => ?_⟩
      rcases hE_G₀ ▸ heG₀ with heG' | heJ
      · have he_u : e ∈ E(subgraphSUnion G' ((fun S₀ : Society α β => S₀.G) '' S_seg)) :=
          hSeg.1.union_eq.symm ▸ heG'
        rw [edgeSet_subgraphSUnion hS_seg_le_img] at he_u
        simp only [mem_iUnion, mem_image, exists_prop] at he_u
        obtain ⟨_, ⟨S₀, hS₀, rfl⟩, heS₀⟩ := he_u
        obtain ⟨S₁, hS₁, hEq⟩ := hf_surj hS₀
        exact ⟨S₁.G, ⟨S₁, hS₁, rfl⟩, ((hf_E S₁ hS₁).symm ▸ hEq ▸ heS₀).1⟩
      · exact ⟨A₀'.G, ⟨A₀', Or.inl rfl, rfl⟩, hA₀G.symm ▸ hE_GA ▸ Or.inr heJ⟩
  · intro S₁ hS₁ S₂ hS₂ hne
    have hf_ne : f S₁ ≠ f S₂ := fun h => hne (hf_inj hS₁ hS₂ h)
    have hsub : V(S₁.G) ∩ V(S₂.G) ⊆ V((f S₁).G) ∩ V((f S₂).G) := by
      rw [← hf_V S₁ hS₁, ← hf_V S₂ hS₂]
      rcases hS₁ with rfl | ⟨hS₁_in, _⟩ <;> rcases hS₂ with rfl | ⟨hS₂_in, _⟩
      · exact (hne rfl).elim
      · intro x ⟨hx₁, hx₂⟩
        have hxG' : x ∈ V(G') := (hSeg.1.le S₂ hS₂_in).vertexSet_mono hx₂
        exact ⟨⟨hx₁, hxG'⟩, ⟨hx₂, hxG'⟩⟩
      · intro x ⟨hx₁, hx₂⟩
        have hxG' : x ∈ V(G') := (hSeg.1.le S₁ hS₁_in).vertexSet_mono hx₁
        exact ⟨⟨hx₁, hxG'⟩, ⟨hx₂, hxG'⟩⟩
      · intro x ⟨hx₁, hx₂⟩
        exact ⟨⟨hx₁, (hSeg.1.le S₁ hS₁_in).vertexSet_mono hx₁⟩,
          ⟨hx₂, (hSeg.1.le S₂ hS₂_in).vertexSet_mono hx₂⟩⟩
    rw [← hf_Ω S₁ hS₁, ← hf_Ω S₂ hS₂]
    exact hsub.trans (hSeg.1.vertex_inter_subset (f S₁) (hf_mem S₁ hS₁) (f S₂)
      (hf_mem S₂ hS₂) hf_ne)
  · intro S₁ hS₁ S₂ hS₂ hne
    have hf_ne : f S₁ ≠ f S₂ := fun h => hne (hf_inj hS₁ hS₂ h)
    have hdisj := hSeg.1.edge_disjoint (f S₁) (hf_mem S₁ hS₁) (f S₂) (hf_mem S₂ hS₂) hf_ne
    rw [← hf_E S₁ hS₁, ← hf_E S₂ hS₂] at hdisj
    refine Set.disjoint_left.mpr fun e he₁ he₂ => ?_
    rcases hS₁ with rfl | ⟨hS₁_in, _⟩ <;> rcases hS₂ with rfl | ⟨hS₂_in, _⟩
    · exact hne rfl
    · have heG' : e ∈ E(G') := (hSeg.1.le S₂ hS₂_in).edgeSet_mono he₂
      exact Set.disjoint_left.mp hdisj ⟨he₁, heG'⟩ ⟨he₂, heG'⟩
    · have heG' : e ∈ E(G') := (hSeg.1.le S₁ hS₁_in).edgeSet_mono he₁
      exact Set.disjoint_left.mp hdisj ⟨he₁, heG'⟩ ⟨he₂, heG'⟩
    · exact Set.disjoint_left.mp hdisj
        ⟨he₁, (hSeg.1.le S₁ hS₁_in).edgeSet_mono he₁⟩
        ⟨he₂, (hSeg.1.le S₂ hS₂_in).edgeSet_mono he₂⟩

private theorem disjoint_bridge_piece_preserves_tangle_locality
    {S : Type u}
    [TopologicalSpace S]
    {α : Type v}
    {β : Type w}
    {G₀ : Graph α β}
    {G' : Graph α β}
    {H : Drawing S}
    {η₀ : SpanEmbedding H G₀}
    {η' : SpanEmbedding H G'}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {S_seg : Set (Society α β)}
    (hG'_le : G' ≤ G₀)
    (hη'_v : ∀ v ∈ H.V, η'.vMap v = η₀.vMap v)
    (hη'_e : ∀ e ∈ H.E, η'.eMap e = η₀.eMap e)
    (hSeg : IsThreeSegregation G' S_seg)
    (hLoc : IsTangleLocal G' H η' T S_seg)
    (S_seg_G : Set (Society α β))
    (f : Society α β → Society α β)
    (hf_mem : ∀ S₀ ∈ S_seg_G, f S₀ ∈ S_seg)
    (hf_Ω : ∀ S₀ ∈ S_seg_G, (f S₀).Ω = S₀.Ω)
    (hf_V : ∀ S₀ ∈ S_seg_G, V(S₀.G) ∩ V(G') = V((f S₀).G))
    (hf_E : ∀ S₀ ∈ S_seg_G, E(S₀.G) ∩ E(G') = E((f S₀).G)) :
    IsTangleLocal G₀ H η₀ T S_seg_G := by
  intro S₀ hS₀ B hsepB hVB_eq
  let B' : Graph α β := (G'.induce (V(B) ∩ V(G'))).restrict E(B)
  have hV_B' : V(B') = V(B) ∩ V(G') := by simp [B']
  have hE_B' : E(B') = E(B) ∩ E(G') := by
    ext e
    simp only [B', edgeSet_restrict, edgeSet_induce, mem_inter_iff]
    refine ⟨fun ⟨⟨u_e, v_e, hlink, _, _⟩, heB⟩ => ⟨heB, hlink.edge_mem⟩, fun ⟨heB, heG'⟩ => ?_⟩
    obtain ⟨u_e, v_e, hlink⟩ := G'.exists_isLink_of_mem_edgeSet heG'
    have hlink_B : B.IsLink e u_e v_e :=
      (hsepB.2.1.isLink_iff heB).mpr (hlink.mono hG'_le)
    exact ⟨⟨u_e, v_e, hlink, ⟨hlink_B.left_mem, hlink.left_mem⟩,
      ⟨hlink_B.right_mem, hlink.right_mem⟩⟩, heB⟩
  have hB'_le : B' ≤ G' := restrict_le.trans (G'.induce_le inter_subset_right)
  have hfS₀_le : (f S₀).G ≤ G' := hSeg.1.le (f S₀) (hf_mem S₀ hS₀)
  have hsepB' : IsGraphSeparation G' (f S₀).G B' := by
    refine ⟨hfS₀_le, hB'_le, ?_, ?_, ?_⟩
    · rw [← hf_V S₀ hS₀, hV_B', ← union_inter_distrib_right, hsepB.2.2.1]
      exact inter_eq_right.mpr hG'_le.vertexSet_mono
    · rw [← hf_E S₀ hS₀, hE_B', ← union_inter_distrib_right, hsepB.2.2.2.1]
      exact inter_eq_right.mpr hG'_le.edgeSet_mono
    · rw [← hf_E S₀ hS₀, hE_B']
      exact hsepB.2.2.2.2.mono inter_subset_left inter_subset_left
  have hVB'_eq : V((f S₀).G) ∩ V(B') = (f S₀).Ω.bar := by
    rw [← hf_V S₀ hS₀, hV_B', hf_Ω S₀ hS₀]
    ext x
    simp only [mem_inter_iff]
    refine ⟨fun ⟨⟨hxS, _⟩, ⟨hxB, _⟩⟩ => hVB_eq ▸ ⟨hxS, hxB⟩, fun hxbar => ?_⟩
    have hxG' : x ∈ V(G') :=
      hfS₀_le.vertexSet_mono ((f S₀).bar_subset (hf_Ω S₀ hS₀ ▸ hxbar))
    have hx_inter : x ∈ V(S₀.G) ∩ V(B) := hVB_eq.symm ▸ hxbar
    exact ⟨⟨hx_inter.1, hxG'⟩, ⟨hx_inter.2, hxG'⟩⟩
  obtain ⟨A_H, B_H, hsep_H, hAH_V, hBH_V, hAH_E, hBH_E, hT_mem⟩ :=
    hLoc (f S₀) (hf_mem S₀ hS₀) B' hsepB' hVB'_eq
  refine ⟨A_H, B_H, hsep_H, ?_, ?_, ?_, ?_, hT_mem⟩
  · rw [hAH_V, ← hf_V S₀ hS₀]
    ext v
    simp only [mem_sep_iff, mem_inter_iff]
    exact ⟨fun ⟨hv, hvS, _⟩ => ⟨hv, hη'_v v hv ▸ hvS⟩,
      fun ⟨hv, hvS⟩ => ⟨hv, (hη'_v v hv).symm ▸ hvS,
        η'.imageGraph_le.vertexSet_mono (η'.bijOn_v.mapsTo hv)⟩⟩
  · rw [hBH_V, hV_B']
    ext v
    simp only [mem_sep_iff, mem_inter_iff]
    exact ⟨fun ⟨hv, hvB, _⟩ => ⟨hv, hη'_v v hv ▸ hvB⟩,
      fun ⟨hv, hvB⟩ => ⟨hv, (hη'_v v hv).symm ▸ hvB,
        η'.imageGraph_le.vertexSet_mono (η'.bijOn_v.mapsTo hv)⟩⟩
  · rw [hAH_E, ← hf_E S₀ hS₀]
    ext e
    simp only [mem_sep_iff, mem_inter_iff]
    exact ⟨fun ⟨he, heS, _⟩ => ⟨he, hη'_e e he ▸ heS⟩,
      fun ⟨he, heS⟩ => ⟨he, (hη'_e e he).symm ▸ heS,
        η'.imageGraph_le.edgeSet_mono (η'.bijOn_e.mapsTo he)⟩⟩
  · rw [hBH_E, hE_B']
    ext e
    simp only [mem_sep_iff, mem_inter_iff]
    exact ⟨fun ⟨he, heB, _⟩ => ⟨he, hη'_e e he ▸ heB⟩,
      fun ⟨he, heB⟩ => ⟨he, (hη'_e e he).symm ▸ heB,
        η'.imageGraph_le.edgeSet_mono (η'.bijOn_e.mapsTo he)⟩⟩

/-- Vertex-disjoint bridge case in the proof of (10.1) (page 49): when `J` is a bridge of `η₀(H)` in
`G₀` with `V(H ∩ J) = ∅`, replacing some `(A₀, Ω₀) ∈ S_seg` by `(A₀ ∪ J, Ω₀)` extends a `T`-local
3-segregation of `G'` and compatible arrangement to `G₀`. -/
private theorem disjoint_bridge_step_10_1 {α : Type v} {β : Type w}
    {G₀ G' J : Graph α β} {H : Drawing S} {η₀ : SpanEmbedding H G₀} {η' : SpanEmbedding H G'}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {θ : ℕ}
    {S_seg : Set (Society α β)} {α_disc : Society α β → Set S} {α_pt : α → S}
    (hV_fin : V(G₀).Finite) (hE_fin : E(G₀).Finite)
    (hMetric : HasTangleMetric H θ T d) (hθ : 17 ≤ θ)
    (hJ : IsBridge G₀ η₀.imageGraph J)
    (hG'_le : G' ≤ G₀)
    (hG₀_eq : G₀ = subgraphUnion G₀ G' J)
    (hDisj_E : Disjoint E(G') E(J))
    (hInter_V : V(G') ∩ V(J) ⊆ V(η₀.imageGraph))
    (hVJ_empty : ∀ v ∈ H.V, η₀.vMap v ∉ V(J))
    (hη'_v : ∀ v ∈ H.V, η'.vMap v = η₀.vMap v)
    (hη'_e : ∀ e ∈ H.E, η'.eMap e = η₀.eMap e)
    (hSeg : IsThreeSegregation G' S_seg)
    (hLoc : IsTangleLocal G' H η' T S_seg)
    (hArr : IsSurfaceArrangement S_seg α_disc α_pt)
    (hComp : IsCompatibleWith G' H η' S_seg α_disc α_pt) :
    ∃ (S_seg_G : Set (Society α β)) (α_disc_G : Society α β → Set S) (α_pt_G : α → S),
      IsThreeSegregation G₀ S_seg_G ∧ IsTangleLocal G₀ H η₀ T S_seg_G ∧
      IsSurfaceArrangement S_seg_G α_disc_G α_pt_G ∧
      IsCompatibleWith G₀ H η₀ S_seg_G α_disc_G α_pt_G := by
  classical
  have hDisj_V : Disjoint V(G') V(J) := by
    refine Set.disjoint_left.mpr fun x hxG' hxJ => ?_
    obtain ⟨v, hvH, rfl⟩ := η₀.bijOn_v.surjOn (hInter_V ⟨hxG', hxJ⟩)
    exact hVJ_empty v hvH hxJ
  have hVJ_ne : V(J).Nonempty := by
    rcases hJ.2.2 with ⟨e, _, u, huH, v, _, _, hVJ, _⟩ | ⟨C, hC_comp, hVJ, _⟩
    · obtain ⟨w, hwH, rfl⟩ := η₀.bijOn_v.surjOn huH
      exact (hVJ_empty w hwH (hVJ ▸ Or.inl rfl)).elim
    · obtain ⟨x, hxC⟩ := hC_comp.2.1.1
      exact ⟨x, hVJ ▸ Or.inl hxC⟩
  have hHE_ne : H.E.Nonempty := edgeSet_nonempty_of_isTangle hMetric.1.2.1 (by omega)
  obtain ⟨e₀, he₀H⟩ := hHE_ne
  have he₀_G' : η'.eMap e₀ ∈ E(G') := η'.imageGraph_le.edgeSet_mono (η'.bijOn_e.mapsTo he₀H)
  have he₀_union : η'.eMap e₀ ∈ E(subgraphSUnion G' ((fun S₀ : Society α β => S₀.G) '' S_seg)) :=
    hSeg.1.union_eq.symm ▸ he₀_G'
  simp only [subgraphSUnion, edgeSet_restrict, mem_inter_iff, mem_iUnion, mem_image,
    exists_prop] at he₀_union
  obtain ⟨_, ⟨A₀, hA₀_in, rfl⟩, _⟩ := he₀_union.2
  have hA₀_le_G₀ : A₀.G ≤ G₀ := (hSeg.1.le A₀ hA₀_in).trans hG'_le
  let G_A : Graph α β := subgraphUnion G₀ A₀.G J
  have hG_A_le : G_A ≤ G₀ := subgraphUnion_le hA₀_le_G₀ hJ.2.1
  have hV_GA : V(G_A) = V(A₀.G) ∪ V(J) := vertexSet_subgraphUnion G₀ A₀.G J
  have hE_GA : E(G_A) = E(A₀.G) ∪ E(J) := edgeSet_subgraphUnion hA₀_le_G₀ hJ.2.1
  have hbar_GA : A₀.Ω.bar ⊆ V(G_A) :=
    A₀.bar_subset.trans (hV_GA ▸ subset_union_left)
  let A₀' : Society α β :=
    ⟨G_A, A₀.Ω, hV_fin.subset hG_A_le.vertexSet_mono, hE_fin.subset hG_A_le.edgeSet_mono, hbar_GA⟩
  have hA₀'_not_in : A₀' ∉ S_seg := by
    intro h_in
    obtain ⟨x, hxJ⟩ := hVJ_ne
    have hxG' : x ∈ V(G') :=
      (hSeg.1.le A₀' h_in).vertexSet_mono (hV_GA ▸ Or.inr hxJ)
    exact Set.disjoint_left.mp hDisj_V hxG' hxJ
  let S_seg_G : Set (Society α β) := insert A₀' (S_seg \ {A₀})
  let f : Society α β → Society α β := fun S₀ => if S₀ = A₀' then A₀ else S₀
  let α_disc_G : Society α β → Set S := fun S₀ => α_disc (f S₀)
  have hf_mem : ∀ S₀ ∈ S_seg_G, f S₀ ∈ S_seg := by
    rintro S₀ (rfl | ⟨hS₀_in, _⟩)
    · simp [f, hA₀_in]
    · have hne : S₀ ≠ A₀' := fun h => hA₀'_not_in (h ▸ hS₀_in)
      simp [f, hne, hS₀_in]
  have hf_inj : InjOn f S_seg_G := by
    rintro S₁ (rfl | ⟨hS₁, hne₁⟩) S₂ (rfl | ⟨hS₂, hne₂⟩) hEq
    · rfl
    · have hne₂' : S₂ ≠ A₀' := fun h => hA₀'_not_in (h ▸ hS₂)
      simp only [f, ↓reduceIte, hne₂'] at hEq
      exact (hne₂ hEq.symm).elim
    · have hne₁' : S₁ ≠ A₀' := fun h => hA₀'_not_in (h ▸ hS₁)
      simp only [f, hne₁', ↓reduceIte] at hEq
      exact (hne₁ hEq).elim
    · have hne₁' : S₁ ≠ A₀' := fun h => hA₀'_not_in (h ▸ hS₁)
      have hne₂' : S₂ ≠ A₀' := fun h => hA₀'_not_in (h ▸ hS₂)
      simpa [f, hne₁', hne₂'] using hEq
  have hf_surj : SurjOn f S_seg_G S_seg := by
    intro S₀ hS₀
    by_cases h : S₀ = A₀
    · subst h
      exact ⟨A₀', Or.inl rfl, by simp [f]⟩
    · have hne : S₀ ≠ A₀' := fun h' => hA₀'_not_in (h' ▸ hS₀)
      exact ⟨S₀, Or.inr ⟨hS₀, h⟩, by simp [f, hne]⟩
  have hf_Ω : ∀ S₀ ∈ S_seg_G, (f S₀).Ω = S₀.Ω := by
    rintro S₀ (rfl | ⟨hS₀_in, _⟩)
    · simp [f, A₀']
    · have hne : S₀ ≠ A₀' := fun h => hA₀'_not_in (h ▸ hS₀_in)
      simp [f, hne]
  have hf_V : ∀ S₀ ∈ S_seg_G, V(S₀.G) ∩ V(G') = V((f S₀).G) := by
    rintro S₀ (rfl | ⟨hS₀_in, _⟩)
    · simp only [f, ↓reduceIte, A₀', hV_GA, union_inter_distrib_right,
        hDisj_V.symm.inter_eq, union_empty]
      exact inter_eq_left.mpr (hSeg.1.le A₀ hA₀_in).vertexSet_mono
    · have hne : S₀ ≠ A₀' := fun h => hA₀'_not_in (h ▸ hS₀_in)
      simp only [f, hne, ↓reduceIte]
      exact inter_eq_left.mpr (hSeg.1.le S₀ hS₀_in).vertexSet_mono
  have hf_E : ∀ S₀ ∈ S_seg_G, E(S₀.G) ∩ E(G') = E((f S₀).G) := by
    rintro S₀ (rfl | ⟨hS₀_in, _⟩)
    · simp only [f, ↓reduceIte, A₀', hE_GA, union_inter_distrib_right,
        hDisj_E.symm.inter_eq, union_empty]
      exact inter_eq_left.mpr (hSeg.1.le A₀ hA₀_in).edgeSet_mono
    · have hne : S₀ ≠ A₀' := fun h => hA₀'_not_in (h ▸ hS₀_in)
      simp only [f, hne, ↓reduceIte]
      exact inter_eq_left.mpr (hSeg.1.le S₀ hS₀_in).edgeSet_mono
  have hsegV_eq : segregationVertices S_seg_G = segregationVertices S_seg := by
    ext x
    simp only [segregationVertices, mem_iUnion, exists_prop]
    refine ⟨fun ⟨S₀, hS₀, hx⟩ => ⟨f S₀, hf_mem S₀ hS₀, (hf_Ω S₀ hS₀).symm ▸ hx⟩,
      fun ⟨S₀, hS₀, hx⟩ => ?_⟩
    obtain ⟨S₁, hS₁, rfl⟩ := hf_surj hS₀
    exact ⟨S₁, hS₁, (hf_Ω S₁ hS₁) ▸ hx⟩
  have hS_seg_G_le : ∀ S₀ ∈ S_seg_G, S₀.G ≤ G₀ := by
    rintro S₀ (rfl | ⟨hS₀_in, _⟩)
    · exact hG_A_le
    · exact (hSeg.1.le S₀ hS₀_in).trans hG'_le
  have hS_seg_G_le_img : ∀ Q ∈ (fun S₀ : Society α β => S₀.G) '' S_seg_G, Q ≤ G₀ := by
    rintro _ ⟨S₀, hS₀, rfl⟩
    exact hS_seg_G_le S₀ hS₀
  have hS_seg_le_img : ∀ Q ∈ (fun S₀ : Society α β => S₀.G) '' S_seg, Q ≤ G' := by
    rintro _ ⟨S₀, hS₀, rfl⟩
    exact hSeg.1.le S₀ hS₀
  have h3seg_G : IsThreeSegregation G₀ S_seg_G := by
    exact disjoint_bridge_piece_preserves_three_segregation (S := S) (α := α) (β := β) (G₀ := G₀)
      (G' := G') (J := J) (H := H) (η₀ := η₀) (S_seg := S_seg) hJ hG'_le hG₀_eq hSeg A₀ G_A hV_GA
      hE_GA A₀' rfl f hf_mem hf_inj hf_surj hf_Ω hf_V hf_E hS_seg_G_le hS_seg_G_le_img hS_seg_le_img
  have hArr_G : IsSurfaceArrangement S_seg_G α_disc_G α_pt := by
    refine ⟨fun S₀ hS₀ => hf_Ω S₀ hS₀ ▸ hArr.isClosedDisc (f S₀) (hf_mem S₀ hS₀),
      fun S₁ hS₁ S₂ hS₂ hne => ?_,
      fun S₀ hS₀ => hf_Ω S₀ hS₀ ▸ hArr.inter_bd (f S₀) (hf_mem S₀ hS₀),
      hsegV_eq ▸ hArr.injOn_pts,
      fun S₀ hS₀ => hf_Ω S₀ hS₀ ▸ hArr.natural_order (f S₀) (hf_mem S₀ hS₀)⟩
    rw [← hf_Ω S₁ hS₁, ← hf_Ω S₂ hS₂]
    exact hArr.inter_discs (f S₁) (hf_mem S₁ hS₁) (f S₂) (hf_mem S₂ hS₂)
      (fun h => hne (hf_inj hS₁ hS₂ h))
  have hComp_G : IsCompatibleWith G₀ H η₀ S_seg_G α_disc_G α_pt := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro v hvH hv_seg
      rw [← hη'_v v hvH]
      exact hComp.pt_eq v hvH (hsegV_eq ▸ hη'_v v hvH ▸ hv_seg)
    · intro S₀ hS₀
      rw [show α_disc_G S₀ = α_disc (f S₀) from rfl, hComp.bd_inter_eq (f S₀) (hf_mem S₀ hS₀),
        hf_Ω S₀ hS₀]
      ext v
      simp only [mem_sep_iff]
      exact ⟨fun ⟨hv, h⟩ => ⟨hv, hη'_v v hv ▸ h⟩, fun ⟨hv, h⟩ => ⟨hv, (hη'_v v hv).symm ▸ h⟩⟩
    · intro S₀ hS₀ v hvH
      rw [show α_disc_G S₀ = α_disc (f S₀) from rfl, hComp.inter_V_iff (f S₀) (hf_mem S₀ hS₀) v hvH,
        hη'_v v hvH, ← hf_V S₀ hS₀, mem_inter_iff]
      have hvG' : η₀.vMap v ∈ V(G') :=
        hη'_v v hvH ▸ η'.imageGraph_le.vertexSet_mono (η'.bijOn_v.mapsTo hvH)
      exact ⟨fun h => h.1, fun h => ⟨h, hvG'⟩⟩
    · intro S₀ hS₀ e heH
      rw [show α_disc_G S₀ = α_disc (f S₀) from rfl, hComp.inter_E_iff (f S₀) (hf_mem S₀ hS₀) e heH,
        hη'_e e heH, ← hf_E S₀ hS₀, mem_inter_iff]
      have heG' : η₀.eMap e ∈ E(G') :=
        hη'_e e heH ▸ η'.imageGraph_le.edgeSet_mono (η'.bijOn_e.mapsTo heH)
      exact ⟨fun h => h.1, fun h => ⟨h, heG'⟩⟩
  have hLoc_G : IsTangleLocal G₀ H η₀ T S_seg_G := by
    exact disjoint_bridge_piece_preserves_tangle_locality (S := S) (α := α) (β := β) (G₀ := G₀)
      (G' := G') (H := H) (η₀ := η₀) (η' := η') (T := T) (S_seg := S_seg) hG'_le hη'_v hη'_e hSeg
      hLoc S_seg_G f hf_mem hf_Ω hf_V hf_E
  exact ⟨S_seg_G, α_disc_G, α_pt, h3seg_G, hLoc_G, hArr_G, hComp_G⟩

omit [T2Space S] in
private theorem ends_toHypergraph_eq {H : Drawing S} {e : Set S} (he : e ∈ H.E) :
    H.toHypergraph.ends e = closure e ∩ H.V := by
  ext v
  simp only [Hypergraph.ends, mem_ofPred_eq, mem_inter_iff]
  exact ⟨fun ⟨_, hv, hcl⟩ => ⟨hcl, hv⟩, fun ⟨hcl, hv⟩ => ⟨he, hv, hcl⟩⟩

omit [T2Space S] in
/-- Every closed surface `S : Type u` is homeomorphic to a topological space `T : Type 0`. -/
private theorem exists_homeomorph_type_zero (hS : IsClosedSurface S) :
    ∃ (T : Type) (_ : TopologicalSpace T), Nonempty (S ≃ₜ T) := by
  classical
  have : CompactSpace S := hS.1
  have hchart : ∀ x : S, IsInteriorPoint x := hS.2.2
  choose U hU_open hxU hφ using hchart
  obtain ⟨F, hF_cov⟩ :=
    isCompact_univ.elim_finite_subcover U hU_open (fun x _ => mem_iUnion.mpr ⟨x, hxU x⟩)
  let eF : F ≃ Fin F.card := F.equivFin
  have hex : ∀ s : S, ∃ x : F, s ∈ U x.1 := by
    intro s
    obtain ⟨x, hx⟩ := mem_iUnion.mp (hF_cov (mem_univ s))
    obtain ⟨hxF, hsU⟩ := mem_iUnion.mp hx
    exact ⟨⟨x, hxF⟩, hsU⟩
  let φ : ∀ x : S, U x ≃ₜ OpenUnitDisc := fun x => Classical.choice (hφ x)
  let toZero : S → Fin F.card × OpenUnitDisc := fun s =>
    (eF (Classical.choose (hex s)),
      φ (Classical.choose (hex s)).1 ⟨s, Classical.choose_spec (hex s)⟩)
  have haux : ∀ {s₁ s₂ : S} (x₁ x₂ : F) (hs₁ : s₁ ∈ U x₁.1) (hs₂ : s₂ ∈ U x₂.1),
      x₁ = x₂ →
      φ x₁.1 ⟨s₁, hs₁⟩ = φ x₂.1 ⟨s₂, hs₂⟩ →
      s₁ = s₂ := by
    rintro s₁ s₂ x₁ _ hs₁ hs₂ rfl hφ_eq
    exact congrArg Subtype.val ((φ x₁.1).injective hφ_eq)
  have htoZero_inj : Function.Injective toZero := by
    intro s₁ s₂ hEq
    exact haux (Classical.choose (hex s₁)) (Classical.choose (hex s₂))
      (Classical.choose_spec (hex s₁)) (Classical.choose_spec (hex s₂))
      (eF.injective (congrArg Prod.fst hEq)) (congrArg Prod.snd hEq)
  let T : Type := range toZero
  let e : S ≃ T := Equiv.ofInjective toZero htoZero_inj
  let topT : TopologicalSpace T := TopologicalSpace.induced e.symm inferInstance
  have hind : @Topology.IsInducing T S topT _ e.symm := ⟨rfl⟩
  exact ⟨T, topT, ⟨(@Equiv.toHomeomorphOfIsInducing T S topT _ e.symm hind).symm⟩⟩

omit [T2Space S] in
/-- Universe-polymorphic wrapper around `exists_edge_lens` for `S : Type u`. -/
private theorem exists_edge_lens_univ (hS : IsClosedSurface S)
    {L : Set S} {u v : S} (hL : IsLineWithEnds L u v) (huv : u ≠ v)
    {Z : Set S} (hZ : IsClosed Z) (hLZ : L ∩ Z ⊆ {u, v}) :
    ∃ D : Set S,
      IsClosedDisc D ∧ L ⊆ D ∧ D ∩ Z ⊆ {u, v} ∧
      u ∈ discBd D ∧ v ∈ discBd D ∧ discBd D ∩ L ⊆ {u, v} := by
  obtain ⟨T, _, ⟨ψ⟩⟩ := exists_homeomorph_type_zero hS
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  have hT : IsClosedSurface T :=
    ⟨ψ.compactSpace, ψ.t2Space, fun y => by
      simpa using (isInteriorPoint_homeomorph_iff ψ (ψ.symm y)).mpr (hS.2.2 (ψ.symm y))⟩
  have hL' : IsLineWithEnds (ψ '' L) (ψ u) (ψ v) := by
    obtain ⟨f, hf0, hf1⟩ := hL
    exact ⟨f.trans (ψ.image L), congrArg ψ hf0, congrArg ψ hf1⟩
  have huv' : ψ u ≠ ψ v := fun h => huv (ψ.injective h)
  have hZ' : IsClosed (ψ '' Z) := ψ.isClosedMap Z hZ
  have hLZ' : (ψ '' L) ∩ (ψ '' Z) ⊆ {ψ u, ψ v} := by
    rintro _ ⟨⟨x, hxL, rfl⟩, ⟨y, hyZ, hxy⟩⟩
    have hxy' : y = x := ψ.injective hxy
    subst hxy'
    rcases hLZ ⟨hxL, hyZ⟩ with rfl | rfl <;> simp
  obtain ⟨D', _, _, hD'_disc, hL'_sub, hD'Z', hu'_bd, hv'_bd, hbd'_L', _⟩ :=
    exists_edge_lens hT hL' huv' hZ' hLZ'
  let D : Set S := ψ.symm '' D'
  have hD_disc : IsClosedDisc D := by
    obtain ⟨φ⟩ := hD'_disc
    exact ⟨φ.trans (ψ.symm.image D')⟩
  have hbd_eq : discBd D = ψ.symm '' discBd D' := by
    rw [← IsClosedDisc.subBd_eq_discBd hS hD_disc, ← IsClosedDisc.subBd_eq_discBd hT hD'_disc,
      ← subBd_eq_frontier' D, ← subBd_eq_frontier' D']
    exact (ψ.symm.image_frontier D').symm
  refine ⟨D, hD_disc, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hxL
    exact ⟨ψ x, hL'_sub ⟨x, hxL, rfl⟩, ψ.symm_apply_apply x⟩
  · rintro x ⟨⟨y, hyD', rfl⟩, hxZ⟩
    have hy_in : y ∈ D' ∩ ψ '' Z := ⟨hyD', ψ.symm y, hxZ, ψ.apply_symm_apply y⟩
    rcases hD'Z' hy_in with rfl | rfl <;> simp
  · rw [hbd_eq]
    exact ⟨ψ u, hu'_bd, ψ.symm_apply_apply u⟩
  · rw [hbd_eq]
    exact ⟨ψ v, hv'_bd, ψ.symm_apply_apply v⟩
  · rw [hbd_eq]
    rintro x ⟨⟨y, hybd', rfl⟩, hxL⟩
    have hy_in : y ∈ discBd D' ∩ ψ '' L := ⟨hybd', ψ.symm y, hxL, ψ.apply_symm_apply y⟩
    rcases hbd'_L' hy_in with rfl | rfl <;> simp

/-- Every edge of a rigid drawing `H` with a respectful tangle of order `θ ≥ 2` has two distinct
endpoints in `H.V` (`closure e` is a line with ends `u, v`). -/
private theorem no_loop_of_rigid_tangle
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {H : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    (hRig : IsRigid H) (hMetric : HasTangleMetric H θ T d) (hθ : 2 ≤ θ)
    {e : Set S} (he : e ∈ H.E) :
    ∃ u v : S, u ≠ v ∧ closure e ∩ H.V = {u, v} ∧ IsLineWithEnds (closure e) u v := by
  have : ConnectedSpace S := hConn
  rcases H.edge_cond e he with hline | ⟨u, hcap, _⟩
  · exact hline
  · exfalso
    have hu_in : u ∈ closure e ∩ H.V := hcap ▸ mem_singleton u
    have huV : u ∈ H.V := hu_in.2
    have he_hyp : e ∈ H.toHypergraph.edgeSet :=
      (PaintingOrDrawing.toHypergraph_edgeSet (Γ := PaintingOrDrawing.drawing H)).symm ▸ he
    let A : Hypergraph S (Set S) := GM10.edgeHypergraph H.toHypergraph e
    let B : Hypergraph S (Set S) := H.toHypergraph.deleteEdges {e}
    have hVA : A.vertexSet = {u} := by
      change H.toHypergraph.ends e = {u}
      rw [ends_toHypergraph_eq he, hcap]
    have hsep : H.toHypergraph.IsSeparation A B :=
      GM10.isSeparation_edgeHypergraph_deleteEdges he_hyp
    have hord : separationOrder A B < θ := by
      have hV_inter : (A ∩ B).vertexSet = {u} := by
        change A.vertexSet ∩ H.V = {u}
        rw [hVA]
        exact inter_eq_left.mpr (singleton_subset_iff.mpr huV)
      rw [separationOrder, hV_inter, ncard_singleton]
      omega
    have hAB : (A, B) ∈ T :=
      (hMetric.1.2.1.axiom1 hsep hord).resolve_right (fun hBA => hMetric.1.2.1.axiom3 hBA rfl)
    obtain ⟨K, ins, hK, hd, _⟩ := hMetric.2
    obtain ⟨D, hD, hDs, hDlen, hDV, heD⟩ :=
      theorem_7_2_proof hS hConn ⟨e, he⟩ hMetric.1 hK hd hAB (mem_singleton e)
    have hDV_sub : D.V ∩ H.V ⊆ {u} :=
      hDV.trans (hVA ▸ inter_subset_left)
    have hUU : H.U ∩ K.U = H.V := hK.2.1.1
    have hDU_HU : D.U ∩ H.U ⊆ H.V := by
      rintro x ⟨hxD, hxH⟩
      have : x ∈ H.U ∩ K.U := ⟨hxH, hDs.U_subset hxD⟩
      rwa [hUU] at this
    have hDU_HV : D.U ∩ H.V ⊆ {u} := by
      rintro x ⟨hxD, hxV⟩
      have hxDV : x ∈ D.V := by
        by_contra hxnot
        obtain ⟨g, hgD, hxg⟩ := D.exists_edge_of_mem hxD hxnot
        exact ((hDs.2 hgD).2.1 hxg).2 (hK.2.1.2.1 hxV)
      exact hDV_sub ⟨hxDV, hxV⟩
    have hcard_le1 : (D.U ∩ H.V).ncard ≤ 1 :=
      (ncard_le_ncard hDU_HV (finite_singleton u)).trans (by simp)
    obtain ⟨Δ, hΔ_disc, hΔ_bd, hΔ_cases⟩ :=
      hRig D.U (isOArc_of_isCircuit hD) hDU_HU (by omega)
    have hΔ_HU : Δ ∩ H.U ⊆ D.U := by
      rcases hΔ_cases with hsub | ⟨u₁, v₁, huv_ne, hpair, _⟩
      · exact hsub
      · exfalso
        have hu₁ : u₁ = u := hDU_HV (hpair ▸ Or.inl rfl)
        have hv₁ : v₁ = u := hDU_HV (hpair ▸ Or.inr rfl)
        exact huv_ne (hu₁.trans hv₁.symm)
    obtain ⟨hDdisc, hDbd, hDT⟩ := hd D hD hDs hDlen
    by_cases h_eq : ins D = Δ
    · obtain ⟨p, hp⟩ := he.1
      have hp_Δ : p ∈ Δ ∩ H.U := ⟨h_eq ▸ heD hp, (he.2.1 hp).1⟩
      exact (he.2.1 hp).2 (hDU_HU ⟨hΔ_HU hp_Δ, hp_Δ.2⟩)
    · have hdiscBd_eq : discBd (ins D) = discBd Δ := by
        rw [← IsClosedDisc.subBd_eq_discBd hS hDdisc, hDbd,
          ← IsClosedDisc.subBd_eq_discBd hS hΔ_disc, hΔ_bd]
      have hcov : ins D ∪ Δ = univ := cover_of_discBd_eq hS hDdisc hΔ_disc hdiscBd_eq h_eq
      have hDU_ins : D.U ⊆ ins D := by
        have hfr : frontier (ins D) = D.U := by rw [subBd_eq_frontier', hDbd]
        exact hfr ▸ hDdisc.isClosed.frontier_subset
      have hHV_ins : H.V ⊆ ins D := by
        intro v hvV
        have hvU : v ∈ H.U := H.V_subset_U hvV
        rcases (hcov.symm ▸ mem_univ v : v ∈ ins D ∪ Δ) with hvin | hvΔ
        · exact hvin
        · exact hDU_ins (hΔ_HU ⟨hvΔ, hvU⟩)
      have hV_eq : ((PaintingOrDrawing.drawing H).inter (ins D)).vertexSet =
          H.toHypergraph.vertexSet :=
        inter_eq_left.mpr hHV_ins
      exact hMetric.1.2.1.axiom3 hDT hV_eq

private theorem exists_disjoint_edge_lenses
    {S : Type u}
    [TopologicalSpace S]
    [T2Space S]
    (hS : IsClosedSurface S)
    {H : Drawing S}
    (hends : ∀ e ∈ H.E, ∃ u v, u ≠ v ∧ closure e ∩ H.V = {u, v} ∧ IsLineWithEnds (closure e) u v)
    (hcl_inter : ∀ e ∈ H.E, ∀ f ∈ H.E, e ≠ f → closure e ∩ closure f ⊆ H.V) :
    ∀ (E_sub : Finset (Set S)), ↑E_sub ⊆ H.E → ∃ (D : Set S → Set S),
      ∀ e ∈ E_sub, IsClosedDisc (D e) ∧ closure e ⊆
      D e ∧ D e ∩ H.V = closure e ∩ H.V ∧ H.U ∩ subBd (D e) = closure e ∩ H.V ∧ (∀ g ∈ H.E, g ≠ e
      → D e ∩ closure g ⊆ closure e ∩ H.V ∩ (closure g ∩ H.V)) ∧ ∀ f ∈ E_sub, f ≠ e → D e ∩ D f ⊆
      closure e ∩ H.V ∩ (closure f ∩ H.V) := by
  intro E_sub
  induction E_sub using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨fun _ => ∅, fun _ h => (Finset.notMem_empty _ h).elim⟩
  | @insert e₀ E_sub he₀_not ih =>
    intro hsub
    have he₀H : e₀ ∈ H.E := hsub (Finset.mem_insert_self e₀ E_sub)
    have hsub' : (E_sub : Set (Set S)) ⊆ H.E :=
      (Finset.coe_subset.mpr (Finset.subset_insert e₀ E_sub)).trans hsub
    obtain ⟨D₀, hD₀⟩ := ih hsub'
    obtain ⟨u, v, huv, hcap, hL⟩ := hends e₀ he₀H
    let Z : Set S := H.V ∪ (⋃ g ∈ H.E \ {e₀}, closure g) ∪ (⋃ f ∈ E_sub, D₀ f)
    have hZ : IsClosed Z :=
      (H.finite_V.isClosed.union
        ((H.finite_edges.subset sdiff_subset).isClosed_biUnion fun _ _ => isClosed_closure)).union
        (E_sub.finite_toSet.isClosed_biUnion fun f hf => (hD₀ f hf).1.isClosed)
    have hLZ : closure e₀ ∩ Z ⊆ {u, v} := by
      rw [← hcap]
      rintro x ⟨hxe₀, (hxV | hxg) | hxf⟩
      · exact ⟨hxe₀, hxV⟩
      · simp only [mem_iUnion, exists_prop] at hxg
        obtain ⟨g, ⟨hgH, hge₀⟩, hxg⟩ := hxg
        exact ⟨hxe₀, hcl_inter e₀ he₀H g hgH (Ne.symm hge₀) ⟨hxe₀, hxg⟩⟩
      · simp only [mem_iUnion] at hxf
        obtain ⟨f, hf_in, hxf⟩ := hxf
        have hfe₀ : f ≠ e₀ := fun h => he₀_not (h ▸ hf_in)
        exact ((hD₀ f hf_in).2.2.2.2.1 e₀ he₀H hfe₀.symm ⟨hxf, hxe₀⟩).2
    obtain ⟨D_new, hD_disc, hL_sub, hDZ, hu_bd, hv_bd, hbd_L⟩ :=
      exists_edge_lens_univ hS hL huv hZ hLZ
    have hsubBd_eq : subBd D_new = discBd D_new := IsClosedDisc.subBd_eq_discBd hS hD_disc
    have hD_HV : D_new ∩ H.V = closure e₀ ∩ H.V := by
      apply subset_antisymm
      · rw [hcap]
        exact (inter_subset_inter_right D_new
          (subset_union_left.trans subset_union_left)).trans hDZ
      · exact inter_subset_inter_left H.V hL_sub
    have hD_clg : ∀ g ∈ H.E, g ≠ e₀ →
        D_new ∩ closure g ⊆ (closure e₀ ∩ H.V) ∩ (closure g ∩ H.V) := by
      intro g hg hge₀ x ⟨hxD, hxg⟩
      have hxZ : x ∈ Z := Or.inl (Or.inr (mem_biUnion ⟨hg, hge₀⟩ hxg))
      have hx_uv : x ∈ closure e₀ ∩ H.V := hcap ▸ hDZ ⟨hxD, hxZ⟩
      exact ⟨hx_uv, hxg, hx_uv.2⟩
    have hD_Df : ∀ f ∈ E_sub, f ≠ e₀ →
        D_new ∩ D₀ f ⊆ (closure e₀ ∩ H.V) ∩ (closure f ∩ H.V) := by
      intro f hf _ x ⟨hxD, hxDf⟩
      have hxZ : x ∈ Z := Or.inr (mem_biUnion hf hxDf)
      have hx_uv : x ∈ closure e₀ ∩ H.V := hcap ▸ hDZ ⟨hxD, hxZ⟩
      have hx_f : x ∈ closure f ∩ H.V := (hD₀ f hf).2.2.1 ▸ ⟨hxDf, hx_uv.2⟩
      exact ⟨hx_uv, hx_f⟩
    have hHU_bd : H.U ∩ subBd D_new = closure e₀ ∩ H.V := by
      apply subset_antisymm
      · rintro x ⟨hxU, hxbd⟩
        have hxD : x ∈ D_new := hD_disc.isClosed.closure_eq ▸ hxbd.1
        rw [H.U_eq] at hxU
        rcases hxU with hxV | hxe
        · exact hD_HV ▸ ⟨hxD, hxV⟩
        · simp only [mem_iUnion, exists_prop] at hxe
          obtain ⟨g, hgH, hxg⟩ := hxe
          by_cases hge₀ : g = e₀
          · subst hge₀
            rw [hsubBd_eq] at hxbd
            exact hcap ▸ hbd_L ⟨hxbd, hxg⟩
          · exact (hD_clg g hgH hge₀ ⟨hxD, hxg⟩).1
      · rw [hcap, hsubBd_eq]
        rintro x (rfl | rfl)
        · exact ⟨H.V_subset_U (hcap ▸ Or.inl rfl : x ∈ closure e₀ ∩ H.V).2, hu_bd⟩
        · exact ⟨H.V_subset_U (hcap ▸ Or.inr rfl : x ∈ closure e₀ ∩ H.V).2, hv_bd⟩
    let D : Set S → Set S := fun e => if e = e₀ then D_new else D₀ e
    refine ⟨D, fun e he => ?_⟩
    rcases Finset.mem_insert.mp he with rfl | he_in
    · simp only [D, ↓reduceIte]
      refine ⟨hD_disc, hL_sub, hD_HV, hHU_bd, hD_clg, fun f hf hfe => ?_⟩
      rcases Finset.mem_insert.mp hf with rfl | hf_in
      · exact (hfe rfl).elim
      · simp only [hfe, ↓reduceIte]
        exact hD_Df f hf_in hfe
    · have hee₀ : e ≠ e₀ := fun h => he₀_not (h ▸ he_in)
      simp only [D, hee₀, ↓reduceIte]
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hD₀ e he_in
      refine ⟨h1, h2, h3, h4, h5, fun f hf hfe => ?_⟩
      rcases Finset.mem_insert.mp hf with rfl | hf_in
      · simp only [↓reduceIte]
        rw [Set.inter_comm (D₀ e) D_new, Set.inter_comm (closure e ∩ H.V)]
        exact hD_Df e he_in hee₀
      · have hfe₀ : f ≠ e₀ := fun h => he₀_not (h ▸ hf_in)
        simp only [hfe₀, ↓reduceIte]
        exact h6 f hf_in hfe

private theorem edge_societies_form_three_segregation
    {S : Type u}
    [TopologicalSpace S]
    {α : Type v}
    {β : Type w}
    (hS : IsClosedSurface S)
    {G₀ : Graph α β}
    {H : Drawing S}
    {η₀ : SpanEmbedding H G₀}
    (hbase : G₀ = η₀.imageGraph)
    [ConnectedSpace S]
    (K : Drawing S)
    (hrf : RegionFacts (PaintingOrDrawing.drawing H) K)
    (hends : ∀ e ∈ H.E, ∃ u v, u ≠ v ∧ closure e ∩ H.V = {u, v} ∧ IsLineWithEnds (closure e) u v)
    (D_map : Set S → Set S)
    (α_pt : α → S)
    (G_e : Set S → Graph α β)
    (hV_Ge : ∀ (e : Set S), V(G_e e) = (fun e => η₀.vMap '' (closure e ∩ H.V)) e)
    (hE_Ge : ∀ e ∈ H.E, E(G_e e) = {η₀.eMap e})
    (Ω_map : Set S → CyclicPerm α)
    (hΩ_map : ∀ e ∈ H.E, (Ω_map e).bar = (fun e => η₀.vMap '' (closure e ∩ H.V)) e ∧
      IsNaturalOrderFrom α_pt (Ω_map e) (subBd (D_map e)))
    (S_map : Set S → Society α β)
    (hS_map_G : ∀ e ∈ H.E, (S_map e).G = G_e e)
    (hS_map_Ω : ∀ e ∈ H.E, (S_map e).Ω = Ω_map e)
    (hS_seg_le : ∀ S₀ ∈ (S_map '' H.E), S₀.G ≤ G₀)
    (hS_seg_le_img : ∀ Q ∈ (fun S₀ => S₀.G) '' (S_map '' H.E), Q ≤ G₀) :
    IsThreeSegregation G₀ (S_map '' H.E) := by
  let V_e := fun e => η₀.vMap '' (closure e ∩ H.V)
  let S_seg := S_map '' H.E
  refine ⟨⟨H.finite_edges.image S_map, hS_seg_le, ?_, ?_, ?_⟩, ?_⟩
  · refine (Compatible.of_le_le (subgraphSUnion_le hS_seg_le_img) le_rfl).ext ?_ ?_
    · rw [vertexSet_subgraphSUnion]
      ext x
      simp only [mem_iUnion, mem_image, exists_prop]
      refine ⟨fun ⟨_, ⟨S₀, hS₀, rfl⟩, hx⟩ => (hS_seg_le S₀ hS₀).vertexSet_mono hx,
        fun hxG₀ => ?_⟩
      obtain ⟨v, hvH, rfl⟩ := η₀.bijOn_v.surjOn (hbase ▸ hxG₀)
      obtain ⟨e, heH, hve⟩ := GM11.exists_edge_of_regionFacts hS hrf hvH
      refine ⟨G_e e, ⟨S_map e, ⟨e, heH, rfl⟩, hS_map_G e heH⟩, ?_⟩
      rw [hV_Ge e]
      exact ⟨v, ⟨hve, hvH⟩, rfl⟩
    · rw [edgeSet_subgraphSUnion hS_seg_le_img]
      ext e_G
      simp only [mem_iUnion, mem_image, exists_prop]
      refine ⟨fun ⟨_, ⟨S₀, hS₀, rfl⟩, he⟩ => (hS_seg_le S₀ hS₀).edgeSet_mono he,
        fun heG₀ => ?_⟩
      obtain ⟨e, heH, rfl⟩ := η₀.bijOn_e.surjOn (hbase ▸ heG₀)
      refine ⟨G_e e, ⟨S_map e, ⟨e, heH, rfl⟩, hS_map_G e heH⟩, ?_⟩
      rw [hE_Ge e heH]
      exact mem_singleton _
  · rintro _ ⟨e₁, he₁, rfl⟩ _ ⟨e₂, he₂, rfl⟩ _
    rw [hS_map_G e₁ he₁, hS_map_G e₂ he₂, hV_Ge e₁, hV_Ge e₂,
      hS_map_Ω e₁ he₁, hS_map_Ω e₂ he₂, (hΩ_map e₁ he₁).1, (hΩ_map e₂ he₂).1]
  · rintro _ ⟨e₁, he₁, rfl⟩ _ ⟨e₂, he₂, rfl⟩ hne
    have he_ne : e₁ ≠ e₂ := fun h => hne (h ▸ rfl)
    rw [hS_map_G e₁ he₁, hS_map_G e₂ he₂, hE_Ge e₁ he₁, hE_Ge e₂ he₂,
      disjoint_singleton]
    exact fun h => he_ne (η₀.bijOn_e.injOn he₁ he₂ h)
  · rintro _ ⟨e, he, rfl⟩
    rw [hS_map_Ω e he, (hΩ_map e he).1]
    obtain ⟨u, v, _, hcap, _⟩ := hends e he
    have hcard : (V_e e).ncard ≤ 2 := by
      change (η₀.vMap '' (closure e ∩ H.V)).ncard ≤ 2
      rw [hcap]
      exact (ncard_image_le ((finite_singleton v).insert u)).trans
        ((ncard_insert_le u {v}).trans (by simp))
    exact hcard.trans (by decide)

private theorem edge_lenses_form_surface_arrangement
    {S : Type u}
    [TopologicalSpace S]
    {α : Type v}
    {β : Type w}
    (hS : IsClosedSurface S)
    {G₀ : Graph α β}
    {H : Drawing S}
    {η₀ : SpanEmbedding H G₀}
    (D_map : Set S → Set S)
    (hD : ∀ e ∈ H.E, IsClosedDisc (D_map e) ∧ closure e ⊆ D_map e ∧ D_map e ∩ H.V = closure e ∩
      H.V ∧ H.U ∩ subBd (D_map e) = closure e ∩ H.V ∧ (∀ g ∈ H.E, g ≠ e → D_map e ∩ closure g ⊆
      closure e ∩ H.V ∩ (closure g ∩ H.V)) ∧ ∀ f ∈ H.E, f ≠ e → D_map e ∩ D_map f ⊆ closure e ∩
      H.V ∩ (closure f ∩ H.V))
    (α_pt : α → S)
    (hα_pt_vMap : ∀ v ∈ H.V, α_pt (η₀.vMap v) = v)
    (hα_pt_inj : InjOn α_pt V(G₀))
    (Ω_map : Set S → CyclicPerm α)
    (hΩ_map : ∀ e ∈ H.E, (Ω_map e).bar = (fun e => η₀.vMap '' (closure e ∩ H.V)) e ∧
      IsNaturalOrderFrom α_pt (Ω_map e) (subBd (D_map e)))
    (S_map : Set S → Society α β)
    (hS_map_Ω : ∀ e ∈ H.E, (S_map e).Ω = Ω_map e)
    (α_disc : Society α β → Set S)
    (hα_disc_eq : ∀ e ∈ H.E, α_disc (S_map e) = D_map e)
    (hsegV_sub : segregationVertices (S_map '' H.E) ⊆ V(G₀)) :
    IsSurfaceArrangement (S_map '' H.E) α_disc α_pt := by
  let V_e := fun e => η₀.vMap '' (closure e ∩ H.V)
  let S_seg := S_map '' H.E
  refine ⟨?_, ?_, ?_, hα_pt_inj.mono hsegV_sub, ?_⟩
  · rintro _ ⟨e, he, rfl⟩
    rw [hα_disc_eq e he, hS_map_Ω e he, (hΩ_map e he).1]
    refine ⟨(hD e he).1, ?_⟩
    rintro _ ⟨v, hv_cl, rfl⟩
    rw [hα_pt_vMap v hv_cl.2]
    exact ((hD e he).2.2.2.1 ▸ hv_cl).2
  · rintro _ ⟨e₁, he₁, rfl⟩ _ ⟨e₂, he₂, rfl⟩ hne
    have he_ne : e₁ ≠ e₂ := fun h => hne (h ▸ rfl)
    rw [hα_disc_eq e₁ he₁, hα_disc_eq e₂ he₂,
      hS_map_Ω e₁ he₁, hS_map_Ω e₂ he₂, (hΩ_map e₁ he₁).1, (hΩ_map e₂ he₂).1]
    intro x hx
    obtain ⟨hx₁, hx₂⟩ := (hD e₁ he₁).2.2.2.2.2 e₂ he₂ he_ne.symm hx
    exact ⟨η₀.vMap x, ⟨⟨x, hx₁, rfl⟩, ⟨x, hx₂, rfl⟩⟩, hα_pt_vMap x hx₁.2⟩
  · rintro _ ⟨e, he, rfl⟩ x ⟨_, hxbd⟩
    exact (hxbd (hS.2.2 x)).elim
  · rintro _ ⟨e, he, rfl⟩
    rw [hα_disc_eq e he, hS_map_Ω e he]
    exact (hΩ_map e he).2

private theorem edge_lens_arrangement_is_compatible
    {S : Type u}
    [TopologicalSpace S]
    {α : Type v}
    {β : Type w}
    {G₀ : Graph α β}
    {H : Drawing S}
    {η₀ : SpanEmbedding H G₀}
    (D_map : Set S → Set S)
    (hD : ∀ e ∈ H.E, IsClosedDisc (D_map e) ∧ closure e ⊆ D_map e ∧ D_map e ∩ H.V = closure e ∩
      H.V ∧ H.U ∩ subBd (D_map e) = closure e ∩ H.V ∧ (∀ g ∈ H.E, g ≠ e → D_map e ∩ closure g ⊆
      closure e ∩ H.V ∩ (closure g ∩ H.V)) ∧ ∀ f ∈ H.E, f ≠ e → D_map e ∩ D_map f ⊆ closure e ∩
      H.V ∩ (closure f ∩ H.V))
    (α_pt : α → S)
    (hα_pt_vMap : ∀ v ∈ H.V, α_pt (η₀.vMap v) = v)
    (G_e : Set S → Graph α β)
    (hV_Ge : ∀ (e : Set S), V(G_e e) = (fun e => η₀.vMap '' (closure e ∩ H.V)) e)
    (hE_Ge : ∀ e ∈ H.E, E(G_e e) = {η₀.eMap e})
    (Ω_map : Set S → CyclicPerm α)
    (hΩ_map : ∀ e ∈ H.E, (Ω_map e).bar = (fun e => η₀.vMap '' (closure e ∩ H.V)) e ∧
      IsNaturalOrderFrom α_pt (Ω_map e) (subBd (D_map e)))
    (S_map : Set S → Society α β)
    (hS_map_G : ∀ e ∈ H.E, (S_map e).G = G_e e)
    (hS_map_Ω : ∀ e ∈ H.E, (S_map e).Ω = Ω_map e)
    (α_disc : Society α β → Set S)
    (hα_disc_eq : ∀ e ∈ H.E, α_disc (S_map e) = D_map e) :
    IsCompatibleWith G₀ H η₀ (S_map '' H.E) α_disc α_pt := by
  let V_e := fun e => η₀.vMap '' (closure e ∩ H.V)
  let S_seg := S_map '' H.E
  refine ⟨fun v hv _ => hα_pt_vMap v hv, ?_, ?_, ?_⟩
  · rintro _ ⟨e, he, rfl⟩
    rw [hα_disc_eq e he, (hD e he).2.2.2.1, hS_map_Ω e he, (hΩ_map e he).1]
    ext v
    simp only [mem_inter_iff, mem_sep_iff, mem_image]
    refine ⟨fun ⟨hv_cl, hvH⟩ => ⟨hvH, v, ⟨hv_cl, hvH⟩, rfl⟩,
      fun ⟨hvH, w, ⟨hw_cl, hwH⟩, hEq⟩ => ?_⟩
    have hwv : w = v := η₀.bijOn_v.injOn hwH hvH hEq
    exact ⟨hwv ▸ hw_cl, hvH⟩
  · rintro _ ⟨e, he, rfl⟩ v hvH
    rw [hα_disc_eq e he, hS_map_G e he, hV_Ge e]
    simp only [mem_image]
    refine ⟨fun hvD => ⟨v, (hD e he).2.2.1 ▸ ⟨hvD, hvH⟩, rfl⟩,
      fun ⟨w, ⟨hw_cl, hwH⟩, hEq⟩ => ?_⟩
    have hwv : w = v := η₀.bijOn_v.injOn hwH hvH hEq
    exact (hD e he).2.1 (hwv ▸ hw_cl)
  · rintro _ ⟨e, he, rfl⟩ f hfH
    rw [hα_disc_eq e he, hS_map_G e he, hE_Ge e he, mem_singleton_iff]
    refine ⟨fun hfD => ?_, fun hEq => ?_⟩
    · by_contra hne
      have hf_ne_e : f ≠ e := fun h => hne (h ▸ rfl)
      obtain ⟨p, hp⟩ := hfH.1
      have hp_in : p ∈ D_map e ∩ closure f := ⟨hfD hp, subset_closure hp⟩
      have hp_V : p ∈ H.V := ((hD e he).2.2.2.2.1 f hfH hf_ne_e hp_in).1.2
      exact (hfH.2.1 hp).2 hp_V
    · have hfe : f = e := η₀.bijOn_e.injOn hfH he hEq
      subst hfe
      exact subset_closure.trans (hD f hfH).2.1

private theorem edge_society_segregation_is_tangle_local
    {S : Type u}
    [TopologicalSpace S]
    [T2Space S]
    {α : Type v}
    {β : Type w}
    {G₀ : Graph α β}
    {H : Drawing S}
    {η₀ : SpanEmbedding H G₀}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {θ : ℕ}
    (hMetric : HasTangleMetric H θ T d)
    (hθ : 17 ≤ θ)
    (hends : ∀ e ∈ H.E, ∃ u v, u ≠ v ∧ closure e ∩ H.V = {u, v} ∧ IsLineWithEnds (closure e) u v)
    (D_map : Set S → Set S)
    (α_pt : α → S)
    (hVG₀ : V(G₀) = V(η₀.imageGraph))
    (hEG₀ : E(G₀) = E(η₀.imageGraph))
    (G_e : Set S → Graph α β)
    (hV_Ge : ∀ (e : Set S), V(G_e e) = (fun e => η₀.vMap '' (closure e ∩ H.V)) e)
    (hE_Ge : ∀ e ∈ H.E, E(G_e e) = {η₀.eMap e})
    (Ω_map : Set S → CyclicPerm α)
    (hΩ_map : ∀ e ∈ H.E, (Ω_map e).bar = (fun e => η₀.vMap '' (closure e ∩ H.V)) e ∧
      IsNaturalOrderFrom α_pt (Ω_map e) (subBd (D_map e)))
    (S_map : Set S → Society α β)
    (hS_map_G : ∀ e ∈ H.E, (S_map e).G = G_e e)
    (hS_map_Ω : ∀ e ∈ H.E, (S_map e).Ω = Ω_map e) :
    IsTangleLocal G₀ H η₀ T (S_map '' H.E) := by
  let V_e := fun e => η₀.vMap '' (closure e ∩ H.V)
  let S_seg := S_map '' H.E
  rintro _ ⟨e, he, rfl⟩ B hsepB hVB_eq
  rw [hS_map_G e he] at hsepB hVB_eq
  rw [hS_map_Ω e he, (hΩ_map e he).1] at hVB_eq
  have hV_B_eq : V(B) = V(G₀) := by
    have hsub : V_e e ⊆ V(B) := hVB_eq.ge.trans inter_subset_right
    have hu : V(G_e e) ∪ V(B) = V(G₀) := hsepB.2.2.1
    rw [hV_Ge e] at hu
    exact (union_eq_right.mpr hsub).symm.trans hu
  have hE_B_eq : E(B) = E(G₀) \ {η₀.eMap e} := by
    have hu : E(G_e e) ∪ E(B) = E(G₀) := hsepB.2.2.2.1
    have hd : Disjoint E(G_e e) E(B) := hsepB.2.2.2.2
    rw [hE_Ge e he] at hu hd
    ext f_G
    simp only [mem_sdiff, mem_singleton_iff]
    refine ⟨fun hfB => ⟨hsepB.2.1.edgeSet_mono hfB,
      fun hEq => Set.disjoint_left.mp hd (hEq ▸ mem_singleton _) hfB⟩,
      fun ⟨hfG₀, hne⟩ => (hu.symm ▸ hfG₀).resolve_left hne⟩
  have he_hyp : e ∈ H.toHypergraph.edgeSet :=
    (PaintingOrDrawing.toHypergraph_edgeSet (Γ := PaintingOrDrawing.drawing H)).symm ▸ he
  let A_H : Hypergraph S (Set S) := GM10.edgeHypergraph H.toHypergraph e
  let B_H : Hypergraph S (Set S) := H.toHypergraph.deleteEdges {e}
  have hVA_H : A_H.vertexSet = closure e ∩ H.V := ends_toHypergraph_eq he
  have hEA_H : A_H.edgeSet = {e} := rfl
  have hsep_H : H.toHypergraph.IsSeparation A_H B_H :=
    GM10.isSeparation_edgeHypergraph_deleteEdges he_hyp
  have hord_H : separationOrder A_H B_H < θ := by
    obtain ⟨u, v, _, hcap, _⟩ := hends e he
    have hV_inter : (A_H ∩ B_H).vertexSet = {u, v} := by
      change A_H.vertexSet ∩ H.V = {u, v}
      rw [hVA_H, Set.inter_assoc, Set.inter_self, hcap]
    rw [separationOrder, hV_inter]
    have hle2 : ({u, v} : Set S).ncard ≤ 2 := (ncard_insert_le u {v}).trans (by simp)
    omega
  have hAB_T : (A_H, B_H) ∈ T :=
    (hMetric.1.2.1.axiom1 hsep_H hord_H).resolve_right
      (fun hBA => hMetric.1.2.1.axiom3 hBA rfl)
  refine ⟨A_H, B_H, hsep_H, ?_, ?_, ?_, ?_, hAB_T⟩
  · rw [hS_map_G e he, hV_Ge e, hVA_H]
    ext v
    simp only [mem_inter_iff, mem_sep_iff]
    refine ⟨fun ⟨hve, hvH⟩ => ⟨hvH, v, ⟨hve, hvH⟩, rfl⟩,
      fun ⟨hvH, w, ⟨hwe, hwH⟩, hEq⟩ => ?_⟩
    have hwv : w = v := η₀.bijOn_v.injOn hwH hvH hEq
    exact ⟨hwv ▸ hwe, hvH⟩
  · rw [hV_B_eq]
    ext v
    change v ∈ H.V ↔ v ∈ H.V ∧ η₀.vMap v ∈ V(G₀)
    refine ⟨fun hvH => ⟨hvH, ?_⟩, fun h => h.1⟩
    rw [hVG₀]
    exact η₀.bijOn_v.mapsTo hvH
  · rw [hS_map_G e he, hE_Ge e he, hEA_H]
    ext f
    simp only [mem_singleton_iff, mem_sep_iff]
    exact ⟨fun hfe => ⟨hfe ▸ he, hfe ▸ rfl⟩, fun ⟨hfH, hEq⟩ => η₀.bijOn_e.injOn hfH he hEq⟩
  · rw [hE_B_eq]
    ext f
    change f ∈ H.E \ {e} ↔ f ∈ H.E ∧ η₀.eMap f ∈ E(G₀) \ {η₀.eMap e}
    simp only [mem_sdiff, mem_singleton_iff]
    refine ⟨fun ⟨hfH, hne⟩ => ⟨hfH, ⟨by rw [hEG₀]; exact η₀.bijOn_e.mapsTo hfH,
      fun hEq => hne (η₀.bijOn_e.injOn hfH he hEq)⟩⟩,
      fun ⟨hfH, _, hne⟩ => ⟨hfH, fun hfe => hne (hfe ▸ rfl)⟩⟩

/-- Base case `G₀ = η₀.imageGraph` in the proof of (10.1) (page 49): placing a thin closed disc
around each edge of `H` via `exists_edge_lens` yields a `T`-local 3-segregation of `G₀` and an
arrangement in `S` compatible with `H`. -/
private theorem base_case_10_1 {α : Type v} {β : Type w}
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {G₀ : Graph α β} {H : Drawing S} {η₀ : SpanEmbedding H G₀}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {θ : ℕ}
    (hV_fin : V(G₀).Finite) (hE_fin : E(G₀).Finite)
    (hRig : IsRigid H) (hMetric : HasTangleMetric H θ T d) (hθ : 17 ≤ θ)
    (hbase : G₀ = η₀.imageGraph) :
    ∃ (S_seg : Set (Society α β)) (α_disc : Society α β → Set S) (α_pt : α → S),
      IsThreeSegregation G₀ S_seg ∧ IsTangleLocal G₀ H η₀ T S_seg ∧
      IsSurfaceArrangement S_seg α_disc α_pt ∧ IsCompatibleWith G₀ H η₀ S_seg α_disc α_pt := by
  classical
  have : ConnectedSpace S := hConn
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hHE_ne : H.E.Nonempty := edgeSet_nonempty_of_isTangle hMetric.1.2.1 (by omega)
  obtain ⟨K, ins, hK, _, _⟩ := hMetric.2
  have hrf := GM11.regionFacts_of_radial ⟨hK.1, hK.2.1⟩ hS hK.2.2 hHE_ne
  have hends : ∀ e ∈ H.E, ∃ u v : S, u ≠ v ∧ closure e ∩ H.V = {u, v} ∧
      IsLineWithEnds (closure e) u v :=
    fun e he => no_loop_of_rigid_tangle hS hConn hRig hMetric (by omega) he
  have hcl_inter : ∀ e ∈ H.E, ∀ f ∈ H.E, e ≠ f → closure e ∩ closure f ⊆ H.V := by
    rintro e he f hf hef y ⟨h₁, h₂⟩
    by_contra hy
    exact hef (H.edge_eq_of_mem he hf ((H.closure_diff_V he).subset ⟨h₁, hy⟩)
      ((H.closure_diff_V hf).subset ⟨h₂, hy⟩))
  -- Construct thin closed discs `D e` around each `e ∈ H.E` inductively over `Finset (Set S)`
  have hex_lenses : ∀ (E_sub : Finset (Set S)), (E_sub : Set (Set S)) ⊆ H.E →
      ∃ D : Set S → Set S,
        ∀ e ∈ E_sub,
          IsClosedDisc (D e) ∧
          closure e ⊆ D e ∧
          D e ∩ H.V = closure e ∩ H.V ∧
          H.U ∩ subBd (D e) = closure e ∩ H.V ∧
          (∀ g ∈ H.E, g ≠ e → D e ∩ closure g ⊆ (closure e ∩ H.V) ∩ (closure g ∩ H.V)) ∧
          (∀ f ∈ E_sub, f ≠ e → D e ∩ D f ⊆ (closure e ∩ H.V) ∩ (closure f ∩ H.V)) := by
    exact exists_disjoint_edge_lenses (S := S) hS (H := H) hends hcl_inter
  obtain ⟨D_map, hD_map⟩ :=
    hex_lenses H.finite_edges.toFinset (fun e he => H.finite_edges.mem_toFinset.mp he)
  have hD : ∀ e ∈ H.E,
      IsClosedDisc (D_map e) ∧
      closure e ⊆ D_map e ∧
      D_map e ∩ H.V = closure e ∩ H.V ∧
      H.U ∩ subBd (D_map e) = closure e ∩ H.V ∧
      (∀ g ∈ H.E, g ≠ e → D_map e ∩ closure g ⊆ (closure e ∩ H.V) ∩ (closure g ∩ H.V)) ∧
      (∀ f ∈ H.E, f ≠ e → D_map e ∩ D_map f ⊆ (closure e ∩ H.V) ∩ (closure f ∩ H.V)) := by
    intro e he
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hD_map e (H.finite_edges.mem_toFinset.mpr he)
    exact ⟨h1, h2, h3, h4, h5, fun f hf hfe => h6 f (H.finite_edges.mem_toFinset.mpr hf) hfe⟩
  -- Define `α_pt : α → S` as the inverse of `η₀.vMap` on `V(G₀)`
  obtain ⟨e_some, he_some⟩ := hHE_ne
  obtain ⟨p_some, _⟩ := he_some.1
  let α_pt : α → S := fun x =>
    if hx : ∃ v ∈ H.V, η₀.vMap v = x then Classical.choose hx else p_some
  have hα_pt_vMap : ∀ v ∈ H.V, α_pt (η₀.vMap v) = v := by
    intro v hv
    have hex : ∃ w ∈ H.V, η₀.vMap w = η₀.vMap v := ⟨v, hv, rfl⟩
    have hch := Classical.choose_spec hex
    simp only [α_pt, hex, ↓reduceDIte]
    exact η₀.bijOn_v.injOn hch.1 hv hch.2
  have hα_pt_inj : InjOn α_pt V(G₀) := by
    intro x hx y hy hxy
    obtain ⟨u, huV, rfl⟩ := η₀.bijOn_v.surjOn (hbase ▸ hx)
    obtain ⟨v, hvV, rfl⟩ := η₀.bijOn_v.surjOn (hbase ▸ hy)
    rw [hα_pt_vMap u huV, hα_pt_vMap v hvV] at hxy
    rw [hxy]
  -- For each `e ∈ H.E`, define the single-edge subgraph `G_e` and natural order `Ω_e`
  have hVG₀ : V(G₀) = V(η₀.imageGraph) := congrArg (fun K => V(K)) hbase
  have hEG₀ : E(G₀) = E(η₀.imageGraph) := congrArg (fun K => E(K)) hbase
  let V_e : Set S → Set α := fun e => η₀.vMap '' (closure e ∩ H.V)
  have hVe_sub : ∀ e : Set S, V_e e ⊆ V(G₀) := by
    rintro e _ ⟨v, ⟨_, hvV⟩, rfl⟩
    rw [hVG₀]
    exact η₀.bijOn_v.mapsTo hvV
  let G_e : Set S → Graph α β := fun e => (G₀.induce (V_e e)).restrict {η₀.eMap e}
  have hGe_le : ∀ e : Set S, G_e e ≤ G₀ := fun e => restrict_le.trans (G₀.induce_le (hVe_sub e))
  have hV_Ge : ∀ e : Set S, V(G_e e) = V_e e := fun e => by simp [G_e]
  have hE_Ge : ∀ e ∈ H.E, E(G_e e) = {η₀.eMap e} := by
    intro e he
    ext f_G
    simp only [G_e, edgeSet_restrict, edgeSet_induce, mem_inter_iff, mem_singleton_iff]
    refine ⟨fun h => h.2, ?_⟩
    rintro rfl
    have he_G₀ : η₀.eMap e ∈ E(G₀) := by
      rw [hEG₀]
      exact η₀.bijOn_e.mapsTo he
    obtain ⟨x, y, hlink⟩ := G₀.exists_isLink_of_mem_edgeSet he_G₀
    obtain ⟨u, huV, rfl⟩ := η₀.bijOn_v.surjOn (hbase ▸ hlink.left_mem)
    obtain ⟨v, hvV, rfl⟩ := η₀.bijOn_v.surjOn (hbase ▸ hlink.right_mem)
    have hlink_H : η₀.imageGraph.IsLink (η₀.eMap e) (η₀.vMap u) (η₀.vMap v) := hbase ▸ hlink
    have hu_cl : u ∈ closure e := (η₀.inc_iff e he u huV).mp hlink_H.inc_left
    have hv_cl : v ∈ closure e := (η₀.inc_iff e he v hvV).mp hlink_H.inc_right
    exact ⟨⟨η₀.vMap u, η₀.vMap v, hlink, ⟨u, ⟨hu_cl, huV⟩, rfl⟩, ⟨v, ⟨hv_cl, hvV⟩, rfl⟩⟩, rfl⟩
  let Ω_triv : CyclicPerm α :=
    { bar := ∅
      finite_bar := finite_empty
      toFun := id
      bijOn := bijOn_id ∅
      single_orbit := fun _ h => h.elim }
  have hΩ_ex : ∀ e : Set S,
      ∃ Ω : CyclicPerm α,
        e ∈ H.E → Ω.bar = V_e e ∧ IsNaturalOrderFrom α_pt Ω (subBd (D_map e)) := by
    intro e
    by_cases he : e ∈ H.E
    · have hF : IsOArc (subBd (D_map e)) :=
        IsClosedDisc.subBd_eq_discBd hS (hD e he).1 ▸ (hD e he).1.isOArc_discBd
      have hY_fin : (V_e e).Finite := (H.finite_V.subset inter_subset_right).image η₀.vMap
      have hinj : InjOn α_pt (V_e e) := hα_pt_inj.mono (hVe_sub e)
      have hYF : MapsTo α_pt (V_e e) (subBd (D_map e)) := by
        rintro _ ⟨v, hv_cl, rfl⟩
        rw [hα_pt_vMap v hv_cl.2]
        exact ((hD e he).2.2.2.1 ▸ hv_cl).2
      obtain ⟨Ω, hbar, hNat⟩ := exists_natural_order_injOn hF hY_fin hinj hYF
      exact ⟨Ω, fun _ => ⟨hbar, hNat⟩⟩
    · exact ⟨Ω_triv, fun h => (he h).elim⟩
  choose Ω_map hΩ_map using hΩ_ex
  let S_map : Set S → Society α β := fun e =>
    if he : e ∈ H.E then
      ⟨G_e e, Ω_map e, hV_fin.subset (hGe_le e).vertexSet_mono,
        hE_fin.subset (hGe_le e).edgeSet_mono, (hΩ_map e he).1 ▸ (hV_Ge e).symm.subset⟩
    else
      ⟨⊥, Ω_triv, finite_empty, finite_empty, empty_subset _⟩
  have hS_map_G : ∀ e ∈ H.E, (S_map e).G = G_e e := by
    intro e he
    simp [S_map, he]
  have hS_map_Ω : ∀ e ∈ H.E, (S_map e).Ω = Ω_map e := by
    intro e he
    simp [S_map, he]
  have hS_map_inj : InjOn S_map H.E := by
    intro e₁ he₁ e₂ he₂ hEq
    have hE_eq : E((S_map e₁).G) = E((S_map e₂).G) := by rw [hEq]
    rw [hS_map_G e₁ he₁, hS_map_G e₂ he₂, hE_Ge e₁ he₁, hE_Ge e₂ he₂,
      singleton_eq_singleton_iff] at hE_eq
    exact η₀.bijOn_e.injOn he₁ he₂ hE_eq
  let S_seg : Set (Society α β) := S_map '' H.E
  let α_disc : Society α β → Set S := fun S₀ =>
    if h : ∃ e ∈ H.E, S_map e = S₀ then D_map (Classical.choose h) else ∅
  have hα_disc_eq : ∀ e ∈ H.E, α_disc (S_map e) = D_map e := by
    intro e he
    have hex : ∃ f ∈ H.E, S_map f = S_map e := ⟨e, he, rfl⟩
    have hch := Classical.choose_spec hex
    simp only [α_disc, hex, ↓reduceDIte]
    rw [hS_map_inj hch.1 he hch.2]
  have hsegV_sub : segregationVertices S_seg ⊆ V(G₀) := by
    rintro x hx
    simp only [segregationVertices, mem_iUnion, exists_prop] at hx
    obtain ⟨_, ⟨e, he, rfl⟩, hx_bar⟩ := hx
    exact (hGe_le e).vertexSet_mono (hS_map_G e he ▸ (S_map e).bar_subset hx_bar)
  have hS_seg_le : ∀ S₀ ∈ S_seg, S₀.G ≤ G₀ := by
    rintro _ ⟨e, he, rfl⟩
    rw [hS_map_G e he]
    exact hGe_le e
  have hS_seg_le_img : ∀ Q ∈ (fun S₀ : Society α β => S₀.G) '' S_seg, Q ≤ G₀ := by
    rintro _ ⟨S₀, hS₀, rfl⟩
    exact hS_seg_le S₀ hS₀
  have h3seg : IsThreeSegregation G₀ S_seg := by
    exact edge_societies_form_three_segregation (S := S) (α := α) (β := β) hS (G₀ := G₀) (H := H)
      (η₀ := η₀) hbase K hrf hends D_map α_pt G_e hV_Ge hE_Ge Ω_map hΩ_map S_map hS_map_G
      hS_map_Ω hS_seg_le hS_seg_le_img
  have hArr : IsSurfaceArrangement S_seg α_disc α_pt := by
    exact edge_lenses_form_surface_arrangement (S := S) (α := α) (β := β) hS (G₀ := G₀) (H := H)
      (η₀ := η₀) D_map hD α_pt hα_pt_vMap hα_pt_inj Ω_map hΩ_map S_map hS_map_Ω α_disc hα_disc_eq
      hsegV_sub
  have hComp : IsCompatibleWith G₀ H η₀ S_seg α_disc α_pt := by
    exact edge_lens_arrangement_is_compatible (S := S) (α := α) (β := β) (G₀ := G₀) (H := H) (η₀
      := η₀) D_map hD α_pt hα_pt_vMap G_e hV_Ge hE_Ge Ω_map hΩ_map S_map hS_map_G hS_map_Ω α_disc
      hα_disc_eq
  have hLoc : IsTangleLocal G₀ H η₀ T S_seg := by
    exact edge_society_segregation_is_tangle_local (S := S) (α := α) (β := β) (G₀ := G₀) (H := H)
      (η₀ := η₀) (T := T) (d := d) (θ := θ) hMetric hθ hends D_map α_pt hVG₀ hEG₀ G_e hV_Ge hE_Ge
      Ω_map hΩ_map S_map hS_map_G hS_map_Ω
  exact ⟨S_seg, α_disc, α_pt, h3seg, hLoc, hArr, hComp⟩

/-! ## Disc Replacement and Arrangement Gluing for (10.1) (pages 49–50) -/

omit [T2Space S] in
/-- Piecewise-linear strictly increasing interpolation between `a 0 < a 1 < ... < a (n + 1)` and
`b 0 < b 1 < ... < b (n + 1)`. -/
private theorem exists_strictMonoOn_interp (n : ℕ) (a b : ℕ → ℝ)
    (ha : StrictMono a) (hb : StrictMono b) :
    ∃ τ : ℝ → ℝ,
      ContinuousOn τ (Icc (a 0) (a (n + 1))) ∧
      StrictMonoOn τ (Icc (a 0) (a (n + 1))) ∧
      ∀ i ≤ n + 1, τ (a i) = b i := by
  induction n with
  | zero =>
    have ha01 : a 0 < a 1 := ha Nat.zero_lt_one
    have hb01 : b 0 < b 1 := hb Nat.zero_lt_one
    have hslope : 0 < (b 1 - b 0) / (a 1 - a 0) := div_pos (by linarith) (by linarith)
    let τ : ℝ → ℝ := fun x => b 0 + (b 1 - b 0) / (a 1 - a 0) * (x - a 0)
    refine ⟨τ, by fun_prop, ?_, ?_⟩
    · intro x _ y _ hxy
      dsimp only [τ]
      nlinarith
    · intro i hi
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hi with rfl | rfl
      · simp [τ]
      · dsimp only [τ]
        have hne : a 1 - a 0 ≠ 0 := by linarith
        rw [div_mul_cancel₀ _ hne]
        ring
  | succ n ih =>
    obtain ⟨τ₀, hcont₀, hmono₀, hval₀⟩ := ih
    have ha_step : a (n + 1) < a (n + 2) := ha (Nat.lt_succ_self (n + 1))
    have hb_step : b (n + 1) < b (n + 2) := hb (Nat.lt_succ_self (n + 1))
    have ha0_le : a 0 ≤ a (n + 1) := ha.monotone (Nat.zero_le (n + 1))
    have hslope : 0 < (b (n + 2) - b (n + 1)) / (a (n + 2) - a (n + 1)) :=
      div_pos (by linarith) (by linarith)
    let τ₁ : ℝ → ℝ := fun x =>
      b (n + 1) + (b (n + 2) - b (n + 1)) / (a (n + 2) - a (n + 1)) * (x - a (n + 1))
    let τ : ℝ → ℝ := fun x => if x ≤ a (n + 1) then τ₀ x else τ₁ x
    have hτ_left : ∀ x ≤ a (n + 1), τ x = τ₀ x := fun x hx => by simp [τ, hx]
    have hτ_right : ∀ x, a (n + 1) ≤ x → τ x = τ₁ x := by
      intro x hx
      rcases eq_or_lt_of_le hx with rfl | hlt
      · simp [τ, τ₁, hval₀ (n + 1) le_rfl]
      · have hnot : ¬ x ≤ a (n + 1) := not_le.mpr hlt
        simp [τ, hnot]
    have hcont₁ : ContinuousOn τ (Icc (a (n + 1)) (a (n + 2))) := by
      refine (by fun_prop : ContinuousOn τ₁ (Icc (a (n + 1)) (a (n + 2)))).congr ?_
      intro x hx
      exact hτ_right x hx.1
    have hcont₀' : ContinuousOn τ (Icc (a 0) (a (n + 1))) := by
      refine hcont₀.congr ?_
      intro x hx
      exact hτ_left x hx.2
    have hIcc_union : Icc (a 0) (a (n + 1)) ∪ Icc (a (n + 1)) (a (n + 2)) = Icc (a 0) (a (n + 2)) :=
      Icc_union_Icc_eq_Icc ha0_le ha_step.le
    refine ⟨τ, ?_, ?_, ?_⟩
    · rw [← hIcc_union]
      exact hcont₀'.union_of_isClosed hcont₁ isClosed_Icc isClosed_Icc
    · intro x hx y hy hxy
      by_cases hy_le : y ≤ a (n + 1)
      · have hx_le : x ≤ a (n + 1) := hxy.le.trans hy_le
        rw [hτ_left x hx_le, hτ_left y hy_le]
        exact hmono₀ ⟨hx.1, hx_le⟩ ⟨hy.1, hy_le⟩ hxy
      · have hy_gt : a (n + 1) < y := not_le.mp hy_le
        by_cases hx_le : x ≤ a (n + 1)
        · have h1 : τ x ≤ b (n + 1) := by
            rw [hτ_left x hx_le, ← hval₀ (n + 1) le_rfl]
            exact hmono₀.monotoneOn ⟨hx.1, hx_le⟩ ⟨ha0_le, le_rfl⟩ hx_le
          have h2 : b (n + 1) < τ y := by
            rw [hτ_right y hy_gt.le]
            dsimp only [τ₁]
            nlinarith
          exact h1.trans_lt h2
        · have hx_gt : a (n + 1) < x := not_le.mp hx_le
          rw [hτ_right x hx_gt.le, hτ_right y hy_gt.le]
          dsimp only [τ₁]
          nlinarith
    · intro i hi
      rcases Nat.of_le_succ hi with hi_le | rfl
      · rw [hτ_left (a i) (ha.monotone hi_le)]
        exact hval₀ i hi_le
      · rw [hτ_right (a (n + 2)) ha_step.le]
        dsimp only [τ₁]
        have hne : a (n + 2) - a (n + 1) ≠ 0 := by linarith
        rw [div_mul_cancel₀ _ hne]
        ring

omit [T2Space S] in
/-- Given `m ≥ 1` and strictly increasing sequences `t₁, t₂ : ℕ → ℝ` with
`t₁ i < t₁ 0 + 2π` and `t₂ i < t₂ 0 + 2π` for `i < m`, there is a homeomorphism
`h_circ : Circle ≃ₜ Circle` mapping `Circle.exp (t₁ i)` to `Circle.exp (t₂ i)` for all `i < m`. -/
private theorem exists_circle_homeo_matching_angles (m : ℕ) (hm : 1 ≤ m)
    (t₁ t₂ : ℕ → ℝ) (ht₁ : StrictMono t₁) (ht₂ : StrictMono t₂)
    (hbd₁ : ∀ i < m, t₁ i < t₁ 0 + 2 * Real.pi)
    (hbd₂ : ∀ i < m, t₂ i < t₂ 0 + 2 * Real.pi) :
    ∃ h_circ : Circle ≃ₜ Circle,
      ∀ i < m, h_circ (Circle.exp (t₁ i)) = Circle.exp (t₂ i) := by
  have hpi : 0 < 2 * Real.pi := by positivity
  let a : ℕ → ℝ := fun i =>
    if i < m then (t₁ i - t₁ 0) / (2 * Real.pi) else 1 + (i - m : ℕ)
  let b : ℕ → ℝ := fun i =>
    if i < m then (t₂ i - t₂ 0) / (2 * Real.pi) else 1 + (i - m : ℕ)
  have ha_mono : StrictMono a := by
    intro i j hij
    dsimp only [a]
    by_cases hj : j < m
    · have hi : i < m := hij.trans hj
      simp only [hi, hj, ↓reduceIte]
      exact div_lt_div_of_pos_right (by linarith [ht₁ hij]) hpi
    · by_cases hi : i < m
      · simp only [hi, hj, ↓reduceIte]
        have hlt : (t₁ i - t₁ 0) / (2 * Real.pi) < 1 := by
          rw [div_lt_one hpi]
          linarith [hbd₁ i hi]
        have hge : (0 : ℝ) ≤ (j - m : ℕ) := Nat.cast_nonneg _
        linarith
      · simp only [hi, hj, ↓reduceIte]
        have hsub : i - m < j - m := by omega
        have hcast : ((i - m : ℕ) : ℝ) < ((j - m : ℕ) : ℝ) := Nat.cast_lt.mpr hsub
        linarith
  have hb_mono : StrictMono b := by
    intro i j hij
    dsimp only [b]
    by_cases hj : j < m
    · have hi : i < m := hij.trans hj
      simp only [hi, hj, ↓reduceIte]
      exact div_lt_div_of_pos_right (by linarith [ht₂ hij]) hpi
    · by_cases hi : i < m
      · simp only [hi, hj, ↓reduceIte]
        have hlt : (t₂ i - t₂ 0) / (2 * Real.pi) < 1 := by
          rw [div_lt_one hpi]
          linarith [hbd₂ i hi]
        have hge : (0 : ℝ) ≤ (j - m : ℕ) := Nat.cast_nonneg _
        linarith
      · simp only [hi, hj, ↓reduceIte]
        have hsub : i - m < j - m := by omega
        have hcast : ((i - m : ℕ) : ℝ) < ((j - m : ℕ) : ℝ) := Nat.cast_lt.mpr hsub
        linarith
  have hm0 : 0 < m := hm
  have ha0 : a 0 = 0 := by simp [a, hm0]
  have hb0 : b 0 = 0 := by simp [b, hm0]
  have ham : a m = 1 := by simp [a]
  have hbm : b m = 1 := by simp [b]
  have hm_eq : m = (m - 1) + 1 := (Nat.sub_add_cancel hm).symm
  obtain ⟨τ, hcont, hmono, hval⟩ := exists_strictMonoOn_interp (m - 1) a b ha_mono hb_mono
  rw [← hm_eq, ha0, ham] at hcont hmono
  rw [← hm_eq] at hval
  have hτ0 : τ 0 = 0 := by
    have h := hval 0 (Nat.zero_le m)
    rwa [ha0, hb0] at h
  have hτ1 : τ 1 = τ 0 + 1 := by
    have h := hval m le_rfl
    rw [ham, hbm] at h
    rw [hτ0, zero_add, h]
  obtain ⟨h₀, _, hh₀⟩ := exists_circle_homeo hcont hmono hτ1
  let rot₁ : Circle ≃ₜ Circle := Homeomorph.mulRight (Circle.exp (-t₁ 0))
  let rot₂ : Circle ≃ₜ Circle := Homeomorph.mulRight (Circle.exp (t₂ 0))
  refine ⟨(rot₁.trans h₀).trans rot₂, fun i hi => ?_⟩
  have hai_mem : a i ∈ Icc (0 : ℝ) 1 := by
    rw [← ha0, ← ham]
    exact ⟨ha_mono.monotone (Nat.zero_le i), ha_mono.monotone (le_of_lt hi)⟩
  have hai_ee : ee (a i) = rot₁ (Circle.exp (t₁ i)) := by
    change Circle.exp (2 * Real.pi * a i) = Circle.exp (t₁ i) * Circle.exp (-t₁ 0)
    dsimp only [a]
    simp only [hi, ↓reduceIte]
    rw [mul_div_cancel₀ _ (ne_of_gt hpi), ← Circle.exp_add, sub_eq_add_neg]
  have hbi_ee : ee (b i) = Circle.exp (t₂ i - t₂ 0) := by
    dsimp only [ee, b]
    simp only [hi, ↓reduceIte]
    rw [mul_div_cancel₀ _ (ne_of_gt hpi)]
  simp only [Homeomorph.trans_apply]
  rw [← hai_ee, hh₀ (a i) hai_mem, hval i (le_of_lt hi), hbi_ee]
  change Circle.exp (t₂ i - t₂ 0) * Circle.exp (t₂ 0) = Circle.exp (t₂ i)
  rw [← Circle.exp_add, sub_add_cancel]

omit [T2Space S] in
/-- Given two closed discs `D₁` and `D₂` and a homeomorphism `e_bd : discBd D₁ ≃ₜ discBd D₂`,
there exist mutually-inverse continuous maps `f : S₁ → S₂` and `f' : S₂ → S₁` between `D₁` and `D₂`
extending `e_bd`. -/
private theorem exists_disc_extension_of_bd_homeo
    {S₁ : Type*} {S₂ : Type*} [TopologicalSpace S₁] [TopologicalSpace S₂]
    {D₁ : Set S₁} {D₂ : Set S₂} (hD₁ : IsClosedDisc D₁) (hD₂ : IsClosedDisc D₂)
    (e_bd : discBd D₁ ≃ₜ discBd D₂) :
    ∃ (f : S₁ → S₂) (f' : S₂ → S₁),
      MapsTo f D₁ D₂ ∧ MapsTo f' D₂ D₁ ∧
      ContinuousOn f D₁ ∧ ContinuousOn f' D₂ ∧
      LeftInvOn f' f D₁ ∧ LeftInvOn f f' D₂ ∧
      ∀ x : discBd D₁, f x.1 = (e_bd x).1 := by
  obtain ⟨h₁, g₁, c₁⟩ := hD₁.exists_isChart
  obtain ⟨h₂, g₂, c₂⟩ := hD₂.exists_isChart
  have hsub₁ := Surface.discBd_subset D₁
  have hsub₂ := Surface.discBd_subset D₂
  have hs_sub : Metric.sphere (0 : ℂ) 1 ⊆ Metric.closedBall (0 : ℂ) 1
    := Metric.sphere_subset_closedBall
  obtain ⟨e₁', he₁'⟩ := exists_homeomorph_image (c₁.hc.mono hsub₁)
    (by rw [c₁.bd]; exact c₁.gc.mono hs_sub) (c₁.gh.mono hsub₁)
  let e₁ : discBd D₁ ≃ₜ Metric.sphere (0 : ℂ) 1 := e₁'.trans (Homeomorph.setCongr c₁.bd)
  have he₁ : ∀ x : discBd D₁, (e₁ x).1 = h₁ x.1 := fun x => he₁' x
  obtain ⟨e₂', he₂'⟩ := exists_homeomorph_image (c₂.hc.mono hsub₂)
    (by rw [c₂.bd]; exact c₂.gc.mono hs_sub) (c₂.gh.mono hsub₂)
  let e₂ : discBd D₂ ≃ₜ Metric.sphere (0 : ℂ) 1 := e₂'.trans (Homeomorph.setCongr c₂.bd)
  have he₂ : ∀ x : discBd D₂, (e₂ x).1 = h₂ x.1 := fun x => he₂' x
  let e_sph : Metric.sphere (0 : ℂ) 1 ≃ₜ Metric.sphere (0 : ℂ) 1 := (e₁.symm.trans e_bd).trans e₂
  obtain ⟨h₀, k₀, m, hh₀⟩ := exists_bdMatch e_sph
  obtain ⟨ψ, χ, m', hψ⟩ := exists_bdMatch_closedInner oArc_sphere oArc_sphere m
  rw [closedInner_sphere] at m'
  obtain ⟨m_maps₁, m_maps₂, m_left, m_right, m_cont₁, m_cont₂⟩ := m'
  let f : S₁ → S₂ := g₂ ∘ ψ ∘ h₁
  let f' : S₂ → S₁ := g₁ ∘ χ ∘ h₂
  refine ⟨f, f', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact c₂.gm (m_maps₁ (c₁.hm hx))
  · intro y hy
    exact c₁.gm (m_maps₂ (c₂.hm hy))
  · exact c₂.gc.comp (m_cont₁.comp c₁.hc c₁.hm) (m_maps₁.comp c₁.hm)
  · exact c₁.gc.comp (m_cont₂.comp c₂.hc c₂.hm) (m_maps₂.comp c₂.hm)
  · intro x hx
    dsimp only [f, f', Function.comp_apply]
    rw [c₂.hg (m_maps₁ (c₁.hm hx)), m_left (c₁.hm hx), c₁.gh hx]
  · intro y hy
    dsimp only [f, f', Function.comp_apply]
    rw [c₁.hg (m_maps₂ (c₂.hm hy)), m_right (c₂.hm hy), c₂.gh hy]
  · intro x
    dsimp only [f, Function.comp_apply]
    have hx_sph : h₁ x.1 ∈ Metric.sphere (0 : ℂ) 1 := c₁.bd ▸ mem_image_of_mem h₁ x.2
    have he₁_x : (⟨h₁ x.1, hx_sph⟩ : Metric.sphere (0 : ℂ) 1) = e₁ x := Subtype.ext (he₁ x).symm
    rw [hψ hx_sph, hh₀ ⟨h₁ x.1, hx_sph⟩, he₁_x]
    simp only [e_sph, Homeomorph.trans_apply, Homeomorph.symm_apply_apply]
    rw [he₂ (e_bd x), c₂.gh (hsub₂ (e_bd x).2)]

omit [T2Space S] in
/-- Given `AgreesWithOArcHomeo ν Ω C φ`, `InjOn ν Ω.bar`, and a nonempty `Ω`-clockwise list `L`,
there is a strictly increasing sequence `t : ℕ → ℝ` with `t i < t 0 + 2π` and
`(φ (Circle.exp (t i))).1 = ν (L[i])` for all `i < L.length`. -/
private theorem exists_angles_of_isClockwiseSeq
    {S₁ : Type*} [TopologicalSpace S₁] {α : Type*}
    {ν : α → S₁} {Ω : CyclicPerm α} {C : Set S₁} {φ : Circle ≃ₜ C} {L : List α}
    (hA : AgreesWithOArcHomeo ν Ω C φ) (hinj : InjOn ν Ω.bar)
    (hcw : Ω.IsClockwiseSeq L) (hlen : 1 ≤ L.length) :
    ∃ t : ℕ → ℝ,
      StrictMono t ∧
      (∀ i < L.length, t i < t 0 + 2 * Real.pi) ∧
      ∀ (i : ℕ) (hi : i < L.length), (φ (Circle.exp (t i))).1 = ν (L[i]'hi) := by
  classical
  have hpi : 0 < 2 * Real.pi := Real.two_pi_pos
  let pt : ℝ → S₁ := fun t => (φ (Circle.exp t)).1
  have hpt_eq_iff : ∀ t₁ t₂ : ℝ, pt t₁ = pt t₂ ↔ ∃ m : ℤ, t₁ = t₂ + m * (2 * Real.pi) := by
    intro t₁ t₂
    constructor
    · intro h
      have h1 : φ (Circle.exp t₁) = φ (Circle.exp t₂) := Subtype.ext h
      exact Circle.exp_eq_exp.mp (φ.injective h1)
    · rintro ⟨m, rfl⟩
      have h2 : Circle.exp (t₂ + m * (2 * Real.pi)) = Circle.exp t₂ :=
        Circle.exp_eq_exp.mpr ⟨m, rfl⟩
      simp [pt, h2]
  have hpt_inj : ∀ t₀ : ℝ, InjOn pt (Ico t₀ (t₀ + 2 * Real.pi)) := by
    intro t₀ t₁ ht₁ t₂ ht₂ h
    obtain ⟨m, rfl⟩ := (hpt_eq_iff t₁ t₂).mp h
    have hm0 : m = 0 := by
      by_contra hm
      rcases lt_or_gt_of_ne hm with hlt | hgt
      · have hm_le : (m : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hlt
        have : (m : ℝ) * (2 * Real.pi) ≤ -1 * (2 * Real.pi) :=
          mul_le_mul_of_nonneg_right hm_le hpi.le
        linarith [ht₁.1, ht₂.2]
      · have hm_ge : (1 : ℝ) ≤ m := by exact_mod_cast hgt
        have : 1 * (2 * Real.pi) ≤ (m : ℝ) * (2 * Real.pi) :=
          mul_le_mul_of_nonneg_right hm_ge hpi.le
        linarith [ht₁.2, ht₂.1]
    simp [hm0]
  by_cases hlen3 : 3 ≤ L.length
  · have h012 : Ω.IsClockwise3 (L[0]'(by omega)) (L[1]'(by omega)) (L[2]'(by omega)) :=
      (Ω.mem_interval_of_lt hcw (by omega) (by omega) hlen3).2
    obtain ⟨t₀, t₁, t₂, ht01, ht12, ht20, hpt0, hpt1, hpt2⟩ :=
      hA.2 (L[0]'(by omega)) (L[1]'(by omega)) (L[2]'(by omega)) h012
    have hshift3 : ∀ v₁ v₂ : α, Ω.IsClockwise3 (L[0]'(by omega)) v₁ v₂ →
        ∃ u₁ u₂ : ℝ, t₀ < u₁ ∧ u₁ < u₂ ∧ u₂ < t₀ + 2 * Real.pi ∧
          pt u₁ = ν v₁ ∧ pt u₂ = ν v₂ := by
      intro v₁ v₂ hcw3
      obtain ⟨s₀, s₁, s₂, hs01, hs12, hs20, hs₀, hs₁, hs₂⟩ := hA.2 (L[0]'(by omega)) v₁ v₂ hcw3
      obtain ⟨m, hm⟩ := (hpt_eq_iff t₀ s₀).mp (hpt0.trans hs₀.symm)
      refine ⟨s₁ + m * (2 * Real.pi), s₂ + m * (2 * Real.pi), by linarith, by linarith, by linarith,
        ?_, ?_⟩
      · exact ((hpt_eq_iff _ s₁).mpr ⟨m, rfl⟩).trans hs₁
      · exact ((hpt_eq_iff _ s₂).mpr ⟨m, rfl⟩).trans hs₂
    have hex : ∀ (i : ℕ) (hi : i < L.length),
        ∃ u ∈ Ico t₀ (t₀ + 2 * Real.pi), pt u = ν (L[i]'hi) ∧ (0 < i → t₀ < u) := by
      intro i hi
      rcases Nat.eq_zero_or_pos i with rfl | hi_pos
      · exact ⟨t₀, ⟨le_rfl, by linarith⟩, hpt0, fun h => (Nat.lt_irrefl 0 h).elim⟩
      · by_cases hi1 : i = 1
        · subst hi1
          exact ⟨t₁, ⟨le_of_lt ht01, by linarith⟩, hpt1, fun _ => ht01⟩
        · have hcw_i : Ω.IsClockwise3 (L[0]'(by omega)) (L[1]'(by omega)) (L[i]'hi) :=
            (Ω.mem_interval_of_lt hcw (by omega) (by omega) hi).2
          obtain ⟨u₁, u₂, hu01, hu12, hu20, _, hu₂⟩ := hshift3 (L[1]'(by omega)) (L[i]'hi) hcw_i
          exact ⟨u₂, ⟨le_of_lt (hu01.trans hu12), hu20⟩, hu₂, fun _ => hu01.trans hu12⟩
    let t : ℕ → ℝ := fun i =>
      if hi : i < L.length then Classical.choose (hex i hi) else t₀ + 2 * Real.pi + i
    have ht_spec : ∀ (i : ℕ) (hi : i < L.length),
        t i ∈ Ico t₀ (t₀ + 2 * Real.pi) ∧ pt (t i) = ν (L[i]'hi) ∧ (0 < i → t₀ < t i) := by
      intro i hi
      have h_eq : t i = Classical.choose (hex i hi) := by
        dsimp only [t]; split_ifs; rfl
      rw [h_eq]
      exact Classical.choose_spec (hex i hi)
    have ht0_eq : t 0 = t₀ := by
      obtain ⟨ht0_mem, ht0_pt, _⟩ := ht_spec 0 (by omega)
      exact hpt_inj t₀ ht0_mem ⟨le_rfl, by linarith⟩ (ht0_pt.trans hpt0.symm)
    refine ⟨t, ?_, ?_, ?_⟩
    · intro i j hij
      by_cases hj : j < L.length
      · have hi : i < L.length := hij.trans hj
        rcases Nat.eq_zero_or_pos i with rfl | hi_pos
        · rw [ht0_eq]
          exact (ht_spec j hj).2.2 hij
        · have hcw_ij : Ω.IsClockwise3 (L[0]'(by omega)) (L[i]'hi) (L[j]'hj) :=
            (Ω.mem_interval_of_lt hcw hi_pos hij hj).2
          obtain ⟨u₁, u₂, hu01, hu12, hu20, hu₁, hu₂⟩ := hshift3 (L[i]'hi) (L[j]'hj) hcw_ij
          have hti : t i = u₁ :=
            hpt_inj t₀ (ht_spec i hi).1 ⟨le_of_lt hu01, hu12.trans hu20⟩
              ((ht_spec i hi).2.1.trans hu₁.symm)
          have htj : t j = u₂ :=
            hpt_inj t₀ (ht_spec j hj).1 ⟨le_of_lt (hu01.trans hu12), hu20⟩
              ((ht_spec j hj).2.1.trans hu₂.symm)
          linarith
      · by_cases hi : i < L.length
        · have hti := (ht_spec i hi).1.2
          have htj : t j = t₀ + 2 * Real.pi + j := by dsimp only [t]; split_ifs; rfl
          have hj_nonneg : (0 : ℝ) ≤ j := Nat.cast_nonneg j
          linarith
        · have hti : t i = t₀ + 2 * Real.pi + i := by dsimp only [t]; split_ifs; rfl
          have htj : t j = t₀ + 2 * Real.pi + j := by dsimp only [t]; split_ifs; rfl
          have hij_cast : (i : ℝ) < (j : ℝ) := Nat.cast_lt.mpr hij
          linarith
    · intro i hi
      rw [ht0_eq]
      exact (ht_spec i hi).1.2
    · intro i hi
      simpa [pt] using (ht_spec i hi).2.1
  · have hmem0 : L[0]'hlen ∈ Ω.bar := hcw.2.1 _ (List.getElem_mem hlen)
    obtain ⟨θ₀, hθ₀⟩ := Circle.exp_surjective (φ.symm ⟨ν (L[0]'hlen), hA.1 _ hmem0⟩)
    have hpt0 : (φ (Circle.exp θ₀)).1 = ν (L[0]'hlen) := by
      rw [hθ₀, φ.apply_symm_apply]
    rcases ( by omega : L.length = 1 ∨ L.length = 2 ) with hlen1 | hlen2
    · refine ⟨fun i => θ₀ + i, ?_, ?_, ?_⟩
      · intro i j hij
        have hij_cast : (i : ℝ) < (j : ℝ) := Nat.cast_lt.mpr hij
        linarith
      · intro i hi
        have hi0 : i = 0 := by omega
        subst hi0
        simp [hpi]
      · intro i hi
        have hi0 : i = 0 := by omega
        subst hi0
        simpa using hpt0
    · have h1_lt : 1 < L.length := by omega
      have hmem1 : L[1]'h1_lt ∈ Ω.bar := hcw.2.1 _ (List.getElem_mem h1_lt)
      obtain ⟨θ₁', hθ₁'⟩ := Circle.exp_surjective (φ.symm ⟨ν (L[1]'h1_lt), hA.1 _ hmem1⟩)
      obtain ⟨θ₁, hθ₁_mem, hθ₁_exp⟩ := Circle.periodic_exp.exists_mem_Ico hpi θ₁' θ₀
      have hpt1 : (φ (Circle.exp θ₁)).1 = ν (L[1]'h1_lt) := by
        rw [← hθ₁_exp, hθ₁', φ.apply_symm_apply]
      have hne01 : L[0]'hlen ≠ L[1]'h1_lt := by
        intro heq
        have := (List.Nodup.getElem_inj_iff hcw.1).mp heq
        omega
      have hθ0_lt_θ1 : θ₀ < θ₁ := by
        rcases eq_or_lt_of_le hθ₁_mem.1 with rfl | hlt
        · exfalso
          exact hne01 (hinj hmem0 hmem1 (hpt0.symm.trans hpt1))
        · exact hlt
      let t : ℕ → ℝ := fun i =>
        if i = 0 then θ₀ else if i = 1 then θ₁ else θ₀ + 2 * Real.pi + i
      refine ⟨t, ?_, ?_, ?_⟩
      · intro i j hij
        dsimp only [t]
        by_cases hj : j < 2
        · have hi0 : i = 0 := by omega
          have hj1 : j = 1 := by omega
          subst hi0; subst hj1
          simpa using hθ0_lt_θ1
        · by_cases hi : i < 2
          · have hj_nonneg : (0 : ℝ) ≤ j := Nat.cast_nonneg j
            rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
            · simp only [↓reduceIte, show j ≠ 0 by omega, show j ≠ 1 by omega]
              linarith
            · simp only [show (1 : ℕ) ≠ 0 by omega, ↓reduceIte, show j ≠ 0 by omega,
                show j ≠ 1 by omega]
              linarith [hθ₁_mem.2]
          · simp only [show i ≠ 0 by omega, show i ≠ 1 by omega, show j ≠ 0 by omega,
              show j ≠ 1 by omega, ↓reduceIte]
            have hij_cast : (i : ℝ) < (j : ℝ) := Nat.cast_lt.mpr hij
            linarith
      · intro i hi
        dsimp only [t]
        rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
        · simp [hpi]
        · simpa using hθ₁_mem.2
      · intro i hi
        dsimp only [t]
        rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
        · simpa using hpt0
        · simpa using hpt1

omit [T2Space S] in
/-- Given `AgreesWithOArcHomeo ν₁ Ω C₁ φ₁` and `AgreesWithOArcHomeo ν₂ Ω C₂ φ₂` with
`InjOn ν₁ Ω.bar` and `InjOn ν₂ Ω.bar`, there is a homeomorphism `e_bd : C₁ ≃ₜ C₂` mapping
`ν₁ v` to `ν₂ v` for every `v ∈ Ω.bar`. -/
private theorem exists_bd_homeo_of_agreesWithOArcHomeo
    {S₁ : Type*} {S₂ : Type*} [TopologicalSpace S₁] [TopologicalSpace S₂] {α : Type*}
    {ν₁ : α → S₁} {ν₂ : α → S₂} {Ω : CyclicPerm α} {C₁ : Set S₁} {C₂ : Set S₂}
    {φ₁ : Circle ≃ₜ C₁} {φ₂ : Circle ≃ₜ C₂}
    (hA₁ : AgreesWithOArcHomeo ν₁ Ω C₁ φ₁) (hA₂ : AgreesWithOArcHomeo ν₂ Ω C₂ φ₂)
    (hinj₁ : InjOn ν₁ Ω.bar) (hinj₂ : InjOn ν₂ Ω.bar) :
    ∃ e_bd : C₁ ≃ₜ C₂, ∀ v (hv : v ∈ Ω.bar), (e_bd ⟨ν₁ v, hA₁.1 v hv⟩).1 = ν₂ v := by
  rcases Ω.bar.eq_empty_or_nonempty with hemp | ⟨w₀, hw₀⟩
  · refine ⟨φ₁.symm.trans φ₂, fun v hv => ?_⟩
    rw [hemp] at hv
    exact hv.elim
  · obtain ⟨L, hL_len, hL_set, _, hcw⟩ := Ω.exists_isClockwiseSeq_of_subset_bar Subset.rfl hw₀
    have hlen_pos : 1 ≤ L.length := by
      have hw₀L : w₀ ∈ L := by
        have : w₀ ∈ {v | v ∈ L} := hL_set.symm ▸ hw₀
        exact this
      exact List.length_pos_of_mem hw₀L
    obtain ⟨t₁, ht₁_mono, ht₁_bd, ht₁_pt⟩ := exists_angles_of_isClockwiseSeq hA₁ hinj₁ hcw hlen_pos
    obtain ⟨t₂, ht₂_mono, ht₂_bd, ht₂_pt⟩ := exists_angles_of_isClockwiseSeq hA₂ hinj₂ hcw hlen_pos
    obtain ⟨h_circ, hh_circ⟩ :=
      exists_circle_homeo_matching_angles L.length hlen_pos t₁ t₂ ht₁_mono ht₂_mono ht₁_bd ht₂_bd
    refine ⟨φ₁.symm.trans (h_circ.trans φ₂), fun v hv => ?_⟩
    have hvL : v ∈ L := by
      have : v ∈ {x | x ∈ L} := hL_set.symm ▸ hv
      exact this
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hvL
    have hφ₁_eq : (⟨ν₁ (L[i]'hi), hA₁.1 _ hv⟩ : C₁) = φ₁ (Circle.exp (t₁ i)) :=
      Subtype.ext (ht₁_pt i hi).symm
    simp only [Homeomorph.trans_apply]
    rw [hφ₁_eq, φ₁.symm_apply_apply, hh_circ i hi, ht₂_pt i hi]

private theorem embedded_cell_boundary_is_image
    {S : Type u}
    [TopologicalSpace S]
    {α : Type v}
    {β : Type w}
    (hS : IsClosedSurface S)
    {Δ : Set S}
    [T2Space S]
    (S_seg_0 : Set (Society α β))
    (α_disc_D : Society α β → Set ↑Δ)
    (α_pt_D : α → ↑Δ)
    (harr_D : IsSurfaceArrangement S_seg_0 α_disc_D α_pt_D)
    (hdisc₁_closed : ∀ B ∈ S_seg_0, IsClosedDisc ((fun B => Subtype.val '' α_disc_D B) B) ∧ (fun B
      => Subtype.val '' α_disc_D B) B ⊆ Δ) :
    ∀ B ∈ S_seg_0, subBd ((fun B => Subtype.val '' α_disc_D B) B) = Subtype.val '' subBd (α_disc_D
      B) := by
  let disc₁ := fun B => Subtype.val '' α_disc_D B
  intro B hB
  obtain ⟨⟨φ_bdB⟩, _⟩ := harr_D.natural_order B hB
  let F_B : Set S := Subtype.val '' subBd (α_disc_D B)
  let g_F : Circle → F_B := fun z =>
    ⟨(φ_bdB z).1.1, mem_image_of_mem Subtype.val (φ_bdB z).2⟩
  have hg_F_cont : Continuous g_F := by fun_prop
  have hg_F_bij : Function.Bijective g_F := by
    refine ⟨fun z₁ z₂ h => ?_, fun y => ?_⟩
    · have h0 : (g_F z₁).1 = (g_F z₂).1 := congrArg Subtype.val h
      exact φ_bdB.injective (Subtype.ext (Subtype.ext h0))
    · obtain ⟨x, hx, hxy⟩ := y.2
      refine ⟨φ_bdB.symm ⟨x, hx⟩, Subtype.ext ?_⟩
      change ((φ_bdB (φ_bdB.symm ⟨x, hx⟩)).1).1 = y.1
      rw [φ_bdB.apply_symm_apply]
      exact hxy
  have hF_OArc : IsOArc F_B :=
    ⟨hg_F_cont.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g_F hg_F_bij)⟩
  have hF_sub : F_B ⊆ subBd (disc₁ B) := by
    rintro _ ⟨x, hx_bd, rfl⟩
    rw [← subBd_eq_frontier'] at hx_bd
    rw [← subBd_eq_frontier']
    have hx_disc : x ∈ α_disc_D B :=
      (harr_D.isClosedDisc B hB).1.isCompact.isClosed.closure_eq ▸ hx_bd.1
    refine ⟨subset_closure (mem_image_of_mem Subtype.val hx_disc), fun hx_int => ?_⟩
    have hU_open : IsOpen ((Subtype.val : ↥Δ → S) ⁻¹' interior (disc₁ B)) :=
      isOpen_interior.preimage continuous_subtype_val
    have hU_sub : (Subtype.val : ↥Δ → S) ⁻¹' interior (disc₁ B) ⊆ α_disc_D B := by
      intro y hy
      obtain ⟨z, hz, hzy⟩ := interior_subset hy
      exact Subtype.val_injective hzy ▸ hz
    exact hx_bd.2 (interior_maximal hU_sub hU_open hx_int)
  exact (eq_subBd_of_isOArc_subset hS (hdisc₁_closed B hB).1 hF_OArc hF_sub).symm

private theorem embedded_cell_boundary_retains_cyclic_order
    {S : Type u}
    [TopologicalSpace S]
    {α : Type v}
    {β : Type w}
    {Δ : Set S}
    [T2Space S]
    (S_seg_0 : Set (Society α β))
    (α_disc_D : Society α β → Set ↑Δ)
    (α_pt_D : α → ↑Δ)
    (harr_D : IsSurfaceArrangement S_seg_0 α_disc_D α_pt_D)
    (hdisc₁_subBd_eq : ∀ B ∈ S_seg_0, subBd ((fun B => Subtype.val '' α_disc_D B) B) = Subtype.val
      '' subBd (α_disc_D B)) :
    ∀ B ∈ S_seg_0, ∃ φ, AgreesWithOArcHomeo (fun v => ↑(α_pt_D v)) B.Ω (subBd ((fun B =>
      Subtype.val '' α_disc_D B) B)) φ := by
  let disc₁ := fun B => Subtype.val '' α_disc_D B
  let pt₁ := fun v => ↑(α_pt_D v)
  intro B hB
  obtain ⟨_, φ_bdB, hA_bdB⟩ := harr_D.natural_order B hB
  have hbd_eq := hdisc₁_subBd_eq B hB
  let g_F : Circle → subBd (disc₁ B) := fun z =>
    ⟨(φ_bdB z).1.1, hbd_eq.symm ▸ mem_image_of_mem Subtype.val (φ_bdB z).2⟩
  have hg_F_cont : Continuous g_F := by fun_prop
  have hg_F_bij : Function.Bijective g_F := by
    refine ⟨fun z₁ z₂ h => ?_, fun y => ?_⟩
    · have h0 : (g_F z₁).1 = (g_F z₂).1 := congrArg Subtype.val h
      exact φ_bdB.injective (Subtype.ext (Subtype.ext h0))
    · have hy2 : y.1 ∈ Subtype.val '' subBd (α_disc_D B) := hbd_eq ▸ y.2
      obtain ⟨x, hx, hxy⟩ := hy2
      refine ⟨φ_bdB.symm ⟨x, hx⟩, Subtype.ext ?_⟩
      change ((φ_bdB (φ_bdB.symm ⟨x, hx⟩)).1).1 = y.1
      rw [φ_bdB.apply_symm_apply]
      exact hxy
  let φ_B_1 : Circle ≃ₜ subBd (disc₁ B) :=
    hg_F_cont.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g_F hg_F_bij)
  refine ⟨φ_B_1, fun v hv => hbd_eq.symm ▸ mem_image_of_mem Subtype.val (hA_bdB.1 v hv),
    fun v₁ v₂ v₃ hcw3 => ?_⟩
  obtain ⟨t₁, t₂, t₃, ht12, ht23, ht31, h1, h2, h3⟩ := hA_bdB.2 v₁ v₂ v₃ hcw3
  exact ⟨t₁, t₂, t₃, ht12, ht23, ht31,
    congrArg Subtype.val h1, congrArg Subtype.val h2, congrArg Subtype.val h3⟩

private theorem extended_cell_homeomorphism_preserves_boundary
    {S : Type u}
    [TopologicalSpace S]
    {α : Type v}
    {β : Type w}
    (hS : IsClosedSurface S)
    {Δ : Set S}
    (S_seg_0 : Set (Society α β))
    (f : S → S)
    (f' : S → S)
    (hf_maps : MapsTo f Δ Δ)
    (hf_cont : ContinuousOn f Δ)
    (hf'_cont : ContinuousOn f' Δ)
    (hf_left : LeftInvOn f' f Δ)
    (disc₁ : Society α β → Set S)
    (hdisc₁_closed : ∀ B ∈ S_seg_0, IsClosedDisc (disc₁ B) ∧ disc₁ B ⊆ Δ) :
    ∀ B ∈ S_seg_0, IsClosedDisc (f '' disc₁ B) ∧ subBd (f '' disc₁ B) = f '' subBd (disc₁ B) := by
  intro B hB
  obtain ⟨hB_disc, hB_sub⟩ := hdisc₁_closed B hB
  have hf'_B : ContinuousOn f' (f '' disc₁ B) :=
    hf'_cont.mono (image_subset_iff.mpr fun x hx => hf_maps (hB_sub hx))
  obtain ⟨himg_disc, himg_bd⟩ :=
    hB_disc.image (hf_cont.mono hB_sub) hf'_B (hf_left.mono hB_sub)
  refine ⟨himg_disc, ?_⟩
  rw [IsClosedDisc.subBd_eq_discBd hS himg_disc, himg_bd,
    IsClosedDisc.subBd_eq_discBd hS hB_disc]

omit [T2Space S] in
/-- Applying `(8.1)` (`theorem_8_1_proof`) on `↥Δ` and transporting the resulting arrangement into
`Δ ⊆ S` so that it matches `α_pt` on `localSociety.Ω.bar`. -/
private theorem exists_surface_arrangement_in_disc_of_8_1 {α : Type v} {β : Type w}
    (hS : IsClosedSurface S)
    {Δ : Set S} (hΔ : IsClosedDisc Δ)
    (localSociety : Society α β)
    (hno_crooked2 : ∀ P_set : Set (Graph α β), localSociety.IsCrookedTransaction P_set
      → P_set.ncard ≠ 2)
    (α_pt : α → S) (hinj_bar : InjOn α_pt localSociety.Ω.bar)
    (hNat_bar : IsNaturalOrderFrom α_pt localSociety.Ω (subBd Δ)) :
    ∃ (S_seg_0 : Set (Society α β))
      (α_disc_0 : Society α β → Set S) (α_pt_0 : α → S),
      IsThreeSegregation localSociety.G S_seg_0 ∧
      localSociety.Ω.bar ⊆ segregationVertices S_seg_0 ∧
      IsSurfaceArrangement S_seg_0 α_disc_0 α_pt_0 ∧
      (∀ B ∈ S_seg_0, α_disc_0 B ⊆ Δ) ∧
      (∀ v ∈ localSociety.Ω.bar, α_pt_0 v = α_pt v) ∧
      (∀ v ∈ segregationVertices S_seg_0, α_pt_0 v ∈ Δ) ∧
      (∀ v ∈ segregationVertices S_seg_0, v ∉ localSociety.Ω.bar → α_pt_0 v ∈ Δ \ subBd Δ) ∧
      (∀ B ∈ S_seg_0, α_disc_0 B ∩ subBd Δ ⊆ α_pt_0 '' (B.Ω.bar ∩ localSociety.Ω.bar)) := by
  classical
  have : T2Space S := hS.2.1
  have ⟨φ_Δ⟩ := hΔ
  have : CompactSpace ↥Δ := isCompact_iff_compactSpace.mp hΔ.isCompact
  have hUniv_D : IsClosedDisc (univ : Set ↥Δ) :=
    ⟨φ_Δ.trans (Homeomorph.Set.univ ↥Δ).symm⟩
  have hSurf_D : IsSurface ↥Δ :=
    ⟨inferInstance, inferInstance, fun y => isManifoldPoint_of_disc hUniv_D Filter.univ_mem⟩
  obtain ⟨S_seg_0, α_disc_D, α_pt_D, h3seg_0, hbar_0, harr_D, hpull_D⟩ :=
    (theorem_8_1_proof.{v, w, u} localSociety hSurf_D ⟨φ_Δ.symm⟩).mp hno_crooked2
  let disc₁ : Society α β → Set S := fun B => Subtype.val '' (α_disc_D B)
  let pt₁ : α → S := fun v => (α_pt_D v).1
  have hinj_pt₁ : InjOn pt₁ (segregationVertices S_seg_0) :=
    Subtype.val_injective.comp_injOn harr_D.injOn_pts
  have hbd_S : subBd Δ = discBd Δ := IsClosedDisc.subBd_eq_discBd hS hΔ
  have hbd_Δ_eq : subBd Δ = Subtype.val '' (bd ↥Δ) := hbd_S
  -- Push `hpull_D.2 : IsNaturalOrderFrom α_pt_D localSociety.Ω (bd ↥Δ)` along `Subtype.val` to
  -- `subBd
  -- Δ`.
  obtain ⟨_, φ_D, hA_D⟩ := hpull_D.2
  let g_bd : Circle → subBd Δ := fun z =>
    ⟨(φ_D z).1.1, hbd_Δ_eq.symm ▸ mem_image_of_mem Subtype.val (φ_D z).2⟩
  have hg_bd_cont : Continuous g_bd := by fun_prop
  have hg_bd_bij : Function.Bijective g_bd := by
    refine ⟨fun z₁ z₂ h => ?_, fun y => ?_⟩
    · have h0 : (g_bd z₁).1 = (g_bd z₂).1 := congrArg Subtype.val h
      exact φ_D.injective (Subtype.ext (Subtype.ext h0))
    · have hy2 : y.1 ∈ Subtype.val '' (bd ↥Δ) := hbd_Δ_eq ▸ y.2
      obtain ⟨x, hx, hxy⟩ := hy2
      refine ⟨φ_D.symm ⟨x, hx⟩, Subtype.ext ?_⟩
      change ((φ_D (φ_D.symm ⟨x, hx⟩)).1).1 = y.1
      rw [φ_D.apply_symm_apply]
      exact hxy
  let φ₁ : Circle ≃ₜ subBd Δ :=
    hg_bd_cont.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g_bd hg_bd_bij)
  have hA₁ : AgreesWithOArcHomeo pt₁ localSociety.Ω (subBd Δ) φ₁ := by
    refine ⟨fun v hv => hbd_Δ_eq.symm ▸ mem_image_of_mem Subtype.val (hA_D.1 v hv),
      fun v₁ v₂ v₃ hcw3 => ?_⟩
    obtain ⟨t₁, t₂, t₃, ht12, ht23, ht31, h1, h2, h3⟩ := hA_D.2 v₁ v₂ v₃ hcw3
    exact ⟨t₁, t₂, t₃, ht12, ht23, ht31,
      congrArg Subtype.val h1, congrArg Subtype.val h2, congrArg Subtype.val h3⟩
  obtain ⟨_, φ₂, hA₂⟩ := hNat_bar
  obtain ⟨e_subBd, he_subBd⟩ :=
    exists_bd_homeo_of_agreesWithOArcHomeo hA₁ hA₂ (hinj_pt₁.mono hbar_0) hinj_bar
  let e_bd : discBd Δ ≃ₜ discBd Δ :=
    (Homeomorph.setCongr hbd_S.symm).trans (e_subBd.trans (Homeomorph.setCongr hbd_S))
  obtain ⟨f, f', hf_maps, hf'_maps, hf_cont, hf'_cont, hf_left, _, hf_bd⟩ :=
    exists_disc_extension_of_bd_homeo hΔ hΔ e_bd
  have hf_subBd : ∀ x (hx : x ∈ subBd Δ), f x = (e_subBd ⟨x, hx⟩).1 := by
    intro x hx
    have hx' : x ∈ discBd Δ := hbd_S ▸ hx
    exact hf_bd ⟨x, hx'⟩
  have hf_mem_subBd_iff : ∀ x ∈ Δ, f x ∈ subBd Δ ↔ x ∈ subBd Δ := by
    intro x hx
    constructor
    · intro hfx
      have hfx' : f x ∈ discBd Δ := hbd_S ▸ hfx
      let x₀ : discBd Δ := e_bd.symm ⟨f x, hfx'⟩
      have hx₀_eq : f x₀.1 = f x := by
        rw [hf_bd x₀, e_bd.apply_symm_apply]
      have hx_eq : x₀.1 = x := hf_left.injOn (Surface.discBd_subset Δ x₀.2) hx hx₀_eq
      rw [← hx_eq, hbd_S]
      exact x₀.2
    · intro hx_bd
      rw [hf_subBd x hx_bd]
      exact (e_subBd ⟨x, hx_bd⟩).2
  -- Establish closed-disc and boundary properties of `(disc₁, pt₁)` in `Δ ⊆ S`.
  have hdisc₁_closed : ∀ B ∈ S_seg_0, IsClosedDisc (disc₁ B) ∧ disc₁ B ⊆ Δ := by
    intro B hB
    obtain ⟨⟨φ_B⟩, _⟩ := harr_D.isClosedDisc B hB
    let g_B : ClosedUnitDisc → disc₁ B := fun z =>
      ⟨(φ_B z).1.1, mem_image_of_mem Subtype.val (φ_B z).2⟩
    have hg_B_cont : Continuous g_B := by fun_prop
    have hg_B_bij : Function.Bijective g_B := by
      refine ⟨fun z₁ z₂ h => ?_, fun y => ?_⟩
      · have h0 : (g_B z₁).1 = (g_B z₂).1 := congrArg Subtype.val h
        exact φ_B.injective (Subtype.ext (Subtype.ext h0))
      · obtain ⟨x, hx, hxy⟩ := y.2
        refine ⟨φ_B.symm ⟨x, hx⟩, Subtype.ext ?_⟩
        change ((φ_B (φ_B.symm ⟨x, hx⟩)).1).1 = y.1
        rw [φ_B.apply_symm_apply]
        exact hxy
    exact ⟨⟨hg_B_cont.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g_B hg_B_bij)⟩,
      by rintro _ ⟨x, _, rfl⟩; exact x.2⟩
  have hdisc₁_subBd_eq : ∀ B ∈ S_seg_0,
      subBd (disc₁ B) = Subtype.val '' subBd (α_disc_D B) := by
    exact embedded_cell_boundary_is_image (S := S) (α := α) (β := β) hS (Δ := Δ) S_seg_0 α_disc_D
      α_pt_D harr_D hdisc₁_closed
  have hdisc₁_bd : ∀ B ∈ S_seg_0, ∃ φ : Circle ≃ₜ subBd (disc₁ B),
      AgreesWithOArcHomeo pt₁ B.Ω (subBd (disc₁ B)) φ := by
    exact embedded_cell_boundary_retains_cyclic_order (S := S) (α := α) (β := β) (Δ := Δ) S_seg_0
      α_disc_D α_pt_D harr_D hdisc₁_subBd_eq
  have hdisc₁_inter_bd : ∀ B ∈ S_seg_0,
      disc₁ B ∩ subBd Δ ⊆ pt₁ '' (B.Ω.bar ∩ localSociety.Ω.bar) := by
    rintro B hB _ ⟨⟨x, hxB, rfl⟩, hx_bdΔ⟩
    have hx_bdD : x.1 ∈ Subtype.val '' (bd ↥Δ) := hbd_Δ_eq ▸ hx_bdΔ
    obtain ⟨y, hy_bdD, hyx⟩ := hx_bdD
    have hy_eq : y = x := Subtype.val_injective hyx
    subst hy_eq
    obtain ⟨w, hwB, hwx⟩ := harr_D.inter_bd B hB ⟨hxB, hy_bdD⟩
    have hw_star : w ∈ localSociety.Ω.bar := by
      rw [hpull_D.1]
      exact ⟨mem_biUnion hB hwB, hwx ▸ hy_bdD⟩
    exact ⟨w, ⟨hwB, hw_star⟩, congrArg Subtype.val hwx⟩
  have hdisc₁_inter : ∀ B₁ ∈ S_seg_0, ∀ B₂ ∈ S_seg_0, B₁ ≠ B₂ →
      disc₁ B₁ ∩ disc₁ B₂ ⊆ pt₁ '' (B₁.Ω.bar ∩ B₂.Ω.bar) := by
    rintro B₁ hB₁ B₂ hB₂ hne _ ⟨⟨x₁, hx₁, rfl⟩, ⟨x₂, hx₂, hx_eq⟩⟩
    have hx12 : x₁ = x₂ := Subtype.val_injective hx_eq.symm
    subst hx12
    obtain ⟨v, hv, hxv⟩ := harr_D.inter_discs B₁ hB₁ B₂ hB₂ hne ⟨hx₁, hx₂⟩
    exact ⟨v, hv, congrArg Subtype.val hxv⟩
  have hpt₁_mem : ∀ v ∈ segregationVertices S_seg_0, pt₁ v ∈ Δ := fun v _ => (α_pt_D v).2
  -- Push `(disc₁, pt₁)` along `f : Δ → Δ`.
  let α_disc_0 : Society α β → Set S := fun B => f '' disc₁ B
  let α_pt_0 : α → S := fun v => f (pt₁ v)
  have hB_img : ∀ B ∈ S_seg_0,
      IsClosedDisc (α_disc_0 B) ∧ subBd (α_disc_0 B) = f '' subBd (disc₁ B) := by
    exact extended_cell_homeomorphism_preserves_boundary (S := S) (α := α) (β := β) hS (Δ := Δ)
      S_seg_0 f f' hf_maps hf_cont hf'_cont hf_left disc₁ hdisc₁_closed
  refine ⟨S_seg_0, α_disc_0, α_pt_0, h3seg_0, hbar_0, ⟨?_, ?_, ?_, ?_, ?_⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · -- `isClosedDisc`
    intro B hB
    obtain ⟨hdisc_B, hbd_B⟩ := hB_img B hB
    refine ⟨hdisc_B, fun x hx => ?_⟩
    obtain ⟨φ_B, hA_B⟩ := hdisc₁_bd B hB
    rw [hbd_B]
    exact mem_image_of_mem f (hA_B.1 x hx)
  · -- `inter_discs`
    rintro B₁ hB₁ B₂ hB₂ hne _ ⟨⟨x₁, hx₁, rfl⟩, ⟨x₂, hx₂, hx_eq⟩⟩
    have hx12 : x₁ = x₂ :=
      hf_left.injOn ((hdisc₁_closed B₁ hB₁).2 hx₁) ((hdisc₁_closed B₂ hB₂).2 hx₂) hx_eq.symm
    subst hx12
    obtain ⟨v, hv, hxv⟩ := hdisc₁_inter B₁ hB₁ B₂ hB₂ hne ⟨hx₁, hx₂⟩
    exact ⟨v, hv, congrArg f hxv⟩
  · -- `inter_bd`
    rintro B _ x ⟨_, hxbd⟩
    exact (hxbd (hS.2.2 x)).elim
  · -- `injOn_pts`
    intro u hu v hv huv
    exact hinj_pt₁ hu hv (hf_left.injOn (hpt₁_mem u hu) (hpt₁_mem v hv) huv)
  · -- `natural_order`
    intro B hB
    obtain ⟨hdisc_B, hbd_B⟩ := hB_img B hB
    obtain ⟨φ_B, hA_B⟩ := hdisc₁_bd B hB
    have hsub_B : subBd (disc₁ B) ⊆ Δ := by
      rw [IsClosedDisc.subBd_eq_discBd hS (hdisc₁_closed B hB).1]
      exact (Surface.discBd_subset (disc₁ B)).trans (hdisc₁_closed B hB).2
    have hf'_bdB : ContinuousOn f' (f '' subBd (disc₁ B)) :=
      hf'_cont.mono (image_subset_iff.mpr fun x hx => hf_maps (hsub_B hx))
    obtain ⟨e_B, he_B⟩ := exists_homeomorph_image (hf_cont.mono hsub_B) hf'_bdB
      (hf_left.mono hsub_B)
    let φ_B_S : Circle ≃ₜ subBd (α_disc_0 B) :=
      φ_B.trans (e_B.trans (Homeomorph.setCongr hbd_B.symm))
    refine ⟨⟨φ_B_S⟩, φ_B_S, ?_, ?_⟩
    · intro v hv
      rw [hbd_B]
      exact mem_image_of_mem f (hA_B.1 v hv)
    · intro v₁ v₂ v₃ hcw3
      obtain ⟨t₁, t₂, t₃, ht12, ht23, ht31, h1, h2, h3⟩ := hA_B.2 v₁ v₂ v₃ hcw3
      refine ⟨t₁, t₂, t₃, ht12, ht23, ht31, ?_, ?_, ?_⟩
      · exact (he_B (φ_B (Circle.exp t₁))).trans (congrArg f h1)
      · exact (he_B (φ_B (Circle.exp t₂))).trans (congrArg f h2)
      · exact (he_B (φ_B (Circle.exp t₃))).trans (congrArg f h3)
  · -- `∀ B ∈ S_seg_0, α_disc_0 B ⊆ Δ`
    intro B hB
    exact image_subset_iff.mpr fun x hx => hf_maps ((hdisc₁_closed B hB).2 hx)
  · -- `∀ v ∈ localSociety.Ω.bar, α_pt_0 v = α_pt v`
    intro v hv
    dsimp only [α_pt_0]
    rw [hf_subBd (pt₁ v) (hA₁.1 v hv), he_subBd v hv]
  · -- `∀ v ∈ segregationVertices S_seg_0, α_pt_0 v ∈ Δ`
    intro v hv
    exact hf_maps (hpt₁_mem v hv)
  · -- `∀ v ∈ segregationVertices S_seg_0, v ∉ localSociety.Ω.bar → α_pt_0 v ∈ Δ \ subBd Δ`
    intro v hv hv_not
    refine ⟨hf_maps (hpt₁_mem v hv), fun hbd => ?_⟩
    have hx_bd : pt₁ v ∈ subBd Δ := (hf_mem_subBd_iff (pt₁ v) (hpt₁_mem v hv)).mp hbd
    rcases mem_iUnion₂.mp hv with ⟨B, hB, hvB⟩
    obtain ⟨φ_B, hA_B⟩ := hdisc₁_bd B hB
    have hsub : subBd (disc₁ B) ⊆ disc₁ B := by
      rw [IsClosedDisc.subBd_eq_discBd hS (hdisc₁_closed B hB).1]
      exact Surface.discBd_subset (disc₁ B)
    have hmem_inter : pt₁ v ∈ disc₁ B ∩ subBd Δ := ⟨hsub (hA_B.1 v hvB), hx_bd⟩
    obtain ⟨w, ⟨hwB, hwS⟩, hw_eq⟩ := hdisc₁_inter_bd B hB hmem_inter
    have hw_seg : w ∈ segregationVertices S_seg_0 := mem_biUnion hB hwB
    have hvw : w = v := hinj_pt₁ hw_seg hv hw_eq
    exact hv_not (hvw ▸ hwS)
  · -- `∀ B ∈ S_seg_0, α_disc_0 B ∩ subBd Δ ⊆ α_pt_0 '' (B.Ω.bar ∩ localSociety.Ω.bar)`
    rintro B hB _ ⟨⟨x, hxB, rfl⟩, hy_bd⟩
    have hx_Δ : x ∈ Δ := (hdisc₁_closed B hB).2 hxB
    have hx_bd : x ∈ subBd Δ := (hf_mem_subBd_iff x hx_Δ).mp hy_bd
    obtain ⟨v, hv, hxv⟩ := hdisc₁_inter_bd B hB ⟨hxB, hx_bd⟩
    exact ⟨v, hv, congrArg f hxv⟩

/-- The glued arrangement `(α'_disc, α'_pt)` on `S_seg' = S_seg₂ ∪ S_seg*` in the proof of
`(10.1)` (page 50):
"For $v \in V(\mathscr{S}')$, define $\alpha'(v) = \alpha(v)$ if $v \in V(\mathscr{S}_2)$,
and $\alpha'(v) = \alpha^*(v)$ otherwise. For $(A, \Omega) \in \mathscr{S}'$, define
$\alpha'(A, \Omega) = \alpha(A, \Omega)$ if $(A, \Omega) \in \mathscr{S}_2$, and $\alpha'(A,
\Omega) = \alpha^*(A, \Omega)$ otherwise." -/
noncomputable def gluedArrangementDisc {S : Type u} {α : Type v} {β : Type w}
    (S_seg₂ : Set (Society α β))
    (α_disc α_disc_star : Society α β → Set S) : Society α β → Set S :=
  open Classical in
  fun S₀ => if S₀ ∈ S_seg₂ then α_disc S₀ else α_disc_star S₀

/-- The glued point map `α'_pt` on `V(S_seg')` in the proof of `(10.1)` (page 50). -/
noncomputable def gluedArrangementPt {S : Type u} {α : Type v} {β : Type w}
    (S_seg₂ : Set (Society α β))
    (α_pt α_pt_star : α → S) : α → S :=
  open Classical in
  fun v => if v ∈ segregationVertices S_seg₂ then α_pt v else α_pt_star v

/-- If `subBd Δ` is `α`-normal for a surface arrangement `(S_seg, α_disc, α_pt)` on a closed
surface `S`, and `A ∈ S_seg` satisfies `¬ α_disc A ⊆ Δ`, then `α_disc A ∩ Δ ⊆ subBd Δ` and
`α_disc A ∩ Δ ⊆ α_pt '' A.Ω.bar`. -/
private theorem inter_disc_subset_subBd_of_not_subset {α : Type v} {β : Type w}
    (hS : IsClosedSurface S)
    {S_seg : Set (Society α β)} {α_disc : Society α β → Set S} {α_pt : α → S}
    (hArr : IsSurfaceArrangement S_seg α_disc α_pt)
    {Δ : Set S} (hΔ : IsClosedDisc Δ)
    (hNorm : IsArrangementNormal S_seg α_disc α_pt (subBd Δ))
    {A : Society α β} (hA : A ∈ S_seg) (hnot_sub : ¬ α_disc A ⊆ Δ) :
    α_disc A ∩ Δ ⊆ subBd Δ ∧ α_disc A ∩ Δ ⊆ α_pt '' A.Ω.bar := by
  let D := α_disc A
  obtain ⟨hD, hD_bd⟩ := hArr.isClosedDisc A hA
  have hfr_D : frontier D = subBd D := (GM11.subBd_eq_frontier D).symm
  have hfr_Δ : frontier Δ = subBd Δ := (GM11.subBd_eq_frontier Δ).symm
  have hdis_fr : Disjoint (D \ frontier D) (frontier Δ) := by
    rw [hfr_D, hfr_Δ, Set.disjoint_left]
    rintro x ⟨hxD, hx_not_bd⟩ hx_bdΔ
    obtain ⟨v, hv, rfl⟩ := hNorm A hA ⟨hx_bdΔ, hxD⟩
    exact hx_not_bd (hD_bd v hv)
  have hdis_Δ : Disjoint (D \ frontier D) Δ := by
    refine (subset_or_disjoint_of_frontier hΔ.isClosed
      (IsClosedDisc.isPreconnected_diff_frontier hS hD) hdis_fr).resolve_left ?_
    intro hsub
    exact hnot_sub ((IsClosedDisc.subset_closure_diff_frontier hS hD).trans
      (hΔ.isClosed.closure_subset_iff.mpr hsub))
  have hD_compl : D ⊆ closure Δᶜ :=
    (IsClosedDisc.subset_closure_diff_frontier hS hD).trans
      (closure_mono (Set.disjoint_left.mp hdis_Δ))
  have hsub_bd : D ∩ Δ ⊆ subBd Δ := by
    rintro x ⟨hxD, hxΔ⟩
    rw [← hfr_Δ, frontier_eq_closure_inter_closure]
    exact ⟨subset_closure hxΔ, hD_compl hxD⟩
  refine ⟨hsub_bd, fun x hx => hNorm A hA ⟨hsub_bd hx, hx.1⟩⟩

/-- If `(A, Ω) ∈ S_seg` and `¬ α_disc A ⊆ Δ`, then `E(localSociety.G ∩ A) = ∅` and
`V(localSociety.G ∩ A) ⊆ localSociety.Ω.bar` (Graph Minors XIV, Section 10, page 50). -/
private theorem claim_1_of_10_1 {α : Type v} {β : Type w}
    (hS : IsClosedSurface S)
    {G₀ G' J : Graph α β} {H : Drawing S} {η₀ : SpanEmbedding H G₀} {η' : SpanEmbedding H G'}
    {S_seg : Set (Society α β)} {α_disc : Society α β → Set S} {α_pt : α → S}
    {Δ : Set S} {localSociety : Society α β}
    (hJ : IsBridge G₀ η₀.imageGraph J)
    (hG'_le : G' ≤ G₀)
    (hDisj_E : Disjoint E(G') E(J))
    (hInter_V : V(G') ∩ V(J) ⊆ V(η₀.imageGraph))
    (hη'_v : ∀ v ∈ H.V, η'.vMap v = η₀.vMap v)
    (hSeg : IsThreeSegregation G' S_seg)
    (hArr : IsSurfaceArrangement S_seg α_disc α_pt)
    (hComp : IsCompatibleWith G' H η' S_seg α_disc α_pt)
    (hΔ : IsClosedDisc Δ)
    (hNorm : IsArrangementNormal S_seg α_disc α_pt (subBd Δ))
    (hVJ_Δ : ∀ v ∈ H.V, η₀.vMap v ∈ V(J) → v ∈ Δ \ subBd Δ)
    (hsoc_star_G : localSociety.G = subgraphUnion G₀ J (arrangementPullbackGraph G' S_seg α_disc
      α_pt
      Δ))
    (hsoc_star_Ω : IsPullbackPerm S_seg α_pt (subBd Δ) localSociety.Ω)
    {A : Society α β} (hA : A ∈ S_seg) (hA_not : ¬ α_disc A ⊆ Δ) :
    Disjoint E(localSociety.G) E(A.G) ∧
    V(localSociety.G) ∩ V(A.G) ⊆ localSociety.Ω.bar := by
  let P_Δ := arrangementPullbackGraph G' S_seg α_disc α_pt Δ
  have hA_le : A.G ≤ G' := hSeg.1.le A hA
  have hP_le : P_Δ ≤ G' := restrict_le.trans (G'.induce_le inter_subset_right)
  have hseg_in_bar : ∀ {v' : α}, v' ∈ V(A.G) → v' ∈ segregationVertices S_seg → v' ∈ A.Ω.bar := by
    intro v' hv'A hv'seg
    obtain ⟨A', hA', hv'A'_bar⟩ := mem_iUnion₂.mp hv'seg
    by_cases hAA' : A = A'
    · subst hAA'; exact hv'A'_bar
    · exact (hSeg.1.vertex_inter_subset A hA A' hA' hAA' ⟨hv'A, A'.bar_subset hv'A'_bar⟩).1
  obtain ⟨hinter_subBd, _⟩ :=
    inter_disc_subset_subBd_of_not_subset hS hArr hΔ hNorm hA hA_not
  refine ⟨?_, ?_⟩
  · rw [hsoc_star_G, edgeSet_subgraphUnion hJ.2.1 (hP_le.trans hG'_le)]
    refine Set.disjoint_left.mpr ?_
    rintro e (heJ | heP) heA
    · exact Set.disjoint_left.mp hDisj_E (hA_le.edgeSet_mono heA) heJ
    · change e ∈ E(arrangementPullbackGraph G' S_seg α_disc α_pt Δ) at heP
      rw [arrangementPullbackGraph, edgeSet_restrict] at heP
      obtain ⟨A', ⟨hA'_S, hA'_sub⟩, heA'⟩ := mem_iUnion₂.mp heP.2
      have hAA'_ne : A ≠ A' := fun hEq => hA_not (hEq ▸ hA'_sub)
      exact Set.disjoint_left.mp (hSeg.1.edge_disjoint A hA A' hA'_S hAA'_ne) heA heA'
  · rintro x ⟨hx_star, hxA⟩
    rw [hsoc_star_G, vertexSet_subgraphUnion] at hx_star
    rcases hx_star with hxJ | hxP
    · exfalso
      have hxG' : x ∈ V(G') := hA_le.vertexSet_mono hxA
      obtain ⟨u, huH, rfl⟩ := η₀.bijOn_v.surjOn (hInter_V ⟨hxG', hxJ⟩)
      have hu_int : u ∈ Δ \ subBd Δ := hVJ_Δ u huH hxJ
      have hu_A : u ∈ α_disc A := by
        rw [hComp.inter_V_iff A hA u huH, hη'_v u huH]
        exact hxA
      exact hu_int.2 (hinter_subBd ⟨hu_A, hu_int.1⟩)
    · change x ∈ V(arrangementPullbackGraph G' S_seg α_disc α_pt Δ) at hxP
      rw [arrangementPullbackGraph, vertexSet_restrict, vertexSet_induce] at hxP
      have hx_seg_and_Δ : x ∈ segregationVertices S_seg ∧ α_pt x ∈ Δ := by
        rcases hxP.1 with hx_union | hx_seg_Δ
        · obtain ⟨A', ⟨hA'_S, hA'_sub⟩, hxA'⟩ := mem_iUnion₂.mp hx_union
          have hAA'_ne : A ≠ A' := fun hEq => hA_not (hEq ▸ hA'_sub)
          have hx_bars := hSeg.1.vertex_inter_subset A hA A' hA'_S hAA'_ne ⟨hxA, hxA'⟩
          have hx_bdA' : α_pt x ∈ subBd (α_disc A') := (hArr.isClosedDisc A' hA'_S).2 x hx_bars.2
          have hx_discA' : α_pt x ∈ α_disc A' :=
            (hArr.isClosedDisc A' hA'_S).1.isClosed.closure_subset_iff.mpr Subset.rfl hx_bdA'.1
          exact ⟨mem_biUnion hA hx_bars.1, hA'_sub hx_discA'⟩
        · exact hx_seg_Δ
      have hx_bar : x ∈ A.Ω.bar := hseg_in_bar hxA hx_seg_and_Δ.1
      have hx_bdA : α_pt x ∈ subBd (α_disc A) := (hArr.isClosedDisc A hA).2 x hx_bar
      have hx_discA : α_pt x ∈ α_disc A :=
        (hArr.isClosedDisc A hA).1.isClosed.closure_subset_iff.mpr Subset.rfl hx_bdA.1
      have hx_bdΔ : α_pt x ∈ subBd Δ := hinter_subBd ⟨hx_discA, hx_seg_and_Δ.2⟩
      rw [hsoc_star_Ω.1]
      exact ⟨hx_seg_and_Δ.1, hx_bdΔ⟩

private theorem replacement_bridge_pieces_form_three_segregation
    {S : Type u}
    [TopologicalSpace S]
    [T2Space S]
    {α : Type v}
    {β : Type w}
    (G₀ : Graph α β)
    (G' : Graph α β)
    (J : Graph α β)
    (H : Drawing S)
    (η₀ : SpanEmbedding H G₀)
    (η' : SpanEmbedding H G')
    (S_seg : Set (Society α β))
    (α_disc : Society α β → Set S)
    (α_pt : α → S)
    (Δ : Set S)
    (localSociety : Society α β)
    (hS : IsClosedSurface S)
    (hJ : IsBridge G₀ η₀.imageGraph J)
    (hG'_le : G' ≤ G₀)
    (hG₀_eq : G₀ = subgraphUnion G₀ G' J)
    (hDisj_E : Disjoint E(G') E(J))
    (hInter_V : V(G') ∩ V(J) ⊆ V(η₀.imageGraph))
    (hη'_v : ∀ v ∈ H.V, η'.vMap v = η₀.vMap v)
    (hSeg : IsThreeSegregation G' S_seg)
    (hArr : IsSurfaceArrangement S_seg α_disc α_pt)
    (hComp : IsCompatibleWith G' H η' S_seg α_disc α_pt)
    (hΔ : IsClosedDisc Δ)
    (hNorm : IsArrangementNormal S_seg α_disc α_pt (subBd Δ))
    (hVJ_Δ : ∀ v ∈ H.V, η₀.vMap v ∈ V(J) → v ∈ Δ \ subBd Δ)
    (hsoc_star_G : localSociety.G = subgraphUnion G₀ J (arrangementPullbackGraph G' S_seg α_disc
      α_pt
      Δ))
    (hsoc_star_Ω : IsPullbackPerm S_seg α_pt (subBd Δ) localSociety.Ω)
    (hP_le_G₀ : (arrangementPullbackGraph G' S_seg α_disc α_pt Δ) ≤ G₀)
    (S_seg_0 : Set (Society α β))
    (h3seg_0 : IsThreeSegregation localSociety.G S_seg_0)
    (hbar_0 : localSociety.Ω.bar ⊆ segregationVertices S_seg_0)
    (hS_seg'_eq : (({A | A ∈ S_seg ∧ ¬α_disc A ⊆ Δ}) ∪ (S_seg_0 \ ({A | A ∈ S_seg ∧ ¬α_disc A ⊆
      Δ}))) = ({A | A ∈ S_seg ∧ ¬α_disc A ⊆ Δ}) ∪ S_seg_0)
    (hFin' : (({A | A ∈ S_seg ∧ ¬α_disc A ⊆ Δ}) ∪ (S_seg_0 \ ({A | A ∈ S_seg ∧ ¬α_disc A ⊆
      Δ}))).Finite)
    (hLe' : ∀ B ∈ (({A | A ∈ S_seg ∧ ¬α_disc A ⊆ Δ}) ∪ (S_seg_0 \ ({A | A ∈ S_seg ∧ ¬α_disc A ⊆
      Δ}))), B.G ≤ G₀) :
    IsThreeSegregation G₀ (({A | A ∈ S_seg ∧ ¬α_disc A ⊆ Δ}) ∪ (S_seg_0 \ ({A | A ∈ S_seg ∧
      ¬α_disc A ⊆ Δ}))) := by
  let P_Δ := arrangementPullbackGraph G' S_seg α_disc α_pt Δ
  let S_seg₂ := {A | A ∈ S_seg ∧ ¬α_disc A ⊆ Δ}
  let S_seg_star := S_seg_0 \ S_seg₂
  let S_seg' := S_seg₂ ∪ S_seg_star
  refine ⟨⟨hFin', hLe', ?_, ?_, ?_⟩, ?_⟩
  · have hU_le : subgraphSUnion G₀ ((fun B : Society α β => B.G) '' S_seg') ≤ G₀ :=
      subgraphSUnion_le (by rintro _ ⟨B, hB, rfl⟩; exact hLe' B hB)
    have hV_G₀ : V(G₀) = V(G') ∪ V(J) :=
      (congrArg Graph.vertexSet hG₀_eq).trans (vertexSet_subgraphUnion G₀ G' J)
    have hE_G₀ : E(G₀) = E(G') ∪ E(J) :=
      (congrArg Graph.edgeSet hG₀_eq).trans (edgeSet_subgraphUnion hG'_le hJ.2.1)
    have hCover_star_V : ∀ {v : α}, v ∈ V(localSociety.G) → ∃ B ∈ S_seg', v ∈ V(B.G) := by
      intro v hv
      have hv_u : v ∈ V(subgraphSUnion localSociety.G ((fun B : Society α β => B.G) '' S_seg_0))
        := by
        rw [h3seg_0.1.union_eq]; exact hv
      rw [vertexSet_subgraphSUnion] at hv_u
      obtain ⟨_, ⟨B, hB, rfl⟩, hvB⟩ := mem_iUnion₂.mp hv_u
      refine ⟨B, ?_, hvB⟩
      change B ∈ S_seg₂ ∪ (S_seg_0 \ S_seg₂)
      exact hS_seg'_eq.symm ▸ (show B ∈ S_seg₂ ∪ S_seg_0 from Or.inr hB)
    have hCover_star_E : ∀ {e : β}, e ∈ E(localSociety.G) → ∃ B ∈ S_seg', e ∈ E(B.G) := by
      intro e he
      have he_u : e ∈ E(subgraphSUnion localSociety.G ((fun B : Society α β => B.G) '' S_seg_0))
        := by
        rw [h3seg_0.1.union_eq]; exact he
      rw [edgeSet_subgraphSUnion (by rintro _ ⟨B, hB, rfl⟩; exact h3seg_0.1.le B hB)] at he_u
      obtain ⟨_, ⟨B, hB, rfl⟩, heB⟩ := mem_iUnion₂.mp he_u
      refine ⟨B, ?_, heB⟩
      change B ∈ S_seg₂ ∪ (S_seg_0 \ S_seg₂)
      exact hS_seg'_eq.symm ▸ (show B ∈ S_seg₂ ∪ S_seg_0 from Or.inr hB)
    refine (Compatible.of_le_le hU_le le_rfl).ext ?_ ?_
    · ext v
      rw [vertexSet_subgraphSUnion]
      refine ⟨fun h => hU_le.vertexSet_mono (vertexSet_subgraphSUnion _ _ ▸ h), fun hvG₀ => ?_⟩
      rcases hV_G₀ ▸ hvG₀ with hvG' | hvJ
      · have hv_u : v ∈ V(subgraphSUnion G' ((fun A : Society α β => A.G) '' S_seg)) := by
          rw [hSeg.1.union_eq]; exact hvG'
        rw [vertexSet_subgraphSUnion] at hv_u
        obtain ⟨_, ⟨A, hA, rfl⟩, hvA⟩ := mem_iUnion₂.mp hv_u
        by_cases hA_sub : α_disc A ⊆ Δ
        · have hv_star : v ∈ V(localSociety.G) := by
            rw [hsoc_star_G, vertexSet_subgraphUnion]
            refine Or.inr ?_
            rw [arrangementPullbackGraph, vertexSet_restrict, vertexSet_induce]
            exact ⟨Or.inl (mem_iUnion₂.mpr ⟨A, ⟨hA, hA_sub⟩, hvA⟩), hvG'⟩
          obtain ⟨B, hB, hvB⟩ := hCover_star_V hv_star
          exact mem_iUnion₂.mpr ⟨B.G, ⟨B, hB, rfl⟩, hvB⟩
        · exact mem_iUnion₂.mpr ⟨A.G, ⟨A, Or.inl ⟨hA, hA_sub⟩, rfl⟩, hvA⟩
      · have hv_star : v ∈ V(localSociety.G) := by
          rw [hsoc_star_G, vertexSet_subgraphUnion]
          exact Or.inl hvJ
        obtain ⟨B, hB, hvB⟩ := hCover_star_V hv_star
        exact mem_iUnion₂.mpr ⟨B.G, ⟨B, hB, rfl⟩, hvB⟩
    · ext e
      rw [edgeSet_subgraphSUnion (by rintro _ ⟨B, hB, rfl⟩; exact hLe' B hB)]
      refine ⟨fun h => ?_, fun heG₀ => ?_⟩
      · obtain ⟨_, ⟨B, hB, rfl⟩, heB⟩ := mem_iUnion₂.mp h
        exact (hLe' B hB).edgeSet_mono heB
      · rcases hE_G₀ ▸ heG₀ with heG' | heJ
        · have he_u : e ∈ E(subgraphSUnion G' ((fun A : Society α β => A.G) '' S_seg)) := by
            rw [hSeg.1.union_eq]; exact heG'
          rw [edgeSet_subgraphSUnion (by rintro _ ⟨A, hA, rfl⟩; exact hSeg.1.le A hA)] at he_u
          obtain ⟨_, ⟨A, hA, rfl⟩, heA⟩ := mem_iUnion₂.mp he_u
          by_cases hA_sub : α_disc A ⊆ Δ
          · have he_star : e ∈ E(localSociety.G) := by
              rw [hsoc_star_G, edgeSet_subgraphUnion hJ.2.1 hP_le_G₀]
              refine Or.inr ?_
              rw [arrangementPullbackGraph, edgeSet_restrict]
              obtain ⟨x, y, hxy_A⟩ := A.G.exists_isLink_of_mem_edgeSet heA
              have hxy_G' : G'.IsLink e x y := hxy_A.mono (hSeg.1.le A hA)
              exact ⟨⟨x, y, hxy_G',
                ⟨Or.inl (mem_iUnion₂.mpr ⟨A, ⟨hA, hA_sub⟩, hxy_A.left_mem⟩), hxy_G'.left_mem⟩,
                ⟨Or.inl (mem_iUnion₂.mpr ⟨A, ⟨hA, hA_sub⟩, hxy_A.right_mem⟩), hxy_G'.right_mem⟩⟩,
                mem_iUnion₂.mpr ⟨A, ⟨hA, hA_sub⟩, heA⟩⟩
            obtain ⟨B, hB, heB⟩ := hCover_star_E he_star
            exact mem_iUnion₂.mpr ⟨B.G, ⟨B, hB, rfl⟩, heB⟩
          · exact mem_iUnion₂.mpr ⟨A.G, ⟨A, Or.inl ⟨hA, hA_sub⟩, rfl⟩, heA⟩
        · have he_star : e ∈ E(localSociety.G) := by
            rw [hsoc_star_G, edgeSet_subgraphUnion hJ.2.1 hP_le_G₀]
            exact Or.inl heJ
          obtain ⟨B, hB, heB⟩ := hCover_star_E he_star
          exact mem_iUnion₂.mpr ⟨B.G, ⟨B, hB, rfl⟩, heB⟩
  · have hV_inter_S₂_0 : ∀ {A B : Society α β},
        A ∈ S_seg₂ → B ∈ S_seg_0 → V(A.G) ∩ V(B.G) ⊆ A.Ω.bar ∩ B.Ω.bar := by
      intro A B hA_S₂ hB_0 v ⟨hvA, hvB⟩
      have hv_star : v ∈ V(localSociety.G) := (h3seg_0.1.le B hB_0).vertexSet_mono hvB
      have hv_bar_star : v ∈ localSociety.Ω.bar :=
        (claim_1_of_10_1 hS hJ hG'_le hDisj_E hInter_V hη'_v hSeg hArr hComp
          hΔ hNorm hVJ_Δ hsoc_star_G hsoc_star_Ω hA_S₂.1 hA_S₂.2).2
          ⟨hv_star, hvA⟩
      have hv_seg : v ∈ segregationVertices S_seg := (hsoc_star_Ω.1 ▸ hv_bar_star).1
      have hv_seg_0 : v ∈ segregationVertices S_seg_0 := hbar_0 hv_bar_star
      have hv_barA : v ∈ A.Ω.bar := by
        obtain ⟨A', hA', hvA'⟩ := mem_iUnion₂.mp hv_seg
        by_cases hAA' : A = A'
        · subst hAA'; exact hvA'
        · exact (hSeg.1.vertex_inter_subset A hA_S₂.1 A' hA' hAA' ⟨hvA, A'.bar_subset hvA'⟩).1
      have hv_barB : v ∈ B.Ω.bar := by
        obtain ⟨B', hB', hvB'⟩ := mem_iUnion₂.mp hv_seg_0
        by_cases hBB' : B = B'
        · subst hBB'; exact hvB'
        · exact (h3seg_0.1.vertex_inter_subset B hB_0 B' hB' hBB' ⟨hvB, B'.bar_subset hvB'⟩).1
      exact ⟨hv_barA, hv_barB⟩
    rintro B₁ (hB₁_S₂ | hB₁_star) B₂ (hB₂_S₂ | hB₂_star) hne
    · exact hSeg.1.vertex_inter_subset B₁ hB₁_S₂.1 B₂ hB₂_S₂.1 hne
    · exact hV_inter_S₂_0 hB₁_S₂ hB₂_star.1
    · intro v ⟨hv1, hv2⟩
      have h := hV_inter_S₂_0 hB₂_S₂ hB₁_star.1 ⟨hv2, hv1⟩
      exact ⟨h.2, h.1⟩
    · exact h3seg_0.1.vertex_inter_subset B₁ hB₁_star.1 B₂ hB₂_star.1 hne
  · rintro B₁ (hB₁_S₂ | hB₁_star) B₂ (hB₂_S₂ | hB₂_star) hne
    · exact hSeg.1.edge_disjoint B₁ hB₁_S₂.1 B₂ hB₂_S₂.1 hne
    · have hdisj :=
        (claim_1_of_10_1 hS hJ hG'_le hDisj_E hInter_V hη'_v hSeg hArr hComp
          hΔ hNorm hVJ_Δ hsoc_star_G hsoc_star_Ω hB₁_S₂.1 hB₁_S₂.2).1
      exact hdisj.symm.mono_right (h3seg_0.1.le B₂ hB₂_star.1).edgeSet_mono
    · have hdisj :=
        (claim_1_of_10_1 hS hJ hG'_le hDisj_E hInter_V hη'_v hSeg hArr hComp
          hΔ hNorm hVJ_Δ hsoc_star_G hsoc_star_Ω hB₂_S₂.1 hB₂_S₂.2).1
      exact hdisj.mono_left (h3seg_0.1.le B₁ hB₁_star.1).edgeSet_mono
    · exact h3seg_0.1.edge_disjoint B₁ hB₁_star.1 B₂ hB₂_star.1 hne
  · rintro B (hB_S₂ | hB_star)
    · exact hSeg.2 B hB_S₂.1
    · exact h3seg_0.2 B hB_star.1

private theorem replacement_bridge_segregation_is_tangle_local
    {S : Type u}
    [TopologicalSpace S]
    {α : Type v}
    {β : Type w}
    (G₀ : Graph α β)
    (G' : Graph α β)
    (H : Drawing S)
    (η₀ : SpanEmbedding H G₀)
    (η' : SpanEmbedding H G')
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (S_seg : Set (Society α β))
    (α_disc : Society α β → Set S)
    (Δ : Set S)
    (hG'_le : G' ≤ G₀)
    (hη'_v : ∀ v ∈ H.V, η'.vMap v = η₀.vMap v)
    (hη'_e : ∀ e ∈ H.E, η'.eMap e = η₀.eMap e)
    (hSeg : IsThreeSegregation G' S_seg)
    (hLoc : IsTangleLocal G' H η' T S_seg)
    (S_seg_0 : Set (Society α β))
    (hLoc_star : IsTangleLocal G₀ H η₀ T (S_seg_0 \ ({A | A ∈ S_seg ∧ ¬α_disc A ⊆ Δ}))) :
    IsTangleLocal G₀ H η₀ T (({A | A ∈ S_seg ∧ ¬α_disc A ⊆ Δ}) ∪ (S_seg_0 \ ({A | A ∈ S_seg ∧
      ¬α_disc A ⊆ Δ}))) := by
  let S_seg₂ := {A | A ∈ S_seg ∧ ¬α_disc A ⊆ Δ}
  let S_seg_star := S_seg_0 \ S_seg₂
  let S_seg' := S_seg₂ ∪ S_seg_star
  rintro S₀ (hS₀_S₂ | hS₀_star) B hsepB hVB_eq
  · let B' : Graph α β := (G'.induce (V(B) ∩ V(G'))).restrict E(B)
    have hV_B' : V(B') = V(B) ∩ V(G') := by simp [B']
    have hE_B' : E(B') = E(B) ∩ E(G') := by
      ext e
      simp only [B', edgeSet_restrict, edgeSet_induce, mem_inter_iff]
      refine ⟨fun ⟨⟨u_e, v_e, hlink, _, _⟩, heB⟩ => ⟨heB, hlink.edge_mem⟩, fun ⟨heB,
        heG'⟩ => ?_⟩
      obtain ⟨u_e, v_e, hlink⟩ := G'.exists_isLink_of_mem_edgeSet heG'
      have hlink_B : B.IsLink e u_e v_e :=
        (hsepB.2.1.isLink_iff heB).mpr (hlink.mono hG'_le)
      exact ⟨⟨u_e, v_e, hlink, ⟨hlink_B.left_mem, hlink.left_mem⟩,
        ⟨hlink_B.right_mem, hlink.right_mem⟩⟩, heB⟩
    have hB'_le : B' ≤ G' := restrict_le.trans (G'.induce_le inter_subset_right)
    have hS₀_le : S₀.G ≤ G' := hSeg.1.le S₀ hS₀_S₂.1
    have hsepB' : IsGraphSeparation G' S₀.G B' := by
      refine ⟨hS₀_le, hB'_le, ?_, ?_, ?_⟩
      · rw [← inter_eq_left.mpr hS₀_le.vertexSet_mono, hV_B', ← union_inter_distrib_right,
          hsepB.2.2.1]
        exact inter_eq_right.mpr hG'_le.vertexSet_mono
      · rw [← inter_eq_left.mpr hS₀_le.edgeSet_mono, hE_B', ← union_inter_distrib_right,
          hsepB.2.2.2.1]
        exact inter_eq_right.mpr hG'_le.edgeSet_mono
      · rw [hE_B']
        exact hsepB.2.2.2.2.mono_right inter_subset_left
    have hVB'_eq : V(S₀.G) ∩ V(B') = S₀.Ω.bar := by
      rw [hV_B', ← Set.inter_assoc, inter_eq_left.mpr
        (inter_subset_left.trans hS₀_le.vertexSet_mono)]
      exact hVB_eq
    obtain ⟨A_H, B_H, hsep_H, hAH_V, hBH_V, hAH_E, hBH_E, hT_mem⟩ :=
      hLoc S₀ hS₀_S₂.1 B' hsepB' hVB'_eq
    refine ⟨A_H, B_H, hsep_H, ?_, ?_, ?_, ?_, hT_mem⟩
    · rw [hAH_V]
      ext v
      simp only [mem_sep_iff]
      exact ⟨fun ⟨hv, hvS⟩ => ⟨hv, hη'_v v hv ▸ hvS⟩,
        fun ⟨hv, hvS⟩ => ⟨hv, (hη'_v v hv).symm ▸ hvS⟩⟩
    · rw [hBH_V, hV_B']
      ext v
      simp only [mem_sep_iff, mem_inter_iff]
      exact ⟨fun ⟨hv, hvB, _⟩ => ⟨hv, hη'_v v hv ▸ hvB⟩,
        fun ⟨hv, hvB⟩ => ⟨hv, (hη'_v v hv).symm ▸ hvB,
          η'.imageGraph_le.vertexSet_mono (η'.bijOn_v.mapsTo hv)⟩⟩
    · rw [hAH_E]
      ext e
      simp only [mem_sep_iff]
      exact ⟨fun ⟨he, heS⟩ => ⟨he, hη'_e e he ▸ heS⟩,
        fun ⟨he, heS⟩ => ⟨he, (hη'_e e he).symm ▸ heS⟩⟩
    · rw [hBH_E, hE_B']
      ext e
      simp only [mem_sep_iff, mem_inter_iff]
      exact ⟨fun ⟨he, heB, _⟩ => ⟨he, hη'_e e he ▸ heB⟩,
        fun ⟨he, heB⟩ => ⟨he, (hη'_e e he).symm ▸ heB,
          η'.imageGraph_le.edgeSet_mono (η'.bijOn_e.mapsTo he)⟩⟩
  · exact hLoc_star S₀ hS₀_star B hsepB hVB_eq

private theorem replacement_bridge_discs_form_surface_arrangement
    {S : Type u}
    [TopologicalSpace S]
    [T2Space S]
    {α : Type v}
    {β : Type w}
    (S_seg : Set (Society α β))
    (α_disc : Society α β → Set S)
    (α_pt : α → S)
    (Δ : Set S)
    (localSociety : Society α β)
    (hS : IsClosedSurface S)
    (hArr : IsSurfaceArrangement S_seg α_disc α_pt)
    (hΔ : IsClosedDisc Δ)
    (hNorm : IsArrangementNormal S_seg α_disc α_pt (subBd Δ))
    (hsoc_star_Ω : IsPullbackPerm S_seg α_pt (subBd Δ) localSociety.Ω)
    (S_seg_0 : Set (Society α β))
    (hbar_0 : localSociety.Ω.bar ⊆ segregationVertices S_seg_0)
    (α_disc_star : Society α β → Set S)
    (α_pt_star : α → S)
    (harr_star : IsSurfaceArrangement S_seg_0 α_disc_star α_pt_star)
    (hdisc_star_sub : ∀ S₀ ∈ S_seg_0, α_disc_star S₀ ⊆ Δ)
    (hpt_star_eq : ∀ v ∈ localSociety.Ω.bar, α_pt_star v = α_pt v)
    (hpt_star_mem : ∀ v ∈ segregationVertices S_seg_0, α_pt_star v ∈ Δ)
    (hdisc_star_inter_bd : ∀ B ∈ S_seg_0, α_disc_star B ∩ subBd Δ ⊆ α_pt_star '' (B.Ω.bar ∩
      localSociety.Ω.bar))
    (α'_disc : Society α β → Set S)
    (α'_pt : α → S)
    (hα'_disc_S₂ : ∀ {B : Society α β}, B ∈ ({A | A ∈ S_seg ∧ ¬α_disc A ⊆ Δ}) → α'_disc B = α_disc
      B)
    (hα'_disc_star : ∀ {B : Society α β}, B ∈ (S_seg_0 \ ({A | A ∈ S_seg ∧ ¬α_disc A ⊆ Δ})) →
      α'_disc B = α_disc_star B)
    (hα'_pt_S₂ : ∀ {v : α}, v ∈ segregationVertices ({A | A ∈ S_seg ∧ ¬α_disc A ⊆ Δ}) → α'_pt v =
      α_pt v)
    (hα'_pt_0 : ∀ {v : α}, v ∈ segregationVertices S_seg_0 → α'_pt v = α_pt_star v) :
    IsSurfaceArrangement (({A | A ∈ S_seg ∧ ¬α_disc A ⊆ Δ}) ∪ (S_seg_0 \ ({A | A ∈ S_seg ∧ ¬α_disc
      A ⊆ Δ}))) α'_disc α'_pt := by
  let S_seg₂ := {A | A ∈ S_seg ∧ ¬α_disc A ⊆ Δ}
  let S_seg_star := S_seg_0 \ S_seg₂
  let S_seg' := S_seg₂ ∪ S_seg_star
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro B (hB_S₂ | hB_star)
    · rw [hα'_disc_S₂ hB_S₂]
      refine ⟨(hArr.isClosedDisc B hB_S₂.1).1, fun x hx => ?_⟩
      rw [hα'_pt_S₂ (mem_biUnion hB_S₂ hx)]
      exact (hArr.isClosedDisc B hB_S₂.1).2 x hx
    · rw [hα'_disc_star hB_star]
      refine ⟨(harr_star.isClosedDisc B hB_star.1).1, fun x hx => ?_⟩
      rw [hα'_pt_0 (mem_biUnion hB_star.1 hx)]
      exact (harr_star.isClosedDisc B hB_star.1).2 x hx
  · have hinter_star_S₂ : ∀ {B A : Society α β},
        B ∈ S_seg_star → A ∈ S_seg₂ →
        α'_disc B ∩ α'_disc A ⊆ α'_pt '' (B.Ω.bar ∩ A.Ω.bar) := by
      intro B A hB_star hA_S₂ x ⟨hxB, hxA⟩
      rw [hα'_disc_star hB_star] at hxB
      rw [hα'_disc_S₂ hA_S₂] at hxA
      have hx_Δ : x ∈ Δ := hdisc_star_sub B hB_star.1 hxB
      have hx_bdΔ : x ∈ subBd Δ :=
        (inter_disc_subset_subBd_of_not_subset hS hArr hΔ hNorm hA_S₂.1 hA_S₂.2).1 ⟨hxA, hx_Δ⟩
      obtain ⟨v, hvA_bar, rfl⟩ := hNorm A hA_S₂.1 ⟨hx_bdΔ, hxA⟩
      obtain ⟨w, ⟨hwB_bar, hw_star_bar⟩, hw_eq⟩ := hdisc_star_inter_bd B hB_star.1 ⟨hxB, hx_bdΔ⟩
      have hw_eq_0 : α_pt w = α_pt v := by
        rw [← hpt_star_eq w hw_star_bar, hw_eq]
      have hv_seg : v ∈ segregationVertices S_seg := mem_biUnion hA_S₂.1 hvA_bar
      have hw_seg : w ∈ segregationVertices S_seg := (hsoc_star_Ω.1 ▸ hw_star_bar).1
      have hvw : w = v := hArr.injOn_pts hw_seg hv_seg hw_eq_0
      subst hvw
      exact ⟨w, ⟨hwB_bar, hvA_bar⟩, hα'_pt_S₂ (mem_biUnion hA_S₂ hvA_bar)⟩
    rintro B₁ (hB₁_S₂ | hB₁_star) B₂ (hB₂_S₂ | hB₂_star) hne
    · rw [hα'_disc_S₂ hB₁_S₂, hα'_disc_S₂ hB₂_S₂]
      intro x hx
      obtain ⟨v, hv, rfl⟩ := hArr.inter_discs B₁ hB₁_S₂.1 B₂ hB₂_S₂.1 hne hx
      exact ⟨v, hv, hα'_pt_S₂ (mem_biUnion hB₁_S₂ hv.1)⟩
    · rw [Set.inter_comm, Set.inter_comm B₁.Ω.bar]
      exact hinter_star_S₂ hB₂_star hB₁_S₂
    · exact hinter_star_S₂ hB₁_star hB₂_S₂
    · rw [hα'_disc_star hB₁_star, hα'_disc_star hB₂_star]
      intro x hx
      obtain ⟨v, hv, rfl⟩ := harr_star.inter_discs B₁ hB₁_star.1 B₂ hB₂_star.1 hne hx
      exact ⟨v, hv, hα'_pt_0 (mem_biUnion hB₁_star.1 hv.1)⟩
  · rintro B _ x ⟨_, hxbd⟩
    exact (hxbd (hS.2.2 x)).elim
  · have hseg'_cases : ∀ {v : α}, v ∈ segregationVertices S_seg' →
        v ∈ segregationVertices S_seg₂ ∨ v ∈ segregationVertices S_seg_0 := by
      intro v hv
      rcases mem_iUnion₂.mp hv with ⟨B, hB_S₂ | hB_star, hvB⟩
      · exact Or.inl (mem_biUnion hB_S₂ hvB)
      · exact Or.inr (mem_biUnion hB_star.1 hvB)
    have hinj_0_S₂ : ∀ {u v : α},
        u ∈ segregationVertices S_seg_0 → v ∈ segregationVertices S_seg₂ →
        α'_pt u = α'_pt v → u = v := by
      intro u v hu_0 hv_S₂ huv
      by_cases hv_0 : v ∈ segregationVertices S_seg_0
      · rw [hα'_pt_0 hu_0, hα'_pt_0 hv_0] at huv
        exact harr_star.injOn_pts hu_0 hv_0 huv
      · exfalso
        have hv_not_bar_star : v ∉ localSociety.Ω.bar := fun hbar => hv_0 (hbar_0 hbar)
        obtain ⟨A, hA_S₂, hvA_bar⟩ := mem_iUnion₂.mp hv_S₂
        have hv_seg : v ∈ segregationVertices S_seg := mem_biUnion hA_S₂.1 hvA_bar
        have hv_not_bdΔ : α_pt v ∉ subBd Δ := by
          intro hbd
          apply hv_not_bar_star
          rw [hsoc_star_Ω.1]
          exact ⟨hv_seg, hbd⟩
        have hv_bdA : α_pt v ∈ subBd (α_disc A) := (hArr.isClosedDisc A hA_S₂.1).2 v hvA_bar
        have hv_discA : α_pt v ∈ α_disc A :=
          (hArr.isClosedDisc A hA_S₂.1).1.isClosed.closure_subset_iff.mpr Subset.rfl hv_bdA.1
        have hv_not_Δ : α_pt v ∉ Δ := fun hxΔ =>
          hv_not_bdΔ ((inter_disc_subset_subBd_of_not_subset hS hArr hΔ hNorm hA_S₂.1 hA_S₂.2).1
            ⟨hv_discA, hxΔ⟩)
        rw [hα'_pt_0 hu_0, hα'_pt_S₂ hv_S₂] at huv
        exact hv_not_Δ (huv ▸ hpt_star_mem u hu_0)
    intro u hu v hv huv
    rcases hseg'_cases hu with hu_S₂ | hu_0 <;> rcases hseg'_cases hv with hv_S₂ | hv_0
    · rw [hα'_pt_S₂ hu_S₂, hα'_pt_S₂ hv_S₂] at huv
      have hsub : segregationVertices S_seg₂ ⊆ segregationVertices S_seg :=
        biUnion_mono (fun _ h => h.1) (fun _ _ => Subset.rfl)
      exact hArr.injOn_pts (hsub hu_S₂) (hsub hv_S₂) huv
    · exact (hinj_0_S₂ hv_0 hu_S₂ huv.symm).symm
    · exact hinj_0_S₂ hu_0 hv_S₂ huv
    · rw [hα'_pt_0 hu_0, hα'_pt_0 hv_0] at huv
      exact harr_star.injOn_pts hu_0 hv_0 huv
  · have hnat_congr : ∀ {ν₁ ν₂ : α → S} {Ω : CyclicPerm α} {F : Set S},
        (∀ v ∈ Ω.bar, ν₁ v = ν₂ v) → IsNaturalOrderFrom ν₁ Ω F → IsNaturalOrderFrom ν₂ Ω F := by
      intro ν₁ ν₂ Ω F heq ⟨hOArc, φ, hmem, hcw3⟩
      refine ⟨hOArc, φ, fun v hv => heq v hv ▸ hmem v hv, fun v₁ v₂ v₃ hcw => ?_⟩
      obtain ⟨t₁, t₂, t₃, h12, h23, h31, h1, h2, h3⟩ := hcw3 v₁ v₂ v₃ hcw
      have hv1 : v₁ ∈ Ω.bar := hcw.2.1 v₁ (by simp)
      have hv2 : v₂ ∈ Ω.bar := hcw.2.1 v₂ (by simp)
      have hv3 : v₃ ∈ Ω.bar := hcw.2.1 v₃ (by simp)
      exact ⟨t₁, t₂, t₃, h12, h23, h31, h1.trans (heq v₁ hv1),
        h2.trans (heq v₂ hv2), h3.trans (heq v₃ hv3)⟩
    rintro B (hB_S₂ | hB_star)
    · rw [hα'_disc_S₂ hB_S₂]
      exact hnat_congr (fun v hv => (hα'_pt_S₂ (mem_biUnion hB_S₂ hv)).symm)
        (hArr.natural_order B hB_S₂.1)
    · rw [hα'_disc_star hB_star]
      exact hnat_congr (fun v hv => (hα'_pt_0 (mem_biUnion hB_star.1 hv)).symm)
        (harr_star.natural_order B hB_star.1)

private theorem replacement_bridge_arrangement_is_compatible
    {S : Type u}
    [TopologicalSpace S]
    [T2Space S]
    {α : Type v}
    {β : Type w}
    (G₀ : Graph α β)
    (G' : Graph α β)
    (J : Graph α β)
    (H : Drawing S)
    (η₀ : SpanEmbedding H G₀)
    (η' : SpanEmbedding H G')
    (S_seg : Set (Society α β))
    (α_disc : Society α β → Set S)
    (α_pt : α → S)
    (Δ : Set S)
    (localSociety : Society α β)
    (hJ : IsBridge G₀ η₀.imageGraph J)
    (hDisj_E : Disjoint E(G') E(J))
    (hη'_v : ∀ v ∈ H.V, η'.vMap v = η₀.vMap v)
    (hη'_e : ∀ e ∈ H.E, η'.eMap e = η₀.eMap e)
    (hComp : IsCompatibleWith G' H η' S_seg α_disc α_pt)
    (hΔ : IsClosedDisc Δ)
    (hsoc_star_G : localSociety.G = subgraphUnion G₀ J (arrangementPullbackGraph G' S_seg α_disc
      α_pt
      Δ))
    (hP_le_G₀ : (arrangementPullbackGraph G' S_seg α_disc α_pt Δ) ≤ G₀)
    (S_seg_0 : Set (Society α β))
    (h3seg_0 : IsThreeSegregation localSociety.G S_seg_0)
    (hseg_0_sub_V : segregationVertices S_seg_0 ⊆ V(localSociety.G))
    (hV_HΔ : (H.interSet Δ).V = H.V ∩ Δ)
    (hU_HΔ : (H.interSet Δ).U = H.U ∩ Δ)
    (hE_HΔ : (H.interSet Δ).E = {e | e ∈ H.E ∧ e ⊆ Δ})
    (η_Δ : SpanEmbedding (H.interSet Δ) localSociety.G)
    (hvMap : η_Δ.vMap = η₀.vMap) (heMap : η_Δ.eMap = η₀.eMap)
    (α_disc_star : Society α β → Set S)
    (α_pt_star : α → S)
    (hdisc_star_sub : ∀ S₀ ∈ S_seg_0, α_disc_star S₀ ⊆ Δ)
    (hcomp_star : IsCompatibleWith localSociety.G (H.interSet Δ) η_Δ S_seg_0 α_disc_star α_pt_star)
    (α'_disc : Society α β → Set S)
    (α'_pt : α → S)
    (hα'_disc_S₂ : ∀ {B : Society α β}, B ∈ ({A | A ∈ S_seg ∧ ¬α_disc A ⊆ Δ}) → α'_disc B = α_disc
      B)
    (hα'_disc_star : ∀ {B : Society α β}, B ∈ (S_seg_0 \ ({A | A ∈ S_seg ∧ ¬α_disc A ⊆ Δ})) →
      α'_disc B = α_disc_star B)
    (hα'_pt_S₂ : ∀ {v : α}, v ∈ segregationVertices ({A | A ∈ S_seg ∧ ¬α_disc A ⊆ Δ}) → α'_pt v =
      α_pt v)
    (hα'_pt_0 : ∀ {v : α}, v ∈ segregationVertices S_seg_0 → α'_pt v = α_pt_star v)
    (hHV_mem_star_imp_Δ : ∀ v ∈ H.V, η₀.vMap v ∈ V(localSociety.G) → v ∈ Δ) :
    IsCompatibleWith G₀ H η₀ (({A | A ∈ S_seg ∧ ¬α_disc A ⊆ Δ}) ∪ (S_seg_0 \ ({A | A ∈ S_seg ∧
      ¬α_disc A ⊆ Δ}))) α'_disc α'_pt := by
  let P_Δ := arrangementPullbackGraph G' S_seg α_disc α_pt Δ
  let S_seg₂ := {A | A ∈ S_seg ∧ ¬α_disc A ⊆ Δ}
  let S_seg_star := S_seg_0 \ S_seg₂
  let S_seg' := S_seg₂ ∪ S_seg_star
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hvH hv_seg'
    rcases mem_iUnion₂.mp hv_seg' with ⟨B, hB_S₂ | hB_star, hvB⟩
    · rw [hα'_pt_S₂ (mem_biUnion hB_S₂ hvB), ← hη'_v v hvH]
      exact hComp.pt_eq v hvH (hη'_v v hvH ▸ mem_biUnion hB_S₂.1 hvB)
    · have hv_0 : η₀.vMap v ∈ segregationVertices S_seg_0 := mem_biUnion hB_star.1 hvB
      have hvΔ : v ∈ Δ := hHV_mem_star_imp_Δ v hvH (hseg_0_sub_V hv_0)
      rw [hα'_pt_0 hv_0]
      rw [← hvMap]
      exact hcomp_star.pt_eq v (hV_HΔ.symm ▸ ⟨hvH, hvΔ⟩) (hvMap.symm ▸ hv_0)
  · rintro B (hB_S₂ | hB_star)
    · rw [hα'_disc_S₂ hB_S₂, hComp.bd_inter_eq B hB_S₂.1]
      ext v
      simp only [mem_sep_iff]
      exact ⟨fun ⟨hv, hvB⟩ => ⟨hv, hη'_v v hv ▸ hvB⟩,
        fun ⟨hv, hvB⟩ => ⟨hv, (hη'_v v hv).symm ▸ hvB⟩⟩
    · rw [hα'_disc_star hB_star]
      have hsub_bd : subBd (α_disc_star B) ⊆ Δ := fun _ hx =>
        hΔ.isClosed.closure_subset_iff.mpr (hdisc_star_sub B hB_star.1) hx.1
      have hU_eq : H.U ∩ subBd (α_disc_star B) = (H.interSet Δ).U ∩ subBd (α_disc_star B) := by
        rw [hU_HΔ]
        ext x
        simp only [mem_inter_iff]
        exact ⟨fun ⟨hxU, hxbd⟩ => ⟨⟨hxU, hsub_bd hxbd⟩, hxbd⟩, fun ⟨⟨hxU, _⟩, hxbd⟩ => ⟨hxU,
          hxbd⟩⟩
      rw [hU_eq, hcomp_star.bd_inter_eq B hB_star.1, hV_HΔ, hvMap]
      ext v
      simp only [mem_sep_iff, mem_inter_iff]
      refine ⟨fun ⟨⟨hvH, _⟩, hvB⟩ => ⟨hvH, hvB⟩, fun ⟨hvH, hvB⟩ => ⟨⟨hvH, ?_⟩, hvB⟩⟩
      exact hHV_mem_star_imp_Δ v hvH ((h3seg_0.1.le B hB_star.1).vertexSet_mono (B.bar_subset hvB))
  · rintro B (hB_S₂ | hB_star) v hvH
    · rw [hα'_disc_S₂ hB_S₂, hComp.inter_V_iff B hB_S₂.1 v hvH, hη'_v v hvH]
    · rw [hα'_disc_star hB_star]
      by_cases hvΔ : v ∈ Δ
      · simpa only [hvMap] using hcomp_star.inter_V_iff B hB_star.1 v (hV_HΔ.symm ▸ ⟨hvH, hvΔ⟩)
      · refine ⟨fun hv_disc => (hvΔ (hdisc_star_sub B hB_star.1 hv_disc)).elim,
          fun hvB => (hvΔ (hHV_mem_star_imp_Δ v hvH
            ((h3seg_0.1.le B hB_star.1).vertexSet_mono hvB))).elim⟩
  · rintro B (hB_S₂ | hB_star) e heH
    · rw [hα'_disc_S₂ hB_S₂, hComp.inter_E_iff B hB_S₂.1 e heH, hη'_e e heH]
    · rw [hα'_disc_star hB_star]
      by_cases heΔ : e ⊆ Δ
      · simpa only [heMap] using hcomp_star.inter_E_iff B hB_star.1 e (hE_HΔ.symm ▸ ⟨heH, heΔ⟩)
      · refine ⟨fun he_disc => (heΔ (he_disc.trans (hdisc_star_sub B hB_star.1))).elim,
          fun heB => ?_⟩
        have he_star : η₀.eMap e ∈ E(localSociety.G) := (h3seg_0.1.le B hB_star.1).edgeSet_mono heB
        rw [hsoc_star_G, edgeSet_subgraphUnion hJ.2.1 hP_le_G₀] at he_star
        have he_G' : η₀.eMap e ∈ E(G') :=
          hη'_e e heH ▸ η'.imageGraph_le.edgeSet_mono (η'.bijOn_e.mapsTo heH)
        have he_P : η₀.eMap e ∈ E(P_Δ) :=
          he_star.resolve_left (fun heJ => Set.disjoint_left.mp hDisj_E he_G' heJ)
        rw [← hη'_e e heH] at he_P
        change η'.eMap e ∈ E(arrangementPullbackGraph G' S_seg α_disc α_pt Δ) at he_P
        rw [arrangementPullbackGraph, edgeSet_restrict] at he_P
        obtain ⟨A', ⟨hA'_S, hA'_sub⟩, heA'⟩ := mem_iUnion₂.mp he_P.2
        exact (heΔ (((hComp.inter_E_iff A' hA'_S e heH).mpr heA').trans hA'_sub)).elim

private theorem edges_meeting_replacement_disc_are_carried_inside
    {S : Type u}
    [TopologicalSpace S]
    [T2Space S]
    {α : Type v}
    {β : Type w}
    (G' : Graph α β)
    (H : Drawing S)
    (η' : SpanEmbedding H G')
    (S_seg : Set (Society α β))
    (α_disc : Society α β → Set S)
    (α_pt : α → S)
    (Δ : Set S)
    (hS : IsClosedSurface S)
    (hSeg : IsThreeSegregation G' S_seg)
    (hArr : IsSurfaceArrangement S_seg α_disc α_pt)
    (hComp : IsCompatibleWith G' H η' S_seg α_disc α_pt)
    (hΔ : IsClosedDisc Δ)
    (hNorm : IsArrangementNormal S_seg α_disc α_pt (subBd Δ)) :
    ∀ e ∈ H.E, (e ∩ Δ).Nonempty → ∃ A ∈ S_seg, α_disc A ⊆ Δ ∧ η'.eMap e ∈ E(A.G) ∧ e ⊆ Δ := by
  rintro e he ⟨x, hxe, hxΔ⟩
  have he_G' : η'.eMap e ∈ E(G') := η'.imageGraph_le.edgeSet_mono (η'.bijOn_e.mapsTo he)
  have he_u : η'.eMap e ∈ E(subgraphSUnion G' ((fun A : Society α β => A.G) '' S_seg)) := by
    rw [hSeg.1.union_eq]; exact he_G'
  rw [edgeSet_subgraphSUnion (by rintro _ ⟨A, hA, rfl⟩; exact hSeg.1.le A hA)] at he_u
  obtain ⟨_, ⟨A, hA, rfl⟩, heA⟩ := mem_iUnion₂.mp he_u
  have he_disc : e ⊆ α_disc A := (hComp.inter_E_iff A hA e he).mpr heA
  have hA_sub : α_disc A ⊆ Δ := by
    by_contra hnot
    obtain ⟨_, hbar⟩ := inter_disc_subset_subBd_of_not_subset hS hArr hΔ hNorm hA hnot
    obtain ⟨y, hy_bar, rfl⟩ := hbar ⟨he_disc hxe, hxΔ⟩
    have hx_bdA : α_pt y ∈ H.U ∩ subBd (α_disc A) :=
      ⟨(he.2.1 hxe).1, (hArr.isClosedDisc A hA).2 y hy_bar⟩
    rw [hComp.bd_inter_eq A hA] at hx_bdA
    exact (he.2.1 hxe).2 hx_bdA.1
  exact ⟨A, hA, hA_sub, heA, he_disc.trans hA_sub⟩

private theorem vertices_in_replacement_disc_belong_to_pullback
    {S : Type u}
    [TopologicalSpace S]
    [T2Space S]
    {α : Type v}
    {β : Type w}
    (G₀ : Graph α β)
    (G' : Graph α β)
    (H : Drawing S)
    (η₀ : SpanEmbedding H G₀)
    (η' : SpanEmbedding H G')
    (S_seg : Set (Society α β))
    (α_disc : Society α β → Set S)
    (α_pt : α → S)
    (Δ : Set S)
    (hS : IsClosedSurface S)
    (hη'_v : ∀ v ∈ H.V, η'.vMap v = η₀.vMap v)
    (hSeg : IsThreeSegregation G' S_seg)
    (hArr : IsSurfaceArrangement S_seg α_disc α_pt)
    (hComp : IsCompatibleWith G' H η' S_seg α_disc α_pt)
    (hΔ : IsClosedDisc Δ)
    (hNorm : IsArrangementNormal S_seg α_disc α_pt (subBd Δ)) :
    ∀ v ∈ H.V, v ∈ Δ → η₀.vMap v ∈ V((arrangementPullbackGraph G' S_seg α_disc α_pt Δ)) := by
  let P_Δ := arrangementPullbackGraph G' S_seg α_disc α_pt Δ
  intro v hvH hvΔ
  have hv_G' : η'.vMap v ∈ V(G') := η'.imageGraph_le.vertexSet_mono (η'.bijOn_v.mapsTo hvH)
  have hv_u : η'.vMap v ∈ V(subgraphSUnion G' ((fun A : Society α β => A.G) '' S_seg)) := by
    rw [hSeg.1.union_eq]; exact hv_G'
  rw [vertexSet_subgraphSUnion] at hv_u
  obtain ⟨_, ⟨A, hA, rfl⟩, hvA⟩ := mem_iUnion₂.mp hv_u
  have hv_disc : v ∈ α_disc A := (hComp.inter_V_iff A hA v hvH).mpr hvA
  rw [ ← hη'_v v hvH]
  change η'.vMap v ∈ V(arrangementPullbackGraph G' S_seg α_disc α_pt Δ)
  rw [arrangementPullbackGraph, vertexSet_restrict, vertexSet_induce]
  by_cases hA_sub : α_disc A ⊆ Δ
  · exact ⟨Or.inl (mem_iUnion₂.mpr ⟨A, ⟨hA, hA_sub⟩, hvA⟩), hv_G'⟩
  · obtain ⟨_, hbar⟩ := inter_disc_subset_subBd_of_not_subset hS hArr hΔ hNorm hA hA_sub
    obtain ⟨y, hy_bar, rfl⟩ := hbar ⟨hv_disc, hvΔ⟩
    have hv_bdA : α_pt y ∈ H.U ∩ subBd (α_disc A) :=
      ⟨H.V_subset_U hvH, (hArr.isClosedDisc A hA).2 y hy_bar⟩
    rw [hComp.bd_inter_eq A hA] at hv_bdA
    have hv_seg : η'.vMap (α_pt y) ∈ segregationVertices S_seg := mem_biUnion hA hv_bdA.2
    have hpt_eq : α_pt (η'.vMap (α_pt y)) = α_pt y := hComp.pt_eq (α_pt y) hvH hv_seg
    exact ⟨Or.inr ⟨hv_seg, hpt_eq.symm ▸ hvΔ⟩, hv_G'⟩

private theorem vertices_on_replacement_boundary_belong_to_society
    {S : Type u}
    [TopologicalSpace S]
    {α : Type v}
    {β : Type w}
    (G₀ : Graph α β)
    (G' : Graph α β)
    (H : Drawing S)
    (η₀ : SpanEmbedding H G₀)
    (η' : SpanEmbedding H G')
    (S_seg : Set (Society α β))
    (α_disc : Society α β → Set S)
    (α_pt : α → S)
    (Δ : Set S)
    (localSociety : Society α β)
    (hη'_v : ∀ v ∈ H.V, η'.vMap v = η₀.vMap v)
    (hSeg : IsThreeSegregation G' S_seg)
    (hArr : IsSurfaceArrangement S_seg α_disc α_pt)
    (hComp : IsCompatibleWith G' H η' S_seg α_disc α_pt)
    (hNorm : IsArrangementNormal S_seg α_disc α_pt (subBd Δ))
    (hsoc_star_Ω : IsPullbackPerm S_seg α_pt (subBd Δ) localSociety.Ω) :
    ∀ v ∈ H.V, v ∈ subBd Δ → η₀.vMap v ∈ localSociety.Ω.bar ∧ α_pt (η₀.vMap v) = v := by
  intro v hvH hv_bd
  have hv_G' : η'.vMap v ∈ V(G') := η'.imageGraph_le.vertexSet_mono (η'.bijOn_v.mapsTo hvH)
  have hv_u : η'.vMap v ∈ V(subgraphSUnion G' ((fun A : Society α β => A.G) '' S_seg)) := by
    rw [hSeg.1.union_eq]; exact hv_G'
  rw [vertexSet_subgraphSUnion] at hv_u
  obtain ⟨_, ⟨A, hA, rfl⟩, hvA⟩ := mem_iUnion₂.mp hv_u
  have hv_disc : v ∈ α_disc A := (hComp.inter_V_iff A hA v hvH).mpr hvA
  obtain ⟨y, hy_bar, rfl⟩ := hNorm A hA ⟨hv_bd, hv_disc⟩
  have hv_bdA : α_pt y ∈ H.U ∩ subBd (α_disc A) :=
    ⟨H.V_subset_U hvH, (hArr.isClosedDisc A hA).2 y hy_bar⟩
  rw [hComp.bd_inter_eq A hA] at hv_bdA
  have hv_seg : η₀.vMap (α_pt y) ∈ segregationVertices S_seg :=
    hη'_v (α_pt y) hvH ▸ mem_biUnion hA hv_bdA.2
  have hpt_eq : α_pt (η₀.vMap (α_pt y)) = α_pt y := by
    rw [← hη'_v (α_pt y) hvH]
    exact hComp.pt_eq (α_pt y) hvH (hη'_v (α_pt y) hvH ▸ hv_seg)
  rw [hsoc_star_Ω.1]
  exact ⟨⟨hv_seg, hpt_eq.symm ▸ hv_bd⟩, hpt_eq⟩

private theorem replacement_society_uses_vertices_inside_disc
    {S : Type u}
    [TopologicalSpace S]
    [T2Space S]
    {α : Type v}
    {β : Type w}
    (G₀ : Graph α β)
    (G' : Graph α β)
    (J : Graph α β)
    (H : Drawing S)
    (η₀ : SpanEmbedding H G₀)
    (η' : SpanEmbedding H G')
    (S_seg : Set (Society α β))
    (α_disc : Society α β → Set S)
    (α_pt : α → S)
    (Δ : Set S)
    (localSociety : Society α β)
    (hS : IsClosedSurface S)
    (hJ : IsBridge G₀ η₀.imageGraph J)
    (hG'_le : G' ≤ G₀)
    (hDisj_E : Disjoint E(G') E(J))
    (hInter_V : V(G') ∩ V(J) ⊆ V(η₀.imageGraph))
    (hη'_v : ∀ v ∈ H.V, η'.vMap v = η₀.vMap v)
    (hSeg : IsThreeSegregation G' S_seg)
    (hArr : IsSurfaceArrangement S_seg α_disc α_pt)
    (hComp : IsCompatibleWith G' H η' S_seg α_disc α_pt)
    (hΔ : IsClosedDisc Δ)
    (hNorm : IsArrangementNormal S_seg α_disc α_pt (subBd Δ))
    (hVJ_Δ : ∀ v ∈ H.V, η₀.vMap v ∈ V(J) → v ∈ Δ \ subBd Δ)
    (hsoc_star_G : localSociety.G = subgraphUnion G₀ J (arrangementPullbackGraph G' S_seg α_disc
      α_pt
      Δ))
    (hsoc_star_Ω : IsPullbackPerm S_seg α_pt (subBd Δ) localSociety.Ω) :
    ∀ v ∈ H.V, η₀.vMap v ∈ V(localSociety.G) → v ∈ Δ := by
  intro v hvH hv_star
  by_contra hv_not_Δ
  have hv_G' : η'.vMap v ∈ V(G') := η'.imageGraph_le.vertexSet_mono (η'.bijOn_v.mapsTo hvH)
  have hv_u : η'.vMap v ∈ V(subgraphSUnion G' ((fun A : Society α β => A.G) '' S_seg)) := by
    rw [hSeg.1.union_eq]; exact hv_G'
  rw [vertexSet_subgraphSUnion] at hv_u
  obtain ⟨_, ⟨A, hA, rfl⟩, hvA⟩ := mem_iUnion₂.mp hv_u
  have hv_disc : v ∈ α_disc A := (hComp.inter_V_iff A hA v hvH).mpr hvA
  have hA_not : ¬ (α_disc A ⊆ Δ) := fun hsub => hv_not_Δ (hsub hv_disc)
  rw [hη'_v v hvH] at hvA
  have hv_bar_star : η₀.vMap v ∈ localSociety.Ω.bar :=
    (claim_1_of_10_1 hS hJ hG'_le hDisj_E hInter_V hη'_v hSeg hArr hComp
      hΔ hNorm hVJ_Δ hsoc_star_G hsoc_star_Ω hA hA_not).2
      ⟨hv_star, hvA⟩
  have hv_seg : η₀.vMap v ∈ segregationVertices S_seg := (hsoc_star_Ω.1 ▸ hv_bar_star).1
  have hpt_v : α_pt (η₀.vMap v) = v := by
    rw [← hη'_v v hvH]
    exact hComp.pt_eq v hvH (hη'_v v hvH ▸ hv_seg)
  have hv_bdΔ : v ∈ subBd Δ := hpt_v ▸ (hsoc_star_Ω.1 ▸ hv_bar_star).2
  exact hv_not_Δ (hΔ.isClosed.closure_subset_iff.mpr Subset.rfl hv_bdΔ.1)

private theorem replacement_disc_segregation_is_tangle_local
    {S : Type u}
    [TopologicalSpace S]
    [T2Space S]
    {α : Type v}
    {β : Type w}
    (G₀ : Graph α β)
    (G' : Graph α β)
    (J : Graph α β)
    (H : Drawing S)
    (η₀ : SpanEmbedding H G₀)
    (η' : SpanEmbedding H G')
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ)
    (θ : ℕ)
    (beta : ℕ)
    (S_seg : Set (Society α β))
    (α_disc : Society α β → Set S)
    (α_pt : α → S)
    (Δ : Set S)
    (localSociety : Society α β)
    (hMetric : HasTangleMetric H θ T d)
    (hθ : 16 * beta + 17 ≤ θ)
    (hJ : IsBridge G₀ η₀.imageGraph J)
    (hDisj_E : Disjoint E(G') E(J))
    (hη'_e : ∀ e ∈ H.E, η'.eMap e = η₀.eMap e)
    (hComp : IsCompatibleWith G' H η' S_seg α_disc α_pt)
    (hsoc_star_G : localSociety.G = subgraphUnion G₀ J (arrangementPullbackGraph G' S_seg α_disc
      α_pt
      Δ))
    (hP_le_G₀ : (arrangementPullbackGraph G' S_seg α_disc α_pt Δ) ≤ G₀)
    (S_seg_0 : Set (Society α β))
    (h3seg_0 : IsThreeSegregation localSociety.G S_seg_0) :
    ∀ S₀ ∈ (S_seg_0 \ ({A | A ∈ S_seg ∧ ¬α_disc A ⊆ Δ})), ∀ (B : Graph α β), IsGraphSeparation G₀
      S₀.G B → V(S₀.G) ∩ V(B) = S₀.Ω.bar → ∃ A_H B_H, H.toHypergraph.IsSeparation A_H B_H ∧
      A_H.vertexSet = {v | v ∈ H.V ∧ η₀.vMap v ∈ V(S₀.G)} ∧ B_H.vertexSet = {v | v ∈ H.V ∧ η₀.vMap
      v ∈ V(B)} ∧ A_H.edgeSet = {e | e ∈ H.E ∧ η₀.eMap e ∈ E(S₀.G)} ∧ B_H.edgeSet = {e | e ∈ H.E ∧
      η₀.eMap e ∈ E(B)} ∧ ((A_H, B_H) ∈ T ∨ (B_H, A_H) ∈ T) ∧ B_H.separationOrder A_H ≤ 3 ∧ ∀ e ∈
      A_H.edgeSet, (e ∩ Δ).Nonempty := by
  let P_Δ := arrangementPullbackGraph G' S_seg α_disc α_pt Δ
  let S_seg₂ := {A | A ∈ S_seg ∧ ¬α_disc A ⊆ Δ}
  let S_seg_star := S_seg_0 \ S_seg₂
  intro S₀ hS₀ B hsepB hVB_eq
  have hS₀_0 : S₀ ∈ S_seg_0 := hS₀.1
  have hS₀_le_star : S₀.G ≤ localSociety.G := h3seg_0.1.le S₀ hS₀_0
  let mkSub (X : Graph α β) (hX : X ≤ G₀) : Hypergraph S (Set S) :=
    { vertexSet := {v ∈ H.V | η₀.vMap v ∈ V(X)}
      edgeSet := {e ∈ H.E | η₀.eMap e ∈ E(X)}
      Inc := fun e v => H.toHypergraph.Inc e v ∧ e ∈ H.E ∧ η₀.eMap e ∈ E(X)
      vertex_mem_of_inc := fun e v h => by
        refine ⟨h.1.2.1, ?_⟩
        obtain ⟨w, hlink_im⟩ := (η₀.inc_iff e h.2.1 v h.1.2.1).mpr h.1.2.2
        have hlink_G₀ : G₀.IsLink (η₀.eMap e) (η₀.vMap v) w :=
          (η₀.imageGraph_le.isLink_iff (η₀.bijOn_e.mapsTo h.2.1)).mp hlink_im
        exact ((hX.isLink_iff h.2.2).mpr hlink_G₀).left_mem
      edge_mem_of_inc := fun _ _ h => h.2
      vertexSet_finite := H.finite_V.subset fun _ h => h.1
      edgeSet_finite := H.finite_edges.subset fun _ h => h.1 }
  have hmk_le : ∀ (X : Graph α β) (hX : X ≤ G₀), mkSub X hX ≤ H.toHypergraph := by
    intro X hX
    refine ⟨fun _ h => h.1, fun _ h => h.1, fun e he => ?_⟩
    ext v
    change H.toHypergraph.Inc e v ↔ H.toHypergraph.Inc e v ∧ e ∈ H.E ∧ η₀.eMap e ∈ E(X)
    exact ⟨fun h => ⟨h, he.1, he.2⟩, fun h => h.1⟩
  let A_H := mkSub S₀.G hsepB.1
  let B_H := mkSub B hsepB.2.1
  have hAl : A_H ≤ H.toHypergraph := hmk_le S₀.G hsepB.1
  have hBl : B_H ≤ H.toHypergraph := hmk_le B hsepB.2.1
  have hsep_H : H.toHypergraph.IsSeparation A_H B_H := by
    refine (GM10.isSeparation_iff_of_le hAl hBl).mpr ⟨?_, ?_, ?_⟩
    · ext v
      change (v ∈ H.V ∧ η₀.vMap v ∈ V(S₀.G) ∨ v ∈ H.V ∧ η₀.vMap v ∈ V(B)) ↔ v ∈ H.V
      refine ⟨by rintro (⟨hv, _⟩ | ⟨hv, _⟩) <;> exact hv, fun hv => ?_⟩
      have hvG₀ : η₀.vMap v ∈ V(S₀.G) ∪ V(B) := by
        rw [hsepB.2.2.1]
        exact η₀.imageGraph_le.vertexSet_mono (η₀.bijOn_v.mapsTo hv)
      rcases hvG₀ with hvA | hvB
      · exact Or.inl ⟨hv, hvA⟩
      · exact Or.inr ⟨hv, hvB⟩
    · ext e
      change (e ∈ H.E ∧ η₀.eMap e ∈ E(S₀.G) ∨ e ∈ H.E ∧ η₀.eMap e ∈ E(B)) ↔ e ∈ H.E
      refine ⟨by rintro (⟨he, _⟩ | ⟨he, _⟩) <;> exact he, fun he => ?_⟩
      have heG₀ : η₀.eMap e ∈ E(S₀.G) ∪ E(B) := by
        rw [hsepB.2.2.2.1]
        exact η₀.imageGraph_le.edgeSet_mono (η₀.bijOn_e.mapsTo he)
      rcases heG₀ with heA | heB
      · exact Or.inl ⟨he, heA⟩
      · exact Or.inr ⟨he, heB⟩
    · ext e
      change ((e ∈ H.E ∧ η₀.eMap e ∈ E(S₀.G)) ∧ (e ∈ H.E ∧ η₀.eMap e ∈ E(B))) ↔
        e ∈ (∅ : Set (Set S))
      simp only [mem_empty_iff_false, iff_false]
      rintro ⟨⟨_, heA⟩, ⟨_, heB⟩⟩
      exact Set.disjoint_left.mp hsepB.2.2.2.2 heA heB
  have hord_BA : separationOrder B_H A_H ≤ 3 := by
    have hsub_img : η₀.vMap '' (B_H ∩ A_H).vertexSet ⊆ S₀.Ω.bar := by
      rintro x ⟨v, ⟨hvB, hvA⟩, rfl⟩
      rw [← hVB_eq]
      exact ⟨hvA.2, hvB.2⟩
    have hinj : InjOn η₀.vMap (B_H ∩ A_H).vertexSet :=
      η₀.bijOn_v.injOn.mono fun v ⟨hvB, _⟩ => hvB.1
    calc separationOrder B_H A_H
      _ = (η₀.vMap '' (B_H ∩ A_H).vertexSet).ncard := hinj.ncard_image.symm
      _ ≤ S₀.Ω.bar.ncard := Set.ncard_le_ncard hsub_img S₀.Ω.finite_bar
      _ ≤ 3 := h3seg_0.2 S₀ hS₀_0
  have hord_AB : separationOrder A_H B_H < θ := by
    have hcomm : (A_H ∩ B_H).vertexSet = (B_H ∩ A_H).vertexSet := Set.inter_comm _ _
    have hle3 : separationOrder A_H B_H ≤ 3 := by
      simpa [separationOrder, hcomm] using hord_BA
    omega
  have hor_T : (A_H, B_H) ∈ T ∨ (B_H, A_H) ∈ T :=
    hMetric.1.2.1.axiom1 hsep_H hord_AB
  refine ⟨A_H, B_H, hsep_H, rfl, rfl, rfl, rfl, hor_T, hord_BA, ?_⟩
  rintro e ⟨heH, heS₀⟩
  have he_star : η₀.eMap e ∈ E(localSociety.G) := hS₀_le_star.edgeSet_mono heS₀
  rw [hsoc_star_G, edgeSet_subgraphUnion hJ.2.1 hP_le_G₀] at he_star
  have he_G' : η₀.eMap e ∈ E(G') :=
    hη'_e e heH ▸ η'.imageGraph_le.edgeSet_mono (η'.bijOn_e.mapsTo heH)
  have he_P : η₀.eMap e ∈ E(P_Δ) :=
    he_star.resolve_left (fun heJ => Set.disjoint_left.mp hDisj_E he_G' heJ)
  rw [← hη'_e e heH] at he_P
  change η'.eMap e ∈ E(arrangementPullbackGraph G' S_seg α_disc α_pt Δ) at he_P
  rw [arrangementPullbackGraph, edgeSet_restrict] at he_P
  obtain ⟨A', ⟨hA'_S, hA'_sub⟩, heA'⟩ := mem_iUnion₂.mp he_P.2
  have he_sub_Δ : e ⊆ Δ := ((hComp.inter_E_iff A' hA'_S e heH).mpr heA').trans hA'_sub
  obtain ⟨p, hp⟩ := heH.1
  exact ⟨p, hp, he_sub_Δ hp⟩

/-- Local disc-replacement and arrangement-gluing step in Case 2 of the proof of Graph Minors XIV,
(10.1) (page 50), proved from `(8.1)` (`theorem_8_1_proof`) and `(6.5)` (`theorem_6_5_proof`). -/
private theorem disc_replacement_gluing_10_1 {α : Type v} {β : Type w}
    (G₀ G' J : Graph α β) (H : Drawing S) (η₀ : SpanEmbedding H G₀) (η' : SpanEmbedding H G')
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ) (θ beta : ℕ)
    (S_seg : Set (Society α β)) (α_disc : Society α β → Set S) (α_pt : α → S)
    (Δ : Set S) (localSociety : Society α β)
    (hS : IsClosedSurface S)
    (hMetric : HasTangleMetric H θ T d) (hθ : 16 * beta + 17 ≤ θ)
    (hJ : IsBridge G₀ η₀.imageGraph J)
    (hG'_le : G' ≤ G₀) (hG₀_eq : G₀ = subgraphUnion G₀ G' J)
    (hDisj_E : Disjoint E(G') E(J)) (hInter_V : V(G') ∩ V(J) ⊆ V(η₀.imageGraph))
    (hη'_v : ∀ v ∈ H.V, η'.vMap v = η₀.vMap v)
    (hη'_e : ∀ e ∈ H.E, η'.eMap e = η₀.eMap e)
    (hSeg : IsThreeSegregation G' S_seg)
    (hLoc : IsTangleLocal G' H η' T S_seg)
    (hArr : IsSurfaceArrangement S_seg α_disc α_pt)
    (hComp : IsCompatibleWith G' H η' S_seg α_disc α_pt)
    (hΔ : IsClosedDisc Δ)
    (hNorm : IsArrangementNormal S_seg α_disc α_pt (subBd Δ))
    (hRig_Δ : IsRigidIn (H.interSet Δ) Δ)
    (hVJ_Δ : ∀ v ∈ H.V, η₀.vMap v ∈ V(J) → v ∈ Δ \ subBd Δ)
    (hsoc_star_G : localSociety.G = subgraphUnion G₀ J (arrangementPullbackGraph G' S_seg α_disc
      α_pt
      Δ))
    (hsoc_star_Ω : IsPullbackPerm S_seg α_pt (subBd Δ) localSociety.Ω)
    (hno_crooked2 : ∀ P_set : Set (Graph α β), localSociety.IsCrookedTransaction P_set
      → P_set.ncard ≠ 2) :
    ∃ (S_seg_star : Set (Society α β))
      (α_disc_star : Society α β → Set S) (α_pt_star : α → S),
      (∀ S₀ ∈ S_seg_star, ∀ B : Graph α β,
        IsGraphSeparation G₀ S₀.G B → V(S₀.G) ∩ V(B) = S₀.Ω.bar →
        ∃ A_H B_H : Hypergraph S (Set S),
          H.toHypergraph.IsSeparation A_H B_H ∧
          A_H.vertexSet = {v ∈ H.V | η₀.vMap v ∈ V(S₀.G)} ∧
          B_H.vertexSet = {v ∈ H.V | η₀.vMap v ∈ V(B)} ∧
          A_H.edgeSet = {e ∈ H.E | η₀.eMap e ∈ E(S₀.G)} ∧
          B_H.edgeSet = {e ∈ H.E | η₀.eMap e ∈ E(B)} ∧
          ((A_H, B_H) ∈ T ∨ (B_H, A_H) ∈ T) ∧
          separationOrder B_H A_H ≤ 3 ∧
          (∀ e ∈ A_H.edgeSet, (e ∩ Δ).Nonempty)) ∧
      (IsTangleLocal G₀ H η₀ T S_seg_star →
        let S_seg₂ := {S₀ ∈ S_seg | ¬ (α_disc S₀ ⊆ Δ)}
        let S_seg' := S_seg₂ ∪ S_seg_star
        IsThreeSegregation G₀ S_seg' ∧
        IsTangleLocal G₀ H η₀ T S_seg' ∧
        IsSurfaceArrangement S_seg'
          (gluedArrangementDisc S_seg₂ α_disc α_disc_star)
          (gluedArrangementPt S_seg₂ α_pt α_pt_star) ∧
        IsCompatibleWith G₀ H η₀ S_seg'
          (gluedArrangementDisc S_seg₂ α_disc α_disc_star)
          (gluedArrangementPt S_seg₂ α_pt α_pt_star)) := by
  classical
  let P_Δ := arrangementPullbackGraph G' S_seg α_disc α_pt Δ
  have hP_le_G' : P_Δ ≤ G' := restrict_le.trans (G'.induce_le inter_subset_right)
  have hP_le_G₀ : P_Δ ≤ G₀ := hP_le_G'.trans hG'_le
  have hstar_le : localSociety.G ≤ G₀ := by
    rw [hsoc_star_G]
    exact subgraphUnion_le hJ.2.1 hP_le_G₀
  -- Step 1: Apply `(8.1)` (`exists_surface_arrangement_in_disc_of_8_1`) to `localSociety` in `Δ`.
  have hinj_bar : InjOn α_pt localSociety.Ω.bar :=
    hArr.injOn_pts.mono (fun v hv => (hsoc_star_Ω.1 ▸ hv).1)
  obtain ⟨S_seg_0, α_disc_0, α_pt_0, h3seg_0, hbar_0, harr_0,
      hdisc_0_sub, hpt_0_eq, hpt_0_mem, hpt_0_int, hdisc_0_inter_bd⟩ :=
    exists_surface_arrangement_in_disc_of_8_1 hS hΔ localSociety hno_crooked2
      α_pt hinj_bar hsoc_star_Ω.2
  have hseg_0_sub_V : segregationVertices S_seg_0 ⊆ V(localSociety.G) := by
    intro v hv
    rcases mem_iUnion₂.mp hv with ⟨B, hB, hvB⟩
    exact (h3seg_0.1.le B hB).vertexSet_mono (B.bar_subset hvB)
  -- Step 2: Establish properties of `H.interSet Δ` and construct `η_Δ : SpanEmbedding (H.interSet
  -- Δ) localSociety.G`.
  have hEdges_Δ : ∀ e ∈ H.E, (e ∩ Δ).Nonempty →
      ∃ A ∈ S_seg, α_disc A ⊆ Δ ∧ η'.eMap e ∈ E(A.G) ∧ e ⊆ Δ := by
    exact edges_meeting_replacement_disc_are_carried_inside (S := S) (α := α) (β := β) G' H η'
      S_seg α_disc α_pt Δ hS hSeg hArr hComp hΔ hNorm
  obtain ⟨hV_HΔ, hU_HΔ⟩ :=
    interSet_V_and_U_of_edges hΔ.isClosed (fun e he hne => (hEdges_Δ e he hne).choose_spec.2.2.2)
  have hE_HΔ : (H.interSet Δ).E = {e ∈ H.E | e ⊆ Δ} := interSet_E H Δ
  have hHV_Δ_mem_P : ∀ v ∈ H.V, v ∈ Δ → η₀.vMap v ∈ V(P_Δ) := by
    exact vertices_in_replacement_disc_belong_to_pullback (S := S) (α := α) (β := β) G₀ G' H η₀ η'
      S_seg α_disc α_pt Δ hS hη'_v hSeg hArr hComp hΔ hNorm
  have hHV_bdΔ_mem_bar : ∀ v ∈ H.V, v ∈ subBd Δ →
      η₀.vMap v ∈ localSociety.Ω.bar ∧ α_pt (η₀.vMap v) = v := by
    exact vertices_on_replacement_boundary_belong_to_society (S := S) (α := α) (β := β) G₀ G' H η₀
      η' S_seg α_disc α_pt Δ localSociety hη'_v hSeg hArr hComp hNorm hsoc_star_Ω
  let η_Δ₀ : SpanEmbedding (H.interSet Δ) G₀ :=
    restrictSpan η₀ (H.V ∩ Δ) {e | e ∈ H.E ∧ e ⊆ Δ}
  have hle_star : η_Δ₀.imageGraph ≤ localSociety.G := by
    refine ⟨?_, fun b x y hlink => ?_⟩
    · rw [← η_Δ₀.bijOn_v.image_eq, hV_HΔ]
      rintro _ ⟨v, ⟨hvH, hvΔ⟩, rfl⟩
      rw [hsoc_star_G, vertexSet_subgraphUnion]
      exact Or.inr (hHV_Δ_mem_P v hvH hvΔ)
    · have hb_im : b ∈ E(η_Δ₀.imageGraph) := hlink.edge_mem
      rw [← η_Δ₀.bijOn_e.image_eq, hE_HΔ] at hb_im
      obtain ⟨e, ⟨heH, he_sub⟩, rfl⟩ := hb_im
      obtain ⟨p, hp⟩ := heH.1
      obtain ⟨A, hA, hA_sub, heA, _⟩ := hEdges_Δ e heH ⟨p, hp, he_sub hp⟩
      have hb_star : η₀.eMap e ∈ E(localSociety.G) := by
        rw [hsoc_star_G, edgeSet_subgraphUnion hJ.2.1 hP_le_G₀]
        refine Or.inr ?_
        rw [← hη'_e e heH]
        change η'.eMap e ∈ E(arrangementPullbackGraph G' S_seg α_disc α_pt Δ)
        rw [arrangementPullbackGraph, edgeSet_restrict]
        obtain ⟨u_e, v_e, huv_A⟩ := A.G.exists_isLink_of_mem_edgeSet heA
        have huv_G' : G'.IsLink (η'.eMap e) u_e v_e := huv_A.mono (hSeg.1.le A hA)
        exact ⟨⟨u_e, v_e, huv_G',
          ⟨Or.inl (mem_iUnion₂.mpr ⟨A, ⟨hA, hA_sub⟩, huv_A.left_mem⟩), huv_G'.left_mem⟩,
          ⟨Or.inl (mem_iUnion₂.mpr ⟨A, ⟨hA, hA_sub⟩, huv_A.right_mem⟩), huv_G'.right_mem⟩⟩,
          mem_iUnion₂.mpr ⟨A, ⟨hA, hA_sub⟩, heA⟩⟩
      exact (hstar_le.isLink_iff hb_star).mpr (hlink.mono η_Δ₀.imageGraph_le)
  let η_Δ : SpanEmbedding (H.interSet Δ) localSociety.G :=
    { η_Δ₀ with imageGraph_le := hle_star }
  -- Step 3: Apply `(6.5)` (`theorem_6_5_proof`) to obtain `(α_disc_star, α_pt_star)` compatible
  -- with `H.interSet Δ`.
  have hHΔ_U : (H.interSet Δ).U ⊆ Δ := hU_HΔ ▸ inter_subset_right
  have hbd_in_seg_0 : ∀ v ∈ (H.interSet Δ).V ∩ subBd Δ, η_Δ.vMap v ∈ segregationVertices S_seg_0
    := by
    rintro v ⟨hv_HΔ, hv_bd⟩
    rw [hV_HΔ] at hv_HΔ
    exact hbar_0 (hHV_bdΔ_mem_bar v hv_HΔ.1 hv_bd).1
  have hα_0_id : ∀ v ∈ (H.interSet Δ).V ∩ subBd Δ, α_pt_0 (η_Δ.vMap v) = v := by
    rintro v ⟨hv_HΔ, hv_bd⟩
    rw [hV_HΔ] at hv_HΔ
    obtain ⟨hv_bar, hpt_v⟩ := hHV_bdΔ_mem_bar v hv_HΔ.1 hv_bd
    exact (hpt_0_eq (η₀.vMap v) hv_bar).trans hpt_v
  have hbdΔ : subBd Δ = discBd Δ := by
    rw [← IsClosedDisc.frontier_eq_discBd hS hΔ, frontier_eq_closure_inter_closure, subBd,
      Set.compl_eq_univ_sdiff]
  have hHΔ_bd : (H.interSet Δ).U ∩ subBd Δ ⊆ (H.interSet Δ).V := by
    rintro p ⟨hpU, hpbd⟩
    rw [hU_HΔ] at hpU
    rw [hV_HΔ]
    refine ⟨?_, hpU.2⟩
    by_contra hpV
    obtain ⟨e, he, hpe⟩ := H.exists_edge_of_mem hpU.1 hpV
    obtain ⟨A, hA, -, heA, -⟩ := hEdges_Δ e he ⟨p, hpe, hpU.2⟩
    obtain ⟨y, hy_bar, rfl⟩ := hNorm A hA ⟨hpbd, (hComp.inter_E_iff A hA e he).mpr heA hpe⟩
    have hx_bdA : α_pt y ∈ H.U ∩ subBd (α_disc A) :=
      ⟨hpU.1, (hArr.isClosedDisc A hA).2 y hy_bar⟩
    rw [hComp.bd_inter_eq A hA] at hx_bdA
    exact hpV hx_bdA.1
  have hα_0_bd : ∀ v ∈ (H.interSet Δ).V, η_Δ.vMap v ∈ segregationVertices S_seg_0 →
      α_pt_0 (η_Δ.vMap v) ∈ subBd Δ → v ∈ subBd Δ := by
    intro v hv hv_seg hv_bd
    rw [hV_HΔ] at hv
    have hbar : η_Δ.vMap v ∈ localSociety.Ω.bar := by
      by_contra hn
      exact (hpt_0_int _ hv_seg hn).2 hv_bd
    have hbar' := hbar
    rw [hsoc_star_Ω.1] at hbar'
    have hseg' : η'.vMap v ∈ segregationVertices S_seg := (hη'_v v hv.1).symm ▸ hbar'.1
    have hpt : α_pt (η'.vMap v) = v := hComp.pt_eq v hv.1 hseg'
    have hbd' : α_pt (η'.vMap v) ∈ subBd Δ := (hη'_v v hv.1).symm ▸ hbar'.2
    rwa [hpt] at hbd'
  obtain ⟨α_disc_star, α_pt_star, harr_star, hdisc_star_sub, hcomp_star,
      hpt_star_bd, hpt_star_int, hdisc_star_bd_eq⟩ :=
    theorem_6_5_proof hΔ hbdΔ hHΔ_U hHΔ_bd hRig_Δ η_Δ
      h3seg_0 hbd_in_seg_0 harr_0 hdisc_0_sub hα_0_id hα_0_bd
  have hpt_star_eq : ∀ v ∈ localSociety.Ω.bar, α_pt_star v = α_pt v := by
    intro v hv
    have hv_bd : α_pt_0 v ∈ subBd Δ := hpt_0_eq v hv ▸ (hsoc_star_Ω.1 ▸ hv).2
    exact (hpt_star_bd v hv_bd).trans (hpt_0_eq v hv)
  have hpt_star_mem : ∀ v ∈ segregationVertices S_seg_0, α_pt_star v ∈ Δ := by
    intro v hv
    by_cases hv_bar : v ∈ localSociety.Ω.bar
    · rw [hpt_star_eq v hv_bar]
      exact hΔ.isClosed.closure_subset_iff.mpr Subset.rfl ((hsoc_star_Ω.1 ▸ hv_bar).2.1)
    · exact (hpt_star_int v (hpt_0_int v hv hv_bar)).1
  have hdisc_star_inter_bd : ∀ B ∈ S_seg_0,
      α_disc_star B ∩ subBd Δ ⊆ α_pt_star '' (B.Ω.bar ∩ localSociety.Ω.bar) := by
    intro B hB x hx
    rw [hdisc_star_bd_eq B hB] at hx
    obtain ⟨v, ⟨hvB, hv_star⟩, rfl⟩ := hdisc_0_inter_bd B hB hx
    refine ⟨v, ⟨hvB, hv_star⟩, ?_⟩
    rw [hpt_star_eq v hv_star, hpt_0_eq v hv_star]
  -- Define `S_seg₂` and `S_seg_star = S_seg_0 \ S_seg₂`.
  let S_seg₂ : Set (Society α β) := {A ∈ S_seg | ¬ (α_disc A ⊆ Δ)}
  let S_seg_star : Set (Society α β) := S_seg_0 \ S_seg₂
  refine ⟨S_seg_star, α_disc_star, α_pt_star, ?_, ?_⟩
  · exact replacement_disc_segregation_is_tangle_local (S := S) (α := α) (β := β) G₀ G' J H η₀ η'
      T d θ beta S_seg α_disc α_pt Δ localSociety hMetric hθ hJ hDisj_E hη'_e hComp hsoc_star_G
      hP_le_G₀ S_seg_0 h3seg_0
  · -- Part 2: Gluing `S_seg₂` and `S_seg_star` once `IsTangleLocal G₀ H η₀ T S_seg_star` holds.
    intro hLoc_star
    let S_seg' : Set (Society α β) := S_seg₂ ∪ S_seg_star
    have hS_seg'_eq : S_seg' = S_seg₂ ∪ S_seg_0 := by
      ext B
      simp only [S_seg', S_seg_star, mem_union, mem_sdiff]
      tauto
    let α'_disc := gluedArrangementDisc S_seg₂ α_disc α_disc_star
    let α'_pt := gluedArrangementPt S_seg₂ α_pt α_pt_star
    have hα'_disc_S₂ : ∀ {B : Society α β}, B ∈ S_seg₂ → α'_disc B = α_disc B := by
      intro B hB
      simp [α'_disc, gluedArrangementDisc, hB]
    have hα'_disc_star : ∀ {B : Society α β}, B ∈ S_seg_star → α'_disc B = α_disc_star B := by
      intro B hB
      have hnot : B ∉ S_seg₂ := hB.2
      simp [α'_disc, gluedArrangementDisc, hnot]
    have hα'_pt_S₂ : ∀ {v : α}, v ∈ segregationVertices S_seg₂ → α'_pt v = α_pt v := by
      intro v hv
      simp [α'_pt, gluedArrangementPt, hv]
    have hα'_pt_0 : ∀ {v : α}, v ∈ segregationVertices S_seg_0 → α'_pt v = α_pt_star v := by
      intro v hv_0
      by_cases hv_S₂ : v ∈ segregationVertices S_seg₂
      · rw [hα'_pt_S₂ hv_S₂]
        obtain ⟨A, hA_S₂, hvA⟩ := mem_iUnion₂.mp hv_S₂
        have hv_bar_star : v ∈ localSociety.Ω.bar :=
          (claim_1_of_10_1 hS hJ hG'_le hDisj_E hInter_V hη'_v hSeg hArr hComp
            hΔ hNorm hVJ_Δ hsoc_star_G hsoc_star_Ω hA_S₂.1 hA_S₂.2).2
            ⟨hseg_0_sub_V hv_0, A.bar_subset hvA⟩
        exact (hpt_star_eq v hv_bar_star).symm
      · simp [α'_pt, gluedArrangementPt, hv_S₂]
    have hS₂fin : S_seg₂.Finite := hSeg.1.finite.subset fun _ h => h.1
    have hFin' : S_seg'.Finite := hS₂fin.union (h3seg_0.1.finite.subset sdiff_subset)
    have hLe' : ∀ B ∈ S_seg', B.G ≤ G₀ := by
      rintro B (hB_S₂ | hB_star)
      · exact (hSeg.1.le B hB_S₂.1).trans hG'_le
      · exact (h3seg_0.1.le B hB_star.1).trans hstar_le
    -- `IsThreeSegregation G₀ S_seg'`
    have h3seg' : IsThreeSegregation G₀ S_seg' := by
      exact replacement_bridge_pieces_form_three_segregation (S := S) (α := α) (β := β) G₀ G' J H
        η₀ η' S_seg α_disc α_pt Δ localSociety hS hJ hG'_le hG₀_eq hDisj_E hInter_V hη'_v hSeg hArr
        hComp hΔ hNorm hVJ_Δ hsoc_star_G hsoc_star_Ω hP_le_G₀ S_seg_0 h3seg_0 hbar_0 hS_seg'_eq
        hFin' hLe'
    -- `IsTangleLocal G₀ H η₀ T S_seg'`
    have hLoc' : IsTangleLocal G₀ H η₀ T S_seg' := by
      exact replacement_bridge_segregation_is_tangle_local (S := S) (α := α) (β := β) G₀ G' H η₀
        η' T S_seg α_disc Δ hG'_le hη'_v hη'_e hSeg hLoc S_seg_0 hLoc_star
    -- `IsSurfaceArrangement S_seg' α'_disc α'_pt`
    have hArr' : IsSurfaceArrangement S_seg' α'_disc α'_pt := by
      exact replacement_bridge_discs_form_surface_arrangement (S := S) (α := α) (β := β) S_seg
        α_disc α_pt Δ localSociety hS hArr hΔ hNorm hsoc_star_Ω S_seg_0 hbar_0 α_disc_star α_pt_star
        harr_star hdisc_star_sub hpt_star_eq hpt_star_mem hdisc_star_inter_bd α'_disc α'_pt
        hα'_disc_S₂ hα'_disc_star hα'_pt_S₂ hα'_pt_0
    -- `IsCompatibleWith G₀ H η₀ S_seg' α'_disc α'_pt`
    have hHV_mem_star_imp_Δ : ∀ v ∈ H.V, η₀.vMap v ∈ V(localSociety.G) → v ∈ Δ := by
      exact replacement_society_uses_vertices_inside_disc (S := S) (α := α) (β := β) G₀ G' J H η₀
        η' S_seg α_disc α_pt Δ localSociety hS hJ hG'_le hDisj_E hInter_V hη'_v hSeg hArr hComp hΔ
        hNorm hVJ_Δ hsoc_star_G hsoc_star_Ω
    have hComp' : IsCompatibleWith G₀ H η₀ S_seg' α'_disc α'_pt := by
      exact replacement_bridge_arrangement_is_compatible (S := S) (α := α) (β := β) G₀ G' J H η₀
        η' S_seg α_disc α_pt Δ localSociety hJ hDisj_E hη'_v hη'_e hComp hΔ hsoc_star_G hP_le_G₀
        S_seg_0 h3seg_0 hseg_0_sub_V hV_HΔ hU_HΔ hE_HΔ η_Δ rfl rfl α_disc_star α_pt_star
          hdisc_star_sub
        hcomp_star α'_disc α'_pt hα'_disc_S₂ hα'_disc_star hα'_pt_S₂ hα'_pt_0 hHV_mem_star_imp_Δ
    exact ⟨h3seg', hLoc', hArr', hComp'⟩

/-! ## Inductive Bridge Step for (10.1) (pages 49–50) -/

/-- **Inductive bridge step in the proof of (10.1)** (Graph Minors XIV, Section 10, pages 49–50):
given a bridge `J` of `H` in `G₀` with `u ∈ H.V` and `η₀(u) ∈ V(J)`, a `T`-local 3-segregation
`S_seg` of `G'` (the union of `H` and all other bridges), and an arrangement `α` compatible with
`H`, we apply `(9.6)` (`theorem_9_6_proof` with `π = 2`), rule out `(9.6)(iv)(a)` via hypothesis
`(ii)`,
and apply `(8.1)` (`Theorem81Statement`), `(6.1)` (`theorem_6_1_proof`), `(6.5)`
(`theorem_6_5_proof`), and
`(7.3)` (`theorem_7_3_proof`) to construct a `T`-local 3-segregation of `G₀` and an arrangement
compatible with `H`. -/
theorem bridge_step_10_1 {α : Type v} {β : Type w}
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    (G₀ G' J : Graph α β) (B_rem : Set (Graph α β))
    (H : Drawing S) (η₀ : SpanEmbedding H G₀) (η' : SpanEmbedding H G')
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ) (θ beta : ℕ)
    (hV_fin : V(G₀).Finite) (hE_fin : E(G₀).Finite)
    (hRig : IsRigid H) (hMetric : HasTangleMetric H θ T d)
    (hbeta : 12 ≤ beta ∧ Even beta) (hθ : 16 * beta + 17 ≤ θ)
    (hJ : IsBridge G₀ η₀.imageGraph J)
    (hB_rem : ∀ B ∈ B_rem, IsBridge G₀ η₀.imageGraph B)
    (hJ_not_rem : J ∉ B_rem)
    (hJ_eq : J = subgraphSUnion G₀ {J})
    (hG'_eq : G' = subgraphSUnion G₀ {η₀.imageGraph, subgraphSUnion G₀ B_rem})
    (hG'_le : G' ≤ G₀)
    (hG₀_eq : G₀ = subgraphUnion G₀ G' J)
    (hDisj_E : Disjoint E(G') E(J))
    (hInter_V : V(G') ∩ V(J) ⊆ V(η₀.imageGraph))
    (hη'_v : ∀ v ∈ H.V, η'.vMap v = η₀.vMap v)
    (hη'_e : ∀ e ∈ H.E, η'.eMap e = η₀.eMap e)
    (u : S) (huV : u ∈ H.V)
    (hJ_dist : ∀ v ∈ H.V, η₀.vMap v ∈ V(J) → d {u} {v} < beta)
    (hii_no_eye : ∀ (Λ : Set S)
      (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d' : Set S → Set S → ℕ)
      (η_cl : SpanEmbedding (clearedSubdrawing H Λ) G₀),
      IsLambdaZoneAround H d (3 * beta + 3) {u} Λ →
      IsClearedTangle H T d θ (3 * beta + 3) Λ T' d' →
      IsRigid (clearedSubdrawing H Λ) →
      (∀ v ∈ (clearedSubdrawing H Λ).V, η_cl.vMap v = η₀.vMap v) →
      (∀ e ∈ (clearedSubdrawing H Λ).E, η_cl.eMap e = η₀.eMap e) →
      ¬ IsDrawingEye G₀ (clearedSubdrawing H Λ) η_cl (θ - 4 * (3 * beta + 3) - 2) T' Λ)
    (S_seg : Set (Society α β)) (α_disc : Society α β → Set S) (α_pt : α → S)
    (hSeg : IsThreeSegregation G' S_seg)
    (hLoc : IsTangleLocal G' H η' T S_seg)
    (hArr : IsSurfaceArrangement S_seg α_disc α_pt)
    (hComp : IsCompatibleWith G' H η' S_seg α_disc α_pt) :
    ∃ (S_seg_G : Set (Society α β)) (α_disc_G : Society α β → Set S) (α_pt_G : α → S),
      IsThreeSegregation G₀ S_seg_G ∧ IsTangleLocal G₀ H η₀ T S_seg_G ∧
      IsSurfaceArrangement S_seg_G α_disc_G α_pt_G ∧
      IsCompatibleWith G₀ H η₀ S_seg_G α_disc_G α_pt_G := by
  have huA : ({u} : Set S) ∈ H.A := Or.inl (Or.inl ⟨u, huV, rfl⟩)
  have hB_J : ∀ B ∈ ({J} : Set (Graph α β)), IsBridge G₀ η₀.imageGraph B := by
    rintro B rfl; exact hJ
  have hDisj_B : Disjoint ({J} : Set (Graph α β)) B_rem :=
    Set.disjoint_singleton_left.mpr hJ_not_rem
  -- Step 1: Apply `(9.6)` (`theorem_9_6_proof`) with `π = 2` and `z = {u}`
  obtain ⟨Λ, Δ, T₁, d₁, clearedEmbedding, clearedSociety, localSociety,
      hZone, hCleared, hΔ_disc, hNorm_Δ, hΛ_sub_Δ,
      h96_i, h96_ii, hCout, hRig_Λ,
      hη_Λ_v, hη_Λ_e, _, _, hNat_Λ,
      hsoc_star_G, hsoc_star_Ω, h96_iv⟩ :=
    theorem_9_6_proof G₀ G₀ G' J {J} B_rem H η₀ η' θ 2 beta T d {u}
      S_seg α_disc α_pt hS hConn hV_fin hE_fin hRig hMetric huA
      (by decide) (by decide) hbeta.1 hbeta.2 hθ
      hB_J hB_rem hDisj_B hJ_eq hG'_eq hG₀_eq hη'_v hη'_e hJ_dist
      hSeg hLoc hArr hComp
  -- Step 2: Rule out `(9.6)(iv)(a)` using `hii_no_eye` and `isDrawingEye_of_crookedTransaction`
  have hno_crooked2 : ∀ P_set : Set (Graph α β), localSociety.IsCrookedTransaction P_set →
      P_set.ncard ≠ 2 := by
    rcases h96_iv with ⟨P_set, X, hCrooked, hCard2, hPaths, hX_sub, hEnds, hFreeX⟩ | h_iv_b
    · exfalso
      have heye : IsDrawingEye G₀ (clearedSubdrawing H Λ) clearedEmbedding (θ - 4 *
        (3 * beta + 3) - 2) T₁ Λ :=
        isDrawingEye_of_crookedTransaction hZone hNat_Λ hCrooked hCard2 hPaths hX_sub hEnds hFreeX
          hCleared.hasMetric.1.2.1
      exact hii_no_eye Λ T₁ d₁ clearedEmbedding hZone hCleared hRig_Λ hη_Λ_v hη_Λ_e heye
    · intro P_set hCr hCardEq
      exact h_iv_b P_set hCr (by omega)
  -- Step 3: By `(6.1)` (`isRigidIn_of_normal_closedDisc`), `H ∩ Δ` is rigid in `Δ`
  have hRig_Δ : IsRigidIn (H.interSet Δ) Δ :=
    isRigidIn_of_normal_closedDisc hS hConn hRig hSeg hArr hComp hΔ_disc hNorm_Δ hCout
  have hVJ_Δ : ∀ v ∈ H.V, η₀.vMap v ∈ V(J) → v ∈ Δ \ subBd Δ := by
    intro v hvV hvJ
    exact h96_ii {v} (Or.inl (Or.inl ⟨v, hvV, rfl⟩)) (hJ_dist v hvV hvJ) (mem_singleton v)
  -- Step 4: Apply `disc_replacement_gluing_10_1` (`(8.1)` and `(6.5)`) to `localSociety` in `Δ`
  obtain ⟨S_seg_star, α_disc_star, α_pt_star, h73_sep, hglue⟩ :=
    disc_replacement_gluing_10_1
      G₀ G' J H η₀ η' T d θ beta S_seg α_disc α_pt Δ localSociety
      hS hMetric hθ hJ hG'_le hG₀_eq hDisj_E hInter_V
      hη'_v hη'_e hSeg hLoc hArr hComp hΔ_disc hNorm_Δ hRig_Δ hVJ_Δ
      hsoc_star_G hsoc_star_Ω hno_crooked2
  -- Step 5: Prove `IsTangleLocal G₀ H η₀ T S_seg_star` using `(7.3)` (`theorem_7_3_proof`) and
  -- `(9.6)(i)`
  have hE_ne : H.E.Nonempty := by
    obtain ⟨C_out, hCout_cir, hCout_sub⟩ := hCout
    obtain ⟨e₀, he₀⟩ := IsCircuit.E_nonempty hCout_cir
    exact ⟨e₀, (H.span_isSubdrawing _ _).2 (hCout_sub.2 he₀)⟩
  have hu_not_E : ({u} : Set S) ∉ H.E := fun huE =>
    (huE.2.1 (mem_singleton u)).2 huV
  have hlocal_star : IsTangleLocal G₀ H η₀ T S_seg_star := by
    intro S₀ hS₀ B hsepB hVB_eq
    rcases h73_sep S₀ hS₀ B hsepB hVB_eq with
      ⟨A_H, B_H, hsep_H, hAH_V, hBH_V, hAH_E, hBH_E, hor_T, _, hAH_Δ⟩
    refine ⟨A_H, B_H, hsep_H, hAH_V, hBH_V, hAH_E, hBH_E, ?_⟩
    rcases hor_T with hAB_in | hBA_in
    · exact hAB_in
    · exfalso
      have hAH_ne_u : A_H.edgeSet ≠ {{u}} := fun h_eq =>
        hu_not_E (hsep_H.left_le.edgeSet_subset (h_eq ▸ mem_singleton {u}))
      obtain ⟨e, he_in_A, hge⟩ :=
        theorem_7_3_proof H θ T d B_H A_H {u} hS hConn hE_ne hMetric huA hBA_in hAH_ne_u
      have heE : e ∈ H.E := hsep_H.left_le.edgeSet_subset he_in_A
      have heA : e ∈ H.A := Or.inl (Or.inr heE)
      have hle : d {u} e ≤ 3 * beta + 6 := h96_i e heA (hAH_Δ e he_in_A)
      omega
  -- Step 6: Glue `S_seg₂` and `S_seg_star` to obtain `S_seg'` and `(α'_disc, α'_pt)`
  rcases hglue hlocal_star with ⟨h3seg', hlocal', harr', hcompat'⟩
  exact ⟨{S₀ ∈ S_seg | ¬ (α_disc S₀ ⊆ Δ)} ∪ S_seg_star,
    gluedArrangementDisc {S₀ ∈ S_seg | ¬ (α_disc S₀ ⊆ Δ)} α_disc α_disc_star,
    gluedArrangementPt {S₀ ∈ S_seg | ¬ (α_disc S₀ ⊆ Δ)} α_pt α_pt_star,
    h3seg', hlocal', harr', hcompat'⟩

/-! ## Theorem (10.1) (pages 49–50) -/

/-- **Graph Minors XIV, (10.1)** (pages 49–50):
"Let $H$ be a 2-cell, rigid drawing in $\Sigma$, and let $\mathscr{T}$ be a respectful tangle
in $H$ of order $\theta$, with metric $d$. Let $H$ be a subgraph of $G$, let $\beta \ge 12$
be an even integer with $\theta \ge 16\beta + 17$, and suppose that* (i) $d(u, v) < \beta$
*for every $H$-path in $G$ with ends $u$, $v$ and* (ii) *if $\mathscr{T}'$ is the tangle of
order $\theta - 4(3\beta + 3) - 2$ obtained from $\mathscr{T}$ by clearing some $(3\beta +
3)$-zone $\Lambda$ such that $H \cap (\Sigma - \Lambda)$ is a rigid drawing in $\Sigma$,
then $\Lambda$ is not an eye of $H \cap (\Sigma - \Lambda)$ in $G$ with respect to
$\mathscr{T}'$.* *Then there is a $\mathscr{T}$-local 3-segregation of $G$ and an
arrangement of it in $\Sigma$ compatible with $H$." -/
theorem theorem_10_1_proof {α : Type v} {β : Type w}
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ) (θ beta : ℕ)
    (hV_fin : V(G).Finite) (hE_fin : E(G).Finite)
    (_h2cell : H.IsTwoCell) (hrigid : IsRigid H)
    (_hT : IsRespectfulDrawingTangle H θ T) (hmetric : HasTangleMetric H θ T d)
    (hbeta : 12 ≤ beta ∧ Even beta) (hθ : 16 * beta + 17 ≤ θ)
    (hi_path : ∀ (P : Graph α β) (u v : S),
      u ∈ H.V → v ∈ H.V →
      IsHPathWithEnds G η.imageGraph P (η.vMap u) (η.vMap v) →
      d {u} {v} < beta)
    (hii_no_eye : ∀ (Λ : Set S)
      (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d' : Set S → Set S → ℕ)
      (η_cl : SpanEmbedding (clearedSubdrawing H Λ) G),
      IsLambdaZone H d (3 * beta + 3) Λ →
      IsRigid (clearedSubdrawing H Λ) →
      IsClearedTangle H T d θ (3 * beta + 3) Λ T' d' →
      (∀ v ∈ (clearedSubdrawing H Λ).V, η_cl.vMap v = η.vMap v) →
      (∀ e ∈ (clearedSubdrawing H Λ).E, η_cl.eMap e = η.eMap e) →
      ¬ IsDrawingEye G (clearedSubdrawing H Λ) η_cl (θ - 4 * (3 * beta + 3) - 2) T' Λ) :
    ∃ (S_seg : Set (Society α β)) (α_disc : Society α β → Set S) (α_pt : α → S),
      IsThreeSegregation G S_seg ∧ IsTangleLocal G H η T S_seg ∧
      IsSurfaceArrangement S_seg α_disc α_pt ∧ IsCompatibleWith G H η S_seg α_disc α_pt := by
  have : ConnectedSpace S := hConn
  have hd_refl : ∀ x ∈ H.A, d x x = 0 := by
    obtain ⟨_, K, ins, _, _, hd_eq⟩ := hmetric
    intro x hx
    rw [hd_eq x hx x hx]
    simp [tangleMetric]
  -- Proceed by strong induction on `n = |V(G₀)| + |E(G₀)|` for `G₀ ≤ G` with `η₀(H) = η(H)`
  suffices hind : ∀ (n : ℕ) (G₀ : Graph α β) (η₀ : SpanEmbedding H G₀),
      V(G₀).ncard + E(G₀).ncard = n → G₀ ≤ G → η₀.imageGraph = η.imageGraph →
      (∀ v ∈ H.V, η₀.vMap v = η.vMap v) →
      (∀ e ∈ H.E, η₀.eMap e = η.eMap e) →
      ∃ (S_seg : Set (Society α β)) (α_disc : Society α β → Set S) (α_pt : α → S),
        IsThreeSegregation G₀ S_seg ∧ IsTangleLocal G₀ H η₀ T S_seg ∧
        IsSurfaceArrangement S_seg α_disc α_pt ∧ IsCompatibleWith G₀ H η₀ S_seg α_disc α_pt by
    exact hind (V(G).ncard + E(G).ncard) G η rfl (Preorder.le_refl G) rfl
      (fun _ _ => rfl) (fun _ _ => rfl)
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro G₀ η₀ hn hG₀_le hη₀_eq hη₀_v hη₀_e
    have hV₀_fin : V(G₀).Finite := hV_fin.subset hG₀_le.vertexSet_mono
    have hE₀_fin : E(G₀).Finite := hE_fin.subset hG₀_le.edgeSet_mono
    have h17_le_θ : 17 ≤ θ := by omega
    -- Base case: `G₀ = η₀(H)`
    by_cases hbase : G₀ = η₀.imageGraph
    · exact base_case_10_1 hS hConn hV₀_fin hE₀_fin hrigid hmetric h17_le_θ hbase
    · -- Inductive step: decompose `G₀` into a bridge `J` and the union `G'` of `H` and all other
      -- bridges of `H` in `G₀`
      obtain ⟨J, G', B_rem, η', hJ, hB_rem, hJ_not_rem, hJ_eq, hG'_eq, hG'_le, hG₀_eq,
          hDisj_E, hInter_V, hη'_eq, hη'_v, hη'_e, hcard_lt⟩ :=
        exists_bridge_decomposition_of_ne η₀ hV₀_fin hE₀_fin hbase
      rw [hn] at hcard_lt
      have hG'_le_G : G' ≤ G := hG'_le.trans hG₀_le
      have hη'_eq_G : η'.imageGraph = η.imageGraph := hη'_eq.trans hη₀_eq
      have hη'_v_G : ∀ v ∈ H.V, η'.vMap v = η.vMap v :=
        fun v hv => (hη'_v v hv).trans (hη₀_v v hv)
      have hη'_e_G : ∀ e ∈ H.E, η'.eMap e = η.eMap e :=
        fun e he => (hη'_e e he).trans (hη₀_e e he)
      -- Apply the induction hypothesis to `G'`
      obtain ⟨S_seg, α_disc, α_pt, h3seg, hlocal, harr, hcompat⟩ :=
        ih (V(G').ncard + E(G').ncard) hcard_lt G' η' rfl hG'_le_G hη'_eq_G hη'_v_G hη'_e_G
      -- Split on whether `V(H ∩ J)` is empty or contains some `u ∈ V(H)`
      by_cases hVJ : ∃ u ∈ H.V, η₀.vMap u ∈ V(J)
      · rcases hVJ with ⟨u, huV, huJ⟩
        have hJ_dist : ∀ v ∈ H.V, η₀.vMap v ∈ V(J) → d {u} {v} < beta := by
          intro v hvV hvJ
          by_cases huv : u = v
          · subst huv
            rw [hd_refl {u} (Or.inl (Or.inl ⟨u, huV, rfl⟩))]
            omega
          · have hvu_ne : η₀.vMap u ≠ η₀.vMap v :=
              fun hEq => huv (η₀.bijOn_v.injOn huV hvV hEq)
            obtain ⟨P, hP₀⟩ :=
              exists_isHPathWithEnds_of_isBridge hJ huJ hvJ
                (η₀.bijOn_v.mapsTo huV) (η₀.bijOn_v.mapsTo hvV) hvu_ne
            have hP_G : IsHPathWithEnds G η.imageGraph P (η.vMap u) (η.vMap v) := by
              rw [← hη₀_eq, ← hη₀_v u huV, ← hη₀_v v hvV]
              exact isHPathWithEnds_mono hG₀_le hP₀
            exact hi_path P u v huV hvV hP_G
        have hii_G₀ : ∀ (Λ : Set S)
            (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
            (d' : Set S → Set S → ℕ)
            (η_cl₀ : SpanEmbedding (clearedSubdrawing H Λ) G₀),
            IsLambdaZoneAround H d (3 * beta + 3) {u} Λ →
            IsClearedTangle H T d θ (3 * beta + 3) Λ T' d' →
            IsRigid (clearedSubdrawing H Λ) →
            (∀ v ∈ (clearedSubdrawing H Λ).V, η_cl₀.vMap v = η₀.vMap v) →
            (∀ e ∈ (clearedSubdrawing H Λ).E, η_cl₀.eMap e = η₀.eMap e) →
            ¬ IsDrawingEye G₀ (clearedSubdrawing H Λ) η_cl₀ (θ - 4 * (3 * beta + 3) - 2) T' Λ := by
          intro Λ T' d' η_cl₀ hzone hT' hrig hcl_v hcl_e heye₀
          have hSub_cl : (clearedSubdrawing H Λ).IsSubdrawing H :=
            clearedSubdrawing_isSubdrawing H Λ
          have hzone_lam : IsLambdaZone H d (3 * beta + 3) Λ :=
            ⟨{u}, Or.inl (Or.inl ⟨u, huV, rfl⟩), hzone⟩
          exact hii_no_eye Λ T' d' (spanEmbeddingMono hG₀_le η_cl₀) hzone_lam hrig hT'
            (fun v hv => (hcl_v v hv).trans (hη₀_v v (hSub_cl.1 hv)))
            (fun e he => (hcl_e e he).trans (hη₀_e e (hSub_cl.2 he)))
            (isDrawingEye_mono hG₀_le η_cl₀ heye₀)
        exact bridge_step_10_1
          hS hConn G₀ G' J B_rem H η₀ η' T d θ beta hV₀_fin hE₀_fin hrigid hmetric hbeta hθ
          hJ hB_rem hJ_not_rem hJ_eq hG'_eq hG'_le hG₀_eq hDisj_E hInter_V hη'_v hη'_e
          u huV hJ_dist hii_G₀ S_seg α_disc α_pt h3seg hlocal harr hcompat
      · have hVJ_empty : ∀ v ∈ H.V, η₀.vMap v ∉ V(J) := by
          intro v hv hvJ
          exact hVJ ⟨v, hv, hvJ⟩
        exact disjoint_bridge_step_10_1 hV₀_fin hE₀_fin hmetric h17_le_θ hJ hG'_le hG₀_eq
          hDisj_E hInter_V hVJ_empty hη'_v hη'_e h3seg hlocal harr hcompat

/-! ## Theorem (4.1) (page 30) -/

/-- **Graph Minors XIV, (4.1)** (page 30):
"Let $H$ be a 2-cell rigid drawing in a surface $\Sigma$, and let $\mathscr{T}$ be a
respectful tangle in $H$ of order $\theta \ge 209$ with metric $d$. Let $H$ be a subgraph of
$G$, and suppose that* (i) *$d(u, v) \le 3$ for every $H$-path in $G$ with ends $u, v$, and*
(ii) *if $\mathscr{T}'$ is the tangle of order $\theta - 158$ obtained by clearing some
39-zone $\Lambda$ such that $H \cap (\Sigma - \Lambda)$ is a rigid drawing in $\Sigma$, then
$\Lambda$ is not an eye of $H \cap (\Sigma - \Lambda)$ in $G$ with respect to
$\mathscr{T}'$.* *Then there is a $\mathscr{T}$-local 3-segregation of $G$ and an
arrangement of it in $\Sigma$ compatible with $H$."

Proved by setting `β = 12` in `(10.1)` (`theorem_10_1_proof`), since `16 * 12 + 17 = 209`,
`3 * 12 + 3 = 39`, `4 * 39 + 2 = 158`, and `3 < 12`. -/
theorem theorem_4_1_proof {α : Type v} {β : Type w}
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ) (θ : ℕ)
    (hV_fin : V(G).Finite) (hE_fin : E(G).Finite)
    (h2cell : H.IsTwoCell) (hrigid : IsRigid H)
    (hT : IsRespectfulDrawingTangle H θ T) (hmetric : HasTangleMetric H θ T d)
    (hθ : 209 ≤ θ)
    (hi_path : ∀ (P : Graph α β) (u v : S),
      u ∈ H.V → v ∈ H.V →
      IsHPathWithEnds G η.imageGraph P (η.vMap u) (η.vMap v) →
      d {u} {v} ≤ 3)
    (hii_no_eye : ∀ (Λ : Set S)
      (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d' : Set S → Set S → ℕ)
      (η_cl : SpanEmbedding (clearedSubdrawing H Λ) G),
      IsLambdaZone H d 39 Λ →
      IsRigid (clearedSubdrawing H Λ) →
      IsClearedTangle H T d θ 39 Λ T' d' →
      (∀ v ∈ (clearedSubdrawing H Λ).V, η_cl.vMap v = η.vMap v) →
      (∀ e ∈ (clearedSubdrawing H Λ).E, η_cl.eMap e = η.eMap e) →
      ¬ IsDrawingEye G (clearedSubdrawing H Λ) η_cl (θ - 158) T' Λ) :
    ∃ (S_seg : Set (Society α β)) (α_disc : Society α β → Set S) (α_pt : α → S),
      IsThreeSegregation G S_seg ∧ IsTangleLocal G H η T S_seg ∧
      IsSurfaceArrangement S_seg α_disc α_pt ∧ IsCompatibleWith G H η S_seg α_disc α_pt := by
  -- Set `beta = 12` in `theorem_10_1_proof`
  have hbeta12 : 12 ≤ 12 ∧ Even 12 := ⟨le_rfl, ⟨6, rfl⟩⟩
  have hθ12 : 16 * 12 + 17 ≤ θ := by omega
  have hi_12 : ∀ (P : Graph α β) (u v : S),
      u ∈ H.V → v ∈ H.V →
      IsHPathWithEnds G η.imageGraph P (η.vMap u) (η.vMap v) →
      d {u} {v} < 12 := by
    intro P u v hu hv hP
    have hle := hi_path P u v hu hv hP
    omega
  have hii_12 : ∀ (Λ : Set S)
      (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d' : Set S → Set S → ℕ)
      (η_cl : SpanEmbedding (clearedSubdrawing H Λ) G),
      IsLambdaZone H d (3 * 12 + 3) Λ →
      IsRigid (clearedSubdrawing H Λ) →
      IsClearedTangle H T d θ (3 * 12 + 3) Λ T' d' →
      (∀ v ∈ (clearedSubdrawing H Λ).V, η_cl.vMap v = η.vMap v) →
      (∀ e ∈ (clearedSubdrawing H Λ).E, η_cl.eMap e = η.eMap e) →
      ¬ IsDrawingEye G (clearedSubdrawing H Λ) η_cl (θ - 4 * (3 * 12 + 3) - 2) T' Λ := by
    intro Λ T' d' η_cl hzone hrig hT' hcl_v hcl_e
    have h39 : 3 * 12 + 3 = 39 := rfl
    have h158 : θ - 4 * (3 * 12 + 3) - 2 = θ - 158 := by omega
    rw [h39] at hzone hT'
    rw [h158]
    exact hii_no_eye Λ T' d' η_cl hzone hrig hT' hcl_v hcl_e
  exact theorem_10_1_proof
    hS hConn G H η T d θ 12 hV_fin hE_fin h2cell hrigid hT hmetric hbeta12 hθ12 hi_12 hii_12

/-! ## Theorem (1.1) (pages 24–25) -/

/-- **Graph Minors XIV, (1.1)** (pages 24–25):
"Let $G$ be a 4-connected graph, and let $H$ be a subgraph of $G$ which is a subdivision of a
simple 3-connected graph. Let $\Sigma$ be a connected surface without boundary, not a
sphere, and let $H$ be drawn in $\Sigma$. Suppose that every closed curve in $\Sigma$ that
meets $H$ at most 208 times is null-homotopic. For such a curve $\phi$, let
$\operatorname{ins}(\phi)$ denote the union of the points of $\Sigma$ appearing in $\phi$
together with all discs in $\Sigma$ with boundary in this set. Then either* (i) *the drawing
of $H$ can be extended to one of $G$, or* (ii) *there is a path of $G$ with distinct ends
$u, v \in V(H)$ and with no other vertex or edge in $H$, such that there is no closed curve
$\phi$ meeting $H$ at most 3 times with $u, v \in \operatorname{ins}(\phi)$, or* (iii)
*there is a circuit $C$ of $H$ bounding an open disc $\Lambda \subseteq \Sigma$, and a point
$x$ of $\Lambda$, and four vertices $a, b, c, d$ of $C$ in order, such that* ... (i) *$H \cap
(\Sigma - \Lambda)$ is a subdivision of a simple 3-connected graph* (ii) *for every $y \in
\Lambda$ there is a closed curve $\phi$ meeting $H$ at most 39 times, with $\{x, y\}
\subseteq \operatorname{ins}(\phi)$* (iii) *$\operatorname{bd}(\Delta) - \Lambda$ meets $H$
at least 4 times, for every closed disc $\Delta \subseteq \Sigma$ with $a, b, c, d \in
\Delta$, and* (iv) *there are two disjoint paths of $G$ with ends $a, c$ and $b, d$ each
meeting $H$ only within $\Lambda \cup \{a, b, c, d\}$." -/
theorem theorem_1_1_proof {α : Type v} {β : Type w}
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S) (hnot_sphere : ¬ IsSphere S)
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G)
    (hV_fin : V(G).Finite) (hE_fin : E(G).Finite)
    (hG_4conn : 5 ≤ V(G).ncard ∧
      ∀ G₁ G₂ : Graph α β, IsGraphSeparation G G₁ G₂ →
        (V(G₁) ∩ V(G₂)).ncard < 4 → V(G₁) = V(G) ∨ V(G₂) = V(G))
    (hH_subdiv : IsSubdivisionOfSimpleThreeConnected η.imageGraph)
    (hrep : H.IsRepresentative 209) :
    -- `(i)` The drawing of `H` can be extended to one of `G`, OR
    (∃ (Γ_G : GraphDrawing G S), H.IsSubdrawing Γ_G.drawing) ∨
    -- `(ii)` There is an `H`-path in `G` whose ends are not enclosed by any closed curve meeting
    -- `H` at most 3 times, OR
    (∃ (P_G : Graph α β) (u_H v_H : S),
      u_H ∈ H.V ∧ v_H ∈ H.V ∧
      IsHPathWithEnds G η.imageGraph P_G (η.vMap u_H) (η.vMap v_H) ∧
      ¬ ∃ φ : C(Circle, S),
        (range φ ∩ H.U).encard ≤ 3 ∧ u_H ∈ curveIns φ ∧ v_H ∈ curveIns φ) ∨
    -- `(iii)` There is an eye configuration `(C, Λ₀, x, a, b, c, d)` satisfying `(iii)(i)–(iv)`:
    (∃ (C : Drawing S) (Λ₀ : Set S) (x : S) (a b c d_v : S) (P₁ P₂ : Graph α β),
      C.IsCircuit ∧ C.IsSubdrawing H ∧ IsOpenDisc Λ₀ ∧ subBd Λ₀ = C.U ∧ x ∈ Λ₀ ∧
      a ∈ C.V ∧ b ∈ C.V ∧ c ∈ C.V ∧ d_v ∈ C.V ∧
      OccurInCircuitOrder C a b c d_v ∧
      IsSubdivisionOfSimpleThreeConnected (clearedSubdrawing H Λ₀).toGraph ∧
      (∀ y ∈ Λ₀, ∃ φ : C(Circle, S),
        (range φ ∩ H.U).encard ≤ 39 ∧ x ∈ curveIns φ ∧ y ∈ curveIns φ) ∧
      (∀ Δ : Set S, IsClosedDisc Δ → ({a, b, c, d_v} : Set S) ⊆ Δ →
        4 ≤ ((subBd Δ \ Λ₀) ∩ H.U).encard) ∧
      Disjoint V(P₁) V(P₂) ∧
      IsGraphPathWithEnds G P₁ (η.vMap a) (η.vMap c) ∧
      IsGraphPathWithEnds G P₂ (η.vMap b) (η.vMap d_v)) := by
  obtain ⟨T, d, h2cell, hrigid, hT, hmetric, h_ii_from_dist, h_iii_from_eye, h_i_from_3seg⟩ :=
    theorem11TranslationStatement_proved hS hConn hnot_sphere G H η hV_fin hE_fin hG_4conn
      hH_subdiv hrep
  -- Check whether `(10.1)(i)` with `β = 12` holds for all `H`-paths in `G`
  by_cases hi : ∀ (P : Graph α β) (u v : S),
      u ∈ H.V → v ∈ H.V →
      IsHPathWithEnds G η.imageGraph P (η.vMap u) (η.vMap v) →
      d {u} {v} < 12
  · -- Check whether `(10.1)(ii)` with `β = 12` holds for all 39-zones `Λ`
    by_cases hii : ∀ (Λ : Set S)
        (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (d' : Set S → Set S → ℕ)
        (η_cl : SpanEmbedding (clearedSubdrawing H Λ) G),
        IsLambdaZone H d 39 Λ →
        IsRigid (clearedSubdrawing H Λ) →
        IsClearedTangle H T d 209 39 Λ T' d' →
        (∀ v ∈ (clearedSubdrawing H Λ).V, η_cl.vMap v = η.vMap v) →
        (∀ e ∈ (clearedSubdrawing H Λ).E, η_cl.eMap e = η.eMap e) →
        ¬ IsDrawingEye G (clearedSubdrawing H Λ) η_cl (209 - 158) T' Λ
    · -- Both `(10.1)(i)` and `(10.1)(ii)` hold (`β = 12`): apply `theorem_10_1_proof` to get
      -- `(1.1)(i)`
      left
      have hbeta12 : 12 ≤ 12 ∧ Even 12 := ⟨le_rfl, ⟨6, rfl⟩⟩
      exact h_i_from_3seg (theorem_10_1_proof
        hS hConn G H η T d 209 12 hV_fin hE_fin h2cell hrigid hT hmetric hbeta12 le_rfl hi hii)
    · -- `(10.1)(ii)` fails: some 39-zone `Λ` is an eye, giving `(1.1)(iii)`
      right; right
      by_contra hnot_iii
      apply hii
      intro Λ T' d' η_cl hzone hrig hT' hv_cl _ heye
      exact hnot_iii (h_iii_from_eye Λ T' d' η_cl hzone hrig hT' hv_cl heye)
  · -- `(10.1)(i)` fails: some `H`-path has `¬ d({u}, {v}) < 12`, giving `(1.1)(ii)`
    right; left
    by_contra hnot_ii
    apply hi
    intro P u v hu hv hP
    by_contra hgt
    exact hnot_ii (h_ii_from_dist P u v hu hv hP hgt)

end GraphMinor.GM14
