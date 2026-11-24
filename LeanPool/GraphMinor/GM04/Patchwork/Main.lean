/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Minor.Model
public import LeanPool.GraphMinor.GM04.Patchwork.VerifyAxioms
import LeanPool.GraphMinor.GM04.Patchwork.Menger
import LeanPool.GraphMinor.GM04.Patchwork.Expansion

/-!
# Deduction of Graph Minors IV, (1.5) from (9.1)

This file formalizes the deduction of (1.5) ("(1.5) *For any integer $k$ the class of all graphs
with tree-width $\le k$ is well-quasi-ordered by minors.*") from (9.1) in Graph Minors IV, Section 9
(pages
252–253):

* `graphPatch`: for a vertex set `U`, the patch `{N_U, K_U}` consisting of the empty and complete
  subgraphs on `U`.
* `graphPatch_isRobust`: when `U` has at most two elements (as is the case for the ends of an edge
  in a graph), `graphPatch U` is a robust patch.
* `graphPatchwork`: the `Unit`-patchwork `P(G) = ((G, 0), μ, Δ, φ)` associated with a finite graph
  `G`, where `dom(μ) = E(G)`, `μ(e)` is a march with `μBar(e) = V(e)`, `Δ(e) = {N_{V(e)},
  K_{V(e)}}`,
  and `φ(e) = ()`.
* `graphPatchwork_isRobust`: `graphPatchwork G hV hE` is a robust patchwork.
* `isMinorModel_of_simulated`: if `graphPatchwork H hVH hEH` is simulated in
  `graphPatchwork G hVG hEG`, then there is a minor model (`IsMinorModel H G ηv ηe`) of `H` in `G`.
* `theorem_1_5`: Graph Minors IV, (1.5).
-/

@[expose] public section

namespace GraphMinor.GM04

open SimpleGraph Graph _root_.GraphMinor.Hypergraph

universe u v u₁ u₂

variable {α : Type u} {β : Type v}

open Classical in
/-- The trivial one-element preorder `Unit` is well-quasi-ordered (`E(Ω) = {1}` on page 252). -/
theorem wellQuasiOrderedLE_unit : WellQuasiOrderedLE Unit :=
  ⟨fun _ ↦ ⟨0, 1, Nat.zero_lt_one, le_rfl⟩⟩

open Classical in
/-- For a set `U : Set α`, the patch `{N_U, K_U}` consisting of the edgeless subgraph `N_U` and the
complete subgraph `K_U` on `U` (Graph Minors IV, Section 9, page 253, condition (iii)). -/
def graphPatch (U : Set α) : Patch α where
  verts := U
  groupings := {emptySubgraph U, completeSubgraph U}
  isGrouping := by
    rintro K (rfl | rfl)
    · exact emptySubgraph_isGrouping U
    · exact completeSubgraph_isGrouping U
  verts_eq := by
    rintro K (rfl | rfl) <;> rfl

open Classical in
@[simp]
theorem graphPatch_verts (U : Set α) : (graphPatch U).verts = U := rfl

open Classical in
@[simp]
theorem mem_graphPatch_iff {U : Set α} {K : (⊤ : SimpleGraph α).Subgraph} :
    K ∈ graphPatch U ↔ K = emptySubgraph U ∨ K = completeSubgraph U := Iff.rfl

open Classical in
/-- When any three elements of `U` have at least two equal (so `|U| ≤ 2`), the patch
`graphPatch U = {N_U, K_U}` is robust. -/
theorem graphPatch_isRobust {U : Set α} (hfin : U.Finite)
    (hU : ∀ a ∈ U, ∀ b ∈ U, ∀ c ∈ U, a = b ∨ a = c ∨ b = c) :
    (graphPatch U).IsRobust := by
  intro X hXU Y hYU hcard hdisj
  have hXfin : X.Finite := hfin.subset hXU
  have hYfin : Y.Finite := hfin.subset hYU
  rcases X.eq_empty_or_nonempty with rfl | ⟨x, hxX⟩
  · have hY0 : Y.ncard = 0 := by simpa using hcard.symm
    obtain rfl : Y = ∅ := (Set.ncard_eq_zero (hs := hYfin)).mp hY0
    exact ⟨emptySubgraph U, Or.inl rfl, emptySubgraph_isPairing U, emptySubgraph_pairs_empty U⟩
  · have hYpos : 0 < Y.ncard := by
      rw [← hcard]
      exact (Set.ncard_pos hXfin).mpr ⟨x, hxX⟩
    obtain ⟨y, hyY⟩ := (Set.ncard_pos hYfin).mp hYpos
    have hxU : x ∈ U := hXU hxX
    have hyU : y ∈ U := hYU hyY
    have hxy : x ≠ y := fun h ↦ Set.disjoint_left.mp hdisj hxX (h ▸ hyY)
    have hU_eq : ∀ z ∈ U, z = x ∨ z = y := by
      intro z hz
      rcases hU z hz x hxU y hyU with rfl | rfl | hEq
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd hEq hxy
    have hX_eq : ∀ z ∈ X, z = x := by
      intro z hz
      rcases hU_eq z (hXU hz) with rfl | rfl
      · rfl
      · exact absurd hyY (Set.disjoint_left.mp hdisj hz)
    have hY_eq : ∀ z ∈ Y, z = y := by
      intro z hz
      rcases hU_eq z (hYU hz) with rfl | rfl
      · exact absurd hz (Set.disjoint_left.mp hdisj hxX)
      · rfl
    have hK_pair : IsPairing U (completeSubgraph U) := by
      rw [isPairing_iff hfin]
      refine ⟨subset_rfl, fun a b c hab hac ↦ ?_⟩
      simp only [completeSubgraph_adj] at hab hac
      rcases hU_eq a hab.1 with rfl | rfl <;>
        rcases hU_eq b hab.2.1 with rfl | rfl <;>
        rcases hU_eq c hac.2.1 with rfl | rfl
      all_goals first | rfl | exact absurd rfl hab.2.2 | exact absurd rfl hac.2.2
    refine ⟨completeSubgraph U, Or.inr rfl, hK_pair, ?_⟩
    rw [graphPatch_verts, pairs_iff_of_isPairing hfin hK_pair]
    refine ⟨hXU, hYU, hdisj, fun u v huv ↦ ?_, fun v hv ↦ ?_⟩
    · simp only [completeSubgraph_adj] at huv
      rcases hU_eq u huv.1 with rfl | rfl <;>
        rcases hU_eq v huv.2.1 with rfl | rfl
      · exact absurd rfl huv.2.2
      · exact Or.inl ⟨hxX, hyY⟩
      · exact Or.inr ⟨hyY, hxX⟩
      · exact absurd rfl huv.2.2
    · rcases hv with hvX | hvY
      · obtain rfl : v = x := hX_eq v hvX
        exact ⟨y, hxU, hyU, hxy⟩
      · obtain rfl : v = y := hY_eq v hvY
        exact ⟨x, hyU, hxU, hxy.symm⟩

open Classical in
theorem ofGraph_ends_finite (G : Graph α β) (hV : V(G).Finite) (hE : E(G).Finite) (e : β) :
    ((Hypergraph.ofGraph G hV hE).ends e).Finite :=
  hV.subset fun _ hv ↦ hv.vertex_mem

open Classical in
/-- The `Unit`-patchwork `P(G) = ((G, 0), μ, Δ, φ)` associated with a finite graph `G`
(Graph Minors IV, Section 9, pages 252–253). -/
noncomputable def graphPatchwork (G : Graph α β) (hV : V(G).Finite) (hE : E(G).Finite) :
    Patchwork Unit α β where
  G := (Hypergraph.ofGraph G hV hE).toRooted
  dom := E(G)
  μ e := (ofGraph_ends_finite G hV hE e).toFinset.toList
  Δ e := graphPatch ((Hypergraph.ofGraph G hV hE).ends e)
  φ _ := ()
  dom_subset := le_rfl
  μ_nodup _ _ := Finset.nodup_toList _
  μ_set e _ := by
    ext v
    simp [Hypergraph.ends, Hypergraph.toRooted]
  Δ_verts _ _ := rfl
  Δ_free _ he hne := absurd he hne

open Classical in
@[simp]
theorem graphPatchwork_G (G : Graph α β) (hV : V(G).Finite) (hE : E(G).Finite) :
    (graphPatchwork G hV hE).G = (Hypergraph.ofGraph G hV hE).toRooted := rfl

open Classical in
theorem graphPatchwork_vertexSet (G : Graph α β) (hV : V(G).Finite) (hE : E(G).Finite) :
    (graphPatchwork G hV hE).G.vertexSet = V(G) := rfl

open Classical in
theorem graphPatchwork_edgeSet (G : Graph α β) (hV : V(G).Finite) (hE : E(G).Finite) :
    (graphPatchwork G hV hE).G.edgeSet = E(G) := rfl

open Classical in
theorem graphPatchwork_ends (G : Graph α β) (hV : V(G).Finite) (hE : E(G).Finite) (e : β) :
    (graphPatchwork G hV hE).G.ends e = {v | G.Inc e v} := rfl

open Classical in
@[simp]
theorem graphPatchwork_dom (G : Graph α β) (hV : V(G).Finite) (hE : E(G).Finite) :
    (graphPatchwork G hV hE).dom = E(G) := rfl

open Classical in
@[simp]
theorem graphPatchwork_Δ (G : Graph α β) (hV : V(G).Finite) (hE : E(G).Finite) (e : β) :
    (graphPatchwork G hV hE).Δ e = graphPatch {v | G.Inc e v} := rfl

open Classical in
/-- For any finite graph `G`, `graphPatchwork G hV hE` is a robust `Unit`-patchwork. -/
theorem graphPatchwork_isRobust (G : Graph α β) (hV : V(G).Finite) (hE : E(G).Finite) :
    (graphPatchwork G hV hE).IsRobust := by
  intro e _
  refine graphPatch_isRobust (ofGraph_ends_finite G hV hE e) ?_
  intro a ha b hb c hc
  exact Inc.eq_or_eq_or_eq ha hb hc

open Classical in
/-- If `graphPatchwork H hVH hEH` is simulated in `graphPatchwork G hVG hEG`, then there is a
minor model (`IsMinorModel H G ηv ηe`) of `H` in `G`. -/
theorem isMinorModel_of_simulated {H G : Graph α β}
    {hVH : V(H).Finite} {hEH : E(H).Finite} {hVG : V(G).Finite} {hEG : E(G).Finite}
    (hsim : Simulated (graphPatchwork H hVH hEH) (graphPatchwork G hVG hEG)) :
    ∃ (ηv : α → Set α) (ηe : β → β), IsMinorModel H G ηv ηe := by
  let PH := graphPatchwork H hVH hEH
  let PG := graphPatchwork G hVG hEG
  obtain ⟨ηv, ηe, hexp, R, hreal⟩ := hsim
  have hVP : ∀ v, v ∈ PH.G.vertexSet ↔ v ∈ V(H) := fun _ ↦ Iff.rfl
  have hEP : ∀ e, e ∈ PH.G.edgeSet ↔ e ∈ E(H) := fun _ ↦ Iff.rfl
  have hdomH : ∀ e, e ∈ PH.dom ↔ e ∈ E(H) := fun _ ↦ Iff.rfl
  have hdomG : ∀ e, e ∈ PG.dom ↔ e ∈ E(G) := fun _ ↦ Iff.rfl
  have hinc_iff : ∀ v ∈ V(H), ∀ e ∈ E(H), H.Inc e v ↔ ∃ x ∈ ηv v, G.Inc (ηe e) x := by
    intro v hv e he
    have he' : ηe e ∈ E(G) := hexp.edge_mem e ((hEP e).mpr he)
    have hμH := PH.μ_set e ((hdomH e).mpr he)
    have hμG := PG.μ_set (ηe e) ((hdomG (ηe e)).mpr he')
    rw [graphPatchwork_ends] at hμH hμG
    constructor
    · intro hinc
      have hv_mem : v ∈ PH.μ e := by
        have hv_ends : v ∈ {u | H.Inc e u} := hinc
        rw [← hμH] at hv_ends
        exact hv_ends
      obtain ⟨r, hr, rfl⟩ := List.mem_iff_getElem.mp hv_mem
      have hr' : r < (PG.μ (ηe e)).length := hexp.μ_length e ((hdomH e).mpr he) ▸ hr
      refine ⟨(PG.μ (ηe e))[r], hexp.μ_mem e ((hdomH e).mpr he) r hr hr', ?_⟩
      have hx_mem : (PG.μ (ηe e))[r] ∈ {x | x ∈ PG.μ (ηe e)} := List.getElem_mem hr'
      rw [hμG] at hx_mem
      exact hx_mem
    · rintro ⟨x, hxv, hinc'⟩
      have hx_mem : x ∈ PG.μ (ηe e) := by
        have hx_ends : x ∈ {u | G.Inc (ηe e) u} := hinc'
        rw [← hμG] at hx_ends
        exact hx_ends
      obtain ⟨r, hr', rfl⟩ := List.mem_iff_getElem.mp hx_mem
      have hr : r < (PH.μ e).length := (hexp.μ_length e ((hdomH e).mpr he)).symm ▸ hr'
      let w := (PH.μ e)[r]
      have hw_inc : H.Inc e w := by
        have hw_mem : w ∈ {u | u ∈ PH.μ e} := List.getElem_mem hr
        rw [hμH] at hw_mem
        exact hw_mem
      have hw_v : w ∈ V(H) := hw_inc.vertex_mem
      have hxw : (PG.μ (ηe e))[r] ∈ ηv w := hexp.μ_mem e ((hdomH e).mpr he) r hr hr'
      have hvw : v = w := by
        by_contra hne
        exact Set.disjoint_left.mp
          (hexp.vertex_disjoint v ((hVP v).mpr hv) w ((hVP w).mpr hw_v) hne) hxv hxw
      exact hvw ▸ hw_inc
  have hisLoopAt_iff : ∀ v ∈ V(H), ∀ e ∈ E(H),
      H.IsLoopAt e v ↔ ∀ x, G.Inc (ηe e) x → x ∈ ηv v := by
    intro v hv e he
    have he' : ηe e ∈ E(G) := hexp.edge_mem e ((hEP e).mpr he)
    have hμH := PH.μ_set e ((hdomH e).mpr he)
    have hμG := PG.μ_set (ηe e) ((hdomG (ηe e)).mpr he')
    rw [graphPatchwork_ends] at hμH hμG
    constructor
    · intro hloop x hinc'
      have hx_mem : x ∈ PG.μ (ηe e) := by
        have hx_ends : x ∈ {u | G.Inc (ηe e) u} := hinc'
        rw [← hμG] at hx_ends
        exact hx_ends
      obtain ⟨r, hr', rfl⟩ := List.mem_iff_getElem.mp hx_mem
      have hr : r < (PH.μ e).length := (hexp.μ_length e ((hdomH e).mpr he)).symm ▸ hr'
      let w := (PH.μ e)[r]
      have hw_inc : H.Inc e w := by
        have hw_mem : w ∈ {u | u ∈ PH.μ e} := List.getElem_mem hr
        rw [hμH] at hw_mem
        exact hw_mem
      have hvw : v = w := hloop.eq_of_inc hw_inc
      exact hvw ▸ hexp.μ_mem e ((hdomH e).mpr he) r hr hr'
    · intro hall
      obtain ⟨a, b, hab⟩ := H.exists_isLink_of_mem_edgeSet he
      have ha_eq : a = v := by
        obtain ⟨x, hxa, hinc_x⟩ := (hinc_iff a hab.left_mem e he).mp hab.inc_left
        have hxv := hall x hinc_x
        by_contra hne
        exact Set.disjoint_left.mp
          (hexp.vertex_disjoint a ((hVP a).mpr hab.left_mem) v ((hVP v).mpr hv) hne) hxa hxv
      have hb_eq : b = v := by
        obtain ⟨x, hxb, hinc_x⟩ := (hinc_iff b hab.right_mem e he).mp hab.inc_right
        have hxv := hall x hinc_x
        by_contra hne
        exact Set.disjoint_left.mp
          (hexp.vertex_disjoint b ((hVP b).mpr hab.right_mem) v ((hVP v).mpr hv) hne) hxb hxv
      rw [← isLink_self_iff]
      rw [ha_eq, hb_eq] at hab
      exact hab
  refine ⟨ηv, ηe,
    fun v hv ↦ hexp.vertex_nonempty v ((hVP v).mpr hv),
    fun v hv ↦ hexp.vertex_subset v ((hVP v).mpr hv),
    fun e he ↦ hexp.edge_mem e ((hEP e).mpr he),
    fun v₁ hv₁ v₂ hv₂ ↦ hexp.vertex_disjoint v₁ ((hVP v₁).mpr hv₁) v₂ ((hVP v₂).mpr hv₂),
    hexp.edge_injOn, hinc_iff, hisLoopAt_iff, ?_⟩
  intro v hv
  let K : Graph α β := (G.deleteEdges (ηe '' E(H))).induce (ηv v)
  have hK_le : K ≤ G.deleteEdges (ηe '' E(H)) :=
    Graph.induce_le (hexp.vertex_subset v ((hVP v).mpr hv))
  refine ⟨K, hK_le, rfl, hexp.vertex_nonempty v ((hVP v).mpr hv), ?_⟩
  intro x hx y hy
  obtain ⟨D, ⟨z, rfl⟩, hD_verts⟩ := hreal.2 v ((hVP v).mpr hv)
  obtain ⟨δ, hδ, hR_eq⟩ := hreal.1
  have hR_adj_to_K : ∀ a b : R.verts,
      a.1 ∈ ηv v → b.1 ∈ ηv v → R.coe.Adj a b → K.Adj a.1 b.1 := by
    intro a b ha hb hab
    have hR_adj : (realizationOf (PG.deleteEdges (ηe '' PH.G.edgeSet)).G.toHypergraph δ).Adj
        a.1 b.1 := by
      rw [← hR_eq]
      exact hab
    rw [realizationOf_adj] at hR_adj
    obtain ⟨e', he', hδ_adj⟩ := hR_adj
    have hδ_mem := hδ e' he'
    have he'_sdiff : e' ∈ PG.G.edgeSet ∧ e' ∉ ηe '' PH.G.edgeSet := he'
    have hδ_cases : δ e' = emptySubgraph {w | G.Inc e' w} ∨
        δ e' = completeSubgraph {w | G.Inc e' w} := by
      change δ e' ∈ PG.Δ e' at hδ_mem
      rw [graphPatchwork_Δ, mem_graphPatch_iff] at hδ_mem
      exact hδ_mem
    rcases hδ_cases with hEq | hEq
    · rw [hEq] at hδ_adj
      exact (not_emptySubgraph_adj hδ_adj).elim
    · rw [hEq, completeSubgraph_adj] at hδ_adj
      obtain ⟨ha_inc, hb_inc, hne⟩ := hδ_adj
      change G.Inc e' a.1 at ha_inc
      change G.Inc e' b.1 at hb_inc
      have hlink : G.IsLink e' a.1 b.1 := by
        rw [isLink_iff_inc]
        refine ⟨ha_inc, hb_inc, fun w hw ↦ ?_⟩
        rcases Inc.eq_or_eq_or_eq hw ha_inc hb_inc with rfl | rfl | hEq'
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact absurd hEq' hne
      refine ⟨e', ?_⟩
      simp only [K, Graph.induce_isLink, Graph.deleteEdges_isLink]
      exact ⟨⟨hlink, he'_sdiff.2⟩, ha, hb⟩
  have hreach_K : ∀ u : R.verts, R.coe.Reachable z u → Relation.ReflTransGen K.Adj z.1 u.1 := by
    intro u hr
    rw [SimpleGraph.reachable_iff_reflTransGen] at hr
    induction hr with
    | refl => exact Relation.ReflTransGen.refl
    | @tail a b ha_rel hab ih =>
      have ha_reach : R.coe.Reachable z a := by
        rw [SimpleGraph.reachable_iff_reflTransGen]
        exact ha_rel
      have hb_reach : R.coe.Reachable z b := ha_reach.trans (SimpleGraph.Adj.reachable hab)
      have ha_v : a.1 ∈ ηv v := hD_verts ▸ ⟨a.2, ha_reach⟩
      have hb_v : b.1 ∈ ηv v := hD_verts ▸ ⟨b.2, hb_reach⟩
      exact ih.tail (hR_adj_to_K a b ha_v hb_v hab)
  have hxD : x ∈ (component R z).verts := hD_verts.symm ▸ hx
  have hyD : y ∈ (component R z).verts := hD_verts.symm ▸ hy
  obtain ⟨hxR, hx_reach⟩ := hxD
  obtain ⟨hyR, hy_reach⟩ := hyD
  have hzx : Relation.ReflTransGen K.Adj z.1 x := hreach_K ⟨x, hxR⟩ hx_reach
  have hzy : Relation.ReflTransGen K.Adj z.1 y := hreach_K ⟨y, hyR⟩ hy_reach
  have hxz : Relation.ReflTransGen K.Adj x z.1 := by
    clear *- hzx
    induction hzx with
    | refl => exact Relation.ReflTransGen.refl
    | @tail a b _ hab ih => exact (Relation.ReflTransGen.single hab.symm).trans ih
  exact hxz.trans hzy

open Classical in
/-- Graph Minors IV, (1.5): for every `k`, the class of graphs of tree-width at most `k` is
well-quasi-ordered by minors. -/
theorem theorem_1_5_of_cited (h53 : Theorem53Statement.{u, v}) (hM : MengerStatement.{u, v})
    (hH : Higman83Statement.{u₁, u₂}) (hModel : MinorModelStatement.{u, v, u, v})
    {α : Type u} {β : Type v} (k : ℕ) (G : ℕ → Graph α β) (hV : ∀ n, V(G n).Finite)
    (hE : ∀ n, E(G n).Finite)
    (htw : ∀ n, TreeWidthLE (Hypergraph.ofGraph (G n) (hV n) (hE n)).toRooted k) :
    ∃ i j, i < j ∧ IsIsoMinor (G i) (G j) := by
  obtain ⟨i, j, hij, hsim⟩ := theorem_9_1_proof h53 hM hH wellQuasiOrderedLE_unit k
    (fun n ↦ graphPatchwork (G n) (hV n) (hE n))
    (fun n ↦ graphPatchwork_isRobust (G n) (hV n) (hE n))
    (fun n ↦ by rw [graphPatchwork_G]; exact htw n)
  obtain ⟨ηv, ηe, hmod⟩ := isMinorModel_of_simulated hsim
  exact ⟨i, j, hij, hModel (G i) (G j) (hV i) (hE i) (hV j) (hE j) ηv ηe hmod⟩

end GraphMinor.GM04
