/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section6
public import LeanPool.GraphMinor.GM10.Section8
import LeanPool.GraphMinor.GM10.TangleLemmas

/-!
# Graph Minors XVI, Section 7: The Giant Steps Application

This file formalizes Section 7 ("The Giant Steps application", pages 62–63) of
N. Robertson and P. D. Seymour, *Graph Minors. XVI. Excluding a non-planar graph*, J. Combin.
Theory Ser. B 89 (2003) 43–76:

- Identification of `Hypergraph.ofGraph (GM09.deleteVertices G Z)` with
  `(Hypergraph.ofGraph G _ _).deleteVertices Z` (`ofGraph_deleteVertices_eq`) and proof that
  `deleteGraphVerticesTangle` is a graph tangle of order `θ_star - Z.ncard` in `GM09.deleteVertices
  G Z`
  (`isGraphTangle_deleteGraphVerticesTangle`).
- Statement and unconditional proof of **Graph Minors XVI, (7.3)** (`GM16Theorem73Statement`,
  `theorem_7_3`, page 63), using **Graph Minors X, (2.9)** (`GM10.theorem_2_9`) and **(8.5)**
  (`GM10.theorem_8_5`).
- Statement and unconditional proof of **Graph Minors XVI, (7.4)** (`GM16Theorem74Statement`,
  `theorem_7_4`, page 63), lifting a `Σ`-span in `G \ Z` with respect to `T* \ Z` to a `Σ`-span in
  `G` with respect to `T*`.
- Proof that `T*` controls every minor controlled by `T* \ Z`
  (`controlsMinor_of_deleteGraphVerticesTangle`, page 63).
- Statements of **Graph Minors XVI, (7.1)** (`GM16Theorem71Statement`, page 62) and **(7.2)**
  (`GM16Theorem72Statement`, page 62), and complete proof of **Graph Minors XVI, (6.1)**
  (`theorem_6_1`, page 63) from `(7.1)` and `(7.2)`.
The backward and tower inductions are proved in `InductionsProved.lean`.
-/

@[expose] public section

namespace GraphMinor.GM16

open Set Function Topology
open Graph SimpleGraph Hypergraph
open GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11
  GraphMinor.GM14 GraphMinor.GM15

universe u v w

variable {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}

/-! ## Vertex Deletion on Graphs, Hypergraphs, and Tangles -/

/-- `Hypergraph.ofGraph G hV hE` is a graph hypergraph (`Hypergraph.IsGraph`). -/
theorem isGraph_ofGraph (G : Graph α β) (hV : V(G).Finite) (hE : E(G).Finite) :
    (Hypergraph.ofGraph G hV hE).IsGraph := by
  intro e he
  change e ∈ E(G) at he
  rw [G.edge_mem_iff_exists_isLink] at he
  obtain ⟨x, y, hlink⟩ := he
  have hne : ((Hypergraph.ofGraph G hV hE).ends e).Nonempty := ⟨x, ⟨y, hlink⟩⟩
  refine ⟨hne, ?_⟩
  have hsub : (Hypergraph.ofGraph G hV hE).ends e ⊆ {x, y} := by
    intro a ⟨z, haz⟩
    rcases G.eq_or_eq_of_isLink_of_isLink haz hlink with rfl | rfl
    · exact mem_insert a {y}
    · exact mem_insert_of_mem x (mem_singleton a)
  have hle1 : ((Hypergraph.ofGraph G hV hE).ends e).ncard ≤ ({x, y} : Set α).ncard :=
    ncard_le_ncard hsub ((finite_singleton y).insert x)
  have hle2 : ({x, y} : Set α).ncard ≤ 2 := by
    have := ncard_insert_le x {y}
    rw [ncard_singleton] at this
    exact this
  exact hle1.trans hle2

/-- Deleting `Z ∩ H.vertexSet` from a hypergraph `H` is the same as deleting `Z`. -/
theorem deleteVertices_inter_vertexSet (H : Hypergraph α β) (Z : Set α) :
    H.deleteVertices (Z ∩ H.vertexSet) = H.deleteVertices Z := by
  have h1 : H.deleteVertices (Z ∩ H.vertexSet) ≤ H := deleteVertices_le H _
  have h2 : H.deleteVertices Z ≤ H := deleteVertices_le H _
  refine eq_of_le_of_vertexSet_eq_of_edgeSet_eq h1 h2 ?_ ?_
  · ext v
    simp only [Hypergraph.deleteVertices, mem_sdiff, mem_inter_iff]
    tauto
  · ext e
    simp only [Hypergraph.deleteVertices, mem_ofPred_eq, mem_inter_iff]
    refine ⟨fun ⟨he, hno⟩ => ⟨he, fun v hvZ hinc => hno v ⟨hvZ, H.vertex_mem_of_inc hinc⟩ hinc⟩,
      fun ⟨he, hno⟩ => ⟨he, fun v ⟨hvZ, _⟩ hinc => hno v hvZ hinc⟩⟩

/-- If `(A, B)` is a separation of `G_H`, then `(A.deleteVertices Z, B.deleteVertices Z)` is a
separation of `G_H.deleteVertices Z` with order `≤ separationOrder A B`. -/
theorem isSeparation_deleteVertices {G_H A B : Hypergraph α β}
    (hsep : G_H.IsSeparation A B) (Z : Set α) :
    (G_H.deleteVertices Z).IsSeparation (A.deleteVertices Z) (B.deleteVertices Z) ∧
      separationOrder (A.deleteVertices Z) (B.deleteVertices Z) ≤ separationOrder A B := by
  have hA_le : A.deleteVertices Z ≤ G_H.deleteVertices Z := by
    refine ⟨sdiff_subset_sdiff hsep.left_le.vertexSet_subset Subset.rfl, ?_, ?_⟩
    · intro e ⟨heA, hno⟩
      exact ⟨hsep.left_le.edgeSet_subset heA, fun v hvZ hincG =>
        hno v hvZ ((inc_iff_of_le hsep.left_le heA).mpr hincG)⟩
    · intro e ⟨heA, _⟩
      ext v
      simp only [Hypergraph.ends, mem_ofPred_eq, Hypergraph.deleteVertices]
      simp_rw [inc_iff_of_le hsep.left_le heA]
  have hB_le : B.deleteVertices Z ≤ G_H.deleteVertices Z := by
    refine ⟨sdiff_subset_sdiff hsep.right_le.vertexSet_subset Subset.rfl, ?_, ?_⟩
    · intro e ⟨heB, hno⟩
      exact ⟨hsep.right_le.edgeSet_subset heB, fun v hvZ hincG =>
        hno v hvZ ((inc_iff_of_le hsep.right_le heB).mpr hincG)⟩
    · intro e ⟨heB, _⟩
      ext v
      simp only [Hypergraph.ends, mem_ofPred_eq, Hypergraph.deleteVertices]
      simp_rw [inc_iff_of_le hsep.right_le heB]
  constructor
  · rw [isSeparation_iff_of_le hA_le hB_le]
    refine ⟨?_, ?_, ?_⟩
    · change (A.vertexSet \ Z) ∪ (B.vertexSet \ Z) = G_H.vertexSet \ Z
      rw [← union_sdiff_distrib, hsep.vertexSet_union]
    · ext e
      simp only [Hypergraph.deleteVertices, mem_union, mem_ofPred_eq]
      constructor
      · rintro (⟨heA, hno⟩ | ⟨heB, hno⟩)
        · exact ⟨hsep.left_le.edgeSet_subset heA, fun v hvZ hincG =>
            hno v hvZ ((inc_iff_of_le hsep.left_le heA).mpr hincG)⟩
        · exact ⟨hsep.right_le.edgeSet_subset heB, fun v hvZ hincG =>
            hno v hvZ ((inc_iff_of_le hsep.right_le heB).mpr hincG)⟩
      · rintro ⟨heG, hno⟩
        rcases hsep.edgeSet_union.symm ▸ heG with heA | heB
        · exact Or.inl ⟨heA, fun v hvZ hincA =>
            hno v hvZ ((inc_iff_of_le hsep.left_le heA).mp hincA)⟩
        · exact Or.inr ⟨heB, fun v hvZ hincB =>
            hno v hvZ ((inc_iff_of_le hsep.right_le heB).mp hincB)⟩
    · ext e
      simp only [Hypergraph.deleteVertices, mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false,
        iff_false]
      rintro ⟨⟨heA, _⟩, ⟨heB, _⟩⟩
      exact hsep.notMem_edgeSet_right heA heB
  · have hsub : (A.deleteVertices Z ∩ B.deleteVertices Z).vertexSet ⊆ (A ∩ B).vertexSet := by
      intro v ⟨⟨hvA, _⟩, ⟨hvB, _⟩⟩
      exact ⟨hvA, hvB⟩
    exact ncard_le_ncard hsub (A ∩ B).vertexSet_finite

/-- `Hypergraph.ofGraph (GM09.deleteVertices G Z)` coincides with
`(Hypergraph.ofGraph G hV hE).deleteVertices Z`. -/
theorem ofGraph_deleteVertices_eq (G : Graph α β) (hV : V(G).Finite) (hE : E(G).Finite)
    (Z : Set α)
    (hV' : V(GM09.deleteVertices G Z).Finite := hV.subset (by simp [GM09.deleteVertices]))
    (hE' : E(GM09.deleteVertices G Z).Finite :=
      hE.subset (G.induce_le sdiff_subset).edgeSet_mono) :
    Hypergraph.ofGraph (GM09.deleteVertices G Z) hV' hE' =
      (Hypergraph.ofGraph G hV hE).deleteVertices Z := by
  have hle1 : Hypergraph.ofGraph (GM09.deleteVertices G Z) hV' hE' ≤
      Hypergraph.ofGraph G hV hE := by
    have hle_G : GM09.deleteVertices G Z ≤ G := G.induce_le sdiff_subset
    refine ⟨hle_G.vertexSet_mono, hle_G.edgeSet_mono, fun e he => ?_⟩
    ext v
    simp only [Hypergraph.ends, Hypergraph.ofGraph, GM09.deleteVertices, Graph.Inc,
      induce_isLink, mem_ofPred_eq, mem_sdiff]
    change e ∈ E(G.induce (V(G) \ Z)) at he
    rw [Graph.edgeSet_induce, mem_ofPred_eq] at he
    obtain ⟨x, y, hlink, ⟨hxG, hxZ⟩, ⟨hyG, hyZ⟩⟩ := he
    constructor
    · rintro ⟨z, hlink'⟩
      have hv : v ∈ V(G) ∧ v ∉ Z := by
        rcases G.eq_or_eq_of_isLink_of_isLink hlink' hlink with rfl | rfl
        · exact ⟨hxG, hxZ⟩
        · exact ⟨hyG, hyZ⟩
      have hz : z ∈ V(G) ∧ z ∉ Z := by
        rcases G.eq_or_eq_of_isLink_of_isLink hlink'.symm hlink with rfl | rfl
        · exact ⟨hxG, hxZ⟩
        · exact ⟨hyG, hyZ⟩
      exact ⟨z, hlink', hv, hz⟩
    · rintro ⟨z, hlink', _, _⟩
      exact ⟨z, hlink'⟩
  have hle2 : (Hypergraph.ofGraph G hV hE).deleteVertices Z ≤
      Hypergraph.ofGraph G hV hE := deleteVertices_le _ _
  refine eq_of_le_of_vertexSet_eq_of_edgeSet_eq hle1 hle2 rfl ?_
  ext e
  simp only [Hypergraph.ofGraph, GM09.deleteVertices, Hypergraph.deleteVertices,
    Graph.edgeSet_induce,
    mem_ofPred_eq, mem_sdiff]
  constructor
  · rintro ⟨u, v, hlink, ⟨huG, huZ⟩, ⟨hvG, hvZ⟩⟩
    refine ⟨(G.edge_mem_iff_exists_isLink e).mpr ⟨u, v, hlink⟩, fun w hwZ ⟨z, hwz⟩ => ?_⟩
    rcases G.eq_or_eq_of_isLink_of_isLink hwz hlink with rfl | rfl
    · exact huZ hwZ
    · exact hvZ hwZ
  · rintro ⟨heG, hno⟩
    rw [G.edge_mem_iff_exists_isLink] at heG
    obtain ⟨u, v, hlink⟩ := heG
    exact ⟨u, v, hlink,
      ⟨G.left_mem_of_isLink hlink, fun huZ => hno u huZ ⟨v, hlink⟩⟩,
      ⟨G.left_mem_of_isLink hlink.symm, fun hvZ => hno v hvZ ⟨u, hlink.symm⟩⟩⟩

/-- If `T_star` is a graph tangle of order `θ_star` in `G` and `Z ⊆ V(G)` with `Z.ncard < θ_star`,
then `deleteGraphVerticesTangle G hT.finite_V hT.finite_E Z T_star θ_star` is a graph tangle of
order `θ_star - Z.ncard` in `GM09.deleteVertices G Z`. -/
theorem isGraphTangle_deleteGraphVerticesTangle {G : Graph α β} {θ_star : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    (hT : IsGraphTangle G θ_star T_star) {Z : Set α}
    (hZ_sub : Z ⊆ V(G)) (hZ_lt : Z.ncard < θ_star) :
    IsGraphTangle (GM09.deleteVertices G Z) (θ_star - Z.ncard)
      (deleteGraphVerticesTangle G hT.finite_V hT.finite_E Z T_star θ_star) where
  finite_V := hT.finite_V.subset (by simp [GM09.deleteVertices])
  finite_E := hT.finite_E.subset (G.induce_le sdiff_subset).edgeSet_mono
  isTangle := by
    rw [ofGraph_deleteVertices_eq G hT.finite_V hT.finite_E Z]
    exact GM10.theorem_8_5_proof (isGraph_ofGraph G hT.finite_V hT.finite_E)
      hT.isTangle hZ_sub hZ_lt

/-! ## Statements and Proofs of (7.3) and (7.4) (page 63) -/

/-- Statement of Graph Minors XVI, (7.3) (page 63):
"Let $\mathcal{T}^*$ be a tangle in a graph $G$, let $Z \subseteq V(G)$ with
$|Z| < ord(\mathcal{T}^*)$, and let $(A, B)$ be a separation of $G$ of order
$< ord(\mathcal{T}^*) - |Z|$. Then $(A, B) \in \mathcal{T}^*$ if and only if
$$(A \setminus (Z \cap V(A)), B \setminus (Z \cap V(B))) \in \mathcal{T}^* \setminus Z.$$" -/
def GM16Theorem73Statement : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (hT : IsGraphTangle G θ_star T_star)
    (Z : Set α) (A B : Hypergraph α β),
    Z ⊆ V(G) → Z.ncard < θ_star →
    (Hypergraph.ofGraph G hT.finite_V hT.finite_E).IsSeparation A B →
    separationOrder A B < θ_star - Z.ncard →
    ((A, B) ∈ T_star ↔
      (A.deleteVertices (Z ∩ A.vertexSet), B.deleteVertices (Z ∩ B.vertexSet)) ∈
        deleteGraphVerticesTangle G hT.finite_V hT.finite_E Z T_star θ_star)

/-- **Graph Minors XVI, (7.3)** (page 63):
For any separation `(A, B)` of `G` of order `< θ_star - |Z|`, `(A, B) ∈ T*` if and only if
`(A \ Z, B \ Z) ∈ T* \ Z`. -/
theorem theorem_7_3_proof : GM16Theorem73Statement.{u, v} := by
  intro α β G θ_star T_star hT Z A B hZ_sub hZ_lt hsep hord
  rw [deleteVertices_inter_vertexSet A Z, deleteVertices_inter_vertexSet B Z]
  let G_H := Hypergraph.ofGraph G hT.finite_V hT.finite_E
  have hT_del : IsTangle (G_H.deleteVertices Z) (θ_star - Z.ncard)
      (deleteGraphVerticesTangle G hT.finite_V hT.finite_E Z T_star θ_star) :=
    GM10.theorem_8_5_proof (isGraph_ofGraph G hT.finite_V hT.finite_E) hT.isTangle hZ_sub hZ_lt
  have hback : ∀ {X Y : Hypergraph α β},
      G_H.IsSeparation X Y → separationOrder X Y < θ_star - Z.ncard →
      (X.deleteVertices Z, Y.deleteVertices Z) ∈
        deleteGraphVerticesTangle G hT.finite_V hT.finite_E Z T_star θ_star →
      (X, Y) ∈ T_star := by
    intro X Y hsepXY hordXY hmem_del
    rcases hmem_del.2.2 with ⟨⟨A_star, B_star⟩, hm, hZ_AB, hA_eq, hB_eq⟩
    dsimp only at hm hZ_AB hA_eq hB_eq
    have hVX_sub : X.vertexSet ⊆ A_star.vertexSet := by
      intro v hvX
      by_cases hvZ : v ∈ Z
      · exact (hZ_AB hvZ).1
      · have hv_del : v ∈ (X.deleteVertices Z).vertexSet := ⟨hvX, hvZ⟩
        rw [← hA_eq] at hv_del
        exact hv_del.1
    exact GM10.theorem_2_9_proof hT.isTangle hm hsepXY (by omega) (Or.inr (Or.inl hVX_sub))
  constructor
  · intro hAB
    by_contra hnot_del
    have ⟨hsep_del, hord_del_le⟩ := isSeparation_deleteVertices hsep Z
    have hBA_del : (B.deleteVertices Z, A.deleteVertices Z) ∈
        deleteGraphVerticesTangle G hT.finite_V hT.finite_E Z T_star θ_star :=
      (hT_del.axiom1 hsep_del (hord_del_le.trans_lt hord)).resolve_left hnot_del
    have hord_BA : separationOrder B A < θ_star - Z.ncard := by
      rwa [separationOrder_comm]
    have hBA : (B, A) ∈ T_star := hback hsep.symm hord_BA hBA_del
    exact GM10.theorem_2_1_proof hT.isTangle hAB hBA
  · exact hback hsep hord

/-- Lift a `SpanEmbedding H G'` along a subgraph inclusion `G' ≤ G`. -/
def liftSpanEmbedding {H : Drawing S} {G' G : Graph α β}
    (η : SpanEmbedding H G') (hle : G' ≤ G) :
    SpanEmbedding H G where
  imageGraph := η.imageGraph
  vMap := η.vMap
  eMap := η.eMap
  imageGraph_le := η.imageGraph_le.trans hle
  bijOn_v := η.bijOn_v
  bijOn_e := η.bijOn_e
  inc_iff := η.inc_iff

/-- Statement of Graph Minors XVI, (7.4) (page 63):
"Let $\mathcal{T}^*$ be a tangle in $G$, and let $Z \subseteq V(G)$ with $|Z| < ord(\mathcal{T}^*)$.
If $H, \eta, \mathcal{T}$ is a $\Sigma$-span in $G \setminus Z$ with respect to
$\mathcal{T}^* \setminus Z$ then $H, \eta, \mathcal{T}$ is a $\Sigma$-span in $G$ with respect to
$\mathcal{T}^*$." -/
def GM16Theorem74Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S]
    {α : Type u} {β : Type v} (G : Graph α β) (θ_star θ : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (hT : IsGraphTangle G θ_star T_star)
    (Z : Set α)
    (H : Drawing S) (η : SpanEmbedding H (GM09.deleteVertices G Z))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))),
    Z ⊆ V(G) → Z.ncard < θ_star →
    IsSigmaSpan (GM09.deleteVertices G Z) H η (θ_star - Z.ncard) θ
      (deleteGraphVerticesTangle G hT.finite_V hT.finite_E Z T_star θ_star) T →
    IsSigmaSpan G H (liftSpanEmbedding η (G.induce_le sdiff_subset)) θ_star θ T_star T

/-- **Graph Minors XVI, (7.4)** (page 63):
Every `Σ`-span in `G \ Z` with respect to `T* \ Z` is a `Σ`-span in `G` with respect to `T*`. -/
theorem theorem_7_4_proof : GM16Theorem74Statement.{u, v, w} := by
  intro S _ _ α β G θ_star θ T_star hT Z H η T hZ_sub hZ_lt hSpan
  let η' := liftSpanEmbedding η (G.induce_le sdiff_subset)
  have hθ_le_del : θ ≤ θ_star - Z.ncard := hSpan.isControlling.theta_le
  refine ⟨hSpan.isSurface, hSpan.isConnected, hSpan.bd_empty, hSpan.isRigid, hSpan.isRespectful,
    ⟨by omega, hT, hSpan.isControlling.isTangle_H, ?_⟩⟩
  intro A B hsep hord A_H B_H hRestr
  have hord_lt_del : separationOrder A B < θ_star - Z.ncard := by omega
  have h73 := theorem_7_3_proof G θ_star T_star hT Z A B hZ_sub hZ_lt hsep hord_lt_del
  rw [deleteVertices_inter_vertexSet A Z, deleteVertices_inter_vertexSet B Z] at h73
  have ⟨hsep_del, hord_del_le⟩ := isSeparation_deleteVertices hsep Z
  have hsep_del' :
      (Hypergraph.ofGraph (GM09.deleteVertices G Z)
        hSpan.isControlling.isTangle_star.finite_V
        hSpan.isControlling.isTangle_star.finite_E).IsSeparation
        (A.deleteVertices Z) (B.deleteVertices Z) := by
    rwa [ofGraph_deleteVertices_eq G hT.finite_V hT.finite_E Z]
  have hV_img_sub : V(η.imageGraph) ⊆ V(G) \ Z := by
    simpa [GM09.deleteVertices] using η.imageGraph_le.vertexSet_mono
  have hRestr_del :
      IsRestrictedSeparation H (GM09.deleteVertices G Z) η
        (A.deleteVertices Z) (B.deleteVertices Z) A_H B_H := by
    rcases hRestr with ⟨hsepH, hVA, hEA, hVB, hEB⟩
    change η.vMap '' A_H.vertexSet = A.vertexSet ∩ V(η.imageGraph) at hVA
    change η.eMap '' A_H.edgeSet = A.edgeSet ∩ E(η.imageGraph) at hEA
    change η.vMap '' B_H.vertexSet = B.vertexSet ∩ V(η.imageGraph) at hVB
    change η.eMap '' B_H.edgeSet = B.edgeSet ∩ E(η.imageGraph) at hEB
    refine ⟨hsepH, ?_, ?_, ?_, ?_⟩
    · rw [hVA]
      ext v
      simp only [Hypergraph.deleteVertices, mem_inter_iff, mem_sdiff]
      exact ⟨fun ⟨hvA, hvI⟩ => ⟨⟨hvA, (hV_img_sub hvI).2⟩, hvI⟩,
        fun ⟨⟨hvA, _⟩, hvI⟩ => ⟨hvA, hvI⟩⟩
    · rw [hEA]
      ext e
      simp only [Hypergraph.deleteVertices, mem_inter_iff, mem_ofPred_eq]
      refine ⟨fun ⟨heA, heI⟩ => ⟨⟨heA, fun v hvZ hincA => ?_⟩, heI⟩,
        fun ⟨⟨heA, _⟩, heI⟩ => ⟨heA, heI⟩⟩
      have hincG : (Hypergraph.ofGraph G hT.finite_V hT.finite_E).Inc e v :=
        (inc_iff_of_le hsep.left_le heA).mp hincA
      obtain ⟨w, hlinkG⟩ := hincG
      have heI_save := heI
      rw [η.imageGraph.edge_mem_iff_exists_isLink] at heI
      obtain ⟨x, y, hlinkI⟩ := heI
      have hlinkG' : G.IsLink e x y := (η'.imageGraph_le.isLink_iff heI_save).mp hlinkI
      rcases G.eq_or_eq_of_isLink_of_isLink hlinkG hlinkG' with rfl | rfl
      · exact (hV_img_sub (η.imageGraph.left_mem_of_isLink hlinkI)).2 hvZ
      · exact (hV_img_sub (η.imageGraph.left_mem_of_isLink hlinkI.symm)).2 hvZ
    · rw [hVB]
      ext v
      simp only [Hypergraph.deleteVertices, mem_inter_iff, mem_sdiff]
      exact ⟨fun ⟨hvB, hvI⟩ => ⟨⟨hvB, (hV_img_sub hvI).2⟩, hvI⟩,
        fun ⟨⟨hvB, _⟩, hvI⟩ => ⟨hvB, hvI⟩⟩
    · rw [hEB]
      ext e
      simp only [Hypergraph.deleteVertices, mem_inter_iff, mem_ofPred_eq]
      refine ⟨fun ⟨heB, heI⟩ => ⟨⟨heB, fun v hvZ hincB => ?_⟩, heI⟩,
        fun ⟨⟨heB, _⟩, heI⟩ => ⟨heB, heI⟩⟩
      have hincG : (Hypergraph.ofGraph G hT.finite_V hT.finite_E).Inc e v :=
        (inc_iff_of_le hsep.right_le heB).mp hincB
      obtain ⟨w, hlinkG⟩ := hincG
      have heI_save := heI
      rw [η.imageGraph.edge_mem_iff_exists_isLink] at heI
      obtain ⟨x, y, hlinkI⟩ := heI
      have hlinkG' : G.IsLink e x y := (η'.imageGraph_le.isLink_iff heI_save).mp hlinkI
      rcases G.eq_or_eq_of_isLink_of_isLink hlinkG hlinkG' with rfl | rfl
      · exact (hV_img_sub (η.imageGraph.left_mem_of_isLink hlinkI)).2 hvZ
      · exact (hV_img_sub (η.imageGraph.left_mem_of_isLink hlinkI.symm)).2 hvZ
  rw [h73]
  exact hSpan.isControlling.controls hsep_del' (hord_del_le.trans_lt hord) hRestr_del

/-- If `T* \ Z` controls an `L`-minor of `G \ Z` and `|V(L)| ≤ ord(T*) - |Z|`, then `T*` controls
an `L`-minor of `G` (Graph Minors XVI, Section 7, page 63: "it is easy to see that $\mathcal{T}^*$
controls every minor controlled by $\mathcal{T}^* \setminus Z$"). -/
theorem controlsMinor_of_deleteGraphVerticesTangle
    {α' : Type*} {β' : Type*} {G : Graph α β} {L : Graph α' β'} {θ_star : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    (hT : IsGraphTangle G θ_star T_star) {Z : Set α}
    (hZ_sub : Z ⊆ V(G)) (hZ_lt : Z.ncard < θ_star)
    (hVL_le : V(L).ncard ≤ θ_star - Z.ncard)
    (hCtrl : ControlsMinor (GM09.deleteVertices G Z) L
      (deleteGraphVerticesTangle G hT.finite_V hT.finite_E Z T_star θ_star)) :
    ControlsMinor G L T_star := by
  have hle_del : GM09.deleteVertices G Z ≤ G := G.induce_le sdiff_subset
  obtain ⟨α_v, α_e, hconn, hdisj, hlink, hloop, hinj, htangle⟩ := hCtrl
  refine ⟨α_v, α_e, ?_, hdisj, ?_, ?_, hinj, ?_⟩
  · intro v hv
    obtain ⟨h_le, h_ne, h_gc⟩ := hconn v hv
    exact ⟨h_le.trans hle_del, h_ne, h_gc⟩
  · intro e he u hu v hv huv hLlink
    obtain ⟨he_del, x, hx, y, hy, hlink_del⟩ := hlink e he u hu v hv huv hLlink
    exact ⟨hle_del.edgeSet_mono he_del, x, hx, y, hy, hlink_del.1⟩
  · intro e he v hv hLloop
    obtain ⟨⟨he_del, he_not⟩, x, hx, y, hy, hlink_del⟩ := hloop e he v hv hLloop
    exact ⟨⟨hle_del.edgeSet_mono he_del, he_not⟩, x, hx, y, hy, hlink_del.1⟩
  · intro A B hAB hord v hv hv_sub
    have hsep : (Hypergraph.ofGraph G hT.finite_V hT.finite_E).IsSeparation A B :=
      hT.isTangle.isSeparation hAB
    have hord_lt : separationOrder A B < θ_star - Z.ncard := hord.trans_le hVL_le
    have h73 := (theorem_7_3_proof G θ_star T_star hT Z A B hZ_sub hZ_lt hsep hord_lt).mp hAB
    rw [deleteVertices_inter_vertexSet A Z, deleteVertices_inter_vertexSet B Z] at h73
    have ⟨_, hord_del_le⟩ := isSeparation_deleteVertices hsep Z
    have hv_del_sub : V(α_v v) ⊆ (A.deleteVertices Z).vertexSet := by
      intro x hx
      have hx_in : x ∈ V(GM09.deleteVertices G Z) := (hconn v hv).1.vertexSet_mono hx
      have hx_not_Z : x ∉ Z := by
        change x ∈ V(G) \ Z at hx_in
        exact hx_in.2
      exact ⟨hv_sub hx, hx_not_Z⟩
    exact htangle h73 (hord_del_le.trans_lt hord) v hv hv_del_sub

/-! ## Statements of (7.1) and (7.2), and Proof of (6.1) (pages 62–63) -/

/-- Statement of Graph Minors XVI, (7.1) (page 62):
"Let $\Sigma$ be a surface, and let $\tau, \chi, \delta, \lambda \ge 0, \theta' \ge 1$ and
$\phi, \psi \ge 3$. Then there exist $\theta \ge 1$ and $\sigma \ge 0$ such that if
$\mathcal{T}^*$ is a tangle in a graph $G$, and there is an animal with $\chi$ horns and $\delta$
hairs, of strength $\ge (\theta, \sigma)$, then either
- there is a $\Sigma'$-span of order $\ge \phi$, for some surface $\Sigma'$ obtained from $\Sigma$
  by adding a handle, or
- there is an animal with $\chi$ horns and $\delta + 1$ hairs, of strength $\ge (\psi, \tau)$, or
- there exists $Z \subseteq V(G)$ with $|Z| \le \chi + \frac{1}{2}\delta^2\phi^2$ such that some
  $\Sigma$-span of order $\ge \theta'$ in $G\setminus Z$ with respect to $\mathcal{T}^*\setminus Z$
  is $(\lambda, 2\psi)$-level." -/
def GM16Theorem71Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S],
    IsClosedSurface S → ConnectedSpace S →
    ∀ τ χ δ lam θ' φ ψ : ℕ, 1 ≤ θ' → 3 ≤ φ → 3 ≤ ψ →
      ∃ θ σ : ℕ, 1 ≤ θ ∧
        ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star : ℕ)
          (T_star : Set (Hypergraph α β × Hypergraph α β))
          (hT : IsGraphTangle G θ_star T_star),
          HasAnimal S G T_star θ_star χ δ θ σ →
          (∃ (S' : Type w) (_ : TopologicalSpace S') (_ : T2Space S')
            (H' : Drawing S') (η' : SpanEmbedding H' G) (θ_span' : ℕ)
            (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))),
            IsClosedSurface S' ∧ ConnectedSpace S' ∧
            IsObtainedByAddingHandle S S' ∧
            φ ≤ θ_span' ∧ IsSigmaSpan G H' η' θ_star θ_span' T_star T') ∨
          HasAnimal S G T_star θ_star χ (δ + 1) ψ τ ∨
          (∃ (Z : Set α) (H_l : Drawing S) (η_l : SpanEmbedding H_l (GM09.deleteVertices G Z))
            (θ_l : ℕ)
            (T_l : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
            (d_l : Set S → Set S → ℕ),
            Z ⊆ V(G) ∧ Z.ncard ≤ χ + δ ^ 2 * φ ^ 2 / 2 ∧ Z.ncard < θ_star ∧
            θ' ≤ θ_l ∧
            IsLevelSpan (GM09.deleteVertices G Z) H_l η_l (θ_star - Z.ncard) θ_l lam (2 * ψ)
              (deleteGraphVerticesTangle G hT.finite_V hT.finite_E Z T_star θ_star) T_l d_l)

/-- Statement of Graph Minors XVI, (7.2) (page 62, strengthened from Graph Minors XV, (8.4)):
"Let $\Sigma$ be a surface and let $p, \phi, \mu \ge 0$. Then there exist $\kappa, \lambda, \rho \ge
0$
and $\theta \ge 1$ such that if $\mathcal{T}^*$ is a tangle in a graph $G$, and some $\Sigma$-span
of
order $\ge \theta$ is $(\lambda, \mu)$-level, then either:
1. there is a $\Sigma'$-span of order $\phi$, for some surface $\Sigma'$ obtained from $\Sigma$ by
   adding a crosscap, or
2. there is a $\mathcal{T}^*$-central segregation of $G$ of type $(\rho, \kappa)$ with a proper
   arrangement in $\Sigma$, or
3. $\mathcal{T}^*$ controls a $K_p$ minor of $G$." -/
def GM16Theorem72Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S],
    IsClosedSurface S → ConnectedSpace S →
    ∀ p φ μ : ℕ,
      ∃ κ lam ρ θ : ℕ, 1 ≤ θ ∧
        ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star θ_span : ℕ)
          (T_star : Set (Hypergraph α β × Hypergraph α β))
          (H : Drawing S) (η : SpanEmbedding H G)
          (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
          (d : Set S → Set S → ℕ),
          IsGraphTangle G θ_star T_star →
          θ ≤ θ_span →
          IsLevelSpan G H η θ_star θ_span lam μ T_star T d →
          (∃ (S' : Type w) (_ : TopologicalSpace S') (_ : T2Space S')
            (H' : Drawing S') (η' : SpanEmbedding H' G) (θ_span' : ℕ)
            (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))),
            IsClosedSurface S' ∧ ConnectedSpace S' ∧
            IsObtainedByAddingCrosscap S S' ∧
            φ ≤ θ_span' ∧ IsSigmaSpan G H' η' θ_star θ_span' T_star T') ∨
          (∃ (S_seg : Set (Society α β))
            (α_disc : Society α β → Set S) (α_pt : α → S),
            IsCentralSegregation G T_star S_seg ∧
            IsSegregationOfType G ρ κ S_seg ∧
            IsProperArrangement S_seg α_disc α_pt) ∨
          ControlsMinor G (completeGraph p) T_star


end GraphMinor.GM16
