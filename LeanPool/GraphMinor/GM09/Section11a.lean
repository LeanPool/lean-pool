/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module
public import LeanPool.GraphMinor.GM09.Defs
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM09.Section2d
import LeanPool.GraphMinor.GM09.Section3a

/-!
# Graph Minors IX, Section 11 (Part 1): Consolidations and Their Cores ((11.6)–(11.10))

This file formalizes (11.6), (11.7), (11.8), (11.9), and (11.10) from Section 11 of
N. Robertson and P. D. Seymour, *Graph Minors. IX. Disjoint crossed paths*,
J. Combin. Theory Ser. B **49** (1990) 40–77 (pages 70–73).
-/

@[expose] public section

namespace GraphMinor.GM09
open Set Graph GraphMinor.Surface GraphMinor.GM06
universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}

/-! ## Helper definitions and lemmas for (11.6) -/

/-- The single-vertex edgeless subgraph `A_v` of `G` with `V(A_v) = {v}` and `E(A_v) = ∅`. -/
def singleVertexSubgraph (G : Graph α β) (v : α) : Graph α β := (G.induce {v}).restrict ∅
@[simp] theorem vertexSet_singleVertexSubgraph (G : Graph α β) (v : α) : V(singleVertexSubgraph G
  v) = {v} := rfl
@[simp] theorem edgeSet_singleVertexSubgraph (G : Graph α β) (v : α) :
    E(singleVertexSubgraph G v) = ∅ := by simp [singleVertexSubgraph]
theorem singleVertexSubgraph_le {G : Graph α β} {v : α} (hv : v ∈ V(G)) :
    singleVertexSubgraph G v ≤ G := restrict_le.trans (G.induce_le (singleton_subset_iff.mpr hv))

/-- The single-edge subgraph `A_e` of `G` consisting of `e` and its ends. -/
def singleEdgeSubgraph (G : Graph α β) (e : β) : Graph α β := (G.induce {u : α | G.Inc e
  u}).restrict {e}
@[simp] theorem vertexSet_singleEdgeSubgraph (G : Graph α β) (e : β) :
    V(singleEdgeSubgraph G e) = {u : α | G.Inc e u} := rfl
theorem singleEdgeSubgraph_le (G : Graph α β) (e : β) : singleEdgeSubgraph G e ≤ G :=
  restrict_le.trans (G.induce_le fun _ hu => hu.vertex_mem)
theorem vertexSet_singleEdgeSubgraph_eq_pair {G : Graph α β} {e : β} {x y : α}
    (hxy : G.IsLink e x y) : V(singleEdgeSubgraph G e) = {x, y} := by
  ext u; simp only [vertexSet_singleEdgeSubgraph, mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
  exact ⟨fun ⟨_, huw⟩ => G.eq_or_eq_of_isLink_of_isLink huw hxy,
    by rintro (rfl | rfl); exacts [⟨y, hxy⟩, ⟨x, hxy.symm⟩]⟩
@[simp] theorem edgeSet_singleEdgeSubgraph {G : Graph α β} {e : β} (he : e ∈ E(G)) :
    E(singleEdgeSubgraph G e) = {e} := by
  unfold singleEdgeSubgraph; rw [edgeSet_restrict, inter_eq_right, singleton_subset_iff]
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet he; exact ⟨x, y, hxy, ⟨y, hxy⟩, ⟨x,
    hxy.symm⟩⟩
theorem singleEdgeSubgraph_isLink {G : Graph α β} {e f : β} {x y : α} :
    (singleEdgeSubgraph G e).IsLink f x y ↔ f = e ∧ G.IsLink e x y := by
  rw [(singleEdgeSubgraph_le G e).isLink_iff']
  refine ⟨fun ⟨hlink, hf⟩ => ?_, fun ⟨rfl, hlink⟩ => ?_⟩
  · obtain rfl : f = e := mem_singleton_iff.mp hf.2; exact ⟨rfl, hlink⟩
  · rw [edgeSet_singleEdgeSubgraph hlink.edge_mem]; exact ⟨hlink, rfl⟩

/-- The subgraph `G \ e` obtained by deleting a single edge `e` from `G` while keeping all vertices.
-/
def deleteSingleEdge (G : Graph α β) (e : β) : Graph α β := G.restrict (E(G) \ {e})
@[simp] theorem vertexSet_deleteSingleEdge (G : Graph α β) (e : β) : V(deleteSingleEdge G e) = V(G)
  := rfl
@[simp] theorem edgeSet_deleteSingleEdge (G : Graph α β) (e : β) : E(deleteSingleEdge G e)
  = E(G) \ {e} := by
  unfold deleteSingleEdge; rw [edgeSet_restrict, inter_eq_right]; exact sdiff_subset
theorem deleteSingleEdge_le (G : Graph α β) (e : β) : deleteSingleEdge G e ≤ G := restrict_le
theorem isGraphPathWithEnds_singleEdgeSubgraph {G : Graph α β} {e : β} {u v : α}
    (huv : u ≠ v) (hlink : G.IsLink e u v) :
    IsGraphPathWithEnds (singleEdgeSubgraph G e) (singleEdgeSubgraph G e) u v := by
  have hlink_A := singleEdgeSubgraph_isLink.mpr ⟨rfl, hlink⟩
  let W : GraphWalk (singleEdgeSubgraph G e) u v := .cons hlink_A (.nil hlink_A.right_mem)
  refine ⟨le_rfl, W, by unfold GraphWalk.IsSimple; simp [W, huv], ?_, ?_⟩
  · rw [vertexSet_singleEdgeSubgraph_eq_pair hlink]; ext z; simp [W]
  · rw [edgeSet_singleEdgeSubgraph hlink.edge_mem]; ext f; simp [W]

/-- **Graph Minors IX, (11.6)** (page 70):
"Every society has a consolidation." -/
theorem theorem_11_6_proof (S : Society α β) : ∃ D_set : Set (Graph α β × Graph α β),
  IsConsolidation S D_set := by
  let D_V := (fun v => (singleVertexSubgraph S.G v, S.G)) '' V(S.G)
  let D_E := (fun e => (singleEdgeSubgraph S.G e, deleteSingleEdge S.G e)) '' E(S.G)
  let D_set := D_V ∪ D_E
  have hA_le : ∀ ⦃A B : Graph α β⦄, (A, B) ∈ D_set → A ≤ S.G := by
    rintro A B (⟨v, hv, hpair⟩ | ⟨e, _, hpair⟩) <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
    · exact singleVertexSubgraph_le hv
    · exact singleEdgeSubgraph_le S.G e
  refine ⟨D_set, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · rintro A B (⟨v, hv, hpair⟩ | ⟨e, he, hpair⟩) <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
    · refine ⟨⟨singleVertexSubgraph_le hv, le_rfl, ?_, by simp, ?_⟩, S.bar_subset⟩
      · rw [vertexSet_singleVertexSubgraph, singleton_union, insert_eq_of_mem hv]
      · rw [edgeSet_singleVertexSubgraph]; exact empty_disjoint _
    · refine ⟨⟨singleEdgeSubgraph_le S.G e, deleteSingleEdge_le S.G e, ?_, ?_, ?_⟩, S.bar_subset⟩
      · rw [vertexSet_deleteSingleEdge, union_eq_right.mpr (singleEdgeSubgraph_le S.G
        e).vertexSet_mono]
      · rw [edgeSet_singleEdgeSubgraph he, edgeSet_deleteSingleEdge,
          union_sdiff_cancel (singleton_subset_iff.mpr he)]
      · rw [edgeSet_singleEdgeSubgraph he, edgeSet_deleteSingleEdge]; exact disjoint_sdiff_right
  · rintro A B (⟨v, _, hpair⟩ | ⟨e, he, hpair⟩) <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
    · exact (ncard_le_ncard inter_subset_left (finite_singleton v)).trans (by simp)
    · obtain ⟨x, y, hxy⟩ := S.G.exists_isLink_of_mem_edgeSet he
      have hsub : V(singleEdgeSubgraph S.G e) ∩ V(deleteSingleEdge S.G e) ⊆ {x, y} := by
        rw [vertexSet_singleEdgeSubgraph_eq_pair hxy]; exact inter_subset_left
      exact (ncard_le_ncard hsub ((finite_singleton y).insert x)).trans
        ((ncard_insert_le x {y}).trans (by simp))
  · rintro A B A' B' hAB hA'B' hne
    have hAG : A ≤ S.G := hA_le hAB
    rcases hA'B' with ⟨v', _, hpair'⟩ | ⟨e', he', hpair'⟩ <;> obtain ⟨rfl, rfl⟩
      := Prod.mk.inj hpair'
    · exact hAG
    · rw [(Compatible.of_le_le hAG (deleteSingleEdge_le S.G e')).le_iff,
        vertexSet_deleteSingleEdge, edgeSet_deleteSingleEdge]
      refine ⟨hAG.vertexSet_mono, ?_⟩
      rcases hAB with ⟨v, _, hpair⟩ | ⟨e, he, hpair⟩ <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
      · simp
      · rw [edgeSet_singleEdgeSubgraph he, singleton_subset_iff]; exact ⟨he, fun h => hne (h ▸ rfl)⟩
  · have hP : ∀ P ∈ Prod.fst '' D_set, P ≤ S.G := by rintro P ⟨⟨A, B⟩, hAB, rfl⟩; exact hA_le hAB
    refine (Compatible.of_le_le (subgraphSUnion_le hP) le_rfl).ext
      (subset_antisymm (subgraphSUnion_le hP).vertexSet_mono fun v hv => ?_)
      (subset_antisymm (subgraphSUnion_le hP).edgeSet_mono fun e he => ?_)
    · rw [vertexSet_subgraphSUnion, mem_iUnion₂]
      exact ⟨singleVertexSubgraph S.G v, ⟨(singleVertexSubgraph S.G v, S.G), Or.inl ⟨v, hv, rfl⟩,
        rfl⟩, by simp⟩
    · rw [edgeSet_subgraphSUnion hP, mem_iUnion₂]
      exact ⟨singleEdgeSubgraph S.G e,
        ⟨(singleEdgeSubgraph S.G e, deleteSingleEdge S.G e), Or.inr ⟨e, he, rfl⟩, rfl⟩, by simp
          [he]⟩
  · rintro A B (⟨v, _, hpair⟩ | ⟨e, he, hpair⟩) u hu w hw huw <;> obtain ⟨rfl, rfl⟩
    := Prod.mk.inj hpair
    · exact (huw ((mem_singleton_iff.mp hu.1).trans (mem_singleton_iff.mp hw.1).symm)).elim
    · obtain ⟨x, y, hxy⟩ := S.G.exists_isLink_of_mem_edgeSet he
      have hV_eq := vertexSet_singleEdgeSubgraph_eq_pair hxy
      have hu_xy : u = x ∨ u = y := by
        have h := hu.1; rwa [hV_eq, mem_insert_iff, mem_singleton_iff] at h
      have hw_xy : w = x ∨ w = y := by
        have h := hw.1; rwa [hV_eq, mem_insert_iff, mem_singleton_iff] at h
      have hlink_uw : S.G.IsLink e u w := by
        rcases hu_xy with rfl | rfl <;> rcases hw_xy with rfl | rfl
        · exact (huw rfl).elim
        · exact hxy
        · exact hxy.symm
        · exact (huw rfl).elim
      refine ⟨singleEdgeSubgraph S.G e, isGraphPathWithEnds_singleEdgeSubgraph huw hlink_uw, ?_⟩
      rw [vertexSet_singleEdgeSubgraph_eq_pair hlink_uw, Set.sdiff_self]; exact empty_disjoint _

/-! ## (11.7) and properties of `consolidationBInter` and `consolidationCore` -/

/-- The subgraph intersection `⋂ (B : (A, B) ∈ D_set)` inside `S.G`. -/
def consolidationBInter (S : Society α β) (D_set : Set (Graph α β × Graph α β)) : Graph α β :=
  (S.G.induce (V(S.G) ∩ ⋂ p ∈ D_set, V(p.2))).restrict (E(S.G) ∩ ⋂ p ∈ D_set, E(p.2))
@[simp] theorem vertexSet_consolidationBInter (S : Society α β) (D_set : Set
  (Graph α β × Graph α β)) :
    V(consolidationBInter S D_set) = V(S.G) ∩ ⋂ p ∈ D_set, V(p.2) := rfl
theorem consolidationBInter_le (S : Society α β) (D_set : Set (Graph α β × Graph α β)) :
    consolidationBInter S D_set ≤ S.G := restrict_le.trans (S.G.induce_le inter_subset_left)
theorem IsConsolidation.left_le {S : Society α β} {D_set : Set (Graph α β × Graph α β)}
    (hD : IsConsolidation S D_set) {A B : Graph α β} (hAB : (A, B) ∈ D_set) :
    A ≤ S.G := (hD.isSocietySeparation hAB).1.1
theorem IsConsolidation.right_le {S : Society α β} {D_set : Set (Graph α β × Graph α β)}
    (hD : IsConsolidation S D_set) {A B : Graph α β} (hAB : (A, B) ∈ D_set) :
    B ≤ S.G := (hD.isSocietySeparation hAB).1.2.1
theorem IsConsolidation.forall_fst_le {S : Society α β} {D_set : Set (Graph α β × Graph α β)}
    (hD : IsConsolidation S D_set) : ∀ P ∈ Prod.fst '' D_set, P ≤ S.G := by
  rintro P ⟨⟨A, B⟩, hAB, rfl⟩; exact hD.left_le hAB
theorem IsConsolidation.exists_mem_of_mem_edgeSet {S : Society α β}
    {D_set : Set (Graph α β × Graph α β)} (hD : IsConsolidation S D_set) {e : β} (he : e ∈ E(S.G)) :
    ∃ A B : Graph α β, (A, B) ∈ D_set ∧ e ∈ E(A) := by
  have he' : e ∈ E(subgraphSUnion S.G (Prod.fst '' D_set)) := by rwa [hD.union_eq]
  rw [edgeSet_subgraphSUnion hD.forall_fst_le, mem_iUnion₂] at he'
  rcases he' with ⟨A, ⟨⟨A', B'⟩, hAB, rfl⟩, heA⟩; exact ⟨A', B', hAB, heA⟩
theorem IsConsolidation.exists_mem_of_mem_vertexSet {S : Society α β}
    {D_set : Set (Graph α β × Graph α β)} (hD : IsConsolidation S D_set) {v : α} (hv : v ∈ V(S.G)) :
    ∃ A B : Graph α β, (A, B) ∈ D_set ∧ v ∈ V(A) := by
  have hv' : v ∈ V(subgraphSUnion S.G (Prod.fst '' D_set)) := by rwa [hD.union_eq]
  rw [vertexSet_subgraphSUnion, mem_iUnion₂] at hv'
  rcases hv' with ⟨A, ⟨⟨A', B'⟩, hAB, rfl⟩, hvA⟩; exact ⟨A', B', hAB, hvA⟩

/-- **Graph Minors IX, (11.7)** (page 70):
"If $\mathcal{D}$ is a consolidation of $(G, \Omega)$ and $C = \bigcap (B: (A, B) \in
\mathcal{D})$ then $E(C) = \emptyset$, $\bar{\Omega} \subseteq V(C)$, $A \cap B \subseteq C$
for every $(A, B) \in \mathcal{D}$ and $A_1 \cap A_2 \subseteq C$ for every two distinct
separations $(A_1, B_1), (A_2, B_2) \in \mathcal{D}$." -/
theorem theorem_11_7_proof {S : Society α β} {D_set : Set (Graph α β × Graph α β)}
  (hD : IsConsolidation S D_set) :
    let C := consolidationBInter S D_set
    E(C) = ∅ ∧ S.Ω.bar ⊆ V(C) ∧ (∀ ⦃A B : Graph α β⦄, (A, B) ∈ D_set → subgraphInter S.G A B ≤ C) ∧
    (∀ ⦃A₁ B₁ A₂ B₂ : Graph α β⦄,
      (A₁, B₁) ∈ D_set → (A₂, B₂) ∈ D_set → (A₁, B₁) ≠ (A₂, B₂) → subgraphInter S.G A₁ A₂ ≤ C) := by
  intro C; have hC_le : C ≤ S.G := consolidationBInter_le S D_set
  have hEC : E(C) = ∅ := eq_empty_iff_forall_notMem.mpr fun e heC => by
    obtain ⟨A, B, hAB, heA⟩ := hD.exists_mem_of_mem_edgeSet heC.2.1
    exact disjoint_left.mp (hD.isSocietySeparation hAB).1.2.2.2.2 heA (mem_iInter₂.mp heC.2.2 (A,
      B) hAB)
  have hΩC : S.Ω.bar ⊆ V(C) :=
    subset_inter S.bar_subset (subset_iInter₂_iff.mpr fun ⟨_, _⟩ hAB =>
      (hD.isSocietySeparation hAB).2)
  have hAB_le : ∀ ⦃A B : Graph α β⦄, (A, B) ∈ D_set → subgraphInter S.G A B ≤ C := by
    intro A B hAB; have hsep : IsGraphSeparation S.G A B := (hD.isSocietySeparation hAB).1
    rw [(Compatible.of_le_le (subgraphInter_le hsep.1) hC_le).le_iff]
    refine ⟨subset_inter (inter_subset_left.trans hsep.1.vertexSet_mono) ?_, ?_⟩
    · rw [subset_iInter₂_iff]; rintro ⟨A', B'⟩ hA'B' v ⟨hvA, hvB⟩
      by_cases heq : (A, B) = (A', B')
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq; exact hvB
      · exact (hD.left_le_right hAB hA'B' heq).vertexSet_mono hvA
    · rw [IsGraphSeparation.edgeSet_subgraphInter hsep]; exact empty_subset _
  refine ⟨hEC, hΩC, hAB_le, fun A₁ B₁ A₂ B₂ h1 h2 hne => ?_⟩
  have hA₁G := hD.left_le h1; have hA₂G := hD.left_le h2
  exact (le_subgraphInter hA₁G (hD.right_le h1) (subgraphInter_le_left hA₁G hA₂G)
    ((subgraphInter_le_right hA₁G hA₂G).trans (hD.left_le_right h2 h1 hne.symm))).trans (hAB_le h1)

/-! ## Properties of `consolidationCore` and `consolidationCoreSociety` -/
@[simp] theorem vertexSet_consolidationCore (S : Society α β) (D_set : Set
  (Graph α β × Graph α β)) :
    V(consolidationCore S D_set) = V(S.G) ∩ ⋂ p ∈ D_set, V(p.2) := rfl
@[simp] theorem consolidationCore_isLink (S : Society α β) (D_set : Set (Graph α β × Graph α β))
    {e : Sym2 α} {x y : α} : (consolidationCore S D_set).IsLink e x y ↔
      x ≠ y ∧ e = s(x, y) ∧ x ∈ V(consolidationCore S D_set) ∧ y ∈ V(consolidationCore S D_set) ∧
      ∃ p ∈ D_set, x ∈ V(p.1) ∩ V(p.2) ∧ y ∈ V(p.1) ∩ V(p.2) := Iff.rfl
theorem vertexSet_consolidationCore_subset (S : Society α β) (D_set : Set (Graph α β × Graph α β)) :
    V(consolidationCore S D_set) ⊆ V(S.G) := inter_subset_left
theorem vertexSet_consolidationCore_subset_right {S : Society α β}
    {D_set : Set (Graph α β × Graph α β)} {A B : Graph α β} (hAB : (A, B) ∈ D_set) :
    V(consolidationCore S D_set) ⊆ V(B) := fun _ hv => mem_iInter₂.mp hv.2 (A, B) hAB
theorem IsConsolidation.bar_subset_consolidationCore {S : Society α β}
    {D_set : Set (Graph α β × Graph α β)} (hD : IsConsolidation S D_set) :
    S.Ω.bar ⊆ V(consolidationCore S D_set) := (theorem_11_7_proof hD).2.1
theorem IsConsolidation.inter_subset_consolidationCore {S : Society α β}
    {D_set : Set (Graph α β × Graph α β)} (hD : IsConsolidation S D_set) {A B : Graph α β} (hAB :
      (A, B) ∈ D_set) :
    V(A) ∩ V(B) ⊆ V(consolidationCore S D_set) := ((theorem_11_7_proof hD).2.2.1 hAB).vertexSet_mono
theorem IsConsolidation.left_inter_left_subset_consolidationCore {S : Society α β}
    {D_set : Set (Graph α β × Graph α β)} (hD : IsConsolidation S D_set)
    {A₁ B₁ A₂ B₂ : Graph α β} (h1 : (A₁, B₁) ∈ D_set) (h2 : (A₂, B₂) ∈ D_set) (hne : (A₁, B₁) ≠
      (A₂, B₂)) :
    V(A₁) ∩ V(A₂) ⊆ V(consolidationCore S D_set) := ((theorem_11_7_proof hD).2.2.2 h1 h2
      hne).vertexSet_mono
theorem IsConsolidation.disjoint_edges_of_ne {S : Society α β}
    {D_set : Set (Graph α β × Graph α β)} (hD : IsConsolidation S D_set)
    {A₁ B₁ A₂ B₂ : Graph α β} (h1 : (A₁, B₁) ∈ D_set) (h2 : (A₂, B₂) ∈ D_set)
    (hne : (A₁, B₁) ≠ (A₂, B₂)) : Disjoint E(A₁) E(A₂) := by
  have hE := ((theorem_11_7_proof hD).2.2.2 h1 h2 hne).edgeSet_mono
  rw [(theorem_11_7_proof hD).1, edgeSet_subgraphInter (hD.left_le h1) (hD.left_le h2),
    subset_empty_iff] at hE
  exact disjoint_iff_inter_eq_empty.mpr hE
theorem IsConsolidation.consolidationCore_isLink_of_mem_inter {S : Society α β}
    {D_set : Set (Graph α β × Graph α β)} (hD : IsConsolidation S D_set)
    {A B : Graph α β} (hAB : (A, B) ∈ D_set) {u v : α}
    (hu : u ∈ V(A) ∩ V(B)) (hv : v ∈ V(A) ∩ V(B)) (huv : u ≠ v) : (consolidationCore S
      D_set).IsLink s(u, v) u v :=
  ⟨huv, rfl, hD.inter_subset_consolidationCore hAB hu,
    hD.inter_subset_consolidationCore hAB hv, (A, B), hAB, hu, hv⟩
theorem finite_vertexSet_consolidationCore (S : Society α β) (D_set : Set (Graph α β × Graph α β)) :
    V(consolidationCore S D_set).Finite := S.finite_V.subset (vertexSet_consolidationCore_subset S
      D_set)
theorem finite_edgeSet_consolidationCore (S : Society α β) (D_set : Set (Graph α β × Graph α β)) :
    E(consolidationCore S D_set).Finite := by
  have hsub : E(consolidationCore S D_set) ⊆ (fun p : α × α => s(p.1, p.2)) '' (V(S.G) ×ˢ V(S.G))
    := by
    rintro e ⟨u, v, _, rfl, hu, hv, _⟩; exact ⟨(u, v), ⟨hu.1, hv.1⟩, rfl⟩
  exact ((S.finite_V.prod S.finite_V).image _).subset hsub

/-- The core society `(C, Ω)` of a consolidation `D_set` of `S = (G, Ω)`. -/
def consolidationCoreSociety (S : Society α β)
    (D_set : Set (Graph α β × Graph α β)) (hD : IsConsolidation S D_set) : Society α (Sym2 α) :=
  ⟨consolidationCore S D_set, S.Ω, finite_vertexSet_consolidationCore S D_set,
    finite_edgeSet_consolidationCore S D_set, hD.bar_subset_consolidationCore⟩
@[simp] theorem consolidationCoreSociety_G (S : Society α β)
    (D_set : Set (Graph α β × Graph α β)) (hD : IsConsolidation S D_set) :
    (consolidationCoreSociety S D_set hD).G = consolidationCore S D_set := rfl
@[simp] theorem consolidationCoreSociety_Ω (S : Society α β)
    (D_set : Set (Graph α β × Graph α β)) (hD : IsConsolidation S D_set) :
    (consolidationCoreSociety S D_set hD).Ω = S.Ω := rfl

/-! ## (11.8): Partitioning a consolidation along a separation of its core -/

/-- **Graph Minors IX, (11.8)** (pages 70–71):
"Let $\mathcal{D}$ be a consolidation of $(G, \Omega)$ with core $C$. Let $C_1, C_2 \subseteq
C$ with $C_1 \cup C_2 = C$ and $\bar{\Omega} \subseteq V(C_2)$. Let $\mathcal{D} =
\mathcal{D}_1 \cup \mathcal{D}_2$, where $\mathcal{D}_1 \cap \mathcal{D}_2 = \emptyset$ and
$V(A \cap B) \subseteq V(C_i)$ for $i = 1, 2$ and all $(A, B) \in \mathcal{D}_i$. Let $C^*$
be the graph with $V(C^*) = V(C_1 \cap C_2)$ and $E(C^*) = \emptyset$. Let* $$G_i = C^* \cup
\bigcup (A: (A, B) \in \mathcal{D}_i) \qquad (i = 1, 2).$$ ... *Then $(G_1, G_2)$ is a
separation of $(G, \Omega)$, $G_1 \cap G_2 = C^*$, $V(G_1) \cap V(C) = V(C_1)$, and $V(G_2)
\cap V(C) = V(C_2)$." -/
theorem theorem_11_8_proof {S : Society α β} {D_set D₁ D₂ : Set (Graph α β × Graph α β)}
    (hD : IsConsolidation S D_set) {C₁ C₂ : Graph α (Sym2 α)}
    (hC₁ : C₁ ≤ consolidationCore S D_set) (hC₂ : C₂ ≤ consolidationCore S D_set)
    (_hC_union : subgraphUnion (consolidationCore S D_set) C₁ C₂ = consolidationCore S D_set)
    (hΩ : S.Ω.bar ⊆ V(C₂)) (hD_union : D₁ ∪ D₂ = D_set) (hD_disj : Disjoint D₁ D₂)
    (hD₁ : ∀ ⦃A B : Graph α β⦄, (A, B) ∈ D₁ → V(A) ∩ V(B) ⊆ V(C₁))
    (hD₂ : ∀ ⦃A B : Graph α β⦄, (A, B) ∈ D₂ → V(A) ∩ V(B) ⊆ V(C₂)) :
    let C := consolidationCore S D_set
    let C_star : Graph α β := (S.G.induce (V(C₁) ∩ V(C₂))).restrict ∅
    let G₁ : Graph α β := subgraphUnion S.G C_star (subgraphSUnion S.G (Prod.fst '' D₁))
    let G₂ : Graph α β := subgraphUnion S.G C_star (subgraphSUnion S.G (Prod.fst '' D₂))
    S.IsSocietySeparation G₁ G₂ ∧ subgraphInter S.G G₁ G₂ = C_star ∧
    V(G₁) ∩ V(C) = V(C₁) ∧ V(G₂) ∩ V(C) = V(C₂) := by
  intro C C_star G₁ G₂
  have hD₁_sub : D₁ ⊆ D_set := hD_union ▸ subset_union_left
  have hD₂_sub : D₂ ⊆ D_set := hD_union ▸ subset_union_right
  have hC_star_le : C_star ≤ S.G := restrict_le.trans (S.G.induce_le
      (inter_subset_left.trans (hC₁.vertexSet_mono.trans (vertexSet_consolidationCore_subset S
        D_set))))
  have hE_C_star : E(C_star) = ∅ := by simp [C_star]
  have hU₁_all : ∀ P ∈ Prod.fst '' D₁, P ≤ S.G := fun P hP => hD.forall_fst_le P
    (image_mono hD₁_sub hP)
  have hU₂_all : ∀ P ∈ Prod.fst '' D₂, P ≤ S.G := fun P hP => hD.forall_fst_le P
    (image_mono hD₂_sub hP)
  have hU₁_le := subgraphSUnion_le hU₁_all; have hU₂_le := subgraphSUnion_le hU₂_all
  have hG₁_le := subgraphUnion_le hC_star_le hU₁_le; have hG₂_le := subgraphUnion_le hC_star_le
    hU₂_le
  have hV_union : V(G₁) ∪ V(G₂) = V(S.G) := by
    refine subset_antisymm (union_subset hG₁_le.vertexSet_mono hG₂_le.vertexSet_mono) fun v hv => ?_
    obtain ⟨A, B, hAB, hvA⟩ := hD.exists_mem_of_mem_vertexSet hv
    rcases (hD_union ▸ hAB : (A, B) ∈ D₁ ∪ D₂) with h1 | h2
    · exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨A, ⟨(A, B), h1, rfl⟩, hvA⟩))
    · exact Or.inr (Or.inr (mem_iUnion₂.mpr ⟨A, ⟨(A, B), h2, rfl⟩, hvA⟩))
  have hE_G₁ : E(G₁) = ⋃ P ∈ Prod.fst '' D₁, E(P) := by
    rw [edgeSet_subgraphUnion hC_star_le hU₁_le, hE_C_star, empty_union,
      edgeSet_subgraphSUnion hU₁_all]
  have hE_G₂ : E(G₂) = ⋃ P ∈ Prod.fst '' D₂, E(P) := by
    rw [edgeSet_subgraphUnion hC_star_le hU₂_le, hE_C_star, empty_union,
      edgeSet_subgraphSUnion hU₂_all]
  have hE_union : E(G₁) ∪ E(G₂) = E(S.G) := by
    refine subset_antisymm (union_subset hG₁_le.edgeSet_mono hG₂_le.edgeSet_mono) fun e he => ?_
    obtain ⟨A, B, hAB, heA⟩ := hD.exists_mem_of_mem_edgeSet he
    rcases (hD_union ▸ hAB : (A, B) ∈ D₁ ∪ D₂) with h1 | h2
    · left; rw [hE_G₁, mem_iUnion₂]; exact ⟨A, ⟨(A, B), h1, rfl⟩, heA⟩
    · right; rw [hE_G₂, mem_iUnion₂]; exact ⟨A, ⟨(A, B), h2, rfl⟩, heA⟩
  have hV_inter : V(G₁) ∩ V(G₂) = V(C_star) := by
    refine subset_antisymm ?_ (subset_inter subset_union_left subset_union_left)
    rintro v ⟨hv_star | hvU₁, hv_star | hvU₂⟩
    · exact hv_star
    · exact hv_star
    · exact hv_star
    · obtain ⟨A₁, ⟨⟨A₁', B₁⟩, h1, rfl⟩, hvA₁⟩ := mem_iUnion₂.mp hvU₁
      obtain ⟨A₂, ⟨⟨A₂', B₂⟩, h2, rfl⟩, hvA₂⟩ := mem_iUnion₂.mp hvU₂
      have hne : (A₁', B₁) ≠ (A₂', B₂) := fun heq => disjoint_left.mp hD_disj h1 (heq ▸ h2)
      exact ⟨hD₁ h1 ⟨hvA₁, (hD.left_le_right (hD₂_sub h2) (hD₁_sub h1) hne.symm).vertexSet_mono
        hvA₂⟩,
        hD₂ h2 ⟨hvA₂, (hD.left_le_right (hD₁_sub h1) (hD₂_sub h2) hne).vertexSet_mono hvA₁⟩⟩
  have hE_disj : Disjoint E(G₁) E(G₂) := by
    rw [hE_G₁, hE_G₂, disjoint_left]; intro e he₁ he₂
    obtain ⟨A₁, ⟨⟨A₁', B₁⟩, h1, rfl⟩, heA₁⟩ := mem_iUnion₂.mp he₁
    obtain ⟨A₂, ⟨⟨A₂', B₂⟩, h2, rfl⟩, heA₂⟩ := mem_iUnion₂.mp he₂
    have hne : (A₁', B₁) ≠ (A₂', B₂) := fun heq => disjoint_left.mp hD_disj h1 (heq ▸ h2)
    exact disjoint_left.mp (hD.disjoint_edges_of_ne (hD₁_sub h1) (hD₂_sub h2) hne) heA₁ heA₂
  have hG_inter : subgraphInter S.G G₁ G₂ = C_star := by
    refine (Compatible.of_le_le (subgraphInter_le hG₁_le) hC_star_le).ext ?_ ?_
    · rw [vertexSet_subgraphInter, hV_inter]
    · rw [edgeSet_subgraphInter hG₁_le hG₂_le, disjoint_iff_inter_eq_empty.mp hE_disj, hE_C_star]
  have hX₁_sub : V(G₁) ∩ V(C) ⊆ V(C₁) := by
    rintro v ⟨hv_star | hvU₁, hvC⟩
    · exact hv_star.1
    · obtain ⟨A, ⟨⟨A', B⟩, h1, rfl⟩, hvA⟩ := mem_iUnion₂.mp hvU₁
      exact hD₁ h1 ⟨hvA, vertexSet_consolidationCore_subset_right (hD₁_sub h1) hvC⟩
  have hX₂_sub : V(G₂) ∩ V(C) ⊆ V(C₂) := by
    rintro v ⟨hv_star | hvU₂, hvC⟩
    · exact hv_star.2
    · obtain ⟨A, ⟨⟨A', B⟩, h2, rfl⟩, hvA⟩ := mem_iUnion₂.mp hvU₂
      exact hD₂ h2 ⟨hvA, vertexSet_consolidationCore_subset_right (hD₂_sub h2) hvC⟩
  have hX₁_eq : V(G₁) ∩ V(C) = V(C₁) := by
    refine subset_antisymm hX₁_sub fun v hvC₁ => ?_
    have hvC : v ∈ V(C) := hC₁.vertexSet_mono hvC₁
    rcases (hV_union ▸ vertexSet_consolidationCore_subset S D_set hvC : v ∈ V(G₁) ∪ V(G₂)) with
      hvG₁ | hvG₂
    · exact ⟨hvG₁, hvC⟩
    · have hv_star : v ∈ V(C_star) := ⟨hvC₁, hX₂_sub ⟨hvG₂, hvC⟩⟩
      rw [← hV_inter] at hv_star; exact ⟨hv_star.1, hvC⟩
  have hX₂_eq : V(G₂) ∩ V(C) = V(C₂) := by
    refine subset_antisymm hX₂_sub fun v hvC₂ => ?_
    have hvC : v ∈ V(C) := hC₂.vertexSet_mono hvC₂
    rcases (hV_union ▸ vertexSet_consolidationCore_subset S D_set hvC : v ∈ V(G₁) ∪ V(G₂)) with
      hvG₁ | hvG₂
    · have hv_star : v ∈ V(C_star) := ⟨hX₁_sub ⟨hvG₁, hvC⟩, hvC₂⟩
      rw [← hV_inter] at hv_star; exact ⟨hv_star.2, hvC⟩
    · exact ⟨hvG₂, hvC⟩
  exact ⟨⟨⟨hG₁_le, hG₂_le, hV_union, hE_union, hE_disj⟩, hΩ.trans (hX₂_eq ▸ inter_subset_left)⟩,
    hG_inter, hX₁_eq, hX₂_eq⟩

/-! ## Minimal `k`-separations of societies -/

/-- If a society `S` has a `k`-separation, it has a `k`-separation `(C₁, C₂)` minimizing `|V(C₁)|`
and, subject to that, minimizing `|E(C₁)|`. -/
theorem exists_minimal_kSeparation {S : Society α γ} {k : ℕ} (hex : ∃ C₁ C₂ : Graph α γ,
  S.IsKSeparation k C₁ C₂) :
    ∃ C₁ C₂ : Graph α γ, S.IsKSeparation k C₁ C₂ ∧
      (∀ C₁' C₂' : Graph α γ, S.IsKSeparation k C₁' C₂' → V(C₁).ncard ≤ V(C₁').ncard) ∧
      (∀ C₁' C₂' : Graph α γ, S.IsKSeparation k C₁' C₂' →
        V(C₁').ncard = V(C₁).ncard → E(C₁).ncard ≤ E(C₁').ncard) := by
  classical
  let N_E := E(S.G).ncard + 1
  have hex_wt : ∃ m : ℕ, ∃ C₁ C₂ : Graph α γ, S.IsKSeparation k C₁ C₂
    ∧ V(C₁).ncard * N_E + E(C₁).ncard = m := by
    rcases hex with ⟨C₁, C₂, hsep⟩; exact ⟨V(C₁).ncard * N_E + E(C₁).ncard, C₁, C₂, hsep, rfl⟩
  obtain ⟨C₁, C₂, hsep, hm₀⟩ := Nat.find_spec hex_wt
  have hmin_wt : ∀ C₁' C₂' : Graph α γ, S.IsKSeparation k C₁' C₂' →
      V(C₁).ncard * N_E + E(C₁).ncard ≤ V(C₁').ncard * N_E + E(C₁').ncard := by
    intro C₁' C₂' hsep'; rw [hm₀]; exact Nat.find_le ⟨C₁', C₂', hsep', rfl⟩
  refine ⟨C₁, C₂, hsep, ?_, fun C₁' C₂' hsep' hV_eq => ?_⟩
  · intro C₁' C₂' hsep'; by_contra! hlt
    have hlt' : V(C₁').ncard + 1 ≤ V(C₁).ncard := hlt
    have hE_lt : E(C₁').ncard < N_E := Nat.lt_succ_of_le (ncard_le_ncard hsep'.1.1.1.edgeSet_mono
      S.finite_E)
    have h1 : V(C₁').ncard * N_E + E(C₁').ncard < (V(C₁').ncard + 1) * N_E := by
      rw [Nat.add_one_mul]; omega
    have h2 : (V(C₁').ncard + 1) * N_E ≤ V(C₁).ncard * N_E := Nat.mul_le_mul_right N_E hlt'
    have h3 := hmin_wt C₁' C₂' hsep'; omega
  · have h3 := hmin_wt C₁' C₂' hsep'; rw [hV_eq] at h3; omega

/-- In a `k`-separation `(C₁, C₂)` of `S` minimizing `|E(C₁)|` for its `|V(C₁)|`, no edge of `C₁`
has both ends in `V(C₂)`. -/
theorem minimal_kSeparation_no_edge_in_right {S : Society α γ} {k : ℕ}
    {C₁ C₂ : Graph α γ} (hsep : S.IsKSeparation k C₁ C₂)
    (hminE : ∀ C₁' C₂' : Graph α γ, S.IsKSeparation k C₁' C₂' →
      V(C₁').ncard = V(C₁).ncard → E(C₁).ncard ≤ E(C₁').ncard)
    {e : γ} {x y : α} (hlink : C₁.IsLink e x y) (hx : x ∈ V(C₂)) (hy : y ∈ V(C₂)) : False := by
  have hC₁_le : C₁ ≤ S.G := hsep.1.1.1; have hC₂_le : C₂ ≤ S.G := hsep.1.1.2.1
  let C₁' : Graph α γ := C₁.restrict (E(C₁) \ {e})
  let C₂' : Graph α γ := (S.G.induce V(C₂)).restrict (E(C₂) ∪ {e})
  have hC₁'_le : C₁' ≤ S.G := restrict_le.trans hC₁_le
  have hC₂'_le : C₂' ≤ S.G := restrict_le.trans (S.G.induce_le hC₂_le.vertexSet_mono)
  have hE₁' : E(C₁') = E(C₁) \ {e} := by
    change E(C₁.restrict (E(C₁) \ {e})) = E(C₁) \ {e}; rw [edgeSet_restrict, inter_eq_right]; exact
      sdiff_subset
  have hE₂' : E(C₂') = E(C₂) ∪ {e} := by
    change E((S.G.induce V(C₂)).restrict (E(C₂) ∪ {e})) = E(C₂) ∪ {e}
    rw [edgeSet_restrict, inter_eq_right]; rintro f (hf | rfl)
    · obtain ⟨u, v, huv⟩ := C₂.exists_isLink_of_mem_edgeSet hf
      exact ⟨u, v, huv.mono hC₂_le, huv.left_mem, huv.right_mem⟩
    · exact ⟨x, y, hlink.mono hC₁_le, hx, hy⟩
  have he_C₁ : e ∈ E(C₁) := hlink.edge_mem
  have hE_union' : E(C₁') ∪ E(C₂') = E(S.G) := by
    rw [hE₁', hE₂']; ext f; simp only [mem_union, mem_sdiff, mem_singleton_iff]
    refine ⟨?_, fun hfG => ?_⟩
    · rintro (⟨hf₁, _⟩ | hf₂ | rfl)
      · exact hC₁_le.edgeSet_mono hf₁
      · exact hC₂_le.edgeSet_mono hf₂
      · exact hC₁_le.edgeSet_mono he_C₁
    · by_cases hfe : f = e
      · exact Or.inr (Or.inr hfe)
      · rcases (hsep.1.1.2.2.2.1.symm ▸ hfG : f ∈ E(C₁) ∪ E(C₂)) with hf₁ | hf₂
        · exact Or.inl ⟨hf₁, hfe⟩
        · exact Or.inr (Or.inl hf₂)
  have hE_disj' : Disjoint E(C₁') E(C₂') := by
    rw [hE₁', hE₂', disjoint_left]; rintro f ⟨hf₁, hfe⟩ (hf₂ | rfl)
    · exact disjoint_left.mp hsep.1.1.2.2.2.2 hf₁ hf₂
    · exact hfe rfl
  have hsep' : S.IsKSeparation k C₁' C₂' :=
    ⟨⟨⟨hC₁'_le, hC₂'_le, hsep.1.1.2.2.1, hE_union', hE_disj'⟩, hsep.1.2⟩, hsep.2.1, hsep.2.2⟩
  have hle_E := hminE C₁' C₂' hsep' rfl
  have hlt_E : E(C₁').ncard < E(C₁).ncard := by
    rw [hE₁']; exact ncard_lt_ncard ⟨sdiff_subset, fun hsub => (hsub he_C₁).2 rfl⟩
      (S.finite_E.subset hC₁_le.edgeSet_mono)
  omega

/-- In a `k`-separation `(C₁, C₂)` of `S` minimizing `|V(C₁)|`, every pair of distinct vertices
`u, v ∈ V(C₁) ∩ V(C₂)` is joined by a path in `C₁` with no internal vertex in `V(C₂)`. -/
theorem minimal_kSeparation_exists_path {S : Society α γ} {k : ℕ}
    {C₁ C₂ : Graph α γ} (hsep : S.IsKSeparation k C₁ C₂)
    (hminV : ∀ C₁' C₂' : Graph α γ, S.IsKSeparation k C₁' C₂' → V(C₁).ncard ≤ V(C₁').ncard)
    {u v : α} (hu : u ∈ V(C₁) ∩ V(C₂)) (hv : v ∈ V(C₁) ∩ V(C₂)) :
    ∃ P : Graph α γ, IsGraphPathWithEnds C₁ P u v ∧ Disjoint (V(P) \ {u, v}) V(C₂) := by
  have hC₁_le : C₁ ≤ S.G := hsep.1.1.1; have hC₂_le : C₂ ≤ S.G := hsep.1.1.2.1
  have hdiff_ne : (V(C₁) \ V(C₂)).Nonempty := by
    by_contra h_empty; rw [not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at h_empty
    exact hsep.2.2 ((union_eq_right.mpr h_empty).symm.trans hsep.1.1.2.2.1)
  obtain ⟨w₀, hw₀⟩ := hdiff_ne
  let H := deleteVertices C₁ V(C₂); have hw₀H : w₀ ∈ V(H) := hw₀
  let K₀ := reachableComponent H w₀; let U₀ := V(K₀)
  have hU₀_sub : U₀ ⊆ V(C₁) \ V(C₂) := (reachableComponent_le H w₀).vertexSet_mono
  let N₀ := {z ∈ V(C₁) ∩ V(C₂) | ∃ x ∈ U₀, C₁.Adj x z}
  let E₁_star := {e ∈ E(C₁) | ∃ x ∈ U₀, C₁.Inc e x}; let E₂_star := E(S.G) \ E₁_star
  let C₁_star := (S.G.induce (U₀ ∪ N₀)).restrict E₁_star
  let C₂_star := (S.G.induce (V(S.G) \ U₀)).restrict E₂_star
  have hV₁_star_sub_C₁ : U₀ ∪ N₀ ⊆ V(C₁) := union_subset (hU₀_sub.trans sdiff_subset) (fun _ hz
    => hz.1.1)
  have hC₁_star_le : C₁_star ≤ S.G :=
    restrict_le.trans (S.G.induce_le (hV₁_star_sub_C₁.trans hC₁_le.vertexSet_mono))
  have hC₂_star_le : C₂_star ≤ S.G := restrict_le.trans (S.G.induce_le sdiff_subset)
  have hE₁_star_eq : E(C₁_star) = E₁_star := by
    change E((S.G.induce (U₀ ∪ N₀)).restrict E₁_star) = E₁_star
    rw [edgeSet_restrict, inter_eq_right]; rintro e ⟨heC₁, x, hxU₀, y, hlink⟩
    refine ⟨x, y, hlink.mono hC₁_le, Or.inl hxU₀, ?_⟩
    by_cases hyC₂ : y ∈ V(C₂)
    · exact Or.inr ⟨⟨hlink.right_mem, hyC₂⟩, x, hxU₀, e, hlink⟩
    · left
      have hlinkH : H.IsLink e x y := (deleteVertices_isLink C₁ V(C₂)).mpr ⟨hlink,
        (hU₀_sub hxU₀).2, hyC₂⟩
      exact (mem_graphComponent_iff_of_isLink (isGraphComponent_reachableComponent hw₀H) hlinkH).mp
        hxU₀
  have hE₂_star_eq : E(C₂_star) = E₂_star := by
    change E((S.G.induce (V(S.G) \ U₀)).restrict E₂_star) = E₂_star
    rw [edgeSet_restrict, inter_eq_right]; rintro e ⟨heG, he_not⟩
    obtain ⟨x, y, hxy⟩ := S.G.exists_isLink_of_mem_edgeSet heG
    have hnot_U₀ : ∀ z, S.G.Inc e z → z ∉ U₀ := by
      rintro z ⟨w, hzw⟩ hzU₀
      have he_not_C₂ : e ∉ E(C₂) := fun heC₂ => (hU₀_sub hzU₀).2 ((hC₂_le.isLink_iff heC₂).mpr
        hzw).left_mem
      have heC₁ : e ∈ E(C₁) := (hsep.1.1.2.2.2.1.symm ▸ heG).resolve_right he_not_C₂
      exact he_not ⟨heC₁, z, hzU₀, w, (hC₁_le.isLink_iff heC₁).mpr hzw⟩
    exact ⟨x, y, hxy, ⟨hxy.left_mem, hnot_U₀ x ⟨y, hxy⟩⟩, ⟨hxy.right_mem, hnot_U₀ y ⟨x, hxy.symm⟩⟩⟩
  have hV_star_union : V(C₁_star) ∪ V(C₂_star) = V(S.G) := by
    refine subset_antisymm (union_subset hC₁_star_le.vertexSet_mono hC₂_star_le.vertexSet_mono) fun
      z hzG => ?_
    by_cases hzU₀ : z ∈ U₀; exacts [Or.inl (Or.inl hzU₀), Or.inr ⟨hzG, hzU₀⟩]
  have hE_star_union : E(C₁_star) ∪ E(C₂_star) = E(S.G) := by
    rw [hE₁_star_eq, hE₂_star_eq]; exact union_sdiff_cancel fun e he => hC₁_le.edgeSet_mono he.1
  have hE_star_disj : Disjoint E(C₁_star) E(C₂_star) := by
    rw [hE₁_star_eq, hE₂_star_eq]; exact disjoint_sdiff_right
  have hΩ_star : S.Ω.bar ⊆ V(C₂_star) :=
    fun z hzΩ => ⟨S.bar_subset hzΩ, fun hzU₀ => (hU₀_sub hzU₀).2 (hsep.1.2 hzΩ)⟩
  have hV_star_inter : V(C₁_star) ∩ V(C₂_star) = N₀ := by
    ext z; simp only [C₁_star, C₂_star, mem_inter_iff]
    exact ⟨fun ⟨hz_or, _, hz_not_U₀⟩ => hz_or.resolve_left hz_not_U₀,
      fun hzN₀ => ⟨Or.inr hzN₀, hC₁_le.vertexSet_mono hzN₀.1.1, fun hzU₀ =>
        (hU₀_sub hzU₀).2 hzN₀.1.2⟩⟩
  have hcard_star : (V(C₁_star) ∩ V(C₂_star)).ncard ≤ k := by
    rw [hV_star_inter]
    exact (ncard_le_ncard (s := N₀) (fun _ hz => hz.1)
      (S.finite_V.subset (inter_subset_left.trans hC₁_le.vertexSet_mono))).trans hsep.2.1
  have hV₂_star_ne : V(C₂_star) ≠ V(S.G) := fun heq =>
    (heq.symm ▸ hC₁_le.vertexSet_mono hw₀.1 : w₀ ∈ V(C₂_star)).2 (self_mem_reachableComponent hw₀H)
  have hsep_star : S.IsKSeparation k C₁_star C₂_star :=
    ⟨⟨⟨hC₁_star_le, hC₂_star_le, hV_star_union, hE_star_union, hE_star_disj⟩, hΩ_star⟩, hcard_star,
      hV₂_star_ne⟩
  have hV₁_eq : V(C₁_star) = V(C₁) := eq_of_subset_of_ncard_le hV₁_star_sub_C₁
    (hminV C₁_star C₂_star hsep_star)
      (S.finite_V.subset hC₁_le.vertexSet_mono)
  obtain ⟨x_u, hx_u, e_u, he_u⟩ := ((hV₁_eq ▸ hu.1).resolve_left fun h => (hU₀_sub h).2 hu.2).2
  obtain ⟨x_v, hx_v, e_v, he_v⟩ := ((hV₁_eq ▸ hv.1).resolve_left fun h => (hU₀_sub h).2 hv.2).2
  obtain ⟨W_K⟩ := (isGraphConnected_reachableComponent hw₀H).2 x_u hx_u x_v hx_v
  obtain ⟨W_mid, hs_mid, _⟩ :=
    exists_walk_up_of_le ((reachableComponent_le H w₀).trans (deleteVertices_le C₁ V(C₂))) W_K
  let W_full : GraphWalk C₁ u v :=
    (GraphWalk.cons he_u.symm W_mid).append (GraphWalk.cons he_v (GraphWalk.nil hv.1))
  obtain ⟨P, hP, hVP_sub, _⟩ := exists_isGraphPathWithEnds_of_walk W_full
  refine ⟨P, hP, disjoint_left.mpr fun z ⟨hzP, hz_not_uv⟩ hzC₂ => ?_⟩
  rcases (GraphWalk.mem_support_append (GraphWalk.cons he_u.symm W_mid)
    (GraphWalk.cons he_v (GraphWalk.nil hv.1))).mp (hVP_sub hzP) with hz1 | hz2
  · rcases List.mem_cons.mp hz1 with rfl | hz_mid
    · exact hz_not_uv (by simp)
    · rw [hs_mid] at hz_mid; exact (hU₀_sub (W_K.mem_vertexSet_of_mem_support hz_mid)).2 hzC₂
  · simp only [GraphWalk.support_cons, GraphWalk.support_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hz2
    rcases hz2 with rfl | rfl; exacts [(hU₀_sub hx_v).2 hzC₂, hz_not_uv (by simp)]

/-! ## (11.9): Minimality of core implies 4-connectivity -/

/-- Walk-lifting helper for (11.9) Claim (1). -/
private theorem lift_walk_claim_1 {S : Society α β} {D_set D₁ D₂ : Set (Graph α β × Graph α β)}
    (hD : IsConsolidation S D_set) {C₁ C₂ : Graph α (Sym2 α)} (hC₁ : C₁ ≤ consolidationCore S D_set)
    (hno_edge : ∀ e x y, C₁.IsLink e x y → x ∈ V(C₂) → y ∈ V(C₂) → False) (hD_union : D₁ ∪ D₂
      = D_set)
    (hD₂ : ∀ ⦃A B : Graph α β⦄, (A, B) ∈ D₂ → V(A) ∩ V(B) ⊆ V(C₂)) {G₁ G₂ : Graph α β}
      (hC₁_sub_G₁ : V(C₁) ⊆ V(G₁))
    (hA_le_G₁ : ∀ ⦃A B : Graph α β⦄, (A, B) ∈ D₁ → A ≤ G₁)
    (hinter_sub_C : V(G₁) ∩ V(G₂) ⊆ V(consolidationCore S D_set))
    (hdiff_sub : V(C₁) \ V(C₂) ⊆ V(G₁) \ V(G₂)) {u v a b : α} (W_C : GraphWalk C₁ a b)
    (hsupp : ∀ z ∈ W_C.support, z ∈ (V(C₁) \ V(C₂)) ∪ {u, v}) :
    ∃ W_G : GraphWalk G₁ a b, ∀ z ∈ W_G.support, z ∈ (V(G₁) \ V(G₂)) ∪ {u, v} := by
  induction W_C with
  | @nil x hx =>
    refine ⟨.nil (hC₁_sub_G₁ hx), fun z hz => ?_⟩
    simp only [GraphWalk.support_nil, List.mem_singleton] at hz; subst hz
    exact (hsupp z (by simp)).imp_left fun h => hdiff_sub h
  | @cons x y z e hlink W_rest ih =>
    have hx_in := (hsupp x (by simp)).imp_left fun h => hdiff_sub h
    have hy_in := (hsupp y (List.mem_cons_of_mem _ W_rest.start_mem_support)).imp_left fun h
      => hdiff_sub h
    obtain ⟨W_rest_G, hW_rest_G⟩ := ih fun w hw => hsupp w (List.mem_cons_of_mem _ hw)
    obtain ⟨hxy, _, _, _, ⟨A, B⟩, hAB, hx_AB, hy_AB⟩ := hlink.mono hC₁
    have hAB_D₁ : (A, B) ∈ D₁ := (hD_union.symm ▸ hAB).resolve_right fun hAB₂ =>
      hno_edge e x y hlink (hD₂ hAB₂ hx_AB) (hD₂ hAB₂ hy_AB)
    have hAG₁ : A ≤ G₁ := hA_le_G₁ hAB_D₁
    obtain ⟨P_xy, ⟨hP_xy_A, W_xy, _, hVP_xy, _⟩, hdisj_xy⟩ := hD.exists_path hAB x hx_AB y hy_AB hxy
    obtain ⟨W_xy_G, hs_xy, _⟩ := exists_walk_up_of_le (hP_xy_A.trans hAG₁) W_xy
    refine ⟨W_xy_G.append W_rest_G, fun w hw => ?_⟩
    rcases (GraphWalk.mem_support_append W_xy_G W_rest_G).mp hw with hw_xy | hw_rest
    · rw [hs_xy] at hw_xy; have hwP : w ∈ V(P_xy) := by rw [hVP_xy]; exact hw_xy
      by_cases hw_end : w ∈ ({x, y} : Set α)
      · rcases hw_end with rfl | rfl; exacts [hx_in, hy_in]
      · left; have hwG₁ : w ∈ V(G₁) := (hP_xy_A.trans hAG₁).vertexSet_mono hwP
        exact ⟨hwG₁, fun hwG₂ => disjoint_left.mp hdisj_xy ⟨hwP, hw_end⟩
          (vertexSet_consolidationCore_subset_right hAB (hinter_sub_C ⟨hwG₁, hwG₂⟩))⟩
    · exact hW_rest_G w hw_rest

/-- **Graph Minors IX, (11.9)** (page 71):
"Let $\mathcal{D}$ be a consolidation of $(G, \Omega)$ chosen so that its core $C$ has as few
vertices as possible. Then $(C, \Omega)$ is 4-connected." -/
theorem theorem_11_9_proof (S : Society α β) (D_set : Set (Graph α β × Graph α β))
  (hD : IsConsolidation S D_set)
    (hmin : ∀ D' : Set (Graph α β × Graph α β), IsConsolidation S D' →
      V(consolidationCore S D_set).ncard ≤ V(consolidationCore S D').ncard) :
    (consolidationCoreSociety S D_set hD).IsKConnected 4 := by
  classical
  let CS := consolidationCoreSociety S D_set hD; let C := consolidationCore S D_set
  intro k' hk' C₁₀ C₂₀ hsep₀
  obtain ⟨C₁, C₂, hsep, hminV, hminE⟩ :=
    exists_minimal_kSeparation (k := 3) ⟨C₁₀, C₂₀, hsep₀.1, hsep₀.2.1.trans (by omega), hsep₀.2.2⟩
  have hC₁_le : C₁ ≤ C := hsep.1.1.1; have hC₂_le : C₂ ≤ C := hsep.1.1.2.1
  let D₁ : Set (Graph α β × Graph α β) := {p ∈ D_set | V(p.1) ∩ V(p.2) ⊆ V(C₁)}
  let D₂ : Set (Graph α β × Graph α β) := D_set \ D₁
  have hD_union : D₁ ∪ D₂ = D_set := union_sdiff_cancel (fun _ hp => hp.1)
  have hD_disj : Disjoint D₁ D₂ := disjoint_sdiff_right
  have hD₁_sub_C₁ : ∀ ⦃A B : Graph α β⦄, (A, B) ∈ D₁ → V(A) ∩ V(B) ⊆ V(C₁) := fun _ _ hp => hp.2
  have hD₂_sub_C₂ : ∀ ⦃A B : Graph α β⦄, (A, B) ∈ D₂ → V(A) ∩ V(B) ⊆ V(C₂) := by
    intro A B ⟨hAB, hnot₁⟩
    rcases not_subset.mp (fun h => hnot₁ ⟨hAB, h⟩) with ⟨v, hvAB, hv_not_C₁⟩
    have hvC : v ∈ V(C) := hD.inter_subset_consolidationCore hAB hvAB
    have hvC₂ : v ∈ V(C₂) := (hsep.1.1.2.2.1 ▸ hvC).resolve_left hv_not_C₁
    intro w hwAB; by_cases hwv : w = v
    · exact hwv ▸ hvC₂
    · have hlink_C : C.IsLink s(v, w) v w :=
        hD.consolidationCore_isLink_of_mem_inter hAB hvAB hwAB (Ne.symm hwv)
      rcases (hsep.1.1.2.2.2.1.symm ▸ hlink_C.edge_mem : s(v, w) ∈ E(C₁) ∪ E(C₂)) with he₁ | he₂
      · exact (hv_not_C₁ ((hC₁_le.isLink_iff he₁).mpr hlink_C).left_mem).elim
      · exact ((hC₂_le.isLink_iff he₂).mpr hlink_C).right_mem
  let C_star : Graph α β := (S.G.induce (V(C₁) ∩ V(C₂))).restrict ∅
  let G₁ : Graph α β := subgraphUnion S.G C_star (subgraphSUnion S.G (Prod.fst '' D₁))
  let G₂ : Graph α β := subgraphUnion S.G C_star (subgraphSUnion S.G (Prod.fst '' D₂))
  obtain ⟨hsep_G, hG_inter, hX₁_eq, hX₂_eq⟩ :=
    theorem_11_8_proof hD hC₁_le hC₂_le (IsGraphSeparation.subgraphUnion_eq hsep.1.1)
      hsep.1.2 hD_union hD_disj hD₁_sub_C₁ hD₂_sub_C₂
  have hV_G_inter : V(G₁) ∩ V(G₂) = V(C₁) ∩ V(C₂) := by
    rw [← vertexSet_subgraphInter S.G G₁ G₂, hG_inter]; rfl
  have hC_star_le : C_star ≤ S.G := restrict_le.trans (S.G.induce_le
      (inter_subset_left.trans (hC₁_le.vertexSet_mono.trans (vertexSet_consolidationCore_subset S
        D_set))))
  have hU₁_all : ∀ P ∈ Prod.fst '' D₁, P ≤ S.G := fun P hP =>
    hD.forall_fst_le P (image_mono (s := D₁) (fun _ hp => hp.1) hP)
  have hU₂_all : ∀ P ∈ Prod.fst '' D₂, P ≤ S.G := fun P hP => hD.forall_fst_le P
    (image_mono sdiff_subset hP)
  have hU₁_le := subgraphSUnion_le hU₁_all; have hU₂_le := subgraphSUnion_le hU₂_all
  have hA_le_G₁ : ∀ ⦃A B : Graph α β⦄, (A, B) ∈ D₁ → A ≤ G₁ := fun A B hAB =>
    (le_subgraphSUnion hU₁_all ⟨(A, B), hAB, rfl⟩).trans (le_subgraphUnion_right hC_star_le hU₁_le)
  have hA_le_G₂ : ∀ ⦃A B : Graph α β⦄, (A, B) ∈ D₂ → A ≤ G₂ := fun A B hAB =>
    (le_subgraphSUnion hU₂_all ⟨(A, B), hAB, rfl⟩).trans (le_subgraphUnion_right hC_star_le hU₂_le)
  have hclaim1 : ∀ u ∈ V(G₁) ∩ V(G₂), ∀ v ∈ V(G₁) ∩ V(G₂), u ≠ v →
      ∃ P : Graph α β, IsGraphPathWithEnds G₁ P u v ∧ Disjoint (V(P) \ {u, v}) V(G₂) := by
    intro u hu v hv _
    obtain ⟨P_C, ⟨hP_C_le, W_C, _, hVP_C, _⟩, hdisj_C⟩ :=
      minimal_kSeparation_exists_path hsep hminV (hV_G_inter ▸ hu) (hV_G_inter ▸ hv)
    obtain ⟨W_C₁, hs_C₁, _⟩ := exists_walk_up_of_le hP_C_le W_C
    have hC₁_sub_G₁ : V(C₁) ⊆ V(G₁) := hX₁_eq ▸ inter_subset_left
    have hinter_sub_C : V(G₁) ∩ V(G₂) ⊆ V(C) := hV_G_inter ▸ inter_subset_left.trans
      hC₁_le.vertexSet_mono
    have hdiff_sub : V(C₁) \ V(C₂) ⊆ V(G₁) \ V(G₂) := fun z ⟨hzC₁, hz_not_C₂⟩ =>
      ⟨hC₁_sub_G₁ hzC₁, fun hzG₂ => hz_not_C₂ (hX₂_eq ▸ ⟨hzG₂, hC₁_le.vertexSet_mono hzC₁⟩)⟩
    have hsupp_C₁ : ∀ z ∈ W_C₁.support, z ∈ (V(C₁) \ V(C₂)) ∪ {u, v} := by
      intro z hz; rw [hs_C₁] at hz; have hzP : z ∈ V(P_C) := by rw [hVP_C]; exact hz
      by_cases hz_uv : z ∈ ({u, v} : Set α)
      · exact Or.inr hz_uv
      · exact Or.inl ⟨hP_C_le.vertexSet_mono hzP, fun hzC₂ => disjoint_left.mp hdisj_C ⟨hzP,
          hz_uv⟩ hzC₂⟩
    obtain ⟨W_G, hW_G⟩ := lift_walk_claim_1 hD hC₁_le
      (fun e x y hl hx hy => minimal_kSeparation_no_edge_in_right hsep hminE hl hx hy)
      hD_union hD₂_sub_C₂ hC₁_sub_G₁ hA_le_G₁ hinter_sub_C hdiff_sub W_C₁ hsupp_C₁
    obtain ⟨P, hP, hVP_sub, _⟩ := exists_isGraphPathWithEnds_of_walk W_G
    refine ⟨P, hP, disjoint_left.mpr fun z ⟨hzP, hz_not_uv⟩ hzG₂ => ?_⟩
    rcases hW_G z (hVP_sub hzP) with ⟨_, hz_not_G₂⟩ | hz_uv; exacts [hz_not_G₂ hzG₂, hz_not_uv
      hz_uv]
  have hG₁_le_B₂ : ∀ ⦃A₂ B₂ : Graph α β⦄, (A₂, B₂) ∈ D₂ → G₁ ≤ B₂ := by
    intro A₂ B₂ hAB₂; have hB₂_le : B₂ ≤ S.G := hD.right_le hAB₂.1
    rw [subgraphUnion_le_iff hC_star_le hU₁_le hB₂_le]; refine ⟨?_, ?_⟩
    · rw [(Compatible.of_le_le hC_star_le hB₂_le).le_iff]
      exact ⟨(inter_subset_left.trans hC₁_le.vertexSet_mono).trans
        (vertexSet_consolidationCore_subset_right hAB₂.1), by simp [C_star]⟩
    · rw [(Compatible.of_le_le hU₁_le hB₂_le).le_iff, vertexSet_subgraphSUnion,
        edgeSet_subgraphSUnion hU₁_all]
      refine ⟨iUnion₂_subset ?_, iUnion₂_subset ?_⟩ <;>
      · rintro A ⟨⟨A₁, B₁⟩, hAB₁, rfl⟩
        have hne : (A₁, B₁) ≠ (A₂, B₂) := fun heq => disjoint_left.mp hD_disj hAB₁ (heq ▸ hAB₂)
        first
        | exact (hD.left_le_right hAB₁.1 hAB₂.1 hne).vertexSet_mono
        | exact (hD.left_le_right hAB₁.1 hAB₂.1 hne).edgeSet_mono
  let D' : Set (Graph α β × Graph α β) := D₂ ∪ {(G₁, G₂)}
  have hD'_all : ∀ P ∈ Prod.fst '' D', P ≤ S.G := by
    rintro P ⟨⟨A, B⟩, hAB₂ | hG₁₂, rfl⟩
    · exact hD.left_le hAB₂.1
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (mem_singleton_iff.mp hG₁₂); exact hsep_G.1.1
  have hD' : IsConsolidation S D' := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rintro A B (hAB₂ | hG₁₂)
      · exact hD.isSocietySeparation hAB₂.1
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (mem_singleton_iff.mp hG₁₂); exact hsep_G
    · rintro A B (hAB₂ | hG₁₂)
      · exact hD.order_le_three hAB₂.1
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (mem_singleton_iff.mp hG₁₂); rw [hV_G_inter]; exact
        hsep.2.1
    · rintro A B A' B' (h1 | h1) (h2 | h2) hne
      · exact hD.left_le_right h1.1 h2.1 hne
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (mem_singleton_iff.mp h2); exact hA_le_G₂ h1
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (mem_singleton_iff.mp h1); exact hG₁_le_B₂ h2
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (mem_singleton_iff.mp h1)
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (mem_singleton_iff.mp h2); exact (hne rfl).elim
    · refine (Compatible.of_le_le (subgraphSUnion_le hD'_all) le_rfl).ext
        (subset_antisymm (subgraphSUnion_le hD'_all).vertexSet_mono fun v hv => ?_)
        (subset_antisymm (subgraphSUnion_le hD'_all).edgeSet_mono fun e he => ?_)
      · rw [vertexSet_subgraphSUnion, mem_iUnion₂]
        rcases (hsep_G.1.2.2.1.symm ▸ hv : v ∈ V(G₁) ∪ V(G₂)) with hvG₁ | (hv_star | hvU₂)
        · exact ⟨G₁, ⟨(G₁, G₂), Or.inr rfl, rfl⟩, hvG₁⟩
        · exact ⟨G₁, ⟨(G₁, G₂), Or.inr rfl, rfl⟩, Or.inl hv_star⟩
        · obtain ⟨A, ⟨⟨A', B'⟩, hAB₂, rfl⟩, hvA⟩ := mem_iUnion₂.mp hvU₂
          exact ⟨A', ⟨(A', B'), Or.inl hAB₂, rfl⟩, hvA⟩
      · rw [edgeSet_subgraphSUnion hD'_all, mem_iUnion₂]
        rcases (hsep_G.1.2.2.2.1.symm ▸ he : e ∈ E(G₁) ∪ E(G₂)) with heG₁ | heG₂
        · exact ⟨G₁, ⟨(G₁, G₂), Or.inr rfl, rfl⟩, heG₁⟩
        · rw [edgeSet_subgraphUnion hC_star_le hU₂_le, edgeSet_subgraphSUnion hU₂_all] at heG₂
          rcases heG₂ with he_star | heU₂
          · simp [C_star] at he_star
          · obtain ⟨A, ⟨⟨A', B'⟩, hAB₂, rfl⟩, heA⟩ := mem_iUnion₂.mp heU₂
            exact ⟨A', ⟨(A', B'), Or.inl hAB₂, rfl⟩, heA⟩
    · rintro A B (hAB₂ | hG₁₂)
      · exact hD.exists_path hAB₂.1
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (mem_singleton_iff.mp hG₁₂); exact hclaim1
  let C' := consolidationCore S D'
  have hC'_sub_C : V(C') ⊆ V(C) := by
    intro v hvC'
    rcases (vertexSet_consolidationCore_subset_right (Or.inr (mem_singleton (G₁, G₂))) hvC' :
      v ∈ V(C_star) ∪ ⋃ P ∈ Prod.fst '' D₂, V(P)) with hv_star | hvU₂
    · exact hC₁_le.vertexSet_mono hv_star.1
    · obtain ⟨A, ⟨⟨A', B'⟩, hAB₂, rfl⟩, hvA⟩ := mem_iUnion₂.mp hvU₂
      exact hD.inter_subset_consolidationCore hAB₂.1 ⟨hvA, vertexSet_consolidationCore_subset_right
        (Or.inl hAB₂) hvC'⟩
  have hdiff_ne : (V(C₁) \ V(C₂)).Nonempty := by
    by_contra h_empty; rw [not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at h_empty
    exact hsep.2.2 ((union_eq_right.mpr h_empty).symm.trans hsep.1.1.2.2.1)
  obtain ⟨v₀, hv₀C₁, hv₀_not_C₂⟩ := hdiff_ne; have hv₀C : v₀ ∈ V(C) := hC₁_le.vertexSet_mono hv₀C₁
  have hv₀_not_C' : v₀ ∉ V(C') := fun hv₀C' => hv₀_not_C₂ (hX₂_eq ▸
    ⟨vertexSet_consolidationCore_subset_right
      (Or.inr (mem_singleton (G₁, G₂))) hv₀C', hv₀C⟩)
  have hlt_card : V(consolidationCore S D').ncard < V(consolidationCore S D_set).ncard :=
    ncard_lt_ncard ⟨hC'_sub_C, fun hsub => hv₀_not_C' (hsub hv₀C)⟩
      (finite_vertexSet_consolidationCore S D_set)
  have hge_card := hmin D' hD'; omega

/-! ## (11.10): Transactions and patterns in a society and its consolidation core -/

/-- If `P` is a jump in `S.G` with distinct ends `a, b ∈ V(consolidationCore S D_set)` and no
internal vertex in `V(consolidationCore S D_set)`, then `a` and `b` are adjacent in
`consolidationCore S D_set`. -/
theorem consolidationCore_isLink_of_jump {S : Society α β}
    {D_set : Set (Graph α β × Graph α β)} (hD : IsConsolidation S D_set) {P : Graph α β} {a b : α}
    (hP : IsGraphPathWithEnds S.G P a b) (hab : a ≠ b)
    (ha : a ∈ V(consolidationCore S D_set)) (hb : b ∈ V(consolidationCore S D_set))
    (hjump : Disjoint (V(P) \ {a, b}) V(consolidationCore S D_set)) :
    (consolidationCore S D_set).IsLink s(a, b) a b := by
  rcases hP with ⟨hPG, W, hW, hVP, _⟩
  cases W with
  | nil _ => exact (hab rfl).elim
  | @cons _ w _ e₁ hlink₁ W_rest =>
    obtain ⟨A, B, hAB, he₁A⟩ := hD.exists_mem_of_mem_edgeSet (hlink₁.mono hPG).edge_mem
    have hlink₁A : A.IsLink e₁ a w := ((hD.left_le hAB).isLink_iff he₁A).mpr (hlink₁.mono hPG)
    have haB : a ∈ V(B) := vertexSet_consolidationCore_subset_right hAB ha
    have hbB : b ∈ V(B) := vertexSet_consolidationCore_subset_right hAB hb
    have hbA : b ∈ V(A) := by
      by_contra hb_not_A
      obtain ⟨W_rest_G, hs_rest, _⟩ := exists_walk_up_of_le hPG W_rest
      obtain ⟨z, hzW, hz_AB⟩ :=
        exists_mem_inter_of_graphWalk (hD.isSocietySeparation hAB).1 W_rest_G hlink₁A.right_mem hbB
      rw [hs_rest] at hzW
      have hzP : z ∈ V(P) := by rw [hVP]; exact List.mem_cons_of_mem _ hzW
      have hz_ne_a : z ≠ a := fun h => (List.nodup_cons.mp hW).1 (h ▸ hzW)
      have hz_ne_b : z ≠ b := fun h => hb_not_A (h ▸ hz_AB.1)
      exact disjoint_left.mp hjump ⟨hzP, by simp [hz_ne_a, hz_ne_b]⟩
        (hD.inter_subset_consolidationCore hAB hz_AB)
    exact hD.consolidationCore_isLink_of_mem_inter hAB ⟨hlink₁A.left_mem, haB⟩ ⟨hbA, hbB⟩ hab

/-- Every path `P` in `S.G` with ends `a, b ∈ V(consolidationCore S D_set)` induces a path `Q` in
`consolidationCore S D_set` with ends `a, b` and `V(Q) ⊆ V(P) ∩ V(consolidationCore S D_set)`. -/
theorem exists_core_path_of_path {S : Society α β}
    {D_set : Set (Graph α β × Graph α β)} (hD : IsConsolidation S D_set) {P : Graph α β} {a b : α}
    (hP : IsGraphPathWithEnds S.G P a b)
    (ha : a ∈ V(consolidationCore S D_set)) (hb : b ∈ V(consolidationCore S D_set)) : ∃ Q : Graph α
      (Sym2 α),
      IsGraphPathWithEnds (consolidationCore S D_set) Q a b ∧ V(Q) ⊆ V(P) ∩ V(consolidationCore S
        D_set) := by
  classical
  let C := consolidationCore S D_set
  have hwalk : ∀ (n : ℕ) {a' b' : α} {P' : Graph α β},
      IsGraphPathWithEnds S.G P' a' b' → V(P').ncard = n → a' ∈ V(C) → b' ∈ V(C) →
      ∃ W_C : GraphWalk C a' b', ∀ z ∈ W_C.support, z ∈ V(P') ∩ V(C) := by
    intro n; induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro a' b' P' hP' hcard ha' hb'
      by_cases hab' : a' = b'
      · subst hab'; refine ⟨.nil ha', fun z hz => ?_⟩
        simp only [GraphWalk.support_nil, List.mem_singleton] at hz; exact hz ▸ ⟨hP'.left_mem, ha'⟩
      · by_cases hhit : ∃ z ∈ V(P') \ {a', b'}, z ∈ V(C)
        · rcases hhit with ⟨z, ⟨hzP', hz_not_ab⟩, hzC⟩
          simp only [mem_insert_iff, mem_singleton_iff, not_or] at hz_not_ab
          obtain ⟨P₁, P₂, hP₁, hP₂, hpath₁, hpath₂, _, hinter, _⟩ := hP'.exists_split_at hzP'
          have hfin : V(P').Finite := hP'.vertexSet_finite
          have hb_not_P₁ : b' ∉ V(P₁) := fun hb₁ =>
            hz_not_ab.2 (mem_singleton_iff.mp (hinter ▸ ⟨hb₁, hpath₂.right_mem⟩)).symm
          have ha_not_P₂ : a' ∉ V(P₂) := fun ha₂ =>
            hz_not_ab.1 (mem_singleton_iff.mp (hinter ▸ ⟨hpath₁.left_mem, ha₂⟩)).symm
          have hlt₁ : V(P₁).ncard < n := hcard ▸
            ncard_lt_ncard ⟨hP₁.vertexSet_mono, fun hsub => hb_not_P₁ (hsub hP'.right_mem)⟩ hfin
          have hlt₂ : V(P₂).ncard < n := hcard ▸
            ncard_lt_ncard ⟨hP₂.vertexSet_mono, fun hsub => ha_not_P₂ (hsub hP'.left_mem)⟩ hfin
          obtain ⟨W₁, hW₁⟩ := ih V(P₁).ncard hlt₁ (hpath₁.mono hP'.le) rfl ha' hzC
          obtain ⟨W₂, hW₂⟩ := ih V(P₂).ncard hlt₂ (hpath₂.mono hP'.le) rfl hzC hb'
          refine ⟨W₁.append W₂, fun w hw => ?_⟩
          rcases (GraphWalk.mem_support_append W₁ W₂).mp hw with hw₁ | hw₂
          · exact ⟨hP₁.vertexSet_mono (hW₁ w hw₁).1, (hW₁ w hw₁).2⟩
          · exact ⟨hP₂.vertexSet_mono (hW₂ w hw₂).1, (hW₂ w hw₂).2⟩
        · have hjump : Disjoint (V(P') \ {a', b'}) V(C) := disjoint_left.mpr fun z hz1 hz2
          => hhit ⟨z, hz1, hz2⟩
          refine ⟨.cons (consolidationCore_isLink_of_jump hD hP' hab' ha' hb' hjump) (.nil hb'),
            fun z hz => ?_⟩
          simp only [GraphWalk.support_cons, GraphWalk.support_nil, List.mem_cons,
            List.not_mem_nil, or_false] at hz
          rcases hz with rfl | rfl; exacts [⟨hP'.left_mem, ha'⟩, ⟨hP'.right_mem, hb'⟩]
  obtain ⟨W_C, hW_C⟩ := hwalk V(P).ncard hP rfl ha hb
  obtain ⟨Q, hQ, hVQ, _⟩ := exists_isGraphPathWithEnds_of_walk W_C
  exact ⟨Q, hQ, fun z hz => hW_C z (hVQ hz)⟩

/-- Four-element cardinality bound: if `u₁ ≠ v₁`, `u₂ ≠ v₂`, and `Disjoint {u₁, v₁} {u₂, v₂}`, then
`{u₁, v₁, u₂, v₂}` cannot be contained in any finite set `X` with `X.ncard ≤ 3`. -/
private theorem not_subset_of_ncard_le_three {u₁ v₁ u₂ v₂ : α} {X : Set α}
    (hfin : X.Finite) (hcard : X.ncard ≤ 3) (h1 : u₁ ≠ v₁) (h2 : u₂ ≠ v₂)
    (hdisj : Disjoint ({u₁, v₁} : Set α) {u₂, v₂})
    (hu₁ : u₁ ∈ X) (hv₁ : v₁ ∈ X) (hu₂ : u₂ ∈ X) (hv₂ : v₂ ∈ X) : False := by
  let S2 : Set α := {u₂, v₂}; let S3 : Set α := insert v₁ S2; let S4 : Set α := insert u₁ S3
  have hv₁_not_S2 : v₁ ∉ S2 := fun hv => disjoint_left.mp hdisj (by simp) hv
  have hu₁_not_S3 : u₁ ∉ S3 := by
    simp only [S3, S2, mem_insert_iff, mem_singleton_iff, not_or]
    refine ⟨h1, ?_, ?_⟩ <;> (rintro rfl; exact disjoint_left.mp hdisj (Or.inl rfl) (by simp))
  have hS3_card : S3.ncard = 3 := by
    rw [ncard_insert_of_notMem hv₁_not_S2 ((finite_singleton v₂).insert u₂), ncard_pair h2]
  have hS4_card : S4.ncard = 4 := by
    rw [ncard_insert_of_notMem hu₁_not_S3 (((finite_singleton v₂).insert u₂).insert v₁), hS3_card]
  have hS4_sub : S4 ⊆ X := by rintro z (rfl | rfl | rfl | rfl) <;> assumption
  have hle : S4.ncard ≤ X.ncard := ncard_le_ncard hS4_sub hfin; omega

/-- Every transaction in `(consolidationCoreSociety S D_set hD)` lifts to a transaction in `S` with
the same pattern. -/
theorem exists_transaction_of_core_transaction {S : Society α β}
    {D_set : Set (Graph α β × Graph α β)} (hD : IsConsolidation S D_set) {Q_set : Set (Graph α
      (Sym2 α))}
    (hQ_trans : (consolidationCoreSociety S D_set hD).IsTransaction Q_set) :
    ∃ P_set : Set (Graph α β), S.IsTransaction P_set ∧ S.transactionPattern P_set =
        (consolidationCoreSociety S D_set hD).transactionPattern Q_set := by
  classical
  let CS := consolidationCoreSociety S D_set hD; let C := consolidationCore S D_set
  have hex_jump : ∀ e : Sym2 α, e ∈ E(C) → ∃ (p : Graph α β × Graph α β) (J : Graph α β), p ∈ D_set
    ∧ J ≤ p.1 ∧
        (∀ x y : α, C.IsLink e x y → x ∈ V(p.1) ∩ V(p.2) ∧ y ∈ V(p.1) ∩ V(p.2) ∧
          IsGraphPathWithEnds S.G J x y ∧ V(J) ∩ V(C) = {x, y}) := by
    rintro e ⟨u, v, huv, rfl, huC, hvC, p, hp, hu_p, hv_p⟩
    obtain ⟨J, hJ, hdisj⟩ := hD.exists_path hp u hu_p v hv_p huv
    have hJG : IsGraphPathWithEnds S.G J u v := hJ.mono (hD.left_le hp)
    have hJC : V(J) ∩ V(C) = {u, v} := by
      ext z; simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
      refine ⟨fun ⟨hzJ, hzC⟩ => by_contra fun h_not_uv =>
        disjoint_left.mp hdisj ⟨hzJ, h_not_uv⟩ (vertexSet_consolidationCore_subset_right hp hzC),
          ?_⟩
      rintro (rfl | rfl); exacts [⟨hJ.left_mem, huC⟩, ⟨hJ.right_mem, hvC⟩]
    refine ⟨p, J, hp, hJ.le, fun x y hlink => ?_⟩
    rcases Sym2.eq_iff.mp hlink.2.1.symm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hu_p, hv_p, hJG, hJC⟩
    · exact ⟨hv_p, hu_p, hJG.symm, by rw [hJC, pair_comm]⟩
  choose p_of J_of hp_of hJ_le hJ_spec using fun (e : E(C)) => hex_jump e.1 e.2
  have hJ_disj : ∀ (e₁ e₂ : E(C)) {x₁ y₁ x₂ y₂ : α}, C.IsLink e₁.1 x₁ y₁ → C.IsLink e₂.1 x₂ y₂ →
      Disjoint ({x₁, y₁} : Set α) {x₂, y₂} → Disjoint V(J_of e₁) V(J_of e₂) := by
    intro e₁ e₂ x₁ y₁ x₂ y₂ hl₁ hl₂ hdisj_ends
    obtain ⟨hx₁_p, hy₁_p, _, hJ₁_C⟩ := hJ_spec e₁ x₁ y₁ hl₁
    obtain ⟨hx₂_p, hy₂_p, _, hJ₂_C⟩ := hJ_spec e₂ x₂ y₂ hl₂
    have hp_ne : p_of e₁ ≠ p_of e₂ := fun heq => not_subset_of_ncard_le_three
        (S.finite_V.subset (inter_subset_left.trans (hD.left_le (hp_of e₁)).vertexSet_mono))
        (hD.order_le_three (hp_of e₁)) hl₁.1 hl₂.1 hdisj_ends hx₁_p hy₁_p (heq ▸ hx₂_p)
          (heq ▸ hy₂_p)
    have hA_inter_C := hD.left_inter_left_subset_consolidationCore (hp_of e₁) (hp_of e₂) hp_ne
    refine disjoint_left.mpr fun z hz₁ hz₂ => ?_
    have hzC : z ∈ V(C) := hA_inter_C ⟨(hJ_le e₁).vertexSet_mono hz₁, (hJ_le e₂).vertexSet_mono hz₂⟩
    have hz_ends₁ : z ∈ ({x₁, y₁} : Set α) := hJ₁_C ▸ ⟨hz₁, hzC⟩
    have hz_ends₂ : z ∈ ({x₂, y₂} : Set α) := hJ₂_C ▸ ⟨hz₂, hzC⟩
    exact disjoint_left.mp hdisj_ends hz_ends₁ hz_ends₂
  have hlift_walk : ∀ {a b : α} (W : GraphWalk C a b), ∃ W_G : GraphWalk S.G a b, ∀ z ∈ W_G.support,
          z ∈ {x | x ∈ W.support} ∪ ⋃ (e : E(C)) (_ : e.1 ∈ W.edges), V(J_of e) := by
    intro a b W; induction W with
    | @nil u hu =>
      refine ⟨.nil (vertexSet_consolidationCore_subset S D_set hu), fun z hz => ?_⟩
      simp only [GraphWalk.support_nil, List.mem_singleton] at hz; exact Or.inl (by simp [hz])
    | @cons x y z e hlink W_rest ih =>
      obtain ⟨W_rest_G, hW_rest_G⟩ := ih; let e_sub : E(C) := ⟨e, hlink.edge_mem⟩
      obtain ⟨_, _, ⟨hJ_G, W_J, _, hVJ, _⟩, _⟩ := hJ_spec e_sub x y hlink
      obtain ⟨W_J_G, hs_J, _⟩ := exists_walk_up_of_le hJ_G W_J
      refine ⟨W_J_G.append W_rest_G, fun w hw => ?_⟩
      rcases (GraphWalk.mem_support_append W_J_G W_rest_G).mp hw with hw_J | hw_rest
      · right
        rw [hs_J] at hw_J
        exact mem_iUnion₂.mpr ⟨e_sub, List.mem_cons_self, by rw [hVJ]; exact hw_J⟩
      · rcases hW_rest_G w hw_rest with hw_supp | hw_edges
        · exact Or.inl (List.mem_cons_of_mem _ hw_supp)
        · right; obtain ⟨e', he', hwJ'⟩ := mem_iUnion₂.mp hw_edges
          exact mem_iUnion₂.mpr ⟨e', List.mem_cons_of_mem _ he', hwJ'⟩
  rcases hQ_trans with ⟨A_f, B_f, hQ_disj, hfence, hQ_ends⟩
  have hex_P : ∀ Q : Graph α (Sym2 α), Q ∈ Q_set → ∃ P : Graph α β,
        (∃ a ∈ A_f, ∃ b ∈ B_f, CS.IsOmegaPathWithEnds Q a b ∧ S.IsOmegaPathWithEnds P a b) ∧
        pathEnds S.G P = pathEnds C Q ∧ V(P) ⊆ V(Q) ∪ ⋃ (e : E(C)) (_ : e.1 ∈ E(Q)), V(J_of e) := by
    intro Q hQ_in; obtain ⟨a, haA, b, hbB, hQ_ab⟩ := hQ_ends Q hQ_in
    have hQ_path_C : IsGraphPathWithEnds C Q a b := hQ_ab.1; rcases hQ_ab.1 with ⟨hQC, W_Q, _, hVQ,
      hEQ⟩
    obtain ⟨W_C, hs_C, he_C⟩ := exists_walk_up_of_le (show Q ≤ C from hQC) W_Q
    obtain ⟨W_G, hW_G⟩ := hlift_walk W_C; obtain ⟨P, hP, hVP, _⟩ :=
      exists_isGraphPathWithEnds_of_walk W_G
    refine ⟨P, ⟨a, haA, b, hbB, hQ_ab, ⟨hP, hQ_ab.2⟩⟩, by rw [hP.pathEnds_eq,
      hQ_path_C.pathEnds_eq], fun z hz => ?_⟩
    rcases hW_G z (hVP hz) with hz_supp | hz_edges
    · left; rw [hVQ, mem_ofPred_eq, ← hs_C]; exact hz_supp
    · right; obtain ⟨e, heW, hzJ⟩ := mem_iUnion₂.mp hz_edges
      rw [he_C] at heW; exact mem_iUnion₂.mpr ⟨e, by rw [hEQ]; exact heW, hzJ⟩
  choose g_map hg_ends hg_pattern hg_sub using fun (Q : Q_set) => hex_P Q.1 Q.2; let P_set : Set
    (Graph α β) := range g_map
  have hdisj_envelopes : ∀ (Q₁ Q₂ : Q_set), Q₁ ≠ Q₂ →
      Disjoint (V(Q₁.1) ∪ ⋃ (e : E(C)) (_ : e.1 ∈ E(Q₁.1)), V(J_of e))
        (V(Q₂.1) ∪ ⋃ (e : E(C)) (_ : e.1 ∈ E(Q₂.1)), V(J_of e)) := by
    intro Q₁ Q₂ hne; have hVQ_disj : Disjoint V(Q₁.1) V(Q₂.1) := hQ_disj.2 Q₁.2 Q₂.2
      (Subtype.ext_iff.not.mp hne)
    obtain ⟨_, _, _, _, hQ₁_ab, _⟩ := hg_ends Q₁; obtain ⟨_, _, _, _, hQ₂_ab, _⟩ := hg_ends Q₂
    have hQ₁C : Q₁.1 ≤ C := hQ₁_ab.1.le; have hQ₂C : Q₂.1 ≤ C := hQ₂_ab.1.le
    rw [disjoint_union_left, disjoint_union_right, disjoint_union_right]
    refine ⟨⟨hVQ_disj, disjoint_iUnion₂_right.mpr fun e₂ he₂ => ?_⟩,
      ⟨disjoint_iUnion₂_left.mpr fun e₁ he₁ => ?_,
        disjoint_iUnion₂_left.mpr fun e₁ he₁ => disjoint_iUnion₂_right.mpr fun e₂ he₂ => ?_⟩⟩
    · obtain ⟨x₂, y₂, hxy₂⟩ := Q₂.1.exists_isLink_of_mem_edgeSet he₂
      obtain ⟨_, _, _, hJ₂_C⟩ := hJ_spec e₂ x₂ y₂ (hxy₂.mono hQ₂C)
      refine disjoint_left.mpr fun z hzQ₁ hzJ₂ => disjoint_left.mp hVQ_disj hzQ₁ ?_
      rcases (hJ₂_C ▸ ⟨hzJ₂, hQ₁C.vertexSet_mono hzQ₁⟩ : z ∈ ({x₂, y₂} : Set α)) with rfl | rfl
      · exact hxy₂.left_mem
      · exact hxy₂.right_mem
    · obtain ⟨x₁, y₁, hxy₁⟩ := Q₁.1.exists_isLink_of_mem_edgeSet he₁
      obtain ⟨_, _, _, hJ₁_C⟩ := hJ_spec e₁ x₁ y₁ (hxy₁.mono hQ₁C)
      refine disjoint_left.mpr fun z hzJ₁ hzQ₂ => disjoint_left.mp hVQ_disj ?_ hzQ₂
      rcases (hJ₁_C ▸ ⟨hzJ₁, hQ₂C.vertexSet_mono hzQ₂⟩ : z ∈ ({x₁, y₁} : Set α)) with rfl | rfl
      · exact hxy₁.left_mem
      · exact hxy₁.right_mem
    · obtain ⟨x₁, y₁, hxy₁⟩ := Q₁.1.exists_isLink_of_mem_edgeSet he₁
      obtain ⟨x₂, y₂, hxy₂⟩ := Q₂.1.exists_isLink_of_mem_edgeSet he₂
      exact hJ_disj e₁ e₂ (hxy₁.mono hQ₁C) (hxy₂.mono hQ₂C) (hVQ_disj.mono
          (by rintro z (rfl | rfl); exacts [hxy₁.left_mem, hxy₁.right_mem])
          (by rintro z (rfl | rfl); exacts [hxy₂.left_mem, hxy₂.right_mem]))
  refine ⟨P_set, ⟨A_f, B_f, ⟨?_, ?_⟩, hfence, ?_⟩, ?_⟩
  · rintro P ⟨Q, rfl⟩; obtain ⟨a, _, b, _, _, hP_ab⟩ := hg_ends Q; exact ⟨a, b, hP_ab⟩
  · rintro P₁ ⟨Q₁, rfl⟩ P₂ ⟨Q₂, rfl⟩ hne
    exact (hdisj_envelopes Q₁ Q₂ (fun h => hne (congrArg g_map h))).mono (hg_sub Q₁) (hg_sub Q₂)
  · rintro P ⟨Q, rfl⟩; obtain ⟨a, haA, b, hbB, _, hP_ab⟩ := hg_ends Q; exact ⟨a, haA, b, hbB, hP_ab⟩
  · ext X; simp only [Society.transactionPattern, P_set, mem_image, mem_range, exists_exists_eq_and]
    exact ⟨by rintro ⟨Q, rfl⟩; exact ⟨Q.1, Q.2, (hg_pattern Q).symm⟩,
      by rintro ⟨Q, hQ, rfl⟩; exact ⟨⟨Q, hQ⟩, hg_pattern ⟨Q, hQ⟩⟩⟩

/-- **Graph Minors IX, (11.10)** (page 73):
"Let $C$ be the core of a consolidation $\mathcal{D}$ of $(G, \Omega)$. For any $\Pi$, there
is a transaction in $(G, \Omega)$ with pattern $\Pi$ if and only if there is such a
transaction in $(C, \Omega)$." -/
theorem theorem_11_10_proof (S : Society α β) (D_set : Set (Graph α β × Graph α β))
  (hD : IsConsolidation S D_set)
    (P_pat : Set (Set α)) :
    (∃ P_set : Set (Graph α β), S.IsTransaction P_set ∧ S.transactionPattern P_set = P_pat) ↔
      (∃ Q_set : Set (Graph α (Sym2 α)), (consolidationCoreSociety S D_set hD).IsTransaction Q_set ∧
        (consolidationCoreSociety S D_set hD).transactionPattern Q_set = P_pat) := by
  classical
  let CS := consolidationCoreSociety S D_set hD; let C := consolidationCore S D_set; constructor
  · rintro ⟨P_set, ⟨A_f, B_f, hP_disj, hfence, hP_ends⟩, rfl⟩
    have hex_Q : ∀ P : P_set, ∃ Q : Graph α (Sym2 α),
          (∃ a ∈ A_f, ∃ b ∈ B_f, S.IsOmegaPathWithEnds P.1 a b ∧ CS.IsOmegaPathWithEnds Q a b) ∧
          pathEnds C Q = pathEnds S.G P.1 ∧ V(Q) ⊆ V(P.1) := by
      intro P; obtain ⟨a, haA, b, hbB, hP_ab⟩ := hP_ends P.1 P.2
      obtain ⟨Q, hQ, hVQ⟩ := exists_core_path_of_path hD hP_ab.1
        (hD.bar_subset_consolidationCore hP_ab.2.2.1) (hD.bar_subset_consolidationCore hP_ab.2.2.2)
      exact ⟨Q, ⟨a, haA, b, hbB, hP_ab, ⟨hQ, hP_ab.2⟩⟩, by rw [hQ.pathEnds_eq, hP_ab.1.pathEnds_eq],
        hVQ.trans inter_subset_left⟩
    choose f_map hf_ends hf_pattern hf_sub using hex_Q; let Q_set : Set (Graph α (Sym2 α))
      := range f_map
    refine ⟨Q_set, ⟨A_f, B_f, ⟨?_, ?_⟩, hfence, ?_⟩, ?_⟩
    · rintro Q ⟨P, rfl⟩; obtain ⟨a, _, b, _, _, hQ_ab⟩ := hf_ends P; exact ⟨a, b, hQ_ab⟩
    · rintro Q₁ ⟨P₁, rfl⟩ Q₂ ⟨P₂, rfl⟩ hne
      exact (hP_disj.2 P₁.2 P₂.2 (fun h => hne (congrArg f_map (Subtype.ext h)))).mono (hf_sub P₁)
        (hf_sub P₂)
    · rintro Q ⟨P, rfl⟩; obtain ⟨a, haA, b, hbB, _, hQ_ab⟩ := hf_ends P; exact ⟨a, haA, b, hbB,
      hQ_ab⟩
    · ext X; simp only [Society.transactionPattern, Q_set, mem_image, mem_range,
      exists_exists_eq_and]
      exact ⟨by rintro ⟨P, rfl⟩; exact ⟨P.1, P.2, (hf_pattern P).symm⟩,
        by rintro ⟨P, hP, rfl⟩; exact ⟨⟨P, hP⟩, hf_pattern ⟨P, hP⟩⟩⟩
  · rintro ⟨Q_set, hQ_trans, rfl⟩; exact exists_transaction_of_core_transaction hD hQ_trans

end GraphMinor.GM09
