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
import LeanPool.GraphMinor.GM16.ProperBridgeIntersections
import LeanPool.GraphMinor.GM09.Section4b
import LeanPool.GraphMinor.GM10.Section12
import LeanPool.GraphMinor.GM11.OArcCircuit
import LeanPool.GraphMinor.GM11.Section81
import LeanPool.GraphMinor.GM14.Section7b
import LeanPool.GraphMinor.Surface.CircleMove

import LeanPool.GraphMinor.GM09.Bridge

/-!
# The proper arrangement in the proof of XVI (7.2)

We retain the arrangement constructed in XV (7.7), pages 139–142.
A large society belongs to one of its local segregations, each of which
has at most one large society. Distinct local pieces have disjoint vertex
sets by XV (7.6), so their large societies have disjoint boundary sets.
This proves the properness asserted in XVI, page 62.
-/

public section
namespace GraphMinor.GM16
open Set Function Topology
open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14 GM15
universe u v w
variable {α : Type u} {β : Type v}

/-- Claim (1) in the proof of Graph Minors XV, (7.7) (pages 139–140):
"For* $1 \le i \le k$, *if* $(A, \Omega) \in \mathcal{S}'$ *then* $E(G_i^* \cap A) =
\emptyset$ *and* $V(G_i^* \cap A) \subseteq \bar{\Omega}_i^*$." -/
private theorem theorem_7_7_claim_1
    {S : Type w} [TopologicalSpace S] [T2Space S] (hS : IsClosedSurface S) {α : Type u} {β : Type v}
    {G : Graph α β} {H : Drawing S} {η : SpanEmbedding H G}
    {θ_star θ θ' π beta μ k : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {r : Fin k → Set S}
    {η₀ : SpanEmbedding H (section7G0 G H η d θ' μ r)}
    {S₀ : Set (Society α β)} {α₀_disc : Society α β → Set S} {α₀_pt : α → S}
    {i : Fin k}
    (D_i : Section75EyeData G H η θ_star θ θ' π beta μ T_star T d r S₀ α₀_disc α₀_pt i)
    (hη₀_v : ∀ v ∈ H.V, η₀.vMap v = η.vMap v)
    (hThree : IsThreeSegregation (section7G0 G H η d θ' μ r) S₀)
    (hArr₀ : IsSurfaceArrangement S₀ α₀_disc α₀_pt)
    (hCompat₀ : IsCompatibleWith (section7G0 G H η d θ' μ r) H η₀ S₀ α₀_disc α₀_pt)
    {A : Society α β} (hA : A ∈ S₀) (hA_not : ¬ α₀_disc A ⊆ D_i.Δ) :
    Disjoint E(D_i.localSociety.G) E(A.G) ∧
    V(D_i.localSociety.G) ∩ V(A.G) ⊆ D_i.localSociety.Ω.bar := by
  let G₀ := section7G0 G H η d θ' μ r
  let J_i := eyeBridgeUnion G H η d θ' μ (r i)
  let P_i := arrangementPullbackGraph G₀ S₀ α₀_disc α₀_pt D_i.Δ
  have hA_le : A.G ≤ G₀ := hThree.1.le A hA
  have hJ_le : J_i ≤ G := subgraphSUnion_le (fun _ hB => hB.1.2.1)
  have hJ₀_le : remainingBridgeUnion G H η d θ' μ r ≤ G :=
    subgraphSUnion_le (fun _ hB => hB.1.2.1)
  have hPair_le : ∀ Q ∈ ({η.imageGraph, remainingBridgeUnion G H η d θ' μ r} : Set (Graph α β)),
      Q ≤ G := by
    rintro Q (rfl | rfl)
    · exact η.imageGraph_le
    · exact hJ₀_le
  have hG₀_le : G₀ ≤ G := subgraphSUnion_le hPair_le
  have hP_le : P_i ≤ G₀ := restrict_le.trans (G₀.induce_le inter_subset_right)
  have hseg_in_bar : ∀ {v' : α}, v' ∈ V(A.G) → v' ∈ segregationVertices S₀ → v' ∈ A.Ω.bar := by
    intro v' hv'A hv'seg
    obtain ⟨A', hA', hv'A'_bar⟩ := mem_iUnion₂.mp hv'seg
    by_cases hAA' : A = A'
    · subst hAA'; exact hv'A'_bar
    · exact (hThree.1.vertex_inter_subset A hA A' hA' hAA' ⟨hv'A, A'.bar_subset hv'A'_bar⟩).1
  obtain ⟨hinter_subBd, _⟩ :=
    inter_disc_subset_subBd_of_not_subset hS hArr₀ D_i.isClosedDisc_Δ D_i.isNormal_bd hA hA_not
  refine ⟨?_, ?_⟩
  · rw [D_i.soc_star_G, edgeSet_subgraphUnion hJ_le (hP_le.trans hG₀_le)]
    refine Set.disjoint_left.mpr ?_
    rintro e (heJ | heP) heA
    · have he_G₀ : e ∈ E(G₀) := hA_le.edgeSet_mono heA
      change e ∈ E(subgraphSUnion G {η.imageGraph, remainingBridgeUnion G H η d θ' μ r}) at he_G₀
      rw [edgeSet_subgraphSUnion hPair_le] at he_G₀
      change e ∈ E(eyeBridgeUnion G H η d θ' μ (r i)) at heJ
      rw [eyeBridgeUnion_edgeSet] at heJ
      obtain ⟨B₁, ⟨hB₁, z₁, hz₁B₁, u₁, ⟨hu₁H, hu₁Z₁⟩, rfl⟩, heB₁⟩ := mem_iUnion₂.mp heJ
      obtain ⟨Q, hQ, heQ⟩ := mem_iUnion₂.mp he_G₀
      rcases hQ with rfl | rfl
      · exact Set.disjoint_left.mp (isBridge_disjoint_edgeSet hB₁) heB₁ heQ
      · rw [remainingBridgeUnion_edgeSet] at heQ
        obtain ⟨B₀, ⟨hB₀, hB₀_disj⟩, heB₀⟩ := mem_iUnion₂.mp heQ
        have hVB_eq : V(B₁) = V(B₀) :=
          (isBridge_vertexSet_eq_of_inter hB₁ hB₀).2 e ⟨heB₁, heB₀⟩
        exact Set.disjoint_left.mp hB₀_disj (hVB_eq ▸ hz₁B₁)
          (mem_iUnion.mpr ⟨i, u₁, ⟨hu₁H, hu₁Z₁⟩, rfl⟩)
    · change e ∈ E(arrangementPullbackGraph G₀ S₀ α₀_disc α₀_pt D_i.Δ) at heP
      rw [arrangementPullbackGraph, edgeSet_restrict] at heP
      obtain ⟨A', ⟨hA'_S₀, hA'_sub⟩, heA'⟩ := mem_iUnion₂.mp heP.2
      have hAA'_ne : A ≠ A' := fun hEq => hA_not (hEq ▸ hA'_sub)
      exact Set.disjoint_left.mp (hThree.1.edge_disjoint A hA A' hA'_S₀ hAA'_ne) heA heA'
  · rintro x ⟨hx_star, hxA⟩
    rw [D_i.soc_star_G, vertexSet_subgraphUnion] at hx_star
    have hx_seg_and_Δ : x ∈ segregationVertices S₀ ∧ α₀_pt x ∈ D_i.Δ := by
      rcases hx_star with hxJ | hxP
      · have hx_G₀ : x ∈ V(G₀) := hA_le.vertexSet_mono hxA
        have hx_im : x ∈ V(η.imageGraph) := by
          by_contra hx_not_im
          change x ∈ V(subgraphSUnion G {η.imageGraph, remainingBridgeUnion G H η d θ' μ r})
            at hx_G₀
          rw [vertexSet_subgraphSUnion] at hx_G₀
          obtain ⟨Q, hQ, hxQ⟩ := mem_iUnion₂.mp hx_G₀
          have hxJ₀ : x ∈ V(remainingBridgeUnion G H η d θ' μ r) := by
            rcases hQ with rfl | rfl
            · exact (hx_not_im hxQ).elim
            · exact hxQ
          change x ∈ V(eyeBridgeUnion G H η d θ' μ (r i)) at hxJ
          rw [eyeBridgeUnion, vertexSet_subgraphSUnion] at hxJ
          rw [remainingBridgeUnion, vertexSet_subgraphSUnion] at hxJ₀
          obtain ⟨B₁, ⟨hB₁, z₁, hz₁B₁, u₁, ⟨hu₁H, hu₁Z₁⟩, rfl⟩, hxB₁⟩ := mem_iUnion₂.mp hxJ
          obtain ⟨B₀, ⟨hB₀, hB₀_disj⟩, hxB₀⟩ := mem_iUnion₂.mp hxJ₀
          have hVB_eq : V(B₁) = V(B₀) :=
            (isBridge_vertexSet_eq_of_inter hB₁ hB₀).1 x ⟨hxB₁, hxB₀⟩ hx_not_im
          exact Set.disjoint_left.mp hB₀_disj (hVB_eq ▸ hz₁B₁)
            (mem_iUnion.mpr ⟨i, u₁, ⟨hu₁H, hu₁Z₁⟩, rfl⟩)
        obtain ⟨u, huH, rfl⟩ := η.bijOn_v.surjOn hx_im
        have hu_Δ : u ∈ D_i.Δ := D_i.bridge_V_subset_Δ u huH hxJ
        have hu_A : u ∈ α₀_disc A := by
          rw [hCompat₀.inter_V_iff A hA u huH, hη₀_v u huH]
          exact hxA
        obtain ⟨w, hw_bar, hwu⟩ :=
          (inter_disc_subset_subBd_of_not_subset hS hArr₀ D_i.isClosedDisc_Δ
            D_i.isNormal_bd hA hA_not).2 ⟨hu_A, hu_Δ⟩
        have hu_bdA : u ∈ subBd (α₀_disc A) := hwu ▸ (hArr₀.isClosedDisc A hA).2 w hw_bar
        have hu_mem : u ∈ {v ∈ H.V | η₀.vMap v ∈ A.Ω.bar} := by
          rw [← hCompat₀.bd_inter_eq A hA]
          exact ⟨H.V_subset_U huH, hu_bdA⟩
        have hx_bar : η.vMap u ∈ A.Ω.bar := hη₀_v u huH ▸ hu_mem.2
        have hx_seg : η.vMap u ∈ segregationVertices S₀ := mem_biUnion hA hx_bar
        have hpt_eq : α₀_pt (η.vMap u) = u := by
          rw [← hη₀_v u huH]
          exact hCompat₀.pt_eq u huH (hη₀_v u huH ▸ hx_seg)
        exact ⟨hx_seg, hpt_eq.symm ▸ hu_Δ⟩
      · change x ∈ V(arrangementPullbackGraph G₀ S₀ α₀_disc α₀_pt D_i.Δ) at hxP
        rw [arrangementPullbackGraph, vertexSet_restrict, vertexSet_induce] at hxP
        rcases hxP.1 with hx_union | hx_seg_Δ
        · obtain ⟨A', ⟨hA'_S₀, hA'_sub⟩, hxA'⟩ := mem_iUnion₂.mp hx_union
          have hAA'_ne : A ≠ A' := fun hEq => hA_not (hEq ▸ hA'_sub)
          have hx_bars := hThree.1.vertex_inter_subset A hA A' hA'_S₀ hAA'_ne ⟨hxA, hxA'⟩
          have hx_bdA' : α₀_pt x ∈ subBd (α₀_disc A') := (hArr₀.isClosedDisc A' hA'_S₀).2 x
            hx_bars.2
          have hx_discA' : α₀_pt x ∈ α₀_disc A' :=
            (hArr₀.isClosedDisc A' hA'_S₀).1.isClosed.closure_subset_iff.mpr Subset.rfl hx_bdA'.1
          exact ⟨mem_biUnion hA hx_bars.1, hA'_sub hx_discA'⟩
        · exact hx_seg_Δ
    have hx_bar : x ∈ A.Ω.bar := hseg_in_bar hxA hx_seg_and_Δ.1
    have hx_bdA : α₀_pt x ∈ subBd (α₀_disc A) := (hArr₀.isClosedDisc A hA).2 x hx_bar
    have hx_discA : α₀_pt x ∈ α₀_disc A :=
      (hArr₀.isClosedDisc A hA).1.isClosed.closure_subset_iff.mpr Subset.rfl hx_bdA.1
    have hx_bdΔ : α₀_pt x ∈ subBd D_i.Δ := hinter_subBd ⟨hx_discA, hx_seg_and_Δ.2⟩
    rw [D_i.soc_star_Ω.1]
    exact ⟨hx_seg_and_Δ.1, hx_bdΔ⟩

/-- If each `F i` (`i : Fin k`) has `ncard ≤ 1`, then `(⋃ i : Fin k, F i).ncard ≤ k`. -/
private theorem ncard_iUnion_le_of_ncard_le_one {γ : Type*} :
    ∀ (k : ℕ) (F : Fin k → Set γ), (∀ i, (F i).ncard ≤ 1) → (⋃ i : Fin k, F i).ncard ≤ k
  | 0, F, _ => by simp
  | k + 1, F, hle => by
    have hunion : (⋃ i : Fin (k + 1), F i) = F 0 ∪ ⋃ i : Fin k, F i.succ := by
      ext x
      simp only [mem_iUnion, mem_union]
      constructor
      · rintro ⟨i, hx⟩
        exact Fin.cases (fun h0 => Or.inl h0) (fun j hj => Or.inr ⟨j, hj⟩) i hx
      · rintro (hx | ⟨j, hx⟩)
        · exact ⟨0, hx⟩
        · exact ⟨j.succ, hx⟩
    rw [hunion]
    have h1 : (F 0 ∪ ⋃ i : Fin k, F i.succ).ncard ≤ (F 0).ncard + (⋃ i : Fin k, F i.succ).ncard :=
      ncard_union_le _ _
    have h2 : (F 0).ncard ≤ 1 := hle 0
    have h3 : (⋃ i : Fin k, F i.succ).ncard ≤ k :=
      ncard_iUnion_le_of_ncard_le_one k (fun i => F i.succ) (fun i => hle i.succ)
    omega

/-- Pullback of a hypergraph separation `(A, B)` of `G` along `η : SpanEmbedding H G`. -/
private theorem exists_restrictedSeparation_of_isSeparation
    {S : Type w} [TopologicalSpace S] {α : Type u} {β : Type v}
    {G : Graph α β} (hV : V(G).Finite) (hE : E(G).Finite)
    (H : Drawing S) (η : SpanEmbedding H G) {A B : Hypergraph α β}
    (hsep : (Hypergraph.ofGraph G hV hE).IsSeparation A B) :
    ∃ A_H B_H : Hypergraph S (Set S),
      IsRestrictedSeparation H G η A B A_H B_H ∧
      A_H.vertexSet = {v ∈ H.V | η.vMap v ∈ A.vertexSet} ∧
      A_H.edgeSet = {e ∈ H.E | η.eMap e ∈ A.edgeSet} ∧
      B_H.vertexSet = {v ∈ H.V | η.vMap v ∈ B.vertexSet} ∧
      B_H.edgeSet = {e ∈ H.E | η.eMap e ∈ B.edgeSet} ∧
      separationOrder A_H B_H ≤ separationOrder A B := by
  let mkSub (X : Hypergraph α β) (hX : X ≤ Hypergraph.ofGraph G hV hE) : Hypergraph S (Set S) :=
    { vertexSet := {v ∈ H.V | η.vMap v ∈ X.vertexSet}
      edgeSet := {e ∈ H.E | η.eMap e ∈ X.edgeSet}
      Inc := fun e v => H.toHypergraph.Inc e v ∧ e ∈ H.E ∧ η.eMap e ∈ X.edgeSet
      vertex_mem_of_inc := fun e v h => by
        refine ⟨h.1.2.1, ?_⟩
        obtain ⟨w, hlink_im⟩ := (η.inc_iff e h.2.1 v h.1.2.1).mpr h.1.2.2
        have hlink_G : G.IsLink (η.eMap e) (η.vMap v) w :=
          (η.imageGraph_le.isLink_iff (η.bijOn_e.mapsTo h.2.1)).mp hlink_im
        have hinc_G : (Hypergraph.ofGraph G hV hE).Inc (η.eMap e) (η.vMap v) := ⟨w, hlink_G⟩
        have hv_ends : η.vMap v ∈ X.ends (η.eMap e) := by
          rw [← hX.ends_eq (η.eMap e) h.2.2]
          exact hinc_G
        exact X.vertex_mem_of_inc hv_ends
      edge_mem_of_inc := fun _ _ h => h.2
      vertexSet_finite := H.finite_V.subset fun _ h => h.1
      edgeSet_finite := H.finite_edges.subset fun _ h => h.1 }
  have hmk_le : ∀ (X : Hypergraph α β) (hX : X ≤ Hypergraph.ofGraph G hV hE),
      mkSub X hX ≤ H.toHypergraph := by
    intro X hX
    refine ⟨fun _ h => h.1, fun _ h => h.1, fun e he => ?_⟩
    ext v
    change H.toHypergraph.Inc e v ↔ H.toHypergraph.Inc e v ∧ e ∈ H.E ∧ η.eMap e ∈ X.edgeSet
    exact ⟨fun h => ⟨h, he.1, he.2⟩, fun h => h.1⟩
  let A_H := mkSub A hsep.left_le
  let B_H := mkSub B hsep.right_le
  have hAl : A_H ≤ H.toHypergraph := hmk_le A hsep.left_le
  have hBl : B_H ≤ H.toHypergraph := hmk_le B hsep.right_le
  have hRestr : IsRestrictedSeparation H G η A B A_H B_H := by
    refine ⟨(isSeparation_iff_of_le hAl hBl).mpr ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · ext v
      change (v ∈ H.V ∧ η.vMap v ∈ A.vertexSet ∨ v ∈ H.V ∧ η.vMap v ∈ B.vertexSet) ↔ v ∈ H.V
      refine ⟨by rintro (⟨hv, _⟩ | ⟨hv, _⟩) <;> exact hv, fun hv => ?_⟩
      have hvG : η.vMap v ∈ A.vertexSet ∪ B.vertexSet := by
        rw [hsep.vertexSet_union]
        exact η.imageGraph_le.vertexSet_mono (η.bijOn_v.mapsTo hv)
      rcases hvG with hvA | hvB
      · exact Or.inl ⟨hv, hvA⟩
      · exact Or.inr ⟨hv, hvB⟩
    · ext e
      change (e ∈ H.E ∧ η.eMap e ∈ A.edgeSet ∨ e ∈ H.E ∧ η.eMap e ∈ B.edgeSet) ↔ e ∈ H.E
      refine ⟨by rintro (⟨he, _⟩ | ⟨he, _⟩) <;> exact he, fun he => ?_⟩
      have heG : η.eMap e ∈ A.edgeSet ∪ B.edgeSet := by
        rw [hsep.edgeSet_union]
        exact η.imageGraph_le.edgeSet_mono (η.bijOn_e.mapsTo he)
      rcases heG with heA | heB
      · exact Or.inl ⟨he, heA⟩
      · exact Or.inr ⟨he, heB⟩
    · ext e
      change ((e ∈ H.E ∧ η.eMap e ∈ A.edgeSet) ∧ (e ∈ H.E ∧ η.eMap e ∈ B.edgeSet)) ↔
        e ∈ (∅ : Set (Set S))
      simp only [mem_empty_iff_false, iff_false]
      rintro ⟨⟨_, heA⟩, ⟨_, heB⟩⟩
      exact hsep.notMem_edgeSet_right heA heB
    · ext x
      refine ⟨by rintro ⟨v, ⟨hvH, hvA⟩, rfl⟩; exact ⟨hvA, η.bijOn_v.mapsTo hvH⟩, ?_⟩
      rintro ⟨hxA, hxIm⟩
      obtain ⟨v, hvH, rfl⟩ := η.bijOn_v.surjOn hxIm
      exact ⟨v, ⟨hvH, hxA⟩, rfl⟩
    · ext f
      refine ⟨by rintro ⟨e, ⟨heH, heA⟩, rfl⟩; exact ⟨heA, η.bijOn_e.mapsTo heH⟩, ?_⟩
      rintro ⟨hfA, hfIm⟩
      obtain ⟨e, heH, rfl⟩ := η.bijOn_e.surjOn hfIm
      exact ⟨e, ⟨heH, hfA⟩, rfl⟩
    · ext x
      refine ⟨by rintro ⟨v, ⟨hvH, hvB⟩, rfl⟩; exact ⟨hvB, η.bijOn_v.mapsTo hvH⟩, ?_⟩
      rintro ⟨hxB, hxIm⟩
      obtain ⟨v, hvH, rfl⟩ := η.bijOn_v.surjOn hxIm
      exact ⟨v, ⟨hvH, hxB⟩, rfl⟩
    · ext f
      refine ⟨by rintro ⟨e, ⟨heH, heB⟩, rfl⟩; exact ⟨heB, η.bijOn_e.mapsTo heH⟩, ?_⟩
      rintro ⟨hfB, hfIm⟩
      obtain ⟨e, heH, rfl⟩ := η.bijOn_e.surjOn hfIm
      exact ⟨e, ⟨heH, hfB⟩, rfl⟩
  have hord : separationOrder A_H B_H ≤ separationOrder A B := by
    have hsub_img : η.vMap '' (A_H ∩ B_H).vertexSet ⊆ (A ∩ B).vertexSet := by
      rintro x ⟨v, ⟨hvA, hvB⟩, rfl⟩
      exact ⟨hvA.2, hvB.2⟩
    have hinj : InjOn η.vMap (A_H ∩ B_H).vertexSet :=
      η.bijOn_v.injOn.mono fun v ⟨hvA, _⟩ => hvA.1
    calc separationOrder A_H B_H
      _ = (η.vMap '' (A_H ∩ B_H).vertexSet).ncard := hinj.ncard_image.symm
      _ ≤ separationOrder A B := Set.ncard_le_ncard hsub_img (A ∩ B).vertexSet_finite
  exact ⟨A_H, B_H, hRestr, rfl, rfl, rfl, rfl, hord⟩

/-- For any member `A ∈ S_seg` of a graph segregation `S_seg` of `G₀`, there is a complementary
subgraph `B ≤ G₀` such that `(A.G, B)` is a separation of `G₀` with `V(A.G) ∩ V(B) = A.Ω.bar`. -/
private theorem exists_graphSeparation_of_mem_segregation {α : Type u} {β : Type v}
    {G₀ : Graph α β} {S_seg : Set (Society α β)} (hSeg : IsGraphSegregation G₀ S_seg)
    {A : Society α β} (hA : A ∈ S_seg) :
    ∃ B : Graph α β, IsGraphSeparation G₀ A.G B ∧ V(A.G) ∩ V(B) = A.Ω.bar := by
  have hA_le : A.G ≤ G₀ := hSeg.le A hA
  let V_B := (V(G₀) \ V(A.G)) ∪ A.Ω.bar
  let E_B := E(G₀) \ E(A.G)
  let B := (G₀.induce V_B).restrict E_B
  have hVB_sub : V_B ⊆ V(G₀) := by
    rintro v (⟨hvG₀, _⟩ | hv_bar)
    · exact hvG₀
    · exact hA_le.vertexSet_mono (A.bar_subset hv_bar)
  have hB_le : B ≤ G₀ := restrict_le.trans (G₀.induce_le hVB_sub)
  have hVB_eq : V(B) = V_B := by simp [B]
  have hEB_eq : E(B) = E_B := by
    ext e
    simp only [B, edgeSet_restrict, mem_inter_iff, Graph.edgeSet_induce]
    refine ⟨fun h => h.2, fun ⟨heG₀, he_not_A⟩ => ⟨?_, ⟨heG₀, he_not_A⟩⟩⟩
    have he_union : e ∈ E(subgraphSUnion G₀ ((fun S' : Society α β => S'.G) '' S_seg)) := by
      rw [hSeg.union_eq]
      exact heG₀
    rw [edgeSet_subgraphSUnion (by rintro _ ⟨S', hS', rfl⟩; exact hSeg.le S' hS')] at he_union
    obtain ⟨_, ⟨A', hA', rfl⟩, heA'⟩ := mem_iUnion₂.mp he_union
    have hAA'_ne : A ≠ A' := fun hEq => he_not_A (hEq ▸ heA')
    obtain ⟨x, y, hxy_A'⟩ := A'.G.exists_isLink_of_mem_edgeSet heA'
    have hxy_G₀ : G₀.IsLink e x y := hxy_A'.mono (hSeg.le A' hA')
    have hmem_VB : ∀ z ∈ V(A'.G), z ∈ V_B := by
      intro z hzA'
      by_cases hzA : z ∈ V(A.G)
      · exact Or.inr (hSeg.vertex_inter_subset A hA A' hA' hAA'_ne ⟨hzA, hzA'⟩).1
      · exact Or.inl ⟨(hSeg.le A' hA').vertexSet_mono hzA', hzA⟩
    exact ⟨x, y, hxy_G₀, hmem_VB x hxy_A'.left_mem, hmem_VB y hxy_A'.right_mem⟩
  refine ⟨B, ⟨hA_le, hB_le, ?_, ?_, ?_⟩, ?_⟩
  · ext v
    rw [mem_union, hVB_eq]
    refine ⟨?_, fun hvG₀ => ?_⟩
    · rintro (hvA | hvB)
      · exact hA_le.vertexSet_mono hvA
      · exact hVB_sub hvB
    · by_cases hvA : v ∈ V(A.G)
      · exact Or.inl hvA
      · exact Or.inr (Or.inl ⟨hvG₀, hvA⟩)
  · ext e
    rw [mem_union, hEB_eq]
    refine ⟨?_, fun heG₀ => ?_⟩
    · rintro (heA | ⟨heG₀, _⟩)
      · exact hA_le.edgeSet_mono heA
      · exact heG₀
    · by_cases heA : e ∈ E(A.G)
      · exact Or.inl heA
      · exact Or.inr ⟨heG₀, heA⟩
  · rw [hEB_eq]
    exact disjoint_sdiff_self_right
  · ext v
    rw [mem_inter_iff, hVB_eq]
    constructor
    · rintro ⟨hvA, ⟨_, hv_not_A⟩ | hv_bar⟩
      · exact (hv_not_A hvA).elim
      · exact hv_bar
    · intro hv_bar
      exact ⟨A.bar_subset hv_bar, Or.inr hv_bar⟩


/-- The construction of XV (7.7), pages 139–142, gives a proper arrangement,
as observed in XVI (7.2), page 62. Its claims (1)–(9) build the segregation
and arrangement. Properness then follows from XV (7.6) and the fact that
each local segregation has at most one society with more than three ends. -/
theorem exists_proper_arrangement_of_no_crooked_transactions
     :
    ∀ {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G)
    (θ_star θ θ' lam π beta μ k : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ) (r : Fin k → Set S)
    (η₀ : SpanEmbedding H (section7G0 G H η d θ' μ r))
    (S₀ : Set (Society α β)) (α₀_disc : Society α β → Set S) (α₀_pt : α → S)
    (D : ∀ i : Fin k, Section75EyeData G H η θ_star θ θ' π beta μ T_star T d r S₀ α₀_disc α₀_pt i),
    IsFlatSpan G H η θ_star θ lam μ T_star T →
    HasTangleMetric H θ T d →
    1 ≤ μ → 2 ≤ π → π ≠ 3 → beta = 2 * π + 8 →
    θ' + 13 * μ + 14 ≤ beta → 100 * beta ≤ θ →
    Injective r →
    (∀ i : Fin k, IsDrawingEye G H η θ T (r i)) →
    (∀ i j : Fin k, i ≠ j → d (r i) (r j) = θ) →
    (∀ v ∈ H.V, η₀.vMap v = η.vMap v) →
    (∀ e ∈ H.E, η₀.eMap e = η.eMap e) →
    IsThreeSegregation (section7G0 G H η d θ' μ r) S₀ →
    IsTangleLocal (section7G0 G H η d θ' μ r) H η₀ T S₀ →
    IsSurfaceArrangement S₀ α₀_disc α₀_pt →
    IsCompatibleWith (section7G0 G H η d θ' μ r) H η₀ S₀ α₀_disc α₀_pt →
    Pairwise (fun i j : Fin k => Disjoint (D i).Δ (D j).Δ) →
    (∀ i : Fin k, ∀ P_set : Set (Graph α β),
      (D i).localSociety.IsCrookedTransaction P_set → P_set.ncard ≠ π) →
    ∃ (𝒮 : Set (Society α β)) (disc : Society α β → Set S) (pt : α → S),
      IsCentralSegregation G T_star 𝒮 ∧
      GM15.IsSegregationOfType G (3 * π + 9) k 𝒮 ∧ IsProperArrangement 𝒮 disc pt := by
  classical
  intro S _ _ α β G H η θ_star θ θ' lam π beta μ k T_star T d r η₀ S₀ α₀_disc α₀_pt D
    hFlat hMetric hμ1 hπ2 hπ3 hbeta_eq hbeta_ge hθ_ge hr_inj hr_eye hr_dist hη₀_v hη₀_e
    hThree hLocal hArr₀ hCompat₀ hDisj_Δ hno_crooked
  have hS : IsClosedSurface S :=
    ⟨hFlat.isSpan.isSurface.1, hFlat.isSpan.isSurface.2.1, fun x =>
      by_contra fun hx => Set.eq_empty_iff_forall_notMem.mp hFlat.isSpan.bd_empty x hx⟩
  have hConn : ConnectedSpace S := hFlat.isSpan.isConnected
  have hθ_bound : 2 * (θ' + 12 * μ + 14) + μ ≤ θ := by omega
  have hDisj_star : Pairwise (fun i j : Fin k => Disjoint V((D i).localSociety.G) V((D
    j).localSociety.G))
    :=
    theorem_7_6_proof G H η θ_star θ θ' lam π beta μ k T_star T d r η₀ S₀ α₀_disc α₀_pt D
      hFlat hMetric hμ1 hθ_bound hr_inj hr_eye hr_dist hη₀_v hThree hArr₀ hCompat₀ hDisj_Δ
  let G₀ := section7G0 G H η d θ' μ r
  have hJ₀_le : remainingBridgeUnion G H η d θ' μ r ≤ G :=
    subgraphSUnion_le (fun _ hB => hB.1.2.1)
  have hPair_le : ∀ Q ∈ ({η.imageGraph, remainingBridgeUnion G H η d θ' μ r} : Set (Graph α β)),
      Q ≤ G := by
    rintro Q (rfl | rfl)
    · exact η.imageGraph_le
    · exact hJ₀_le
  have hG₀_le : G₀ ≤ G := subgraphSUnion_le hPair_le
  have hJi_le : ∀ i : Fin k, eyeBridgeUnion G H η d θ' μ (r i) ≤ G :=
    fun _ => subgraphSUnion_le (fun _ hB => hB.1.2.1)
  have hPi_le : ∀ i : Fin k, arrangementPullbackGraph G₀ S₀ α₀_disc α₀_pt (D i).Δ ≤ G :=
    fun _ => (restrict_le.trans (G₀.induce_le inter_subset_right)).trans hG₀_le
  have hstar_le : ∀ i : Fin k, (D i).localSociety.G ≤ G := by
    intro i
    rw [(D i).soc_star_G]
    exact subgraphUnion_le (hJi_le i) (hPi_le i)
  -- For each `i : Fin k`, apply (6.1) (`theorem_6_1_proof`) and transport to `(D i).Δ`.
  have hex_i : ∀ i : Fin k,
      ∃ (S_seg_i : Set (Society α β)) (α_disc_i : Society α β → Set S) (α_pt_i : α → S),
        GM15.IsSegregationOfType (D i).localSociety.G (3 * π + 9) 1 S_seg_i ∧
        (D i).localSociety.Ω.bar ⊆ segregationVertices S_seg_i ∧
        (∀ v ∈ (D i).localSociety.Ω.bar, α_pt_i v = α₀_pt v) ∧
        (∀ v ∈ segregationVertices S_seg_i, α_pt_i v ∈ (D i).Δ) ∧
        (∀ v ∈ segregationVertices S_seg_i, v ∉ (D i).localSociety.Ω.bar →
          α_pt_i v ∈ (D i).Δ \ subBd (D i).Δ) ∧
        InjOn α_pt_i (segregationVertices S_seg_i) ∧
        (∀ B ∈ S_seg_i, IsClosedDisc (α_disc_i B) ∧ α_disc_i B ⊆ (D i).Δ ∧
          ∀ x ∈ B.Ω.bar, α_pt_i x ∈ subBd (α_disc_i B)) ∧
        (∀ B ∈ S_seg_i, IsNaturalOrderFrom α_pt_i B.Ω (subBd (α_disc_i B))) ∧
        (∀ B ∈ S_seg_i, α_disc_i B ∩ subBd (D i).Δ ⊆ α_pt_i '' (B.Ω.bar ∩
          (D i).localSociety.Ω.bar)) ∧
        (∀ B₁ ∈ S_seg_i, ∀ B₂ ∈ S_seg_i, B₁ ≠ B₂ →
          α_disc_i B₁ ∩ α_disc_i B₂ ⊆ α_pt_i '' (B₁.Ω.bar ∩ B₂.Ω.bar)) := by
    intro i
    obtain ⟨S_seg_i, m, A₀_i, A_i, Δ_E, α₀_E, α_disc_E, α_pt_E,
        hS_eq, hType_i, hBar_i, hDiscArr_i⟩ :=
      GM15.theorem_6_1_proof (D i).localSociety π hπ2 hπ3 (hno_crooked i)
    subst hS_eq
    have hinj_bar_i : InjOn α₀_pt (D i).localSociety.Ω.bar :=
      hArr₀.injOn_pts.mono (fun v hv => ((D i).soc_star_Ω.1 ▸ hv).1)
    obtain ⟨α_disc_S, α_pt_S, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
      exists_surface_disc_arrangement_of_isDiscArrangement hS (D i).localSociety A₀_i A_i
        Δ_E α₀_E α_disc_E α_pt_E hBar_i hDiscArr_i (D i).Δ (D i).isClosedDisc_Δ
        α₀_pt hinj_bar_i (D i).soc_star_Ω.2
    exact ⟨insert A₀_i (range A_i), α_disc_S, α_pt_S, hType_i, hBar_i,
      h1, h2, h3, h4, h5, h6, h7, h8⟩
  choose S_seg α_disc_i α_pt_i hType_i hBar_i hpt_i_eq_0 hpt_i_mem_Δ hpt_i_mem_int
    hinj_i hdisc_i_closed hnat_i hinter_bd_i hinter_discs_i using hex_i
  have hseg_i_sub_V : ∀ i : Fin k, segregationVertices (S_seg i) ⊆ V((D i).localSociety.G) := by
    intro i v hv
    rcases mem_iUnion₂.mp hv with ⟨B, hB, hvB⟩
    exact ((hType_i i).1.le B hB).vertexSet_mono (B.bar_subset hvB)
  -- Define `S'`, `S_seg' i`, and `S_final`.
  let S' : Set (Society α β) := {A ∈ S₀ | ∀ i : Fin k, ¬ α₀_disc A ⊆ (D i).Δ}
  let S_seg' : Fin k → Set (Society α β) := fun i =>
    {B ∈ S_seg i | V(B.G).Nonempty ∧ B ∉ S'}
  let S_final : Set (Society α β) := S' ∪ ⋃ i : Fin k, S_seg' i
  have hDisj_S'_seg' : ∀ i : Fin k, Disjoint S' (S_seg' i) :=
    fun i => Set.disjoint_left.mpr fun _ hS' hseg' => hseg'.2.2 hS'
  have hDisj_seg' : Pairwise (fun i j : Fin k => Disjoint (S_seg' i) (S_seg' j)) := by
    intro i j hij
    refine Set.disjoint_left.mpr fun B hBi hBj => ?_
    obtain ⟨v, hv⟩ := hBi.2.1
    exact Set.disjoint_left.mp (hDisj_star hij)
      (((hType_i i).1.le B hBi.1).vertexSet_mono hv)
      (((hType_i j).1.le B hBj.1).vertexSet_mono hv)
  -- Claim (2): `S_final` is a graph segregation of `G`.
  have hFin₀ : S'.Finite := hThree.1.finite.subset fun _ h => h.1
  have hFin_eye (i : Fin k) : (S_seg' i).Finite := (hType_i i).1.finite.subset fun _ h => h.1
  have hFin_final : S_final.Finite := hFin₀.union (finite_iUnion hFin_eye)
  have hLe_final : ∀ B ∈ S_final, B.G ≤ G := by
    rintro B (hB_S' | hB_i)
    · exact (hThree.1.le B hB_S'.1).trans hG₀_le
    · obtain ⟨i, hBi⟩ := mem_iUnion.mp hB_i
      exact ((hType_i i).1.le B hBi.1).trans (hstar_le i)
  have hCover_star_V : ∀ (i : Fin k) {v : α}, v ∈ V((D i).localSociety.G) →
      ∃ B ∈ S_final, v ∈ V(B.G) := by
    intro i v hv
    have hv_u : v ∈ V(subgraphSUnion (D i).localSociety.G ((fun B : Society α β => B.G) '' S_seg i))
      := by
      rw [(hType_i i).1.union_eq]; exact hv
    rw [vertexSet_subgraphSUnion] at hv_u
    obtain ⟨_, ⟨B, hB, rfl⟩, hvB⟩ := mem_iUnion₂.mp hv_u
    by_cases hB_S' : B ∈ S'
    · exact ⟨B, Or.inl hB_S', hvB⟩
    · exact ⟨B, Or.inr (mem_iUnion.mpr ⟨i, hB, ⟨v, hvB⟩, hB_S'⟩), hvB⟩
  have hCover_star_E : ∀ (i : Fin k) {e : β}, e ∈ E((D i).localSociety.G) →
      ∃ B ∈ S_final, e ∈ E(B.G) := by
    intro i e he
    have he_u : e ∈ E(subgraphSUnion (D i).localSociety.G ((fun B : Society α β => B.G) '' S_seg i))
      := by
      rw [(hType_i i).1.union_eq]; exact he
    rw [edgeSet_subgraphSUnion (by rintro _ ⟨B, hB, rfl⟩; exact (hType_i i).1.le B hB)] at he_u
    obtain ⟨_, ⟨B, hB, rfl⟩, heB⟩ := mem_iUnion₂.mp he_u
    obtain ⟨x, _, hxy⟩ := B.G.exists_isLink_of_mem_edgeSet heB
    by_cases hB_S' : B ∈ S'
    · exact ⟨B, Or.inl hB_S', heB⟩
    · exact ⟨B, Or.inr (mem_iUnion.mpr ⟨i, hB, ⟨x, hxy.left_mem⟩, hB_S'⟩), heB⟩
  have hClaim2 : IsGraphSegregation G S_final := by
    exact assemble_eye_segregation (S := S) (α := α) (β := β) G H η θ_star θ θ' π beta μ k T_star
      T d r η₀ S₀ α₀_disc α₀_pt D hη₀_v hThree hArr₀ hCompat₀ hS hDisj_star hPair_le hJi_le
      hPi_le hstar_le S_seg hType_i hBar_i hFin_final hLe_final hCover_star_V
      hCover_star_E
  -- Claim (3): `S_final` is of type `(3 * π + 9, k)`.
  have hClaim3 : GM15.IsSegregationOfType G (3 * π + 9) k S_final := by
    refine ⟨hClaim2, ?_, ?_⟩
    · let F : Fin k → Set (Society α β) := fun i => {B ∈ S_seg i | 3 < B.Ω.bar.ncard}
      have hsub : {B ∈ S_final | 3 < B.Ω.bar.ncard} ⊆ ⋃ i : Fin k, F i := by
        rintro B ⟨hB_S' | hB_i, hgt⟩
        · exact False.elim (not_lt_of_ge (hThree.2 B hB_S'.1) hgt)
        · obtain ⟨i, hBi⟩ := mem_iUnion.mp hB_i
          exact mem_iUnion.mpr ⟨i, hBi.1, hgt⟩
      have hfin_u : (⋃ i : Fin k, F i).Finite :=
        finite_iUnion fun i => (hType_i i).1.finite.subset fun _ h => h.1
      exact (ncard_le_ncard hsub hfin_u).trans
        (ncard_iUnion_le_of_ncard_le_one k F (fun i => (hType_i i).vortex_count_le))
    · rintro B (hB_S' | hB_i) hgt
      · exact False.elim (not_lt_of_ge (hThree.2 B hB_S'.1) hgt)
      · obtain ⟨i, hBi⟩ := mem_iUnion.mp hB_i
        exact (hType_i i).is_p_vortex hBi.1 hgt
  -- Claim (4): `S_final` is `T_star`-central.
  have hClaim4 : IsCentralSegregation G T_star S_final := by
    exact assembled_eye_segregation_is_central (S := S) (α := α) (β := β) G H η θ_star θ θ' lam π
      beta μ k T_star T d r η₀ S₀ α₀_disc α₀_pt D hFlat hMetric hμ1 hπ2 hbeta_eq hθ_ge hr_eye
      hη₀_v hη₀_e hThree hLocal hCompat₀ hS hθ_bound hJi_le hPi_le S_seg hType_i
       hClaim3
  -- Define `α_disc` and `α_pt` and prove Claims (5)–(9).
  let α_disc : Society α β → Set S := fun B =>
    if h : ∃ i : Fin k, B ∈ S_seg' i then α_disc_i (Classical.choose h) B else α₀_disc B
  let α_pt : α → S := fun v =>
    if h : ∃ i : Fin k, v ∈ segregationVertices (S_seg i) then α_pt_i (Classical.choose h) v
    else α₀_pt v
  have hα_disc_S' : ∀ {B : Society α β}, B ∈ S' → α_disc B = α₀_disc B := by
    intro B hB
    have hnot : ¬ ∃ i : Fin k, B ∈ S_seg' i := by
      rintro ⟨i, hBi⟩
      exact Set.disjoint_left.mp (hDisj_S'_seg' i) hB hBi
    simp [α_disc, hnot]
  have hα_disc_seg' : ∀ (i : Fin k) {B : Society α β}, B ∈ S_seg' i → α_disc B = α_disc_i i B := by
    intro i B hBi
    have hex : ∃ j : Fin k, B ∈ S_seg' j := ⟨i, hBi⟩
    have hij : Classical.choose hex = i := by
      by_contra hne
      exact Set.disjoint_left.mp (hDisj_seg' hne) (Classical.choose_spec hex) hBi
    simp [α_disc, hex, hij]
  -- Claim (5): For `i : Fin k`, if `v ∈ segregationVertices (S_seg i)` then `α_pt v = α_pt_i i v`.
  have hClaim5 : ∀ (i : Fin k) {v : α}, v ∈ segregationVertices (S_seg i) →
      α_pt v = α_pt_i i v := by
    intro i v hvi
    have hex : ∃ j : Fin k, v ∈ segregationVertices (S_seg j) := ⟨i, hvi⟩
    have hij : Classical.choose hex = i := by
      by_contra hne
      exact Set.disjoint_left.mp (hDisj_star hne)
        (hseg_i_sub_V _ (Classical.choose_spec hex)) (hseg_i_sub_V i hvi)
    simp [α_pt, hex, hij]
  have hα_pt_S' : ∀ {v : α}, v ∈ segregationVertices S' → α_pt v = α₀_pt v := by
    intro v hv_S'
    by_cases hex : ∃ i : Fin k, v ∈ segregationVertices (S_seg i)
    · obtain ⟨i, hvi⟩ := hex
      rw [hClaim5 i hvi]
      obtain ⟨A, hA_S', hvA⟩ := mem_iUnion₂.mp hv_S'
      have hv_bar_star : v ∈ (D i).localSociety.Ω.bar :=
        (theorem_7_7_claim_1 hS (D i) hη₀_v hThree hArr₀ hCompat₀ hA_S'.1 (hA_S'.2 i)).2
          ⟨hseg_i_sub_V i hvi, A.bar_subset hvA⟩
      exact hpt_i_eq_0 i v hv_bar_star
    · simp [α_pt, hex]
  -- Claims (6)–(9): `(S_final, α_disc, α_pt)` is a surface arrangement in `S`.
  have hArr_final : IsSurfaceArrangement S_final α_disc α_pt := by
    exact arrange_replacement_societies (S := S) (α := α) (β := β) G H η θ_star θ θ' lam π beta μ
      k T_star T d r S₀ α₀_disc α₀_pt D hFlat hArr₀ hDisj_Δ hS S_seg α_disc_i α_pt_i hBar_i
      hpt_i_eq_0 hpt_i_mem_Δ hinj_i hdisc_i_closed hnat_i hinter_bd_i hinter_discs_i
       α_disc α_pt hα_disc_S' hα_disc_seg' hClaim5 hα_pt_S'
  refine ⟨S_final, α_disc, α_pt, hClaim4, hClaim3,
    IsSurfaceArrangement.isProper_of_disjoint_boundaries hArr_final ?_⟩
  intro A hA B hB hne hlargeA hlargeB
  have hLargeLocal : ∀ C ∈ S_final, 3 < C.Ω.bar.ncard → ∃ i, C ∈ S_seg' i := by
    intro C hC hlarge
    rcases hC with hC | hC
    · exact (not_lt_of_ge (hThree.2 C hC.1) hlarge).elim
    · exact mem_iUnion.mp hC
  obtain ⟨i, hAi⟩ := hLargeLocal A hA hlargeA
  obtain ⟨j, hBj⟩ := hLargeLocal B hB hlargeB
  have hij : i ≠ j := by
    intro hij
    subst j
    have hfin : {C ∈ S_seg i | 3 < C.Ω.bar.ncard}.Finite :=
      (hType_i i).1.finite.subset fun _ h => h.1
    exact hne ((Set.ncard_le_one hfin).mp (hType_i i).vortex_count_le A
      ⟨hAi.1, hlargeA⟩ B ⟨hBj.1, hlargeB⟩)
  exact (hDisj_star hij).mono
    (fun _ hv => ((hType_i i).1.le A hAi.1).vertexSet_mono (A.bar_subset hv))
    (fun _ hv => ((hType_i j).1.le B hBj.1).vertexSet_mono (B.bar_subset hv))

end GraphMinor.GM16
