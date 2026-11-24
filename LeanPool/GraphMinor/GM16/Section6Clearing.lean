/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section6
import LeanPool.GraphMinor.GM16.Section8Truncation
import LeanPool.GraphMinor.GM12.Induced
import LeanPool.GraphMinor.GM11.Walks
import LeanPool.GraphMinor.GM14.Section3
import LeanPool.GraphMinor.GM10.TangleLemmas

/-!
# Clearing a zone in a span

In XVI (6.3), page 60, the drawing and tangle obtained by clearing a zone
are again a span when the remaining drawing is rigid. Restrict a separation
to the original drawing and then to the cleared drawing. The membership
property of the cleared tangle preserves control by the ambient tangle.
-/

public section
namespace GraphMinor.GM16
open Set Graph Hypergraph GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM14
  GraphMinor.GM15
universe u v w

private def spanPullback {S : Type w} [TopologicalSpace S] {α : Type u} {β : Type v}
    {G : Graph α β} (hV : V(G).Finite) (hE : E(G).Finite)
    (H : Drawing S) (η : SpanEmbedding H G) (A : Hypergraph α β)
    (hA : A ≤ Hypergraph.ofGraph G hV hE) : Hypergraph S (Set S) where
  vertexSet := {v ∈ H.V | η.vMap v ∈ A.vertexSet}
  edgeSet := {e ∈ H.E | η.eMap e ∈ A.edgeSet}
  Inc e v := H.toHypergraph.Inc e v ∧ e ∈ H.E ∧ η.eMap e ∈ A.edgeSet
  vertex_mem_of_inc e v h := by
    refine ⟨h.1.2.1, ?_⟩
    have hinc_im : η.imageGraph.Inc (η.eMap e) (η.vMap v) :=
      (η.inc_iff e h.2.1 v h.1.2.1).mpr h.1.2.2
    obtain ⟨w, hlink_im⟩ := hinc_im
    have hlink_G : G.IsLink (η.eMap e) (η.vMap v) w :=
      (η.imageGraph_le.isLink_iff (η.bijOn_e.mapsTo h.2.1)).mp hlink_im
    have hinc_G : (Hypergraph.ofGraph G hV hE).Inc (η.eMap e) (η.vMap v) := ⟨w, hlink_G⟩
    have hv_ends : η.vMap v ∈ A.ends (η.eMap e) := by
      rw [← hA.ends_eq (η.eMap e) h.2.2]
      exact hinc_G
    exact A.vertex_mem_of_inc hv_ends
  edge_mem_of_inc _ _ h := h.2
  vertexSet_finite := H.finite_V.subset fun _ h => h.1
  edgeSet_finite := H.finite_edges.subset fun _ h => h.1

private theorem spanPullback_le {S : Type w} [TopologicalSpace S] {α : Type u} {β : Type v}
    {G : Graph α β} (hV : V(G).Finite) (hE : E(G).Finite)
    (H : Drawing S) (η : SpanEmbedding H G) (A : Hypergraph α β)
    (hA : A ≤ Hypergraph.ofGraph G hV hE) :
    spanPullback hV hE H η A hA ≤ H.toHypergraph := by
  refine ⟨fun _ h => h.1, fun _ h => h.1, fun e he => ?_⟩
  ext v
  change H.toHypergraph.Inc e v ↔ H.toHypergraph.Inc e v ∧ e ∈ H.E ∧ η.eMap e ∈ A.edgeSet
  exact ⟨fun h => ⟨h, he.1, he.2⟩, fun h => h.1⟩

private theorem isRestrictedSeparation_spanPullback
    {S : Type w} [TopologicalSpace S] {α : Type u} {β : Type v}
    {G : Graph α β} (hV : V(G).Finite) (hE : E(G).Finite)
    (H : Drawing S) (η : SpanEmbedding H G) {A B : Hypergraph α β}
    (hsep : (Hypergraph.ofGraph G hV hE).IsSeparation A B) :
    IsRestrictedSeparation H G η A B
      (spanPullback hV hE H η A hsep.left_le)
      (spanPullback hV hE H η B hsep.right_le) := by
  have hAl := spanPullback_le hV hE H η A hsep.left_le
  have hBl := spanPullback_le hV hE H η B hsep.right_le
  refine ⟨(isSeparation_iff_of_le hAl hBl).mpr ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · ext v
    change (v ∈ H.V ∧ η.vMap v ∈ A.vertexSet ∨ v ∈ H.V ∧ η.vMap v ∈ B.vertexSet) ↔ v ∈ H.V
    constructor
    · rintro (⟨hv, _⟩ | ⟨hv, _⟩) <;> exact hv
    · intro hv
      have hvG : η.vMap v ∈ A.vertexSet ∪ B.vertexSet := by
        rw [hsep.vertexSet_union]
        exact η.imageGraph_le.vertexSet_mono (η.bijOn_v.mapsTo hv)
      rcases hvG with hvA | hvB
      · exact Or.inl ⟨hv, hvA⟩
      · exact Or.inr ⟨hv, hvB⟩
  · ext e
    change (e ∈ H.E ∧ η.eMap e ∈ A.edgeSet ∨ e ∈ H.E ∧ η.eMap e ∈ B.edgeSet) ↔ e ∈ H.E
    constructor
    · rintro (⟨he, _⟩ | ⟨he, _⟩) <;> exact he
    · intro he
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
    constructor
    · rintro ⟨v, ⟨hvH, hvA⟩, rfl⟩
      exact ⟨hvA, η.bijOn_v.mapsTo hvH⟩
    · rintro ⟨hxA, hxIm⟩
      obtain ⟨v, hvH, rfl⟩ := η.bijOn_v.surjOn hxIm
      exact ⟨v, ⟨hvH, hxA⟩, rfl⟩
  · ext f
    constructor
    · rintro ⟨e, ⟨heH, heA⟩, rfl⟩
      exact ⟨heA, η.bijOn_e.mapsTo heH⟩
    · rintro ⟨hfA, hfIm⟩
      obtain ⟨e, heH, rfl⟩ := η.bijOn_e.surjOn hfIm
      exact ⟨e, ⟨heH, hfA⟩, rfl⟩
  · ext x
    constructor
    · rintro ⟨v, ⟨hvH, hvB⟩, rfl⟩
      exact ⟨hvB, η.bijOn_v.mapsTo hvH⟩
    · rintro ⟨hxB, hxIm⟩
      obtain ⟨v, hvH, rfl⟩ := η.bijOn_v.surjOn hxIm
      exact ⟨v, ⟨hvH, hxB⟩, rfl⟩
  · ext f
    constructor
    · rintro ⟨e, ⟨heH, heB⟩, rfl⟩
      exact ⟨heB, η.bijOn_e.mapsTo heH⟩
    · rintro ⟨hfB, hfIm⟩
      obtain ⟨e, heH, rfl⟩ := η.bijOn_e.surjOn hfIm
      exact ⟨e, ⟨heH, hfB⟩, rfl⟩

/-- Restriction of a separation along a span embedding is unique. -/
theorem restrictedSeparation_unique
    {S : Type w} [TopologicalSpace S] {α : Type u} {β : Type v}
    {G : Graph α β} {H : Drawing S} {η : SpanEmbedding H G}
    {A B : Hypergraph α β} {A₁ B₁ A₂ B₂ : Hypergraph S (Set S)}
    (h₁ : IsRestrictedSeparation H G η A B A₁ B₁)
    (h₂ : IsRestrictedSeparation H G η A B A₂ B₂) : A₁ = A₂ ∧ B₁ = B₂ := by
  constructor
  · apply eq_of_le_of_vertexSet_eq_of_edgeSet_eq h₁.1.left_le h₂.1.left_le
    · apply (η.bijOn_v.injOn.image_eq_image_iff h₁.1.left_le.vertexSet_subset
        h₂.1.left_le.vertexSet_subset).mp
      rw [h₁.2.1, h₂.2.1]
    · apply (η.bijOn_e.injOn.image_eq_image_iff h₁.1.left_le.edgeSet_subset
        h₂.1.left_le.edgeSet_subset).mp
      rw [h₁.2.2.1, h₂.2.2.1]
  · apply eq_of_le_of_vertexSet_eq_of_edgeSet_eq h₁.1.right_le h₂.1.right_le
    · apply (η.bijOn_v.injOn.image_eq_image_iff h₁.1.right_le.vertexSet_subset
        h₂.1.right_le.vertexSet_subset).mp
      rw [h₁.2.2.2.1, h₂.2.2.2.1]
    · apply (η.bijOn_e.injOn.image_eq_image_iff h₁.1.right_le.edgeSet_subset
        h₂.1.right_le.edgeSet_subset).mp
      rw [h₁.2.2.2.2, h₂.2.2.2.2]

/-- Restricting a separation to a cleared drawing is the same as
intersecting its restriction to the original drawing with that drawing. -/
theorem restrictedSeparation_clear
    {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}
    {G : Graph α β} {H : Drawing S} {η : SpanEmbedding H G}
    {A B : Hypergraph α β} {A_H B_H : Hypergraph S (Set S)} (Λ : Set S)
    (h : IsRestrictedSeparation H G η A B A_H B_H) :
    IsRestrictedSeparation (clearedSubdrawing H Λ) G (restrictCleared η Λ) A B
      (A_H ∩ (clearedSubdrawing H Λ).toHypergraph)
      (B_H ∩ (clearedSubdrawing H Λ).toHypergraph) := by
  let H' := clearedSubdrawing H Λ
  let η' := restrictCleared η Λ
  have hsub := clearedSubdrawing_isSubdrawing H Λ
  have hHyp : H'.toHypergraph ≤ H.toHypergraph := by
    refine ⟨hsub.1, hsub.2, fun e he => ?_⟩
    ext z
    change (e ∈ H.E ∧ z ∈ H.V ∧ z ∈ closure e) ↔
      (e ∈ H'.E ∧ z ∈ H'.V ∧ z ∈ closure e)
    constructor
    · rintro ⟨_, hz, hze⟩
      have hz' : z ∈ closure e ∩ H'.V := by
        rw [hsub.closure_inter_V he]
        exact ⟨hze, hz⟩
      exact ⟨he, hz'.2, hze⟩
    · rintro ⟨_, hz, hze⟩
      exact ⟨hsub.2 he, hsub.1 hz, hze⟩
  have hηsub := restrictCleared_imageGraph_le η Λ
  refine ⟨GM12.separation_inter_subgraph h.1 hHyp, ?_, ?_, ?_, ?_⟩
  · change η.vMap '' (A_H.vertexSet ∩ H'.V) = A.vertexSet ∩ V(η'.imageGraph)
    rw [η.bijOn_v.injOn.image_inter h.1.left_le.vertexSet_subset hsub.1, h.2.1]
    change (A.vertexSet ∩ V(η.imageGraph)) ∩ (η'.vMap '' H'.V) = _
    rw [η'.bijOn_v.image_eq, Set.inter_assoc, Set.inter_eq_right.mpr hηsub.vertexSet_mono]
  · change η.eMap '' (A_H.edgeSet ∩ H'.E) = A.edgeSet ∩ E(η'.imageGraph)
    rw [η.bijOn_e.injOn.image_inter h.1.left_le.edgeSet_subset hsub.2, h.2.2.1]
    change (A.edgeSet ∩ E(η.imageGraph)) ∩ (η'.eMap '' H'.E) = _
    rw [η'.bijOn_e.image_eq, Set.inter_assoc, Set.inter_eq_right.mpr hηsub.edgeSet_mono]
  · change η.vMap '' (B_H.vertexSet ∩ H'.V) = B.vertexSet ∩ V(η'.imageGraph)
    rw [η.bijOn_v.injOn.image_inter h.1.right_le.vertexSet_subset hsub.1, h.2.2.2.1]
    change (B.vertexSet ∩ V(η.imageGraph)) ∩ (η'.vMap '' H'.V) = _
    rw [η'.bijOn_v.image_eq, Set.inter_assoc, Set.inter_eq_right.mpr hηsub.vertexSet_mono]
  · change η.eMap '' (B_H.edgeSet ∩ H'.E) = B.edgeSet ∩ E(η'.imageGraph)
    rw [η.bijOn_e.injOn.image_inter h.1.right_le.edgeSet_subset hsub.2, h.2.2.2.2]
    change (B.edgeSet ∩ E(η.imageGraph)) ∩ (η'.eMap '' H'.E) = _
    rw [η'.bijOn_e.image_eq, Set.inter_assoc, Set.inter_eq_right.mpr hηsub.edgeSet_mono]

/-- Clearing a zone preserves a span if the cleared drawing is rigid.
This proves the assertion about `H', T'` in XVI (6.3), page 60. -/
theorem IsSigmaSpan.clear
    {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}
    {G : Graph α β} {H : Drawing S} {η : SpanEmbedding H G}
    {θ_star θ lam : ℕ} {Λ : Set S}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' : Set S → Set S → ℕ}
    (hSpan : IsSigmaSpan G H η θ_star θ T_star T)
    (hclear : IsClearedTangle H T d θ lam Λ T' d')
    (hrigid : IsRigid (clearedSubdrawing H Λ)) :
    IsSigmaSpan G (clearedSubdrawing H Λ) (restrictCleared η Λ)
      θ_star (θ - 4 * lam - 2) T_star T' := by
  have hT := hSpan.isControlling.isTangle_star
  have hforward : ∀ {A B : Hypergraph α β},
      (Hypergraph.ofGraph G hT.finite_V hT.finite_E).IsSeparation A B →
      separationOrder A B < θ - 4 * lam - 2 →
      ∀ {A' B'}, IsRestrictedSeparation (clearedSubdrawing H Λ) G
        (restrictCleared η Λ) A B A' B' →
      (A, B) ∈ T_star → (A', B') ∈ T' := by
    intro A B hsep hord A' B' hrestr hm
    have hrest := isRestrictedSeparation_spanPullback hT.finite_V hT.finite_E H η hsep
    have horder := restrictedSeparation_order_le hrest
    have hmem := (hSpan.isControlling.controls hsep (by omega) hrest).mp hm
    have hmem' := hclear.mem_of_order_lt _ _ hmem (horder.trans_lt hord)
    obtain ⟨ha, hb⟩ := restrictedSeparation_unique (restrictedSeparation_clear Λ hrest) hrestr
    rwa [ha, hb] at hmem'
  refine ⟨hSpan.isSurface, hSpan.isConnected, hSpan.bd_empty, hrigid,
    hclear.hasMetric.1, ⟨?_, hT, hclear.hasMetric.1.2.1, ?_⟩⟩
  · exact (Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans hSpan.isControlling.theta_le)
  · intro A B hsep hord A' B' hrestr
    refine ⟨hforward hsep hord hrestr, ?_⟩
    intro hm
    by_contra hnot
    have hordstar : separationOrder A B < θ_star :=
      hord.trans_le ((Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans hSpan.isControlling.theta_le))
    have hswap := (hT.isTangle.axiom1 hsep hordstar).resolve_left hnot
    have hrestrswap : IsRestrictedSeparation (clearedSubdrawing H Λ) G
        (restrictCleared η Λ) B A B' A' :=
      ⟨hrestr.1.symm, hrestr.2.2.2.1, hrestr.2.2.2.2, hrestr.2.1, hrestr.2.2.1⟩
    have hm' := hforward hsep.symm (by rwa [separationOrder_comm]) hrestrswap hswap
    exact GM10.theorem_2_1_proof hclear.hasMetric.1.2.1 hm hm'

end GraphMinor.GM16
