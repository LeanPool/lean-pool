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
import LeanPool.GraphMinor.GM12.Section4SpanSeparation

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
    obtain ⟨_, _, hrest, _, _, _, _, horder⟩ :=
      GM12.exists_span_restricted_separation hT.finite_V hT.finite_E H η hsep
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
