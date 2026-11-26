/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM15.Defs
import LeanPool.GraphMinor.GM10.TangleLemmas

/-!
# Pulling a separation back through a drawing embedding

To express XII (4.3), page 249, for an ambient graph with different
vertex and edge labels, pull each separation back to the drawing.
Restrict its vertex and edge sets along the embedding. Incidence
preservation makes the restrictions subhypergraphs. Their union
covers the drawing and their common edges are empty. Injectivity
on drawing vertices bounds the separator order.
-/

public section

namespace GraphMinor.GM12

open Set Graph Surface Hypergraph GM14 GM15 GM10

universe u v w

/-- Restrict an ambient separation to an embedded drawing, retaining
the exact preimage vertex and edge sets and bounding its order. -/
theorem exists_span_restricted_separation
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

end GraphMinor.GM12
