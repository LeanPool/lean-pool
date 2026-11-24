/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM15.Defs

/-!
# Identifying restricted span embeddings

Successive clearings and clearing their union give the same drawing.
Their vertex and edge maps are unchanged. Since both images are
subgraphs of the same graph, these two maps determine the embedding,
and hence identify the corresponding span statements.
-/

public section
namespace GraphMinor.GM16
open Set Graph GraphMinor.Surface GraphMinor.GM14 GraphMinor.GM15
universe u v w

/-- Two embeddings of the same drawing into the same ambient graph
are equal when their vertex and edge maps agree. -/
theorem spanEmbedding_eq_of_maps {S : Type w} [TopologicalSpace S]
    {α : Type u} {β : Type v} {G : Graph α β} {H : Drawing S}
    (η η' : SpanEmbedding H G) (hv : η.vMap = η'.vMap) (he : η.eMap = η'.eMap) : η = η' := by
  have hV : V(η.imageGraph) = V(η'.imageGraph) := by
    rw [← η.bijOn_v.image_eq, ← η'.bijOn_v.image_eq, hv]
  have hE : E(η.imageGraph) = E(η'.imageGraph) := by
    rw [← η.bijOn_e.image_eq, ← η'.bijOn_e.image_eq, he]
  have hG : η.imageGraph = η'.imageGraph :=
    (Graph.Compatible.of_le_le η.imageGraph_le η'.imageGraph_le).ext hV hE
  cases η
  cases η'
  simp only at hv he hG
  cases hv
  cases he
  cases hG
  rfl

/-- Transport a span along equality of drawings and equality of its
vertex and edge maps. This is used for the iterated clearings in XVI. -/
theorem span_congr_drawing_embedding {S : Type w} [TopologicalSpace S] [T2Space S]
    {α : Type u} {β : Type v} {G : Graph α β} {H K : Drawing S}
    (hHK : H = K) (η : SpanEmbedding H G) (η' : SpanEmbedding K G)
    (hv : η.vMap = η'.vMap) (he : η.eMap = η'.eMap)
    {θ_star θ : ℕ} {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hSpan : IsSigmaSpan G H η θ_star θ T_star T) : IsSigmaSpan G K η' θ_star θ T_star T := by
  subst K
  exact spanEmbedding_eq_of_maps η η' hv he ▸ hSpan

end GraphMinor.GM16
