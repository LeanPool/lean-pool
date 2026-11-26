/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Defs
public import LeanPool.GraphMinor.GM11.Defs
import LeanPool.GraphMinor.GM16.Section6
import LeanPool.GraphMinor.GM16.SpanPaths
import LeanPool.GraphMinor.GM11.Walks
import LeanPool.GraphMinor.GM09.Basic

/-!
# Restricting a span embedding to a subdrawing

A subdrawing is spanned by its own vertices and edges. Restrict the
span embedding to that span and identify it with the given drawing.
The vertex and edge maps are retained, and the image graph is a
subgraph of the original image. This transfers the connected annulus
of XVI (8.1), Claim (14), to the ambient graph.
-/

public section
namespace GraphMinor.GM16
open Set Graph GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM06
universe u v w
variable {S : Type w} [TopologicalSpace S] [T2Space S]
variable {α : Type u} {β : Type v}

/-- Every subdrawing is the span of its own vertices and edges. -/
theorem span_subdrawing_eq {H J : Drawing S} (hJ : J.IsSubdrawing H) :
    H.span J.V J.E = J := by
  apply Drawing.ext_of_V_E
  · rw [H.span_V]
    change (J.V ∩ H.V) ∪ (⋃ e ∈ J.E ∩ H.E, closure e ∩ H.V) = J.V
    apply subset_antisymm
    · rintro x (hx | hx)
      · exact hx.1
      · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
        exact (hJ.closure_inter_V he.1 ▸ hxe).2
    · intro x hx
      exact Or.inl ⟨hx, hJ.1 hx⟩
  · rw [H.span_E]
    exact inter_eq_left.mpr hJ.2

omit [T2Space S] in
private theorem cast_embedding_fields {D E : Drawing S} (h : D = E)
    {G : Graph α β} (η : SpanEmbedding D G) :
    (h ▸ η).vMap = η.vMap ∧ (h ▸ η).eMap = η.eMap ∧
      (h ▸ η).imageGraph = η.imageGraph := by
  cases h
  exact ⟨rfl, rfl, rfl⟩

/-- Restrict a span embedding to any subdrawing while keeping its
vertex and edge maps. Its image is a subgraph of the old image. -/
theorem exists_spanEmbedding_subdrawing {H J : Drawing S} {G : Graph α β}
    (η : SpanEmbedding H G) (hJ : J.IsSubdrawing H) :
    ∃ ηJ : SpanEmbedding J G, ηJ.vMap = η.vMap ∧ ηJ.eMap = η.eMap ∧
      ηJ.imageGraph ≤ η.imageGraph := by
  let η₀ := restrictSpan η J.V J.E
  have hspan := span_subdrawing_eq hJ
  let ηJ : SpanEmbedding J G := hspan ▸ η₀
  obtain ⟨hv, he, hIm⟩ := cast_embedding_fields hspan η₀
  refine ⟨ηJ, hv, he, ?_⟩
  change (hspan ▸ η₀).imageGraph ≤ η.imageGraph
  rw [hIm]
  apply Graph.restrict_le.trans
  apply Graph.induce_le
  intro x hx
  obtain ⟨v, hv, rfl⟩ := hx
  exact η.bijOn_v.mapsTo ((H.spanV_subset J.V J.E) hv)

omit [T2Space S] in
/-- A span embedding carries a connected drawing to a connected
image graph. -/
theorem spanEmbedding_image_connected {H : Drawing S} {G : Graph α β}
    (η : SpanEmbedding H G) (hH : IsGraphConnected H.toGraph) :
    IsGraphConnected η.imageGraph := by
  constructor
  · obtain ⟨a, ha⟩ := hH.1
    exact ⟨η.vMap a, η.bijOn_v.mapsTo ha⟩
  · intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := η.bijOn_v.surjOn hx
    obtain ⟨b, hb, rfl⟩ := η.bijOn_v.surjOn hy
    obtain ⟨W⟩ := hH.2 a ha b hb
    exact ⟨mapSpanWalk η W⟩

omit [T2Space S] in
/-- A span embedding maps a drawing path to an ambient graph path
whose vertex set is exactly the image of the path's vertex set. -/
theorem exists_span_image_path {H P : Drawing S} {G : Graph α β}
    (η : SpanEmbedding H G) {a b : S} (hP : P.IsSubdrawing H)
    (hPath : P.IsPathBetween a b) :
    ∃ R : Graph α β, GraphMinor.GM09.IsGraphPathWithEnds G R (η.vMap a) (η.vMap b) ∧
      V(R) = η.vMap '' P.V ∧ R ≤ η.imageGraph := by
  obtain ⟨W, hW, hV, _⟩ := hPath
  obtain ⟨W', hs, _⟩ := hP.exists_walk_up W
  have hSimple : (mapSpanWalk η W').IsSimple := by
    change (mapSpanWalk η W').support.Nodup
    rw [mapSpanWalk_support]
    apply List.Nodup.map_on
    · intro x hx y hy heq
      exact η.bijOn_v.injOn (W'.mem_vertexSet_of_mem_support hx)
        (W'.mem_vertexSet_of_mem_support hy) heq
    · rw [hs]
      exact hW
  let R := GraphMinor.GM09.walkSubgraph (mapSpanWalk η W')
  have hR := GraphMinor.GM09.isGraphPathWithEnds_walkSubgraph hSimple
  refine ⟨R, hR.mono η.imageGraph_le, ?_, hR.1⟩
  change V(GraphMinor.GM09.walkSubgraph (mapSpanWalk η W')) = η.vMap '' P.V
  rw [GraphMinor.GM09.vertexSet_walkSubgraph, mapSpanWalk_support, hs, hV]
  ext x
  simp only [mem_ofPred_eq, List.mem_map, mem_image]

end GraphMinor.GM16
