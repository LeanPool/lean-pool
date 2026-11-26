/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
public import LeanPool.GraphMinor.GM06.Defs
import LeanPool.GraphMinor.GM16.SpanSubdrawing
import LeanPool.GraphMinor.GM16.ConnectedAttachment
import LeanPool.GraphMinor.GM16.DrawingGraphPaths

/-!
# Transporting the clean attachment through the span embedding

Map the clean path and the connected annular subdrawing into the
ambient graph. Injectivity of the vertex map preserves their
intersections with the cleared drawing. Their connected union then
gives the attachment forbidden in XVI (8.1), Claim (9), completing
the graph step used in Claim (14).
-/

public section
namespace GraphMinor.GM16
open Set Graph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM11 GraphMinor.GM14
universe u v w
variable {S : Type w} [TopologicalSpace S] [T2Space S]
variable {α : Type u} {β : Type v}

/-- A clean path joined to a clean connected subdrawing gives an
ambient attachment, with exactly the vertex-map interpretation of
its intersection with the cleared drawing. -/
theorem span_connected_extension_gives_attachment
    {G P₀ : Graph α β} {H H' P J : Drawing S}
    (η : SpanEmbedding H G) (η' : SpanEmbedding H' G)
    (hH' : H'.IsSubdrawing H) (hMap : η'.vMap = η.vMap)
    {a b : S} {X : Set S} {Z : Set α}
    (hP : P.IsSubdrawing H) (hPath : P.IsPathBetween a b)
    (hJ : J.IsSubdrawing H) (hConn : IsGraphConnected J.toGraph)
    (hMeet : (P.V ∩ J.V).Nonempty) (hHit : (V(P₀) ∩ (η.vMap '' J.V)).Nonempty)
    (hPClear : P.V ∩ H'.V ⊆ X) (hJClear : Disjoint J.V H'.V)
    (hPZ : Disjoint (η.vMap '' P.V) Z) (hJZ : Disjoint (η.vMap '' J.V) Z) :
    ∃ c ∈ V(P₀), ∃ Q : Graph α β,
      IsGraphPathWithEnds G Q (η.vMap a) c ∧
      V(Q) ∩ V(η'.imageGraph) ⊆ η.vMap '' X ∧ Disjoint V(Q) Z := by
  obtain ⟨R, hR, hRV, _⟩ := exists_span_image_path η hP hPath
  obtain ⟨ηJ, hηJv, _, _⟩ := exists_spanEmbedding_subdrawing η hJ
  have hJV : V(ηJ.imageGraph) = η.vMap '' J.V := by
    rw [← ηJ.bijOn_v.image_eq, hηJv]
  have hH'V : V(η'.imageGraph) = η.vMap '' H'.V := by
    rw [← η'.bijOn_v.image_eq, hMap]
  have hRMeet : (V(R) ∩ V(ηJ.imageGraph)).Nonempty := by
    obtain ⟨x, hxP, hxJ⟩ := hMeet
    rw [hRV, hJV]
    exact ⟨η.vMap x, mem_image_of_mem _ hxP, mem_image_of_mem _ hxJ⟩
  have hRHit : (V(P₀) ∩ V(ηJ.imageGraph)).Nonempty := hJV.symm ▸ hHit
  have hRInt : V(R) ∩ V(η'.imageGraph) ⊆ η.vMap '' X := by
    rw [hRV, hH'V, ← η.bijOn_v.injOn.image_inter hP.1 hH'.1]
    exact image_mono hPClear
  have hJInt : Disjoint V(ηJ.imageGraph) V(η'.imageGraph) := by
    rw [hJV, hH'V]
    apply disjoint_left.mpr
    rintro x ⟨v, hv, rfl⟩ ⟨w, hw, heq⟩
    have hwv := η.bijOn_v.injOn (hH'.1 hw) (hJ.1 hv) heq
    exact hJClear.notMem_of_mem_left hv (hwv ▸ hw)
  have hRZ : Disjoint V(R) Z := hRV.symm ▸ hPZ
  have hJZ' : Disjoint V(ηJ.imageGraph) Z := hJV.symm ▸ hJZ
  exact connected_extension_gives_attachment hR ηJ.imageGraph_le
    (spanEmbedding_image_connected ηJ hConn) hRMeet hRHit hRInt hJInt hRZ hJZ'

end GraphMinor.GM16
