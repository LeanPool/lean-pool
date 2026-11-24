/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section6
import LeanPool.GraphMinor.GM16.AnnulusConnected
import LeanPool.GraphMinor.GM16.AnnulusPathIntersection
import LeanPool.GraphMinor.GM16.SpanAttachment
import LeanPool.GraphMinor.GM16.DrawingConnected
import LeanPool.GraphMinor.GM16.DrawingGraphPaths
import LeanPool.GraphMinor.GM16.Section9Zones
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM11.Section85
import LeanPool.GraphMinor.GM11.Section88

/-!
# Meeting a clean annulus gives the forbidden attachment

The path of Claim (11) crosses the clean annular subdrawing. The
annulus is connected and lies inside one cleared battlefield, so it
has no vertex in the cleared drawing. Its union with the clean path
therefore gives a clean attachment to any ambient path meeting it.
This is the implication used to prove XVI (8.1), Claim (14).
-/

public section
namespace GraphMinor.GM16
open Set Topology Graph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM11
  GraphMinor.GM14
universe u v w
variable {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
variable {α : Type u} {β : Type v}

/-- The substantive implication of XVI (8.1), Claim (14), page 74:
meeting the clean annulus gives a clean attachment to the bad path.
The annulus's connectedness and its intersection with the clean path
are both proved from the drawing data. -/
theorem section9_annular_intersection_gives_attachment (hS : IsClosedSurface S)
    {G P₀ : Graph α β} {H P : Drawing S} (η : SpanEmbedding H G)
    {Y : Set S} {Λ : S → Set S} {γ θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (hMet : HasTangleMetric H θ T d)
    (hZone : ∀ y ∈ Y, IsLambdaZoneAround H d γ {y} (Λ y))
    {y : S} (hy : y ∈ Y)
    (η' : SpanEmbedding (clearEnvelopeDrawing H Y Λ) G) (hMap : η'.vMap = η.vMap)
    {I O : Set S} {γI γO : ℕ} {a b : S} {X : Set S} {Z : Set α}
    (hI : IsLambdaZoneAround H d γI {y} I) (hO : IsLambdaZoneAround H d γO {y} O)
    (hNest : closure I ⊆ O) (hOuter : closure O ⊆ Λ y)
    (hP : P.IsSubdrawing H) (hPath : P.IsPathBetween b a) (hbX : b ∈ X)
    (ha : a ∈ O) (hb : b ∉ O)
    (hPClear : P.V ∩ (clearEnvelopeDrawing H Y Λ).V = {b})
    (hPZ : Disjoint P.V (H.V ∩ η.vMap ⁻¹' Z))
    (hClean : Disjoint (closure O \ I) (H.V ∩ η.vMap ⁻¹' Z))
    (hHit : (V(P₀) ∩ (η.vMap '' (H.interSet (closure O \ I)).V)).Nonempty) :
    ∃ c ∈ V(P₀), ∃ R : Graph α β,
      IsGraphPathWithEnds G R (η.vMap b) c ∧
      V(R) ∩ V(η'.imageGraph) ⊆ η.vMap '' X ∧ Disjoint V(R) Z := by
  let J := H.interSet (closure O \ I)
  have hJH : J.IsSubdrawing H := interSet_isSub
  have hJClosed : IsClosed (closure O \ I) := isClosed_closure.sdiff hI.isOpenDisc.1
  have hJInside : J.U ⊆ Λ y := fun _ hx => hOuter ((interSet_U_subset hJClosed hx).1)
  have haH : a ∈ H.V := hP.1 (graphPath_of_drawingPath hP hPath).right_mem
  have hH : IsGraphConnected H.toGraph :=
    ⟨⟨a, haH⟩, fun x hx z hz => drawing_walk_of_twoCell hS hMet.1.1 hx hz⟩
  have hConn : IsGraphConnected J.toGraph := annular_subdrawing_connected hS hI hO hNest hH
  have hMeet : (P.V ∩ J.V).Nonempty :=
    drawingPath_meets_annular_subdrawing hI hO hNest hP (drawingPath_symm hPath) ha hb
  have hJClear : Disjoint J.V (clearEnvelopeDrawing H Y Λ).V := by
    apply disjoint_left.mpr
    intro x hxJ hxClear
    have hxΛ := hJInside (J.V_subset_U hxJ)
    have hxOut := (clearFamily_U hZone ▸ (clearEnvelopeDrawing H Y Λ).V_subset_U hxClear).2
    exact hxOut (mem_iUnion₂.mpr ⟨y, hy, hxΛ⟩)
  have hPZ' : Disjoint (η.vMap '' P.V) Z := by
    apply disjoint_left.mpr
    rintro x ⟨z, hz, rfl⟩ hxZ
    exact hPZ.notMem_of_mem_left hz ⟨hP.1 hz, hxZ⟩
  have hJZ : Disjoint (η.vMap '' J.V) Z := by
    apply disjoint_left.mpr
    rintro x ⟨z, hz, rfl⟩ hxZ
    exact hClean.notMem_of_mem_left (interSet_U_subset hJClosed (J.V_subset_U hz))
      ⟨hJH.1 hz, hxZ⟩
  apply span_connected_extension_gives_attachment η η' interSet_isSub hMap
    hP hPath hJH hConn hMeet hHit _ hJClear hPZ' hJZ
  intro x hx
  have hxb : x = b := mem_singleton_iff.mp (hPClear ▸ hx)
  exact hxb ▸ hbX

end GraphMinor.GM16
