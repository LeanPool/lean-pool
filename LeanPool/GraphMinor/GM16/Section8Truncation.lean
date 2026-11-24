/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section8
import LeanPool.GraphMinor.GM16.MetricBounds
import LeanPool.GraphMinor.GM12.Section4WalkMetric

/-!
# Truncating animals in Graph Minors XVI

The same radial drawing and inside discs give the metric of a truncated tangle.
Its distances are the old distances cut off at the new order. Thus truncation
preserves an animal whose required strength is at most the new order, as used
in Claim (1) of the proof of XVI (8.3).
-/

public section
namespace GraphMinor.GM16
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15
open Hypergraph
universe u v w
variable {S : Type w} [TopologicalSpace S] [T2Space S]

/-- Truncation of a respectful drawing tangle cuts off its metric at the new order
(Graph Minors XVI, proof of (8.3), Claim (1), page 65). -/
theorem HasTangleMetric.truncation {H : Drawing S} {θ θ' : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (h : HasTangleMetric H θ T d)
    (hpos : 1 ≤ θ') (hle : θ' ≤ θ) :
    HasTangleMetric H θ' (GM10.truncation T θ') (fun a b => min (d a b) θ') := by
  classical
  obtain ⟨hresp, K, ins, hK, hins, hd⟩ := h
  refine ⟨IsRespectfulDrawingTangle.truncation hresp hpos hle, K, ins, hK, ?_, ?_⟩
  · intro C hC hCK hlen
    obtain ⟨hD, hbd, hmem⟩ := hins C hC hCK (lt_of_lt_of_le hlen (Nat.mul_le_mul_left 2 hle))
    refine ⟨hD, hbd, hmem, ?_⟩
    have hsub : (((PaintingOrDrawing.drawing H).inter (ins C)) ∩
        ((PaintingOrDrawing.drawing H).interOutside (ins C))).vertexSet ⊆ C.V ∩ H.V := by
      rintro x ⟨⟨hxH, hxD⟩, ⟨_, hxout⟩⟩
      have hxC : x ∈ C.U := hbd ▸ (show x ∈ subBd (ins C) from ⟨subset_closure hxD, hxout⟩)
      rw [C.U_eq] at hxC
      rcases hxC with hxCV | hxE
      · exact ⟨hxCV, hxH⟩
      · obtain ⟨e, heC, hxe⟩ := mem_iUnion₂.mp hxE
        have hxK := hK.2.1.2.1 hxH
        have hxCV : x ∈ closure e ∩ C.V := by
          rw [hCK.closure_inter_V heC]
          exact ⟨hxe, hxK⟩
        exact ⟨hxCV.2, hxH⟩
    have hc := (GM12.circuit_length_eq_two_mul_ncard hK.2.1 hC hCK).1
    have hcount := ncard_le_ncard hsub (C.finite_V.subset inter_subset_left)
    change (((PaintingOrDrawing.drawing H).inter (ins C)) ∩
        ((PaintingOrDrawing.drawing H).interOutside (ins C))).vertexSet.ncard < θ'
    omega
  · intro a ha b hb
    change min (d a b) θ' = _
    rw [hd a ha b hb, tangleMetric_truncation hK ins hle]

omit [T2Space S] in
/-- Restricting a separation to an embedded drawing cannot increase its order. -/
theorem restrictedSeparation_order_le {α : Type u} {β : Type v}
    {G : Graph α β} {H : Drawing S} {η : SpanEmbedding H G}
    {A B : Hypergraph α β} {A_H B_H : Hypergraph S (Set S)}
    (h : IsRestrictedSeparation H G η A B A_H B_H) :
    separationOrder A_H B_H ≤ separationOrder A B := by
  have hinj : Set.InjOn η.vMap (A_H ∩ B_H).vertexSet :=
    η.bijOn_v.injOn.mono (inter_subset_left.trans h.1.left_le.vertexSet_subset)
  have hsub : η.vMap '' (A_H ∩ B_H).vertexSet ⊆ (A ∩ B).vertexSet := by
    rintro x ⟨y, ⟨hyA, hyB⟩, rfl⟩
    have ha : η.vMap y ∈ η.vMap '' A_H.vertexSet := ⟨y, hyA, rfl⟩
    have hb : η.vMap y ∈ η.vMap '' B_H.vertexSet := ⟨y, hyB, rfl⟩
    rw [h.2.1] at ha
    rw [h.2.2.2.1] at hb
    exact ⟨ha.1, hb.1⟩
  have heq : (η.vMap '' (A_H ∩ B_H).vertexSet).ncard = separationOrder A_H B_H :=
    hinj.ncard_image
  rw [← heq]
  exact ncard_le_ncard hsub (A ∩ B).vertexSet_finite

/-- Truncating the tangle of a span preserves control by its ambient tangle
(Graph Minors XVI, proof of (8.3), Claim (1), page 65). -/
theorem IsSigmaSpan.truncation {α : Type u} {β : Type v}
    {G : Graph α β} {H : Drawing S} {η : SpanEmbedding H G}
    {θ_star θ θ' : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (h : IsSigmaSpan G H η θ_star θ T_star T) (hpos : 1 ≤ θ') (hle : θ' ≤ θ) :
    IsSigmaSpan G H η θ_star θ' T_star (GM10.truncation T θ') := by
  have hresp := IsRespectfulDrawingTangle.truncation h.isRespectful hpos hle
  refine ⟨h.isSurface, h.isConnected, h.bd_empty, h.isRigid, hresp,
    ⟨hle.trans h.isControlling.theta_le, h.isControlling.isTangle_star, hresp.2.1, ?_⟩⟩
  intro A B hsep hord A_H B_H hrestr
  have hc := h.isControlling.controls hsep (hord.trans_le hle) hrestr
  have hsmall := (restrictedSeparation_order_le hrestr).trans_lt hord
  exact ⟨fun hm => ⟨hc.mp hm, hsmall⟩, fun hm => hc.mpr hm.1⟩

/-- Graph Minors XVI, proof of (8.3), Claim (1), page 65: an animal of
strength `(θ, σ)` can be represented with its span order exactly `θ`.
Its metric is the original metric cut off at `θ`. -/
theorem theorem_8_3_claim_1 {α : Type u} {β : Type v}
    {G : Graph α β} {H : Drawing S} {η : SpanEmbedding H G}
    {θ_star θ_span χ δ θ σ : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {X : Set α} {Y : Set S}
    (h : IsAnimal G T_star θ_star H η θ_span T d X Y χ δ θ σ) :
    IsAnimal G T_star θ_star H η θ (GM10.truncation T θ)
      (fun a b => min (d a b) θ) X Y χ δ θ σ := by
  rcases h with ⟨hpos, hle, hspan, hmet, hX, hXcard, hY, hYcard, hhorn, hhair, hsep⟩
  refine ⟨hpos, le_rfl, IsSigmaSpan.truncation hspan hpos hle,
    HasTangleMetric.truncation hmet hpos hle, hX, hXcard, hY, hYcard, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨P, u, hvG, hu, hpath, hinter, hpair, hdist⟩ := hhorn v hv
    refine ⟨P, u, hvG, hu, hpath, hinter, hpair, ?_⟩
    intro i j hij
    exact le_min (hdist i j hij) le_rfl
  · intro y hy
    obtain ⟨v, P, hv, hne, hp, hd, hdist⟩ := hhair y hy
    exact ⟨v, P, hv, hne, hp, hd, le_min hdist le_rfl⟩
  · intro y₁ hy₁ y₂ hy₂ hne
    exact le_min (hsep y₁ hy₁ y₂ hy₂ hne) le_rfl

/-- Truncating twice is the same as truncating directly to the smaller order. -/
theorem truncation_truncation_eq {α : Type u} {β : Type v}
    (T : Set (Hypergraph α β × Hypergraph α β)) {a b : ℕ} (hle : b ≤ a) :
    GM10.truncation (GM10.truncation T a) b = GM10.truncation T b := by
  ext p
  constructor
  · exact fun h => ⟨h.1.1, h.2⟩
  · exact fun h => ⟨⟨h.1, h.2.trans_le hle⟩, h.2⟩

end GraphMinor.GM16
