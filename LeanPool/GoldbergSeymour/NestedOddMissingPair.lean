/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.BoundaryMissingColorAugmentation

public import LeanPool.GoldbergSeymour.ElementaryClosedMissingColorOdd
public import LeanPool.GoldbergSeymour.MissingColorsNonemptyOfMaximumDegree
public import LeanPool.GoldbergSeymour.TreeColorSetMinusClosed

/-!
# P2940_T1_Nested Odd Missing Pair

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem P2940_T1_NestedOddMissingPair
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (phi : PartialEdgeColoring E k) (A U : TreeSequence G e0)
    (hproper : IsProperEdgeColoring G phi)
    (helem : ColoredVertexSetElementary G phi (TreeSequenceVertexSet U))
    (hAU : TreeSequenceInitialSegment A U) (hstrict : A.length < U.length)
    (hoddA : Odd (TreeSequenceVertexSet A).card)
    (hdegree : MaximumDegree G + 1 <= k)
    (D : Finset (Fin k)) (gamma : Fin k -> Finset (Fin k))
    (hreserved : forall eta, eta ∈ D -> gamma eta ⊆ TreeMissingColors phi A)
    (hdisjoint : forall eta theta, eta ∈ D -> theta ∈ D -> eta ≠ theta ->
      Disjoint (gamma eta) (gamma theta))
    (hgap : (D.biUnion gamma).card < (TreeMissingColors phi U).card)
    (hminus : TreeColorSetMinusClosed G phi U (D.biUnion gamma))
    (hnotClosed : Not (TreeColorSetClosed G phi U (TreeMissingColors phi U))) :
    exists (alpha beta eta gammaOne gammaTwo : Fin k) (f : E)
        (W : TreeSequence G e0),
      Odd (TreeSequenceVertexSet U).card /\
      alpha ∈ TreeMissingColors phi U \ D.biUnion gamma /\
      TreeColorSetClosed G phi U {alpha} /\
      beta ∈ TreeMissingColors phi U /\ beta ∈ D.biUnion gamma /\
      eta ∈ D /\ beta ∈ gamma eta /\
      (forall theta, theta ∈ D -> beta ∈ gamma theta -> theta = eta) /\
      f ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet U) beta /\
      phi f = some beta /\ TreeSequenceAdjoinEdge U f W /\
      TashkinovAugmentation phi U W /\ gammaOne ≠ gammaTwo /\
      gammaOne ∈ (TreeSequenceVertexSet U \ TreeSequenceVertexSet A).biUnion
        (MissingColors G phi) /\
      gammaTwo ∈ (TreeSequenceVertexSet U \ TreeSequenceVertexSet A).biUnion
        (MissingColors G phi) /\
      Disjoint {gammaOne, gammaTwo} (D.biUnion gamma) /\
      beta ∉ ({gammaOne, gammaTwo} : Finset (Fin k)) := by
  classical
  have halphaExists : (TreeMissingColors phi U \ D.biUnion gamma).Nonempty := by
    by_contra hn
    have hsub : TreeMissingColors phi U ⊆ D.biUnion gamma := by
      intro c hc
      by_contra hcnot
      exact hn ⟨c, Finset.mem_sdiff.mpr ⟨hc, hcnot⟩⟩
    have := Finset.card_le_card hsub
    omega
  obtain ⟨alpha, halpha⟩ := halphaExists
  have halphaClosed : TreeColorSetClosed G phi U {alpha} := by
    intro c hc
    have hcEq := Finset.mem_singleton.mp hc
    subst c
    exact hminus alpha halpha
  have hoddU := ElementaryClosedMissingColorOdd G k e0 phi U alpha
    hproper helem (Finset.mem_sdiff.mp halpha).1 halphaClosed
  have hsub := TreeSequenceInitialSegmentVertexSetSubset hAU
  have hcardA : (TreeSequenceVertexSet A).card = A.length + 1 := by
    simp [TreeSequenceVertexSet, Finset.card_image_of_injective, A.vertex_injective]
  have hcardU : (TreeSequenceVertexSet U).card = U.length + 1 := by
    simp [TreeSequenceVertexSet, Finset.card_image_of_injective, U.vertex_injective]
  have htwo : 1 < (TreeSequenceVertexSet U \ TreeSequenceVertexSet A).card := by
    rw [Finset.card_sdiff_of_subset hsub]
    obtain ⟨a, ha⟩ := hoddA
    obtain ⟨u, hu⟩ := hoddU
    omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp htwo
  obtain ⟨gammaOne, hg1x⟩ := MissingColorsNonemptyOfMaximumDegree G phi hdegree x
  obtain ⟨gammaTwo, hg2y⟩ := MissingColorsNonemptyOfMaximumDegree G phi hdegree y
  have hne : gammaOne ≠ gammaTwo := by
    intro heq
    have hd := helem (Finset.mem_sdiff.mp hx).1 (Finset.mem_sdiff.mp hy).1 hxy
    exact Finset.disjoint_left.mp hd hg1x (heq ▸ hg2y)
  have outside_not_reserved : forall v, v ∈ TreeSequenceVertexSet U \
      TreeSequenceVertexSet A -> forall c, c ∈ MissingColors G phi v ->
      c ∉ D.biUnion gamma := by
    intro v hv c hc hr
    obtain ⟨owner, ho, hco⟩ := Finset.mem_biUnion.mp hr
    obtain ⟨w, hw, hcw⟩ := Finset.mem_biUnion.mp (hreserved owner ho hco)
    have hvw : v ≠ w := by
      intro h
      exact (Finset.mem_sdiff.mp hv).2 (h ▸ hw)
    exact Finset.disjoint_left.mp
      (helem (Finset.mem_sdiff.mp hv).1 (hsub hw) hvw) hc hcw
  have hfresh : Disjoint {gammaOne, gammaTwo} (D.biUnion gamma) := by
    rw [Finset.disjoint_left]
    intro c hc hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with hc | hc
    · subst c
      exact outside_not_reserved x hx gammaOne hg1x hr
    · subst c
      exact outside_not_reserved y hy gammaTwo hg2y hr
  have hboundary : exists beta, beta ∈ TreeMissingColors phi U /\
      (BoundaryColorEdges G phi (TreeSequenceVertexSet U) beta).Nonempty := by
    by_contra hn
    apply hnotClosed
    intro beta hb
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hne
    exact hn ⟨beta, hb, hne⟩
  obtain ⟨beta, hbeta, f, hf⟩ := hboundary
  have hbReserved : beta ∈ D.biUnion gamma := by
    by_contra hn
    have hemp := hminus beta (Finset.mem_sdiff.mpr ⟨hbeta, hn⟩)
    exact Finset.notMem_empty f (hemp ▸ hf)
  obtain ⟨eta, heta, hbEta⟩ := Finset.mem_biUnion.mp hbReserved
  have howner : forall theta, theta ∈ D -> beta ∈ gamma theta -> theta = eta := by
    intro theta ht hb
    by_contra hne
    exact Finset.disjoint_left.mp (hdisjoint theta eta ht heta hne) hb hbEta
  have hfc : phi f = some beta := (Finset.mem_filter.mp hf).2
  obtain ⟨W, hadjoin, haug, _⟩ :=
    BoundaryMissingColorAugmentation G k e0 phi U beta f hf hbeta
  refine ⟨alpha, beta, eta, gammaOne, gammaTwo, f, W, hoddU, halpha,
    halphaClosed, hbeta, hbReserved, heta, hbEta, howner, hf, hfc, hadjoin,
    haug, hne, Finset.mem_biUnion.mpr ⟨x, hx, hg1x⟩,
    Finset.mem_biUnion.mpr ⟨y, hy, hg2y⟩, hfresh, ?_⟩
  intro hbPair
  exact Finset.disjoint_left.mp hfresh hbPair hbReserved

end GoldbergSeymour

end
