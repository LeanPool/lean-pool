/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.InterchangePETreeConstituent

public import LeanPool.GoldbergSeymour.OutsideKempeRecoloringStable

public import LeanPool.GoldbergSeymour.CopyAugmentationPrefix
public import LeanPool.GoldbergSeymour.OppositeRootComponents

/-!
# Interchange PEMixed Core

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem InterchangePEMixedCore {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating sigma : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hMP : MaximumProperty ett) (hpositive : 0 < ett.rounds)
    (hlower : LowerRoundInductionHypothesis G k e0 ett.rounds)
    (hPE : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE)
    (base : HierarchyBase ett generating)
    (hproper : IsProperEdgeColoring G sigma)
    (hone : IsOneEdgeUncolored sigma e0)
    (hstable : CombinedStableColoring
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      base.closure
      (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
      generating sigma)
    (alpha beta : Fin k) :
    let Tn := ett.series.data.tree (Fin.last ett.rounds).castSucc
    alpha ∈ TreeMissingColors sigma Tn →
      beta ∈ TreeMissingColors sigma base.closure →
      TreeInterchangeable G base.core sigma alpha beta := by
  classical
  dsimp
  intro halpha hbeta
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn := ett.series.data.tree n.castSucc
  let S := TreeSequencePrefix Tn base.supportPosition.val
    base.supportPositive (Nat.le_of_lt_succ base.supportPosition.isLt)
  have hSTn : TreeSequenceInitialSegment S Tn :=
    ⟨Nat.le_of_lt_succ base.supportPosition.isLt,
      (fun _ => rfl), (fun _ => rfl)⟩
  obtain ⟨hchosen, _, ⟨ord⟩⟩ := base.parallel hPE
  obtain ⟨hproperGen, honeGen, _⟩ := P2634_T1_PETerminalFacts ett hPE
  have hpreserved := CombinedStableClosurePreserved G k e0 input T
    generating generating sigma ett hpositive base ett.generatingColoring hPE
    hproperGen honeGen hproper hone hstable
  have hclosure : TashkinovClosure sigma S base.closure := hpreserved.2.2
  let baseSigma : HierarchyBase ett sigma := {
    core := base.core
    closure := base.closure
    supportPosition := base.supportPosition
    supportPositive := base.supportPositive
    terminalMissingColors := by
      dsimp
      ext c
      simp only [TreeMissingColors, Finset.mem_biUnion]
      constructor
      · rintro ⟨v, hv, hc⟩
        exact ⟨v, hv, by rw [← hstable.1.2 v hv]; exact hc⟩
      · rintro ⟨v, hv, hc⟩
        exact ⟨v, hv, by rw [hstable.1.2 v hv]; exact hc⟩
    parallel := fun hp => ⟨(base.parallel hp).1,
      hclosure, (base.parallel hp).2.2⟩
    nonparallel := base.nonparallel }
  have helem : ColoredVertexSetElementary G sigma
      (TreeSequenceVertexSet base.core) :=
    ParallelClosureUnionElementary G k e0 input T generating ett hMP
      hpositive hlower hPE sigma hproper hone hstable.1 baseSigma
  have hX : TreeInterchangeable G Tn sigma alpha beta :=
    InterchangePETreeConstituent G k e0 input T generating sigma ett hMP
      hpositive hlower hPE base hproper hone hstable alpha beta halpha
  have hgraph : TwoColorIncidenceGraph G sigma beta alpha =
      TwoColorIncidenceGraph G sigma alpha beta := by
    ext a b
    cases a <;> cases b <;> simp [TwoColorIncidenceGraph, or_comm]
  have hY : TreeInterchangeable G base.closure sigma alpha beta := by
    have hcomp : ∀ z, TwoColorComponent G sigma beta alpha z =
        TwoColorComponent G sigma alpha beta z := by
      intro z
      unfold TwoColorComponent
      rw [hgraph]
    have hrev := InterchangePEClosureConstituent G k e0 input T
      generating sigma ett hMP hpositive hlower hPE base hproper hone
      hstable beta alpha hbeta
    simpa only [TreeInterchangeable, TwoColorPathComponent,
      hcomp, hgraph, ne_comm] using hrev
  by_contra hnot
  obtain ⟨u, hu, hua⟩ := Finset.mem_biUnion.mp halpha
  obtain ⟨v, hv, hvb⟩ := Finset.mem_biUnion.mp hbeta
  obtain ⟨hab, huR, hvTn, avoidTn, _⟩ :=
    P2668_T2_OppositeRootComponents sigma alpha beta Tn base.closure
      base.core ⟨ord⟩ hproper hX hY u v hu hv hua hvb hnot
  let psi := TwoColorComponentSwap G sigma alpha beta (Sum.inl v)
  have hrecolor : OutsideKempeRecoloring Tn sigma psi alpha beta := by
    refine ⟨hab, {Sum.inl v}, ?_, ?_⟩
    · intro z hz x hxc hx
      have hzv : z = Sum.inl v := Finset.mem_singleton.mp hz
      subst z
      exact avoidTn x hx hxc
    · intro f
      simp [psi, TwoColorComponentSwap]
  obtain ⟨hproperPsi, honePsi, hchange, _, _⟩ :=
    OutsideKempeRecoloringStable G e0 Tn
      (TashkinovStoredColors ett.series.data n)
      sigma psi alpha beta hproper hone hrecolor
  have hterminal : StableColoring Tn
      (TashkinovStoredColors ett.series.data n) generating psi := by
    let a : {chi : PartialEdgeColoring E k //
        IsProperEdgeColoring G chi ∧ IsOneEdgeUncolored chi e0} :=
      ⟨generating, hproperGen, honeGen⟩
    let b : {chi : PartialEdgeColoring E k //
        IsProperEdgeColoring G chi ∧ IsOneEdgeUncolored chi e0} :=
      ⟨sigma, hproper, hone⟩
    let c : {chi : PartialEdgeColoring E k //
        IsProperEdgeColoring G chi ∧ IsOneEdgeUncolored chi e0} :=
      ⟨psi, hproperPsi, honePsi⟩
    have hab' : StableColoring Tn
        (TashkinovStoredColors ett.series.data n) a.1 b.1 := hstable.1
    have hbc' : StableColoring Tn
        (TashkinovStoredColors ett.series.data n) b.1 c.1 := hchange
    exact (sc2 G e0 Tn (TashkinovStoredColors ett.series.data n)).trans
      (x := a) (y := b) (z := c) hab' hbc'
  have huCore : u ∈ TreeSequenceVertexSet base.core := by
    rw [ord.vertexSet]
    exact Finset.mem_union_left _ hu
  have hRCore : TreeSequenceVertexSet base.closure ⊆
      TreeSequenceVertexSet base.core := by
    intro x hx
    rw [ord.vertexSet]
    exact Finset.mem_union_right _ hx
  have hvS : v ∉ TreeSequenceVertexSet S := by
    intro h
    exact hvTn (TreeSequenceInitialSegmentVertexSetSubset hSTn h)
  obtain ⟨B, _, hlast, hcopied⟩ :=
    P2668_T2_CopyAugmentationPrefix sigma alpha beta hab hproper
      (Sum.inl v) S base.closure (TreeSequenceVertexSet base.core)
      helem hRCore u v huCore huR hv hvS hua hvb hclosure.1
  obtain ⟨R', hR'⟩ := TashkinovClosureExists psi B
  have hnewClosure : TashkinovClosure psi S R' :=
    ⟨hcopied.trans hR'.1, hR'.2⟩
  obtain ⟨U', hU'⟩ := OrderedTreeUnionExists Tn R'
  let newBase : HierarchyBase ett psi := {
    core := U'
    closure := R'
    supportPosition := base.supportPosition
    supportPositive := base.supportPositive
    terminalMissingColors := by
      dsimp
      ext c
      simp only [TreeMissingColors, Finset.mem_biUnion]
      constructor
      · rintro ⟨x, hx, hc⟩
        exact ⟨x, hx, by rw [← hterminal.2 x hx]; exact hc⟩
      · rintro ⟨x, hx, hc⟩
        exact ⟨x, hx, by rw [hterminal.2 x hx]; exact hc⟩
    parallel := fun hp => ⟨(base.parallel hp).1, hnewClosure, hU'⟩
    nonparallel := by dsimp only; intro hn; exact (hn hPE).elim }
  have hnewElementary : ColoredVertexSetElementary G psi
      (TreeSequenceVertexSet U') :=
    ParallelClosureUnionElementary G k e0 input T generating ett hMP
      hpositive hlower hPE psi hproperPsi honePsi hterminal newBase
  obtain ⟨newOrd⟩ := hU'
  have hvB : v ∈ TreeSequenceVertexSet B := by
    rw [← hlast]
    simp [TreeSequenceVertexSet]
  have hvR' : v ∈ TreeSequenceVertexSet R' :=
    TreeSequenceInitialSegmentVertexSetSubset
      (TashkinovAugmentationSequenceInitialSegment psi B R' hR'.1) hvB
  have huU' : u ∈ TreeSequenceVertexSet U' := by
    rw [newOrd.vertexSet]
    exact Finset.mem_union_left _ hu
  have hvU' : v ∈ TreeSequenceVertexSet U' := by
    rw [newOrd.vertexSet]
    exact Finset.mem_union_right _ hvR'
  have huv : u ≠ v := by intro h; exact hvTn (h ▸ hu)
  have huaPsi : alpha ∈ MissingColors G psi u := by
    rw [hchange.2 u hu]
    exact hua
  have selfv : Sum.inl v ∈ TwoColorComponent G sigma alpha beta (Sum.inl v) :=
    SimpleGraph.ConnectedComponent.eq.mpr (SimpleGraph.Reachable.refl _)
  have hvaPsi : alpha ∈ MissingColors G psi v :=
    (TwoColorComponentSwapMissingBehavior G sigma alpha beta hab hproper
      (Sum.inl v)).2.2.1 v selfv hvb
  exact (Finset.disjoint_left.mp (hnewElementary huU' hvU' huv)) huaPsi hvaPsi

end GoldbergSeymour

end
