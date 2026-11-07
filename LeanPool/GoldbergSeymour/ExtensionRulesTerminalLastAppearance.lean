/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovSeriesTreeFacts

public import LeanPool.GoldbergSeymour.ETTFirstAppearanceIndex
public import LeanPool.GoldbergSeymour.HkuMissingStoredMonotone
public import LeanPool.GoldbergSeymour.MaximumProperty
public import LeanPool.GoldbergSeymour.StableColoringBeforeVertex
public import LeanPool.GoldbergSeymour.TreeExitComponentMeetsTreeOnlyAtExit
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentVertexSetSubset

/-!
# Extension Rules Terminal Last Appearance

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_beforeInN_165.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating) (v : V)
      (hvFinal : v ∈ TreeSequenceVertexSet T) (j : Fin (ett.rounds + (1 : ℕ)))
      (hj : (↑j : ℕ) + (1 : ℕ) = ett.rounds),
    let q : Fin ett.rounds := (⟨(↑j : ℕ), by omega⟩ : Fin ett.rounds);
    let Tn : TreeSequence G e0 := ett.series.data.tree q.succ.castSucc;
    let B : Finset V := TreeVerticesBefore T v hvFinal;
    ∀ (_ : v ∈ TreeSequenceVertexSet Tn) (_ : TreeSequenceInitialSegment Tn T),
    ∀ w ∈ B,
    w ∈ TreeSequenceVertexSet Tn := by
  classical
  intro V E _ _ _ G k e0 input T generating ett v hvFinal j hj q Tn B hvN terminalSegment w hw
  unfold B TreeVerticesBefore at hw
  rcases Finset.mem_filter.mp hw with
    ⟨hwT, iw, iv, hiw, hiv, hlt⟩
  rcases Finset.mem_image.mp hwT with ⟨iwT, _, hiwT⟩
  rcases Finset.mem_image.mp hvN with ⟨ivN, _, hivN⟩
  rcases terminalSegment with ⟨hlen', hvertices', hedges'⟩
  let ivT := Fin.castLE (Nat.succ_le_succ hlen') ivN
  have hivEq : iv = ivT := by
    apply T.vertex_injective
    exact hiv.trans ((hvertices' ivN).trans hivN).symm
  have hiwEq : iwT = iw := by
    apply T.vertex_injective
    exact hiwT.trans hiw.symm
  have hiBound : iwT.val < Tn.length + 1 := by
    rw [hivEq, ← hiwEq] at hlt
    simp [ivT] at hlt
    omega
  let iwN : Fin (Tn.length + 1) := ⟨iwT.val, hiBound⟩
  apply Finset.mem_image.mpr
  refine ⟨iwN, Finset.mem_univ _, ?_⟩
  have hcast : Fin.castLE (Nat.succ_le_succ hlen') iwN = iwT := by
    apply Fin.ext
    rfl
  exact (hvertices' iwN).symm.trans (by simpa [hcast] using hiwT)

private theorem helper_swapFixed_204.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (v : V) (hvFinal : v ∈ TreeSequenceVertexSet T) (j : Fin
        (ett.rounds + (1 : ℕ))) (hj : (↑j : ℕ) + (1 : ℕ) = ett.rounds),
    let q : Fin ett.rounds := (⟨(↑j : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (secondStable : PartialEdgeColoring E k) (choice : MaximumDefectiveChoice G
        e0 (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors ett.series.data
        q.castSucc) (ett.series.data.coloring q.castSucc)),
    let Tn : TreeSequence G e0 := ett.series.data.tree q.succ.castSucc;
    let B : Finset V := TreeVerticesBefore T v hvFinal;
    ∀ (_ : (
    ∀ w ∈ B, w ∈ TreeSequenceVertexSet Tn)) (_ : (
    ∀ w ∈ B, w ≠ choice.vertex)) (_ : (
    ∀ w ∈ TreeSequenceVertexSet Tn, Sum.inl w ∈ TwoColorComponent G secondStable gamma
        choice.color (Sum.inl choice.vertex) ↔ w = choice.vertex)) (f : E) (_ : (
    ∃ w ∈ B, Incident G w f)), TwoColorComponentSwap G secondStable gamma choice.color (Sum.inl
        choice.vertex) f = secondStable f := by
  classical
  intro V E _ _ _ G k e0 input T generating ett v hvFinal j hj q gamma secondStable choice Tn B
      beforeInN beforeNe componentOnly f hf
  rcases hf with ⟨w, hw, hwf⟩
  have hfOutside : Sum.inr f ∉
      TwoColorComponent G secondStable gamma choice.color
        (Sum.inl choice.vertex) := by
    intro hfComponent
    let graph := TwoColorIncidenceGraph G secondStable gamma choice.color
    have hfSupport : Sum.inr f ∈ graph.support := by
      apply SimpleGraph.mem_support_of_reachable
        (G := graph) (u := Sum.inr f) (v := Sum.inl choice.vertex)
      · simp
      · exact SimpleGraph.ConnectedComponent.eq.mp hfComponent
    obtain ⟨z, hz⟩ := graph.mem_support.mp hfSupport
    have hfColor : secondStable f = some gamma ∨
        secondStable f = some choice.color := by
      cases z with
      | inl z => exact hz.2
      | inr z => simp [graph, TwoColorIncidenceGraph] at hz
    have hwComponent : Sum.inl w ∈
        TwoColorComponent G secondStable gamma choice.color
          (Sum.inl choice.vertex) := by
      change graph.connectedComponentMk (Sum.inl w) =
        graph.connectedComponentMk (Sum.inl choice.vertex)
      exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        (by simp [graph, TwoColorIncidenceGraph, hwf, hfColor])).trans
          hfComponent
    exact beforeNe w hw
      ((componentOnly w (beforeInN w hw)).mp hwComponent)
  simp [TwoColorComponentSwap, hfOutside]

private theorem helper_currentEdgeEq_274.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (v : V) (hvFinal : v ∈ TreeSequenceVertexSet T) (j : Fin
        (ett.rounds + (1 : ℕ))) (hj : (↑j : ℕ) + (1 : ℕ) = ett.rounds) (_ : (
    ∀ {A : TreeSequence G e0} {C : Finset (Fin k)} {phi pi : PartialEdgeColoring E k} (_ :
        StableColoring A C phi pi), TreeMissingColors pi A = TreeMissingColors phi A)),
    let q : Fin ett.rounds := (⟨(↑j : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (secondStable : PartialEdgeColoring E k) (choice : MaximumDefectiveChoice G
        e0 (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors ett.series.data
        q.castSucc) (ett.series.data.coloring q.castSucc)) (_ : StableColoring
        (ett.series.data.tree q.succ.castSucc) (insert choice.color (TashkinovStoredColors
        ett.series.data q.castSucc)) choice.selected secondStable) (_ : ett.series.data.coloring
        q.succ = TwoColorComponentSwap G secondStable gamma choice.color (Sum.inl choice.vertex)),
    let Tn : TreeSequence G e0 := ett.series.data.tree q.succ.castSucc;
    let B : Finset V := TreeVerticesBefore T v hvFinal;
    ∀ (_ : (
    ∀ w ∈ B, w ∈ TreeSequenceVertexSet Tn)) (_ : (
    ∀ (f : E) (_ : (
    ∃ w ∈ B, Incident G w f)), TwoColorComponentSwap G secondStable gamma choice.color (Sum.inl
        choice.vertex) f = secondStable f)) (_ : (
    ∀ c ∈ (B.biUnion fun (w : V) => MissingColors G (ett.series.data.coloring q.castSucc) w) ∪
        TashkinovStoredColors ett.series.data q.castSucc, c ∈ TreeMissingColors
        (ett.series.data.coloring q.castSucc) Tn ∪ TashkinovStoredColors ett.series.data
        q.castSucc)) (f : E) (_ : (
    ∃ w ∈ B, Incident G w f)) (_ : (
    ∃ c ∈ (B.biUnion fun (w : V) => MissingColors G (ett.series.data.coloring q.castSucc) w) ∪
        TashkinovStoredColors ett.series.data q.castSucc, ett.series.data.coloring q.castSucc f =
        some c)), ett.series.data.coloring q.succ f = ett.series.data.coloring q.castSucc f := by
  classical
  intro V E _ _ _ G k e0 input T generating ett v hvFinal j hj stableTreeMissingEq q gamma
      secondStable choice secondStableRelation currentColoring Tn B beforeInN swapFixed
      oldControlInN f hf hcolor
  rcases hcolor with ⟨c, hc, hcf⟩
  have hfN : TreeIncidentEdge Tn f := by
    rcases hf with ⟨w, hw, hwf⟩
    exact ⟨w, beforeInN w hw, hwf⟩
  have hcN := oldControlInN c hc
  have hselected : choice.selected f =
      ett.series.data.coloring q.castSucc f :=
    choice.selectedStable.1 f hfN ⟨c, hcN, hcf⟩
  have hcSecond : c ∈
      TreeMissingColors choice.selected Tn ∪
        insert choice.color
          (TashkinovStoredColors ett.series.data q.castSucc) := by
    rcases Finset.mem_union.mp hcN with hcN | hcN
    · apply Finset.mem_union.mpr
      left
      rw [stableTreeMissingEq choice.selectedStable]
      exact hcN
    · exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_insert_of_mem hcN))
  have hsecond : secondStable f = choice.selected f :=
    secondStableRelation.1 f hfN
      ⟨c, hcSecond, hselected.trans hcf⟩
  calc
    ett.series.data.coloring q.succ f =
        TwoColorComponentSwap G secondStable gamma choice.color
          (Sum.inl choice.vertex) f := congrFun currentColoring f
    _ = secondStable f := swapFixed f hf
    _ = choice.selected f := hsecond
    _ = ett.series.data.coloring q.castSucc f := hselected

private theorem helper_branch_350.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (v : V) (hvFinal : v ∈ TreeSequenceVertexSet T) (j : Fin
        (ett.rounds + (1 : ℕ))) (_ : ETTFirstAppearanceIndex ett v hvFinal = (↑j : ℕ) + (1 : ℕ))
        (hj : (↑j : ℕ) + (1 : ℕ) = ett.rounds) (sigma : PartialEdgeColoring E k),
    let _ : DecidableEq V := Classical.decEq V;
    ∀ (_ : (
    ∀ (a : Fin (ett.rounds + (1 : ℕ))) (_ : (0 : ℕ) < (↑a : ℕ)), TreeSequenceInitialSegment
        (ett.series.data.tree a.castSucc) (ett.series.data.tree a.succ))) (_ : (
    ∀ {A B : TreeSequence G e0} (_ : TreeSequenceInitialSegment A B) (u w : V) (_ :
        TreeVertexOrder A u w), TreeVertexOrder B u w)),
    let q : Fin ett.rounds := (⟨(↑j : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (_ : q.castSucc = j),
    let Tn : TreeSequence G e0 := ett.series.data.tree q.succ.castSucc;
    let _ : Finset V := TreeVerticesBefore T v hvFinal;
    ∀ (_ : v ∈ TreeSequenceVertexSet Tn) (_ : TreeSequenceInitialSegment Tn T) (_ :
        StableColoringBeforeVertex T v hvFinal (TashkinovStoredColors ett.series.data q.castSucc)
        (ett.series.data.coloring q.castSucc) sigma) (_ : (0 : ℕ) < (↑j : ℕ)), StableColoring
        (ett.series.data.tree j.castSucc) (TashkinovStoredColors ett.series.data j)
        (ett.series.data.coloring j) sigma := by
  classical
  intro V E _ _ _ G k e0 input T generating ett v hvFinal j hfirst hj sigma this stepSegment
      orderTransfer q hqj Tn B hvN terminalSegment beforeStableQ hjPositive
  have hqPositive : 0 < q.val := by
    simpa [q] using hjPositive
  let Tprev := ett.series.data.tree q.castSucc.castSucc
  have prevToN : TreeSequenceInitialSegment Tprev Tn := by
    have hs := stepSegment q.castSucc (by simpa using hqPositive)
    simpa [Tprev, Tn] using hs
  have hvNotPrev : v ∉ TreeSequenceVertexSet Tprev := by
    intro hvPrev
    let r : Fin ett.rounds := ⟨q.val - 1, by omega⟩
    have hrq : r.succ = q.castSucc := by
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_castSucc]
      exact Nat.sub_add_cancel hqPositive
    have hvStage : v ∈ TreeSequenceVertexSet
        (ExtendedTashkinovLadderStage ett r.castSucc) := by
      rw [show ExtendedTashkinovLadderStage ett r.castSucc =
          ett.series.data.tree r.succ.castSucc by
        unfold ExtendedTashkinovLadderStage
        exact @Fin.lastCases_castSucc ett.rounds
          (fun _ : Fin (ett.rounds + 1) => TreeSequence G e0) T
          (fun a => ett.series.data.tree a.succ.castSucc) r]
      rw [hrq]
      exact hvPrev
    have hbound : ETTFirstAppearanceIndex ett v hvFinal ≤
        q.val := by
      unfold ETTFirstAppearanceIndex
      dsimp
      have hmem : r.castSucc ∈
          Finset.univ.filter
            (fun a : Fin (ett.rounds + 1) =>
              v ∈ TreeSequenceVertexSet
                (ExtendedTashkinovLadderStage ett a)) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hvStage
      have hle := Finset.min'_le
        (Finset.univ.filter
          (fun a : Fin (ett.rounds + 1) =>
            v ∈ TreeSequenceVertexSet
              (ExtendedTashkinovLadderStage ett a))) r.castSucc hmem
      have hnat := Fin.le_iff_val_le_val.mp hle
      rw [Fin.val_castSucc] at hnat
      calc
        _ + 1 ≤ r.val + 1 := Nat.succ_le_succ hnat
        _ = q.val := by
          simp only [r]
          exact Nat.sub_add_cancel hqPositive
    have hfirstQ : ETTFirstAppearanceIndex ett v hvFinal =
        q.val + 1 := by
      simpa [q] using hfirst
    omega
  have prevInBefore : ∀ w : V, w ∈ TreeSequenceVertexSet Tprev →
      w ∈ B := by
    intro w hw
    have hwN := TreeSequenceInitialSegmentVertexSetSubset prevToN hw
    have hwT := TreeSequenceInitialSegmentVertexSetSubset
      terminalSegment hwN
    apply Finset.mem_filter.mpr
    refine ⟨hwT, ?_⟩
    rcases prevToN with ⟨hlen, hvertices, _⟩
    rcases Finset.mem_image.mp hw with ⟨iw, _, hiw⟩
    rcases Finset.mem_image.mp hvN with ⟨iv, _, hiv⟩
    have hleniv : Tprev.length < iv.val := by
      by_contra hnot
      have hivBound : iv.val < Tprev.length + 1 := by omega
      let ivPrev : Fin (Tprev.length + 1) := ⟨iv.val, hivBound⟩
      apply hvNotPrev
      apply Finset.mem_image.mpr
      refine ⟨ivPrev, Finset.mem_univ _, ?_⟩
      calc
        Tprev.vertex ivPrev =
            Tn.vertex (Fin.castLE (Nat.succ_le_succ hlen) ivPrev) :=
          (hvertices ivPrev).symm
        _ = Tn.vertex iv := by
          congr 1
        _ = v := hiv
    have horderN : TreeVertexOrder Tn w v := by
      refine ⟨Fin.castLE (Nat.succ_le_succ hlen) iw, iv,
        (hvertices iw).trans hiw, hiv, ?_⟩
      have hiwBound : iw.val ≤ Tprev.length := by omega
      simp only [Fin.val_castLE]
      omega
    exact orderTransfer terminalSegment w v horderN
  have stablePrevQ : StableColoring Tprev
      (TashkinovStoredColors ett.series.data q.castSucc)
      (ett.series.data.coloring q.castSucc) sigma := by
    constructor
    · intro f hf hcolor
      rcases hf with ⟨w, hw, hwf⟩
      rcases hcolor with ⟨c, hc, hcf⟩
      apply beforeStableQ.1 f ⟨w, prevInBefore w hw, hwf⟩
      refine ⟨c, ?_, hcf⟩
      rcases Finset.mem_union.mp hc with hc | hc
      · apply Finset.mem_union.mpr
        left
        simp only [TreeMissingColors, Finset.mem_biUnion] at hc
        rcases hc with ⟨z, hz, hzc⟩
        simp only [Finset.mem_biUnion]
        exact ⟨z, prevInBefore z hz, hzc⟩
      · exact Finset.mem_union.mpr (Or.inr hc)
    · intro w hw
      exact beforeStableQ.2 w (prevInBefore w hw)
  simpa [Tprev, hqj] using stablePrevQ

private theorem helper_swapMissing_482.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (v : V) (hvFinal : v ∈ TreeSequenceVertexSet T) (j : Fin
        (ett.rounds + (1 : ℕ))) (hj : (↑j : ℕ) + (1 : ℕ) = ett.rounds),
    let q : Fin ett.rounds := (⟨(↑j : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (secondStable : PartialEdgeColoring E k) (choice : MaximumDefectiveChoice G
        e0 (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors ett.series.data
        q.castSucc) (ett.series.data.coloring q.castSucc)),
    let B : Finset V := TreeVerticesBefore T v hvFinal;
    ∀ (_ : (
    ∀ (f : E) (_ : (
    ∃ w ∈ B, Incident G w f)), TwoColorComponentSwap G secondStable gamma choice.color (Sum.inl
        choice.vertex) f = secondStable f)),
    ∀ w ∈ B, MissingColors G (TwoColorComponentSwap G secondStable gamma choice.color (Sum.inl
        choice.vertex)) w = MissingColors G secondStable w := by
  classical
  intro V E _ _ _ G k e0 input T generating ett v hvFinal j hj q gamma secondStable choice B
      swapFixed w hw
  apply Finset.ext
  intro c
  simp only [MissingColors, PresentColors, Finset.mem_sdiff,
    Finset.mem_univ, true_and, Finset.mem_filter]
  constructor
  · intro hc
    rintro ⟨f, hwf, hfc⟩
    apply hc
    exact ⟨f, hwf, by
      rw [swapFixed f ⟨w, hw, hwf⟩]
      exact hfc⟩
  · intro hc
    rintro ⟨f, hwf, hfc⟩
    apply hc
    exact ⟨f, hwf, by
      rw [← swapFixed f ⟨w, hw, hwf⟩]
      exact hfc⟩

private theorem helper_currentMissingEq_528.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (v : V) (hvFinal : v ∈ TreeSequenceVertexSet T) (j : Fin
        (ett.rounds + (1 : ℕ))) (hj : (↑j : ℕ) + (1 : ℕ) = ett.rounds),
    let q : Fin ett.rounds := (⟨(↑j : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (secondStable : PartialEdgeColoring E k) (choice : MaximumDefectiveChoice G
        e0 (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors ett.series.data
        q.castSucc) (ett.series.data.coloring q.castSucc)) (_ : StableColoring
        (ett.series.data.tree q.succ.castSucc) (insert choice.color (TashkinovStoredColors
        ett.series.data q.castSucc)) choice.selected secondStable) (_ : ett.series.data.coloring
        q.succ = TwoColorComponentSwap G secondStable gamma choice.color (Sum.inl choice.vertex)),
    let Tn : TreeSequence G e0 := ett.series.data.tree q.succ.castSucc;
    let B : Finset V := TreeVerticesBefore T v hvFinal;
    ∀ (_ : (
    ∀ w ∈ B, w ∈ TreeSequenceVertexSet Tn)) (_ : (
    ∀ w ∈ B, MissingColors G (TwoColorComponentSwap G secondStable gamma choice.color (Sum.inl
        choice.vertex)) w = MissingColors G secondStable w)),
    ∀ w ∈ B, MissingColors G (ett.series.data.coloring q.succ) w = MissingColors G
        (ett.series.data.coloring q.castSucc) w := by
  classical
  intro V E _ _ _ G k e0 input T generating ett v hvFinal j hj q gamma secondStable choice
      secondStableRelation currentColoring Tn B beforeInN swapMissing w hw
  calc
    MissingColors G (ett.series.data.coloring q.succ) w =
        MissingColors G
          (TwoColorComponentSwap G secondStable gamma choice.color
            (Sum.inl choice.vertex)) w :=
      congrArg (fun phi => MissingColors G phi w) currentColoring
    _ = MissingColors G secondStable w := swapMissing w hw
    _ = MissingColors G choice.selected w :=
      secondStableRelation.2 w (beforeInN w hw)
    _ = MissingColors G (ett.series.data.coloring q.castSucc) w :=
      choice.selectedStable.2 w (beforeInN w hw)

private theorem helper_beforeStableQ_545.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (v : V) (hvFinal : v ∈ TreeSequenceVertexSet T) (j : Fin
        (ett.rounds + (1 : ℕ))) (hj : (↑j : ℕ) + (1 : ℕ) = ett.rounds) (sigma :
        PartialEdgeColoring E k),
    let q : Fin ett.rounds := (⟨(↑j : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    let Tn : TreeSequence G e0 := ett.series.data.tree q.succ.castSucc;
    let B : Finset V := TreeVerticesBefore T v hvFinal;
    ∀ (_ : StableColoring Tn (TashkinovStoredColors ett.series.data q.succ)
        (ett.series.data.coloring q.succ) sigma) (_ : (
    ∀ w ∈ B, w ∈ TreeSequenceVertexSet Tn)) (_ : (
    ∀ c ∈ (B.biUnion fun (w : V) => MissingColors G (ett.series.data.coloring q.castSucc) w) ∪
        TashkinovStoredColors ett.series.data q.castSucc, c ∈ TreeMissingColors
        (ett.series.data.coloring q.castSucc) Tn ∪ TashkinovStoredColors ett.series.data
        q.castSucc)) (_ : (
    ∀ (f : E) (_ : (
    ∃ w ∈ B, Incident G w f)) (_ : (
    ∃ c ∈ (B.biUnion fun (w : V) => MissingColors G (ett.series.data.coloring q.castSucc) w) ∪
        TashkinovStoredColors ett.series.data q.castSucc, ett.series.data.coloring q.castSucc f =
        some c)), ett.series.data.coloring q.succ f = ett.series.data.coloring q.castSucc f)) (_ :
        (
    ∀ w ∈ B, MissingColors G (ett.series.data.coloring q.succ) w = MissingColors G
        (ett.series.data.coloring q.castSucc) w)) (_ : TreeMissingColors (ett.series.data.coloring
        q.castSucc) (ett.series.data.tree q.succ.castSucc) ∪ TashkinovStoredColors ett.series.data
        q.castSucc ⊆ TreeMissingColors (ett.series.data.coloring q.succ) (ett.series.data.tree
        q.succ.castSucc) ∪ TashkinovStoredColors ett.series.data q.succ),
        StableColoringBeforeVertex T v hvFinal (TashkinovStoredColors ett.series.data q.castSucc)
        (ett.series.data.coloring q.castSucc) sigma := by
  classical
  intro V E _ _ _ G k e0 input T generating ett v hvFinal j hj sigma q Tn B hstableN beforeInN
      oldControlInN currentEdgeEq currentMissingEq hmonotone
  unfold StableColoringBeforeVertex
  change (∀ f, (∃ w ∈ B, Incident G w f) → _ → _) ∧ _
  constructor
  · intro f hf hcolor
    rcases hcolor with ⟨c, hc, hcf⟩
    have hfN : TreeIncidentEdge Tn f := by
      rcases hf with ⟨w, hw, hwf⟩
      exact ⟨w, beforeInN w hw, hwf⟩
    have hcN := oldControlInN c hc
    have hcurrent := currentEdgeEq f hf ⟨c, hc, hcf⟩
    have hsigma : sigma f = ett.series.data.coloring q.succ f :=
      hstableN.1 f hfN
        ⟨c, hmonotone hcN, hcurrent.trans hcf⟩
    exact hsigma.trans hcurrent
  · intro w hw
    exact (hstableN.2 w (beforeInN w hw)).trans
      (currentMissingEq w hw)

private theorem helper_branch_153.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [
    Fintype E] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input :
    PartialEdgeColoring E k) (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating) (v : V) (hvFinal : v ∈
    TreeSequenceVertexSet T) (j : Fin (ett.rounds + (1 : ℕ))), ETTFirstAppearanceIndex ett v
    hvFinal = (↑j : ℕ) + (1 : ℕ) → ∀ (hj : (↑j : ℕ) + (1 : ℕ) = ett.rounds) (sigma :
    PartialEdgeColoring E k), StableColoring (ett.series.data.tree (Fin.last
    ett.rounds).castSucc) (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
    (ett.series.data.coloring (Fin.last ett.rounds)) sigma → (∀ (a : Fin (ett.rounds + (1 :
    ℕ))), (0 : ℕ) < (↑a : ℕ) → TreeSequenceInitialSegment (ett.series.data.tree a.castSucc)
    (ett.series.data.tree a.succ)) → (∀ {A B : TreeSequence G e0}, TreeSequenceInitialSegment
    A B → ∀ (u w : V), TreeVertexOrder A u w → TreeVertexOrder B u w) → (∀ {A : TreeSequence G
    e0} {C : Finset (Fin k)} {phi pi : PartialEdgeColoring E k}, StableColoring A C phi pi →
    TreeMissingColors pi A = TreeMissingColors phi A) → ((⟨(↑j : ℕ), by omega⟩ : Fin
    ett.rounds) : Fin ett.rounds).castSucc = j → ((⟨(↑j : ℕ), by omega⟩ : Fin ett.rounds) :
    Fin ett.rounds).succ = Fin.last ett.rounds → ett.series.data.chosenVertex ((⟨(↑j : ℕ), by
    omega⟩ : Fin ett.rounds) : Fin ett.rounds).succ = some v → ∀ (ci : Fin ett.rounds),
    IsProperEdgeColoring G (ett.series.data.coloring ci.castSucc) → IsOneEdgeUncolored
    (ett.series.data.coloring ci.castSucc) e0 → ColoredVertexSetClosed G
    (ett.series.data.coloring ci.castSucc) (TreeSequenceVertexSet (ett.series.data.tree
    ci.succ.castSucc)) → ¬ColoredVertexSetStronglyClosed G (ett.series.data.coloring
    ci.castSucc) (TreeSequenceVertexSet (ett.series.data.tree ci.succ.castSucc)) → ¬Nonempty
    (RevisitingExtensionCertificate ett.series.data ci.castSucc) → ∀ (choice :
    MaximumDefectiveChoice G e0 (ett.series.data.tree ci.succ.castSucc) (TashkinovStoredColors
    ett.series.data ci.castSucc) (ett.series.data.coloring ci.castSucc)), (∃ (rho :
    PartialEdgeColoring E k), IsProperEdgeColoring G rho ∧ IsOneEdgeUncolored rho e0 ∧
    StableColoring (ett.series.data.tree ci.succ.castSucc) (insert choice.color
    (TashkinovStoredColors ett.series.data ci.castSucc)) choice.selected rho ∧ ¬Disjoint
    (MissingColors G rho choice.otherEndpoint) (TreeMissingColors rho (ett.series.data.tree
    ci.succ.castSucc))) → ∀ (gamma : Fin k), ParallelExtensionColor ett.series.data
    ci.castSucc choice.selected choice.vertex gamma → ∀ (secondStable : PartialEdgeColoring E
    k), IsProperEdgeColoring G secondStable → StableColoring (ett.series.data.tree
    ci.succ.castSucc) (insert choice.color (TashkinovStoredColors ett.series.data
    ci.castSucc)) choice.selected secondStable → TreeExit (ett.series.data.tree
    ci.succ.castSucc) secondStable gamma choice.color choice.vertex → ett.series.data.coloring
    ci.succ = TwoColorComponentSwap G secondStable gamma choice.color (Sum.inl choice.vertex)
    → IsProperEdgeColoring G (ett.series.data.coloring ci.succ) → IsOneEdgeUncolored
    (ett.series.data.coloring ci.succ) e0 → ett.series.data.stored ci.succ = {choice.color,
    gamma} → ett.series.data.connectingEdges ci.succ = {choice.edge} → ett.series.data.kind
    ci.succ = some TashkinovExtensionKind.PE → ett.series.data.chosenVertex ci.succ = some
    choice.vertex → ett.series.data.outsideVertex ci.succ = some choice.otherEndpoint →
    ett.series.data.delta ci.succ = some choice.color → ett.series.data.gamma ci.succ = some
    gamma → TashkinovClosure (ett.series.data.coloring ci.succ) (ett.series.data.tree
    ci.succ.castSucc) (ett.series.data.tree ci.succ.succ) → TreeSequenceInitialSegment
    (ett.series.data.tree ci.succ.castSucc) (ett.series.data.tree ci.succ.succ) →
    (ett.series.data.tree ci.succ.castSucc).length < (ett.series.data.tree
    ci.succ.succ).length → ((⟨(↑j : ℕ), by omega⟩ : Fin ett.rounds) : Fin ett.rounds).succ =
    ci.succ → StableColoringBeforeVertex T v hvFinal (TashkinovStoredColors ett.series.data j)
    (ett.series.data.coloring j) sigma ∧ ((0 : ℕ) < (↑j : ℕ) → StableColoring
    (ett.series.data.tree j.castSucc) (TashkinovStoredColors ett.series.data j)
    (ett.series.data.coloring j) sigma) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett v hvFinal j hfirst hj sigma hstable
  let this : DecidableEq V :=
    Classical.decEq V
  intro stepSegment orderTransfer stableTreeMissingEq
  set q : Fin ett.rounds := (⟨(↑j : ℕ), by omega⟩ : Fin ett.rounds)
  intro hqj hqn hvertexQ ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails gamma gammaRule
      secondStable secondStableProper secondStableRelation exitWitness currentColoring
      currentProper currentOneUncolored currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma closedExtension orderedExtension strictExtension
      htarget
  have hci : ci = q := by
    apply Fin.ext
    simpa using (congrArg Fin.val htarget).symm
  subst ci
  have hvchoice : choice.vertex = v :=
    Option.some.inj
      (currentVertex.symm.trans (by simpa [htarget] using hvertexQ))
  let Tn := ett.series.data.tree q.succ.castSucc
  let B := TreeVerticesBefore T v hvFinal
  have hvN : v ∈ TreeSequenceVertexSet Tn := by
    simpa [Tn, hvchoice] using choice.vertexDefective.1
  have hstableN : StableColoring Tn
      (TashkinovStoredColors ett.series.data q.succ)
      (ett.series.data.coloring q.succ) sigma := by
    simpa [Tn, hqn] using hstable
  have terminalSegment : TreeSequenceInitialSegment Tn T := by
    have hindex : q.succ.castSucc =
        (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2)) := by
      apply Fin.ext
      simpa using congrArg Fin.val hqn
    change TreeSequenceInitialSegment
      (ett.series.data.tree q.succ.castSucc) T
    rw [hindex]
    exact ett.abovePenultimate
  have beforeInN :=
    @helper_beforeInN_165 V E inferInstance inferInstance inferInstance G k e0 input T
        generating ett v hvFinal j hj hvN terminalSegment
  have beforeNe : ∀ w : V, w ∈ B → w ≠ choice.vertex := by
    intro w hw heq
    unfold B TreeVerticesBefore at hw
    have horder := (Finset.mem_filter.mp hw).2
    have heqv : w = v := heq.trans hvchoice
    rcases horder with ⟨a, b, ha, hb, hab⟩
    have : a = b := T.vertex_injective (ha.trans (heqv ▸ hb).symm)
    omega
  have hgammaMissing : gamma ∈ MissingColors G secondStable choice.vertex := by
    rw [secondStableRelation.2 choice.vertex choice.vertexDefective.1]
    exact gammaRule.1
  have componentOnly := TreeExitComponentMeetsTreeOnlyAtExit Tn secondStable
    gamma choice.color choice.vertex secondStableProper hgammaMissing exitWitness
  have swapFixed :=
    @helper_swapFixed_204 V E inferInstance inferInstance inferInstance G k e0 input T
        generating ett v hvFinal j hj gamma secondStable choice beforeInN beforeNe componentOnly
  have swapMissing :=
    @helper_swapMissing_482 V E inferInstance inferInstance inferInstance G k e0 input T
        generating ett v hvFinal j hj gamma secondStable choice swapFixed
  have oldControlInN :
    ∀ c : Fin k, c ∈ (B.biUnion fun w => MissingColors G (ett.series.data.coloring q.castSucc) w)
        ∪ TashkinovStoredColors ett.series.data q.castSucc → c ∈ TreeMissingColors
        (ett.series.data.coloring q.castSucc) Tn ∪ TashkinovStoredColors ett.series.data
        q.castSucc := by
    intro c hc
    rcases Finset.mem_union.mp hc with hc | hc
    · apply Finset.mem_union.mpr
      left
      simp only [Finset.mem_biUnion] at hc
      rcases hc with ⟨w, hw, hc⟩
      simp only [TreeMissingColors, Finset.mem_biUnion]
      exact ⟨w, beforeInN w hw, hc⟩
    · exact Finset.mem_union.mpr (Or.inr hc)
  have currentEdgeEq :=
    @helper_currentEdgeEq_274 V E inferInstance inferInstance inferInstance G k e0 input T
        generating ett v hvFinal j hj stableTreeMissingEq gamma secondStable choice
        secondStableRelation currentColoring beforeInN swapFixed oldControlInN
  have currentMissingEq :=
    @helper_currentMissingEq_528 V E inferInstance inferInstance inferInstance G k e0 input
        T generating ett v hvFinal j hj gamma secondStable choice secondStableRelation
        currentColoring beforeInN swapMissing
  have hmonotone :=
    (HkuMissingStoredMonotone G k ett.rounds e0 input ett.series q).1
  have beforeStableQ :=
    @helper_beforeStableQ_545 V E inferInstance inferInstance inferInstance G k e0 input T
        generating ett v hvFinal j hj sigma hstableN beforeInN oldControlInN currentEdgeEq
        currentMissingEq hmonotone
  constructor
  · simpa [hqj] using beforeStableQ
  · exact @helper_branch_350 V E inferInstance inferInstance inferInstance G k e0 input T
      generating ett v hvFinal j hfirst hj sigma stepSegment orderTransfer hqj hvN
      terminalSegment beforeStableQ
theorem ExtensionRulesTerminalLastAppearance {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (_ : MaximumProperty ett) (_ : 0 < ett.rounds)
    (v : V)
    (hkind : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE)
    (hvertex : ett.series.data.chosenVertex (Fin.last ett.rounds) = some v)
    (hvFinal : v ∈ TreeSequenceVertexSet T)
    (j : Fin (ett.rounds + 1))
    (hfirst : ETTFirstAppearanceIndex ett v hvFinal = j.val + 1)
    (hj : j.val + 1 = ett.rounds)
    (sigma : PartialEdgeColoring E k)
    (_ : IsProperEdgeColoring G sigma)
    (_ : IsOneEdgeUncolored sigma e0)
    (hstable : StableColoring
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
      (ett.series.data.coloring (Fin.last ett.rounds)) sigma) :
    StableColoringBeforeVertex T v hvFinal
        (TashkinovStoredColors ett.series.data j)
        (ett.series.data.coloring j) sigma ∧
      (0 < j.val →
        StableColoring (ett.series.data.tree j.castSucc)
          (TashkinovStoredColors ett.series.data j)
          (ett.series.data.coloring j) sigma) := by
  classical
  let : DecidableEq V := Classical.decEq V
  have stepSegment : ∀ a : Fin (ett.rounds + 1), 0 < a.val →
      TreeSequenceInitialSegment (ett.series.data.tree a.castSucc)
        (ett.series.data.tree a.succ) := by
    intro a ha
    exact ett.series.positiveStepInitialSegment a ha
  have orderTransfer : ∀ {A B : TreeSequence G e0},
      TreeSequenceInitialSegment A B → ∀ u w,
        TreeVertexOrder A u w → TreeVertexOrder B u w := by
    intro A B hAB u w huw
    rcases hAB with ⟨hlen, hvertices, _⟩
    rcases huw with ⟨iu, iw, hu, hw, hi⟩
    exact ⟨Fin.castLE (Nat.succ_le_succ hlen) iu,
      Fin.castLE (Nat.succ_le_succ hlen) iw,
      (hvertices iu).trans hu, (hvertices iw).trans hw, hi⟩
  have stableTreeMissingEq :
    ∀ {A : TreeSequence G e0} {C : Finset (Fin k)} {phi pi : PartialEdgeColoring E k},
        StableColoring A C phi pi → TreeMissingColors pi A = TreeMissingColors phi A := by
    intro A C phi pi h
    ext c
    simp only [TreeMissingColors, Finset.mem_biUnion]
    constructor
    · rintro ⟨w, hw, hc⟩
      rw [h.2 w hw] at hc
      exact ⟨w, hw, hc⟩
    · rintro ⟨w, hw, hc⟩
      rw [← h.2 w hw] at hc
      exact ⟨w, hw, hc⟩
  let q : Fin ett.rounds := ⟨j.val, by omega⟩
  have hqj : q.castSucc = j := by
    apply Fin.ext
    rfl
  have hqn : q.succ = Fin.last ett.rounds := by
    apply Fin.ext
    simp [q]
    omega
  have hkindQ : ett.series.data.kind q.succ =
      some TashkinovExtensionKind.PE := by
    rw [hqn]
    exact hkind
  have hvertexQ : ett.series.data.chosenVertex q.succ = some v := by
    rw [hqn]
    exact hvertex
  generalize htarget : q.succ = target
  cases ett.series.certified target with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
    exact (Fin.succ_ne_zero q htarget).elim
  | SE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    have hbad : some TashkinovExtensionKind.SE =
        some TashkinovExtensionKind.PE :=
      currentKind.symm.trans (by simpa [htarget] using hkindQ)
    cases hbad
  | RE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    have hbad : some TashkinovExtensionKind.RE =
        some TashkinovExtensionKind.PE :=
      currentKind.symm.trans (by simpa [htarget] using hkindQ)
    cases hbad
  | PE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper
      secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma closedExtension orderedExtension strictExtension =>
          exact @helper_branch_153 V E inferInstance inferInstance inferInstance G k e0 input T
              generating ett v hvFinal j hfirst hj sigma hstable stepSegment orderTransfer
              stableTreeMissingEq hqj hqn hvertexQ ci previousProper previousOneUncolored
              previousClosed previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
              gamma gammaRule secondStable secondStableProper secondStableRelation exitWitness
              currentColoring currentProper currentOneUncolored currentStored currentEdges
              currentKind currentVertex currentOutside currentDelta currentGamma closedExtension
              orderedExtension strictExtension htarget
end GoldbergSeymour

end
