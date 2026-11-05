/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovHierarchy

/-!
# Hierarchy Nonparallel First Edge

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem HierarchyNonparallelFirstEdge {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {phi : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input T phi}
    {base : HierarchyBase ett phi} (H : TashkinovHierarchy ett base)
    (f : E)
    (hkind : ett.series.data.kind (Fin.last ett.rounds) =
        some TashkinovExtensionKind.SE ∨
      ett.series.data.kind (Fin.last ett.rounds) =
        some TashkinovExtensionKind.RE)
    (hedges : ett.series.data.connectingEdges (Fin.last ett.rounds) = {f}) :
    let Tn := ett.series.data.tree (Fin.last ett.rounds).castSucc
    ∃ r : Fin (H.stage ⟨1, by omega⟩).length,
      r.val = Tn.length ∧ (H.stage ⟨1, by omega⟩).edge r = f := by
  classical
  dsimp
  have segmentTrans {A B C : TreeSequence G e0}
      (hAB : TreeSequenceInitialSegment A B)
      (hBC : TreeSequenceInitialSegment B C) :
      TreeSequenceInitialSegment A C := by
    rcases hAB with ⟨hab, hvab, heab⟩
    rcases hBC with ⟨hbc, hvbc, hebc⟩
    refine ⟨le_trans hab hbc, ?_, ?_⟩
    · intro i
      have hmid := hvbc (Fin.castLE (Nat.succ_le_succ hab) i)
      have hfirst := hvab i
      simpa using hmid.trans hfirst
    · intro i
      have hmid := hebc (Fin.castLE hab i)
      have hfirst := heab i
      simpa using hmid.trans hfirst
  have chain : ∀ q : ℕ, (hq : q ≤ H.dividerCount) →
      TreeSequenceInitialSegment (H.stage ⟨1, by omega⟩)
        (H.stage ⟨1 + q, by omega⟩) := by
    intro q
    induction q with
    | zero =>
        intro hq
        exact ⟨le_rfl, (by intro i; rfl), (by intro i; rfl)⟩
    | succ q ih =>
        intro hq
        have hprev := ih (by omega)
        have hnext := H.nested ⟨1 + q, by omega⟩
        have hnext' : TreeSequenceInitialSegment
            (H.stage ⟨1 + q, by omega⟩)
            (H.stage ⟨1 + (q + 1), by omega⟩) := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnext
        exact segmentTrans hprev hnext'
  have stageToT : TreeSequenceInitialSegment
      (H.stage ⟨1, by omega⟩) T := by
    have hc := chain H.dividerCount (le_rfl)
    have hi : (⟨1 + H.dividerCount, by omega⟩ : Fin (H.dividerCount + 2)) =
        Fin.last (H.dividerCount + 1) := by
      apply Fin.ext
      simp [Nat.add_comm]
    rw [hi] at hc
    simpa [H.terminalStage] using hc
  have stageToFinal : TreeSequenceInitialSegment
      (H.stage ⟨1, by omega⟩)
      (ett.series.data.tree (Fin.last (ett.rounds + 1))) :=
    segmentTrans stageToT ett.belowFinal
  have reachSegment {A B : TreeSequence G e0} {coloring : PartialEdgeColoring E k}
      (hseq : TashkinovAugmentationSequence coloring A B) :
      TreeSequenceInitialSegment A B := by
    unfold TashkinovAugmentationSequence at hseq
    induction hseq using Relation.ReflTransGen.head_induction_on with
    | refl =>
        exact ⟨le_rfl, (by intro i; rfl), (by intro i; rfl)⟩
    | @head A B hstep htail ih =>
        rcases hstep with ⟨hlen, hseg, color, hedge, hmissing⟩
        exact segmentTrans hseg ih
  let terminalIndex : Fin (ett.rounds + 1) := Fin.last ett.rounds
  change ett.series.data.kind terminalIndex =
      some TashkinovExtensionKind.SE ∨
    ett.series.data.kind terminalIndex =
      some TashkinovExtensionKind.RE at hkind
  have terminalFact :
    ∀ (j : Fin (ett.rounds + 1)), ett.series.data.kind j = some TashkinovExtensionKind.SE ∨
        ett.series.data.kind j = some TashkinovExtensionKind.RE →
    ∀ g : E, ett.series.data.connectingEdges j = {g} →
    ∃ A : TreeSequence G e0,
    ∃ hlen : A.length = (ett.series.data.tree j.castSucc).length + 1, TreeSequenceInitialSegment
        (ett.series.data.tree j.castSucc) A ∧ TreeSequenceInitialSegment A (ett.series.data.tree
        j.succ) ∧ A.edge (Fin.cast hlen.symm (Fin.last (ett.series.data.tree j.castSucc).length))
        = g := by
    intro j hj g hconnect
    have cert := ett.series.certified j
    cases cert with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma
        initialClosure =>
      rcases hj with hj | hj
      · rw [initialKind] at hj
        simp at hj
      · rw [initialKind] at hj
        simp at hj
    | SE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
      refine ⟨adjoined, adjoinedExactly.1, adjoinedExactly.2.1,
        reachSegment closedExtension.1, ?_⟩
      have hmem' : choice.edge ∈
          ett.series.data.connectingEdges i.succ := by
        rw [currentEdges]
        simp
      have hmem : choice.edge ∈ ({g} : Finset E) := by
        rw [hconnect] at hmem'
        exact hmem'
      exact adjoinedExactly.2.2.trans (Finset.mem_singleton.mp hmem)
    | PE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
        gamma gammaRule secondStable secondStableProper
        secondStableOneUncolored secondStableRelation exitWitness
        currentColoring currentProper currentOneUncolored currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma closedExtension orderedExtension strictExtension =>
      rcases hj with hj | hj
      · rw [currentKind] at hj
        simp at hj
      · rw [currentKind] at hj
        simp at hj
    | RE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma adjoined adjoinedExactly closedExtension orderedExtension
        strictExtension =>
      refine ⟨adjoined, adjoinedExactly.1, adjoinedExactly.2.1,
        reachSegment closedExtension.1, ?_⟩
      have hmem' : available.edge ∈
          ett.series.data.connectingEdges i.succ := by
        rw [currentEdges]
        simp
      have hmem : available.edge ∈ ({g} : Finset E) := by
        rw [hconnect] at hmem'
        exact hmem'
      exact adjoinedExactly.2.2.trans (Finset.mem_singleton.mp hmem)
  have terminalEdges : ett.series.data.connectingEdges terminalIndex = {f} := by
    simpa [terminalIndex] using hedges
  obtain ⟨adjoined, adjoinedLength, adjoinedInitial, adjoinedFinal, adjoinedEdge⟩ :=
    terminalFact terminalIndex hkind f terminalEdges
  have hkindIndex : terminalIndex.succ = Fin.last (ett.rounds + 1) := by
    apply Fin.ext
    simp [terminalIndex]
  have hbaseTree :
      ett.series.data.tree terminalIndex.castSucc =
        ett.series.data.tree (Fin.last ett.rounds).castSucc := by
    rfl
  have hfinalEdge :
        (ett.series.data.tree (Fin.last (ett.rounds + 1))).edge
          (Fin.castLE adjoinedFinal.1
            (Fin.cast adjoinedLength.symm
              (Fin.last (ett.series.data.tree terminalIndex.castSucc).length))) = f := by
      have hadge := adjoinedFinal.2.2
        (Fin.cast adjoinedLength.symm
          (Fin.last (ett.series.data.tree terminalIndex.castSucc).length))
      have htree : ett.series.data.tree terminalIndex.succ =
          ett.series.data.tree (Fin.last (ett.rounds + 1)) := by
        rw [hkindIndex]
      cases htree
      exact hadge.trans adjoinedEdge
  have hstrict := H.strict 0
  have hbase := H.baseStage
  have hstageLen :
      (ett.series.data.tree terminalIndex.castSucc).length <
        (H.stage ⟨1, by omega⟩).length := by
    rw [← hbase]
    exact hstrict
  let r : Fin (H.stage ⟨1, by omega⟩).length :=
    ⟨(ett.series.data.tree terminalIndex.castSucc).length, hstageLen⟩
  have htransfer := stageToFinal.2.2 r
  have hidx :
      Fin.castLE stageToFinal.1 r =
        Fin.castLE adjoinedFinal.1
          (Fin.cast adjoinedLength.symm
            (Fin.last (ett.series.data.tree terminalIndex.castSucc).length)) := by
    apply Fin.ext
    rfl
  refine ⟨r, rfl, ?_⟩
  change (H.stage ⟨1, by omega⟩).edge r = f
  calc
    (H.stage ⟨1, by omega⟩).edge r =
        (ett.series.data.tree (Fin.last (ett.rounds + 1))).edge
          (Fin.castLE stageToFinal.1 r) := htransfer.symm
    _ = (ett.series.data.tree (Fin.last (ett.rounds + 1))).edge
          (Fin.castLE adjoinedFinal.1
            (Fin.cast adjoinedLength.symm
              (Fin.last (ett.series.data.tree terminalIndex.castSucc).length))) := by
      rw [hidx]
    _ = f := hfinalEdge

end GoldbergSeymour

end
