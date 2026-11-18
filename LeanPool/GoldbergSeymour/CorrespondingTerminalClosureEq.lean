/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTree
public import LeanPool.GoldbergSeymour.TashkinovClosureVertexSetUnique
public import LeanPool.GoldbergSeymour.TreeSequenceAdjoinEdgeUnique
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentVertexSetEq

/-!
# Corresponding Terminal Closure Eq

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem CorrespondingTerminalClosureEq
    {V E : Type*} [Fintype V] [Fintype E]
     [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (sigmaN : PartialEdgeColoring E k) (Tstar seed : TreeSequence G e0)
    (corr : CorrespondingExtendedTashkinovTree G k e0 ett sigmaN Tstar)
    (seedRoute :
      (ett.series.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.PE /\
        seed = ett.series.data.tree (Fin.last ett.rounds).castSucc) \/
      ((ett.series.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.SE \/
        ett.series.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.RE) /\
        exists f : E,
          ett.series.data.connectingEdges (Fin.last ett.rounds) = {f} /\
          TreeSequenceAdjoinEdge
            (ett.series.data.tree (Fin.last ett.rounds).castSucc) f seed))
    (chosenClosure : TashkinovClosure sigmaN seed Tstar) :
    corr.replacementSeries.data.tree (Fin.last (ett.rounds + 1)) = Tstar := by
  classical
  rcases corr with ⟨replacementInput, replacementSeries, replacementETT,
    rungAgreement, seriesPresentation, finalGeneratingColoring,
    ladderTreesAgree, storedColorsAgree, connectingEdgesAgree,
    extensionKindsAgree, replacementProper, replacementOneUncolored,
    replacementStable⟩
  cases replacementETT with
  | mk rounds roundsPositive replacementData above strict below generating =>
    cases rungAgreement
    have seriesSame : replacementData = replacementSeries :=
      eq_of_heq seriesPresentation
    cases seriesSame
    let q : Fin ett.rounds :=
      ⟨ett.rounds - 1,
        Nat.sub_lt (Nat.zero_lt_of_lt ett.roundsPositive) (by omega)⟩
    have hq : q.succ = Fin.last ett.rounds := by
      apply Fin.ext
      exact Nat.sub_add_cancel ett.roundsPositive
    have hq2 : q.succ.succ = Fin.last (ett.rounds + 1) := by
      rw [hq]
      rfl
    have ladderEq : replacementSeries.data.tree
          (Fin.last ett.rounds).castSucc =
        ett.series.data.tree (Fin.last ett.rounds).castSucc := by
      rw [← hq]
      exact ladderTreesAgree q
    have kindEq : replacementSeries.data.kind (Fin.last ett.rounds) =
        ett.series.data.kind (Fin.last ett.rounds) :=
      extensionKindsAgree (Fin.last ett.rounds)
    have edgesEq : replacementSeries.data.connectingEdges (Fin.last ett.rounds) =
        ett.series.data.connectingEdges (Fin.last ett.rounds) :=
      connectingEdgesAgree (Fin.last ett.rounds)
    have finalStep := replacementSeries.certified (Fin.last ett.rounds)
    generalize finalIndex : Fin.last ett.rounds = target at finalStep
    cases finalStep with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma
        initialClosure =>
      have hnone : replacementSeries.data.kind (Fin.last ett.rounds) = none := by
        rw [finalIndex, initialKind]
      rcases seedRoute with hPE | hSER
      · rw [← kindEq, hnone] at hPE
        cases hPE.1
      · rcases hSER.1 with hSE | hRE
        · rw [← kindEq, hnone] at hSE
          cases hSE
        · rw [← kindEq, hnone] at hRE
          cases hRE
    | SE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
      have hi : i = q := by
        apply Fin.ext
        have hv := congrArg Fin.val finalIndex
        simp [q] at hv ⊢
        omega
      subst i
      have newKind : replacementSeries.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.SE := by
        rw [← hq]
        exact currentKind
      rcases seedRoute with hPE | hSER
      · have : (some TashkinovExtensionKind.SE) =
            some TashkinovExtensionKind.PE := by
          calc
            some TashkinovExtensionKind.SE =
                replacementSeries.data.kind (Fin.last ett.rounds) := newKind.symm
            _ = ett.series.data.kind (Fin.last ett.rounds) := kindEq
            _ = some TashkinovExtensionKind.PE := hPE.1
        cases this
      · rcases hSER with ⟨oldKind, f, oldEdges, oldAdjoined⟩
        have edgeSingleton : ({choice.edge} : Finset E) = {f} := by
          calc
            {choice.edge} = replacementSeries.data.connectingEdges
                (Fin.last ett.rounds) := by rw [← hq, currentEdges]
            _ = ett.series.data.connectingEdges (Fin.last ett.rounds) := edgesEq
            _ = {f} := oldEdges
        have edgeEq : choice.edge = f := by simpa using edgeSingleton
        have newAdjoined : TreeSequenceAdjoinEdge
            (ett.series.data.tree (Fin.last ett.rounds).castSucc) f adjoined := by
          rw [← ladderEq, ← edgeEq, ← hq]
          exact adjoinedExactly
        have adjoinedEq : adjoined = seed :=
          TreeSequenceAdjoinEdgeUnique _ _ _ _ newAdjoined oldAdjoined
        have newClosure : TashkinovClosure sigmaN seed
            (replacementSeries.data.tree (Fin.last (ett.rounds + 1))) := by
          rw [← adjoinedEq, finalGeneratingColoring, ← hq, ← hq2]
          simpa using closedExtension
        have vertexEq : TreeSequenceVertexSet Tstar =
            TreeSequenceVertexSet
              (replacementSeries.data.tree (Fin.last (ett.rounds + 1))) :=
          TashkinovClosureVertexSetUnique sigmaN seed Tstar _
            chosenClosure newClosure
        exact (TreeSequenceInitialSegmentVertexSetEq Tstar _ below vertexEq).symm
    | PE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
        gamma gammaRule secondStable secondStableProper secondStableOneUncolored
        secondStableRelation exitWitness currentColoring currentProper
        currentOneUncolored currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma closedExtension orderedExtension
        strictExtension =>
      have hi : i = q := by
        apply Fin.ext
        have hv := congrArg Fin.val finalIndex
        simp [q] at hv ⊢
        omega
      subst i
      have newKind : replacementSeries.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.PE := by
        rw [← hq]
        exact currentKind
      rcases seedRoute with hPE | hSER
      · have seedEq : seed =
            replacementSeries.data.tree (Fin.last ett.rounds).castSucc :=
          hPE.2.trans ladderEq.symm
        have newClosure : TashkinovClosure sigmaN seed
            (replacementSeries.data.tree (Fin.last (ett.rounds + 1))) := by
          rw [seedEq, finalGeneratingColoring, ← hq, ← hq2]
          simpa using closedExtension
        have vertexEq : TreeSequenceVertexSet Tstar =
            TreeSequenceVertexSet
              (replacementSeries.data.tree (Fin.last (ett.rounds + 1))) :=
          TashkinovClosureVertexSetUnique sigmaN seed Tstar _
            chosenClosure newClosure
        exact (TreeSequenceInitialSegmentVertexSetEq Tstar _ below vertexEq).symm
      · rcases hSER.1 with hSE | hRE
        · have : (some TashkinovExtensionKind.PE) =
              some TashkinovExtensionKind.SE := by
            calc
              some TashkinovExtensionKind.PE =
                  replacementSeries.data.kind (Fin.last ett.rounds) := newKind.symm
              _ = ett.series.data.kind (Fin.last ett.rounds) := kindEq
              _ = some TashkinovExtensionKind.SE := hSE
          cases this
        · have : (some TashkinovExtensionKind.PE) =
              some TashkinovExtensionKind.RE := by
            calc
              some TashkinovExtensionKind.PE =
                  replacementSeries.data.kind (Fin.last ett.rounds) := newKind.symm
              _ = ett.series.data.kind (Fin.last ett.rounds) := kindEq
              _ = some TashkinovExtensionKind.RE := hRE
          cases this
    | RE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma adjoined adjoinedExactly closedExtension orderedExtension
        strictExtension =>
      have hi : i = q := by
        apply Fin.ext
        have hv := congrArg Fin.val finalIndex
        simp [q] at hv ⊢
        omega
      subst i
      have newKind : replacementSeries.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.RE := by
        rw [← hq]
        exact currentKind
      rcases seedRoute with hPE | hSER
      · have : (some TashkinovExtensionKind.RE) =
            some TashkinovExtensionKind.PE := by
          calc
            some TashkinovExtensionKind.RE =
                replacementSeries.data.kind (Fin.last ett.rounds) := newKind.symm
            _ = ett.series.data.kind (Fin.last ett.rounds) := kindEq
            _ = some TashkinovExtensionKind.PE := hPE.1
        cases this
      · rcases hSER with ⟨oldKind, f, oldEdges, oldAdjoined⟩
        have edgeSingleton : ({available.edge} : Finset E) = {f} := by
          calc
            {available.edge} = replacementSeries.data.connectingEdges
                (Fin.last ett.rounds) := by rw [← hq, currentEdges]
            _ = ett.series.data.connectingEdges (Fin.last ett.rounds) := edgesEq
            _ = {f} := oldEdges
        have edgeEq : available.edge = f := by simpa using edgeSingleton
        have newAdjoined : TreeSequenceAdjoinEdge
            (ett.series.data.tree (Fin.last ett.rounds).castSucc) f adjoined := by
          rw [← ladderEq, ← edgeEq, ← hq]
          exact adjoinedExactly
        have adjoinedEq : adjoined = seed :=
          TreeSequenceAdjoinEdgeUnique _ _ _ _ newAdjoined oldAdjoined
        have newClosure : TashkinovClosure sigmaN seed
            (replacementSeries.data.tree (Fin.last (ett.rounds + 1))) := by
          rw [← adjoinedEq, finalGeneratingColoring, ← hq, ← hq2]
          simpa using closedExtension
        have vertexEq : TreeSequenceVertexSet Tstar =
            TreeSequenceVertexSet
              (replacementSeries.data.tree (Fin.last (ett.rounds + 1))) :=
          TashkinovClosureVertexSetUnique sigmaN seed Tstar _
            chosenClosure newClosure
        exact (TreeSequenceInitialSegmentVertexSetEq Tstar _ below vertexEq).symm

end GoldbergSeymour

end
