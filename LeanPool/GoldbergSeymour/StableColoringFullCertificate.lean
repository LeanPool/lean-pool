/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyPrefixData
public import LeanPool.GoldbergSeymour.HierarchyMinimumCounterexampleContext
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceColoringTransport
public import LeanPool.GoldbergSeymour.Td

/-!
# P2752_T2_Full Certificate

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem P2752_T2_FullCertificate {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi sigma : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (Bplus : TreeSequence G e0) (F : HierarchyPrefixData C Bplus sigma)
    (hfixed : ∀ t : Fin T.length, sigma (T.edge t) = phi (T.edge t))
    (hstable : StableColoring
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) phi sigma) :
    ∃ corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma T,
      MaximumProperty corr.replacementETT := by
  classical
  let n := Fin.last ett.rounds
  let Tn := ett.series.data.tree n.castSucc
  let Tout := ett.series.data.tree (Fin.last (ett.rounds + 1))
  have hNT : TreeSequenceInitialSegment Tn T := by
    convert ett.abovePenultimate using 1
    congr 1
  have hstrict : Tn.length < T.length := by
    convert ett.strictAbovePenultimate using 1
    congr 1
  have transport (S : TreeSequence G e0)
      (hs : TreeSequenceInitialSegment S T)
      (hr : TashkinovAugmentationSequence phi S Tout) :
      TashkinovAugmentationSequence sigma S T := by
    have hshort := TashkinovAugmentationSequenceRestrict phi S T Tout hr hs ett.belowFinal
    exact TashkinovAugmentationSequenceColoringTransport phi sigma S Bplus T
      hshort F.belowFull F.penultimateLength
      (fun t _ => hfixed t) F.invariant.2
  have seedBelow (S : TreeSequence G e0)
      (hseed : S.length = Tn.length + 1)
      (hr : TashkinovAugmentationSequence phi S Tout) :
      TreeSequenceInitialSegment S T := by
    have hSO := TashkinovAugmentationSequenceInitialSegment phi S Tout hr
    have hTO := ett.belowFinal
    have hlen : S.length ≤ T.length := by omega
    refine ⟨hlen, ?_, ?_⟩
    · intro i
      rw [← hTO.2.1 (Fin.castLE (Nat.succ_le_succ hlen) i)]
      convert hSO.2.1 i using 1
      congr 1
    · intro i
      rw [← hTO.2.2 (Fin.castLE hlen i)]
      convert hSO.2.2 i using 1
      congr 1
  have eligible :
      (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence sigma Tn T) ∨
      ((ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
          ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
        ∃ (f : E) (seed : TreeSequence G e0),
          ett.series.data.connectingEdges n = {f} ∧
            TreeSequenceAdjoinEdge Tn f seed ∧
            TashkinovAugmentationSequence sigma seed T) := by
    have step := ett.series.certified n
    generalize heq : n = target at step
    cases step with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma initialClosure =>
      have hn : ett.rounds = 0 := congrArg Fin.val heq
      have hp := ett.roundsPositive
      omega
    | SE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
      have hi : i.succ = n := heq.symm
      have hr : TashkinovAugmentationSequence phi adjoined Tout := by
        simpa [Tout, hi, n, ← ett.generatingColoring] using closedExtension.1
      have hs : TreeSequenceAdjoinEdge Tn choice.edge adjoined := by
        simpa [Tn, hi] using adjoinedExactly
      exact Or.inr ⟨Or.inl (by simpa [hi] using currentKind), choice.edge,
        adjoined, by simpa [hi] using currentEdges, hs,
        transport adjoined (seedBelow adjoined hs.1 hr) hr⟩
    | PE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
        gamma gammaRule secondStable secondStableProper secondStableOneUncolored
        secondStableRelation exitWitness currentColoring currentProper
        currentOneUncolored currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma closedExtension
        orderedExtension strictExtension =>
      have hi : i.succ = n := heq.symm
      have hr : TashkinovAugmentationSequence phi Tn Tout := by
        simpa [Tn, Tout, hi, n, ← ett.generatingColoring] using closedExtension.1
      exact Or.inl ⟨by simpa [hi] using currentKind, transport Tn hNT hr⟩
    | RE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma adjoined adjoinedExactly closedExtension
        orderedExtension strictExtension =>
      have hi : i.succ = n := heq.symm
      have hr : TashkinovAugmentationSequence phi adjoined Tout := by
        simpa [Tout, hi, n, ← ett.generatingColoring] using closedExtension.1
      have hs : TreeSequenceAdjoinEdge Tn available.edge adjoined := by
        simpa [Tn, hi] using adjoinedExactly
      exact Or.inr ⟨Or.inr (by simpa [hi] using currentKind), available.edge,
        adjoined, by simpa [hi] using currentEdges, hs,
        transport adjoined (seedBelow adjoined hs.1 hr) hr⟩
  have hmod := Td G k e0 input T phi ett C.maximum C.positive
    ctx.lowerRung sigma F.proper F.oneUncolored
    (by simpa [← ett.generatingColoring] using hstable)
  obtain ⟨corr⟩ := hmod.2.2 T hNT hstrict eligible
  exact ⟨corr, MaximumPropertyTransport G k e0 ett sigma hmod T corr C.maximum⟩

end GoldbergSeymour

end
