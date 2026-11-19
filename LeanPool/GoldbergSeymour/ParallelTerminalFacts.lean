/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ExtendedTashkinovTree

/-!
# P2634_T1_PETerminal Facts

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem P2634_T1_PETerminalFacts
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : Nat} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {phi : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (hPE : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE) :
    IsProperEdgeColoring G phi /\ IsOneEdgeUncolored phi e0 /\
      TashkinovClosure phi
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (ett.series.data.tree (Fin.last (ett.rounds + 1))) := by
  have positive : 0 < ett.rounds := by have := ett.roundsPositive; omega
  let q : Fin ett.rounds := ⟨ett.rounds - 1, by omega⟩
  have hq : q.succ = Fin.last ett.rounds := by
    apply Fin.ext
    simp [q]
    omega
  have hout : q.succ.succ = Fin.last (ett.rounds + 1) := by
    apply Fin.ext
    simp [q]
    omega
  have hkind : ett.series.data.kind q.succ =
      some TashkinovExtensionKind.PE := by rwa [hq]
  have hcolor : phi = ett.series.data.coloring q.succ := by
    rw [hq]
    exact ett.generatingColoring
  rw [← hq, ← hout]
  generalize hi : q.succ = z at hkind hcolor ⊢
  cases ett.series.certified z with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
    exact (Fin.succ_ne_zero q hi).elim
  | SE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    rw [currentKind] at hkind
    cases hkind
  | RE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    rw [currentKind] at hkind
    cases hkind
  | PE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper
      secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma closedExtension orderedExtension strictExtension =>
    refine ⟨?_, ?_, ?_⟩
    · simpa only [← hcolor] using currentProper
    · simpa only [← hcolor] using currentOneUncolored
    · simpa only [← hcolor] using closedExtension

end GoldbergSeymour

end
