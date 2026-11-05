/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TdTerminalRERebuild
public import LeanPool.GoldbergSeymour.TdTerminalSEPERebuild

/-!
# Td

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem Td {V E : Type*} [Fintype V] [Fintype E]
     [DecidableEq E] (G : LooplessMultigraph V E)
    (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
    (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hMP : MaximumProperty ett)
    (hpositive : 0 < ett.rounds)
    (hlower : LowerRoundInductionHypothesis G k e0 ett.rounds) :
    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc
    ∀ sigma : PartialEdgeColoring E k,
      IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
      StableColoring Tn
        (TashkinovStoredColors ett.series.data n)
        (ett.series.data.coloring n) sigma →
      ModColoring ett sigma := by
  classical
  dsimp
  intro sigma hsigmaProper hsigmaOneUncolored hsigmaStable
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  have hkind :
      ett.series.data.kind n = some TashkinovExtensionKind.RE ∨
        ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
        ett.series.data.kind n = some TashkinovExtensionKind.PE := by
    generalize hindex : n = index
    cases ett.series.certified index with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma
        initialClosure =>
      have hval := congrArg Fin.val hindex
      dsimp [n] at hval
      omega
    | SE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
      right
      left
      exact currentKind
    | PE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
        gamma gammaRule secondStable secondStableProper
        secondStableOneUncolored secondStableRelation exitWitness
        currentColoring currentProper currentOneUncolored currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma closedExtension orderedExtension strictExtension =>
      right
      right
      exact currentKind
    | RE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma adjoined adjoinedExactly closedExtension orderedExtension
        strictExtension =>
      left
      exact currentKind
  rcases hkind with hRE | hSE | hPE
  · exact TdTerminalRERebuild G k e0 input T generating ett hMP hpositive
      hlower hRE sigma hsigmaProper hsigmaOneUncolored hsigmaStable
  · exact TdTerminalSEPERebuild G k e0 input T generating ett hMP hpositive
      hlower (Or.inl hSE) sigma hsigmaProper hsigmaOneUncolored hsigmaStable
  · exact TdTerminalSEPERebuild G k e0 input T generating ett hMP hpositive
      hlower (Or.inr hPE) sigma hsigmaProper hsigmaOneUncolored hsigmaStable

end GoldbergSeymour

end
