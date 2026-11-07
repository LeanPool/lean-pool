/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.AlgorithmThreeOneStepExists
public import LeanPool.GoldbergSeymour.MaximumPropertyAppend
public import LeanPool.GoldbergSeymour.NormalizePositiveTerminalMaximum

/-!
# Positive Well Definedness

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem PositiveWellDefinedness
    {V E : Type*} [Fintype V] [Fintype E]
     [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hfinal : T = ett.series.data.tree (Fin.last (ett.rounds + 1)))
    (hMP : MaximumProperty ett)
    (hdegree : MaximumDegree G + 1 <= k)
    (hlarge : 11 <= TashkinovOrder G) :
    (exists (replacementInput : PartialEdgeColoring E k)
        (replacementSeries : TashkinovSeries G k ett.rounds e0 replacementInput)
        (normalized : ExtendedTashkinovTree G k e0 replacementInput
          (replacementSeries.data.tree (Fin.last (ett.rounds + 1)))
          (replacementSeries.data.coloring (Fin.last ett.rounds))),
      normalized.rounds = ett.rounds /\
      HEq normalized.series replacementSeries /\
      IsProperEdgeColoring G
        (replacementSeries.data.coloring (Fin.last ett.rounds)) /\
      IsOneEdgeUncolored
        (replacementSeries.data.coloring (Fin.last ett.rounds)) e0 /\
      ColoredVertexSetClosed G
        (replacementSeries.data.coloring (Fin.last ett.rounds))
        (TreeSequenceVertexSet
          (replacementSeries.data.tree (Fin.last (ett.rounds + 1)))) /\
      ColoredVertexSetStronglyClosed G
        (replacementSeries.data.coloring (Fin.last ett.rounds))
        (TreeSequenceVertexSet
          (replacementSeries.data.tree (Fin.last (ett.rounds + 1)))) /\
      MaximumProperty normalized /\
      TerminalClosureMaximum normalized) \/
    (exists (replacementInput : PartialEdgeColoring E k)
        (extended : TashkinovSeries G k (ett.rounds + 1) e0 replacementInput)
        (extendedETT : ExtendedTashkinovTree G k e0 replacementInput
          (extended.data.tree (Fin.last ((ett.rounds + 1) + 1)))
          (extended.data.coloring (Fin.last (ett.rounds + 1)))),
      extendedETT.rounds = ett.rounds + 1 /\
      HEq extendedETT.series extended /\
      IsProperEdgeColoring G
        (extended.data.coloring (Fin.last (ett.rounds + 1))) /\
      IsOneEdgeUncolored
        (extended.data.coloring (Fin.last (ett.rounds + 1))) e0 /\
      ColoredVertexSetClosed G
        (extended.data.coloring (Fin.last (ett.rounds + 1)))
        (TreeSequenceVertexSet
          (extended.data.tree (Fin.last ((ett.rounds + 1) + 1)))) /\
      MaximumProperty extendedETT) := by
  classical
  obtain ⟨sigmaN, Tstar, seed, corr, hsproper, hsone, hstable,
      hroute, hclosure, hterminalEq, hreplacementMP, hterminalMaximum⟩ :=
    NormalizePositiveTerminalMaximum G k e0 input T generating ett hfinal hMP
      hdegree hlarge
  rcases corr with ⟨replacementInput, replacementSeries, replacementETT,
    rungAgreement, seriesPresentation, finalGeneratingColoring,
    ladderTreesAgree, storedColorsAgree, connectingEdgesAgree,
    extensionKindsAgree, replacementProper, replacementOneUncolored,
    replacementStable⟩
  cases replacementETT with
  | mk replacementRounds replacementRoundsPositive replacementData
      abovePenultimate strictAbovePenultimate belowFinal generatingColoring =>
    dsimp at rungAgreement
    subst replacementRounds
    have replacementDataEq : replacementData = replacementSeries :=
      eq_of_heq seriesPresentation
    subst replacementData
    subst sigmaN
    dsimp at hterminalEq hreplacementMP hterminalMaximum
    subst Tstar
    let normalized : ExtendedTashkinovTree G k e0 replacementInput
        (replacementSeries.data.tree (Fin.last (ett.rounds + 1)))
        (replacementSeries.data.coloring (Fin.last ett.rounds)) := {
      rounds := ett.rounds
      roundsPositive := replacementRoundsPositive
      series := replacementSeries
      abovePenultimate := abovePenultimate
      strictAbovePenultimate := strictAbovePenultimate
      belowFinal := belowFinal
      generatingColoring := generatingColoring }
    change MaximumProperty normalized at hreplacementMP
    change TerminalClosureMaximum normalized at hterminalMaximum
    have hclosed : ColoredVertexSetClosed G
        (replacementSeries.data.coloring (Fin.last ett.rounds))
        (TreeSequenceVertexSet
          (replacementSeries.data.tree (Fin.last (ett.rounds + 1)))) :=
      hclosure.2
    by_cases hstrong : ColoredVertexSetStronglyClosed G
        (replacementSeries.data.coloring (Fin.last ett.rounds))
        (TreeSequenceVertexSet
          (replacementSeries.data.tree (Fin.last (ett.rounds + 1))))
    · exact Or.inl ⟨replacementInput, replacementSeries, normalized, rfl,
        HEq.rfl, hsproper, hsone, hclosed, hstrong, hreplacementMP,
        hterminalMaximum⟩
    · obtain ⟨newTree, newColoring, newStored, newConnectingEdges, newKind,
          newChosenVertex, newOutsideVertex, newDelta, newGamma, extended,
          happend, hstrict⟩ :=
        AlgorithmThreeOneStepExists G k ett.rounds e0 replacementInput
          replacementSeries hdegree hsproper hsone hclosed hstrong
      obtain ⟨extendedETT, hettRounds, hettSeries, hettMP⟩ :=
        MaximumPropertyAppend G k e0 replacementInput
          (replacementSeries.data.tree (Fin.last (ett.rounds + 1)))
          (replacementSeries.data.coloring (Fin.last ett.rounds)) normalized
          hreplacementMP hterminalMaximum newTree newColoring newStored
          newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta
          newGamma extended happend
      have terminalFacts :
    forall (rounds : Nat) (series : TashkinovSeries G k rounds e0 replacementInput), 0 < rounds ->
        IsProperEdgeColoring G (series.data.coloring (Fin.last rounds)) /\ IsOneEdgeUncolored
        (series.data.coloring (Fin.last rounds)) e0 /\ ColoredVertexSetClosed G
        (series.data.coloring (Fin.last rounds)) (TreeSequenceVertexSet (series.data.tree
        (Fin.last (rounds + 1)))) := by
        intro rounds series hrounds
        let q : Fin rounds :=
          ⟨rounds - 1, Nat.sub_lt hrounds (by omega)⟩
        have hq : q.succ = Fin.last rounds := by
          apply Fin.ext
          exact Nat.sub_add_cancel hrounds
        have hq2 : q.succ.succ = Fin.last (rounds + 1) := by
          rw [hq]
          rfl
        have step := series.certified (Fin.last rounds)
        generalize hidx : Fin.last rounds = target at step
        cases step with
        | initial triple seedLength initialColoring initialStored initialEdges
            initialKind initialVertex initialOutside initialDelta initialGamma
            initialClosure =>
          have hv : rounds = 0 := by
            simpa using congrArg Fin.val hidx
          omega
        | SE i previousProper previousOneUncolored previousClosed
            previousNotStronglyClosed noRevisiting choice seriesAlternative
            currentColoring currentStored currentEdges currentKind currentVertex
            currentOutside currentDelta currentGamma adjoined adjoinedExactly
            closedExtension orderedExtension strictExtension =>
          have hi : i = q := by
            apply Fin.ext
            have hv := congrArg Fin.val hidx
            simp [q] at hv ⊢
            omega
          subst i
          constructor
          · rw [currentColoring]
            exact choice.selectedProper
          constructor
          · rw [currentColoring]
            exact choice.selectedOneUncolored
          · rw [← hq2]
            exact closedExtension.2
        | PE i previousProper previousOneUncolored previousClosed
            previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
            gamma gammaRule secondStable secondStableProper secondStableOneUncolored
            secondStableRelation exitWitness currentColoring currentProper
            currentOneUncolored currentStored currentEdges currentKind currentVertex
            currentOutside currentDelta currentGamma closedExtension orderedExtension
            strictExtension =>
          have hi : i = q := by
            apply Fin.ext
            have hv := congrArg Fin.val hidx
            simp [q] at hv ⊢
            omega
          subst i
          constructor
          · exact currentProper
          constructor
          · exact currentOneUncolored
          · rw [← hq2]
            exact closedExtension.2
        | RE i previousProper previousOneUncolored previousClosed
            previousNotStronglyClosed available currentColoring currentStored
            currentEdges currentKind currentVertex currentOutside currentDelta
            currentGamma adjoined adjoinedExactly closedExtension orderedExtension
            strictExtension =>
          have hi : i = q := by
            apply Fin.ext
            have hv := congrArg Fin.val hidx
            simp [q] at hv ⊢
            omega
          subst i
          constructor
          · rw [currentColoring]
            exact previousProper
          constructor
          · rw [currentColoring]
            exact previousOneUncolored
          · rw [← hq2]
            exact closedExtension.2
      obtain ⟨hextProper, hextOne, hextClosed⟩ :=
        terminalFacts (ett.rounds + 1) extended (by omega)
      exact Or.inr ⟨replacementInput, extended, extendedETT, hettRounds,
        hettSeries, hextProper, hextOne, hextClosed, hettMP⟩

end GoldbergSeymour

end
