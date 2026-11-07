/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ParallelExtensionColorAppend
public import LeanPool.GoldbergSeymour.RevisitingExtensionCertificateAppend
public import LeanPool.GoldbergSeymour.TashkinovSeriesDataAppend
public import LeanPool.GoldbergSeymour.TashkinovSeriesStep
public import LeanPool.GoldbergSeymour.TashkinovStoredColorsAppend

/-!
# Tashkinov Series Step Append

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_lifted_223.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (data :
        TashkinovSeriesData G k rounds e0) (newTree : TreeSequence G e0) (newColoring :
        PartialEdgeColoring E k) (newStored : Finset (Fin k)) (newConnectingEdges : Finset E)
        (newKind : Option TashkinovExtensionKind) (newChosenVertex newOutsideVertex : Option V)
        (newDelta newGamma : Option (Fin k)),
    ∀ (i : Fin rounds), IsProperEdgeColoring G (data.coloring i.castSucc) → IsOneEdgeUncolored
        (data.coloring i.castSucc) e0 → ColoredVertexSetClosed G (data.coloring i.castSucc)
        (TreeSequenceVertexSet (data.tree i.succ.castSucc)) → ¬ColoredVertexSetStronglyClosed G
        (data.coloring i.castSucc) (TreeSequenceVertexSet (data.tree i.succ.castSucc)) →
    ∀ (_ : MaximumDefectiveChoice G e0 (data.tree i.succ.castSucc) (TashkinovStoredColors data
        i.castSucc) (data.coloring i.castSucc)) (_ : TreeSequence G e0),
        (TashkinovSeriesDataAppend data newTree newColoring newStored newConnectingEdges newKind
        newChosenVertex newOutsideVertex newDelta newGamma : TashkinovSeriesData G k (rounds + (1
        : ℕ)) e0).tree i.castSucc.succ.castSucc = data.tree i.succ.castSucc →
        (TashkinovSeriesDataAppend data newTree newColoring newStored newConnectingEdges newKind
        newChosenVertex newOutsideVertex newDelta newGamma : TashkinovSeriesData G k (rounds + (1
        : ℕ)) e0).coloring i.castSucc.castSucc = data.coloring i.castSucc →
    ∀ (newChoice : MaximumDefectiveChoice G e0 ((TashkinovSeriesDataAppend data newTree
        newColoring newStored newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta
        newGamma : TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).tree i.castSucc.succ.castSucc)
        (TashkinovStoredColors (TashkinovSeriesDataAppend data newTree newColoring newStored
        newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta newGamma :
        TashkinovSeriesData G k (rounds + (1 : ℕ)) e0) i.castSucc.castSucc)
        ((TashkinovSeriesDataAppend data newTree newColoring newStored newConnectingEdges newKind
        newChosenVertex newOutsideVertex newDelta newGamma : TashkinovSeriesData G k (rounds + (1
        : ℕ)) e0).coloring i.castSucc.castSucc)), (
    ∀ (pi : PartialEdgeColoring E k), IsProperEdgeColoring G pi → IsOneEdgeUncolored pi e0 →
        StableColoring ((TashkinovSeriesDataAppend data newTree newColoring newStored
        newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta newGamma :
        TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).tree i.castSucc.succ.castSucc) (insert
        newChoice.color (TashkinovStoredColors (TashkinovSeriesDataAppend data newTree newColoring
        newStored newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta newGamma :
        TashkinovSeriesData G k (rounds + (1 : ℕ)) e0) i.castSucc.castSucc)) newChoice.selected pi
        → Disjoint (MissingColors G pi newChoice.otherEndpoint) (TreeMissingColors pi
        ((TashkinovSeriesDataAppend data newTree newColoring newStored newConnectingEdges newKind
        newChosenVertex newOutsideVertex newDelta newGamma : TashkinovSeriesData G k (rounds + (1
        : ℕ)) e0).tree i.castSucc.succ.castSucc))) → (TashkinovSeriesDataAppend data newTree
        newColoring newStored newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta
        newGamma : TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).coloring i.castSucc.succ =
        newChoice.selected → (TashkinovSeriesDataAppend data newTree newColoring newStored
        newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta newGamma :
        TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).stored i.castSucc.succ =
        { newChoice.color } → (TashkinovSeriesDataAppend data newTree newColoring newStored
        newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta newGamma :
        TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).connectingEdges i.castSucc.succ =
        { newChoice.edge } → (TashkinovSeriesDataAppend data newTree newColoring newStored
        newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta newGamma :
        TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).kind i.castSucc.succ = some
        TashkinovExtensionKind.SE → (TashkinovSeriesDataAppend data newTree newColoring newStored
        newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta newGamma :
        TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).chosenVertex i.castSucc.succ = some
        newChoice.vertex → (TashkinovSeriesDataAppend data newTree newColoring newStored
        newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta newGamma :
        TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).outsideVertex i.castSucc.succ = some
        newChoice.otherEndpoint → (TashkinovSeriesDataAppend data newTree newColoring newStored
        newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta newGamma :
        TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).delta i.castSucc.succ = some
        newChoice.color → (TashkinovSeriesDataAppend data newTree newColoring newStored
        newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta newGamma :
        TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).gamma i.castSucc.succ = none →
    ∀ (newAdjoined : TreeSequence G e0), TreeSequenceAdjoinEdge ((TashkinovSeriesDataAppend data
        newTree newColoring newStored newConnectingEdges newKind newChosenVertex newOutsideVertex
        newDelta newGamma : TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).tree
        i.castSucc.succ.castSucc) newChoice.edge newAdjoined → TashkinovClosure
        ((TashkinovSeriesDataAppend data newTree newColoring newStored newConnectingEdges newKind
        newChosenVertex newOutsideVertex newDelta newGamma : TashkinovSeriesData G k (rounds + (1
        : ℕ)) e0).coloring i.castSucc.succ) newAdjoined ((TashkinovSeriesDataAppend data newTree
        newColoring newStored newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta
        newGamma : TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).tree i.castSucc.succ.succ) →
        TreeSequenceInitialSegment ((TashkinovSeriesDataAppend data newTree newColoring newStored
        newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta newGamma :
        TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).tree i.castSucc.succ.castSucc)
        ((TashkinovSeriesDataAppend data newTree newColoring newStored newConnectingEdges newKind
        newChosenVertex newOutsideVertex newDelta newGamma : TashkinovSeriesData G k (rounds + (1
        : ℕ)) e0).tree i.castSucc.succ.succ) → ((TashkinovSeriesDataAppend data newTree
        newColoring newStored newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta
        newGamma : TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).tree
        i.castSucc.succ.castSucc).length < ((TashkinovSeriesDataAppend data newTree newColoring
        newStored newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta newGamma :
        TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).tree i.castSucc.succ.succ).length →
        ¬Nonempty (RevisitingExtensionCertificate (TashkinovSeriesDataAppend data newTree
        newColoring newStored newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta
        newGamma : TashkinovSeriesData G k (rounds + (1 : ℕ)) e0) i.castSucc.castSucc) →
        TashkinovSeriesStep G k (rounds + (1 : ℕ)) e0 input (TashkinovSeriesDataAppend data
        newTree newColoring newStored newConnectingEdges newKind newChosenVertex newOutsideVertex
        newDelta newGamma : TashkinovSeriesData G k (rounds + (1 : ℕ)) e0) i.castSucc.succ := by
  classical
  intro V E _ _ _ G k rounds e0 input data newTree newColoring newStored newConnectingEdges
      newKind newChosenVertex newOutsideVertex newDelta newGamma
  set appended : TashkinovSeriesData G k (rounds + (1 : ℕ)) e0 := TashkinovSeriesDataAppend data
      newTree newColoring newStored newConnectingEdges newKind
            newChosenVertex
          newOutsideVertex newDelta newGamma
  intro i previousProper previousOneUncolored previousClosed previousNotStronglyClosed choice
      adjoined previousTreeEq previousColoringEq newChoice newSeriesAlternative
      newCurrentColoring newCurrentStored newCurrentEdges newCurrentKind newCurrentVertex
      newCurrentOutside newCurrentDelta newCurrentGamma newAdjoined newAdjoinedExactly
      newClosedExtension newOrderedExtension newStrictExtension newNoRevisiting
  apply TashkinovSeriesStep.SE (i := i.castSucc) (choice := newChoice)
    (adjoined := newAdjoined)
  · rw [previousColoringEq]
    exact previousProper
  · rw [previousColoringEq]
    exact previousOneUncolored
  · rw [previousColoringEq, previousTreeEq]
    exact previousClosed
  · rw [previousColoringEq, previousTreeEq]
    exact previousNotStronglyClosed
  · exact newNoRevisiting
  · exact newSeriesAlternative
  · exact newCurrentColoring
  · exact newCurrentStored
  · exact newCurrentEdges
  · exact newCurrentKind
  · exact newCurrentVertex
  · exact newCurrentOutside
  · exact newCurrentDelta
  · exact newCurrentGamma
  · exact newAdjoinedExactly
  · exact newClosedExtension
  · exact newOrderedExtension
  · exact newStrictExtension

private theorem helper_continuation_310.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (data :
        TashkinovSeriesData G k rounds e0) (newTree : TreeSequence G e0) (newColoring :
        PartialEdgeColoring E k) (newStored : Finset (Fin k)) (newConnectingEdges : Finset E)
        (newKind : Option TashkinovExtensionKind) (newChosenVertex newOutsideVertex : Option V)
        (newDelta newGamma : Option (Fin k)),
    ∀ (i : Fin rounds), IsProperEdgeColoring G (data.coloring i.castSucc) → IsOneEdgeUncolored
        (data.coloring i.castSucc) e0 → ColoredVertexSetClosed G (data.coloring i.castSucc)
        (TreeSequenceVertexSet (data.tree i.succ.castSucc)) → ¬ColoredVertexSetStronglyClosed G
        (data.coloring i.castSucc) (TreeSequenceVertexSet (data.tree i.succ.castSucc)) → ¬Nonempty
        (RevisitingExtensionCertificate data i.castSucc) →
    ∀ (choice : MaximumDefectiveChoice G e0 (data.tree i.succ.castSucc) (TashkinovStoredColors
        data i.castSucc) (data.coloring i.castSucc)), (
    ∀ (pi : PartialEdgeColoring E k), IsProperEdgeColoring G pi → IsOneEdgeUncolored pi e0 →
        StableColoring (data.tree i.succ.castSucc) (insert choice.color (TashkinovStoredColors
        data i.castSucc) : Finset (Fin k)) choice.selected pi → Disjoint (MissingColors G pi
        choice.otherEndpoint) (TreeMissingColors pi (data.tree i.succ.castSucc))) → data.coloring
        i.succ = choice.selected → data.stored i.succ = ({ choice.color } : Finset (Fin k)) →
        data.connectingEdges i.succ = ({ choice.edge } : Finset E) → data.kind i.succ = some
        TashkinovExtensionKind.SE → data.chosenVertex i.succ = some choice.vertex →
        data.outsideVertex i.succ = some choice.otherEndpoint → data.delta i.succ = some
        choice.color → data.gamma i.succ = none →
    ∀ (adjoined : TreeSequence G e0), TreeSequenceAdjoinEdge (data.tree i.succ.castSucc)
        choice.edge adjoined → TashkinovClosure (data.coloring i.succ) adjoined (data.tree
        i.succ.succ) → TreeSequenceInitialSegment (data.tree i.succ.castSucc) (data.tree
        i.succ.succ) → (data.tree i.succ.castSucc).length < (data.tree i.succ.succ).length →
        i.castSucc.succ = i.succ.castSucc → (TashkinovSeriesDataAppend data newTree newColoring
        newStored newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta newGamma :
        TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).tree i.castSucc.succ.castSucc = data.tree
        i.succ.castSucc → (TashkinovSeriesDataAppend data newTree newColoring newStored
        newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta newGamma :
        TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).tree i.castSucc.succ.succ = data.tree
        i.succ.succ → (TashkinovSeriesDataAppend data newTree newColoring newStored
        newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta newGamma :
        TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).coloring i.castSucc.castSucc =
        data.coloring i.castSucc → TashkinovStoredColors (TashkinovSeriesDataAppend data newTree
        newColoring newStored newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta
        newGamma : TashkinovSeriesData G k (rounds + (1 : ℕ)) e0) i.castSucc.castSucc =
        TashkinovStoredColors data i.castSucc → (TashkinovSeriesDataAppend data newTree
        newColoring newStored newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta
        newGamma : TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).coloring i.castSucc.succ =
        data.coloring i.succ → (TashkinovSeriesDataAppend data newTree newColoring newStored
        newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta newGamma :
        TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).stored i.castSucc.succ = data.stored i.succ
        → (TashkinovSeriesDataAppend data newTree newColoring newStored newConnectingEdges newKind
        newChosenVertex newOutsideVertex newDelta newGamma : TashkinovSeriesData G k (rounds + (1
        : ℕ)) e0).connectingEdges i.castSucc.succ = data.connectingEdges i.succ →
        (TashkinovSeriesDataAppend data newTree newColoring newStored newConnectingEdges newKind
        newChosenVertex newOutsideVertex newDelta newGamma : TashkinovSeriesData G k (rounds + (1
        : ℕ)) e0).kind i.castSucc.succ = data.kind i.succ → (TashkinovSeriesDataAppend data
        newTree newColoring newStored newConnectingEdges newKind newChosenVertex newOutsideVertex
        newDelta newGamma : TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).chosenVertex
        i.castSucc.succ = data.chosenVertex i.succ → (TashkinovSeriesDataAppend data newTree
        newColoring newStored newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta
        newGamma : TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).outsideVertex i.castSucc.succ =
        data.outsideVertex i.succ → (TashkinovSeriesDataAppend data newTree newColoring newStored
        newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta newGamma :
        TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).delta i.castSucc.succ = data.delta i.succ →
        (TashkinovSeriesDataAppend data newTree newColoring newStored newConnectingEdges newKind
        newChosenVertex newOutsideVertex newDelta newGamma : TashkinovSeriesData G k (rounds + (1
        : ℕ)) e0).gamma i.castSucc.succ = data.gamma i.succ → TashkinovSeriesStep G k (rounds + (1
        : ℕ)) e0 input (TashkinovSeriesDataAppend data newTree newColoring newStored
        newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta newGamma)
        i.succ.castSucc := by
  classical
  intro V E _ _ _ G k rounds e0 input data newTree newColoring newStored newConnectingEdges
      newKind newChosenVertex newOutsideVertex newDelta newGamma
  set appended : TashkinovSeriesData G k (rounds + (1 : ℕ)) e0 := TashkinovSeriesDataAppend data
      newTree newColoring newStored newConnectingEdges newKind
            newChosenVertex
          newOutsideVertex newDelta newGamma
  intro i previousProper previousOneUncolored previousClosed previousNotStronglyClosed
      noRevisiting choice seriesAlternative currentColoring currentStored currentEdges
      currentKind currentVertex currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension slotIndexEq previousTreeEq outputTreeEq
      previousColoringEq storedColorsEq currentColoringEq currentStoredEq currentEdgesEq
      currentKindEq currentVertexEq currentOutsideEq currentDeltaEq currentGammaEq
  let Package : PartialEdgeColoring E k → PartialEdgeColoring E k → TreeSequence G e0 →
      TreeSequence G e0 → Finset (Fin k) → Finset (Fin k) → Finset E → Option
      TashkinovExtensionKind → Option V → Option V → Option (Fin k) → Option (Fin k) → Prop :=
    fun
      (previousColor
          currentColor :
        PartialEdgeColoring E k)
      (previousTree
          outputTree :
          TreeSequence G e0)
      (storedColors
          currentStoredValue :
        Finset (Fin k))
      (currentEdgesValue
          : Finset E)
      (currentKindValue :
        Option
            TashkinovExtensionKind)
      (currentVertexValue
          currentOutsideValue :
        Option V)
      (currentDeltaValue
          currentGammaValue :
        Option (Fin k)) ↦
    ∃ (selectedChoice :
      MaximumDefectiveChoice G e0 previousTree
        storedColors
            previousColor),
      (∀ (pi :
          PartialEdgeColoring E k),
          IsProperEdgeColoring G pi →
            IsOneEdgeUncolored pi e0 →
              StableColoring previousTree
                  (insert
                      selectedChoice.color
                      storedColors :
                    Finset (Fin k))
                  selectedChoice.selected pi →
                Disjoint
                  (MissingColors G pi
                    selectedChoice.otherEndpoint)
                  (TreeMissingColors pi
                    previousTree)) ∧
        currentColor =
            selectedChoice.selected ∧
          currentStoredValue =
              ({selectedChoice.color} :
                Finset
                    (Fin
                    k)) ∧
            currentEdgesValue =
                ({selectedChoice.edge} : Finset E) ∧
              currentKindValue =
                  some
                      TashkinovExtensionKind.SE ∧
                currentVertexValue =
                    some
                        selectedChoice.vertex ∧
                  currentOutsideValue =
                      some
                        selectedChoice.otherEndpoint ∧
                    currentDeltaValue =
                        some selectedChoice.color ∧
                      currentGammaValue = none ∧
                        ∃
                            (exactAdjoined :
                          TreeSequence G e0),
                          TreeSequenceAdjoinEdge
                              previousTree
                              selectedChoice.edge
                              exactAdjoined ∧
                            TashkinovClosure
                                currentColor
                                exactAdjoined
                                outputTree ∧
                              TreeSequenceInitialSegment
                                  previousTree
                                  outputTree ∧
                                previousTree.length <
                                  outputTree.length
  have oldPackage : Package (data.coloring i.castSucc) (data.coloring i.succ)
      (data.tree i.succ.castSucc) (data.tree i.succ.succ)
      (TashkinovStoredColors data i.castSucc) (data.stored i.succ)
      (data.connectingEdges i.succ) (data.kind i.succ)
      (data.chosenVertex i.succ) (data.outsideVertex i.succ)
      (data.delta i.succ) (data.gamma i.succ) := by
    exact ⟨choice, seriesAlternative, currentColoring, currentStored,
      currentEdges, currentKind, currentVertex, currentOutside, currentDelta,
      currentGamma, adjoined, adjoinedExactly, closedExtension,
      orderedExtension, strictExtension⟩
  have newPackage : Package (appended.coloring i.castSucc.castSucc)
      (appended.coloring i.castSucc.succ)
      (appended.tree i.castSucc.succ.castSucc)
      (appended.tree i.castSucc.succ.succ)
      (TashkinovStoredColors appended i.castSucc.castSucc)
      (appended.stored i.castSucc.succ)
      (appended.connectingEdges i.castSucc.succ)
      (appended.kind i.castSucc.succ)
      (appended.chosenVertex i.castSucc.succ)
      (appended.outsideVertex i.castSucc.succ)
      (appended.delta i.castSucc.succ) (appended.gamma i.castSucc.succ) := by
    rw [previousColoringEq, currentColoringEq, previousTreeEq, outputTreeEq,
      storedColorsEq, currentStoredEq, currentEdgesEq, currentKindEq,
      currentVertexEq, currentOutsideEq, currentDeltaEq, currentGammaEq]
    exact oldPackage
  rcases newPackage with ⟨newChoice, newSeriesAlternative,
    newCurrentColoring, newCurrentStored, newCurrentEdges, newCurrentKind,
    newCurrentVertex, newCurrentOutside, newCurrentDelta, newCurrentGamma,
    newAdjoined, newAdjoinedExactly, newClosedExtension,
    newOrderedExtension, newStrictExtension⟩
  have newNoRevisiting : ¬ Nonempty
      (RevisitingExtensionCertificate appended i.castSucc.castSucc) := by
    rintro ⟨newCertificate⟩
    rcases (RevisitingExtensionCertificateAppend data newTree newColoring newStored
      newConnectingEdges newKind newChosenVertex newOutsideVertex
      newDelta newGamma i.castSucc).1 newCertificate with ⟨oldCertificate, -⟩
    exact noRevisiting ⟨oldCertificate⟩
  have lifted := @helper_lifted_223 V E inferInstance inferInstance inferInstance G k rounds e0
      input data newTree newColoring newStored newConnectingEdges newKind newChosenVertex
      newOutsideVertex newDelta newGamma i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed choice adjoined previousTreeEq previousColoringEq newChoice
      newSeriesAlternative newCurrentColoring newCurrentStored newCurrentEdges newCurrentKind
      newCurrentVertex newCurrentOutside newCurrentDelta newCurrentGamma newAdjoined
      newAdjoinedExactly newClosedExtension newOrderedExtension newStrictExtension newNoRevisiting
  rw [← slotIndexEq]
  exact lifted

private theorem helper_branch_92.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (data :
        TashkinovSeriesData G k rounds e0) (newTree : TreeSequence G e0) (newColoring :
        PartialEdgeColoring E k) (newStored : Finset (Fin k)) (newConnectingEdges : Finset E)
        (newKind : Option TashkinovExtensionKind) (newChosenVertex newOutsideVertex : Option V)
        (newDelta newGamma : Option (Fin k)), (
    ∀ (i : Fin (rounds + (2 : ℕ))), (TashkinovSeriesDataAppend data newTree newColoring newStored
        newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta newGamma :
        TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).tree i.castSucc = data.tree i) → (
    ∀ (i : Fin (rounds + (1 : ℕ))), (TashkinovSeriesDataAppend data newTree newColoring newStored
        newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta newGamma :
        TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).coloring i.castSucc = data.coloring i ∧
        (TashkinovSeriesDataAppend data newTree newColoring newStored newConnectingEdges newKind
        newChosenVertex newOutsideVertex newDelta newGamma : TashkinovSeriesData G k (rounds + (1
        : ℕ)) e0).stored i.castSucc = data.stored i ∧ (TashkinovSeriesDataAppend data newTree
        newColoring newStored newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta
        newGamma : TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).connectingEdges i.castSucc =
        data.connectingEdges i ∧ (TashkinovSeriesDataAppend data newTree newColoring newStored
        newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta newGamma :
        TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).kind i.castSucc = data.kind i ∧
        (TashkinovSeriesDataAppend data newTree newColoring newStored newConnectingEdges newKind
        newChosenVertex newOutsideVertex newDelta newGamma : TashkinovSeriesData G k (rounds + (1
        : ℕ)) e0).chosenVertex i.castSucc = data.chosenVertex i ∧ (TashkinovSeriesDataAppend data
        newTree newColoring newStored newConnectingEdges newKind newChosenVertex newOutsideVertex
        newDelta newGamma : TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).outsideVertex
        i.castSucc = data.outsideVertex i ∧ (TashkinovSeriesDataAppend data newTree newColoring
        newStored newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta newGamma :
        TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).delta i.castSucc = data.delta i ∧
        (TashkinovSeriesDataAppend data newTree newColoring newStored newConnectingEdges newKind
        newChosenVertex newOutsideVertex newDelta newGamma : TashkinovSeriesData G k (rounds + (1
        : ℕ)) e0).gamma i.castSucc = data.gamma i) →
    ∀ (i : Fin rounds), IsProperEdgeColoring G (data.coloring i.castSucc) → IsOneEdgeUncolored
        (data.coloring i.castSucc) e0 → ColoredVertexSetClosed G (data.coloring i.castSucc)
        (TreeSequenceVertexSet (data.tree i.succ.castSucc)) → ¬ColoredVertexSetStronglyClosed G
        (data.coloring i.castSucc) (TreeSequenceVertexSet (data.tree i.succ.castSucc)) → ¬Nonempty
        (RevisitingExtensionCertificate data i.castSucc) →
    ∀ (choice : MaximumDefectiveChoice G e0 (data.tree i.succ.castSucc) (TashkinovStoredColors
        data i.castSucc) (data.coloring i.castSucc)), (
    ∀ (pi : PartialEdgeColoring E k), IsProperEdgeColoring G pi → IsOneEdgeUncolored pi e0 →
        StableColoring (data.tree i.succ.castSucc) (insert choice.color (TashkinovStoredColors
        data i.castSucc)) choice.selected pi → Disjoint (MissingColors G pi choice.otherEndpoint)
        (TreeMissingColors pi (data.tree i.succ.castSucc))) → data.coloring i.succ =
        choice.selected → data.stored i.succ = { choice.color } → data.connectingEdges i.succ =
        { choice.edge } → data.kind i.succ = some TashkinovExtensionKind.SE → data.chosenVertex
        i.succ = some choice.vertex → data.outsideVertex i.succ = some choice.otherEndpoint →
        data.delta i.succ = some choice.color → data.gamma i.succ = none →
    ∀ (adjoined : TreeSequence G e0), TreeSequenceAdjoinEdge (data.tree i.succ.castSucc)
        choice.edge adjoined → TashkinovClosure (data.coloring i.succ) adjoined (data.tree
        i.succ.succ) → TreeSequenceInitialSegment (data.tree i.succ.castSucc) (data.tree
        i.succ.succ) → (data.tree i.succ.castSucc).length < (data.tree i.succ.succ).length →
        TashkinovSeriesStep G k (rounds + (1 : ℕ)) e0 input (TashkinovSeriesDataAppend data
        newTree newColoring newStored newConnectingEdges newKind newChosenVertex newOutsideVertex
        newDelta newGamma) i.succ.castSucc := by
  classical
  intro V E _ _ _ G k rounds e0 input data newTree newColoring newStored newConnectingEdges
      newKind newChosenVertex newOutsideVertex newDelta newGamma
  set appended : TashkinovSeriesData G k (rounds + (1 : ℕ)) e0 := TashkinovSeriesDataAppend data
      newTree newColoring newStored newConnectingEdges newKind
            newChosenVertex
          newOutsideVertex newDelta newGamma
  intro treeOld slotsOld i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative currentColoring
      currentStored currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension strictExtension
  have slotIndexEq : i.castSucc.succ = i.succ.castSucc := by ext; rfl
  have previousTreeIndexEq : i.castSucc.succ.castSucc =
      i.succ.castSucc.castSucc := by ext; rfl
  have outputTreeIndexEq : i.castSucc.succ.succ =
      i.succ.succ.castSucc := by ext; rfl
  have previousTreeEq : appended.tree i.castSucc.succ.castSucc =
      data.tree i.succ.castSucc := by
    calc
      appended.tree i.castSucc.succ.castSucc =
          appended.tree i.succ.castSucc.castSucc :=
        congrArg appended.tree previousTreeIndexEq
      _ = data.tree i.succ.castSucc := treeOld i.succ.castSucc
  have outputTreeEq : appended.tree i.castSucc.succ.succ =
      data.tree i.succ.succ := by
    calc
      appended.tree i.castSucc.succ.succ =
          appended.tree i.succ.succ.castSucc :=
        congrArg appended.tree outputTreeIndexEq
      _ = data.tree i.succ.succ := treeOld i.succ.succ
  have previousColoringEq : appended.coloring i.castSucc.castSucc =
      data.coloring i.castSucc := (slotsOld i.castSucc).1
  have storedColorsEq : TashkinovStoredColors appended i.castSucc.castSucc =
      TashkinovStoredColors data i.castSucc :=
    TashkinovStoredColorsAppend data newTree newColoring newStored newConnectingEdges
      newKind newChosenVertex newOutsideVertex newDelta newGamma i.castSucc
  have currentColoringEq : appended.coloring i.castSucc.succ =
      data.coloring i.succ := by
    calc
      appended.coloring i.castSucc.succ =
          appended.coloring i.succ.castSucc :=
        congrArg appended.coloring slotIndexEq
      _ = data.coloring i.succ := (slotsOld i.succ).1
  have currentStoredEq : appended.stored i.castSucc.succ =
      data.stored i.succ := by
    calc
      appended.stored i.castSucc.succ = appended.stored i.succ.castSucc :=
        congrArg appended.stored slotIndexEq
      _ = data.stored i.succ := (slotsOld i.succ).2.1
  have currentEdgesEq : appended.connectingEdges i.castSucc.succ =
      data.connectingEdges i.succ := by
    calc
      appended.connectingEdges i.castSucc.succ =
          appended.connectingEdges i.succ.castSucc :=
        congrArg appended.connectingEdges slotIndexEq
      _ = data.connectingEdges i.succ := (slotsOld i.succ).2.2.1
  have currentKindEq : appended.kind i.castSucc.succ = data.kind i.succ := by
    calc
      appended.kind i.castSucc.succ = appended.kind i.succ.castSucc :=
        congrArg appended.kind slotIndexEq
      _ = data.kind i.succ := (slotsOld i.succ).2.2.2.1
  have currentVertexEq : appended.chosenVertex i.castSucc.succ =
      data.chosenVertex i.succ := by
    calc
      appended.chosenVertex i.castSucc.succ =
          appended.chosenVertex i.succ.castSucc :=
        congrArg appended.chosenVertex slotIndexEq
      _ = data.chosenVertex i.succ := (slotsOld i.succ).2.2.2.2.1
  have currentOutsideEq : appended.outsideVertex i.castSucc.succ =
      data.outsideVertex i.succ := by
    calc
      appended.outsideVertex i.castSucc.succ =
          appended.outsideVertex i.succ.castSucc :=
        congrArg appended.outsideVertex slotIndexEq
      _ = data.outsideVertex i.succ := (slotsOld i.succ).2.2.2.2.2.1
  have currentDeltaEq : appended.delta i.castSucc.succ = data.delta i.succ := by
    calc
      appended.delta i.castSucc.succ = appended.delta i.succ.castSucc :=
        congrArg appended.delta slotIndexEq
      _ = data.delta i.succ := (slotsOld i.succ).2.2.2.2.2.2.1
  have currentGammaEq : appended.gamma i.castSucc.succ = data.gamma i.succ := by
    calc
      appended.gamma i.castSucc.succ = appended.gamma i.succ.castSucc :=
        congrArg appended.gamma slotIndexEq
      _ = data.gamma i.succ := (slotsOld i.succ).2.2.2.2.2.2.2
  exact @helper_continuation_310 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
      (@rounds) (@e0) (@input) (@data) (@newTree) (@newColoring) (@newStored)
      (@newConnectingEdges) (@newKind) (@newChosenVertex) (@newOutsideVertex) (@newDelta)
      (@newGamma) (@i) (@previousProper) (@previousOneUncolored) (@previousClosed)
      (@previousNotStronglyClosed) (@noRevisiting) (@choice) (@seriesAlternative)
      (@currentColoring) (@currentStored) (@currentEdges) (@currentKind) (@currentVertex)
      (@currentOutside) (@currentDelta) (@currentGamma) (@adjoined) (@adjoinedExactly)
      (@closedExtension) (@orderedExtension) (@strictExtension) (@slotIndexEq) (@previousTreeEq)
      (@outputTreeEq) (@previousColoringEq) (@storedColorsEq) (@currentColoringEq)
      (@currentStoredEq) (@currentEdgesEq) (@currentKindEq) (@currentVertexEq)
      (@currentOutsideEq) (@currentDeltaEq) (@currentGammaEq)
private theorem helper_lifted_488.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (data :
        TashkinovSeriesData G k rounds e0) (newTree : TreeSequence G e0) (newColoring :
        PartialEdgeColoring E k) (newStored : Finset (Fin k)) (newConnectingEdges : Finset E)
        (newKind : Option TashkinovExtensionKind) (newChosenVertex newOutsideVertex : Option V)
        (newDelta newGamma : Option (Fin k)),
    ∀ (i : Fin rounds), IsProperEdgeColoring G (data.coloring i.castSucc) → IsOneEdgeUncolored
        (data.coloring i.castSucc) e0 → ColoredVertexSetClosed G (data.coloring i.castSucc)
        (TreeSequenceVertexSet (data.tree i.succ.castSucc)) → ¬ColoredVertexSetStronglyClosed G
        (data.coloring i.castSucc) (TreeSequenceVertexSet (data.tree i.succ.castSucc)) →
    ∀ (_ : MaximumDefectiveChoice G e0 (data.tree i.succ.castSucc) (TashkinovStoredColors data
        i.castSucc) (data.coloring i.castSucc)) (_ : Fin k) (_ : PartialEdgeColoring E k),
        (TashkinovSeriesDataAppend data newTree newColoring newStored newConnectingEdges newKind
        newChosenVertex newOutsideVertex newDelta newGamma : TashkinovSeriesData G k (rounds + (1
        : ℕ)) e0).tree i.castSucc.succ.castSucc = data.tree i.succ.castSucc →
        (TashkinovSeriesDataAppend data newTree newColoring newStored newConnectingEdges newKind
        newChosenVertex newOutsideVertex newDelta newGamma : TashkinovSeriesData G k (rounds + (1
        : ℕ)) e0).coloring i.castSucc.castSucc = data.coloring i.castSucc →
    ∀ (newChoice : MaximumDefectiveChoice G e0 ((TashkinovSeriesDataAppend data newTree
        newColoring newStored newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta
        newGamma : TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).tree i.castSucc.succ.castSucc)
        (TashkinovStoredColors (TashkinovSeriesDataAppend data newTree newColoring newStored
        newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta newGamma :
        TashkinovSeriesData G k (rounds + (1 : ℕ)) e0) i.castSucc.castSucc)
        ((TashkinovSeriesDataAppend data newTree newColoring newStored newConnectingEdges newKind
        newChosenVertex newOutsideVertex newDelta newGamma : TashkinovSeriesData G k (rounds + (1
        : ℕ)) e0).coloring i.castSucc.castSucc)), (
    ∃ (rho : PartialEdgeColoring E k), IsProperEdgeColoring G rho ∧ IsOneEdgeUncolored rho e0 ∧
        StableColoring ((TashkinovSeriesDataAppend data newTree newColoring newStored
        newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta newGamma :
        TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).tree i.castSucc.succ.castSucc) (insert
        newChoice.color (TashkinovStoredColors (TashkinovSeriesDataAppend data newTree newColoring
        newStored newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta newGamma :
        TashkinovSeriesData G k (rounds + (1 : ℕ)) e0) i.castSucc.castSucc)) newChoice.selected
        rho ∧ ¬Disjoint (MissingColors G rho newChoice.otherEndpoint) (TreeMissingColors rho
        ((TashkinovSeriesDataAppend data newTree newColoring newStored newConnectingEdges newKind
        newChosenVertex newOutsideVertex newDelta newGamma : TashkinovSeriesData G k (rounds + (1
        : ℕ)) e0).tree i.castSucc.succ.castSucc))) →
    ∀ (newGammaValue : Fin k), (ParallelExtensionColor (TashkinovSeriesDataAppend data newTree
        newColoring newStored newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta
        newGamma : TashkinovSeriesData G k (rounds + (1 : ℕ)) e0) i.castSucc.castSucc :
        PartialEdgeColoring E k → V → Fin k → Prop) newChoice.selected newChoice.vertex
        newGammaValue →
    ∀ (newSecondStable : PartialEdgeColoring E k), IsProperEdgeColoring G newSecondStable →
        IsOneEdgeUncolored newSecondStable e0 → StableColoring ((TashkinovSeriesDataAppend data
        newTree newColoring newStored newConnectingEdges newKind newChosenVertex newOutsideVertex
        newDelta newGamma : TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).tree
        i.castSucc.succ.castSucc) (insert newChoice.color (TashkinovStoredColors
        (TashkinovSeriesDataAppend data newTree newColoring newStored newConnectingEdges newKind
        newChosenVertex newOutsideVertex newDelta newGamma : TashkinovSeriesData G k (rounds + (1
        : ℕ)) e0) i.castSucc.castSucc)) newChoice.selected newSecondStable → TreeExit
        ((TashkinovSeriesDataAppend data newTree newColoring newStored newConnectingEdges newKind
        newChosenVertex newOutsideVertex newDelta newGamma : TashkinovSeriesData G k (rounds + (1
        : ℕ)) e0).tree i.castSucc.succ.castSucc) newSecondStable newGammaValue newChoice.color
        newChoice.vertex → (TashkinovSeriesDataAppend data newTree newColoring newStored
        newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta newGamma :
        TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).coloring i.castSucc.succ =
        TwoColorComponentSwap G newSecondStable newGammaValue newChoice.color (Sum.inl
        newChoice.vertex) → IsProperEdgeColoring G ((TashkinovSeriesDataAppend data newTree
        newColoring newStored newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta
        newGamma : TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).coloring i.castSucc.succ) →
        IsOneEdgeUncolored ((TashkinovSeriesDataAppend data newTree newColoring newStored
        newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta newGamma :
        TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).coloring i.castSucc.succ) e0 →
        (TashkinovSeriesDataAppend data newTree newColoring newStored newConnectingEdges newKind
        newChosenVertex newOutsideVertex newDelta newGamma : TashkinovSeriesData G k (rounds + (1
        : ℕ)) e0).stored i.castSucc.succ = {newChoice.color, newGammaValue} →
        (TashkinovSeriesDataAppend data newTree newColoring newStored newConnectingEdges newKind
        newChosenVertex newOutsideVertex newDelta newGamma : TashkinovSeriesData G k (rounds + (1
        : ℕ)) e0).connectingEdges i.castSucc.succ = { newChoice.edge } →
        (TashkinovSeriesDataAppend data newTree newColoring newStored newConnectingEdges newKind
        newChosenVertex newOutsideVertex newDelta newGamma : TashkinovSeriesData G k (rounds + (1
        : ℕ)) e0).kind i.castSucc.succ = some TashkinovExtensionKind.PE →
        (TashkinovSeriesDataAppend data newTree newColoring newStored newConnectingEdges newKind
        newChosenVertex newOutsideVertex newDelta newGamma : TashkinovSeriesData G k (rounds + (1
        : ℕ)) e0).chosenVertex i.castSucc.succ = some newChoice.vertex →
        (TashkinovSeriesDataAppend data newTree newColoring newStored newConnectingEdges newKind
        newChosenVertex newOutsideVertex newDelta newGamma : TashkinovSeriesData G k (rounds + (1
        : ℕ)) e0).outsideVertex i.castSucc.succ = some newChoice.otherEndpoint →
        (TashkinovSeriesDataAppend data newTree newColoring newStored newConnectingEdges newKind
        newChosenVertex newOutsideVertex newDelta newGamma : TashkinovSeriesData G k (rounds + (1
        : ℕ)) e0).delta i.castSucc.succ = some newChoice.color → (TashkinovSeriesDataAppend data
        newTree newColoring newStored newConnectingEdges newKind newChosenVertex newOutsideVertex
        newDelta newGamma : TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).gamma i.castSucc.succ =
        some newGammaValue → TashkinovClosure ((TashkinovSeriesDataAppend data newTree newColoring
        newStored newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta newGamma :
        TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).coloring i.castSucc.succ)
        ((TashkinovSeriesDataAppend data newTree newColoring newStored newConnectingEdges newKind
        newChosenVertex newOutsideVertex newDelta newGamma : TashkinovSeriesData G k (rounds + (1
        : ℕ)) e0).tree i.castSucc.succ.castSucc) ((TashkinovSeriesDataAppend data newTree
        newColoring newStored newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta
        newGamma : TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).tree i.castSucc.succ.succ) →
        TreeSequenceInitialSegment ((TashkinovSeriesDataAppend data newTree newColoring newStored
        newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta newGamma :
        TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).tree i.castSucc.succ.castSucc)
        ((TashkinovSeriesDataAppend data newTree newColoring newStored newConnectingEdges newKind
        newChosenVertex newOutsideVertex newDelta newGamma : TashkinovSeriesData G k (rounds + (1
        : ℕ)) e0).tree i.castSucc.succ.succ) → ((TashkinovSeriesDataAppend data newTree
        newColoring newStored newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta
        newGamma : TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).tree
        i.castSucc.succ.castSucc).length < ((TashkinovSeriesDataAppend data newTree newColoring
        newStored newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta newGamma :
        TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).tree i.castSucc.succ.succ).length →
        ¬Nonempty (RevisitingExtensionCertificate (TashkinovSeriesDataAppend data newTree
        newColoring newStored newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta
        newGamma : TashkinovSeriesData G k (rounds + (1 : ℕ)) e0) i.castSucc.castSucc) →
        TashkinovSeriesStep G k (rounds + (1 : ℕ)) e0 input (TashkinovSeriesDataAppend data
        newTree newColoring newStored newConnectingEdges newKind newChosenVertex newOutsideVertex
        newDelta newGamma : TashkinovSeriesData G k (rounds + (1 : ℕ)) e0) i.castSucc.succ := by
  classical
  intro V E _ _ _ G k rounds e0 input data newTree newColoring newStored newConnectingEdges
      newKind newChosenVertex newOutsideVertex newDelta newGamma
  set appended : TashkinovSeriesData G k (rounds + (1 : ℕ)) e0 := TashkinovSeriesDataAppend data
      newTree newColoring newStored newConnectingEdges newKind
            newChosenVertex
          newOutsideVertex newDelta newGamma
  intro i previousProper previousOneUncolored previousClosed previousNotStronglyClosed choice
      gamma secondStable previousTreeEq previousColoringEq
  set newRule : PartialEdgeColoring E k → V → Fin k → Prop := ParallelExtensionColor
      (TashkinovSeriesDataAppend data newTree newColoring newStored newConnectingEdges newKind
      newChosenVertex newOutsideVertex newDelta newGamma : TashkinovSeriesData G k (rounds + (1 :
      ℕ)) e0) i.castSucc.castSucc
  intro newChoice newSeriesAlternativeFails newGammaValue newGammaRule newSecondStable
      newSecondStableProper newSecondStableOneUncolored newSecondStableRelation newExitWitness
      newCurrentColoring newCurrentProper newCurrentOneUncolored newCurrentStored newCurrentEdges
      newCurrentKind newCurrentVertex newCurrentOutside newCurrentDelta newCurrentGamma
      newClosedExtension newOrderedExtension newStrictExtension newNoRevisiting
  apply TashkinovSeriesStep.PE (i := i.castSucc) (choice := newChoice)
    (gamma := newGammaValue) (secondStable := newSecondStable)
  · rw [previousColoringEq]
    exact previousProper
  · rw [previousColoringEq]
    exact previousOneUncolored
  · rw [previousColoringEq, previousTreeEq]
    exact previousClosed
  · rw [previousColoringEq, previousTreeEq]
    exact previousNotStronglyClosed
  · exact newNoRevisiting
  · exact newSeriesAlternativeFails
  · exact newGammaRule
  · exact newSecondStableProper
  · exact newSecondStableOneUncolored
  · exact newSecondStableRelation
  · exact newExitWitness
  · exact newCurrentColoring
  · exact newCurrentProper
  · exact newCurrentOneUncolored
  · exact newCurrentStored
  · exact newCurrentEdges
  · exact newCurrentKind
  · exact newCurrentVertex
  · exact newCurrentOutside
  · exact newCurrentDelta
  · exact newCurrentGamma
  · exact newClosedExtension
  · exact newOrderedExtension
  · exact newStrictExtension

private theorem helper_continuation_615.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (data :
        TashkinovSeriesData G k rounds e0) (newTree : TreeSequence G e0) (newColoring :
        PartialEdgeColoring E k) (newStored : Finset (Fin k)) (newConnectingEdges : Finset E)
        (newKind : Option TashkinovExtensionKind) (newChosenVertex newOutsideVertex : Option V)
        (newDelta newGamma : Option (Fin k)),
    ∀ (i : Fin rounds), IsProperEdgeColoring G (data.coloring i.castSucc) → IsOneEdgeUncolored
        (data.coloring i.castSucc) e0 → ColoredVertexSetClosed G (data.coloring i.castSucc)
        (TreeSequenceVertexSet (data.tree i.succ.castSucc)) → ¬ColoredVertexSetStronglyClosed G
        (data.coloring i.castSucc) (TreeSequenceVertexSet (data.tree i.succ.castSucc)) → ¬Nonempty
        (RevisitingExtensionCertificate data i.castSucc) →
    ∀ (choice : MaximumDefectiveChoice G e0 (data.tree i.succ.castSucc) (TashkinovStoredColors
        data i.castSucc) (data.coloring i.castSucc)), (
    ∃ (rho : PartialEdgeColoring E k), IsProperEdgeColoring G rho ∧ IsOneEdgeUncolored rho e0 ∧
        StableColoring (data.tree i.succ.castSucc) (insert choice.color (TashkinovStoredColors
        data i.castSucc)) choice.selected rho ∧ ¬Disjoint (MissingColors G rho
        choice.otherEndpoint) (TreeMissingColors rho (data.tree i.succ.castSucc))) →
    ∀ (gamma : Fin k), ParallelExtensionColor data i.castSucc choice.selected choice.vertex gamma
        →
    ∀ (secondStable : PartialEdgeColoring E k), IsProperEdgeColoring G secondStable →
        IsOneEdgeUncolored secondStable e0 → StableColoring (data.tree i.succ.castSucc) (insert
        choice.color (TashkinovStoredColors data i.castSucc)) choice.selected secondStable →
        TreeExit (data.tree i.succ.castSucc) secondStable gamma choice.color choice.vertex →
        data.coloring i.succ = TwoColorComponentSwap G secondStable gamma choice.color (Sum.inl
        choice.vertex) → IsProperEdgeColoring G (data.coloring i.succ) → IsOneEdgeUncolored
        (data.coloring i.succ) e0 → data.stored i.succ = { choice.color, gamma } →
        data.connectingEdges i.succ = { choice.edge } → data.kind i.succ = some
        TashkinovExtensionKind.PE → data.chosenVertex i.succ = some choice.vertex →
        data.outsideVertex i.succ = some choice.otherEndpoint → data.delta i.succ = some
        choice.color → data.gamma i.succ = some gamma → TashkinovClosure (data.coloring i.succ)
        (data.tree i.succ.castSucc) (data.tree i.succ.succ) → TreeSequenceInitialSegment
        (data.tree i.succ.castSucc) (data.tree i.succ.succ) → (data.tree i.succ.castSucc).length <
        (data.tree i.succ.succ).length → i.castSucc.succ = i.succ.castSucc →
        (TashkinovSeriesDataAppend data newTree newColoring newStored newConnectingEdges newKind
        newChosenVertex newOutsideVertex newDelta newGamma : TashkinovSeriesData G k (rounds + (1
        : ℕ)) e0).tree i.castSucc.succ.castSucc = data.tree i.succ.castSucc →
        (TashkinovSeriesDataAppend data newTree newColoring newStored newConnectingEdges newKind
        newChosenVertex newOutsideVertex newDelta newGamma : TashkinovSeriesData G k (rounds + (1
        : ℕ)) e0).tree i.castSucc.succ.succ = data.tree i.succ.succ → (TashkinovSeriesDataAppend
        data newTree newColoring newStored newConnectingEdges newKind newChosenVertex
        newOutsideVertex newDelta newGamma : TashkinovSeriesData G k (rounds + (1 : ℕ))
        e0).coloring i.castSucc.castSucc = data.coloring i.castSucc → TashkinovStoredColors
        (TashkinovSeriesDataAppend data newTree newColoring newStored newConnectingEdges newKind
        newChosenVertex newOutsideVertex newDelta newGamma : TashkinovSeriesData G k (rounds + (1
        : ℕ)) e0) i.castSucc.castSucc = TashkinovStoredColors data i.castSucc →
        (TashkinovSeriesDataAppend data newTree newColoring newStored newConnectingEdges newKind
        newChosenVertex newOutsideVertex newDelta newGamma : TashkinovSeriesData G k (rounds + (1
        : ℕ)) e0).coloring i.castSucc.succ = data.coloring i.succ → (TashkinovSeriesDataAppend
        data newTree newColoring newStored newConnectingEdges newKind newChosenVertex
        newOutsideVertex newDelta newGamma : TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).stored
        i.castSucc.succ = data.stored i.succ → (TashkinovSeriesDataAppend data newTree newColoring
        newStored newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta newGamma :
        TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).connectingEdges i.castSucc.succ =
        data.connectingEdges i.succ → (TashkinovSeriesDataAppend data newTree newColoring
        newStored newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta newGamma :
        TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).kind i.castSucc.succ = data.kind i.succ →
        (TashkinovSeriesDataAppend data newTree newColoring newStored newConnectingEdges newKind
        newChosenVertex newOutsideVertex newDelta newGamma : TashkinovSeriesData G k (rounds + (1
        : ℕ)) e0).chosenVertex i.castSucc.succ = data.chosenVertex i.succ →
        (TashkinovSeriesDataAppend data newTree newColoring newStored newConnectingEdges newKind
        newChosenVertex newOutsideVertex newDelta newGamma : TashkinovSeriesData G k (rounds + (1
        : ℕ)) e0).outsideVertex i.castSucc.succ = data.outsideVertex i.succ →
        (TashkinovSeriesDataAppend data newTree newColoring newStored newConnectingEdges newKind
        newChosenVertex newOutsideVertex newDelta newGamma : TashkinovSeriesData G k (rounds + (1
        : ℕ)) e0).delta i.castSucc.succ = data.delta i.succ → (TashkinovSeriesDataAppend data
        newTree newColoring newStored newConnectingEdges newKind newChosenVertex newOutsideVertex
        newDelta newGamma : TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).gamma i.castSucc.succ =
        data.gamma i.succ → (ParallelExtensionColor (TashkinovSeriesDataAppend data newTree
        newColoring newStored newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta
        newGamma : TashkinovSeriesData G k (rounds + (1 : ℕ)) e0) i.castSucc.castSucc :
        PartialEdgeColoring E k → V → Fin k → Prop) = (ParallelExtensionColor data i.castSucc :
        PartialEdgeColoring E k → V → Fin k → Prop) → TashkinovSeriesStep G k (rounds + (1 : ℕ))
        e0 input (TashkinovSeriesDataAppend data newTree newColoring newStored newConnectingEdges
        newKind newChosenVertex newOutsideVertex newDelta newGamma) i.succ.castSucc := by
  classical
  intro V E _ _ _ G k rounds e0 input data newTree newColoring newStored newConnectingEdges
      newKind newChosenVertex newOutsideVertex newDelta newGamma
  set appended : TashkinovSeriesData G k (rounds + (1 : ℕ)) e0 := TashkinovSeriesDataAppend data
      newTree newColoring newStored newConnectingEdges newKind
            newChosenVertex
          newOutsideVertex newDelta newGamma
  intro i previousProper previousOneUncolored previousClosed previousNotStronglyClosed
      noRevisiting choice seriesAlternativeFails gamma gammaRule secondStable secondStableProper
      secondStableOneUncolored secondStableRelation exitWitness currentColoring currentProper
      currentOneUncolored currentStored currentEdges currentKind currentVertex currentOutside
      currentDelta currentGamma closedExtension orderedExtension strictExtension slotIndexEq
      previousTreeEq outputTreeEq previousColoringEq storedColorsEq currentColoringEq
      currentStoredEq currentEdgesEq currentKindEq currentVertexEq currentOutsideEq
      currentDeltaEq currentGammaEq
  set oldRule : PartialEdgeColoring E k → V → Fin k → Prop :=
    ParallelExtensionColor data i.castSucc
  set newRule : PartialEdgeColoring E k → V → Fin k → Prop :=
    ParallelExtensionColor
      (TashkinovSeriesDataAppend data newTree newColoring newStored newConnectingEdges newKind
        newChosenVertex newOutsideVertex newDelta newGamma :
        TashkinovSeriesData G k (rounds + 1) e0) i.castSucc.castSucc
  intro ruleEq
  let Package : (PartialEdgeColoring E k → V → Fin k → Prop) → PartialEdgeColoring E k →
      PartialEdgeColoring E k → TreeSequence G e0 → TreeSequence G e0 → Finset (Fin k) → Finset
      (Fin k) → Finset E → Option TashkinovExtensionKind → Option V → Option V → Option (Fin k) →
      Option (Fin k) → Prop :=
    fun
      (rule :
        PartialEdgeColoring E k →
          V → Fin k → Prop)
      (previousColor currentColor :
        PartialEdgeColoring E k)
      (previousTree outputTree :
        TreeSequence G e0)
      (storedColors
          currentStoredValue :
        Finset (Fin k))
      (currentEdgesValue : Finset E)
      (currentKindValue :
        Option
          TashkinovExtensionKind)
      (currentVertexValue
          currentOutsideValue :
        Option V)
      (currentDeltaValue
          currentGammaValue :
        Option (Fin k)) =>
    ∃
        (selectedChoice :
      MaximumDefectiveChoice G e0
        previousTree storedColors
        previousColor),
      (∃
          (rho :
          PartialEdgeColoring E k),
          IsProperEdgeColoring G
              rho ∧
            IsOneEdgeUncolored rho
                e0 ∧
              StableColoring
                  previousTree
                  (insert
                    selectedChoice.color
                    storedColors)
                  selectedChoice.selected
                  rho ∧
                ¬Disjoint
                    (MissingColors G
                      rho
                      selectedChoice.otherEndpoint)
                    (TreeMissingColors
                      rho
                      previousTree)) ∧
        ∃
            (selectedGamma : Fin k),
          rule
              selectedChoice.selected
              selectedChoice.vertex
              selectedGamma ∧
            ∃ (stableColoring :
              PartialEdgeColoring E
                k),
              IsProperEdgeColoring G
                  stableColoring ∧
                IsOneEdgeUncolored
                    stableColoring
                    e0 ∧
                  StableColoring
                      previousTree
                      (insert
                        selectedChoice.color
                        storedColors)
                      selectedChoice.selected
                      stableColoring ∧
                    TreeExit
                        previousTree
                        stableColoring
                        selectedGamma
                        selectedChoice.color
                        selectedChoice.vertex ∧
                      currentColor =
                          TwoColorComponentSwap
                            G
                            stableColoring
                            selectedGamma
                            selectedChoice.color
                            (Sum.inl
                              selectedChoice.vertex) ∧
                        IsProperEdgeColoring
                            G
                            currentColor ∧
                          IsOneEdgeUncolored
                              currentColor
                              e0 ∧
                            currentStoredValue =
                                {selectedChoice.color,
                                  selectedGamma} ∧
                              currentEdgesValue =
                                  {selectedChoice.edge} ∧
                                currentKindValue =
                                    some
                                      TashkinovExtensionKind.PE ∧
                                  currentVertexValue =
                                      some
                                        selectedChoice.vertex ∧
                                    currentOutsideValue =
                                        some
                                          selectedChoice.otherEndpoint ∧
                                      currentDeltaValue =
                                          some
                                            selectedChoice.color ∧
                                        currentGammaValue =
                                            some
                                              selectedGamma ∧
                                          TashkinovClosure
                                              currentColor
                                              previousTree
                                              outputTree ∧
                                            TreeSequenceInitialSegment
                                                previousTree
                                                outputTree ∧
                                              previousTree.length <
                                                outputTree.length
  have oldPackage : Package oldRule (data.coloring i.castSucc)
      (data.coloring i.succ) (data.tree i.succ.castSucc)
      (data.tree i.succ.succ) (TashkinovStoredColors data i.castSucc)
      (data.stored i.succ) (data.connectingEdges i.succ)
      (data.kind i.succ) (data.chosenVertex i.succ)
      (data.outsideVertex i.succ) (data.delta i.succ) (data.gamma i.succ) := by
    exact ⟨choice, seriesAlternativeFails, gamma, gammaRule, secondStable,
      secondStableProper, secondStableOneUncolored, secondStableRelation,
      exitWitness, currentColoring, currentProper, currentOneUncolored,
      currentStored, currentEdges, currentKind, currentVertex, currentOutside,
      currentDelta, currentGamma, closedExtension, orderedExtension,
      strictExtension⟩
  have newPackage : Package newRule (appended.coloring i.castSucc.castSucc)
      (appended.coloring i.castSucc.succ)
      (appended.tree i.castSucc.succ.castSucc)
      (appended.tree i.castSucc.succ.succ)
      (TashkinovStoredColors appended i.castSucc.castSucc)
      (appended.stored i.castSucc.succ)
      (appended.connectingEdges i.castSucc.succ)
      (appended.kind i.castSucc.succ)
      (appended.chosenVertex i.castSucc.succ)
      (appended.outsideVertex i.castSucc.succ)
      (appended.delta i.castSucc.succ) (appended.gamma i.castSucc.succ) := by
    rw [ruleEq, previousColoringEq, currentColoringEq, previousTreeEq,
      outputTreeEq, storedColorsEq, currentStoredEq, currentEdgesEq,
      currentKindEq, currentVertexEq, currentOutsideEq, currentDeltaEq,
      currentGammaEq]
    exact oldPackage
  rcases newPackage with ⟨newChoice, newSeriesAlternativeFails,
    newGammaValue, newGammaRule, newSecondStable, newSecondStableProper,
    newSecondStableOneUncolored, newSecondStableRelation, newExitWitness,
    newCurrentColoring, newCurrentProper, newCurrentOneUncolored,
    newCurrentStored, newCurrentEdges, newCurrentKind, newCurrentVertex,
    newCurrentOutside, newCurrentDelta, newCurrentGamma, newClosedExtension,
    newOrderedExtension, newStrictExtension⟩
  have newNoRevisiting : ¬ Nonempty
      (RevisitingExtensionCertificate appended i.castSucc.castSucc) := by
    rintro ⟨newCertificate⟩
    rcases (RevisitingExtensionCertificateAppend data newTree newColoring newStored
      newConnectingEdges newKind newChosenVertex newOutsideVertex
      newDelta newGamma i.castSucc).1 newCertificate with ⟨oldCertificate, -⟩
    exact noRevisiting ⟨oldCertificate⟩
  have lifted := @helper_lifted_488 V E inferInstance inferInstance inferInstance G k rounds e0
      input data newTree newColoring newStored newConnectingEdges newKind newChosenVertex
      newOutsideVertex newDelta newGamma i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed choice gamma secondStable previousTreeEq previousColoringEq
      newChoice newSeriesAlternativeFails newGammaValue newGammaRule newSecondStable
      newSecondStableProper newSecondStableOneUncolored newSecondStableRelation newExitWitness
      newCurrentColoring newCurrentProper newCurrentOneUncolored newCurrentStored newCurrentEdges
      newCurrentKind newCurrentVertex newCurrentOutside newCurrentDelta newCurrentGamma
      newClosedExtension newOrderedExtension newStrictExtension newNoRevisiting
  rw [← slotIndexEq]
  exact lifted

private theorem helper_branch_265.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (data :
        TashkinovSeriesData G k rounds e0) (newTree : TreeSequence G e0) (newColoring :
        PartialEdgeColoring E k) (newStored : Finset (Fin k)) (newConnectingEdges : Finset E)
        (newKind : Option TashkinovExtensionKind) (newChosenVertex newOutsideVertex : Option V)
        (newDelta newGamma : Option (Fin k)), (
    ∀ (i : Fin (rounds + (2 : ℕ))), (TashkinovSeriesDataAppend data newTree newColoring newStored
        newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta newGamma :
        TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).tree i.castSucc = data.tree i) → (
    ∀ (i : Fin (rounds + (1 : ℕ))), (TashkinovSeriesDataAppend data newTree newColoring newStored
        newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta newGamma :
        TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).coloring i.castSucc = data.coloring i ∧
        (TashkinovSeriesDataAppend data newTree newColoring newStored newConnectingEdges newKind
        newChosenVertex newOutsideVertex newDelta newGamma : TashkinovSeriesData G k (rounds + (1
        : ℕ)) e0).stored i.castSucc = data.stored i ∧ (TashkinovSeriesDataAppend data newTree
        newColoring newStored newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta
        newGamma : TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).connectingEdges i.castSucc =
        data.connectingEdges i ∧ (TashkinovSeriesDataAppend data newTree newColoring newStored
        newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta newGamma :
        TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).kind i.castSucc = data.kind i ∧
        (TashkinovSeriesDataAppend data newTree newColoring newStored newConnectingEdges newKind
        newChosenVertex newOutsideVertex newDelta newGamma : TashkinovSeriesData G k (rounds + (1
        : ℕ)) e0).chosenVertex i.castSucc = data.chosenVertex i ∧ (TashkinovSeriesDataAppend data
        newTree newColoring newStored newConnectingEdges newKind newChosenVertex newOutsideVertex
        newDelta newGamma : TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).outsideVertex
        i.castSucc = data.outsideVertex i ∧ (TashkinovSeriesDataAppend data newTree newColoring
        newStored newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta newGamma :
        TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).delta i.castSucc = data.delta i ∧
        (TashkinovSeriesDataAppend data newTree newColoring newStored newConnectingEdges newKind
        newChosenVertex newOutsideVertex newDelta newGamma : TashkinovSeriesData G k (rounds + (1
        : ℕ)) e0).gamma i.castSucc = data.gamma i) →
    ∀ (i : Fin rounds), IsProperEdgeColoring G (data.coloring i.castSucc) → IsOneEdgeUncolored
        (data.coloring i.castSucc) e0 → ColoredVertexSetClosed G (data.coloring i.castSucc)
        (TreeSequenceVertexSet (data.tree i.succ.castSucc)) → ¬ColoredVertexSetStronglyClosed G
        (data.coloring i.castSucc) (TreeSequenceVertexSet (data.tree i.succ.castSucc)) → ¬Nonempty
        (RevisitingExtensionCertificate data i.castSucc) →
    ∀ (choice : MaximumDefectiveChoice G e0 (data.tree i.succ.castSucc) (TashkinovStoredColors
        data i.castSucc) (data.coloring i.castSucc)), (
    ∃ (rho : PartialEdgeColoring E k), IsProperEdgeColoring G rho ∧ IsOneEdgeUncolored rho e0 ∧
        StableColoring (data.tree i.succ.castSucc) (insert choice.color (TashkinovStoredColors
        data i.castSucc)) choice.selected rho ∧ ¬Disjoint (MissingColors G rho
        choice.otherEndpoint) (TreeMissingColors rho (data.tree i.succ.castSucc))) →
    ∀ (gamma : Fin k), ParallelExtensionColor data i.castSucc choice.selected choice.vertex gamma
        →
    ∀ (secondStable : PartialEdgeColoring E k), IsProperEdgeColoring G secondStable →
        IsOneEdgeUncolored secondStable e0 → StableColoring (data.tree i.succ.castSucc) (insert
        choice.color (TashkinovStoredColors data i.castSucc)) choice.selected secondStable →
        TreeExit (data.tree i.succ.castSucc) secondStable gamma choice.color choice.vertex →
        data.coloring i.succ = TwoColorComponentSwap G secondStable gamma choice.color (Sum.inl
        choice.vertex) → IsProperEdgeColoring G (data.coloring i.succ) → IsOneEdgeUncolored
        (data.coloring i.succ) e0 → data.stored i.succ = {choice.color, gamma} →
        data.connectingEdges i.succ = { choice.edge } → data.kind i.succ = some
        TashkinovExtensionKind.PE → data.chosenVertex i.succ = some choice.vertex →
        data.outsideVertex i.succ = some choice.otherEndpoint → data.delta i.succ = some
        choice.color → data.gamma i.succ = some gamma → TashkinovClosure (data.coloring i.succ)
        (data.tree i.succ.castSucc) (data.tree i.succ.succ) → TreeSequenceInitialSegment
        (data.tree i.succ.castSucc) (data.tree i.succ.succ) → (data.tree i.succ.castSucc).length <
        (data.tree i.succ.succ).length → TashkinovSeriesStep G k (rounds + (1 : ℕ)) e0 input
        (TashkinovSeriesDataAppend data newTree newColoring newStored newConnectingEdges newKind
        newChosenVertex newOutsideVertex newDelta newGamma) i.succ.castSucc := by
  classical
  intro V E _ _ _ G k rounds e0 input data newTree newColoring newStored newConnectingEdges
      newKind newChosenVertex newOutsideVertex newDelta newGamma
  set appended : TashkinovSeriesData G k (rounds + (1 : ℕ)) e0 := TashkinovSeriesDataAppend data
      newTree newColoring newStored newConnectingEdges newKind
            newChosenVertex
          newOutsideVertex newDelta newGamma
  intro treeOld slotsOld i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails gamma gammaRule
      secondStable secondStableProper secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored currentEdges currentKind
      currentVertex currentOutside currentDelta currentGamma closedExtension orderedExtension
      strictExtension
  have slotIndexEq : i.castSucc.succ = i.succ.castSucc := by ext; rfl
  have previousTreeIndexEq : i.castSucc.succ.castSucc =
      i.succ.castSucc.castSucc := by ext; rfl
  have outputTreeIndexEq : i.castSucc.succ.succ =
      i.succ.succ.castSucc := by ext; rfl
  have previousTreeEq : appended.tree i.castSucc.succ.castSucc =
      data.tree i.succ.castSucc := by
    calc
      appended.tree i.castSucc.succ.castSucc =
          appended.tree i.succ.castSucc.castSucc :=
        congrArg appended.tree previousTreeIndexEq
      _ = data.tree i.succ.castSucc := treeOld i.succ.castSucc
  have outputTreeEq : appended.tree i.castSucc.succ.succ =
      data.tree i.succ.succ := by
    calc
      appended.tree i.castSucc.succ.succ =
          appended.tree i.succ.succ.castSucc :=
        congrArg appended.tree outputTreeIndexEq
      _ = data.tree i.succ.succ := treeOld i.succ.succ
  have previousColoringEq : appended.coloring i.castSucc.castSucc =
      data.coloring i.castSucc := (slotsOld i.castSucc).1
  have storedColorsEq : TashkinovStoredColors appended i.castSucc.castSucc =
      TashkinovStoredColors data i.castSucc :=
    TashkinovStoredColorsAppend data newTree newColoring newStored newConnectingEdges
      newKind newChosenVertex newOutsideVertex newDelta newGamma i.castSucc
  have currentColoringEq : appended.coloring i.castSucc.succ =
      data.coloring i.succ := by
    calc
      appended.coloring i.castSucc.succ =
          appended.coloring i.succ.castSucc :=
        congrArg appended.coloring slotIndexEq
      _ = data.coloring i.succ := (slotsOld i.succ).1
  have currentStoredEq : appended.stored i.castSucc.succ =
      data.stored i.succ := by
    calc
      appended.stored i.castSucc.succ = appended.stored i.succ.castSucc :=
        congrArg appended.stored slotIndexEq
      _ = data.stored i.succ := (slotsOld i.succ).2.1
  have currentEdgesEq : appended.connectingEdges i.castSucc.succ =
      data.connectingEdges i.succ := by
    calc
      appended.connectingEdges i.castSucc.succ =
          appended.connectingEdges i.succ.castSucc :=
        congrArg appended.connectingEdges slotIndexEq
      _ = data.connectingEdges i.succ := (slotsOld i.succ).2.2.1
  have currentKindEq : appended.kind i.castSucc.succ = data.kind i.succ := by
    calc
      appended.kind i.castSucc.succ = appended.kind i.succ.castSucc :=
        congrArg appended.kind slotIndexEq
      _ = data.kind i.succ := (slotsOld i.succ).2.2.2.1
  have currentVertexEq : appended.chosenVertex i.castSucc.succ =
      data.chosenVertex i.succ := by
    calc
      appended.chosenVertex i.castSucc.succ =
          appended.chosenVertex i.succ.castSucc :=
        congrArg appended.chosenVertex slotIndexEq
      _ = data.chosenVertex i.succ := (slotsOld i.succ).2.2.2.2.1
  have currentOutsideEq : appended.outsideVertex i.castSucc.succ =
      data.outsideVertex i.succ := by
    calc
      appended.outsideVertex i.castSucc.succ =
          appended.outsideVertex i.succ.castSucc :=
        congrArg appended.outsideVertex slotIndexEq
      _ = data.outsideVertex i.succ := (slotsOld i.succ).2.2.2.2.2.1
  have currentDeltaEq : appended.delta i.castSucc.succ = data.delta i.succ := by
    calc
      appended.delta i.castSucc.succ = appended.delta i.succ.castSucc :=
        congrArg appended.delta slotIndexEq
      _ = data.delta i.succ := (slotsOld i.succ).2.2.2.2.2.2.1
  have currentGammaEq : appended.gamma i.castSucc.succ = data.gamma i.succ := by
    calc
      appended.gamma i.castSucc.succ = appended.gamma i.succ.castSucc :=
        congrArg appended.gamma slotIndexEq
      _ = data.gamma i.succ := (slotsOld i.succ).2.2.2.2.2.2.2
  let oldRule := fun selected v gamma =>
    ParallelExtensionColor data i.castSucc selected v gamma
  let newRule := fun selected v gamma =>
    ParallelExtensionColor appended i.castSucc.castSucc selected v gamma
  have ruleEq : newRule = oldRule := by
    funext selected v gamma
    apply propext
    exact ParallelExtensionColorAppend data newTree newColoring newStored
      newConnectingEdges newKind newChosenVertex newOutsideVertex
      newDelta newGamma i.castSucc selected v gamma
  exact @helper_continuation_615 V E inferInstance inferInstance inferInstance G k rounds e0
      input data newTree newColoring newStored newConnectingEdges newKind newChosenVertex
      newOutsideVertex newDelta newGamma i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails gamma gammaRule
      secondStable secondStableProper secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored currentEdges currentKind
      currentVertex currentOutside currentDelta currentGamma closedExtension orderedExtension
      strictExtension slotIndexEq previousTreeEq outputTreeEq previousColoringEq storedColorsEq
      currentColoringEq currentStoredEq currentEdgesEq currentKindEq currentVertexEq
      currentOutsideEq currentDeltaEq currentGammaEq ruleEq
private theorem helper_branch_472.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (data :
        TashkinovSeriesData G k rounds e0) (newTree : TreeSequence G e0) (newColoring :
        PartialEdgeColoring E k) (newStored : Finset (Fin k)) (newConnectingEdges : Finset E)
        (newKind : Option TashkinovExtensionKind) (newChosenVertex newOutsideVertex : Option V)
        (newDelta newGamma : Option (Fin k)), (
    ∀ (i : Fin (rounds + (2 : ℕ))), (TashkinovSeriesDataAppend data newTree newColoring newStored
        newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta newGamma :
        TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).tree i.castSucc = data.tree i) → (
    ∀ (i : Fin (rounds + (1 : ℕ))), (TashkinovSeriesDataAppend data newTree newColoring newStored
        newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta newGamma :
        TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).coloring i.castSucc = data.coloring i ∧
        (TashkinovSeriesDataAppend data newTree newColoring newStored newConnectingEdges newKind
        newChosenVertex newOutsideVertex newDelta newGamma : TashkinovSeriesData G k (rounds + (1
        : ℕ)) e0).stored i.castSucc = data.stored i ∧ (TashkinovSeriesDataAppend data newTree
        newColoring newStored newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta
        newGamma : TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).connectingEdges i.castSucc =
        data.connectingEdges i ∧ (TashkinovSeriesDataAppend data newTree newColoring newStored
        newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta newGamma :
        TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).kind i.castSucc = data.kind i ∧
        (TashkinovSeriesDataAppend data newTree newColoring newStored newConnectingEdges newKind
        newChosenVertex newOutsideVertex newDelta newGamma : TashkinovSeriesData G k (rounds + (1
        : ℕ)) e0).chosenVertex i.castSucc = data.chosenVertex i ∧ (TashkinovSeriesDataAppend data
        newTree newColoring newStored newConnectingEdges newKind newChosenVertex newOutsideVertex
        newDelta newGamma : TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).outsideVertex
        i.castSucc = data.outsideVertex i ∧ (TashkinovSeriesDataAppend data newTree newColoring
        newStored newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta newGamma :
        TashkinovSeriesData G k (rounds + (1 : ℕ)) e0).delta i.castSucc = data.delta i ∧
        (TashkinovSeriesDataAppend data newTree newColoring newStored newConnectingEdges newKind
        newChosenVertex newOutsideVertex newDelta newGamma : TashkinovSeriesData G k (rounds + (1
        : ℕ)) e0).gamma i.castSucc = data.gamma i) →
    ∀ (i : Fin rounds), IsProperEdgeColoring G (data.coloring i.castSucc) → IsOneEdgeUncolored
        (data.coloring i.castSucc) e0 → ColoredVertexSetClosed G (data.coloring i.castSucc)
        (TreeSequenceVertexSet (data.tree i.succ.castSucc)) → ¬ColoredVertexSetStronglyClosed G
        (data.coloring i.castSucc) (TreeSequenceVertexSet (data.tree i.succ.castSucc)) →
    ∀ (available : RevisitingExtensionCertificate data i.castSucc), data.coloring i.succ =
        data.coloring i.castSucc → data.stored i.succ = { available.delta, available.gamma } →
        data.connectingEdges i.succ = { available.edge } → data.kind i.succ = some
        TashkinovExtensionKind.RE → data.chosenVertex i.succ = some available.insideEndpoint →
        data.outsideVertex i.succ = some available.outsideEndpoint → data.delta i.succ = some
        available.delta → data.gamma i.succ = some available.gamma →
    ∀ (adjoined : TreeSequence G e0), TreeSequenceAdjoinEdge (data.tree i.succ.castSucc)
        available.edge adjoined → TashkinovClosure (data.coloring i.succ) adjoined (data.tree
        i.succ.succ) → TreeSequenceInitialSegment (data.tree i.succ.castSucc) (data.tree
        i.succ.succ) → (data.tree i.succ.castSucc).length < (data.tree i.succ.succ).length →
        TashkinovSeriesStep G k (rounds + (1 : ℕ)) e0 input (TashkinovSeriesDataAppend data
        newTree newColoring newStored newConnectingEdges newKind newChosenVertex newOutsideVertex
        newDelta newGamma) i.succ.castSucc := by
  classical
  intro V E _ _ _ G k rounds e0 input data newTree newColoring newStored newConnectingEdges
      newKind newChosenVertex newOutsideVertex newDelta newGamma
  set appended : TashkinovSeriesData G k (rounds + (1 : ℕ)) e0 := TashkinovSeriesDataAppend data
      newTree newColoring newStored newConnectingEdges newKind
            newChosenVertex
          newOutsideVertex newDelta newGamma
  intro treeOld slotsOld i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored currentEdges currentKind
      currentVertex currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension
  have slotIndexEq : i.castSucc.succ = i.succ.castSucc := by ext; rfl
  have previousTreeIndexEq : i.castSucc.succ.castSucc =
      i.succ.castSucc.castSucc := by ext; rfl
  have outputTreeIndexEq : i.castSucc.succ.succ =
      i.succ.succ.castSucc := by ext; rfl
  have previousTreeEq : appended.tree i.castSucc.succ.castSucc =
      data.tree i.succ.castSucc := by
    calc
      appended.tree i.castSucc.succ.castSucc =
          appended.tree i.succ.castSucc.castSucc :=
        congrArg appended.tree previousTreeIndexEq
      _ = data.tree i.succ.castSucc := treeOld i.succ.castSucc
  have outputTreeEq : appended.tree i.castSucc.succ.succ =
      data.tree i.succ.succ := by
    calc
      appended.tree i.castSucc.succ.succ =
          appended.tree i.succ.succ.castSucc :=
        congrArg appended.tree outputTreeIndexEq
      _ = data.tree i.succ.succ := treeOld i.succ.succ
  have previousColoringEq : appended.coloring i.castSucc.castSucc =
      data.coloring i.castSucc := (slotsOld i.castSucc).1
  have currentColoringEq : appended.coloring i.castSucc.succ =
      data.coloring i.succ := by
    calc
      appended.coloring i.castSucc.succ =
          appended.coloring i.succ.castSucc :=
        congrArg appended.coloring slotIndexEq
      _ = data.coloring i.succ := (slotsOld i.succ).1
  have currentStoredEq : appended.stored i.castSucc.succ =
      data.stored i.succ := by
    calc
      appended.stored i.castSucc.succ = appended.stored i.succ.castSucc :=
        congrArg appended.stored slotIndexEq
      _ = data.stored i.succ := (slotsOld i.succ).2.1
  have currentEdgesEq : appended.connectingEdges i.castSucc.succ =
      data.connectingEdges i.succ := by
    calc
      appended.connectingEdges i.castSucc.succ =
          appended.connectingEdges i.succ.castSucc :=
        congrArg appended.connectingEdges slotIndexEq
      _ = data.connectingEdges i.succ := (slotsOld i.succ).2.2.1
  have currentKindEq : appended.kind i.castSucc.succ = data.kind i.succ := by
    calc
      appended.kind i.castSucc.succ = appended.kind i.succ.castSucc :=
        congrArg appended.kind slotIndexEq
      _ = data.kind i.succ := (slotsOld i.succ).2.2.2.1
  have currentVertexEq : appended.chosenVertex i.castSucc.succ =
      data.chosenVertex i.succ := by
    calc
      appended.chosenVertex i.castSucc.succ =
          appended.chosenVertex i.succ.castSucc :=
        congrArg appended.chosenVertex slotIndexEq
      _ = data.chosenVertex i.succ := (slotsOld i.succ).2.2.2.2.1
  have currentOutsideEq : appended.outsideVertex i.castSucc.succ =
      data.outsideVertex i.succ := by
    calc
      appended.outsideVertex i.castSucc.succ =
          appended.outsideVertex i.succ.castSucc :=
        congrArg appended.outsideVertex slotIndexEq
      _ = data.outsideVertex i.succ := (slotsOld i.succ).2.2.2.2.2.1
  have currentDeltaEq : appended.delta i.castSucc.succ = data.delta i.succ := by
    calc
      appended.delta i.castSucc.succ = appended.delta i.succ.castSucc :=
        congrArg appended.delta slotIndexEq
      _ = data.delta i.succ := (slotsOld i.succ).2.2.2.2.2.2.1
  have currentGammaEq : appended.gamma i.castSucc.succ = data.gamma i.succ := by
    calc
      appended.gamma i.castSucc.succ = appended.gamma i.succ.castSucc :=
        congrArg appended.gamma slotIndexEq
      _ = data.gamma i.succ := (slotsOld i.succ).2.2.2.2.2.2.2
  rcases (RevisitingExtensionCertificateAppend data newTree newColoring newStored
      newConnectingEdges newKind newChosenVertex newOutsideVertex
      newDelta newGamma i.castSucc).2 available with
    ⟨newAvailable, availableGamma, availableDelta, availableEdge,
      availableInside, availableOutside⟩
  have lifted : TashkinovSeriesStep G k (rounds + 1) e0 input appended
      i.castSucc.succ := by
    apply TashkinovSeriesStep.RE (i := i.castSucc)
      (available := newAvailable) (adjoined := adjoined)
    · rw [previousColoringEq]
      exact previousProper
    · rw [previousColoringEq]
      exact previousOneUncolored
    · rw [previousColoringEq, previousTreeEq]
      exact previousClosed
    · rw [previousColoringEq, previousTreeEq]
      exact previousNotStronglyClosed
    · rw [currentColoringEq, previousColoringEq]
      exact currentColoring
    · rw [currentStoredEq, availableDelta, availableGamma]
      exact currentStored
    · rw [currentEdgesEq, availableEdge]
      exact currentEdges
    · rw [currentKindEq]
      exact currentKind
    · rw [currentVertexEq, availableInside]
      exact currentVertex
    · rw [currentOutsideEq, availableOutside]
      exact currentOutside
    · rw [currentDeltaEq, availableDelta]
      exact currentDelta
    · rw [currentGammaEq, availableGamma]
      exact currentGamma
    · rw [previousTreeEq, availableEdge]
      exact adjoinedExactly
    · rw [currentColoringEq, outputTreeEq]
      exact closedExtension
    · rw [previousTreeEq, outputTreeEq]
      exact orderedExtension
    · rw [previousTreeEq, outputTreeEq]
      exact strictExtension
  rw [← slotIndexEq]
  exact lifted

theorem TashkinovSeriesStepAppend {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k)
    (data : TashkinovSeriesData G k rounds e0)
    (newTree : TreeSequence G e0)
    (newColoring : PartialEdgeColoring E k)
    (newStored : Finset (Fin k))
    (newConnectingEdges : Finset E)
    (newKind : Option TashkinovExtensionKind)
    (newChosenVertex newOutsideVertex : Option V)
    (newDelta newGamma : Option (Fin k))
    (j : Fin (rounds + 1))
    (step : TashkinovSeriesStep G k rounds e0 input data j) :
    TashkinovSeriesStep G k (rounds + 1) e0 input
      (TashkinovSeriesDataAppend data newTree newColoring newStored newConnectingEdges
        newKind newChosenVertex newOutsideVertex newDelta newGamma)
      j.castSucc := by
  let appended := TashkinovSeriesDataAppend data newTree newColoring
    newStored newConnectingEdges newKind newChosenVertex newOutsideVertex
    newDelta newGamma
  have treeOld : ∀ i : Fin (rounds + 2),
      appended.tree i.castSucc = data.tree i := by
    intro i
    simp [appended, TashkinovSeriesDataAppend]
  have slotsOld :
    ∀ i : Fin (rounds + 1), appended.coloring i.castSucc = data.coloring i ∧ appended.stored
        i.castSucc = data.stored i ∧ appended.connectingEdges i.castSucc = data.connectingEdges i
        ∧ appended.kind i.castSucc = data.kind i ∧ appended.chosenVertex i.castSucc =
        data.chosenVertex i ∧ appended.outsideVertex i.castSucc = data.outsideVertex i ∧
        appended.delta i.castSucc = data.delta i ∧ appended.gamma i.castSucc = data.gamma i := by
    intro i
    simp [appended, TashkinovSeriesDataAppend]
  have treeZeroIndex : (0 : Fin ((rounds + 1) + 2)) =
      (0 : Fin (rounds + 2)).castSucc := by ext; rfl
  have treeOneIndex : (1 : Fin ((rounds + 1) + 2)) =
      (1 : Fin (rounds + 2)).castSucc := by ext; rfl
  have slotZeroIndex : (0 : Fin ((rounds + 1) + 1)) =
      (0 : Fin (rounds + 1)).castSucc := by ext; rfl
  cases step with
  | initial triple seedLength initialColoring initialStored initialEdges initialKind
      initialVertex initialOutside initialDelta initialGamma initialClosure =>
      apply TashkinovSeriesStep.initial triple
      · rw [treeZeroIndex, treeOld]
        exact seedLength
      · rw [slotZeroIndex, (slotsOld 0).1]
        exact initialColoring
      · rw [slotZeroIndex, (slotsOld 0).2.1]
        exact initialStored
      · rw [slotZeroIndex, (slotsOld 0).2.2.1]
        exact initialEdges
      · rw [slotZeroIndex, (slotsOld 0).2.2.2.1]
        exact initialKind
      · rw [slotZeroIndex, (slotsOld 0).2.2.2.2.1]
        exact initialVertex
      · rw [slotZeroIndex, (slotsOld 0).2.2.2.2.2.1]
        exact initialOutside
      · rw [slotZeroIndex, (slotsOld 0).2.2.2.2.2.2.1]
        exact initialDelta
      · rw [slotZeroIndex, (slotsOld 0).2.2.2.2.2.2.2]
        exact initialGamma
      · rw [treeZeroIndex, treeOneIndex, treeOld, treeOld,
          slotZeroIndex, (slotsOld 0).1]
        exact initialClosure
  | SE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
          exact @helper_branch_92 V E inferInstance inferInstance inferInstance G k rounds e0
              input data newTree newColoring newStored newConnectingEdges newKind newChosenVertex
              newOutsideVertex newDelta newGamma treeOld slotsOld i previousProper
              previousOneUncolored previousClosed previousNotStronglyClosed noRevisiting choice
              seriesAlternative currentColoring currentStored currentEdges currentKind
              currentVertex currentOutside currentDelta currentGamma adjoined adjoinedExactly
              closedExtension orderedExtension strictExtension
  | PE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper secondStableOneUncolored
      secondStableRelation exitWitness currentColoring currentProper
      currentOneUncolored currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma closedExtension orderedExtension
      strictExtension =>
          exact @helper_branch_265 V E inferInstance inferInstance inferInstance G k rounds e0
              input data newTree newColoring newStored newConnectingEdges newKind newChosenVertex
              newOutsideVertex newDelta newGamma treeOld slotsOld i previousProper
              previousOneUncolored previousClosed previousNotStronglyClosed noRevisiting choice
              seriesAlternativeFails gamma gammaRule secondStable secondStableProper
              secondStableOneUncolored secondStableRelation exitWitness currentColoring
              currentProper currentOneUncolored currentStored currentEdges currentKind
              currentVertex currentOutside currentDelta currentGamma closedExtension
              orderedExtension strictExtension
  | RE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
          exact @helper_branch_472 V E inferInstance inferInstance inferInstance G k rounds e0
              input data newTree newColoring newStored newConnectingEdges newKind newChosenVertex
              newOutsideVertex newDelta newGamma treeOld slotsOld i previousProper
              previousOneUncolored previousClosed previousNotStronglyClosed available
              currentColoring currentStored currentEdges currentKind currentVertex currentOutside
              currentDelta currentGamma adjoined adjoinedExactly closedExtension orderedExtension
              strictExtension
end GoldbergSeymour

end
