/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchySituationTwoSubcaseThreeOne.Preparation2

public import LeanPool.GoldbergSeymour.ChangeLemma
public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary
public import LeanPool.GoldbergSeymour.CombinedStableClosurePreserved
public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTree
public import LeanPool.GoldbergSeymour.GoodHierarchy
public import LeanPool.GoldbergSeymour.GoodHierarchyReservedDisjoint
public import LeanPool.GoldbergSeymour.HierarchyCounterexample
public import LeanPool.GoldbergSeymour.HierarchyCounterexampleLess
public import LeanPool.GoldbergSeymour.HierarchyCounterexampleMeasure
public import LeanPool.GoldbergSeymour.HierarchyCounterexamplePenultimateElementary
public import LeanPool.GoldbergSeymour.HierarchyFirstMissingPosition
public import LeanPool.GoldbergSeymour.HierarchyFullTailLength
public import LeanPool.GoldbergSeymour.HierarchyFullTailPrefix
public import LeanPool.GoldbergSeymour.HierarchyMinimumCounterexampleContext
public import LeanPool.GoldbergSeymour.HierarchyNonparallelFirstEdge
public import LeanPool.GoldbergSeymour.HierarchyPathNumber
public import LeanPool.GoldbergSeymour.HierarchyReplacementPresentation
public import LeanPool.GoldbergSeymour.HierarchySegmentColors
public import LeanPool.GoldbergSeymour.HierarchySituationTwoCaseOneData
public import LeanPool.GoldbergSeymour.HierarchySituationTwoCaseThreeNormalization
public import LeanPool.GoldbergSeymour.HierarchySituationTwoCaseThreeOneData
public import LeanPool.GoldbergSeymour.HierarchySituationTwoReorderedTrees
public import LeanPool.GoldbergSeymour.HierarchySituationTwoReorderedTreesCertified
public import LeanPool.GoldbergSeymour.HierarchySituationTwoSubcaseOneOne
public import LeanPool.GoldbergSeymour.HierarchySituationTwoTailData
public import LeanPool.GoldbergSeymour.HierarchyStageMissingColors
public import LeanPool.GoldbergSeymour.HierarchyStarredStage
public import LeanPool.GoldbergSeymour.HierarchyStoredColorsAt
public import LeanPool.GoldbergSeymour.HierarchyTailMissingColorExclusion
public import LeanPool.GoldbergSeymour.HierarchyWeaklyStable
public import LeanPool.GoldbergSeymour.IsOneEdgeUncolored
public import LeanPool.GoldbergSeymour.MissingColors
public import LeanPool.GoldbergSeymour.ModColoring
public import LeanPool.GoldbergSeymour.OrderedTreeUnion
public import LeanPool.GoldbergSeymour.SameGoodHierarchy
public import LeanPool.GoldbergSeymour.StableColoring
public import LeanPool.GoldbergSeymour.StableChangeCasesOneTwo
public import LeanPool.GoldbergSeymour.StableChangeCasesOneTwoFullTail
public import LeanPool.GoldbergSeymour.StableChangeCasesOneTwoSplitTail
public import LeanPool.GoldbergSeymour.TashkinovAugmentation
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequence
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceColoringTransport
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceRestrict
public import LeanPool.GoldbergSeymour.TashkinovClosure
public import LeanPool.GoldbergSeymour.TashkinovHierarchy
public import LeanPool.GoldbergSeymour.TashkinovSeries
public import LeanPool.GoldbergSeymour.TashkinovSeriesStep
public import LeanPool.GoldbergSeymour.TashkinovStoredColors
public import LeanPool.GoldbergSeymour.TreeColoringInvariant
public import LeanPool.GoldbergSeymour.TreeIncidentEdge
public import LeanPool.GoldbergSeymour.TreeMissingColors
public import LeanPool.GoldbergSeymour.TreeSequence
public import LeanPool.GoldbergSeymour.TreeSequenceAdjoinEdge
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegment
public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet
public import LeanPool.GoldbergSeymour.TwoColorComponent
public import LeanPool.GoldbergSeymour.TwoColorComponentsDisjoint
public import LeanPool.GoldbergSeymour.TwoColorComponentSpanningPath
public import LeanPool.GoldbergSeymour.TwoColorComponentSwap
public import LeanPool.GoldbergSeymour.TwoColorComponentSwapProper
public import LeanPool.GoldbergSeymour.TwoColorIncidenceDegreeAtMostTwo
public import LeanPool.GoldbergSeymour.TwoColorIncidenceGraph
public import LeanPool.GoldbergSeymour.TwoColorPathComponent
public import LeanPool.GoldbergSeymour.StableColoringEquivalence
public import LeanPool.GoldbergSeymour.TwoColorComponentSwapMissingBehavior
public import LeanPool.GoldbergSeymour.MinimumContextTransport
public import LeanPool.GoldbergSeymour.HierarchyMeasures
public import LeanPool.GoldbergSeymour.HierarchyReplacementPresentationTrans
public import LeanPool.GoldbergSeymour.HierarchyFirstMissingPositionPrefixCutoff
public import LeanPool.GoldbergSeymour.MissingColorIncidenceEndpoint
public import LeanPool.GoldbergSeymour.TerminalStoredColors
public import LeanPool.GoldbergSeymour.BaseDisplayedEdges
public import LeanPool.GoldbergSeymour.TerminalRoute
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceSuffix

/-!
# Hierarchy Situation Two Subcase Three One

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open HierarchySituationTwoSubcaseThreeOnePreparation

theorem HierarchySituationTwoSubcaseThreeOne {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (D : HierarchySituationTwoCaseThreeOneData
      G k e0 input T phi ett base C ctx) :
    False := by
  classical
  let alpha : Fin k := D.alpha
  let theta : Fin k := D.theta
  let lastIndex : Fin T.length := D.lastEdgeIndex
  let penIndex : Fin (T.length + 1) := D.penultimateVertexIndex
  let endIndex : Fin (T.length + 1) := D.terminalVertexIndex
  let H := C.hierarchy
  let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
  let A := HierarchyStarredStage H q
  let ell := HierarchyFullTailLength C
  let B := HierarchyFullTailPrefix C (ell - 2)
  let Bplus := HierarchyFullTailPrefix C (ell - 1)
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn := ett.series.data.tree n.castSucc
  have lastColor : phi (T.edge lastIndex) = some theta := D.thetaOnLastEdge
  have alphaTerminal : alpha ∈ MissingColors G phi (T.vertex endIndex) := D.alphaMissingTerminal
  have alphaBefore : alpha ∈ TreeMissingColors phi B := D.alphaMissingTwoBefore
  have alphaUnused : ∀ t : Fin T.length, A.length ≤ t.val → phi (T.edge t) ≠ some alpha :=
    D.alphaUnusedOnFullTail
  have lastPosition : lastIndex.val + 1 = T.length := D.lastEdgePosition
  have penPosition : penIndex.val + 1 = T.length := D.penultimateVertexPosition
  have endPosition : endIndex.val = T.length := D.terminalVertexPosition
  have thetaPresent : theta ∉ MissingColors G phi (T.vertex penIndex) := D.thetaPresentPenultimate
  have oldRoute := P2813_T1_TerminalRoute G k e0 input T phi ett
  have h_exception := helper_h_exception_6390 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base)
      (@C) (@ctx) (@D) (@lastColor) (@alphaTerminal) (@alphaBefore) (@lastPosition) (@penPosition)
      (@endPosition) (@thetaPresent)
  exact helper_continuation_3712 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
      (@D)
      (@lastColor) (@alphaTerminal) (@alphaBefore) (@alphaUnused) (@lastPosition) (@penPosition)
      (@endPosition) (@oldRoute) (@h_exception)
end GoldbergSeymour

end
