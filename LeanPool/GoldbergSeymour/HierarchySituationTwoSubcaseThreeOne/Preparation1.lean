/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

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
# HierarchySituationTwoSubcaseThreeOne: supporting constructions, part 1

Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
This module separates dependent data constructors from their supporting proofs.
-/

@[expose] public section

namespace GoldbergSeymour.HierarchySituationTwoSubcaseThreeOnePreparation

/-- Typed data construction shared by the hierarchy construction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
noncomputable abbrev helperPOne1741.{u_1, u_2} :
    open scoped Classical in
  {V : Type u_1} →
  {E : Type u_2} →
  [Fintype V] →
  [Fintype E] →
  [DecidableEq V] →
  [DecidableEq E] →
  (G : LooplessMultigraph V E) →
  (k : ℕ) →
  (e0 : E) →
  (input : PartialEdgeColoring E k) →
  (T : TreeSequence G e0) →
  (phi : PartialEdgeColoring E k) →
  (ett : ExtendedTashkinovTree G k e0 input T phi) →
  (base : HierarchyBase ett phi) →
  (C : HierarchyCounterexample base) →
  (ctx :
      HierarchyMinimumCounterexampleContext G k e0 input T phi ett
        base C) →
  (D :
      HierarchySituationTwoCaseThreeOneData G k e0 input T phi
        ett base C ctx) →
  let alpha : Fin k := D.alpha;
  let theta : Fin k := D.theta;
  let endIndex : Fin (T.length + (1 : ℕ)) :=
    D.terminalVertexIndex;
  let z : V ⊕ E := Sum.inl (T.vertex endIndex);
  let muOne : PartialEdgeColoring E k :=
    TwoColorComponentSwap G phi theta alpha z;
  (corrOne :
      CorrespondingExtendedTashkinovTree G k e0 ett muOne T) →
  MaximumProperty corrOne.replacementETT →
  (baseOne : HierarchyBase corrOne.replacementETT muOne) →
  (COne : HierarchyCounterexample baseOne) →
  SameGoodHierarchy C.good COne.good →
  HierarchyMinimumCounterexampleContext G k e0
      corrOne.replacementInput T muOne
      corrOne.replacementETT baseOne COne →
  HierarchyReplacementPresentation G k e0 input T
    phi ett base C ctx := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D alpha theta endIndex z muOne corrOne
      maxOne baseOne COne sameOne ctxOne
  exact {
    coloring := muOne
    corresponding := corrOne
    maximum := maxOne
    replacementBase := baseOne
    counterexample := COne
    sameGood := sameOne
    minimumContext := ctxOne }

/-- Typed data construction shared by the hierarchy construction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
noncomputable abbrev helperFinalData2160.{u_1, u_2} :
    open scoped Classical in
  {V : Type u_1} →
  {E : Type u_2} →
  [Fintype V] →
  [Fintype E] →
  [DecidableEq V] →
  [DecidableEq E] →
  (G : LooplessMultigraph V E) →
  (k : ℕ) →
  (e0 : E) →
  (input : PartialEdgeColoring E k) →
  (T : TreeSequence G e0) →
  (phi : PartialEdgeColoring E k) →
  (ett : ExtendedTashkinovTree G k e0 input T phi) →
  (base : HierarchyBase ett phi) →
  (C : HierarchyCounterexample base) →
  (ctx :
      HierarchyMinimumCounterexampleContext G k e0 input T phi ett
        base C) →
  (D :
      HierarchySituationTwoCaseThreeOneData G k e0 input T phi
        ett base C ctx) →
  let alpha : Fin k := D.alpha;
  let theta : Fin k := D.theta;
  let lastIndex : Fin T.length := D.lastEdgeIndex;
  let penIndex : Fin (T.length + (1 : ℕ)) :=
    D.penultimateVertexIndex;
  let endIndex : Fin (T.length + (1 : ℕ)) :=
    D.terminalVertexIndex;
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) :=
    Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let ell : ℕ := HierarchyFullTailLength C;
  (↑lastIndex : ℕ) + (1 : ℕ) = T.length →
  (↑penIndex : ℕ) + (1 : ℕ) = T.length →
  (↑endIndex : ℕ) = T.length →
  (eta : Fin k) →
  (2 : ℕ) ≤ ell →
  let z : V ⊕ E := Sum.inl (T.vertex endIndex);
  let muOne : PartialEdgeColoring E k :=
    TwoColorComponentSwap G phi theta alpha z;
  let muTwo : PartialEdgeColoring E k :=
    TwoColorComponentSwap G muOne theta eta z;
  eta ∈ MissingColors G muTwo (T.vertex endIndex) →
  eta ∈
      MissingColors G muTwo (T.vertex penIndex) →
  muTwo (T.edge lastIndex) = some alpha →
  (PTwo :
      HierarchyReplacementPresentation G k e0
        input T phi ett base C ctx) →
  PTwo.coloring = muTwo →
  alpha ∉
      MissingColors G muTwo
        (T.vertex penIndex) →
  HierarchyStarredStage
        PTwo.counterexample.hierarchy
        (Fin.last
          PTwo.counterexample.hierarchy.dividerCount) =
      A →
  HierarchyPathNumber C.hierarchy =
      HierarchyPathNumber
        PTwo.counterexample.hierarchy →
  eta ∈
      HierarchyStoredColorsAt
        PTwo.counterexample.hierarchy
        (Fin.last
          PTwo.counterexample.hierarchy.dividerCount) →
  (gammaOne gammaTwo : Fin k) →
  gammaOne ≠ gammaTwo →
  PTwo.counterexample.good.gamma
        (Fin.last
          PTwo.counterexample.hierarchy.dividerCount)
        eta =
      (insert gammaOne
          ({ gammaTwo } :
            Finset (Fin k)) :
        Finset (Fin k)) →
  HierarchySituationTwoCaseOneData
    G k e0
    PTwo.corresponding.replacementInput
    T PTwo.coloring
    PTwo.corresponding.replacementETT
    PTwo.replacementBase
    PTwo.counterexample
    PTwo.minimumContext := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D alpha theta lastIndex penIndex endIndex H
      q A ell lastPosition penPosition endPosition eta hTailAtLeast z muOne muTwo etaTerminalTwo
      etaPenultimateTwo lastTwo PTwo colorTwo alphaPresentTwo starTwo pathTwoEq etaStoredTwo
      gammaOne gammaTwo gammaDistinct gammaPair
  exact {
    tailAtLeastTwo := by
      change 2 ≤ T.length - (HierarchyStarredStage PTwo.counterexample.hierarchy
        (Fin.last PTwo.counterexample.hierarchy.dividerCount)).length
      rw [starTwo]
      exact hTailAtLeast
    pathNumberFull := by
      rw [← pathTwoEq]
      change HierarchyPathNumber C.hierarchy = T.length -
        (HierarchyStarredStage PTwo.counterexample.hierarchy
          (Fin.last PTwo.counterexample.hierarchy.dividerCount)).length
      rw [starTwo]
      exact D.pathNumberFull
    lastEdgeIndex := lastIndex
    penultimateVertexIndex := penIndex
    terminalVertexIndex := endIndex
    lastEdgePosition := lastPosition
    penultimateVertexPosition := penPosition
    terminalVertexPosition := endPosition
    lastEdgeNotIncidentPenultimate := D.lastEdgeNotIncidentPenultimate
    theta := alpha
    thetaOnLastEdge := colorTwo.symm ▸ lastTwo
    thetaPresentPenultimate := colorTwo.symm ▸ alphaPresentTwo
    alpha := eta
    gammaOne := gammaOne
    gammaTwo := gammaTwo
    alphaMissingPenultimate := colorTwo.symm ▸ etaPenultimateTwo
    alphaMissingTerminal := colorTwo.symm ▸ etaTerminalTwo
    alphaStored := etaStoredTwo
    gammaPair := gammaPair
    gammaDistinct := gammaDistinct }

/-- Dependent contract shared by the hierarchy construction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperContinuation3310Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base)
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
   (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
  let alpha : Fin k := D.alpha;
  let theta : Fin k := D.theta;
  let lastIndex : Fin T.length := D.lastEdgeIndex;
  let penIndex : Fin (T.length + (1 : ℕ)) := D.penultimateVertexIndex;
  let endIndex : Fin (T.length + (1 : ℕ)) := D.terminalVertexIndex;
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let ell : ℕ := HierarchyFullTailLength C;
  ∀ (B Bplus : TreeSequence G e0),
  let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
  let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
  phi (T.edge lastIndex) = some theta →
  alpha ∈ MissingColors G phi (T.vertex endIndex) →
  alpha ∈ TreeMissingColors phi B →
  (
  ∀ (t : Fin T.length),
  A.length ≤ (↑t : ℕ) →
  phi (T.edge t) ≠ some alpha) →
  (↑lastIndex : ℕ) + (1 : ℕ) = T.length →
  (↑penIndex : ℕ) + (1 : ℕ) = T.length →
  (↑endIndex : ℕ) = T.length →
  (
  have n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
  have Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
  have Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
  ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
    TashkinovAugmentationSequence phi Tn T ∨
   (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
     ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
    ∃ (f : E) (seed : TreeSequence G e0),
     ett.series.data.connectingEdges n = ({ f } : Finset E) ∧
      TreeSequenceAdjoinEdge Tn f seed ∧
       TreeIncidentEdge Tn f ∧
        (∃ c ∈ TreeMissingColors phi Tn ∪ Dn, phi f = some c) ∧
         TashkinovAugmentationSequence phi seed T) →
  ∀ eta ∈ HierarchyStoredColorsAt H q,
  eta ∈ MissingColors G phi (T.vertex penIndex) →
  theta ∈ C.good.gamma q eta →
  (2 : ℕ) ≤ ell →
  ell = T.length - A.length →
  B.length + (2 : ℕ) = T.length →
  Bplus.length + (1 : ℕ) = T.length →
  TreeSequenceInitialSegment B T →
  TreeSequenceInitialSegment Bplus T →
  TreeSequenceInitialSegment B Bplus →
  TreeSequenceInitialSegment A T →
  TreeSequenceInitialSegment A Bplus →
  ColoredVertexSetElementary G phi (TreeSequenceVertexSet Bplus) →
  (
  ∀ {X Y : TreeSequence G e0},
  TreeSequenceInitialSegment X Y →
  TreeMissingColors phi X ⊆ TreeMissingColors phi Y) →
  ∀ (vAlpha : V),
  (
  ∀ (X : TreeSequence G e0) (i : Fin (X.length + (1 : ℕ))),
  X.vertex i ∈ TreeSequenceVertexSet X) →
  (
  ∀ (X : TreeSequence G e0),
  ∀ c ∈ TreeMissingColors phi X,
   c ∈
    MissingColors G phi
     (X.vertex (HierarchyFirstMissingPosition phi X c))) →
  T.vertex penIndex ∈ TreeSequenceVertexSet Bplus →
  Bplus = HierarchyFullTailPrefix C (ell - (1 : ℕ)) →
  ColoredVertexSetElementary G phi
    (TreeSequenceVertexSet
     (HierarchyFullTailPrefix C (ell - (1 : ℕ)))) →
  alpha ≠ eta →
  theta ∈ TreeMissingColors phi A →
  eta ∉ TreeMissingColors phi A →
  alpha ∈ TreeMissingColors phi Bplus →
  theta ∈ TreeMissingColors phi Bplus →
  theta ∈
     TreeMissingColors phi
      (HierarchyFullTailPrefix C (ell - (1 : ℕ))) ∧
    alpha ∈
     TreeMissingColors phi
      (HierarchyFullTailPrefix C (ell - (1 : ℕ))) →
  HierarchyFirstMissingPosition phi T eta = penIndex →
  (↑(HierarchyFirstMissingPosition phi T theta) : ℕ) ≤
    A.length →
  (↑(HierarchyFirstMissingPosition phi T alpha) : ℕ) ≤
    B.length →
  vAlpha ∈ TreeSequenceVertexSet Bplus →
  (
  theta ∉ TreeMissingColors phi A ∨
    alpha ∉ TreeMissingColors phi A →
  TreeVertexOrder T
    (T.vertex (HierarchyFirstMissingPosition phi T theta))
    (T.vertex
     (HierarchyFirstMissingPosition phi T alpha)) ∧
   theta ∉
    ({c : Fin k |
      ∃ (t : Fin T.length),
       A.length ≤ (↑t : ℕ) ∧
        (↑t : ℕ) <
          (↑(HierarchyFirstMissingPosition phi T alpha) :
           ℕ) ∧
         phi (T.edge t) = some c} :
     Finset (Fin k))) →
  (
  ∀ (t : Fin T.length),
  A.length ≤ (↑t : ℕ) →
  (↑t : ℕ) < Bplus.length →
  phi (T.edge t) ≠ some theta) →
  theta ≠ alpha →
  (
  H.dividerCount = (0 : ℕ) →
  theta ∈ TreeMissingColors phi Tn) →
  (
  (0 : ℕ) < H.dividerCount →
  theta ∈
   TreeMissingColors phi
    (H.stage
     (⟨H.dividerCount,
       by
       have := TreeSequence.positive T
       omega⟩ :
      Fin (H.dividerCount + (2 : ℕ))))) →
  False

/-- Dependent contract shared by the hierarchy construction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperContinuation3399Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base)
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
   (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
  let alpha : Fin k := D.alpha;
  let theta : Fin k := D.theta;
  let lastIndex : Fin T.length := D.lastEdgeIndex;
  let penIndex : Fin (T.length + (1 : ℕ)) := D.penultimateVertexIndex;
  let endIndex : Fin (T.length + (1 : ℕ)) := D.terminalVertexIndex;
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let ell : ℕ := HierarchyFullTailLength C;
  ∀ (B Bplus : TreeSequence G e0),
  let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
  let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
  phi (T.edge lastIndex) = some theta →
  alpha ∈ MissingColors G phi (T.vertex endIndex) →
  (
  ∀ (t : Fin T.length),
  A.length ≤ (↑t : ℕ) →
  phi (T.edge t) ≠ some alpha) →
  (↑lastIndex : ℕ) + (1 : ℕ) = T.length →
  (↑penIndex : ℕ) + (1 : ℕ) = T.length →
  (↑endIndex : ℕ) = T.length →
  (
  have n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
  have Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
  have Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
  ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
    TashkinovAugmentationSequence phi Tn T ∨
   (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
     ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
    ∃ (f : E) (seed : TreeSequence G e0),
     ett.series.data.connectingEdges n = ({ f } : Finset E) ∧
      TreeSequenceAdjoinEdge Tn f seed ∧
       TreeIncidentEdge Tn f ∧
        (∃ c ∈ TreeMissingColors phi Tn ∪ Dn, phi f = some c) ∧
         TashkinovAugmentationSequence phi seed T) →
  ∀ eta ∈ HierarchyStoredColorsAt H q,
  eta ∈ MissingColors G phi (T.vertex penIndex) →
  theta ∈ C.good.gamma q eta →
  (2 : ℕ) ≤ ell →
  ell = T.length - A.length →
  B.length + (2 : ℕ) = T.length →
  Bplus.length + (1 : ℕ) = T.length →
  TreeSequenceInitialSegment Bplus T →
  TreeSequenceInitialSegment B Bplus →
  TreeSequenceInitialSegment A T →
  TreeSequenceInitialSegment A Bplus →
  ColoredVertexSetElementary G phi (TreeSequenceVertexSet Bplus) →
  ∀ (vAlpha : V),
  (
  ∀ (X : TreeSequence G e0) (i : Fin (X.length + (1 : ℕ))),
  X.vertex i ∈ TreeSequenceVertexSet X) →
  T.vertex penIndex ∈ TreeSequenceVertexSet Bplus →
  Bplus = HierarchyFullTailPrefix C (ell - (1 : ℕ)) →
  ColoredVertexSetElementary G phi
    (TreeSequenceVertexSet (HierarchyFullTailPrefix C (ell - (1 : ℕ)))) →
  alpha ≠ eta →
  theta ∈ TreeMissingColors phi A →
  eta ∉ TreeMissingColors phi A →
  alpha ∈ TreeMissingColors phi Bplus →
  theta ∈ TreeMissingColors phi Bplus →
  theta ∈
     TreeMissingColors phi
      (HierarchyFullTailPrefix C (ell - (1 : ℕ))) ∧
    alpha ∈
     TreeMissingColors phi
      (HierarchyFullTailPrefix C (ell - (1 : ℕ))) →
  HierarchyFirstMissingPosition phi T eta = penIndex →
  (↑(HierarchyFirstMissingPosition phi T theta) : ℕ) ≤ A.length →
  (↑(HierarchyFirstMissingPosition phi T alpha) : ℕ) ≤ B.length →
  vAlpha ∈ TreeSequenceVertexSet Bplus →
  (
  ∀ (t : Fin T.length),
  A.length ≤ (↑t : ℕ) →
  (↑t : ℕ) < Bplus.length →
  phi (T.edge t) ≠ some theta) →
  theta ≠ alpha →
  (
  H.dividerCount = (0 : ℕ) →
  theta ∈ TreeMissingColors phi Tn) →
  (0 : ℕ) < H.dividerCount ∧
     theta ∈
      TreeMissingColors phi
       (H.stage
        (⟨H.dividerCount,
          by
          have := TreeSequence.positive T
          omega⟩ :
         Fin (H.dividerCount + (2 : ℕ)))) ∨
    H.dividerCount = (0 : ℕ) ∧
     (theta ∈ TreeMissingColors phi Tn ∨
      theta ∈ TreeMissingColors phi A ∧
       theta ∉ TashkinovStoredColors ett.series.data n ∧
        alpha ∉ TashkinovStoredColors ett.series.data n) →
  (
  ∀ (rho : PartialEdgeColoring E k) (a b : Fin k) (v : V),
  Sum.inl v ∈ TwoColorComponent G rho a b (Sum.inl v)) →
  (
  ∀ (rho : PartialEdgeColoring E k) (a b : Fin k),
  a ≠ b →
  IsProperEdgeColoring G rho →
  ∀ (v : V),
  a ∈ MissingColors G rho v ∨
    b ∈ MissingColors G rho v →
  ((TwoColorIncidenceGraph G rho a b).neighborSet
    (Sum.inl v)).Subsingleton) →
  (
  ∀ (rho : PartialEdgeColoring E k) (a b : Fin k),
  a ≠ b →
  IsProperEdgeColoring G rho →
  ∀ (u v w : V),
  u ≠ v →
  u ≠ w →
  v ≠ w →
  a ∈ MissingColors G rho u →
  b ∈ MissingColors G rho v →
  a ∈ MissingColors G rho w ∨
    b ∈ MissingColors G rho w →
  TwoColorComponent G rho a b (Sum.inl u) =
    TwoColorComponent G rho a b (Sum.inl v) →
  Disjoint
   (TwoColorComponent G rho a b (Sum.inl w))
   (TwoColorComponent G rho a b
    (Sum.inl u))) →
  theta ∈
    MissingColors G phi
     (T.vertex
      (HierarchyFirstMissingPosition phi T theta)) →
  alpha ∈
    MissingColors G phi
     (T.vertex
      (HierarchyFirstMissingPosition phi T alpha)) →
  T.vertex
     (HierarchyFirstMissingPosition phi T theta) ≠
    T.vertex endIndex →
  Disjoint
    (TwoColorComponent G phi theta alpha
     (Sum.inl (T.vertex endIndex)))
    (TwoColorComponent G phi theta alpha
     (Sum.inl
      (T.vertex
       (HierarchyFirstMissingPosition phi T
        theta)))) →
  let z : V ⊕ E := Sum.inl (T.vertex endIndex);
  TwoColorPathComponent G phi theta alpha z →
  let muOne : PartialEdgeColoring E k :=
   TwoColorComponentSwap G phi theta alpha z;
  ((
  ∀ (v : V),
  Sum.inl v ∉
    TwoColorComponent G phi theta alpha z →
  MissingColors G muOne v =
   MissingColors G phi v) ∧
                                             (
  ∀ (v : V),
  Sum.inl v ∈
    TwoColorComponent G phi theta alpha z →
  theta ∈ MissingColors G phi v →
  alpha ∈ MissingColors G muOne v) ∧
                                              (
  ∀ (v : V),
  Sum.inl v ∈
    TwoColorComponent G phi theta alpha z →
  alpha ∈ MissingColors G phi v →
  theta ∈ MissingColors G muOne v) ∧
  ∀ (v : V) (c : Fin k),
  c ≠ theta →
  c ≠ alpha →
  (c ∈ MissingColors G muOne v ↔
   c ∈ MissingColors G phi v)) →
  (
  ∀ (z : V ⊕ E) (rho : PartialEdgeColoring E k)
   (a b : Fin k),
  a ≠ b →
  IsProperEdgeColoring G rho →
  ColoredVertexSetElementary G rho
    (TreeSequenceVertexSet Bplus) →
  ∀ (u v : V),
  u ∈ TreeSequenceVertexSet Bplus →
  v ∈ TreeSequenceVertexSet Bplus →
  a ∈ MissingColors G rho u →
  b ∈ MissingColors G rho v →
  Sum.inl u ∉
    TwoColorComponent G rho a b z →
  Sum.inl v ∉
    TwoColorComponent G rho a b z →
  ∀ w ∈ TreeSequenceVertexSet Bplus,
   MissingColors G
     (TwoColorComponentSwap G rho a b
      z)
     w =
    MissingColors G rho w) →
  T.vertex
     (HierarchyFirstMissingPosition phi T theta) ∈
    TreeSequenceVertexSet Bplus →
  T.vertex
     (HierarchyFirstMissingPosition phi T
      alpha) ∈
    TreeSequenceVertexSet Bplus →
  (∀ v ∈ TreeSequenceVertexSet Bplus,
    MissingColors G muOne v =
     MissingColors G phi v) →
  (∀ v ∈ TreeSequenceVertexSet Bplus,
    MissingColors G muOne v =
     MissingColors G phi v) →
  False

/-- Dependent contract shared by the hierarchy construction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperContinuation4221Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base)
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
   (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
  let alpha : Fin k := D.alpha;
  let theta : Fin k := D.theta;
  let lastIndex : Fin T.length := D.lastEdgeIndex;
  let penIndex : Fin (T.length + (1 : ℕ)) := D.penultimateVertexIndex;
  let endIndex : Fin (T.length + (1 : ℕ)) := D.terminalVertexIndex;
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let ell : ℕ := HierarchyFullTailLength C;
  ∀ (B Bplus : TreeSequence G e0),
  let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
  let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
  (↑lastIndex : ℕ) + (1 : ℕ) = T.length →
  (↑penIndex : ℕ) + (1 : ℕ) = T.length →
  (↑endIndex : ℕ) = T.length →
  ∀ eta ∈ HierarchyStoredColorsAt H q,
  eta ∈ MissingColors G phi (T.vertex penIndex) →
  (2 : ℕ) ≤ ell →
  ell = T.length - A.length →
  B.length + (2 : ℕ) = T.length →
  Bplus.length + (1 : ℕ) = T.length →
  TreeSequenceInitialSegment Bplus T →
  TreeSequenceInitialSegment B Bplus →
  TreeSequenceInitialSegment A T →
  TreeSequenceInitialSegment A Bplus →
  ColoredVertexSetElementary G phi (TreeSequenceVertexSet Bplus) →
  ∀ (vAlpha : V),
  (
    ∀ (X : TreeSequence G e0) (i : Fin (X.length + (1 : ℕ))),
    X.vertex i ∈ TreeSequenceVertexSet X) →
  T.vertex penIndex ∈ TreeSequenceVertexSet Bplus →
  Bplus = HierarchyFullTailPrefix C (ell - (1 : ℕ)) →
  ColoredVertexSetElementary G phi
    (TreeSequenceVertexSet (HierarchyFullTailPrefix C (ell - (1 : ℕ)))) →
  alpha ≠ eta →
  alpha ∈ TreeMissingColors phi Bplus →
  theta ∈ TreeMissingColors phi Bplus →
  HierarchyFirstMissingPosition phi T eta = penIndex →
  (↑(HierarchyFirstMissingPosition phi T alpha) : ℕ) ≤ B.length →
  vAlpha ∈ TreeSequenceVertexSet Bplus →
  (
    ∀ (t : Fin T.length),
    A.length ≤ (↑t : ℕ) →
    (↑t : ℕ) < Bplus.length →
    phi (T.edge t) ≠ some theta) →
  (
    ∀ (rho : PartialEdgeColoring E k) (a b : Fin k) (v : V),
    Sum.inl v ∈ TwoColorComponent G rho a b (Sum.inl v)) →
  (
    ∀ (rho : PartialEdgeColoring E k) (a b : Fin k),
    a ≠ b →
    IsProperEdgeColoring G rho →
    ∀ (v : V),
    a ∈ MissingColors G rho v ∨ b ∈ MissingColors G rho v →
    ((TwoColorIncidenceGraph G rho a b).neighborSet
      (Sum.inl v)).Subsingleton) →
  (
    ∀ (rho : PartialEdgeColoring E k) (a b : Fin k),
    a ≠ b →
    IsProperEdgeColoring G rho →
    ∀ (u v w : V),
    u ≠ v →
    u ≠ w →
    v ≠ w →
    a ∈ MissingColors G rho u →
    b ∈ MissingColors G rho v →
    a ∈ MissingColors G rho w ∨ b ∈ MissingColors G rho w →
    TwoColorComponent G rho a b (Sum.inl u) =
      TwoColorComponent G rho a b (Sum.inl v) →
    Disjoint (TwoColorComponent G rho a b (Sum.inl w))
     (TwoColorComponent G rho a b (Sum.inl u))) →
  alpha ∈
    MissingColors G phi
     (T.vertex (HierarchyFirstMissingPosition phi T alpha)) →
  T.vertex (HierarchyFirstMissingPosition phi T theta) ≠
    T.vertex endIndex →
  let z : V ⊕ E := Sum.inl (T.vertex endIndex);
  let muOne : PartialEdgeColoring E k :=
   TwoColorComponentSwap G phi theta alpha z;
  (
    ∀ (z : V ⊕ E) (rho : PartialEdgeColoring E k) (a b : Fin k),
    a ≠ b →
    IsProperEdgeColoring G rho →
    ColoredVertexSetElementary G rho
      (TreeSequenceVertexSet Bplus) →
    ∀ (u v : V),
    u ∈ TreeSequenceVertexSet Bplus →
    v ∈ TreeSequenceVertexSet Bplus →
    a ∈ MissingColors G rho u →
    b ∈ MissingColors G rho v →
    Sum.inl u ∉ TwoColorComponent G rho a b z →
    Sum.inl v ∉ TwoColorComponent G rho a b z →
    ∀ w ∈ TreeSequenceVertexSet Bplus,
     MissingColors G (TwoColorComponentSwap G rho a b z)
       w =
      MissingColors G rho w) →
  T.vertex (HierarchyFirstMissingPosition phi T theta) ∈
    TreeSequenceVertexSet Bplus →
  T.vertex (HierarchyFirstMissingPosition phi T alpha) ∈
    TreeSequenceVertexSet Bplus →
  (∀ v ∈ TreeSequenceVertexSet Bplus,
    MissingColors G muOne v = MissingColors G phi v) →
  (∀ v ∈ TreeSequenceVertexSet Bplus,
    MissingColors G muOne v = MissingColors G phi v) →
  TreeMissingColors muOne Bplus =
    TreeMissingColors phi Bplus →
  (
    ∀ (t : Fin T.length),
    A.length ≤ (↑t : ℕ) →
    (↑t : ℕ) < Bplus.length →
    muOne (T.edge t) = phi (T.edge t)) →
  muOne (T.edge lastIndex) = some alpha →
  theta ∈ MissingColors G muOne (T.vertex endIndex) →
  eta ∈ MissingColors G muOne (T.vertex penIndex) →
  (
    H.dividerCount = (0 : ℕ) →
    A = base.core) →
  TreeSequenceInitialSegment Tn Bplus →
  (
    ∀ (aLen : ℕ),
    aLen = A.length →
    (
    ∀ (t : Fin Bplus.length),
    (↑t : ℕ) < aLen ∨ aLen ≤ (↑t : ℕ)) →
    ∀ (t : Fin Bplus.length),
    muOne (Bplus.edge t) = phi (Bplus.edge t)) →
  (
    ∀ (t : Fin Bplus.length),
    muOne (Bplus.edge t) = phi (Bplus.edge t)) →
  Bplus.length = B.length + (1 : ℕ) →
  (
    ∀ (S : TreeSequence G e0),
    TashkinovAugmentationSequence phi S Bplus →
    TashkinovAugmentationSequence muOne S Bplus) →
  (ett.series.data.kind n =
      some TashkinovExtensionKind.PE ∧
     TashkinovAugmentationSequence muOne Tn Bplus ∨
    (ett.series.data.kind n =
       some TashkinovExtensionKind.SE ∨
      ett.series.data.kind n =
       some TashkinovExtensionKind.RE) ∧
     ∃ (f : E) (seed : TreeSequence G e0),
      ett.series.data.connectingEdges n =
        ({ f } : Finset E) ∧
       TreeSequenceAdjoinEdge Tn f seed ∧
        TashkinovAugmentationSequence muOne seed
         Bplus) →
  (
    ∀ (rho : PartialEdgeColoring E k),
    ∀ c ∈ TreeMissingColors rho Bplus,
     c ∈
       MissingColors G rho
        (T.vertex
         (HierarchyFirstMissingPosition rho T
          c)) ∧
      (↑(HierarchyFirstMissingPosition rho T c) :
        ℕ) ≤
       Bplus.length) →
  (
    ∀ (rho sigma : PartialEdgeColoring E k)
     (c : Fin k),
    ColoredVertexSetElementary G rho
      (TreeSequenceVertexSet Bplus) →
    (∀ v ∈ TreeSequenceVertexSet Bplus,
      MissingColors G sigma v =
       MissingColors G rho v) →
    c ∈ TreeMissingColors rho Bplus →
    HierarchyFirstMissingPosition sigma T c =
     HierarchyFirstMissingPosition rho T c) →
  (
    ∀ (rho sigma : PartialEdgeColoring E k)
     (c : Fin k),
    (
    ∀ (v : V),
    c ∈ MissingColors G sigma v ↔
     c ∈ MissingColors G rho v) →
    HierarchyFirstMissingPosition sigma T c =
     HierarchyFirstMissingPosition rho T c) →
  (∀ c ∈ HierarchyStoredColorsAt H q,
    alpha ∈ C.good.gamma q c ∨
      theta ∈ C.good.gamma q c →
    (↑(HierarchyFirstMissingPosition phi T
        c) :
      ℕ) ≤
     Bplus.length) →
  theta ∈ TreeMissingColors muOne Bplus ∧
    alpha ∈ TreeMissingColors muOne Bplus →
  TashkinovAugmentationSequence phi Bplus T →
  ∀
   (corrOne :
    CorrespondingExtendedTashkinovTree G k
     e0 ett muOne T)
   (maxOne :
    MaximumProperty corrOne.replacementETT)
   (baseOne :
    HierarchyBase corrOne.replacementETT
     muOne)
   (COne : HierarchyCounterexample baseOne)
   (sameOne :
    SameGoodHierarchy C.good COne.good)
   (ctxOne :
    HierarchyMinimumCounterexampleContext G
     k e0 corrOne.replacementInput T muOne
     corrOne.replacementETT baseOne COne),
  let POne :
   HierarchyReplacementPresentation G k e0
    input T phi ett base C ctx :=
   helperPOne1741 G k e0 input T phi ett
    base C ctx D corrOne maxOne baseOne
    COne sameOne ctxOne;
  let HOne :
   TashkinovHierarchy
    corrOne.replacementETT baseOne :=
   COne.hierarchy;
  let qOne :
   Fin (HOne.dividerCount + (1 : ℕ)) :=
   Fin.last HOne.dividerCount;
  HierarchyStarredStage HOne qOne = A →
  H.dividerCount = HOne.dividerCount →
  HierarchyFullTailPrefix COne
     (HierarchyFullTailLength COne -
      (1 : ℕ)) =
    Bplus →
  ColoredVertexSetElementary G muOne
    (TreeSequenceVertexSet Bplus) →
  (
    ∀ (X : TreeSequence G e0),
    TreeSequenceInitialSegment X
      Bplus →
    TreeMissingColors muOne X =
     TreeMissingColors phi X) →
  HierarchyFirstMissingPosition muOne
     T theta =
    HierarchyFirstMissingPosition phi
     T theta →
  HierarchyFirstMissingPosition muOne
     T eta =
    penIndex →
  theta ∈
    MissingColors G muOne
     (T.vertex
      (HierarchyFirstMissingPosition
       phi T theta)) →
  theta ≠ eta →
  (
    ∀ (t : Fin T.length),
    A.length ≤ (↑t : ℕ) →
    muOne (T.edge t) ≠
     some theta) →
  theta ∉
    HierarchyStoredColorsAt HOne
     qOne →
  corrOne.replacementETT.series.data.tree
     (Fin.last
       corrOne.replacementETT.rounds).castSucc =
    Tn →
  (0 : ℕ) < HOne.dividerCount ∧
     theta ∈
      TreeMissingColors muOne
       (HOne.stage
        (⟨HOne.dividerCount,
          by
          have :=
           CorrespondingExtendedTashkinovTree.rungAgreement
            corrOne
          have :=
           TreeSequence.positive
            T
          omega⟩ :
         Fin
          (HOne.dividerCount +
           (2 : ℕ)))) ∨
    HOne.dividerCount =
      (0 : ℕ) ∧
     (theta ∈
       TreeMissingColors muOne
        (corrOne.replacementETT.series.data.tree
         (Fin.last
           corrOne.replacementETT.rounds).castSucc) ∨
      theta ∈
        TreeMissingColors muOne
         (HierarchyStarredStage
          HOne qOne) ∧
       theta ∉
         TashkinovStoredColors
          corrOne.replacementETT.series.data
          (Fin.last
           corrOne.replacementETT.rounds) ∧
        eta ∉
         TashkinovStoredColors
          corrOne.replacementETT.series.data
          (Fin.last
           corrOne.replacementETT.rounds)) →
  eta ∈
    TreeMissingColors muOne
     Bplus →
  theta ∈
    TreeMissingColors muOne
     Bplus →
  TwoColorComponent G muOne
     theta eta
     (Sum.inl
      (T.vertex
       (HierarchyFirstMissingPosition
        phi T theta))) =
    TwoColorComponent G
     muOne theta eta
     (Sum.inl
      (T.vertex penIndex)) →
  T.vertex
     (HierarchyFirstMissingPosition
      phi T theta) ≠
    T.vertex penIndex →
  False

/-- Dependent contract shared by the hierarchy construction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperContinuation3757Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base)
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
   (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
  let alpha : Fin k := D.alpha;
  let theta : Fin k := D.theta;
  let lastIndex : Fin T.length := D.lastEdgeIndex;
  let penIndex : Fin (T.length + (1 : ℕ)) := D.penultimateVertexIndex;
  let endIndex : Fin (T.length + (1 : ℕ)) := D.terminalVertexIndex;
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let ell : ℕ := HierarchyFullTailLength C;
  ∀ (B Bplus : TreeSequence G e0),
  let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
  let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
  (↑lastIndex : ℕ) + (1 : ℕ) = T.length →
  (↑penIndex : ℕ) + (1 : ℕ) = T.length →
  (↑endIndex : ℕ) = T.length →
  ∀ eta ∈ HierarchyStoredColorsAt H q,
  eta ∈ MissingColors G phi (T.vertex penIndex) →
  theta ∈ C.good.gamma q eta →
  (2 : ℕ) ≤ ell →
  ell = T.length - A.length →
  B.length + (2 : ℕ) = T.length →
  Bplus.length + (1 : ℕ) = T.length →
  TreeSequenceInitialSegment Bplus T →
  TreeSequenceInitialSegment B Bplus →
  TreeSequenceInitialSegment A T →
  TreeSequenceInitialSegment A Bplus →
  ColoredVertexSetElementary G phi (TreeSequenceVertexSet Bplus) →
  ∀ (vAlpha : V),
  (
    ∀ (X : TreeSequence G e0) (i : Fin (X.length + (1 : ℕ))),
    X.vertex i ∈ TreeSequenceVertexSet X) →
  T.vertex penIndex ∈ TreeSequenceVertexSet Bplus →
  Bplus = HierarchyFullTailPrefix C (ell - (1 : ℕ)) →
  ColoredVertexSetElementary G phi
    (TreeSequenceVertexSet (HierarchyFullTailPrefix C (ell - (1 : ℕ)))) →
  alpha ≠ eta →
  theta ∈ TreeMissingColors phi A →
  eta ∉ TreeMissingColors phi A →
  alpha ∈ TreeMissingColors phi Bplus →
  theta ∈ TreeMissingColors phi Bplus →
  HierarchyFirstMissingPosition phi T eta = penIndex →
  (↑(HierarchyFirstMissingPosition phi T theta) : ℕ) ≤ A.length →
  (↑(HierarchyFirstMissingPosition phi T alpha) : ℕ) ≤ B.length →
  vAlpha ∈ TreeSequenceVertexSet Bplus →
  (
    ∀ (t : Fin T.length),
    A.length ≤ (↑t : ℕ) →
    (↑t : ℕ) < Bplus.length →
    phi (T.edge t) ≠ some theta) →
  theta ≠ alpha →
  (
    H.dividerCount = (0 : ℕ) →
    theta ∈ TreeMissingColors phi Tn) →
  (
    ∀ (rho : PartialEdgeColoring E k) (a b : Fin k) (v : V),
    Sum.inl v ∈ TwoColorComponent G rho a b (Sum.inl v)) →
  (
    ∀ (rho : PartialEdgeColoring E k) (a b : Fin k),
    a ≠ b →
    IsProperEdgeColoring G rho →
    ∀ (v : V),
    a ∈ MissingColors G rho v ∨ b ∈ MissingColors G rho v →
    ((TwoColorIncidenceGraph G rho a b).neighborSet
      (Sum.inl v)).Subsingleton) →
  (
    ∀ (rho : PartialEdgeColoring E k) (a b : Fin k),
    a ≠ b →
    IsProperEdgeColoring G rho →
    ∀ (u v w : V),
    u ≠ v →
    u ≠ w →
    v ≠ w →
    a ∈ MissingColors G rho u →
    b ∈ MissingColors G rho v →
    a ∈ MissingColors G rho w ∨
      b ∈ MissingColors G rho w →
    TwoColorComponent G rho a b (Sum.inl u) =
      TwoColorComponent G rho a b (Sum.inl v) →
    Disjoint (TwoColorComponent G rho a b (Sum.inl w))
     (TwoColorComponent G rho a b (Sum.inl u))) →
  theta ∈
    MissingColors G phi
     (T.vertex (HierarchyFirstMissingPosition phi T theta)) →
  alpha ∈
    MissingColors G phi
     (T.vertex (HierarchyFirstMissingPosition phi T alpha)) →
  T.vertex (HierarchyFirstMissingPosition phi T theta) ≠
    T.vertex endIndex →
  let z : V ⊕ E := Sum.inl (T.vertex endIndex);
  let muOne : PartialEdgeColoring E k :=
   TwoColorComponentSwap G phi theta alpha z;
  (
    ∀ (z : V ⊕ E) (rho : PartialEdgeColoring E k)
     (a b : Fin k),
    a ≠ b →
    IsProperEdgeColoring G rho →
    ColoredVertexSetElementary G rho
      (TreeSequenceVertexSet Bplus) →
    ∀ (u v : V),
    u ∈ TreeSequenceVertexSet Bplus →
    v ∈ TreeSequenceVertexSet Bplus →
    a ∈ MissingColors G rho u →
    b ∈ MissingColors G rho v →
    Sum.inl u ∉ TwoColorComponent G rho a b z →
    Sum.inl v ∉ TwoColorComponent G rho a b z →
    ∀ w ∈ TreeSequenceVertexSet Bplus,
     MissingColors G
       (TwoColorComponentSwap G rho a b z) w =
      MissingColors G rho w) →
  T.vertex (HierarchyFirstMissingPosition phi T theta) ∈
    TreeSequenceVertexSet Bplus →
  T.vertex (HierarchyFirstMissingPosition phi T alpha) ∈
    TreeSequenceVertexSet Bplus →
  (∀ v ∈ TreeSequenceVertexSet Bplus,
    MissingColors G muOne v = MissingColors G phi v) →
  (∀ v ∈ TreeSequenceVertexSet Bplus,
    MissingColors G muOne v = MissingColors G phi v) →
  TreeMissingColors muOne Bplus =
    TreeMissingColors phi Bplus →
  (
    ∀ (t : Fin T.length),
    A.length ≤ (↑t : ℕ) →
    (↑t : ℕ) < Bplus.length →
    muOne (T.edge t) = phi (T.edge t)) →
  muOne (T.edge lastIndex) = some alpha →
  theta ∈
    MissingColors G muOne (T.vertex endIndex) →
  eta ∈ MissingColors G muOne (T.vertex penIndex) →
  (
    ∀ (a d : ℕ)
     (hb : a + d ≤ H.dividerCount + (1 : ℕ)),
    TreeSequenceInitialSegment
     (H.stage
      (⟨a, by
        have := TreeSequence.positive T
        omega⟩ :
       Fin (H.dividerCount + (2 : ℕ))))
     (H.stage
      (⟨a + d,
        by
        have := TreeSequence.positive T
        omega⟩ :
       Fin (H.dividerCount + (2 : ℕ))))) →
  (
    H.dividerCount = (0 : ℕ) →
    A = base.core) →
  TreeSequenceInitialSegment Tn Bplus →
  (
    ∀ (aLen : ℕ),
    aLen = A.length →
    (
    ∀ (t : Fin Bplus.length),
    (↑t : ℕ) < aLen ∨ aLen ≤ (↑t : ℕ)) →
    ∀ (t : Fin Bplus.length),
    muOne (Bplus.edge t) =
     phi (Bplus.edge t)) →
  (
    ∀ (t : Fin Bplus.length),
    muOne (Bplus.edge t) =
     phi (Bplus.edge t)) →
  Bplus.length = B.length + (1 : ℕ) →
  (
    ∀ (S : TreeSequence G e0),
    TashkinovAugmentationSequence phi S
      Bplus →
    TashkinovAugmentationSequence muOne S
     Bplus) →
  (ett.series.data.kind n =
      some TashkinovExtensionKind.PE ∧
     TashkinovAugmentationSequence muOne Tn
      Bplus ∨
    (ett.series.data.kind n =
       some TashkinovExtensionKind.SE ∨
      ett.series.data.kind n =
       some TashkinovExtensionKind.RE) ∧
     ∃ (f : E) (seed : TreeSequence G e0),
      ett.series.data.connectingEdges n =
        ({ f } : Finset E) ∧
       TreeSequenceAdjoinEdge Tn f seed ∧
        TashkinovAugmentationSequence muOne
         seed Bplus) →
  (
    ∀ (rho : PartialEdgeColoring E k),
    ∀ c ∈ TreeMissingColors rho Bplus,
     c ∈
       MissingColors G rho
        (T.vertex
         (HierarchyFirstMissingPosition
          rho T c)) ∧
      (↑(HierarchyFirstMissingPosition rho
          T c) :
        ℕ) ≤
       Bplus.length) →
  (
    ∀
     (rho sigma : PartialEdgeColoring E k)
     (c : Fin k),
    ColoredVertexSetElementary G rho
      (TreeSequenceVertexSet Bplus) →
    (∀ v ∈ TreeSequenceVertexSet Bplus,
      MissingColors G sigma v =
       MissingColors G rho v) →
    c ∈ TreeMissingColors rho Bplus →
    HierarchyFirstMissingPosition
      sigma T c =
     HierarchyFirstMissingPosition rho
      T c) →
  (
    ∀
     (rho sigma :
      PartialEdgeColoring E k)
     (c : Fin k),
    (
    ∀ (v : V),
    c ∈ MissingColors G sigma v ↔
     c ∈ MissingColors G rho v) →
    HierarchyFirstMissingPosition sigma
      T c =
     HierarchyFirstMissingPosition rho
      T c) →
  (∀ c ∈ HierarchyStoredColorsAt H q,
    alpha ∈ C.good.gamma q c ∨
      theta ∈ C.good.gamma q c →
    (↑(HierarchyFirstMissingPosition
        phi T c) :
      ℕ) ≤
     Bplus.length) →
  theta ∈
     TreeMissingColors muOne Bplus ∧
    alpha ∈
     TreeMissingColors muOne Bplus →
  TashkinovAugmentationSequence phi
    Bplus T →
  ∀
   (corrOne :
    CorrespondingExtendedTashkinovTree
     G k e0 ett muOne T),
  MaximumProperty
    corrOne.replacementETT →
  ∀
   (baseOne :
    HierarchyBase
     corrOne.replacementETT muOne)
   (KOne :
    TashkinovHierarchy
     corrOne.replacementETT
     baseOne)
   (goodOne : GoodHierarchy KOne),
  SameGoodHierarchy C.good
    goodOne →
  False

/-- Dependent contract shared by the hierarchy construction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperContinuation6530Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
   (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
   (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base)
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
   (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
  let alpha : Fin k := D.alpha;
  let theta : Fin k := D.theta;
  let lastIndex : Fin T.length := D.lastEdgeIndex;
  let penIndex : Fin (T.length + (1 : ℕ)) := D.penultimateVertexIndex;
  let endIndex : Fin (T.length + (1 : ℕ)) := D.terminalVertexIndex;
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let ell : ℕ := HierarchyFullTailLength C;
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
  let Bplus : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
  let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
  let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
  ∀ (lastColor : phi (T.edge lastIndex) = some theta)
   (_ : alpha ∈ MissingColors G phi (T.vertex endIndex)) (_ : alpha ∈ TreeMissingColors phi B)
   (lastPosition : (↑lastIndex : ℕ) + (1 : ℕ) = T.length)
   (penPosition : (↑penIndex : ℕ) + (1 : ℕ) = T.length) (endPosition : (↑endIndex : ℕ) = T.length)
   (thetaPresent : theta ∉ MissingColors G phi (T.vertex penIndex)),
  let tail : HierarchySituationTwoTailData G k e0 input T phi ett base C ctx :=
   {
    tailAtLeastTwo := D.tailAtLeastTwo, pathNumberFull := D.pathNumberFull,
    lastEdgeIndex := lastIndex, penultimateVertexIndex := penIndex,
    terminalVertexIndex := endIndex, lastEdgePosition := lastPosition,
    penultimateVertexPosition := penPosition, terminalVertexPosition := endPosition,
    lastEdgeNotIncidentPenultimate := D.lastEdgeNotIncidentPenultimate, theta := theta,
    thetaOnLastEdge := lastColor, thetaPresentPenultimate := thetaPresent :
    HierarchySituationTwoTailData G k e0 input T phi ett base C ctx };
  ∀ (R : HierarchySituationTwoReorderedTrees G k e0 input T phi ett base C ctx tail)
   (corrMinus : CorrespondingExtendedTashkinovTree G k e0 ett phi R.minus)
   (_ : MaximumProperty corrMinus.replacementETT)
   (baseMinus : HierarchyBase corrMinus.replacementETT phi) (_ : baseMinus.core = base.core)
   (_ : baseMinus.closure = base.closure)
   (HMinus : TashkinovHierarchy corrMinus.replacementETT baseMinus)
   (hcountMinus : HMinus.dividerCount = C.hierarchy.dividerCount)
   (_ :
  ∀ (j : Fin (HMinus.dividerCount + (1 : ℕ))),
  HMinus.stage j.castSucc =
   C.hierarchy.stage (Fin.cast (congrArg (fun (d : ℕ) ↦ d + (1 : ℕ)) hcountMinus) j).castSucc)
   (_ :
  ∀ (j : Fin HMinus.dividerCount),
  (↑(HMinus.dividerPosition j) : ℕ) =
   (↑(C.hierarchy.dividerPosition (Fin.cast hcountMinus j)) : ℕ))
   (corrStar : CorrespondingExtendedTashkinovTree G k e0 ett phi R.star)
   (baseStar : HierarchyBase corrStar.replacementETT phi)
   (HStar : TashkinovHierarchy corrStar.replacementETT baseStar)
   (_ : HStar.dividerCount = C.hierarchy.dividerCount)
   (_ :
  ∀ {X Y Z : TreeSequence G e0} (_ : TreeSequenceInitialSegment X Y)
   (_ : TreeSequenceInitialSegment Y Z),
  TreeSequenceInitialSegment X Z)
   (_ :
  ∀ (j : Fin (H.dividerCount + (1 : ℕ))) (_ : (↑j : ℕ) ≠ (0 : ℕ)),
  HierarchyStarredStage H j = H.stage j.castSucc)
   (_ : B.length + (2 : ℕ) = T.length) (_ : Bplus.length + (1 : ℕ) = T.length)
   (_ : TreeSequenceInitialSegment B T) (_ : TreeSequenceInitialSegment A B)
   (_ :
    TreeSequenceInitialSegment (HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ)))
     R.minus)
   (_ :
    R.minus.length =
     (HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ))).length + (1 : ℕ))
   (_ : R.minus.length = B.length + (1 : ℕ)) (_ : R.minus.length + (1 : ℕ) = T.length)
   (_ :
  ∀ (X : TreeSequence G e0) (i : Fin (X.length + (1 : ℕ))),
  X.vertex i ∈ TreeSequenceVertexSet X)
   (_ :
  ∀ (X : TreeSequence G e0) (c : Fin k) (i : Fin (X.length + (1 : ℕ)))
   (_ : c ∈ MissingColors G phi (X.vertex i)),
  (↑(HierarchyFirstMissingPosition phi X c) : ℕ) ≤ (↑i : ℕ))
   (_ :
  ∀ (X : TreeSequence G e0) (c : Fin k) (i : Fin (X.length + (1 : ℕ)))
   (_ : (↑i : ℕ) < (↑(HierarchyFirstMissingPosition phi X c) : ℕ)),
  c ∉ MissingColors G phi (X.vertex i))
   (_ :
  ∀ (X : TreeSequence G e0) (c : Fin k) (t : ℕ) (_ : t ≤ X.length)
       (_ :
  ∀ (i : Fin (X.length + (1 : ℕ))),
  (↑i : ℕ) < t →
  c ∉ MissingColors G phi (X.vertex i)),
  t ≤ (↑(HierarchyFirstMissingPosition phi X c) : ℕ))
   (_ :
  ∀ (eta c : Fin k) (_ : eta ∈ HierarchyStoredColorsAt H q) (_ : c ∈ C.good.gamma q eta),
  c ∉
   ({c : Fin k |
     ∃ (r : Fin T.length),
      A.length ≤ (↑r : ℕ) ∧
       (↑r : ℕ) < min (↑(HierarchyFirstMissingPosition phi T eta) : ℕ) T.length ∧
        phi (T.edge r) = some c} :
    Finset (Fin k)))
   (_ :
  ∀ (eta : Fin k) (_ : eta ∈ HierarchyStoredColorsAt H q) (_ : theta ∈ C.good.gamma q eta),
  (↑(HierarchyFirstMissingPosition phi T eta) : ℕ) ≤ B.length)
   (_ :
    corrMinus.replacementETT.series.data.tree
       (Fin.last corrMinus.replacementETT.rounds).castSucc =
      Tn ∧
     corrMinus.replacementETT.series.data.kind (Fin.last corrMinus.replacementETT.rounds) =
       ett.series.data.kind n ∧
      TashkinovStoredColors corrMinus.replacementETT.series.data
        (Fin.last corrMinus.replacementETT.rounds) =
       TashkinovStoredColors ett.series.data n)
   (_ :
  ∀ (j : Fin (HMinus.dividerCount + (1 : ℕ))),
  let jo : Fin (C.hierarchy.dividerCount + (1 : ℕ)) :=
   Fin.cast (congrArg (fun (d : ℕ) ↦ d + (1 : ℕ)) hcountMinus) j;
  HierarchyStarredStage HMinus j = HierarchyStarredStage H jo ∧
   HierarchyStoredColorsAt HMinus j = HierarchyStoredColorsAt H jo ∧
    HierarchyStageMissingColors HMinus j = HierarchyStageMissingColors H jo)
   (_ :
  ∀ (j : Fin (HMinus.dividerCount + (1 : ℕ))),
  HMinus.stage j.castSucc =
   H.stage (Fin.cast (congrArg (fun (d : ℕ) ↦ d + (1 : ℕ)) hcountMinus) j).castSucc),
  False

theorem helper_transSegment_333.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
  {X Y Z : TreeSequence G e0},
  TreeSequenceInitialSegment X Y →
  TreeSequenceInitialSegment Y Z →
  TreeSequenceInitialSegment X Z := by
  classical
  intro V E G e0 X Y Z hXY hYZ
  as_aux_lemma =>
    refine ⟨le_trans hXY.1 hYZ.1, ?_, ?_⟩
    · intro i
      exact (hYZ.2.1 (Fin.castLE (Nat.succ_le_succ hXY.1) i)).trans (hXY.2.1 i)
    · intro i
      exact (hYZ.2.2 (Fin.castLE hXY.1 i)).trans (hXY.2.2 i)

theorem helper_restrictSegment_343.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
  {X Y Z : TreeSequence G e0},
  TreeSequenceInitialSegment X Z →
  TreeSequenceInitialSegment Y Z →
  X.length ≤ Y.length →
  TreeSequenceInitialSegment X Y := by
  classical
  intro V E G e0 X Y Z hXZ hYZ hXY
  as_aux_lemma =>
    refine ⟨hXY, ?_, ?_⟩
    · intro i
      exact (hYZ.2.1 (Fin.castLE (Nat.succ_le_succ hXY) i)).symm.trans (hXZ.2.1 i)
    · intro i
      exact (hYZ.2.2 (Fin.castLE hXY i)).symm.trans (hXZ.2.2 i)

theorem helper_hAT_359.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  (
  ∀ (j : Fin (H.dividerCount + (1 : ℕ))),
  (↑j : ℕ) ≠ (0 : ℕ) →
  HierarchyStarredStage H j = H.stage j.castSucc) →
  TreeSequenceInitialSegment A T := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q A starredAt
  by_cases hz : H.dividerCount = 0
  · have hq : q = 0 := Fin.ext (by simp [q, hz])
    have hs : (⟨1, Nat.lt_succ_of_le (Nat.succ_le_succ (Nat.zero_le _))⟩ : Fin
        (H.dividerCount + 2)) =
        Fin.last (H.dividerCount + 1) := Fin.ext (by simp [hz])
    simpa [A, hq, HierarchyStarredStage, hs, H.terminalStage] using H.coreInsideFirst
  · have ha : A = H.stage q.castSucc := starredAt q (by simpa [q] using hz)
    rw [ha]
    have hs : H.stage q.succ = T := by convert H.terminalStage using 1; congr 1
    simpa only [hs] using H.nested q

theorem helper_firstLe_400.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E)
  (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (X : TreeSequence G e0) (c : Fin k)
  (i : Fin (X.length + (1 : ℕ))),
  c ∈ MissingColors G phi (X.vertex i) →
  (↑(HierarchyFirstMissingPosition phi X c) : ℕ) ≤ (↑i : ℕ) := by
  classical
  intro V E _ _ G k e0 phi X c i hi
  let _ := Fintype.ofFinite V
  as_aux_lemma =>
    unfold HierarchyFirstMissingPosition
    dsimp only
    have hm : i ∈ Finset.univ.filter
        (fun j => c ∈ MissingColors G phi (X.vertex j)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
    rw [dite_eq_left ⟨i, hm⟩]
    exact Finset.min'_le _ _ hm

theorem helper_firstMissing_411.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E)
  (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (X : TreeSequence G e0),
  ∀ c ∈ TreeMissingColors phi X,
  c ∈ MissingColors G phi (X.vertex (HierarchyFirstMissingPosition phi X c)) := by
  classical
  intro V E _ _ G k e0 phi X c hc
  let _ := Fintype.ofFinite V
  as_aux_lemma =>
    obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hc
    obtain ⟨i, _, rfl⟩ := (@Finset.mem_image _ _ (Classical.decEq V)).mp hv
    unfold HierarchyFirstMissingPosition
    dsimp only
    have hm : i ∈ Finset.univ.filter
        (fun j => c ∈ MissingColors G phi (X.vertex j)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcv⟩
    rw [dite_eq_left ⟨i, hm⟩]
    exact (Finset.mem_filter.mp (Finset.min'_mem _ ⟨i, hm⟩)).2

theorem helper_oldAvoid_453.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  ∀ (eta c : Fin k),
  eta ∈ HierarchyStoredColorsAt H q →
  c ∈ C.good.gamma q eta →
  c ∉
    ({c : Fin k |
        ∃ (r : Fin T.length),
          A.length ≤ (↑r : ℕ) ∧
            (↑r : ℕ) < min (↑(HierarchyFirstMissingPosition phi T eta) : ℕ) T.length ∧
              phi (T.edge r) = some c} :
      Finset (Fin k)) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q A eta c hs hc
  as_aux_lemma =>
    have hh := (Finset.mem_sdiff.mp (C.good.avoidance q eta hs hc)).2
    change c ∉ HierarchySegmentColors H q eta at hh
    unfold HierarchySegmentColors at hh
    dsimp only at hh
    have hend : H.stage q.succ = T := by convert H.terminalStage using 1; congr 1
    rw [hend] at hh
    exact hh

theorem helper_thetaCutoff_466.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
  let theta : Fin k := D.theta;
  let lastIndex : Fin T.length := D.lastEdgeIndex;
  let penIndex : Fin (T.length + (1 : ℕ)) := D.penultimateVertexIndex;
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let ell : ℕ := HierarchyFullTailLength C;
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
  phi (T.edge lastIndex) = some theta →
  (↑lastIndex : ℕ) + (1 : ℕ) = T.length →
  (↑penIndex : ℕ) + (1 : ℕ) = T.length →
  (∀ eta ∈ HierarchyStoredColorsAt H q,
  eta ∈ MissingColors G phi (T.vertex penIndex) →
  theta ∉ C.good.gamma q eta) →
  (2 : ℕ) ≤ ell →
  ell = T.length - A.length →
  B.length + (2 : ℕ) = T.length →
  (
  ∀ (X : TreeSequence G e0) (i : Fin (X.length + (1 : ℕ))),
  X.vertex i ∈ TreeSequenceVertexSet X) →
  (
  ∀ (X : TreeSequence G e0),
  ∀ c ∈ TreeMissingColors phi X,
    c ∈ MissingColors G phi (X.vertex (HierarchyFirstMissingPosition phi X c))) →
  (
  ∀ (eta c : Fin k),
  eta ∈ HierarchyStoredColorsAt H q →
  c ∈ C.good.gamma q eta →
  c ∉
    ({c : Fin k |
        ∃ (r : Fin T.length),
          A.length ≤ (↑r : ℕ) ∧
            (↑r : ℕ) <
                min (↑(HierarchyFirstMissingPosition phi T eta) : ℕ) T.length ∧
              phi (T.edge r) = some c} :
      Finset (Fin k))) →
  ∀ eta ∈ HierarchyStoredColorsAt H q,
  theta ∈ C.good.gamma q eta →
  (↑(HierarchyFirstMissingPosition phi T eta) : ℕ) ≤ B.length := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D theta lastIndex penIndex H q A ell B
      lastColor lastPosition penPosition hnone' htail hell hBL vertexMem firstMissing oldAvoid
      eta hs hc
  as_aux_lemma =>
    have hlast : lastIndex.val = B.length + 1 := by
      have := lastPosition
      omega
    have hpen : penIndex.val = B.length + 1 := by
      have := penPosition
      omega
    by_contra hcut
    have hgt : B.length < (HierarchyFirstMissingPosition phi T eta).val := by omega
    by_cases hafter : B.length + 1 < (HierarchyFirstMissingPosition phi T eta).val
    · apply oldAvoid eta theta hs hc
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lastIndex,
        by have := lastPosition; omega,
        by have := lastIndex.isLt; omega, lastColor⟩
    · have heq : HierarchyFirstMissingPosition phi T eta = penIndex := by
        apply Fin.ext
        have hpos := penPosition
        omega
      have hm := firstMissing T eta (by
        by_contra h
        have he : HierarchyFirstMissingPosition phi T eta = Fin.last T.length := by
          unfold HierarchyFirstMissingPosition
          dsimp only
          rw [dite_eq_right]
          intro hne
          obtain ⟨i, hi⟩ := hne
          exact h (Finset.mem_biUnion.mpr ⟨T.vertex i, vertexMem T i,
            (Finset.mem_filter.mp hi).2⟩)
        have hv := congrArg Fin.val he
        simp only [Fin.val_last] at hv
        omega)
      rw [heq] at hm
      exact hnone' eta hs hm hc

theorem helper_hBBplusOuter_953.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
  let penIndex : Fin (T.length + (1 : ℕ)) := D.penultimateVertexIndex;
  let endIndex : Fin (T.length + (1 : ℕ)) := D.terminalVertexIndex;
  let ell : ℕ := HierarchyFullTailLength C;
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
  let Bplus : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
  (↑penIndex : ℕ) + (1 : ℕ) = T.length →
  (↑endIndex : ℕ) = T.length →
  B.length + (2 : ℕ) = T.length →
  Bplus.length + (1 : ℕ) = T.length →
  TreeSequenceInitialSegment B Bplus := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D penIndex endIndex ell B Bplus penPosition
      endPosition hBLouter hPLouter
  refine ⟨by omega, ?_, ?_⟩
  · intro i
    rfl
  · intro i
    rfl

theorem helper_hATouter_959.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (_ : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  TreeSequenceInitialSegment A T := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A
  by_cases hz : H.dividerCount = 0
  · have hq : q = 0 := Fin.ext (by simp [q, hz])
    have hs : (⟨1, Nat.lt_succ_of_le (Nat.succ_le_succ (Nat.zero_le _))⟩ : Fin (H.dividerCount
        + 2)) =
        Fin.last (H.dividerCount + 1) := Fin.ext (by simp [hz])
    simpa [A, hq, HierarchyStarredStage, hs, H.terminalStage] using H.coreInsideFirst
  · have hq : q ≠ 0 := by
      intro he
      have hv := congrArg Fin.val he
      simp [q] at hv
      omega
    have ha : A = H.stage q.castSucc := by
      dsimp [A]
      rw [← Fin.succ_pred q hq]
      rfl
    rw [ha]
    have hs : H.stage q.succ = T := by
      convert H.terminalStage using 1
      congr 1
    simpa only [hs] using H.nested q

theorem helper_hABouter_980.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
  let penIndex : Fin (T.length + (1 : ℕ)) := D.penultimateVertexIndex;
  let endIndex : Fin (T.length + (1 : ℕ)) := D.terminalVertexIndex;
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let ell : ℕ := HierarchyFullTailLength C;
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
  let Bplus : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
  (↑penIndex : ℕ) + (1 : ℕ) = T.length →
  (↑endIndex : ℕ) = T.length →
  (2 : ℕ) ≤ ell →
  ell = T.length - A.length →
  B.length + (2 : ℕ) = T.length →
  Bplus.length + (1 : ℕ) = T.length →
  TreeSequenceInitialSegment A T →
  TreeSequenceInitialSegment A B := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D penIndex endIndex H q A ell B Bplus
      penPosition endPosition hTailAtLeast hellOuter hBLouter hPLouter hATouter
  refine ⟨by omega, ?_, ?_⟩
  · intro i
    exact hATouter.2.1 i
  · intro i
    exact hATouter.2.2 i

theorem helper_hABplusouter_986.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
  let penIndex : Fin (T.length + (1 : ℕ)) := D.penultimateVertexIndex;
  let endIndex : Fin (T.length + (1 : ℕ)) := D.terminalVertexIndex;
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let ell : ℕ := HierarchyFullTailLength C;
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
  let Bplus : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
  (↑penIndex : ℕ) + (1 : ℕ) = T.length →
  (↑endIndex : ℕ) = T.length →
  (2 : ℕ) ≤ ell →
  ell = T.length - A.length →
  B.length + (2 : ℕ) = T.length →
  Bplus.length + (1 : ℕ) = T.length →
  TreeSequenceInitialSegment A T →
  TreeSequenceInitialSegment A Bplus := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D penIndex endIndex H q A ell B Bplus
      penPosition endPosition hTailAtLeast hellOuter hBLouter hPLouter hATouter
  refine ⟨by omega, ?_, ?_⟩
  · intro i
    exact hATouter.2.1 i
  · intro i
    exact hATouter.2.2 i

theorem helper_firstMissingOuter_1008.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E)
  (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (X : TreeSequence G e0),
  ∀ c ∈ TreeMissingColors phi X,
  c ∈ MissingColors G phi (X.vertex (HierarchyFirstMissingPosition phi X c)) := by
  classical
  intro V E _ _ G k e0 phi X c hc
  let _ := Fintype.ofFinite V
  as_aux_lemma =>
    obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hc
    obtain ⟨i, _, rfl⟩ := (@Finset.mem_image _ _ (Classical.decEq V)).mp hv
    unfold HierarchyFirstMissingPosition
    dsimp only
    have hm : i ∈ Finset.univ.filter
        (fun j => c ∈ MissingColors G phi (X.vertex j)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcv⟩
    rw [dite_eq_left ⟨i, hm⟩]
    exact (Finset.mem_filter.mp (Finset.min'_mem _ ⟨i, hm⟩)).2

theorem helper_firstLeOuter_1021.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E)
  (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (X : TreeSequence G e0) (c : Fin k)
  (i : Fin (X.length + (1 : ℕ))),
  c ∈ MissingColors G phi (X.vertex i) →
  (↑(HierarchyFirstMissingPosition phi X c) : ℕ) ≤ (↑i : ℕ) := by
  classical
  intro V E _ _ G k e0 phi X c i hi
  let _ := Fintype.ofFinite V
  as_aux_lemma =>
    unfold HierarchyFirstMissingPosition
    dsimp only
    have hm : i ∈ Finset.univ.filter
        (fun j => c ∈ MissingColors G phi (X.vertex j)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
    rw [dite_eq_left ⟨i, hm⟩]
    exact Finset.min'_le _ _ hm

theorem helper_firstBoundByPrefix_1032.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (_ : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
  (
  ∀ (X : TreeSequence G e0) (c : Fin k) (i : Fin (X.length + (1 : ℕ))),
  c ∈ MissingColors G phi (X.vertex i) →
  (↑(HierarchyFirstMissingPosition phi X c) : ℕ) ≤ (↑i : ℕ)) →
  ∀ (X : TreeSequence G e0),
  TreeSequenceInitialSegment X T →
  ∀ c ∈ TreeMissingColors phi X,
  (↑(HierarchyFirstMissingPosition phi T c) : ℕ) ≤ X.length := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D firstLeOuter X hXT c hc
  as_aux_lemma =>
    obtain ⟨v, hv, hvc⟩ := Finset.mem_biUnion.mp hc
    obtain ⟨i, _, rfl⟩ := (@Finset.mem_image _ _ (Classical.decEq V)).mp hv
    let j : Fin (T.length + 1) := Fin.castLE (Nat.succ_le_succ hXT.1) i
    have hj : c ∈ MissingColors G phi (T.vertex j) := by
      rw [hXT.2.1 i]
      exact hvc
    have hfirst := firstLeOuter T c j hj
    change (HierarchyFirstMissingPosition phi T c).val ≤ j.val at hfirst
    dsimp [j] at hfirst
    have hi := i.isLt
    omega

theorem helper_hPenultimateInBplus_1048.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
  let penIndex : Fin (T.length + (1 : ℕ)) := D.penultimateVertexIndex;
  let endIndex : Fin (T.length + (1 : ℕ)) := D.terminalVertexIndex;
  let ell : ℕ := HierarchyFullTailLength C;
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
  let Bplus : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
  (↑penIndex : ℕ) + (1 : ℕ) = T.length →
  (↑endIndex : ℕ) = T.length →
  B.length + (2 : ℕ) = T.length →
  Bplus.length + (1 : ℕ) = T.length →
  TreeSequenceInitialSegment Bplus T →
  T.vertex penIndex ∈ TreeSequenceVertexSet Bplus := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D penIndex endIndex ell B Bplus penPosition
      endPosition hBLouter hPLouter hBplusTouter
  let i : Fin (Bplus.length + 1) := ⟨Bplus.length, by omega⟩
  have hi : Fin.castLE (Nat.succ_le_succ hBplusTouter.1) i =
      penIndex := by
    apply Fin.ext
    have hp := penPosition
    have hpos : penIndex.val = Bplus.length := by
      have h1 : penIndex.val + 1 = Bplus.length + 1 :=
        hp.trans hPLouter.symm
      omega
    simp only [Fin.val_castLE]
    simpa [i] using hpos.symm
  exact (@Finset.mem_image _ _ (Classical.decEq V)).mpr
    ⟨i, Finset.mem_univ _, by
      apply congrArg T.vertex
      exact hi⟩

theorem helper_hAlphaEtaNe_1071.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
  let alpha : Fin k := D.alpha;
  let penIndex : Fin (T.length + (1 : ℕ)) := D.penultimateVertexIndex;
  let endIndex : Fin (T.length + (1 : ℕ)) := D.terminalVertexIndex;
  ∀ (B Bplus : TreeSequence G e0),
  (↑penIndex : ℕ) + (1 : ℕ) = T.length →
  (↑endIndex : ℕ) = T.length →
  ∀ eta ∈ MissingColors G phi (T.vertex penIndex),
  B.length + (2 : ℕ) = T.length →
  Bplus.length + (1 : ℕ) = T.length →
  TreeSequenceInitialSegment B T →
  TreeSequenceInitialSegment B Bplus →
  ColoredVertexSetElementary G phi (TreeSequenceVertexSet Bplus) →
  ∀ vAlpha ∈ TreeSequenceVertexSet B,
  alpha ∈ MissingColors G phi vAlpha →
  T.vertex penIndex ∈ TreeSequenceVertexSet Bplus →
  alpha ≠ eta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D alpha penIndex endIndex B Bplus
      penPosition endPosition eta hetaMissing hBLouter hPLouter hBTouter hBBplusOuter hElemOuter
      vAlpha hvAlpha hAlphaAt hPenultimateInBplus he
  have hvNe : vAlpha ≠ T.vertex penIndex := by
    intro hv
    obtain ⟨i, _, rfl⟩ := (@Finset.mem_image _ _ (Classical.decEq V)).mp hvAlpha
    have hi : Fin.castLE (Nat.succ_le_succ hBTouter.1) i =
        penIndex := by
      apply T.vertex_injective
      exact (hBTouter.2.1 i).trans hv
    have hval := congrArg Fin.val hi
    simp only [Fin.val_castLE] at hval
    have hiB : i.val ≤ B.length := Nat.lt_succ_iff.mp i.isLt
    have hp := penPosition
    omega
  have hvAlphaBplus := TreeSequenceInitialSegmentVertexSetSubset hBBplusOuter hvAlpha
  have hdis := hElemOuter hvAlphaBplus hPenultimateInBplus hvNe
  exact Finset.disjoint_left.mp hdis hAlphaAt (he ▸ hetaMissing)

theorem helper_hetaFirst_1100.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
  let penIndex : Fin (T.length + (1 : ℕ)) := D.penultimateVertexIndex;
  let endIndex : Fin (T.length + (1 : ℕ)) := D.terminalVertexIndex;
  ∀ (B Bplus : TreeSequence G e0),
  (↑penIndex : ℕ) + (1 : ℕ) = T.length →
  (↑endIndex : ℕ) = T.length →
  ∀ eta ∈ MissingColors G phi (T.vertex penIndex),
  B.length + (2 : ℕ) = T.length →
  Bplus.length + (1 : ℕ) = T.length →
  TreeSequenceInitialSegment Bplus T →
  ColoredVertexSetElementary G phi (TreeSequenceVertexSet Bplus) →
  (
  ∀ (X : TreeSequence G e0) (i : Fin (X.length + (1 : ℕ))),
  X.vertex i ∈ TreeSequenceVertexSet X) →
  (
  ∀ (X : TreeSequence G e0),
  ∀ c ∈ TreeMissingColors phi X,
    c ∈ MissingColors G phi (X.vertex (HierarchyFirstMissingPosition phi X c))) →
  (
  ∀ (X : TreeSequence G e0) (c : Fin k) (i : Fin (X.length + (1 : ℕ))),
  c ∈ MissingColors G phi (X.vertex i) →
  (↑(HierarchyFirstMissingPosition phi X c) : ℕ) ≤ (↑i : ℕ)) →
  T.vertex penIndex ∈ TreeSequenceVertexSet Bplus →
  HierarchyFirstMissingPosition phi T eta = penIndex := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D penIndex endIndex B Bplus penPosition
      endPosition eta hetaMissing hBLouter hPLouter hBplusTouter hElemOuter vertexMemOuter
      firstMissingOuter firstLeOuter hPenultimateInBplus
  apply Fin.ext
  have htreeMiss : eta ∈ TreeMissingColors phi T :=
    Finset.mem_biUnion.mpr ⟨T.vertex penIndex,
      vertexMemOuter T penIndex, hetaMissing⟩
  have hfirstAt := firstMissingOuter T eta htreeMiss
  have hle := firstLeOuter T eta penIndex hetaMissing
  by_contra hne
  have hlt : (HierarchyFirstMissingPosition phi T eta).val <
      penIndex.val := by omega
  let i : Fin (Bplus.length + 1) :=
    ⟨(HierarchyFirstMissingPosition phi T eta).val, by
      have hp := penPosition
      have hpos := hPLouter
      omega⟩
  have hi : Fin.castLE (Nat.succ_le_succ hBplusTouter.1) i =
      HierarchyFirstMissingPosition phi T eta := by
    apply Fin.ext
    rfl
  have hvFirst : T.vertex (HierarchyFirstMissingPosition phi T eta) ∈
      TreeSequenceVertexSet Bplus := by
    exact (@Finset.mem_image _ _ (Classical.decEq V)).mpr
      ⟨i, Finset.mem_univ _, by
        rw [← hBplusTouter.2.1 i]
        apply congrArg T.vertex
        exact hi⟩
  have hverticesNe : T.vertex (HierarchyFirstMissingPosition phi T eta) ≠
      T.vertex penIndex := by
    intro he
    have hv := congrArg Fin.val (T.vertex_injective he)
    omega
  have hdis := hElemOuter hvFirst hPenultimateInBplus hverticesNe
  exact Finset.disjoint_left.mp hdis hfirstAt hetaMissing

theorem helper_thetaOldAvoid_1134.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
  let theta : Fin k := D.theta;
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  ∀ eta ∈ HierarchyStoredColorsAt H q,
  theta ∈ C.good.gamma q eta →
  theta ∉
    ({c : Fin k |
        ∃ (r : Fin T.length),
          A.length ≤ (↑r : ℕ) ∧
            (↑r : ℕ) < min (↑(HierarchyFirstMissingPosition phi T eta) : ℕ) T.length ∧
              phi (T.edge r) = some c} :
      Finset (Fin k)) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D theta H q A eta hetaStored hthetaGamma
  have hh := (Finset.mem_sdiff.mp
    (C.good.avoidance q eta hetaStored hthetaGamma)).2
  change theta ∉ HierarchySegmentColors H q eta at hh
  unfold HierarchySegmentColors at hh
  dsimp only at hh
  have hend : H.stage q.succ = T := by
    convert H.terminalStage using 1
    congr 1
  rw [hend] at hh
  exact hh

theorem helper_horderedUnused_1156.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
  let alpha : Fin k := D.alpha;
  let theta : Fin k := D.theta;
  let penIndex : Fin (T.length + (1 : ℕ)) := D.penultimateVertexIndex;
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  ∀ (B Bplus : TreeSequence G e0),
  alpha ∈ TreeMissingColors phi B →
  (↑penIndex : ℕ) + (1 : ℕ) = T.length →
  ∀ (eta : Fin k),
  B.length + (2 : ℕ) = T.length →
  Bplus.length + (1 : ℕ) = T.length →
  TreeSequenceInitialSegment B T →
  TreeSequenceInitialSegment A T →
  (
  ∀ {X Y : TreeSequence G e0},
  TreeSequenceInitialSegment X Y →
  TreeMissingColors phi X ⊆ TreeMissingColors phi Y) →
  (
  ∀ (X : TreeSequence G e0) (i : Fin (X.length + (1 : ℕ))),
  X.vertex i ∈ TreeSequenceVertexSet X) →
  (
  ∀ (X : TreeSequence G e0),
  ∀ c ∈ TreeMissingColors phi X,
    c ∈ MissingColors G phi (X.vertex (HierarchyFirstMissingPosition phi X c))) →
  theta ∈ TreeMissingColors phi A →
  HierarchyFirstMissingPosition phi T eta = penIndex →
  theta ∉
      ({c : Fin k |
          ∃ (r : Fin T.length),
            A.length ≤ (↑r : ℕ) ∧
              (↑r : ℕ) < min (↑(HierarchyFirstMissingPosition phi T eta) : ℕ) T.length ∧
                phi (T.edge r) = some c} :
        Finset (Fin k)) →
  (↑(HierarchyFirstMissingPosition phi T theta) : ℕ) ≤ A.length →
  (↑(HierarchyFirstMissingPosition phi T alpha) : ℕ) ≤ B.length →
  theta ∉ TreeMissingColors phi A ∨ alpha ∉ TreeMissingColors phi A →
  TreeVertexOrder T (T.vertex (HierarchyFirstMissingPosition phi T theta))
      (T.vertex (HierarchyFirstMissingPosition phi T alpha)) ∧
    theta ∉
      ({c : Fin k |
          ∃ (t : Fin T.length),
            A.length ≤ (↑t : ℕ) ∧
              (↑t : ℕ) < (↑(HierarchyFirstMissingPosition phi T alpha) : ℕ) ∧
                phi (T.edge t) = some c} :
        Finset (Fin k)) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D alpha theta penIndex H q A B Bplus
      alphaBefore penPosition eta hBLouter hPLouter hBTouter hATouter missingMonoOuter
      vertexMemOuter firstMissingOuter hthetaInA hetaFirst thetaOldAvoid hthetaFirstBound
      hAlphaFirstBound hnot
  rcases hnot with hnotTheta | hnotAlpha
  · exact False.elim (hnotTheta hthetaInA)
  · have hAlphaAfter : A.length <
        (HierarchyFirstMissingPosition phi T alpha).val := by
      by_contra h
      have hle : (HierarchyFirstMissingPosition phi T alpha).val ≤ A.length :=
        Nat.le_of_not_gt h
      have hAlphaMissingT : alpha ∈ TreeMissingColors phi T :=
        missingMonoOuter hBTouter alphaBefore
      have hmiss := firstMissingOuter T alpha hAlphaMissingT
      let i : Fin (A.length + 1) :=
        ⟨(HierarchyFirstMissingPosition phi T alpha).val, by omega⟩
      have hi : Fin.castLE (Nat.succ_le_succ hATouter.1) i =
          HierarchyFirstMissingPosition phi T alpha := Fin.ext rfl
      have hvA : A.vertex i ∈ TreeSequenceVertexSet A := vertexMemOuter A i
      have hsameVertex : A.vertex i = T.vertex
          (HierarchyFirstMissingPosition phi T alpha) := by
        rw [← hATouter.2.1 i, hi]
      have hv : T.vertex (HierarchyFirstMissingPosition phi T alpha) ∈
          TreeSequenceVertexSet A := hsameVertex ▸ hvA
      exact hnotAlpha (Finset.mem_biUnion.mpr ⟨_, hv, hmiss⟩)
    refine ⟨?_, ?_⟩
    · exact ⟨HierarchyFirstMissingPosition phi T theta,
        HierarchyFirstMissingPosition phi T alpha, rfl, rfl,
        lt_of_le_of_lt hthetaFirstBound hAlphaAfter⟩
    · intro hc
      obtain ⟨_, t, htA, htB, he⟩ := Finset.mem_filter.mp hc
      apply thetaOldAvoid
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, htA, ?_, he⟩
      rw [hetaFirst]
      have hp := penPosition
      have hlen := hBLouter
      have hfirstAlpha := hAlphaFirstBound
      omega

theorem helper_thetaAvoidsSplit_1203.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
  let theta : Fin k := D.theta;
  let penIndex : Fin (T.length + (1 : ℕ)) := D.penultimateVertexIndex;
  let endIndex : Fin (T.length + (1 : ℕ)) := D.terminalVertexIndex;
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  ∀ (B Bplus : TreeSequence G e0),
  (↑penIndex : ℕ) + (1 : ℕ) = T.length →
  (↑endIndex : ℕ) = T.length →
  ∀ (eta : Fin k),
  B.length + (2 : ℕ) = T.length →
  Bplus.length + (1 : ℕ) = T.length →
  HierarchyFirstMissingPosition phi T eta = penIndex →
  theta ∉
      ({c : Fin k |
          ∃ (r : Fin T.length),
            A.length ≤ (↑r : ℕ) ∧
              (↑r : ℕ) < min (↑(HierarchyFirstMissingPosition phi T eta) : ℕ) T.length ∧
                phi (T.edge r) = some c} :
        Finset (Fin k)) →
  ∀ (t : Fin T.length),
  A.length ≤ (↑t : ℕ) →
  (↑t : ℕ) < Bplus.length →
  phi (T.edge t) ≠ some theta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D theta penIndex endIndex H q A B Bplus
      penPosition endPosition eta hBLouter hPLouter hetaFirst thetaOldAvoid t ht htb he
  apply thetaOldAvoid
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, ht, ?_, he⟩
  rw [hetaFirst]
  have hp := penPosition
  have hpos := hPLouter
  have hbt := t.isLt
  omega

theorem helper_hthetaAlphaNe_1213.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
  let alpha : Fin k := D.alpha;
  let theta : Fin k := D.theta;
  let lastIndex : Fin T.length := D.lastEdgeIndex;
  let penIndex : Fin (T.length + (1 : ℕ)) := D.penultimateVertexIndex;
  let endIndex : Fin (T.length + (1 : ℕ)) := D.terminalVertexIndex;
  ∀ (_ _ : TreeSequence G e0),
  phi (T.edge lastIndex) = some theta →
  alpha ∈ MissingColors G phi (T.vertex endIndex) →
  (↑lastIndex : ℕ) + (1 : ℕ) = T.length →
  (↑penIndex : ℕ) + (1 : ℕ) = T.length →
  (↑endIndex : ℕ) = T.length →
  ∀ (_ : Fin k),
  theta ≠ alpha := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D alpha theta lastIndex penIndex endIndex B
      Bplus lastColor alphaTerminal lastPosition penPosition endPosition eta he
  have hInc : Incident G (T.vertex endIndex) (T.edge lastIndex) := by
    obtain ⟨i, hi⟩ := T.attaches lastIndex
    have hj : lastIndex.succ = endIndex := by
      apply Fin.ext
      have hl := lastPosition
      have ht := endPosition
      simp only [Fin.val_succ]
      omega
    change _ ∈ G.ends (T.edge lastIndex)
    rw [hi, hj]
    exact Sym2.mem_mk_left _ _
  apply (Finset.mem_sdiff.mp alphaTerminal).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, T.edge lastIndex, hInc,
    he ▸ lastColor⟩

theorem helper_hThetaTnq_1236.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
  [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
  (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
  (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
  (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
  let theta : Fin k := D.theta;
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  ∀ (_ _ : TreeSequence G e0) (_ : Fin k),
  theta ∈ HierarchyStageMissingColors H q →
  (0 : ℕ) < H.dividerCount →
  theta ∈
    TreeMissingColors phi
      (H.stage
        (⟨H.dividerCount, by
            have := TreeSequence.positive T
            omega⟩ :
          Fin (H.dividerCount + (2 : ℕ)))) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D theta H q B Bplus eta hstageTheta hz
  have hq0 : q ≠ 0 := by
    intro he
    have hv := congrArg Fin.val he
    simp [q] at hv
    omega
  rcases Fin.eq_zero_or_eq_succ q with hqzero | ⟨i, hqi⟩
  · exact False.elim (hq0 hqzero)
  · rw [hqi] at hstageTheta
    change theta ∈ TreeMissingColors phi (H.stage i.succ.castSucc) at hstageTheta
    have hidx : i.succ.castSucc =
        (⟨H.dividerCount, Nat.lt_succ_of_lt (Nat.lt_succ_self _)⟩ : Fin (H.dividerCount + 2))
           := by
      apply Fin.ext
      have hqval := congrArg Fin.val hqi
      simp only [q, Fin.val_last, Fin.val_succ, Fin.val_castSucc] at hqval ⊢
      omega
    rw [hidx] at hstageTheta
    exact hstageTheta

theorem helper_hChange_1257.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
  [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
  (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
  (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
  (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
  let alpha : Fin k := D.alpha;
  let theta : Fin k := D.theta;
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
  let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
  (
  H.dividerCount = (0 : ℕ) →
  theta ∈ TreeMissingColors phi Tn) →
  (
  (0 : ℕ) < H.dividerCount →
  theta ∈
    TreeMissingColors phi
      (H.stage
        (⟨H.dividerCount,
            by
            have := TreeSequence.positive T
            omega⟩ :
          Fin (H.dividerCount + (2 : ℕ))))) →
  (0 : ℕ) < H.dividerCount ∧
      theta ∈
        TreeMissingColors phi
          (H.stage
            (⟨H.dividerCount,
                by
                have := TreeSequence.positive T
                omega⟩ :
              Fin (H.dividerCount + (2 : ℕ)))) ∨
    H.dividerCount = (0 : ℕ) ∧
      (theta ∈ TreeMissingColors phi Tn ∨
        theta ∈ TreeMissingColors phi A ∧
          theta ∉ TashkinovStoredColors ett.series.data n ∧
            alpha ∉ TashkinovStoredColors ett.series.data n) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D alpha theta H q A n Tn hThetaTn hThetaTnq
  by_cases hz : H.dividerCount = 0
  · right
    exact ⟨hz, Or.inl (hThetaTn hz)⟩
  · left
    exact ⟨Nat.pos_of_ne_zero hz, hThetaTnq (Nat.pos_of_ne_zero hz)⟩

theorem helper_leafComponent_1287.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E)
  (k : ℕ) (rho : PartialEdgeColoring E k) (a b : Fin k),
  a ≠ b →
  IsProperEdgeColoring G rho →
  ∀ (v : V),
  a ∈ MissingColors G rho v ∨ b ∈ MissingColors G rho v →
  ((TwoColorIncidenceGraph G rho a b).neighborSet (Sum.inl v)).Subsingleton := by
  classical
  intro V E _ _ G k rho a b hne hp v hm
  let _ := Fintype.ofFinite V
  as_aux_lemma =>
    have hd : @SimpleGraph.degree _ (TwoColorIncidenceGraph G rho a b)
        (Sum.inl v) (Fintype.ofFinite _) ≤ 1 := by
      rcases hm with ha | hb
      · exact MissingColorIncidenceEndpoint G rho a b hne hp v ha
      · have he : TwoColorIncidenceGraph G rho a b = TwoColorIncidenceGraph G rho b a := by
          ext x y
          cases x <;> cases y <;> simp [TwoColorIncidenceGraph, or_comm]
        rw [he]
        exact MissingColorIncidenceEndpoint G rho b a hne.symm hp v hb
    rw [← SimpleGraph.card_neighborFinset_eq_degree] at hd
    intro x hx y hy
    exact Finset.card_le_one_iff.mp hd
      (by simpa [SimpleGraph.mem_neighborFinset] using hx)
      (by simpa [SimpleGraph.mem_neighborFinset] using hy)

theorem helper_separateVertices_1307.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E)
  (k : ℕ),
  (
  ∀ (rho : PartialEdgeColoring E k) (a b : Fin k) (v : V),
  Sum.inl v ∈ TwoColorComponent G rho a b (Sum.inl v)) →
  (
  ∀ (rho : PartialEdgeColoring E k) (a b : Fin k),
  a ≠ b →
  IsProperEdgeColoring G rho →
  ∀ (v : V),
  a ∈ MissingColors G rho v ∨ b ∈ MissingColors G rho v →
  ((TwoColorIncidenceGraph G rho a b).neighborSet (Sum.inl v)).Subsingleton) →
  ∀ (rho : PartialEdgeColoring E k) (a b : Fin k),
  a ≠ b →
  IsProperEdgeColoring G rho →
  ∀ (u v w : V),
  u ≠ v →
  u ≠ w →
  v ≠ w →
  a ∈ MissingColors G rho u →
  b ∈ MissingColors G rho v →
  a ∈ MissingColors G rho w ∨ b ∈ MissingColors G rho w →
  TwoColorComponent G rho a b (Sum.inl u) = TwoColorComponent G rho a b (Sum.inl v) →
  Disjoint (TwoColorComponent G rho a b (Sum.inl w))
    (TwoColorComponent G rho a b (Sum.inl u)) := by
  classical
  intro V E _ _ G k selfComponent leafComponent rho a b hne hp u v w huv huw hvw hu hv hw hsame
  let _ := Fintype.ofFinite V
  as_aux_lemma =>
    rcases TwoColorComponentsDisjoint G rho a b (Sum.inl w) (Sum.inl u) with he | hd
    · exfalso
      obtain ⟨s, t, p, hpPath, hsupport⟩ :=
        TwoColorComponentSpanningPath G rho a b hp (Sum.inl w)
      have endpoint (x : V) (hx : Sum.inl x ∈ TwoColorComponent G rho a b (Sum.inl w))
          (hm : a ∈ MissingColors G rho x ∨ b ∈ MissingColors G rho x) :
          Sum.inl x = s ∨ Sum.inl x = t := by
        by_contra hn
        push Not at hn
        have hs : Sum.inl x ∈ p.support := by
          change Sum.inl x ∈ {z | z ∈ p.support}
          rw [hsupport]
          exact hx
        exact hpPath.isTrail.not_mem_support_of_subsingleton_neighborSet
          hn.1 hn.2 (leafComponent rho a b hne hp x hm) hs
      have hue := endpoint u (he ▸ selfComponent rho a b u) (Or.inl hu)
      have hve := endpoint v (by rw [he, hsame]; exact selfComponent rho a b v) (Or.inr hv)
      have hwe := endpoint w (selfComponent rho a b w) hw
      rcases hue with hue | hue <;> rcases hve with hve | hve <;>
        rcases hwe with hwe | hwe
      all_goals first
        | exact huv (Sum.inl.inj (hue.trans hve.symm))
        | exact huw (Sum.inl.inj (hue.trans hwe.symm))
        | exact hvw (Sum.inl.inj (hve.trans hwe.symm))
    · exact hd

theorem helper_separateMaybeCoincident_1344.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E)
  (k : ℕ),
  (
  ∀ (rho : PartialEdgeColoring E k) (a b : Fin k) (v : V),
  Sum.inl v ∈ TwoColorComponent G rho a b (Sum.inl v)) →
  (
  ∀ (rho : PartialEdgeColoring E k) (a b : Fin k),
  a ≠ b →
  IsProperEdgeColoring G rho →
  ∀ (u v w : V),
  u ≠ v →
  u ≠ w →
  v ≠ w →
  a ∈ MissingColors G rho u →
  b ∈ MissingColors G rho v →
  a ∈ MissingColors G rho w ∨ b ∈ MissingColors G rho w →
  TwoColorComponent G rho a b (Sum.inl u) =
      TwoColorComponent G rho a b (Sum.inl v) →
  Disjoint (TwoColorComponent G rho a b (Sum.inl w))
    (TwoColorComponent G rho a b (Sum.inl u))) →
  ∀ (rho : PartialEdgeColoring E k) (a b : Fin k),
  a ≠ b →
  IsProperEdgeColoring G rho →
  ∀ (u v w : V),
  u ≠ w →
  v ≠ w →
  a ∈ MissingColors G rho u →
  b ∈ MissingColors G rho v →
  a ∈ MissingColors G rho w ∨ b ∈ MissingColors G rho w →
  TwoColorComponent G rho a b (Sum.inl u) = TwoColorComponent G rho a b (Sum.inl v) →
  Disjoint (TwoColorComponent G rho a b (Sum.inl w))
    (TwoColorComponent G rho a b (Sum.inl u)) := by
  classical
  intro V E _ _ G k selfComponent separateVertices rho a b hne hp u v w huw hvw hu hv hw hsame
  let _ := Fintype.ofFinite V
  as_aux_lemma =>
    by_cases huv : u = v
    · subst v
      rcases TwoColorComponentsDisjoint G rho a b (Sum.inl w) (Sum.inl u) with he | hd
      · have noColor (c : Fin k) (hc : c ∈ MissingColors G rho u)
            (f : E) (hf : Incident G u f) : rho f ≠ some c := by
          intro hcol
          exact (Finset.mem_sdiff.mp hc).2
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, f, hf, hcol⟩)
        have hn : (TwoColorIncidenceGraph G rho a b).neighborSet (Sum.inl u) = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro x hx
          cases x with
          | inl x => exact hx
          | inr f =>
            rcases hx with ⟨hi, hc⟩
            exact hc.elim (noColor a hu f hi) (noColor b hv f hi)
        have hwIn : Sum.inl w ∈ TwoColorComponent G rho a b (Sum.inl u) :=
          he ▸ selfComponent rho a b w
        change (TwoColorIncidenceGraph G rho a b).connectedComponentMk (Sum.inl w) =
          (TwoColorIncidenceGraph G rho a b).connectedComponentMk (Sum.inl u) at hwIn
        exact False.elim (SimpleGraph.not_reachable_of_neighborSet_left_eq_empty
          (fun h => huw (Sum.inl.inj h)) hn
          (SimpleGraph.ConnectedComponent.exact hwIn).symm)
      · exact hd
    · exact separateVertices rho a b hne hp u v w huv huw hvw hu hv hw hsame

theorem helper_hthetaTerminalNe_1391.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
  let theta : Fin k := D.theta;
  let endIndex : Fin (T.length + (1 : ℕ)) := D.terminalVertexIndex;
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let ell : ℕ := HierarchyFullTailLength C;
  (↑endIndex : ℕ) = T.length →
  (2 : ℕ) ≤ ell →
  ell = T.length - A.length →
  (↑(HierarchyFirstMissingPosition phi T theta) : ℕ) ≤ A.length →
  T.vertex (HierarchyFirstMissingPosition phi T theta) ≠ T.vertex endIndex := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D theta endIndex H q A ell endPosition
      hTailAtLeast hellOuter hthetaFirstBound he
  have hv := congrArg Fin.val (T.vertex_injective he)
  have ht := endPosition
  have hlen := hellOuter
  have htail := hTailAtLeast
  have hbound := hthetaFirstBound
  clear * - hv ht hlen htail hbound
  omega

theorem helper_hAlphaTerminalNe_1401.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
  let alpha : Fin k := D.alpha;
  let endIndex : Fin (T.length + (1 : ℕ)) := D.terminalVertexIndex;
  ∀ (B : TreeSequence G e0),
  (↑endIndex : ℕ) = T.length →
  B.length + (2 : ℕ) = T.length →
  (↑(HierarchyFirstMissingPosition phi T alpha) : ℕ) ≤ B.length →
  T.vertex (HierarchyFirstMissingPosition phi T alpha) ≠ T.vertex endIndex := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D alpha endIndex B endPosition hBLouter
      hAlphaFirstBound he
  have hv := congrArg Fin.val (T.vertex_injective he)
  have ht := endPosition
  have hlen := hBLouter
  have hbound := hAlphaFirstBound
  clear * - hv ht hlen hbound
  omega

theorem helper_prefixMissing_1434.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E)
  (k : ℕ) (e0 : E) (Bplus : TreeSequence G e0) (z : V ⊕ E)
  (rho : PartialEdgeColoring E k) (a b : Fin k),
  a ≠ b →
  IsProperEdgeColoring G rho →
  ColoredVertexSetElementary G rho (TreeSequenceVertexSet Bplus) →
  ∀ (u v : V),
  u ∈ TreeSequenceVertexSet Bplus →
  v ∈ TreeSequenceVertexSet Bplus →
  a ∈ MissingColors G rho u →
  b ∈ MissingColors G rho v →
  Sum.inl u ∉ TwoColorComponent G rho a b z →
  Sum.inl v ∉ TwoColorComponent G rho a b z →
  ∀ w ∈ TreeSequenceVertexSet Bplus,
  MissingColors G (TwoColorComponentSwap G rho a b z) w = MissingColors G rho w := by
  classical
  intro V E _ _ G k e0 Bplus z rho a b hne hp helem u v huB hvB hu hv hdu hdv
  let _ := Fintype.ofFinite V
  as_aux_lemma =>
    have behavior := TwoColorComponentSwapMissingBehavior G rho a b hne hp z
    intro w hwB
    by_cases hw : Sum.inl w ∈ TwoColorComponent G rho a b z
    · have hwa : a ∉ MissingColors G rho w := by
        intro hm
        have hwu : w ≠ u := fun he => hdu (he ▸ hw)
        exact Finset.disjoint_left.mp (helem hwB huB hwu) hm hu
      have hwb : b ∉ MissingColors G rho w := by
        intro hm
        have hwv : w ≠ v := fun he => hdv (he ▸ hw)
        exact Finset.disjoint_left.mp (helem hwB hvB hwv) hm hv
      have presentSwapped (c d : Fin k)
          (hd : d ∉ MissingColors G rho w)
          (hdab : (d = a ∧ c = b) ∨ (d = b ∧ c = a)) :
          c ∉ MissingColors G (TwoColorComponentSwap G rho a b z) w := by
        have hpres : d ∈ PresentColors G rho w := by simpa [MissingColors] using hd
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and] at hpres
        rcases hpres with ⟨e, hwe, he⟩
        have hadj : (TwoColorIncidenceGraph G rho a b).Adj (Sum.inr e) (Sum.inl w) := by
          simp only [TwoColorIncidenceGraph]
          exact ⟨hwe, hdab.elim (fun h => Or.inl (he.trans (congrArg some h.1)))
            (fun h => Or.inr (he.trans (congrArg some h.1)))⟩
        have heC : Sum.inr e ∈ TwoColorComponent G rho a b z := by
          change (TwoColorIncidenceGraph G rho a b).connectedComponentMk (Sum.inl w) = _ at hw
          change (TwoColorIncidenceGraph G rho a b).connectedComponentMk (Sum.inr e) = _
          exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans hw
        have heSwap : TwoColorComponentSwap G rho a b z e = some c := by
          rcases hdab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · simp [TwoColorComponentSwap, heC, he]
          · simp [TwoColorComponentSwap, heC, he]
        have hpresent : c ∈ PresentColors G (TwoColorComponentSwap G rho a b z) w := by
          simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨e, hwe, heSwap⟩
        simpa [MissingColors] using hpresent
      have hnewa := presentSwapped a b hwb (Or.inr ⟨rfl, rfl⟩)
      have hnewb := presentSwapped b a hwa (Or.inl ⟨rfl, rfl⟩)
      apply Finset.ext
      intro c
      by_cases hca : c = a
      · subst c
        simp only [hnewa, hwa]
      · by_cases hcb : c = b
        · subst c
          simp only [hnewb, hwb]
        · exact behavior.2.2.2 w c hca hcb
    · exact behavior.1 w hw

theorem helper_hThetaFirstBplus_1491.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
  let theta : Fin k := D.theta;
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  ∀ (Bplus : TreeSequence G e0),
  TreeSequenceInitialSegment Bplus T →
  TreeSequenceInitialSegment A Bplus →
  (↑(HierarchyFirstMissingPosition phi T theta) : ℕ) ≤ A.length →
  T.vertex (HierarchyFirstMissingPosition phi T theta) ∈ TreeSequenceVertexSet Bplus := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D theta H q A Bplus hBplusTouter
      hABplusouter hthetaFirstBound
  let i : Fin (T.length + 1) := HierarchyFirstMissingPosition phi T theta
  have hi : i.val ≤ Bplus.length := le_trans hthetaFirstBound hABplusouter.1
  let j : Fin (Bplus.length + 1) := ⟨i.val, Nat.lt_succ_of_le hi⟩
  have he : Fin.castLE (Nat.succ_le_succ hBplusTouter.1) j = i := Fin.ext rfl
  exact (@Finset.mem_image _ _ (Classical.decEq V)).mpr
    ⟨j, Finset.mem_univ _, (hBplusTouter.2.1 j).symm.trans (congrArg T.vertex he)⟩

theorem helper_hAlphaFirstBplus_1500.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
  let alpha : Fin k := D.alpha;
  let penIndex : Fin (T.length + (1 : ℕ)) := D.penultimateVertexIndex;
  let endIndex : Fin (T.length + (1 : ℕ)) := D.terminalVertexIndex;
  ∀ (B Bplus : TreeSequence G e0),
  (↑penIndex : ℕ) + (1 : ℕ) = T.length →
  (↑endIndex : ℕ) = T.length →
  ∀ (_ : Fin k),
  B.length + (2 : ℕ) = T.length →
  Bplus.length + (1 : ℕ) = T.length →
  TreeSequenceInitialSegment Bplus T →
  (↑(HierarchyFirstMissingPosition phi T alpha) : ℕ) ≤ B.length →
  T.vertex (HierarchyFirstMissingPosition phi T alpha) ∈ TreeSequenceVertexSet Bplus := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D alpha penIndex endIndex B Bplus
      penPosition endPosition eta hBLouter hPLouter hBplusTouter hAlphaFirstBound
  let i : Fin (T.length + 1) := HierarchyFirstMissingPosition phi T alpha
  have hi : i.val ≤ Bplus.length := le_trans hAlphaFirstBound
    (by omega)
  let j : Fin (Bplus.length + 1) := ⟨i.val, Nat.lt_succ_of_le hi⟩
  have he : Fin.castLE (Nat.succ_le_succ hBplusTouter.1) j = i := Fin.ext rfl
  exact (@Finset.mem_image _ _ (Classical.decEq V)).mpr
    ⟨j, Finset.mem_univ _, (hBplusTouter.2.1 j).symm.trans (congrArg T.vertex he)⟩

theorem helper_hvOutsideOne_1516.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
  let alpha : Fin k := D.alpha;
  let theta : Fin k := D.theta;
  let endIndex : Fin (T.length + (1 : ℕ)) := D.terminalVertexIndex;
  TwoColorComponent G phi theta alpha
        (Sum.inl (T.vertex (HierarchyFirstMissingPosition phi T theta))) =
      TwoColorComponent G phi theta alpha
        (Sum.inl (T.vertex (HierarchyFirstMissingPosition phi T alpha))) →
  (
  ∀ (rho : PartialEdgeColoring E k) (a b : Fin k) (v : V),
  Sum.inl v ∈ TwoColorComponent G rho a b (Sum.inl v)) →
  Disjoint (TwoColorComponent G phi theta alpha (Sum.inl (T.vertex endIndex)))
      (TwoColorComponent G phi theta alpha
        (Sum.inl (T.vertex (HierarchyFirstMissingPosition phi T theta)))) →
  let z : V ⊕ E := Sum.inl (T.vertex endIndex);
  Sum.inl (T.vertex (HierarchyFirstMissingPosition phi T alpha)) ∉
    TwoColorComponent G phi theta alpha z := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D alpha theta endIndex hcomponentEq
      selfComponent hdisjointComponent z hh
  have hhTheta : Sum.inl (T.vertex (HierarchyFirstMissingPosition phi T alpha)) ∈
      TwoColorComponent G phi theta alpha
        (Sum.inl (T.vertex (HierarchyFirstMissingPosition phi T theta))) := by
    rw [hcomponentEq]
    exact selfComponent phi theta alpha
      (T.vertex (HierarchyFirstMissingPosition phi T alpha))
  exact Set.disjoint_left.mp hdisjointComponent hh hhTheta

theorem helper_hfixedCoreOne_1548.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
  let alpha : Fin k := D.alpha;
  let theta : Fin k := D.theta;
  let endIndex : Fin (T.length + (1 : ℕ)) := D.terminalVertexIndex;
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  ∀ (_ _ : TreeSequence G e0),
  let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
  let _ : TreeSequence G e0 := ett.series.data.tree n.castSucc;
  ∀ (_ : Fin k),
  let z : V ⊕ E := Sum.inl (T.vertex endIndex);
  let muOne : PartialEdgeColoring E k := TwoColorComponentSwap G phi theta alpha z;
  (
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  have n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  have Tnq : TreeSequence G e0 :=
    H.stage
      (⟨H.dividerCount, by
          have := TreeSequence.positive T
          omega⟩ :
        Fin (H.dividerCount + (2 : ℕ)));
  have Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
  have Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q;
  HierarchyWeaklyStable H q muOne ∧
        ModColoring ett muOne ∧
          (A = Tn ∨
              ∃ (inputA : PartialEdgeColoring E k) (ettA :
                ExtendedTashkinovTree G k e0 inputA A muOne), MaximumProperty ettA) ∧
            (
    (0 : ℕ) < H.dividerCount →
    ∃ (inputA : PartialEdgeColoring E k) (ettA :
                  ExtendedTashkinovTree G k e0 inputA A muOne) (baseA :
                  HierarchyBase ettA muOne) (K : TashkinovHierarchy ettA baseA) (goodA :
                  GoodHierarchy K),
                  MaximumProperty ettA ∧
                    ettA.series.data.kind (Fin.last ettA.rounds) =
                        ett.series.data.kind (Fin.last ett.rounds) ∧
                      ∃ (hcount : K.dividerCount + (1 : ℕ) = H.dividerCount),
                        baseA.core = base.core ∧
                          baseA.closure = base.closure ∧
                            (
    ∀ (j : Fin (K.dividerCount + (2 : ℕ))),
    K.stage j =
      H.stage
        (⟨(↑j : ℕ),
            by
            have := TreeSequence.positive T
            omega⟩ :
          Fin (H.dividerCount + (2 : ℕ)))) ∧
                              (
    ∀ (j : Fin (K.dividerCount + (1 : ℕ))),
    have jH : Fin (H.dividerCount + (1 : ℕ)) :=
      (⟨(↑j : ℕ),
          by
          have := TreeSequence.positive T
          omega⟩ :
        Fin (H.dividerCount + (1 : ℕ)));
    HierarchyStoredColorsAt K j = HierarchyStoredColorsAt H jH ∧
      ∀ eta ∈ HierarchyStoredColorsAt K j,
        goodA.gamma j eta = C.good.gamma jH eta) ∧
                                TreeColorSetMinusClosed G muOne Tnq
                                  (Dnq.biUnion
                                    (C.good.gamma
                                      (⟨C.hierarchy.dividerCount - (1 : ℕ),
                                          by
                                          have := TreeSequence.positive T
                                          omega⟩ :
                                        Fin (C.hierarchy.dividerCount + (1 : ℕ))))))) →
  ∀ (t : Fin A.length),
  muOne (A.edge t) = phi (A.edge t) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D alpha theta endIndex H q A B Bplus n Tn
      eta z muOne hstableOne
  by_cases hz : H.dividerCount = 0
  · have hq : q = 0 := Fin.ext (by simp [q, hz])
    have hw := hstableOne.1
    have hi : (Fin.last H.dividerCount : Fin (H.dividerCount + 1)) = 0 := Fin.ext hz
    rw [hi] at hw
    change (if ett.series.data.kind (Fin.last ett.rounds) =
        some TashkinovExtensionKind.PE then
      CombinedStableColoring Tn base.closure
        (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) phi muOne
      else StableColoring Tn
        (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) phi muOne) at hw
    have hcore := P2813_T1_BaseDisplayedEdges G k e0 input T phi ett base muOne
      ctx.oneEdgeUncolored hstableOne.2.1.2.1 hw
    have hAzero : A = base.core := by
      change HierarchyStarredStage H q = base.core
      rw [hq]
      rfl
    rw [hAzero]
    exact hcore
  · have hq : q = (⟨H.dividerCount - 1, by omega⟩ : Fin H.dividerCount).succ := by
      apply Fin.ext
      simp only [q, Fin.val_last, Fin.val_succ]
      omega
    have hw := hstableOne.1
    have hi : (Fin.last H.dividerCount : Fin (H.dividerCount + 1)) =
        (⟨H.dividerCount - 1, by omega⟩ : Fin H.dividerCount).succ := hq
    rw [hi] at hw
    intro t
    have hAstage : A = H.stage
        (⟨H.dividerCount - 1, by omega⟩ : Fin H.dividerCount).succ.castSucc := by
      change HierarchyStarredStage H _ = _
      rw [hq]
      rfl
    by_cases ht : 1 ≤ t.val
    · have hinv := (hAstage ▸ hw.2.1) t ht
      exact hinv
    · have ht0 : t.val = 0 := by omega
      have he : A.edge t = e0 := by
        rw [show t = ⟨0, A.positive⟩ from Fin.ext ht0]
        exact A.first_edge
      rw [he, hstableOne.2.1.2.1.1, ctx.oneEdgeUncolored.1]

theorem helper_hlastIncident_1596.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
  let lastIndex : Fin T.length := D.lastEdgeIndex;
  let penIndex : Fin (T.length + (1 : ℕ)) := D.penultimateVertexIndex;
  let endIndex : Fin (T.length + (1 : ℕ)) := D.terminalVertexIndex;
  ∀ (_ _ : TreeSequence G e0),
  (↑lastIndex : ℕ) + (1 : ℕ) = T.length →
  (↑penIndex : ℕ) + (1 : ℕ) = T.length →
  (↑endIndex : ℕ) = T.length →
  ∀ (_ : Fin k),
  Incident G (T.vertex endIndex) (T.edge lastIndex) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D lastIndex penIndex endIndex B Bplus
      lastPosition penPosition endPosition eta
  obtain ⟨i, hi⟩ := T.attaches lastIndex
  have hj : lastIndex.succ = endIndex := by
    apply Fin.ext
    have hl := lastPosition
    have ht := endPosition
    simp only [Fin.val_succ]
    omega
  change _ ∈ G.ends (T.edge lastIndex)
  rw [hi, hj]
  exact Sym2.mem_mk_left _ _

theorem helper_hlastEdgeInOne_1608.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
  let alpha : Fin k := D.alpha;
  let theta : Fin k := D.theta;
  let lastIndex : Fin T.length := D.lastEdgeIndex;
  let endIndex : Fin (T.length + (1 : ℕ)) := D.terminalVertexIndex;
  phi (T.edge lastIndex) = some theta →
  let z : V ⊕ E := Sum.inl (T.vertex endIndex);
  Incident G (T.vertex endIndex) (T.edge lastIndex) →
  Sum.inr (T.edge lastIndex) ∈ TwoColorComponent G phi theta alpha z := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D alpha theta lastIndex endIndex lastColor
      z hlastIncident
  have hadj : (TwoColorIncidenceGraph G phi theta alpha).Adj
      (Sum.inr (T.edge lastIndex)) z := by
    exact ⟨hlastIncident, Or.inl lastColor⟩
  change (TwoColorIncidenceGraph G phi theta alpha).connectedComponentMk
    (Sum.inr (T.edge lastIndex)) = _
  exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj

theorem helper_segTrans_1626.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
  {X Y Z : TreeSequence G e0},
  TreeSequenceInitialSegment X Y →
  TreeSequenceInitialSegment Y Z →
  TreeSequenceInitialSegment X Z := by
  classical
  intro V E G e0 X Y Z hXY hYZ
  refine ⟨hXY.1.trans hYZ.1, ?_, ?_⟩
  · intro i
    exact (hYZ.2.1 (Fin.castLE (Nat.succ_le_succ hXY.1) i)).trans (hXY.2.1 i)
  · intro i
    exact (hYZ.2.2 (Fin.castLE hXY.1 i)).trans (hXY.2.2 i)

theorem helper_stageSegment_1634.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
  [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
  (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
  (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
  (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (_ : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  ∀ (_ _ : TreeSequence G e0) (_ : Fin k),
  (
  ∀ {X Y Z : TreeSequence G e0},
  TreeSequenceInitialSegment X Y →
  TreeSequenceInitialSegment Y Z →
  TreeSequenceInitialSegment X Z) →
  ∀ (a d : ℕ) (hb : a + d ≤ H.dividerCount + (1 : ℕ)),
  TreeSequenceInitialSegment
    (H.stage
      (⟨a, by
          have := TreeSequence.positive T
          omega⟩ :
        Fin (H.dividerCount + (2 : ℕ))))
    (H.stage
      (⟨a + d, by
          have := TreeSequence.positive T
          omega⟩ :
        Fin (H.dividerCount + (2 : ℕ)))) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H B Bplus eta segTrans a d hb
  as_aux_lemma =>
    clear * - H a d hb segTrans
    induction d with
    | zero => exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
    | succ d ih =>
        exact segTrans (ih (by omega)) (H.nested ⟨a + d, by omega⟩)

theorem helper_lastPositive_1645.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
  [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
  (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
  (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
  (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (_ : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  ∀ (_ _ : TreeSequence G e0) (_ : Fin k),
  H.dividerCount ≠ (0 : ℕ) →
  A =
    H.stage
      (⟨H.dividerCount, by
          have := TreeSequence.positive T
          omega⟩ :
        Fin (H.dividerCount + (2 : ℕ))) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B Bplus eta hz
  have hq : q = (⟨H.dividerCount - 1, by omega⟩ : Fin H.dividerCount).succ := by
    apply Fin.ext
    simp only [q, Fin.val_last, Fin.val_succ]
    omega
  change HierarchyStarredStage H q = H.stage ⟨H.dividerCount, Nat.lt_succ_of_lt
      (Nat.lt_succ_self _)⟩
  rw [hq]
  change H.stage
    ((⟨H.dividerCount - 1, by omega⟩ : Fin H.dividerCount).succ.castSucc) = _
  apply congrArg H.stage
  apply Fin.ext
  simp only [Fin.val_castSucc, Fin.val_succ]
  omega

theorem helper_coreToA_1660.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
  [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
  (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
  (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
  (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (_ : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  ∀ (_ _ : TreeSequence G e0) (_ : Fin k),
  (
  ∀ {X Y Z : TreeSequence G e0},
  TreeSequenceInitialSegment X Y →
  TreeSequenceInitialSegment Y Z →
  TreeSequenceInitialSegment X Z) →
  (
  ∀ (a d : ℕ) (hb : a + d ≤ H.dividerCount + (1 : ℕ)),
  TreeSequenceInitialSegment
    (H.stage
      (⟨a, by
          have := TreeSequence.positive T
          omega⟩ :
        Fin (H.dividerCount + (2 : ℕ))))
    (H.stage
      (⟨a + d, by
          have := TreeSequence.positive T
          omega⟩ :
        Fin (H.dividerCount + (2 : ℕ))))) →
  (
  H.dividerCount = (0 : ℕ) →
  A = base.core) →
  (
  H.dividerCount ≠ (0 : ℕ) →
  A =
    H.stage
      (⟨H.dividerCount,
          by
          have := TreeSequence.positive T
          omega⟩ :
        Fin (H.dividerCount + (2 : ℕ)))) →
  TreeSequenceInitialSegment base.core A := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B Bplus eta segTrans stageSegment
      lastZero lastPositive
  by_cases hz : H.dividerCount = 0
  · rw [lastZero hz]
    exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
  · rw [lastPositive hz]
    have hs := stageSegment 1 (H.dividerCount - 1) (by omega)
    have he : 1 + (H.dividerCount - 1) = H.dividerCount := by omega
    simpa [he] using segTrans H.coreInsideFirst hs

theorem helper_hTnBplus_1668.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (_ : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx)
  (_ Bplus : TreeSequence G e0),
  let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
  let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
  ∀ (_ : Fin k),
  Bplus.length + (1 : ℕ) = T.length →
  TreeSequenceInitialSegment Bplus T →
  TreeSequenceInitialSegment Tn Bplus := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D B Bplus n Tn eta hPLouter hBplusTouter
  have hsourceT : TreeSequenceInitialSegment Tn T := ett.abovePenultimate
  have hlen : Tn.length ≤ Bplus.length := by
    have hs : Tn.length < T.length := by
      have hi : n.castSucc = (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2)) :=
        Fin.ext rfl
      simpa [Tn, n, hi] using ett.strictAbovePenultimate
    have hp := hPLouter
    clear * - hs hp
    omega
  exact ⟨hlen,
    fun i => (hBplusTouter.2.1 (Fin.castLE (Nat.succ_le_succ hlen) i)).symm.trans
      (hsourceT.2.1 i),
    fun i => (hBplusTouter.2.2 (Fin.castLE hlen i)).symm.trans (hsourceT.2.2 i)⟩

theorem helper_hfixedBplusAux_1682.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
  let alpha : Fin k := D.alpha;
  let theta : Fin k := D.theta;
  let endIndex : Fin (T.length + (1 : ℕ)) := D.terminalVertexIndex;
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  ∀ (Bplus : TreeSequence G e0),
  TreeSequenceInitialSegment Bplus T →
  TreeSequenceInitialSegment A Bplus →
  let z : V ⊕ E := Sum.inl (T.vertex endIndex);
  let muOne : PartialEdgeColoring E k := TwoColorComponentSwap G phi theta alpha z;
  (
  ∀ (t : Fin A.length),
  muOne (A.edge t) = phi (A.edge t)) →
  (
  ∀ (t : Fin T.length),
  A.length ≤ (↑t : ℕ) →
  (↑t : ℕ) < Bplus.length →
  muOne (T.edge t) = phi (T.edge t)) →
  ∀ (aLen : ℕ),
  aLen = A.length →
  (
  ∀ (t : Fin Bplus.length),
  (↑t : ℕ) < aLen ∨ aLen ≤ (↑t : ℕ)) →
  ∀ (t : Fin Bplus.length),
  muOne (Bplus.edge t) = phi (Bplus.edge t) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D alpha theta endIndex H q A Bplus
      hBplusTouter hABplusouter z muOne hfixedCoreOne hfixedSplit aLen haLen hcut
  as_aux_lemma =>
    intro t
    have left (ha : t.val < aLen) :
        muOne (Bplus.edge t) = phi (Bplus.edge t) := by
      let ta0 : Fin aLen := ⟨t.val, ha⟩
      let ta : Fin A.length := Fin.cast haLen ta0
      have he : Fin.castLE hABplusouter.1 ta = t := Fin.ext (by simp [ta, ta0])
      have heEdge : Bplus.edge t = A.edge ta := by
        calc
          Bplus.edge t = Bplus.edge (Fin.castLE hABplusouter.1 ta) := by rw [he]
          _ = A.edge ta := hABplusouter.2.2 ta
      rw [heEdge]
      exact hfixedCoreOne ta
    have right (ha : aLen ≤ t.val) :
        muOne (Bplus.edge t) = phi (Bplus.edge t) := by
      let tt : Fin T.length := Fin.castLE hBplusTouter.1 t
      have he : Bplus.edge t = T.edge tt := (hBplusTouter.2.2 t).symm
      rw [he]
      apply hfixedSplit tt
      · have hh : A.length ≤ t.val := by rw [← haLen]; exact ha
        exact hh
      · have hval : tt.val = t.val := by simp [tt]
        rw [hval]
        exact t.isLt
    exact (hcut t).elim left right

theorem helper_hBplusLength_1712.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
  (T B Bplus : TreeSequence G e0),
  B.length + (2 : ℕ) = T.length →
  Bplus.length + (1 : ℕ) = T.length →
  Bplus.length = B.length + (1 : ℕ) := by
  classical
  intro V E G e0 T B Bplus hBLouter hPLouter
  have hp := hPLouter
  have hb := hBLouter
  apply Nat.succ.inj
  change Bplus.length + 1 = (B.length + 1) + 1
  calc
    Bplus.length + 1 = T.length := hp
    _ = B.length + 2 := hb.symm
    _ = (B.length + 1) + 1 := by rfl

theorem helper_transportOne_1721.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
  let alpha : Fin k := D.alpha;
  let theta : Fin k := D.theta;
  let endIndex : Fin (T.length + (1 : ℕ)) := D.terminalVertexIndex;
  ∀ (B Bplus : TreeSequence G e0),
  TreeSequenceInitialSegment B Bplus →
  let z : V ⊕ E := Sum.inl (T.vertex endIndex);
  let muOne : PartialEdgeColoring E k := TwoColorComponentSwap G phi theta alpha z;
  (∀ v ∈ TreeSequenceVertexSet Bplus, MissingColors G muOne v = MissingColors G phi v) →
  (
  ∀ (t : Fin Bplus.length),
  muOne (Bplus.edge t) = phi (Bplus.edge t)) →
  Bplus.length = B.length + (1 : ℕ) →
  ∀ (S : TreeSequence G e0),
  TashkinovAugmentationSequence phi S Bplus →
  TashkinovAugmentationSequence muOne S Bplus := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D alpha theta endIndex B Bplus hBBplusOuter
      z muOne hmissingOne hfixedBplus hBplusLength S hseq
  refine TashkinovAugmentationSequenceColoringTransport phi muOne S B Bplus hseq
    hBBplusOuter hBplusLength ?_ ?_
  · intro t _
    exact hfixedBplus t
  · intro v hv
    exact hmissingOne v (TreeSequenceInitialSegmentVertexSetSubset hBBplusOuter hv)

theorem helper_hrouteOne_1730.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
  let alpha : Fin k := D.alpha;
  let theta : Fin k := D.theta;
  let endIndex : Fin (T.length + (1 : ℕ)) := D.terminalVertexIndex;
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let ell : ℕ := HierarchyFullTailLength C;
  ∀ (Bplus : TreeSequence G e0),
  let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
  let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
  (
  have n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
  have Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
  have Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
  ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
      TashkinovAugmentationSequence phi Tn T ∨
    (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
        ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
      ∃ (f : E) (seed : TreeSequence G e0),
        ett.series.data.connectingEdges n = ({ f } : Finset E) ∧
          TreeSequenceAdjoinEdge Tn f seed ∧
            TreeIncidentEdge Tn f ∧
              (∃ c ∈ TreeMissingColors phi Tn ∪ Dn, phi f = some c) ∧
                TashkinovAugmentationSequence phi seed T) →
  (2 : ℕ) ≤ ell →
  ell = T.length - A.length →
  Bplus.length + (1 : ℕ) = T.length →
  TreeSequenceInitialSegment Bplus T →
  TreeSequenceInitialSegment A Bplus →
  let z : V ⊕ E := Sum.inl (T.vertex endIndex);
  let muOne : PartialEdgeColoring E k := TwoColorComponentSwap G phi theta alpha z;
  (
  ∀ {X Y Z : TreeSequence G e0},
  TreeSequenceInitialSegment X Y →
  TreeSequenceInitialSegment Y Z →
  TreeSequenceInitialSegment X Z) →
  TreeSequenceInitialSegment base.core A →
  TreeSequenceInitialSegment Tn Bplus →
  (
  ∀ (S : TreeSequence G e0),
  TashkinovAugmentationSequence phi S Bplus →
  TashkinovAugmentationSequence muOne S Bplus) →
  ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
      TashkinovAugmentationSequence muOne Tn Bplus ∨
    (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
        ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
      ∃ (f : E) (seed : TreeSequence G e0),
        ett.series.data.connectingEdges n = ({ f } : Finset E) ∧
          TreeSequenceAdjoinEdge Tn f seed ∧
            TashkinovAugmentationSequence muOne seed Bplus := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D alpha theta endIndex H q A ell Bplus n Tn
      oldRoute hTailAtLeast hellOuter hPLouter hBplusTouter hABplusouter z muOne segTrans coreToA
      hTnBplus transportOne
  rcases oldRoute with ⟨hp, hseq⟩ |
    ⟨hnp', f, seed, hconnecting, hadjoin, _, _, hseq⟩
  · have hsourceB := hTnBplus
    exact Or.inl ⟨hp, transportOne Tn
      (TashkinovAugmentationSequenceRestrict phi Tn Bplus T hseq hsourceB hBplusTouter)⟩
  · have hseedT : TreeSequenceInitialSegment seed T :=
      TashkinovAugmentationSequenceInitialSegment phi seed T hseq
    have hnp : ett.series.data.kind n ≠ some TashkinovExtensionKind.PE := by
      intro hpe
      rcases hnp' with hse | hre
      · rw [hpe] at hse
        cases hse
      · rw [hpe] at hre
        cases hre
    have hTnA : TreeSequenceInitialSegment Tn A := by
      have hcoreTn : base.core = Tn := by
        simpa [Tn, n] using base.nonparallel hnp
      have hTnCore : TreeSequenceInitialSegment Tn base.core := by
        rw [hcoreTn]
        exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
      exact segTrans hTnCore coreToA
    have hseedLen : seed.length ≤ Bplus.length := by
      have hadjLen := hadjoin.1
      change seed.length = Tn.length + 1 at hadjLen
      have ha := hTnA.1
      have htail := hTailAtLeast
      have hp := hPLouter
      have hell := hellOuter
      have hAlen := hABplusouter.1
      clear * - hadjLen ha htail hp hell hAlen
      omega
    have hseedB : TreeSequenceInitialSegment seed Bplus := by
      refine ⟨hseedLen, ?_, ?_⟩
      · intro i
        exact (hBplusTouter.2.1 (Fin.castLE (Nat.succ_le_succ hseedLen) i)).symm.trans
          (hseedT.2.1 i)
      · intro i
        exact (hBplusTouter.2.2 (Fin.castLE hseedLen i)).symm.trans (hseedT.2.2 i)
    exact Or.inr ⟨hnp', f, seed, hconnecting, hadjoin,
      transportOne seed
        (TashkinovAugmentationSequenceRestrict phi seed Bplus T hseq hseedB hBplusTouter)⟩

theorem helper_firstWitness_1779.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E)
  (k : ℕ) (e0 : E) (T Bplus : TreeSequence G e0),
  TreeSequenceInitialSegment Bplus T →
  ∀ (rho : PartialEdgeColoring E k),
  ∀ c ∈ TreeMissingColors rho Bplus,
  c ∈ MissingColors G rho (T.vertex (HierarchyFirstMissingPosition rho T c)) ∧
    (↑(HierarchyFirstMissingPosition rho T c) : ℕ) ≤ Bplus.length := by
  classical
  intro V E _ _ G k e0 T Bplus hBplusTouter rho c hc
  let _ := Fintype.ofFinite V
  as_aux_lemma =>
    obtain ⟨v, hv, hvc⟩ := Finset.mem_biUnion.mp hc
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hv
    obtain ⟨i, rfl⟩ := hv
    let candidates := Finset.univ.filter fun j : Fin (T.length + 1) =>
      c ∈ MissingColors G rho (T.vertex j)
    have hi : Fin.castLE (Nat.succ_le_succ hBplusTouter.1) i ∈ candidates := by
      simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hBplusTouter.2.1 i]
      exact hvc
    have hn : candidates.Nonempty := ⟨_, hi⟩
    have hm := (Finset.mem_filter.mp (Finset.min'_mem candidates hn)).2
    have hle := Finset.min'_le candidates _ hi
    unfold HierarchyFirstMissingPosition
    change (c ∈ MissingColors G rho (T.vertex (if h : candidates.Nonempty then
      candidates.min' h else Fin.last T.length))) ∧ _
    rw [dite_eq_left hn]
    refine ⟨hm, ?_⟩
    change (candidates.min' hn).val ≤ i.val at hle
    have hib := i.isLt
    omega

theorem helper_firstPreserved_1805.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E)
  (k : ℕ) (e0 : E) (T Bplus : TreeSequence G e0),
  TreeSequenceInitialSegment Bplus T →
  (
  ∀ (rho : PartialEdgeColoring E k),
  ∀ c ∈ TreeMissingColors rho Bplus,
    c ∈ MissingColors G rho (T.vertex (HierarchyFirstMissingPosition rho T c)) ∧
      (↑(HierarchyFirstMissingPosition rho T c) : ℕ) ≤ Bplus.length) →
  ∀ (rho sigma : PartialEdgeColoring E k) (c : Fin k),
  ColoredVertexSetElementary G rho (TreeSequenceVertexSet Bplus) →
  (∀ v ∈ TreeSequenceVertexSet Bplus, MissingColors G sigma v = MissingColors G rho v) →
  c ∈ TreeMissingColors rho Bplus →
  HierarchyFirstMissingPosition sigma T c = HierarchyFirstMissingPosition rho T c := by
  classical
  intro V E _ _ G k e0 T Bplus hBplusTouter firstWitness rho sigma c helem hmiss hc
  let _ := Fintype.ofFinite V
  as_aux_lemma =>
    have hr := firstWitness rho c hc
    have hc' : c ∈ TreeMissingColors sigma Bplus := by
      obtain ⟨v, hv, hm⟩ := Finset.mem_biUnion.mp hc
      exact Finset.mem_biUnion.mpr ⟨v, hv, (hmiss v hv).symm ▸ hm⟩
    have hs := firstWitness sigma c hc'
    have pref (i : Fin (T.length + 1)) (hi : i.val ≤ Bplus.length) :
        T.vertex i ∈ TreeSequenceVertexSet Bplus := by
      let j : Fin (Bplus.length + 1) := ⟨i.val, Nat.lt_succ_of_le hi⟩
      have he : Fin.castLE (Nat.succ_le_succ hBplusTouter.1) j = i := Fin.ext rfl
      exact (@Finset.mem_image _ _ (Classical.decEq V)).mpr
        ⟨j, Finset.mem_univ _, (hBplusTouter.2.1 j).symm.trans (congrArg T.vertex he)⟩
    by_contra hne
    have hvne : T.vertex (HierarchyFirstMissingPosition sigma T c) ≠
        T.vertex (HierarchyFirstMissingPosition rho T c) :=
      fun he => hne (T.vertex_injective he)
    have hsOld := (hmiss _ (pref _ hs.2)) ▸ hs.1
    exact Finset.disjoint_left.mp (helem (pref _ hs.2) (pref _ hr.2) hvne) hsOld hr.1

theorem helper_firstFromMembership_1829.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E)
  (k : ℕ) (e0 : E) (T : TreeSequence G e0) (rho sigma : PartialEdgeColoring E k)
  (c : Fin k),
  (
  ∀ (v : V),
  c ∈ MissingColors G sigma v ↔ c ∈ MissingColors G rho v) →
  HierarchyFirstMissingPosition sigma T c = HierarchyFirstMissingPosition rho T c := by
  classical
  intro V E _ _ G k e0 T rho sigma c hc
  let _ := Fintype.ofFinite V
  as_aux_lemma =>
    have he : (Finset.univ.filter fun i : Fin (T.length + 1) =>
        c ∈ MissingColors G sigma (T.vertex i)) =
        (Finset.univ.filter fun i : Fin (T.length + 1) =>
          c ∈ MissingColors G rho (T.vertex i)) := by
      apply Finset.filter_congr
      intro i _
      exact hc _
    unfold HierarchyFirstMissingPosition
    rw [he]

theorem helper_hstoredFirst_1843.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
  let alpha : Fin k := D.alpha;
  let theta : Fin k := D.theta;
  let endIndex : Fin (T.length + (1 : ℕ)) := D.terminalVertexIndex;
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  ∀ (Bplus : TreeSequence G e0),
  ColoredVertexSetElementary G phi (TreeSequenceVertexSet Bplus) →
  theta ∈ TreeMissingColors phi A →
  alpha ∈ TreeMissingColors phi Bplus →
  let z : V ⊕ E := Sum.inl (T.vertex endIndex);
  let muOne : PartialEdgeColoring E k := TwoColorComponentSwap G phi theta alpha z;
  ((
  ∀ (v : V),
  Sum.inl v ∉ TwoColorComponent G phi theta alpha z →
  MissingColors G muOne v = MissingColors G phi v) ∧
      (
  ∀ (v : V),
  Sum.inl v ∈ TwoColorComponent G phi theta alpha z →
  theta ∈ MissingColors G phi v →
  alpha ∈ MissingColors G muOne v) ∧
        (
  ∀ (v : V),
  Sum.inl v ∈ TwoColorComponent G phi theta alpha z →
  alpha ∈ MissingColors G phi v →
  theta ∈ MissingColors G muOne v) ∧
  ∀ (v : V) (c : Fin k),
  c ≠ theta →
  c ≠ alpha →
  (c ∈ MissingColors G muOne v ↔ c ∈ MissingColors G phi v)) →
  (∀ v ∈ TreeSequenceVertexSet Bplus, MissingColors G muOne v = MissingColors G phi v) →
  (
  ∀ (rho sigma : PartialEdgeColoring E k) (c : Fin k),
  ColoredVertexSetElementary G rho (TreeSequenceVertexSet Bplus) →
  (∀ v ∈ TreeSequenceVertexSet Bplus,
      MissingColors G sigma v = MissingColors G rho v) →
  c ∈ TreeMissingColors rho Bplus →
  HierarchyFirstMissingPosition sigma T c =
    HierarchyFirstMissingPosition rho T c) →
  (
  ∀ (rho sigma : PartialEdgeColoring E k) (c : Fin k),
  (
  ∀ (v : V),
  c ∈ MissingColors G sigma v ↔ c ∈ MissingColors G rho v) →
  HierarchyFirstMissingPosition sigma T c = HierarchyFirstMissingPosition rho T c) →
  ∀ c ∈ HierarchyStoredColorsAt H q,
  HierarchyFirstMissingPosition muOne T c = HierarchyFirstMissingPosition phi T c := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D alpha theta endIndex H q A Bplus
      hElemOuter hthetaInA hAlphaMissingBplus z muOne behaviorOne hmissingPointwise
      firstPreserved firstFromMembership c hc
  have hct : c ≠ theta := by
    intro he
    have hs : theta ∈ HierarchyStoredColorsAt H q := he ▸ hc
    exact (Finset.mem_sdiff.mp hs).2 hthetaInA
  by_cases hca : c = alpha
  · exact hca.symm ▸ firstPreserved phi muOne alpha hElemOuter hmissingPointwise
      hAlphaMissingBplus
  · exact firstFromMembership phi muOne c (fun v => behaviorOne.2.2.2 v c hct hca)

theorem helper_hAlphaNoGamma_1854.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
  let alpha : Fin k := D.alpha;
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  alpha ∉ (HierarchyStoredColorsAt H q).biUnion (C.good.gamma q) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D alpha H q
  rcases D.normalizedAlternative with ⟨_, _, hnot⟩ | ⟨_, _, hnot⟩ | ⟨haStored, _⟩
  · exact hnot
  · exact hnot
  · intro hm
    exact Finset.disjoint_left.mp (GoodHierarchyReservedDisjoint C.good q).2 hm haStored

theorem helper_hgammaCutoff_1866.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
  let alpha : Fin k := D.alpha;
  let theta : Fin k := D.theta;
  let penIndex : Fin (T.length + (1 : ℕ)) := D.penultimateVertexIndex;
  let endIndex : Fin (T.length + (1 : ℕ)) := D.terminalVertexIndex;
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  ∀ (B Bplus : TreeSequence G e0),
  (↑penIndex : ℕ) + (1 : ℕ) = T.length →
  (↑endIndex : ℕ) = T.length →
  ∀ (eta : Fin k),
  B.length + (2 : ℕ) = T.length →
  Bplus.length + (1 : ℕ) = T.length →
  HierarchyFirstMissingPosition phi T eta = penIndex →
  alpha ∉ (HierarchyStoredColorsAt H q).biUnion (C.good.gamma q) →
  (∀ c ∈ HierarchyStoredColorsAt H q,
  theta ∈ C.good.gamma q c →
  c = eta) →
  ∀ c ∈ HierarchyStoredColorsAt H q,
  alpha ∈ C.good.gamma q c ∨ theta ∈ C.good.gamma q c →
  (↑(HierarchyFirstMissingPosition phi T c) : ℕ) ≤ Bplus.length := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D alpha theta penIndex endIndex H q B Bplus
      penPosition endPosition eta hBLouter hPLouter hetaFirst hAlphaNoGamma hthetaOwner c hc hp
  rcases hp with ha | ht
  · exact False.elim (hAlphaNoGamma (Finset.mem_biUnion.mpr ⟨c, hc, ha⟩))
  · have he := hthetaOwner c hc ht
    rw [he, hetaFirst]
    have hp := penPosition
    have hb := hPLouter
    omega

theorem helper_hsuffixPhi_1881.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
  let theta : Fin k := D.theta;
  let lastIndex : Fin T.length := D.lastEdgeIndex;
  ∀ (Bplus : TreeSequence G e0),
  phi (T.edge lastIndex) = some theta →
  (↑lastIndex : ℕ) + (1 : ℕ) = T.length →
  Bplus.length + (1 : ℕ) = T.length →
  TreeSequenceInitialSegment Bplus T →
  theta ∈ TreeMissingColors phi Bplus →
  TashkinovAugmentationSequence phi Bplus T := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D theta lastIndex Bplus lastColor
      lastPosition hPLouter hBplusTouter hthetaMissingBplus
  apply Relation.ReflTransGen.single
  refine ⟨hPLouter.symm, hBplusTouter, theta, ?_, hthetaMissingBplus⟩
  have hi : Fin.cast hPLouter (Fin.last Bplus.length) = lastIndex :=
    Fin.ext (by
      have hl := lastPosition
      simp only [Fin.val_cast, Fin.val_last]
      clear * - hl hPLouter
      omega)
  rw [hi]
  exact lastColor

theorem helper_prefixOne_1931.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
  let alpha : Fin k := D.alpha;
  let theta : Fin k := D.theta;
  let endIndex : Fin (T.length + (1 : ℕ)) := D.terminalVertexIndex;
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let ell : ℕ := HierarchyFullTailLength C;
  ∀ (Bplus : TreeSequence G e0),
  Bplus = HierarchyFullTailPrefix C (ell - (1 : ℕ)) →
  let z : V ⊕ E := Sum.inl (T.vertex endIndex);
  let muOne : PartialEdgeColoring E k := TwoColorComponentSwap G phi theta alpha z;
  ∀ (corrOne : CorrespondingExtendedTashkinovTree G k e0 ett muOne T)
    (baseOne : HierarchyBase corrOne.replacementETT muOne)
    (COne : HierarchyCounterexample baseOne),
  let HOne : TashkinovHierarchy corrOne.replacementETT baseOne := COne.hierarchy;
  let qOne : Fin (HOne.dividerCount + (1 : ℕ)) := Fin.last HOne.dividerCount;
  HierarchyStarredStage HOne qOne = A →
  HierarchyFullTailPrefix COne (HierarchyFullTailLength COne - (1 : ℕ)) = Bplus := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D alpha theta endIndex H q A ell Bplus
      hBplusDef z muOne corrOne baseOne COne HOne qOne starOne
  unfold HierarchyFullTailPrefix HierarchyFullTailLength
  change TreeSequencePrefix T
    (min ((HierarchyStarredStage HOne qOne).length +
      (T.length - (HierarchyStarredStage HOne qOne).length - 1)) T.length) _ _ = Bplus
  simp only [starOne]
  exact hBplusDef.symm

theorem helper_thetaUnusedOne_1963.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
  let alpha : Fin k := D.alpha;
  let theta : Fin k := D.theta;
  let lastIndex : Fin T.length := D.lastEdgeIndex;
  let endIndex : Fin (T.length + (1 : ℕ)) := D.terminalVertexIndex;
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  ∀ (Bplus : TreeSequence G e0),
  (↑lastIndex : ℕ) + (1 : ℕ) = T.length →
  Bplus.length + (1 : ℕ) = T.length →
  (
  ∀ (t : Fin T.length),
  A.length ≤ (↑t : ℕ) →
  (↑t : ℕ) < Bplus.length →
  phi (T.edge t) ≠ some theta) →
  theta ≠ alpha →
  let z : V ⊕ E := Sum.inl (T.vertex endIndex);
  let muOne : PartialEdgeColoring E k := TwoColorComponentSwap G phi theta alpha z;
  (
  ∀ (t : Fin T.length),
  A.length ≤ (↑t : ℕ) →
  (↑t : ℕ) < Bplus.length →
  muOne (T.edge t) = phi (T.edge t)) →
  muOne (T.edge lastIndex) = some alpha →
  ∀ (t : Fin T.length),
  A.length ≤ (↑t : ℕ) →
  muOne (T.edge t) ≠ some theta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D alpha theta lastIndex endIndex H q A
      Bplus lastPosition hPLouter thetaAvoidsSplit hthetaAlphaNe z muOne hfixedSplit hlastOne t ht
  by_cases hb : t.val < Bplus.length
  · rw [hfixedSplit t ht hb]
    exact thetaAvoidsSplit t ht hb
  · have he : t = lastIndex := by
      apply Fin.ext
      have hl := lastPosition
      have hp := hPLouter
      have htlt := t.isLt
      clear * - hl hp htlt hb
      omega
    rw [he, hlastOne]
    exact fun h => hthetaAlphaNe (Option.some.inj h).symm

theorem helper_tnOne_1991.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
  let alpha : Fin k := D.alpha;
  let theta : Fin k := D.theta;
  let endIndex : Fin (T.length + (1 : ℕ)) := D.terminalVertexIndex;
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
  let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
  let z : V ⊕ E := Sum.inl (T.vertex endIndex);
  let muOne : PartialEdgeColoring E k := TwoColorComponentSwap G phi theta alpha z;
  ∀ (corrOne : CorrespondingExtendedTashkinovTree G k e0 ett muOne T)
    (baseOne : HierarchyBase corrOne.replacementETT muOne)
    (COne : HierarchyCounterexample baseOne),
  SameGoodHierarchy C.good COne.good →
  let HOne : TashkinovHierarchy corrOne.replacementETT baseOne := COne.hierarchy;
  H.dividerCount = HOne.dividerCount →
  corrOne.replacementETT.series.data.tree
      (Fin.last corrOne.replacementETT.rounds).castSucc =
    Tn := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D alpha theta endIndex H n Tn z muOne
      corrOne baseOne COne sameOne HOne countOne
  have hs : H.stage 0 = HOne.stage 0 := by
    have hs :=
      (Fin.heq_fun_iff (congrArg (fun d => d + 2) countOne)).mp sameOne.1.2.2.1 0
    exact hs.trans (congrArg HOne.stage (Fin.ext (by simp)))
  exact HOne.baseStage.symm.trans (hs.symm.trans H.baseStage)

theorem helper_positiveStarOne_2005.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
  [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
  (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
  (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
  (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
  let alpha : Fin k := D.alpha;
  let theta : Fin k := D.theta;
  let endIndex : Fin (T.length + (1 : ℕ)) := D.terminalVertexIndex;
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  ∀ (_ _ : TreeSequence G e0) (_ : Fin k),
  let z : V ⊕ E := Sum.inl (T.vertex endIndex);
  let muOne : PartialEdgeColoring E k := TwoColorComponentSwap G phi theta alpha z;
  ∀ (corrOne : CorrespondingExtendedTashkinovTree G k e0 ett muOne T)
    (baseOne : HierarchyBase corrOne.replacementETT muOne)
    (COne : HierarchyCounterexample baseOne),
  let HOne : TashkinovHierarchy corrOne.replacementETT baseOne := COne.hierarchy;
  let qOne : Fin (HOne.dividerCount + (1 : ℕ)) := Fin.last HOne.dividerCount;
  HierarchyStarredStage HOne qOne = A →
  H.dividerCount = HOne.dividerCount →
  HOne.dividerCount ≠ (0 : ℕ) →
  HOne.stage
      (⟨HOne.dividerCount,
          by
          have := CorrespondingExtendedTashkinovTree.rungAgreement corrOne
          have := TreeSequence.positive T
          omega⟩ :
        Fin (HOne.dividerCount + (2 : ℕ))) =
    A := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D alpha theta endIndex H q A B Bplus eta z
      muOne corrOne baseOne COne HOne qOne starOne countOne hz
  have hi : qOne = (⟨HOne.dividerCount - 1, by omega⟩ : Fin HOne.dividerCount).succ :=
    Fin.ext (by simp only [qOne, Fin.val_last, Fin.val_succ]; omega)
  have hs := starOne
  rw [hi] at hs
  change HOne.stage _ = A at hs
  convert hs using 1
  apply congrArg HOne.stage
  apply Fin.ext
  simp only [Fin.val_succ, Fin.val_castSucc]
  omega

theorem helper_caseTwo_2017.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
  [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
  (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
  (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
  (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
  let alpha : Fin k := D.alpha;
  let theta : Fin k := D.theta;
  let endIndex : Fin (T.length + (1 : ℕ)) := D.terminalVertexIndex;
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  ∀ (Bplus : TreeSequence G e0) (eta : Fin k),
  TreeSequenceInitialSegment A Bplus →
  theta ∈ TreeMissingColors phi A →
  let z : V ⊕ E := Sum.inl (T.vertex endIndex);
  let muOne : PartialEdgeColoring E k := TwoColorComponentSwap G phi theta alpha z;
  ∀ (corrOne : CorrespondingExtendedTashkinovTree G k e0 ett muOne T)
    (baseOne : HierarchyBase corrOne.replacementETT muOne)
    (COne : HierarchyCounterexample baseOne),
  let HOne : TashkinovHierarchy corrOne.replacementETT baseOne := COne.hierarchy;
  let qOne : Fin (HOne.dividerCount + (1 : ℕ)) := Fin.last HOne.dividerCount;
  (
  ∀ (X : TreeSequence G e0),
  TreeSequenceInitialSegment X Bplus →
  TreeMissingColors muOne X = TreeMissingColors phi X) →
  (
  HOne.dividerCount = (0 : ℕ) →
  theta ∈
    TreeMissingColors muOne
      (corrOne.replacementETT.series.data.tree
        (Fin.last corrOne.replacementETT.rounds).castSucc)) →
  (
  HOne.dividerCount ≠ (0 : ℕ) →
  HOne.stage
      (⟨HOne.dividerCount,
          by
          have :=
            CorrespondingExtendedTashkinovTree.rungAgreement corrOne
          have := TreeSequence.positive T
          omega⟩ :
        Fin (HOne.dividerCount + (2 : ℕ))) =
    A) →
  (0 : ℕ) < HOne.dividerCount ∧
      theta ∈
        TreeMissingColors muOne
          (HOne.stage
            (⟨HOne.dividerCount,
                by
                have :=
                  CorrespondingExtendedTashkinovTree.rungAgreement corrOne
                have := TreeSequence.positive T
                omega⟩ :
              Fin (HOne.dividerCount + (2 : ℕ)))) ∨
    HOne.dividerCount = (0 : ℕ) ∧
      (theta ∈
          TreeMissingColors muOne
            (corrOne.replacementETT.series.data.tree
              (Fin.last corrOne.replacementETT.rounds).castSucc) ∨
        theta ∈ TreeMissingColors muOne (HierarchyStarredStage HOne qOne) ∧
          theta ∉
              TashkinovStoredColors corrOne.replacementETT.series.data
                (Fin.last corrOne.replacementETT.rounds) ∧
            eta ∉
              TashkinovStoredColors corrOne.replacementETT.series.data
                (Fin.last corrOne.replacementETT.rounds)) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D alpha theta endIndex H q A Bplus eta
      hABplusouter hthetaInA z muOne corrOne baseOne COne HOne qOne missingPrefixOne thetaTnOne
      positiveStarOne
  by_cases hz : HOne.dividerCount = 0
  · exact Or.inr ⟨hz, Or.inl (thetaTnOne hz)⟩
  · exact Or.inl ⟨Nat.pos_of_ne_zero hz, by
      rw [positiveStarOne hz, missingPrefixOne A hABplusouter]
      exact hthetaInA⟩

theorem helper_orderedTwo_2037.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
  let alpha : Fin k := D.alpha;
  let theta : Fin k := D.theta;
  let penIndex : Fin (T.length + (1 : ℕ)) := D.penultimateVertexIndex;
  let endIndex : Fin (T.length + (1 : ℕ)) := D.terminalVertexIndex;
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let ell : ℕ := HierarchyFullTailLength C;
  (↑penIndex : ℕ) + (1 : ℕ) = T.length →
  ∀ (eta : Fin k),
  (2 : ℕ) ≤ ell →
  ell = T.length - A.length →
  (↑(HierarchyFirstMissingPosition phi T theta) : ℕ) ≤ A.length →
  let z : V ⊕ E := Sum.inl (T.vertex endIndex);
  let muOne : PartialEdgeColoring E k := TwoColorComponentSwap G phi theta alpha z;
  ∀ (corrOne : CorrespondingExtendedTashkinovTree G k e0 ett muOne T)
    (baseOne : HierarchyBase corrOne.replacementETT muOne)
    (COne : HierarchyCounterexample baseOne),
  let HOne : TashkinovHierarchy corrOne.replacementETT baseOne := COne.hierarchy;
  let qOne : Fin (HOne.dividerCount + (1 : ℕ)) := Fin.last HOne.dividerCount;
  HierarchyStarredStage HOne qOne = A →
  HierarchyFirstMissingPosition muOne T theta =
      HierarchyFirstMissingPosition phi T theta →
  HierarchyFirstMissingPosition muOne T eta = penIndex →
  (
  ∀ (t : Fin T.length),
  A.length ≤ (↑t : ℕ) →
  muOne (T.edge t) ≠ some theta) →
  theta ∉ TreeMissingColors muOne (HierarchyStarredStage HOne qOne) ∨
      eta ∉ TreeMissingColors muOne (HierarchyStarredStage HOne qOne) →
  TreeVertexOrder T (T.vertex (HierarchyFirstMissingPosition muOne T theta))
      (T.vertex (HierarchyFirstMissingPosition muOne T eta)) ∧
    theta ∉
      ({c : Fin k |
          ∃ (t : Fin T.length),
            (HierarchyStarredStage HOne qOne).length ≤ (↑t : ℕ) ∧
              (↑t : ℕ) < (↑(HierarchyFirstMissingPosition muOne T eta) : ℕ) ∧
                muOne (T.edge t) = some c} :
        Finset (Fin k)) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D alpha theta penIndex endIndex H q A ell
      penPosition eta hTailAtLeast hellOuter hthetaFirstBound z muOne corrOne baseOne COne HOne
      qOne starOne firstThetaOne firstEtaOne thetaUnusedOne _
  rw [firstThetaOne, firstEtaOne, starOne]
  refine ⟨⟨_, _, rfl, rfl, ?_⟩, ?_⟩
  · have hb := hthetaFirstBound
    have hp := penPosition
    have hl := hTailAtLeast
    have hell := hellOuter
    clear * - hb hp hl hell
    omega
  · intro hc
    obtain ⟨t, ht, _, he⟩ := (Finset.mem_filter.mp hc).2
    exact thetaUnusedOne t ht he

theorem helper_componentEqTwo_2072.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
  [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
  (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
  (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
  (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
  let alpha : Fin k := D.alpha;
  let theta : Fin k := D.theta;
  let penIndex : Fin (T.length + (1 : ℕ)) := D.penultimateVertexIndex;
  let endIndex : Fin (T.length + (1 : ℕ)) := D.terminalVertexIndex;
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  ∀ (Bplus : TreeSequence G e0) (eta : Fin k),
  TreeSequenceInitialSegment A Bplus →
  theta ∈ TreeMissingColors phi A →
  let z : V ⊕ E := Sum.inl (T.vertex endIndex);
  let muOne : PartialEdgeColoring E k := TwoColorComponentSwap G phi theta alpha z;
  ∀ (corrOne : CorrespondingExtendedTashkinovTree G k e0 ett muOne T)
    (baseOne : HierarchyBase corrOne.replacementETT muOne)
    (COne : HierarchyCounterexample baseOne),
  let HOne : TashkinovHierarchy corrOne.replacementETT baseOne := COne.hierarchy;
  (
  ∀ (X : TreeSequence G e0),
  TreeSequenceInitialSegment X Bplus →
  TreeMissingColors muOne X = TreeMissingColors phi X) →
  HierarchyFirstMissingPosition muOne T theta =
      HierarchyFirstMissingPosition phi T theta →
  HierarchyFirstMissingPosition muOne T eta = penIndex →
  (
  HOne.dividerCount = (0 : ℕ) →
  theta ∈
    TreeMissingColors muOne
      (corrOne.replacementETT.series.data.tree
        (Fin.last corrOne.replacementETT.rounds).castSucc)) →
  (
  HOne.dividerCount ≠ (0 : ℕ) →
  HOne.stage
      (⟨HOne.dividerCount,
          by
          have :=
            CorrespondingExtendedTashkinovTree.rungAgreement corrOne
          have := TreeSequence.positive T
          omega⟩ :
        Fin (HOne.dividerCount + (2 : ℕ))) =
    A) →
  (
  let H : TashkinovHierarchy corrOne.replacementETT baseOne := COne.hierarchy;
  have q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  have n : Fin (corrOne.replacementETT.rounds + (1 : ℕ)) :=
    Fin.last corrOne.replacementETT.rounds;
  have A : TreeSequence G e0 := HierarchyStarredStage H q;
  have Tnq : TreeSequence G e0 :=
    H.stage
      (⟨H.dividerCount,
          by
          have :=
            CorrespondingExtendedTashkinovTree.rungAgreement corrOne
          have := TreeSequence.positive T
          omega⟩ :
        Fin (H.dividerCount + (2 : ℕ)));
  have Tn : TreeSequence G e0 := corrOne.replacementETT.series.data.tree n.castSucc;
  have Dn : Finset (Fin k) :=
    TashkinovStoredColors corrOne.replacementETT.series.data n;
  have Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q;
  have va : V := T.vertex (HierarchyFirstMissingPosition muOne T theta);
  have vb : V := T.vertex (HierarchyFirstMissingPosition muOne T eta);
  have sameComponent : Prop :=
    TwoColorComponent G muOne theta eta (Sum.inl va) =
      TwoColorComponent G muOne theta eta (Sum.inl vb);
  (
  (0 : ℕ) < H.dividerCount ∧
       (theta ∈ TreeMissingColors muOne Tnq ∨
         Disjoint (insert theta ({ eta } : Finset (Fin k)) : Finset (Fin k)) Dnq) →
  sameComponent) ∧
        (
  H.dividerCount = (0 : ℕ) ∧
       (theta ∈ TreeMissingColors muOne Tn ∨
         Disjoint (insert theta ({ eta } : Finset (Fin k)) : Finset (Fin k)) Dn) →
  sameComponent) ∧
          (
  theta ∈ TreeMissingColors muOne A ∧
     TreeColorSetClosed G muOne A ({ theta } : Finset (Fin k)) →
  sameComponent ∧ TreeInterchangeable G A muOne theta eta)) →
  TwoColorComponent G muOne theta eta
      (Sum.inl (T.vertex (HierarchyFirstMissingPosition phi T theta))) =
    TwoColorComponent G muOne theta eta (Sum.inl (T.vertex penIndex)) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D alpha theta penIndex endIndex H q A Bplus
      eta hABplusouter hthetaInA z muOne corrOne baseOne COne HOne missingPrefixOne firstThetaOne
      firstEtaOne thetaTnOne positiveStarOne changeTwo
  rw [← firstThetaOne, ← firstEtaOne]
  by_cases hz : HOne.dividerCount = 0
  · exact changeTwo.2.1 ⟨hz, Or.inl (thetaTnOne hz)⟩
  · exact changeTwo.1 ⟨Nat.pos_of_ne_zero hz, Or.inl (by
      rw [positiveStarOne hz, missingPrefixOne A hABplusouter]
      exact hthetaInA)⟩

theorem helper_thetaPenultimateNe_2082.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
  let theta : Fin k := D.theta;
  let penIndex : Fin (T.length + (1 : ℕ)) := D.penultimateVertexIndex;
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let ell : ℕ := HierarchyFullTailLength C;
  (↑penIndex : ℕ) + (1 : ℕ) = T.length →
  (2 : ℕ) ≤ ell →
  ell = T.length - A.length →
  (↑(HierarchyFirstMissingPosition phi T theta) : ℕ) ≤ A.length →
  T.vertex (HierarchyFirstMissingPosition phi T theta) ≠ T.vertex penIndex := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D theta penIndex H q A ell penPosition
      hTailAtLeast hellOuter hthetaFirstBound he
  have hv := congrArg Fin.val (T.vertex_injective he)
  have hb := hthetaFirstBound
  have hp := penPosition
  have ht := hTailAtLeast
  have hell := hellOuter
  clear * - hv hb hp ht hell
  omega

theorem helper_penultimateTerminalNe_2092.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
  let penIndex : Fin (T.length + (1 : ℕ)) := D.penultimateVertexIndex;
  let endIndex : Fin (T.length + (1 : ℕ)) := D.terminalVertexIndex;
  (↑penIndex : ℕ) + (1 : ℕ) = T.length →
  (↑endIndex : ℕ) = T.length →
  T.vertex penIndex ≠ T.vertex endIndex := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D penIndex endIndex penPosition endPosition he
  have hv := congrArg Fin.val (T.vertex_injective he)
  have hp := penPosition
  have ht := endPosition
  clear * - hv hp ht
  omega

theorem helper_hv_2145.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
  let penIndex : Fin (T.length + (1 : ℕ)) := D.penultimateVertexIndex;
  ∀ (Bplus : TreeSequence G e0),
  (↑penIndex : ℕ) + (1 : ℕ) = T.length →
  Bplus.length + (1 : ℕ) = T.length →
  TreeSequenceInitialSegment Bplus T →
  Bplus.vertex (Fin.last Bplus.length) = T.vertex penIndex := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D penIndex Bplus penPosition hPLouter
      hBplusTouter
  rw [← hBplusTouter.2.1 (Fin.last Bplus.length)]
  apply congrArg T.vertex
  apply Fin.ext
  have hp := penPosition
  have hb := hPLouter
  simp only [Fin.val_castLE, Fin.val_last]
  clear * - hp hb
  omega

/-- Dependent contract shared by the hierarchy construction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperFixedTailTwo2168Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base)
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
   (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
  let alpha : Fin k := D.alpha;
  let theta : Fin k := D.theta;
  let lastIndex : Fin T.length := D.lastEdgeIndex;
  let penIndex : Fin (T.length + (1 : ℕ)) := D.penultimateVertexIndex;
  let endIndex : Fin (T.length + (1 : ℕ)) := D.terminalVertexIndex;
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let ell : ℕ := HierarchyFullTailLength C;
  ∀ (B Bplus : TreeSequence G e0),
  let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
  let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
  (↑lastIndex : ℕ) + (1 : ℕ) = T.length →
  (↑penIndex : ℕ) + (1 : ℕ) = T.length →
  (↑endIndex : ℕ) = T.length →
  ∀ (eta : Fin k),
  ell = T.length - A.length →
  B.length + (2 : ℕ) = T.length →
  Bplus.length + (1 : ℕ) = T.length →
  TreeSequenceInitialSegment Bplus T →
  TreeSequenceInitialSegment A T →
  (
  ∀ (X : TreeSequence G e0) (i : Fin (X.length + (1 : ℕ))),
  X.vertex i ∈ TreeSequenceVertexSet X) →
  alpha ≠ eta →
  HierarchyFirstMissingPosition phi T eta = penIndex →
  let z : V ⊕ E := Sum.inl (T.vertex endIndex);
  let muOne : PartialEdgeColoring E k := TwoColorComponentSwap G phi theta alpha z;
  (
  ∀ (t : Fin T.length),
  A.length ≤ (↑t : ℕ) →
  (↑t : ℕ) < Bplus.length →
  muOne (T.edge t) = phi (T.edge t)) →
  muOne (T.edge lastIndex) = some alpha →
  (
  H.dividerCount = (0 : ℕ) →
  A = base.core) →
  ∀ (corrOne : CorrespondingExtendedTashkinovTree G k e0 ett muOne T)
   (baseOne : HierarchyBase corrOne.replacementETT muOne)
   (COne : HierarchyCounterexample baseOne),
  let HOne : TashkinovHierarchy corrOne.replacementETT baseOne := COne.hierarchy;
  H.dividerCount = HOne.dividerCount →
  HierarchyFirstMissingPosition muOne T eta = penIndex →
  (
  ∀ (t : Fin T.length),
  A.length ≤ (↑t : ℕ) →
  muOne (T.edge t) ≠ some theta) →
  corrOne.replacementETT.series.data.tree
     (Fin.last corrOne.replacementETT.rounds).castSucc =
    Tn →
  let muTwo : PartialEdgeColoring E k :=
   TwoColorComponentSwap G muOne theta eta z;
  (
  let H : TashkinovHierarchy corrOne.replacementETT baseOne :=
   COne.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  have n : Fin (corrOne.replacementETT.rounds + (1 : ℕ)) :=
   Fin.last corrOne.replacementETT.rounds;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  have Tnq : TreeSequence G e0 :=
   H.stage
    (⟨H.dividerCount,
      by
      have := CorrespondingExtendedTashkinovTree.rungAgreement corrOne
      have := TreeSequence.positive T
      omega⟩ :
     Fin (H.dividerCount + (2 : ℕ)));
  have Tn : TreeSequence G e0 :=
   corrOne.replacementETT.series.data.tree n.castSucc;
  have Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q;
  HierarchyWeaklyStable H q muTwo ∧
      ModColoring corrOne.replacementETT muTwo ∧
       (A = Tn ∨
         ∃ (inputA : PartialEdgeColoring E k) (ettA :
          ExtendedTashkinovTree G k e0 inputA A muTwo), MaximumProperty ettA) ∧
        (
    (0 : ℕ) < H.dividerCount →
    ∃ (inputA : PartialEdgeColoring E k) (ettA :
            ExtendedTashkinovTree G k e0 inputA A muTwo) (baseA :
            HierarchyBase ettA muTwo) (K : TashkinovHierarchy ettA baseA) (goodA :
            GoodHierarchy K),
            MaximumProperty ettA ∧
             ettA.series.data.kind (Fin.last ettA.rounds) =
               corrOne.replacementETT.series.data.kind
                (Fin.last corrOne.replacementETT.rounds) ∧
              ∃ (hcount : K.dividerCount + (1 : ℕ) = H.dividerCount),
               baseA.core = baseOne.core ∧
                baseA.closure = baseOne.closure ∧
                 (
    ∀ (j : Fin (K.dividerCount + (2 : ℕ))),
    K.stage j =
     H.stage
      (⟨(↑j : ℕ),
        by
        have :=
         CorrespondingExtendedTashkinovTree.rungAgreement corrOne
        have := TreeSequence.positive T
        omega⟩ :
       Fin (H.dividerCount + (2 : ℕ)))) ∧
                  (
    ∀ (j : Fin (K.dividerCount + (1 : ℕ))),
    have jH : Fin (H.dividerCount + (1 : ℕ)) :=
     (⟨(↑j : ℕ),
       by
       have :=
        CorrespondingExtendedTashkinovTree.rungAgreement corrOne
       have := TreeSequence.positive T
       omega⟩ :
      Fin (H.dividerCount + (1 : ℕ)));
    HierarchyStoredColorsAt K j = HierarchyStoredColorsAt H jH ∧
     ∀ eta ∈ HierarchyStoredColorsAt K j,
      goodA.gamma j eta = COne.good.gamma jH eta) ∧
                   TreeColorSetMinusClosed G muTwo Tnq
                    (Dnq.biUnion
                     (COne.good.gamma
                      (⟨COne.hierarchy.dividerCount - (1 : ℕ),
                        by
                        have :=
                         CorrespondingExtendedTashkinovTree.rungAgreement corrOne
                        have := TreeSequence.positive T
                        omega⟩ :
                       Fin (COne.hierarchy.dividerCount + (1 : ℕ))))))) →
  (
  ∀ (t : Fin Bplus.length),
  A.length ≤ (↑t : ℕ) →
  (↑t : ℕ) < A.length + (ell - (1 : ℕ)) →
  phi (Bplus.edge t) = some eta →
  H.dividerCount = (0 : ℕ) ∧
   base.core = Tn ∧
    (↑t : ℕ) = A.length ∧
     ∃ (f : E),
      TashkinovSeriesStep G k ett.rounds e0 input ett.series.data n ∧
       (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
         ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
        ett.series.data.connectingEdges n = ({ f } : Finset E) ∧
         Bplus.edge t = f ∧
          phi f = some eta ∧
           eta ∈ TashkinovStoredColors ett.series.data n) →
  ∀ (t : Fin T.length),
  A.length ≤ (↑t : ℕ) →
  muTwo (T.edge t) = muOne (T.edge t)

theorem helper_fixedTailTwo_2168.{u_1, u_2} :
    helperFixedTailTwo2168Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D alpha theta lastIndex penIndex endIndex H
      q A ell B Bplus n Tn lastPosition penPosition endPosition eta hellOuter hBLouter hPLouter
      hBplusTouter hATouter vertexMemOuter hAlphaEtaNe hetaFirst z muOne hfixedSplit hlastOne
      lastZero corrOne baseOne COne HOne countOne firstEtaOne thetaUnusedOne tnOne muTwo
      stableTwo exclusionEta' t ht
  have hnt := thetaUnusedOne t ht
  by_cases heta : muOne (T.edge t) = some eta
  · have hb : t.val < Bplus.length := by
      by_contra hnot
      have he : t = lastIndex := by
        apply Fin.ext
        have hl := lastPosition
        have hp := hPLouter
        have htlt := t.isLt
        clear * - hl hp htlt hnot
        omega
      rw [he, hlastOne] at heta
      exact hAlphaEtaNe (Option.some.inj heta)
    let tB : Fin Bplus.length := ⟨t.val, hb⟩
    have hcast : Fin.castLE hBplusTouter.1 tB = t := Fin.ext rfl
    have heOld : phi (Bplus.edge tB) = some eta := by
      rw [← hBplusTouter.2.2 tB, hcast, ← hfixedSplit t ht hb]
      exact heta
    obtain ⟨hz, hcore, hpos, f, _, _, _, _, _, hs⟩ :=
      exclusionEta' tB ht (by
        have hv := tB.isLt
        have hp := hPLouter
        have hell := hellOuter
        clear * - hv hp hell
        change tB.val < Bplus.length at hv
        omega) heOld
    have hzOne : HOne.dividerCount = 0 := countOne.symm.trans hz
    have htn : corrOne.replacementETT.series.data.tree
        (Fin.last corrOne.replacementETT.rounds).castSucc = A :=
      tnOne.trans ((lastZero hz).trans hcore).symm
    have hinc : TreeIncidentEdge
        (corrOne.replacementETT.series.data.tree (Fin.last
            corrOne.replacementETT.rounds).castSucc)
        (T.edge t) := by
      rw [htn]
      obtain ⟨i, hi⟩ := T.attaches t
      let j : Fin (A.length + 1) :=
        ⟨i.val, by
          have := i.isLt
          change t.val = A.length at hpos
          omega⟩
      have he : Fin.castLE (Nat.succ_le_succ hATouter.1) j =
          Fin.castLE (by omega : t.val + 1 ≤ T.length + 1) i := Fin.ext rfl
      refine ⟨A.vertex j, vertexMemOuter A j, ?_⟩
      rw [← hATouter.2.1 j, he, Incident, hi]
      exact Sym2.mem_mk_right _ _
    have hsOne : eta ∈ TashkinovStoredColors corrOne.replacementETT.series.data
        (Fin.last corrOne.replacementETT.rounds) := by
      rw [P2752_T2_TerminalStoredColors ett corrOne]
      exact hs
    have hw := stableTwo.1
    have hi : (Fin.last HOne.dividerCount : Fin (HOne.dividerCount + 1)) = 0 :=
      Fin.ext hzOne
    rw [hi] at hw
    change (if corrOne.replacementETT.series.data.kind (Fin.last corrOne.replacementETT.rounds) =
      some TashkinovExtensionKind.PE then _ else _) at hw
    have stableSeed : StableColoring
        (corrOne.replacementETT.series.data.tree (Fin.last
            corrOne.replacementETT.rounds).castSucc)
        (TashkinovStoredColors corrOne.replacementETT.series.data (Fin.last
            corrOne.replacementETT.rounds))
        muOne muTwo := by
      split_ifs at hw with hp
      · exact hw.1
      · exact hw
    exact stableSeed.1 _ hinc ⟨eta, Finset.mem_union_right _ hsOne, heta⟩
  · simp only [muTwo, TwoColorComponentSwap, hnt, heta, ite_false, ite_self]

theorem helper_storedFirstTwo_2236.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
  let alpha : Fin k := D.alpha;
  let theta : Fin k := D.theta;
  let endIndex : Fin (T.length + (1 : ℕ)) := D.terminalVertexIndex;
  ∀ (Bplus : TreeSequence G e0) (eta : Fin k),
  let z : V ⊕ E := Sum.inl (T.vertex endIndex);
  let muOne : PartialEdgeColoring E k := TwoColorComponentSwap G phi theta alpha z;
  (
  ∀ (rho sigma : PartialEdgeColoring E k) (c : Fin k),
  ColoredVertexSetElementary G rho (TreeSequenceVertexSet Bplus) →
  (∀ v ∈ TreeSequenceVertexSet Bplus,
      MissingColors G sigma v = MissingColors G rho v) →
  c ∈ TreeMissingColors rho Bplus →
  HierarchyFirstMissingPosition sigma T c =
    HierarchyFirstMissingPosition rho T c) →
  (
  ∀ (rho sigma : PartialEdgeColoring E k) (c : Fin k),
  (
  ∀ (v : V),
  c ∈ MissingColors G sigma v ↔ c ∈ MissingColors G rho v) →
  HierarchyFirstMissingPosition sigma T c = HierarchyFirstMissingPosition rho T c) →
  ∀ (corrOne : CorrespondingExtendedTashkinovTree G k e0 ett muOne T)
    (baseOne : HierarchyBase corrOne.replacementETT muOne)
    (COne : HierarchyCounterexample baseOne),
  let HOne : TashkinovHierarchy corrOne.replacementETT baseOne := COne.hierarchy;
  let qOne : Fin (HOne.dividerCount + (1 : ℕ)) := Fin.last HOne.dividerCount;
  ColoredVertexSetElementary G muOne (TreeSequenceVertexSet Bplus) →
  theta ∉ HierarchyStoredColorsAt HOne qOne →
  eta ∈ TreeMissingColors muOne Bplus →
  let muTwo : PartialEdgeColoring E k := TwoColorComponentSwap G muOne theta eta z;
  (∀ v ∈ TreeSequenceVertexSet Bplus, MissingColors G muTwo v = MissingColors G muOne v) →
  (
  have C : Set (V ⊕ E) := TwoColorComponent G muOne theta eta z;
  have phi' : PartialEdgeColoring E k := TwoColorComponentSwap G muOne theta eta z;
  (
  ∀ (v : V),
  Sum.inl v ∉ C →
  MissingColors G phi' v = MissingColors G muOne v) ∧
        (
  ∀ (v : V),
  Sum.inl v ∈ C →
  theta ∈ MissingColors G muOne v →
  eta ∈ MissingColors G phi' v) ∧
          (
  ∀ (v : V),
  Sum.inl v ∈ C →
  eta ∈ MissingColors G muOne v →
  theta ∈ MissingColors G phi' v) ∧
  ∀ (v : V) (c : Fin k),
  c ≠ theta →
  c ≠ eta →
  (c ∈ MissingColors G phi' v ↔ c ∈ MissingColors G muOne v)) →
  ∀ c ∈ HierarchyStoredColorsAt HOne qOne,
  HierarchyFirstMissingPosition muTwo T c = HierarchyFirstMissingPosition muOne T c := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D alpha theta endIndex Bplus eta z muOne
      firstPreserved firstFromMembership corrOne baseOne COne HOne qOne elemOne thetaStoredOne
      etaMissingPrefixOne muTwo missingTwo behaviorTwo c hc
  have hct : c ≠ theta := fun he => thetaStoredOne (he ▸ hc)
  by_cases hce : c = eta
  · exact hce.symm ▸ firstPreserved muOne muTwo eta elemOne missingTwo etaMissingPrefixOne
  · exact firstFromMembership muOne muTwo c (fun v => behaviorTwo.2.2.2 v c hct hce)

theorem helper_lastTailBound_2256.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
  let lastIndex : Fin T.length := D.lastEdgeIndex;
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let ell : ℕ := HierarchyFullTailLength C;
  (↑lastIndex : ℕ) + (1 : ℕ) = T.length →
  (2 : ℕ) ≤ ell →
  ell = T.length - A.length →
  A.length ≤ (↑lastIndex : ℕ) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D lastIndex H q A ell lastPosition
      hTailAtLeast hellOuter
  have ht := hTailAtLeast
  have hell := hellOuter
  have hl := lastPosition
  clear * - ht hell hl
  omega

theorem helper_alphaPresentPenultimate_2279.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
  let alpha : Fin k := D.alpha;
  let penIndex : Fin (T.length + (1 : ℕ)) := D.penultimateVertexIndex;
  ∀ (B Bplus : TreeSequence G e0),
  (↑penIndex : ℕ) + (1 : ℕ) = T.length →
  B.length + (2 : ℕ) = T.length →
  ColoredVertexSetElementary G phi (TreeSequenceVertexSet Bplus) →
  T.vertex penIndex ∈ TreeSequenceVertexSet Bplus →
  (↑(HierarchyFirstMissingPosition phi T alpha) : ℕ) ≤ B.length →
  alpha ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T alpha)) →
  T.vertex (HierarchyFirstMissingPosition phi T alpha) ∈ TreeSequenceVertexSet Bplus →
  alpha ∉ MissingColors G phi (T.vertex penIndex) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D alpha penIndex B Bplus penPosition
      hBLouter hElemOuter hPenultimateInBplus hAlphaFirstBound hAlphaAtFirst hAlphaFirstBplus hm
  have hne : T.vertex (HierarchyFirstMissingPosition phi T alpha) ≠
      T.vertex penIndex := by
    intro he
    have hi := congrArg Fin.val (T.vertex_injective he)
    have hb := hAlphaFirstBound
    have hp := penPosition
    have hl := hBLouter
    clear * - hi hb hp hl
    omega
  exact Finset.disjoint_left.mp (hElemOuter hAlphaFirstBplus hPenultimateInBplus hne)
      hAlphaAtFirst hm

theorem helper_etaStoredTwo_2301.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  ∀ eta ∈ HierarchyStoredColorsAt H q,
  ∀ (PTwo : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
  eta ∈
    HierarchyStoredColorsAt PTwo.counterexample.hierarchy
      (Fin.last PTwo.counterexample.hierarchy.dividerCount) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx H q eta hetaStored PTwo
  obtain ⟨hc, hd⟩ := PTwo.sameGood.2
  have hi : Fin.cast (congrArg (fun d => d + 1) hc) q =
      Fin.last PTwo.counterexample.hierarchy.dividerCount := Fin.ext hc
  have hs := (hd q).1
  rw [hi] at hs
  exact hs ▸ hetaStored

theorem helper_continuation_4221.{u_1, u_2} :
    helperContinuation4221Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D alpha theta lastIndex penIndex endIndex H
      q A ell B Bplus n Tn lastPosition penPosition endPosition eta hetaStored hetaMissing
      hTailAtLeast hellOuter hBLouter hPLouter hBplusTouter hBBplusOuter hATouter hABplusouter
      hElemOuter vAlpha vertexMemOuter hPenultimateInBplus hBplusDef canonicalElem hAlphaEtaNe
      hAlphaMissingBplus hthetaMissingBplus hetaFirst hAlphaFirstBound hvAlphaBplus
      thetaAvoidsSplit selfComponent leafComponent separateVertices hAlphaAtFirst
      hthetaTerminalNe z muOne prefixMissing hThetaFirstBplus hAlphaFirstBplus hmissingOne
      hmissingPointwise htreeMissingEq hfixedSplit hlastOne hthetaTerminalOne hetaPenultimateOne
      lastZero hTnBplus hfixedBplusAux hfixedBplus hBplusLength transportOne hrouteOne
      firstWitness firstPreserved firstFromMembership hgammaCutoff hmissingPairOne hsuffixPhi
      corrOne maxOne baseOne COne sameOne ctxOne POne HOne qOne starOne countOne prefixOne
      elemOne missingPrefixOne firstThetaOne firstEtaOne thetaFirstOne thetaEtaNe thetaUnusedOne
      thetaStoredOne tnOne caseTwo etaMissingPrefixOne thetaMissingPrefixOne componentEqTwo
      thetaPenultimateNe
  have penultimateTerminalNe : T.vertex penIndex ≠
      T.vertex endIndex := by
    exact helper_penultimateTerminalNe_2092 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base)
        (@C) (@ctx) (@D)
        (@penPosition) (@endPosition)
  have disjointTwo := separateVertices muOne theta eta thetaEtaNe ctxOne.proper
    (T.vertex (HierarchyFirstMissingPosition phi T theta))
    (T.vertex penIndex) (T.vertex endIndex)
    thetaPenultimateNe hthetaTerminalNe penultimateTerminalNe
    thetaFirstOne hetaPenultimateOne (Or.inl hthetaTerminalOne) componentEqTwo
  let muTwo := TwoColorComponentSwap G muOne theta eta z
  have pathTwo : TwoColorPathComponent G muOne theta eta z :=
    ⟨thetaEtaNe, _, selfComponent muOne theta eta _,
      leafComponent muOne theta eta thetaEtaNe ctxOne.proper _ (Or.inl hthetaTerminalOne)⟩
  have thetaOutsideTwo : Sum.inl (T.vertex (HierarchyFirstMissingPosition phi T theta)) ∉
      TwoColorComponent G muOne theta eta z := by
    intro hm
    exact Set.disjoint_left.mp disjointTwo hm (selfComponent muOne theta eta _)
  have etaOutsideTwo : Sum.inl (T.vertex penIndex) ∉
      TwoColorComponent G muOne theta eta z := by
    intro hm
    apply Set.disjoint_left.mp disjointTwo hm
    rw [componentEqTwo]
    exact selfComponent muOne theta eta _
  have missingTwo : ∀ v ∈ TreeSequenceVertexSet Bplus,
      MissingColors G muTwo v = MissingColors G muOne v :=
    prefixMissing z muOne theta eta thetaEtaNe ctxOne.proper elemOne
      _ _ hThetaFirstBplus hPenultimateInBplus thetaFirstOne hetaPenultimateOne
      thetaOutsideTwo etaOutsideTwo
  have stableTwo := StableChangeCasesOneTwo G k e0 corrOne.replacementInput T muOne
    corrOne.replacementETT baseOne COne ctxOne.proper ctxOne.oneEdgeUncolored
    ctxOne.lowerRung ctxOne.fewerDividers ctxOne.lexicographicMinimality
    (by
      change ColoredVertexSetElementary G muOne (TreeSequenceVertexSet
        (HierarchyFullTailPrefix COne (HierarchyFullTailLength COne - 1)))
      rw [prefixOne]; exact elemOne) ctxOne.largeMissingSet
    theta eta thetaEtaNe (by
      change theta ∈ TreeMissingColors muOne
          (HierarchyFullTailPrefix COne (HierarchyFullTailLength COne - 1)) ∧
        eta ∈ TreeMissingColors muOne
          (HierarchyFullTailPrefix COne (HierarchyFullTailLength COne - 1))
      rw [prefixOne]; exact ⟨thetaMissingPrefixOne, etaMissingPrefixOne⟩)
    z pathTwo muTwo rfl caseTwo (by
      dsimp only
      rw [firstThetaOne]
      exact disjointTwo)
  have exclusionEta := HierarchyTailMissingColorExclusion G k e0 input T phi ett base H
      canonicalElem
    (ell - 1) (by clear * - hTailAtLeast; omega)
    (by change ell - 1 < ell; clear * - hTailAtLeast; omega) eta (by
      have hv : Bplus.vertex (Fin.last Bplus.length) = T.vertex penIndex := by
        exact helper_hv_2145 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
            (@Bplus)
            (@penPosition) (@hPLouter) (@hBplusTouter)
      have hm : eta ∈ MissingColors G phi (Bplus.vertex (Fin.last Bplus.length)) := hv.symm ▸
          hetaMissing
      subst Bplus
      exact hm)
  have exclusionEta' : ∀ t : Fin Bplus.length, A.length ≤ t.val →
      t.val < A.length + (ell - 1) → phi (Bplus.edge t) = some eta →
      H.dividerCount = 0 ∧ base.core = Tn ∧ t.val = A.length ∧
        ∃ f : E, TashkinovSeriesStep G k ett.rounds e0 input ett.series.data n ∧
          (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
            ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
          ett.series.data.connectingEdges n = {f} ∧ Bplus.edge t = f ∧
          phi f = some eta ∧ eta ∈ TashkinovStoredColors ett.series.data n := by
    subst Bplus
    exact exclusionEta
  have fixedTailTwo : ∀ t : Fin T.length, A.length ≤ t.val →
      muTwo (T.edge t) = muOne (T.edge t) := by
    exact helper_fixedTailTwo_2168 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@ctx) (@D) (@B)
        (@Bplus) (@lastPosition) (@penPosition) (@endPosition) (@eta) (@hellOuter) (@hBLouter)
        (@hPLouter) (@hBplusTouter) (@hATouter) (@vertexMemOuter) (@hAlphaEtaNe) (@hetaFirst)
        (@hfixedSplit) (@hlastOne) (@lastZero) (@corrOne) (@baseOne) (@COne) (@countOne)
        (@firstEtaOne) (@thetaUnusedOne) (@tnOne) (@stableTwo) (@exclusionEta')
  have behaviorTwo := TwoColorComponentSwapMissingBehavior G muOne theta eta thetaEtaNe
      ctxOne.proper z
  have storedFirstTwo : ∀ c ∈ HierarchyStoredColorsAt HOne qOne,
      HierarchyFirstMissingPosition muTwo T c = HierarchyFirstMissingPosition muOne T c := by
    exact helper_storedFirstTwo_2236 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@ctx) (@D)
        (@Bplus) (@eta) (@firstPreserved) (@firstFromMembership) (@corrOne) (@baseOne) (@COne)
        (@elemOne) (@thetaStoredOne) (@etaMissingPrefixOne) (@missingTwo) (@behaviorTwo)
  obtain ⟨corrTwo, maxTwo, baseTwo, KTwo, goodTwo, sameTwo⟩ :=
    (StableChangeCasesOneTwoFullTail G k e0 corrOne.replacementInput T muOne
      corrOne.replacementETT baseOne COne ctxOne theta eta thetaEtaNe
      (by rw [prefixOne]; exact ⟨thetaMissingPrefixOne, etaMissingPrefixOne⟩)
      z pathTwo muTwo rfl caseTwo
      (by dsimp only; rw [firstThetaOne]; exact disjointTwo)
      (by dsimp only; rw [starOne]; exact fixedTailTwo)
      (by rw [prefixOne]; exact missingTwo) storedFirstTwo).2.2.2.2
  have etaTerminalTwo : eta ∈ MissingColors G muTwo (T.vertex endIndex) :=
    behaviorTwo.2.1 _ (selfComponent muOne theta eta _) hthetaTerminalOne
  have etaPenultimateTwo : eta ∈ MissingColors G muTwo (T.vertex penIndex) := by
    rw [missingTwo _ hPenultimateInBplus]
    exact hetaPenultimateOne
  have lastTailBound : A.length ≤ lastIndex.val := by
    exact helper_lastTailBound_2256 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@ctx) (@D)
        (@lastPosition) (@hTailAtLeast) (@hellOuter)
  have lastTwo : muTwo (T.edge lastIndex) = some alpha :=
    (fixedTailTwo lastIndex lastTailBound).trans hlastOne
  obtain ⟨CTwo, sameTwo⟩ : ∃ CTwo : HierarchyCounterexample baseTwo,
      SameGoodHierarchy COne.good CTwo.good := by
    refine ⟨{
      positive := by rw [corrTwo.rungAgreement]; exact COne.positive
      hierarchy := KTwo
      good := goodTwo
      maximum := maxTwo
      notElementary := ?_ }, sameTwo⟩
    intro he
    exact Finset.disjoint_left.mp
      (he (vertexMemOuter T penIndex)
        (vertexMemOuter T endIndex) penultimateTerminalNe)
      etaPenultimateTwo etaTerminalTwo
  obtain ⟨PTwo, colorTwo⟩ := HierarchyReplacementPresentationTrans G k e0 input T phi
    ett base C ctx POne muTwo corrTwo baseTwo CTwo sameTwo
  have alphaPresentPenultimate : alpha ∉ MissingColors G phi (T.vertex penIndex) := by
    exact helper_alphaPresentPenultimate_2279 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base)
        (@C) (@ctx) (@D) (@B) (@Bplus) (@penPosition) (@hBLouter) (@hElemOuter)
        (@hPenultimateInBplus)
        (@hAlphaFirstBound) (@hAlphaAtFirst) (@hAlphaFirstBplus)
  have alphaPresentTwo : alpha ∉ MissingColors G muTwo (T.vertex penIndex) := by
    rw [missingTwo _ hPenultimateInBplus, hmissingPointwise _ hPenultimateInBplus]
    exact alphaPresentPenultimate
  have starTwo : HierarchyStarredStage PTwo.counterexample.hierarchy
      (Fin.last PTwo.counterexample.hierarchy.dividerCount) = A :=
    (P2752_T2_HierarchyMeasures C.hierarchy PTwo.counterexample.hierarchy PTwo.sameGood.1).1.symm
  have pathTwoEq : HierarchyPathNumber C.hierarchy = HierarchyPathNumber
      PTwo.counterexample.hierarchy :=
    (P2752_T2_HierarchyMeasures C.hierarchy PTwo.counterexample.hierarchy PTwo.sameGood.1).2.1
  have etaStoredTwo : eta ∈ HierarchyStoredColorsAt PTwo.counterexample.hierarchy
      (Fin.last PTwo.counterexample.hierarchy.dividerCount) := by
    exact helper_etaStoredTwo_2301 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@ctx) (@eta)
        (@hetaStored) (@PTwo)
  obtain ⟨gammaOne, gammaTwo, gammaDistinct, gammaPair⟩ :=
    Finset.card_eq_two.mp (PTwo.counterexample.good.twoColors _ eta etaStoredTwo)
  let finalData : HierarchySituationTwoCaseOneData G k e0 PTwo.corresponding.replacementInput T
      PTwo.coloring PTwo.corresponding.replacementETT PTwo.replacementBase
      PTwo.counterexample PTwo.minimumContext := by
    exact @helperFinalData2160 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@lastPosition) (@penPosition) (@endPosition) (@eta) (@hTailAtLeast) (@etaTerminalTwo)
        (@etaPenultimateTwo) (@lastTwo) (@PTwo) (@colorTwo) (@alphaPresentTwo) (@starTwo)
        (@pathTwoEq) (@etaStoredTwo) (@gammaOne) (@gammaTwo) (@gammaDistinct) (@gammaPair)
  exact HierarchySituationTwoSubcaseOneOne G k e0 PTwo.corresponding.replacementInput T
    PTwo.coloring PTwo.corresponding.replacementETT PTwo.replacementBase
    PTwo.counterexample PTwo.minimumContext finalData

theorem helper_continuation_3757.{u_1, u_2} :
    helperContinuation3757Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D alpha theta lastIndex penIndex endIndex H
      q A ell B Bplus n Tn lastPosition penPosition endPosition eta hetaStored hetaMissing
      hthetaGamma hTailAtLeast hellOuter hBLouter hPLouter hBplusTouter hBBplusOuter hATouter
      hABplusouter hElemOuter vAlpha vertexMemOuter hPenultimateInBplus hBplusDef canonicalElem
      hAlphaEtaNe hthetaInA hetaNotA hAlphaMissingBplus hthetaMissingBplus hetaFirst
      hthetaFirstBound hAlphaFirstBound hvAlphaBplus thetaAvoidsSplit hthetaAlphaNe hThetaTn
      selfComponent leafComponent separateVertices hthetaAtFirst hAlphaAtFirst hthetaTerminalNe z
      muOne prefixMissing hThetaFirstBplus hAlphaFirstBplus hmissingOne hmissingPointwise
      htreeMissingEq hfixedSplit hlastOne hthetaTerminalOne hetaPenultimateOne stageSegment
      lastZero hTnBplus hfixedBplusAux hfixedBplus hBplusLength transportOne hrouteOne
      firstWitness firstPreserved firstFromMembership hgammaCutoff hmissingPairOne hsuffixPhi
      corrOne maxOne baseOne KOne goodOne sameOne
  obtain ⟨COne, sameOne⟩ : ∃ COne : HierarchyCounterexample baseOne,
      SameGoodHierarchy C.good COne.good := by
    refine ⟨{
      positive := by rw [corrOne.rungAgreement]; exact C.positive
      hierarchy := KOne
      good := goodOne
      maximum := maxOne
      notElementary := ?_ }, sameOne⟩
    intro he
    exact Finset.disjoint_left.mp
      (he (vertexMemOuter T (HierarchyFirstMissingPosition phi T theta))
        (vertexMemOuter T endIndex) hthetaTerminalNe)
      ((hmissingPointwise _ hThetaFirstBplus).symm ▸ hthetaAtFirst) hthetaTerminalOne
  obtain ⟨ctxOne⟩ := P2752_T2_MinimumContextTransport G k e0 input T phi muOne
    ett base C ctx corrOne baseOne COne sameOne
  let POne : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx := by
    exact @helperPOne1741 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@corrOne) (@maxOne)
        (@baseOne) (@COne) (@sameOne) (@ctxOne)
  let HOne := COne.hierarchy
  let qOne : Fin (HOne.dividerCount + 1) := Fin.last HOne.dividerCount
  have starOne : HierarchyStarredStage HOne qOne = A :=
    (P2752_T2_HierarchyMeasures C.hierarchy COne.hierarchy sameOne.1).1.symm
  have countOne : H.dividerCount = HOne.dividerCount := sameOne.2.choose
  have prefixOne : HierarchyFullTailPrefix COne (HierarchyFullTailLength COne - 1) =
      Bplus := by
    exact helper_prefixOne_1931 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@Bplus) (@hBplusDef) (@corrOne) (@baseOne) (@COne) (@starOne)
  have elemOne : ColoredVertexSetElementary G muOne (TreeSequenceVertexSet Bplus) := by
    intro u hu v hv hne
    rw [hmissingPointwise u hu, hmissingPointwise v hv]
    exact hElemOuter hu hv hne
  have missingPrefixOne : ∀ X : TreeSequence G e0,
      TreeSequenceInitialSegment X Bplus → TreeMissingColors muOne X = TreeMissingColors phi X := by
    intro X hX
    unfold TreeMissingColors
    exact Finset.biUnion_congr rfl (fun v hv =>
      hmissingPointwise v (TreeSequenceInitialSegmentVertexSetSubset hX hv))
  have firstThetaOne : HierarchyFirstMissingPosition muOne T theta =
      HierarchyFirstMissingPosition phi T theta := firstPreserved phi muOne theta hElemOuter
          hmissingPointwise hthetaMissingBplus
  have firstEtaOne : HierarchyFirstMissingPosition muOne T eta =
      penIndex :=
    (firstPreserved phi muOne eta hElemOuter hmissingPointwise (Finset.mem_biUnion.mpr ⟨_,
        hPenultimateInBplus, hetaMissing⟩)).trans hetaFirst
  have thetaFirstOne : theta ∈ MissingColors G muOne
      (T.vertex (HierarchyFirstMissingPosition phi T theta)) := by
    rw [hmissingPointwise _ hThetaFirstBplus]
    exact hthetaAtFirst
  have thetaEtaNe : theta ≠ eta := by
    intro he
    exact hetaNotA (he ▸ hthetaInA)
  have thetaUnusedOne : ∀ t : Fin T.length, A.length ≤ t.val →
      muOne (T.edge t) ≠ some theta := by
    exact helper_thetaUnusedOne_1963 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@ctx) (@D)
        (@Bplus) (@lastPosition) (@hPLouter) (@thetaAvoidsSplit) (@hthetaAlphaNe) (@hfixedSplit)
        (@hlastOne)
  have sameLastOne : HierarchyStoredColorsAt H q = HierarchyStoredColorsAt HOne qOne ∧
      ∀ c ∈ HierarchyStoredColorsAt H q, C.good.gamma q c = COne.good.gamma qOne c := by
    obtain ⟨hc, hd⟩ := sameOne.2
    have hi : Fin.cast (congrArg (fun d => d + 1) hc) q = qOne :=
      Fin.ext hc
    simpa only [hi] using hd q
  have thetaStoredOne : theta ∉ HierarchyStoredColorsAt HOne qOne := by
    rw [← sameLastOne.1]
    exact fun hm => (Finset.mem_sdiff.mp hm).2 hthetaInA
  have etaStoredOne : eta ∈ HierarchyStoredColorsAt HOne qOne :=
    sameLastOne.1 ▸ hetaStored
  have etaGammaOne : theta ∈ COne.good.gamma qOne eta :=
    sameLastOne.2 eta hetaStored ▸ hthetaGamma
  have tnOne :
      corrOne.replacementETT.series.data.tree (Fin.last corrOne.replacementETT.rounds).castSucc =
          Tn := by
    exact helper_tnOne_1991 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@corrOne)
        (@baseOne) (@COne) (@sameOne) (@countOne)
  have thetaTnOne (hz : HOne.dividerCount = 0) :
      theta ∈ TreeMissingColors muOne
        (corrOne.replacementETT.series.data.tree (Fin.last
            corrOne.replacementETT.rounds).castSucc) := by
    rw [tnOne, missingPrefixOne Tn hTnBplus]
    exact hThetaTn (countOne.trans hz)
  have positiveStarOne (hz : HOne.dividerCount ≠ 0) :
      HOne.stage ⟨HOne.dividerCount, Nat.lt_succ_of_lt (Nat.lt_succ_self _)⟩ = A := by
    exact helper_positiveStarOne_2005 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@ctx) (@D) (@B)
        (@Bplus) (@eta) (@corrOne) (@baseOne) (@COne) (@starOne) (@countOne) (@hz)
  have caseTwo :
      (0 < HOne.dividerCount ∧ theta ∈ TreeMissingColors muOne
        (HOne.stage ⟨HOne.dividerCount, Nat.lt_succ_of_lt (Nat.lt_succ_self _)⟩)) ∨
      (HOne.dividerCount = 0 ∧
        (theta ∈ TreeMissingColors muOne
          (corrOne.replacementETT.series.data.tree (Fin.last
              corrOne.replacementETT.rounds).castSucc) ∨
          (theta ∈ TreeMissingColors muOne (HierarchyStarredStage HOne qOne) ∧
            theta ∉ TashkinovStoredColors corrOne.replacementETT.series.data
              (Fin.last corrOne.replacementETT.rounds) ∧
            eta ∉ TashkinovStoredColors corrOne.replacementETT.series.data
              (Fin.last corrOne.replacementETT.rounds)))) := by
    exact helper_caseTwo_2017 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
        (@D) (@Bplus) (@eta)
        (@hABplusouter) (@hthetaInA) (@corrOne) (@baseOne) (@COne) (@missingPrefixOne)
        (@thetaTnOne) (@positiveStarOne)
  have etaMissingPrefixOne : eta ∈ TreeMissingColors muOne Bplus :=
    Finset.mem_biUnion.mpr ⟨_, hPenultimateInBplus, hetaPenultimateOne⟩
  have thetaMissingPrefixOne : theta ∈ TreeMissingColors muOne Bplus := hmissingPairOne.1
  have orderedTwo :
      (theta ∉ TreeMissingColors muOne (HierarchyStarredStage HOne qOne) ∨
        eta ∉ TreeMissingColors muOne (HierarchyStarredStage HOne qOne)) →
      TreeVertexOrder T (T.vertex (HierarchyFirstMissingPosition muOne T theta))
        (T.vertex (HierarchyFirstMissingPosition muOne T eta)) ∧
      theta ∉ Finset.univ.filter (fun c =>
        ∃ t : Fin T.length, (HierarchyStarredStage HOne qOne).length ≤ t.val ∧
          t.val < (HierarchyFirstMissingPosition muOne T eta).val ∧
          muOne (T.edge t) = some c) := by
    exact helper_orderedTwo_2037 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
        (@D)
        (@penPosition) (@eta) (@hTailAtLeast) (@hellOuter) (@hthetaFirstBound) (@corrOne)
        (@baseOne) (@COne) (@starOne) (@firstThetaOne) (@firstEtaOne) (@thetaUnusedOne)
  have changeTwo := ChangeLemma G k e0 corrOne.replacementInput T muOne
    corrOne.replacementETT baseOne COne ctxOne.proper ctxOne.oneEdgeUncolored
    ctxOne.lowerRung ctxOne.fewerDividers ctxOne.lexicographicMinimality
    (by
      change ColoredVertexSetElementary G muOne (TreeSequenceVertexSet
        (HierarchyFullTailPrefix COne (HierarchyFullTailLength COne - 1)))
      rw [prefixOne]; exact elemOne) ctxOne.largeMissingSet
    theta eta thetaEtaNe (by
      change theta ∈ TreeMissingColors muOne
          (HierarchyFullTailPrefix COne (HierarchyFullTailLength COne - 1)) ∧
        eta ∈ TreeMissingColors muOne
          (HierarchyFullTailPrefix COne (HierarchyFullTailLength COne - 1))
      rw [prefixOne]
      exact ⟨thetaMissingPrefixOne, etaMissingPrefixOne⟩) orderedTwo
  have componentEqTwo :
      TwoColorComponent G muOne theta eta
        (Sum.inl (T.vertex (HierarchyFirstMissingPosition phi T theta))) =
      TwoColorComponent G muOne theta eta (Sum.inl (T.vertex penIndex)) := by
    exact helper_componentEqTwo_2072 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@ctx) (@D)
        (@Bplus) (@eta) (@hABplusouter) (@hthetaInA) (@corrOne) (@baseOne) (@COne)
        (@missingPrefixOne) (@firstThetaOne) (@firstEtaOne) (@thetaTnOne) (@positiveStarOne)
        (@changeTwo)
  have thetaPenultimateNe : T.vertex (HierarchyFirstMissingPosition phi T theta) ≠
      T.vertex penIndex := by
    exact helper_thetaPenultimateNe_2082 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@ctx) (@D)
        (@penPosition) (@hTailAtLeast) (@hellOuter) (@hthetaFirstBound)
  exact @helper_continuation_4221 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@B)
      (@Bplus) (@lastPosition) (@penPosition) (@endPosition) (@eta) (@hetaStored) (@hetaMissing)
      (@hTailAtLeast) (@hellOuter) (@hBLouter) (@hPLouter) (@hBplusTouter) (@hBBplusOuter)
      (@hATouter) (@hABplusouter) (@hElemOuter) (@vAlpha) (@vertexMemOuter)
      (@hPenultimateInBplus) (@hBplusDef) (@canonicalElem) (@hAlphaEtaNe) (@hAlphaMissingBplus)
      (@hthetaMissingBplus) (@hetaFirst) (@hAlphaFirstBound) (@hvAlphaBplus) (@thetaAvoidsSplit)
      (@selfComponent) (@leafComponent) (@separateVertices) (@hAlphaAtFirst) (@hthetaTerminalNe)
      (@prefixMissing) (@hThetaFirstBplus) (@hAlphaFirstBplus) (@hmissingOne)
      (@hmissingPointwise) (@htreeMissingEq) (@hfixedSplit) (@hlastOne) (@hthetaTerminalOne)
      (@hetaPenultimateOne) (@lastZero) (@hTnBplus) (@hfixedBplusAux) (@hfixedBplus)
      (@hBplusLength) (@transportOne) (@hrouteOne) (@firstWitness) (@firstPreserved)
      (@firstFromMembership) (@hgammaCutoff) (@hmissingPairOne) (@hsuffixPhi) (@corrOne)
      (@maxOne) (@baseOne) (@COne) (@sameOne) (@ctxOne) (@starOne) (@countOne) (@prefixOne)
      (@elemOne) (@missingPrefixOne) (@firstThetaOne) (@firstEtaOne) (@thetaFirstOne)
      (@thetaEtaNe) (@thetaUnusedOne) (@thetaStoredOne) (@tnOne) (@caseTwo)
      (@etaMissingPrefixOne) (@thetaMissingPrefixOne) (@componentEqTwo) (@thetaPenultimateNe)
theorem helper_continuation_3399.{u_1, u_2} :
    helperContinuation3399Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D alpha theta lastIndex penIndex endIndex H
      q A ell B Bplus n Tn lastColor alphaTerminal alphaUnused lastPosition penPosition
      endPosition oldRoute eta hetaStored hetaMissing hthetaGamma hTailAtLeast hellOuter hBLouter
      hPLouter hBplusTouter hBBplusOuter hATouter hABplusouter hElemOuter vAlpha vertexMemOuter
      hPenultimateInBplus hBplusDef canonicalElem hAlphaEtaNe hthetaInA hetaNotA
      hAlphaMissingBplus hthetaMissingBplus canonicalMissing hetaFirst hthetaFirstBound
      hAlphaFirstBound hvAlphaBplus thetaAvoidsSplit hthetaAlphaNe hThetaTn hChange selfComponent
      leafComponent separateVertices hthetaAtFirst hAlphaAtFirst hthetaTerminalNe
      hdisjointComponent z hpath muOne behaviorOne prefixMissing hThetaFirstBplus
      hAlphaFirstBplus hmissingOne hmissingPointwise
  have htreeMissingEq : TreeMissingColors muOne Bplus = TreeMissingColors phi Bplus := by
    as_aux_lemma =>
      unfold TreeMissingColors
      exact Finset.biUnion_congr rfl hmissingPointwise
  have hstableOne := StableChangeCasesOneTwo G k e0 input T phi ett base C
      ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
      ctx.lexicographicMinimality canonicalElem ctx.largeMissingSet
      theta alpha hthetaAlphaNe canonicalMissing
      z hpath muOne rfl hChange hdisjointComponent
  have hfixedCoreOne : ∀ t : Fin A.length,
      muOne (A.edge t) = phi (A.edge t) := by
    exact helper_hfixedCoreOne_1548 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@ctx) (@D) (@B)
        (@Bplus) (@eta) (@hstableOne)
  have hfixedSplit : ∀ t : Fin T.length, A.length ≤ t.val →
      t.val < Bplus.length → muOne (T.edge t) = phi (T.edge t) := by
    intro t ht htb
    simp [muOne, TwoColorComponentSwap, alphaUnused t ht,
      thetaAvoidsSplit t ht htb]
  have hlastIncident : Incident G (T.vertex endIndex)
      (T.edge lastIndex) := by
    exact helper_hlastIncident_1596 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@ctx) (@D) (@B)
        (@Bplus) (@lastPosition) (@penPosition) (@endPosition) (@eta)
  have hlastEdgeInOne : Sum.inr (T.edge lastIndex) ∈
      TwoColorComponent G phi theta alpha z := by
    exact helper_hlastEdgeInOne_1608 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@ctx) (@D)
        (@lastColor) (@hlastIncident)
  have hlastOne : muOne (T.edge lastIndex) = some alpha := by
    simp [muOne, TwoColorComponentSwap, hlastEdgeInOne, lastColor]
  have hthetaTerminalOne : theta ∈ MissingColors G muOne
      (T.vertex endIndex) := by
    exact behaviorOne.2.2.1 _ (selfComponent phi theta alpha
      (T.vertex endIndex)) alphaTerminal
  have hetaPenultimateOne : eta ∈ MissingColors G muOne
      (T.vertex penIndex) := by
    rw [hmissingOne _ hPenultimateInBplus]
    exact hetaMissing
  have segTrans {X Y Z : TreeSequence G e0}
      (hXY : TreeSequenceInitialSegment X Y)
      (hYZ : TreeSequenceInitialSegment Y Z) : TreeSequenceInitialSegment X Z := by
    exact helper_segTrans_1626 (@G) (@e0) (@hXY) (@hYZ)
  have stageSegment (a d : ℕ) (hb : a + d ≤ H.dividerCount + 1) :
      TreeSequenceInitialSegment (H.stage ⟨a, by omega⟩)
        (H.stage ⟨a + d, by omega⟩) := by
    exact @helper_stageSegment_1634 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@B)
        (@Bplus) (@eta) (@segTrans) (@a) (@d) (@hb)
  have lastZero (hz : H.dividerCount = 0) : A = base.core := by
    simp [A, q, HierarchyStarredStage, hz, Fin.last]
  have lastPositive (hz : H.dividerCount ≠ 0) :
      A = H.stage ⟨H.dividerCount, Nat.lt_succ_of_lt (Nat.lt_succ_self _)⟩ := by
    exact helper_lastPositive_1645 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@ctx) (@D) (@B)
        (@Bplus) (@eta) (@hz)
  have coreToA : TreeSequenceInitialSegment base.core A := by
    exact @helper_coreToA_1660 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@B) (@Bplus) (@eta)
        (@segTrans) (@stageSegment) (@lastZero) (@lastPositive)
  have hTnBplus : TreeSequenceInitialSegment Tn Bplus := by
    exact helper_hTnBplus_1668 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
        (@D) (@B) (@Bplus) (@eta)
        (@hPLouter) (@hBplusTouter)
  have hfixedBplusAux (aLen : Nat) (haLen : aLen = A.length)
      (hcut : ∀ t : Fin Bplus.length, t.val < aLen ∨ aLen ≤ t.val) :
      ∀ t : Fin Bplus.length, muOne (Bplus.edge t) = phi (Bplus.edge t) := by
    exact helper_hfixedBplusAux_1682 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@ctx) (@D)
        (@Bplus) (@hBplusTouter) (@hABplusouter) (@hfixedCoreOne) (@hfixedSplit) (@aLen) (@haLen)
        (@hcut)
  have hfixedBplus := hfixedBplusAux A.length rfl
    (fun t => Nat.lt_or_ge t.val A.length)
  have hBplusLength : Bplus.length = B.length + 1 := by
    exact helper_hBplusLength_1712 (@G) (@e0) (@T) (@B) (@Bplus) (@hBLouter) (@hPLouter)
  have transportOne (S : TreeSequence G e0)
      (hseq : TashkinovAugmentationSequence phi S Bplus) :
      TashkinovAugmentationSequence muOne S Bplus := by
    exact helper_transportOne_1721 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@ctx) (@D) (@B)
        (@Bplus) (@hBBplusOuter) (@hmissingOne) (@hfixedBplus) (@hBplusLength) (@S) (@hseq)
  have hrouteOne :
      (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence muOne Tn Bplus) ∨
      ((ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
          ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
        ∃ f seed, ett.series.data.connectingEdges n = {f} ∧
          TreeSequenceAdjoinEdge Tn f seed ∧
          TashkinovAugmentationSequence muOne seed Bplus) := by
    exact @helper_hrouteOne_1730 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@Bplus) (@oldRoute) (@hTailAtLeast) (@hellOuter) (@hPLouter) (@hBplusTouter)
        (@hABplusouter) (@segTrans) (@coreToA) (@hTnBplus) (@transportOne)
  have firstWitness (rho : PartialEdgeColoring E k) (c : Fin k)
      (hc : c ∈ TreeMissingColors rho Bplus) :
      c ∈ MissingColors G rho (T.vertex (HierarchyFirstMissingPosition rho T c)) ∧
        (HierarchyFirstMissingPosition rho T c).val ≤ Bplus.length := by
    exact helper_firstWitness_1779 (@G) (@k) (@e0) (@T) (@Bplus) (@hBplusTouter) (@rho) (@c) (@hc)
  have firstPreserved (rho sigma : PartialEdgeColoring E k) (c : Fin k)
      (helem : ColoredVertexSetElementary G rho (TreeSequenceVertexSet Bplus))
      (hmiss : ∀ v ∈ TreeSequenceVertexSet Bplus, MissingColors G sigma v = MissingColors G rho v)
      (hc : c ∈ TreeMissingColors rho Bplus) :
      HierarchyFirstMissingPosition sigma T c = HierarchyFirstMissingPosition rho T c := by
    exact helper_firstPreserved_1805 (@G) (@k) (@e0) (@T) (@Bplus) (@hBplusTouter)
        (@firstWitness) (@rho) (@sigma) (@c) (@helem) (@hmiss) (@hc)
  have firstFromMembership (rho sigma : PartialEdgeColoring E k) (c : Fin k)
      (hc : ∀ v, c ∈ MissingColors G sigma v ↔ c ∈ MissingColors G rho v) :
      HierarchyFirstMissingPosition sigma T c = HierarchyFirstMissingPosition rho T c := by
    exact helper_firstFromMembership_1829 (@G) (@k) (@e0) (@T) (@rho) (@sigma) (@c) (@hc)
  have hstoredFirst : ∀ c, c ∈ HierarchyStoredColorsAt H q →
      HierarchyFirstMissingPosition muOne T c = HierarchyFirstMissingPosition phi T c := by
    exact helper_hstoredFirst_1843 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@ctx) (@D)
        (@Bplus) (@hElemOuter) (@hthetaInA) (@hAlphaMissingBplus) (@behaviorOne)
        (@hmissingPointwise) (@firstPreserved) (@firstFromMembership)
  have hAlphaNoGamma : alpha ∉ (HierarchyStoredColorsAt H q).biUnion (C.good.gamma q) := by
    exact helper_hAlphaNoGamma_1854 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@ctx) (@D)
  have hthetaOwner : ∀ c, c ∈ HierarchyStoredColorsAt H q →
      theta ∈ C.good.gamma q c → c = eta := by
    intro c hc hct
    by_contra hne
    exact Finset.disjoint_left.mp (C.good.disjointPairs q c eta hc hetaStored hne)
      hct hthetaGamma
  have hgammaCutoff : ∀ c, c ∈ HierarchyStoredColorsAt H q →
      (alpha ∈ C.good.gamma q c ∨ theta ∈ C.good.gamma q c) →
        (HierarchyFirstMissingPosition phi T c).val ≤ Bplus.length := by
    exact helper_hgammaCutoff_1866 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@ctx) (@D) (@B)
        (@Bplus) (@penPosition) (@endPosition) (@eta) (@hBLouter) (@hPLouter) (@hetaFirst)
        (@hAlphaNoGamma) (@hthetaOwner)
  have hmissingPairOne :
      theta ∈ TreeMissingColors muOne Bplus ∧
        alpha ∈ TreeMissingColors muOne Bplus := by
    exact htreeMissingEq.symm ▸ ⟨hthetaMissingBplus, hAlphaMissingBplus⟩
  have hsuffixPhi : TashkinovAugmentationSequence phi Bplus T := by
    exact helper_hsuffixPhi_1881 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
        (@D)
        (@Bplus) (@lastColor) (@lastPosition) (@hPLouter) (@hBplusTouter) (@hthetaMissingBplus)
  obtain ⟨_, _, corrOne, maxOne, baseOne, KOne, goodOne, sameOne⟩ :=
    StableChangeCasesOneTwoSplitTail G k e0 input T phi ett base C ctx
      theta alpha hthetaAlphaNe canonicalMissing
      z hpath muOne rfl hChange hdisjointComponent
      Bplus hABplusouter (by
        change A.length < Bplus.length
        have htail := hTailAtLeast
        have hp := hPLouter
        have hell := hellOuter
        clear * - htail hp hell
        omega)
      (by rw [← hBplusDef]; exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩)
      hfixedSplit hrouteOne hsuffixPhi hmissingPairOne
      (by rw [← hBplusDef]; exact hmissingPointwise)
      hstoredFirst (fun c hc hp => hgammaCutoff c hc hp.symm)
  exact @helper_continuation_3757 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@B)
      (@Bplus) (@lastPosition) (@penPosition) (@endPosition) (@eta) (@hetaStored) (@hetaMissing)
      (@hthetaGamma) (@hTailAtLeast) (@hellOuter) (@hBLouter) (@hPLouter) (@hBplusTouter)
      (@hBBplusOuter) (@hATouter) (@hABplusouter) (@hElemOuter) (@vAlpha) (@vertexMemOuter)
      (@hPenultimateInBplus) (@hBplusDef) (@canonicalElem) (@hAlphaEtaNe) (@hthetaInA)
      (@hetaNotA) (@hAlphaMissingBplus) (@hthetaMissingBplus) (@hetaFirst) (@hthetaFirstBound)
      (@hAlphaFirstBound) (@hvAlphaBplus) (@thetaAvoidsSplit) (@hthetaAlphaNe) (@hThetaTn)
      (@selfComponent) (@leafComponent) (@separateVertices) (@hthetaAtFirst) (@hAlphaAtFirst)
      (@hthetaTerminalNe) (@prefixMissing) (@hThetaFirstBplus) (@hAlphaFirstBplus) (@hmissingOne)
      (@hmissingPointwise) (@htreeMissingEq) (@hfixedSplit) (@hlastOne) (@hthetaTerminalOne)
      (@hetaPenultimateOne) (@stageSegment) (@lastZero) (@hTnBplus) (@hfixedBplusAux)
      (@hfixedBplus) (@hBplusLength) (@transportOne) (@hrouteOne) (@firstWitness)
      (@firstPreserved) (@firstFromMembership) (@hgammaCutoff) (@hmissingPairOne) (@hsuffixPhi)
      (@corrOne) (@maxOne) (@baseOne) (@KOne) (@goodOne) (@sameOne)
theorem helper_continuation_3310.{u_1, u_2} :
    helperContinuation3310Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D alpha theta lastIndex penIndex endIndex H
      q A ell B Bplus n Tn lastColor alphaTerminal alphaBefore alphaUnused lastPosition
      penPosition endPosition oldRoute eta hetaStored hetaMissing hthetaGamma hTailAtLeast
      hellOuter hBLouter hPLouter hBTouter hBplusTouter hBBplusOuter hATouter hABplusouter
      hElemOuter missingMonoOuter vAlpha vertexMemOuter firstMissingOuter hPenultimateInBplus
      hBplusDef canonicalElem hAlphaEtaNe hthetaInA hetaNotA hAlphaMissingBplus
      hthetaMissingBplus canonicalMissing hetaFirst hthetaFirstBound hAlphaFirstBound
      hvAlphaBplus horderedUnused thetaAvoidsSplit hthetaAlphaNe hThetaTn hThetaTnq
  have hChange :
      (0 < H.dividerCount ∧ theta ∈ TreeMissingColors phi
        (H.stage ⟨H.dividerCount, Nat.lt_succ_of_lt (Nat.lt_succ_self _)⟩)) ∨
      (H.dividerCount = 0 ∧
        (theta ∈ TreeMissingColors phi Tn ∨
          (theta ∈ TreeMissingColors phi A ∧
            theta ∉ TashkinovStoredColors ett.series.data n ∧
            alpha ∉ TashkinovStoredColors ett.series.data n))) := by
    exact helper_hChange_1257 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
        (@D) (@hThetaTn)
        (@hThetaTnq)
  have hchange := ChangeLemma G k e0 input T phi ett base C
      ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
      ctx.lexicographicMinimality canonicalElem ctx.largeMissingSet
      theta alpha hthetaAlphaNe canonicalMissing horderedUnused
  have hcomponentEq :
      TwoColorComponent G phi theta alpha
          (Sum.inl (T.vertex (HierarchyFirstMissingPosition phi T theta))) =
        TwoColorComponent G phi theta alpha
          (Sum.inl (T.vertex (HierarchyFirstMissingPosition phi T alpha))) := by
    by_cases hz : H.dividerCount = 0
    · exact hchange.2.1 ⟨hz, Or.inl (hThetaTn hz)⟩
    · exact hchange.1 ⟨Nat.pos_of_ne_zero hz,
        Or.inl (hThetaTnq (Nat.pos_of_ne_zero hz))⟩
  have selfComponent (rho : PartialEdgeColoring E k) (a b : Fin k) (v : V) :
      Sum.inl v ∈ TwoColorComponent G rho a b (Sum.inl v) := by
    change (TwoColorIncidenceGraph G rho a b).connectedComponentMk (Sum.inl v) = _
    rfl
  have leafComponent (rho : PartialEdgeColoring E k) (a b : Fin k) (hne : a ≠ b)
      (hp : IsProperEdgeColoring G rho) (v : V)
      (hm : a ∈ MissingColors G rho v ∨ b ∈ MissingColors G rho v) :
      Set.Subsingleton ((TwoColorIncidenceGraph G rho a b).neighborSet (Sum.inl v)) := by
    exact helper_leafComponent_1287 (@G) (@k) (@rho) (@a) (@b) (@hne) (@hp) (@v) (@hm)
  have separateVertices (rho : PartialEdgeColoring E k) (a b : Fin k) (hne : a ≠ b)
      (hp : IsProperEdgeColoring G rho) (u v w : V)
      (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
      (hu : a ∈ MissingColors G rho u) (hv : b ∈ MissingColors G rho v)
      (hw : a ∈ MissingColors G rho w ∨ b ∈ MissingColors G rho w)
      (hsame : TwoColorComponent G rho a b (Sum.inl u) =
        TwoColorComponent G rho a b (Sum.inl v)) :
      Disjoint (TwoColorComponent G rho a b (Sum.inl w))
        (TwoColorComponent G rho a b (Sum.inl u)) := by
    exact helper_separateVertices_1307 (@G) (@k) (@selfComponent) (@leafComponent) (@rho) (@a)
        (@b) (@hne) (@hp)
        (@u) (@v) (@w) (@huv) (@huw) (@hvw) (@hu) (@hv) (@hw) (@hsame)
  have separateMaybeCoincident (rho : PartialEdgeColoring E k) (a b : Fin k)
      (hne : a ≠ b) (hp : IsProperEdgeColoring G rho) (u v w : V)
      (huw : u ≠ w) (hvw : v ≠ w)
      (hu : a ∈ MissingColors G rho u) (hv : b ∈ MissingColors G rho v)
      (hw : a ∈ MissingColors G rho w ∨ b ∈ MissingColors G rho w)
      (hsame : TwoColorComponent G rho a b (Sum.inl u) =
        TwoColorComponent G rho a b (Sum.inl v)) :
      Disjoint (TwoColorComponent G rho a b (Sum.inl w))
        (TwoColorComponent G rho a b (Sum.inl u)) := by
    exact helper_separateMaybeCoincident_1344 (@G) (@k) (@selfComponent) (@separateVertices)
        (@rho) (@a) (@b) (@hne)
        (@hp) (@u) (@v) (@w) (@huw) (@hvw) (@hu) (@hv) (@hw) (@hsame)
  have hAlphaMissingT : alpha ∈ TreeMissingColors phi T :=
    missingMonoOuter (X := B) (Y := T) hBTouter alphaBefore
  have hthetaMissingT : theta ∈ TreeMissingColors phi T :=
    missingMonoOuter (X := A) (Y := T) hATouter hthetaInA
  have hthetaAtFirst : theta ∈ MissingColors G phi
      (T.vertex (HierarchyFirstMissingPosition phi T theta)) :=
    firstMissingOuter T theta hthetaMissingT
  have hAlphaAtFirst : alpha ∈ MissingColors G phi
      (T.vertex (HierarchyFirstMissingPosition phi T alpha)) :=
    firstMissingOuter T alpha hAlphaMissingT
  have hthetaTerminalNe : T.vertex (HierarchyFirstMissingPosition phi T theta) ≠
      T.vertex endIndex := by
    exact helper_hthetaTerminalNe_1391 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@ctx) (@D)
        (@endPosition) (@hTailAtLeast) (@hellOuter) (@hthetaFirstBound)
  have hAlphaTerminalNe : T.vertex (HierarchyFirstMissingPosition phi T alpha) ≠
      T.vertex endIndex := by
    exact helper_hAlphaTerminalNe_1401 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@ctx) (@D) (@B)
        (@endPosition) (@hBLouter) (@hAlphaFirstBound)
  have hdisjointComponent := separateMaybeCoincident phi theta alpha
      hthetaAlphaNe ctx.proper
      (T.vertex (HierarchyFirstMissingPosition phi T theta))
      (T.vertex (HierarchyFirstMissingPosition phi T alpha))
      (T.vertex endIndex)
      hthetaTerminalNe hAlphaTerminalNe hthetaAtFirst hAlphaAtFirst
      (Or.inr alphaTerminal) hcomponentEq
  let z : Sum V E := Sum.inl (T.vertex endIndex)
  have hpath : TwoColorPathComponent G phi theta alpha z :=
    ⟨hthetaAlphaNe, _, selfComponent phi theta alpha _,
      leafComponent phi theta alpha hthetaAlphaNe ctx.proper _
        (Or.inr alphaTerminal)⟩
  let muOne := TwoColorComponentSwap G phi theta alpha z
  have behaviorOne :
      (∀ v : V, Sum.inl v ∉ TwoColorComponent G phi theta alpha z →
        MissingColors G muOne v = MissingColors G phi v) ∧
      (∀ v : V, Sum.inl v ∈ TwoColorComponent G phi theta alpha z →
        theta ∈ MissingColors G phi v → alpha ∈ MissingColors G muOne v) ∧
      (∀ v : V, Sum.inl v ∈ TwoColorComponent G phi theta alpha z →
        alpha ∈ MissingColors G phi v → theta ∈ MissingColors G muOne v) ∧
      (∀ v : V, ∀ c : Fin k, c ≠ theta → c ≠ alpha →
        (c ∈ MissingColors G muOne v ↔ c ∈ MissingColors G phi v)) := by
    exact TwoColorComponentSwapMissingBehavior G phi theta alpha
      hthetaAlphaNe ctx.proper z
  have prefixMissing (z : Sum V E) (rho : PartialEdgeColoring E k) (a b : Fin k) (hne : a ≠ b)
      (hp : IsProperEdgeColoring G rho)
      (helem : ColoredVertexSetElementary G rho (TreeSequenceVertexSet Bplus))
      (u v : V) (huB : u ∈ TreeSequenceVertexSet Bplus) (hvB : v ∈ TreeSequenceVertexSet Bplus)
      (hu : a ∈ MissingColors G rho u) (hv : b ∈ MissingColors G rho v)
      (hdu : Sum.inl u ∉ TwoColorComponent G rho a b z)
      (hdv : Sum.inl v ∉ TwoColorComponent G rho a b z) :
      ∀ w ∈ TreeSequenceVertexSet Bplus,
        MissingColors G (TwoColorComponentSwap G rho a b z) w = MissingColors G rho w := by
    exact helper_prefixMissing_1434 (@G) (@k) (@e0) (@Bplus) (@z) (@rho) (@a) (@b) (@hne) (@hp)
        (@helem) (@u) (@v) (@huB) (@hvB) (@hu) (@hv)
        (@hdu) (@hdv)
  have hThetaFirstBplus :
      T.vertex (HierarchyFirstMissingPosition phi T theta) ∈
        TreeSequenceVertexSet Bplus := by
    exact helper_hThetaFirstBplus_1491 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@ctx) (@D)
        (@Bplus) (@hBplusTouter) (@hABplusouter) (@hthetaFirstBound)
  have hAlphaFirstBplus :
      T.vertex (HierarchyFirstMissingPosition phi T alpha) ∈
        TreeSequenceVertexSet Bplus := by
    exact helper_hAlphaFirstBplus_1500 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@ctx) (@D) (@B)
        (@Bplus) (@penPosition) (@endPosition) (@eta) (@hBLouter) (@hPLouter) (@hBplusTouter)
        (@hAlphaFirstBound)
  have huOutsideOne : Sum.inl (T.vertex (HierarchyFirstMissingPosition phi T theta)) ∉
      TwoColorComponent G phi theta alpha z := by
    intro hh
    exact Set.disjoint_left.mp hdisjointComponent hh
      (selfComponent phi theta alpha
        (T.vertex (HierarchyFirstMissingPosition phi T theta)))
  have hvOutsideOne : Sum.inl (T.vertex (HierarchyFirstMissingPosition phi T alpha)) ∉
      TwoColorComponent G phi theta alpha z := by
    exact helper_hvOutsideOne_1516 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@ctx) (@D)
        (@hcomponentEq) (@selfComponent) (@hdisjointComponent)
  have hmissingOne : ∀ v ∈ TreeSequenceVertexSet Bplus,
      MissingColors G muOne v = MissingColors G phi v :=
    prefixMissing z phi theta alpha hthetaAlphaNe ctx.proper hElemOuter
      (T.vertex (HierarchyFirstMissingPosition phi T theta))
      (T.vertex (HierarchyFirstMissingPosition phi T alpha))
      hThetaFirstBplus hAlphaFirstBplus hthetaAtFirst hAlphaAtFirst
      huOutsideOne hvOutsideOne
  have hmissingPointwise (v : V) (hv : v ∈ TreeSequenceVertexSet Bplus) :
      MissingColors G muOne v = MissingColors G phi v := by
    as_aux_lemma =>
      clear_value muOne
      clear * - hmissingOne hv
      exact hmissingOne v hv
  exact @helper_continuation_3399 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@B)
      (@Bplus) (@lastColor) (@alphaTerminal) (@alphaUnused) (@lastPosition) (@penPosition)
      (@endPosition) (@oldRoute) (@eta) (@hetaStored) (@hetaMissing) (@hthetaGamma)
      (@hTailAtLeast) (@hellOuter) (@hBLouter) (@hPLouter) (@hBplusTouter) (@hBBplusOuter)
      (@hATouter) (@hABplusouter) (@hElemOuter) (@vAlpha) (@vertexMemOuter)
      (@hPenultimateInBplus) (@hBplusDef) (@canonicalElem) (@hAlphaEtaNe) (@hthetaInA)
      (@hetaNotA) (@hAlphaMissingBplus) (@hthetaMissingBplus) (@canonicalMissing) (@hetaFirst)
      (@hthetaFirstBound) (@hAlphaFirstBound) (@hvAlphaBplus) (@thetaAvoidsSplit)
      (@hthetaAlphaNe) (@hThetaTn) (@hChange) (@selfComponent) (@leafComponent)
      (@separateVertices) (@hthetaAtFirst) (@hAlphaAtFirst) (@hthetaTerminalNe)
      (@hdisjointComponent) (@hpath) (@behaviorOne) (@prefixMissing) (@hThetaFirstBplus)
      (@hAlphaFirstBplus) (@hmissingOne) (@hmissingPointwise)

end GoldbergSeymour.HierarchySituationTwoSubcaseThreeOnePreparation

end
