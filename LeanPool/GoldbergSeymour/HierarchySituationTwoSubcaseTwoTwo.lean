/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Data.Fintype.EquivFin
public import LeanPool.GoldbergSeymour.ChangeLemma
public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary
public import LeanPool.GoldbergSeymour.CombinedStableClosurePreserved
public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTree
public import LeanPool.GoldbergSeymour.ExtendedTashkinovTree
public import LeanPool.GoldbergSeymour.GoodHierarchy
public import LeanPool.GoldbergSeymour.GoodHierarchyReservedDisjoint
public import LeanPool.GoldbergSeymour.HierarchyCounterexample
public import LeanPool.GoldbergSeymour.HierarchyCounterexampleMeasure
public import LeanPool.GoldbergSeymour.HierarchyCounterexamplePenultimateElementary
public import LeanPool.GoldbergSeymour.HierarchyFirstMissingPosition
public import LeanPool.GoldbergSeymour.HierarchyFullTailLength
public import LeanPool.GoldbergSeymour.HierarchyFullTailPrefix
public import LeanPool.GoldbergSeymour.HierarchyMinimumCounterexampleContext
public import LeanPool.GoldbergSeymour.HierarchyNonparallelFirstEdge
public import LeanPool.GoldbergSeymour.HierarchyReplacementPresentation
public import LeanPool.GoldbergSeymour.HierarchySegmentColors
public import LeanPool.GoldbergSeymour.HierarchySituationTwoCaseOneData
public import LeanPool.GoldbergSeymour.HierarchySituationTwoCaseTwoData
public import LeanPool.GoldbergSeymour.HierarchySituationTwoCaseTwoTwoData
public import LeanPool.GoldbergSeymour.HierarchySituationTwoSubcaseOneOne
public import LeanPool.GoldbergSeymour.HierarchySituationTwoSubcaseTwoOne
public import LeanPool.GoldbergSeymour.HierarchyStageMissingColors
public import LeanPool.GoldbergSeymour.HierarchyStarredStage
public import LeanPool.GoldbergSeymour.HierarchyStoredColorsAt
public import LeanPool.GoldbergSeymour.HierarchyStoredColorsCardinality
public import LeanPool.GoldbergSeymour.HierarchyTailMissingColorExclusion
public import LeanPool.GoldbergSeymour.HierarchyWeaklyStable
public import LeanPool.GoldbergSeymour.IsOneEdgeUncolored
public import LeanPool.GoldbergSeymour.MissingColors
public import LeanPool.GoldbergSeymour.ModColoring
public import LeanPool.GoldbergSeymour.NineN
public import LeanPool.GoldbergSeymour.OrderedTreeUnion
public import LeanPool.GoldbergSeymour.SameGoodHierarchy
public import LeanPool.GoldbergSeymour.StableColoring
public import LeanPool.GoldbergSeymour.StableChangeCaseThree
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
public import LeanPool.GoldbergSeymour.HierarchyReplacementPresentationTrans
public import LeanPool.GoldbergSeymour.MissingColorIncidenceEndpoint
public import LeanPool.GoldbergSeymour.TwoColorComponentSwapMissingBehavior
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentVertexSetSubset
public import LeanPool.GoldbergSeymour.HierarchyStoredColorsAntitone
public import LeanPool.GoldbergSeymour.BaseDisplayedEdges
public import LeanPool.GoldbergSeymour.TerminalRoute

/-!
# Hierarchy Situation Two Subcase Two Two

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev helperHsameTwo964Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base)
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
   (D : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
  (∀ {c : Fin k},
    c ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex) → c ∉ TreeMissingColors phi A) →
  let Bshort : TreeSequence G e0 :=
   HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ));
  (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    HierarchyStarredStage P.counterexample.hierarchy
      (Fin.last P.counterexample.hierarchy.dividerCount) =
     A) →
  (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    HierarchyStoredColorsAt H q =
      HierarchyStoredColorsAt P.counterexample.hierarchy
       (Fin.last P.counterexample.hierarchy.dividerCount) ∧
     ∀ eta ∈ HierarchyStoredColorsAt H q,
      C.good.gamma q eta =
       P.counterexample.good.gamma (Fin.last P.counterexample.hierarchy.dividerCount) eta) →
  ∀ beta ∈ TreeMissingColors phi Bshort,
   (∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → phi (T.edge t) ≠ some beta) →
    beta ∉ HierarchyStoredColorsAt H q →
     (H.dividerCount = (0 : ℕ) →
       beta ∈ TreeMissingColors phi A →
        beta ∈ TreeMissingColors phi (ett.series.data.tree (Fin.last ett.rounds).castSucc)) →
      (beta ∉ TreeMissingColors phi A → D.theta ∉ HierarchyStoredColorsAt H q) →
       (∀ eta ∈ HierarchyStoredColorsAt H q,
         beta ∈ C.good.gamma q eta → eta = D.theta ∨ eta ∈ TreeMissingColors phi Bshort) →
        beta ≠ D.alpha →
         beta ≠ D.theta →
          let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
          beta ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T beta)) ∧
            (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ Bshort.length →
           T.vertex ib ∈ TreeSequenceVertexSet B →
            T.vertex ib ≠ T.vertex D.penultimateVertexIndex →
             T.vertex ib ≠ T.vertex D.terminalVertexIndex →
              TreeVertexOrder T (T.vertex ib) (T.vertex D.penultimateVertexIndex) →
               (beta ∉ TreeMissingColors phi A →
                 beta ∉ TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) →
                beta ∈ TreeMissingColors phi B ∧ D.alpha ∈ TreeMissingColors phi B →
                 (let H : TashkinovHierarchy ett base := C.hierarchy;
                  have q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
                  have n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
                  have A : TreeSequence G e0 := HierarchyStarredStage H q;
                  have Tnq : TreeSequence G e0 :=
                   H.stage
                    (⟨H.dividerCount,
                      by
                      have := GoldbergSeymour.TreeSequence.positive T
                      omega⟩ :
                     Fin (H.dividerCount + (2 : ℕ)));
                  have Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
                  have Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
                  have Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q;
                  have va : V := T.vertex (HierarchyFirstMissingPosition phi T beta);
                  have vb : V := T.vertex (HierarchyFirstMissingPosition phi T D.alpha);
                  have sameComponent : Prop :=
                   TwoColorComponent G phi beta D.alpha (Sum.inl va) =
                    TwoColorComponent G phi beta D.alpha (Sum.inl vb);
                  ((0 : ℕ) < H.dividerCount ∧
                     (beta ∈ TreeMissingColors phi Tnq ∨
                      Disjoint (insert beta ({ D.alpha } : Finset (Fin k)) : Finset (Fin k))
                       Dnq) →
                    sameComponent) ∧
                   (H.dividerCount = (0 : ℕ) ∧
                      (beta ∈ TreeMissingColors phi Tn ∨
                       Disjoint (insert beta ({ D.alpha } : Finset (Fin k)) : Finset (Fin k))
                        Dn) →
                     sameComponent) ∧
                    (beta ∈ TreeMissingColors phi A ∧
                      TreeColorSetClosed G phi A ({ beta } : Finset (Fin k)) →
                     sameComponent ∧ TreeInterchangeable G A phi beta D.alpha)) →
                  TwoColorComponent G phi beta D.alpha (Sum.inl (T.vertex ib)) =
                    TwoColorComponent G phi beta D.alpha
                     (Sum.inl (T.vertex D.penultimateVertexIndex)) →
                   let z : V ⊕ E := Sum.inl (T.vertex D.terminalVertexIndex);
                   let muOne : PartialEdgeColoring E k :=
                    TwoColorComponentSwap G phi beta D.alpha z;
                   Disjoint
                     (TwoColorComponent G phi beta D.alpha
                      (Sum.inl (T.vertex D.terminalVertexIndex)))
                     (TwoColorComponent G phi beta D.alpha (Sum.inl (T.vertex ib))) →
                    TwoColorPathComponent G phi beta D.alpha z →
                     Sum.inl (T.vertex ib) ∉ TwoColorComponent G phi beta D.alpha z →
                      Sum.inl (T.vertex D.penultimateVertexIndex) ∉
                        TwoColorComponent G phi beta D.alpha z →
                       (∀ w ∈ TreeSequenceVertexSet B,
                         MissingColors G (TwoColorComponentSwap G phi beta D.alpha z) w =
                          MissingColors G phi w) →
                        (∀ (t : Fin T.length),
                          A.length ≤ (↑t : ℕ) → muOne (T.edge t) = phi (T.edge t)) →
                         (∀ c ∈ HierarchyStoredColorsAt H q,
                           HierarchyFirstMissingPosition muOne T c =
                            HierarchyFirstMissingPosition phi T c) →
                          (beta ∈ TreeMissingColors phi A →
                            (0 : ℕ) < H.dividerCount ∧
                              beta ∈
                               TreeMissingColors phi
                                (H.stage
                                 (⟨H.dividerCount,
                                   by
                                   have := GoldbergSeymour.TreeSequence.positive T
                                   omega⟩ :
                                  Fin (H.dividerCount + (2 : ℕ)))) ∨
                             H.dividerCount = (0 : ℕ) ∧
                              beta ∈
                               TreeMissingColors phi
                                (ett.series.data.tree (Fin.last ett.rounds).castSucc)) →
                           ∀ (corrOne : CorrespondingExtendedTashkinovTree G k e0 ett muOne T),
                            MaximumProperty corrOne.replacementETT →
                             ∀ (baseOne : HierarchyBase corrOne.replacementETT muOne)
                              (KOne : TashkinovHierarchy corrOne.replacementETT baseOne)
                              (goodOne : GoodHierarchy KOne),
                              SameGoodHierarchy C.good goodOne →
                               beta ∈ MissingColors G muOne (T.vertex D.terminalVertexIndex) →
                                ∀
                                 (POne :
                                  HierarchyReplacementPresentation G k e0 input T phi ett base C
                                   ctx),
                                 POne.coloring = muOne →
                                  let rho : PartialEdgeColoring E k := POne.coloring;
                                  let ettOne :
                                   ExtendedTashkinovTree G k e0
                                    POne.corresponding.replacementInput T POne.coloring :=
                                   POne.corresponding.replacementETT;
                                  let baseOne' :
                                   HierarchyBase POne.corresponding.replacementETT
                                    POne.coloring :=
                                   POne.replacementBase;
                                  let COne' : HierarchyCounterexample POne.replacementBase :=
                                   POne.counterexample;
                                  let HOne :
                                   TashkinovHierarchy POne.corresponding.replacementETT
                                    POne.replacementBase :=
                                   COne'.hierarchy;
                                  let qOne : Fin (HOne.dividerCount + (1 : ℕ)) :=
                                   Fin.last HOne.dividerCount;
                                  TreeMissingColors rho A = TreeMissingColors phi A →
                                   beta ∉ HierarchyStoredColorsAt HOne qOne →
                                    beta ∉
                                      MissingColors G rho (T.vertex D.penultimateVertexIndex) →
                                     beta ∈
                                       MissingColors G rho (T.vertex D.terminalVertexIndex) →
                                      beta ∈ MissingColors G rho (T.vertex ib) →
                                       HierarchyFirstMissingPosition rho T beta = ib →
                                        HierarchyFirstMissingPosition rho T D.theta =
                                          D.penultimateVertexIndex →
                                         (∀ (t : Fin T.length),
                                           A.length ≤ (↑t : ℕ) → rho (T.edge t) ≠ some beta) →
                                          (beta ∈ TreeMissingColors phi A →
                                            (0 : ℕ) < HOne.dividerCount ∧
                                              beta ∈
                                               TreeMissingColors rho
                                                (HOne.stage
                                                 (⟨HOne.dividerCount,
                                                   by
                                                   have :=
                                                    GoldbergSeymour.TreeSequence.positive T
                                                   omega⟩ :
                                                  Fin (HOne.dividerCount + (2 : ℕ)))) ∨
                                             HOne.dividerCount = (0 : ℕ) ∧
                                              beta ∈
                                               TreeMissingColors rho
                                                (ettOne.series.data.tree
                                                 (Fin.last ettOne.rounds).castSucc)) →
                                           beta ∈ TreeMissingColors rho B ∧
                                             D.theta ∈ TreeMissingColors rho B →
                                            (let H : TashkinovHierarchy ettOne baseOne' :=
                                              COne'.hierarchy;
                                             have q : Fin (H.dividerCount + (1 : ℕ)) :=
                                              Fin.last H.dividerCount;
                                             have n : Fin (ettOne.rounds + (1 : ℕ)) :=
                                              Fin.last ettOne.rounds;
                                             have A : TreeSequence G e0 :=
                                              HierarchyStarredStage H q;
                                             have Tnq : TreeSequence G e0 :=
                                              H.stage
                                               (⟨H.dividerCount,
                                                 by
                                                 have := GoldbergSeymour.TreeSequence.positive T
                                                 omega⟩ :
                                                Fin (H.dividerCount + (2 : ℕ)));
                                             have Tn : TreeSequence G e0 :=
                                              ettOne.series.data.tree n.castSucc;
                                             have Dn : Finset (Fin k) :=
                                              TashkinovStoredColors ettOne.series.data n;
                                             have Dnq : Finset (Fin k) :=
                                              HierarchyStoredColorsAt H q;
                                             have va : V :=
                                              T.vertex
                                               (HierarchyFirstMissingPosition rho T beta);
                                             have vb : V :=
                                              T.vertex
                                               (HierarchyFirstMissingPosition rho T D.theta);
                                             have sameComponent : Prop :=
                                              TwoColorComponent G rho beta D.theta
                                                (Sum.inl va) =
                                               TwoColorComponent G rho beta D.theta
                                                (Sum.inl vb);
                                             ((0 : ℕ) < H.dividerCount ∧
                                                (beta ∈ TreeMissingColors rho Tnq ∨
                                                 Disjoint
                                                  (insert beta ({ D.theta } : Finset (Fin k)) :
                                                   Finset (Fin k))
                                                  Dnq) →
                                               sameComponent) ∧
                                              (H.dividerCount = (0 : ℕ) ∧
                                                 (beta ∈ TreeMissingColors rho Tn ∨
                                                  Disjoint
                                                   (insert beta ({ D.theta } : Finset (Fin k)) :
                                                    Finset (Fin k))
                                                   Dn) →
                                                sameComponent) ∧
                                               (beta ∈ TreeMissingColors rho A ∧
                                                 TreeColorSetClosed G rho A
                                                  ({ beta } : Finset (Fin k)) →
                                                sameComponent ∧
                                                 TreeInterchangeable G A rho beta D.theta)) →
                                             TwoColorComponent G rho beta D.theta
                                               (Sum.inl (T.vertex ib)) =
                                              TwoColorComponent G rho beta D.theta
                                               (Sum.inl (T.vertex D.penultimateVertexIndex))

private abbrev helperBranch3242Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base)
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
   (D : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
  (2 : ℕ) ≤ T.length - A.length →
  B.length + (1 : ℕ) = T.length →
  TreeSequenceInitialSegment B T →
  (H.dividerCount = (0 : ℕ) → A = base.core) →
  TreeSequenceInitialSegment A T →
  TreeSequenceInitialSegment A B →
  B.vertex (Fin.last B.length) = T.vertex D.penultimateVertexIndex →
  T.vertex D.penultimateVertexIndex ∈ TreeSequenceVertexSet B →
  ColoredVertexSetElementary G phi (TreeSequenceVertexSet B) →
  (∀ {c : Fin k},
    c ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex) →
     c ∉ TreeMissingColors phi A) →
  (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    HierarchyStarredStage P.counterexample.hierarchy
      (Fin.last P.counterexample.hierarchy.dividerCount) =
     A) →
  (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    HierarchyFullTailPrefix P.counterexample
      (HierarchyFullTailLength P.counterexample - (1 : ℕ)) =
     B) →
  (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    P.corresponding.replacementETT.series.data.tree
      (Fin.last P.corresponding.replacementETT.rounds).castSucc =
     ett.series.data.tree (Fin.last ett.rounds).castSucc) →
  (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    HierarchyStoredColorsAt H q =
      HierarchyStoredColorsAt P.counterexample.hierarchy
       (Fin.last P.counterexample.hierarchy.dividerCount) ∧
     ∀ eta ∈ HierarchyStoredColorsAt H q,
      C.good.gamma q eta =
       P.counterexample.good.gamma (Fin.last P.counterexample.hierarchy.dividerCount)
        eta) →
  (∀ {X Y F : TreeSequence G e0},
    TreeSequenceInitialSegment X F →
     TreeSequenceInitialSegment Y F →
      X.length ≤ Y.length → TreeSequenceInitialSegment X Y) →
  base.core.length ≤ A.length →
  (∀ (X : TreeSequence G e0),
    TreeSequenceInitialSegment X T →
     ∀ (t : Fin T.length), (↑t : ℕ) = X.length → TreeIncidentEdge X (T.edge t)) →
  (∀ {input' : PartialEdgeColoring E k} (rho sigma : PartialEdgeColoring E k)
    (ett' : ExtendedTashkinovTree G k e0 input' T rho)
    (base' : HierarchyBase ett' rho) (K : TashkinovHierarchy ett' base'),
    HierarchyWeaklyStable K (Fin.last K.dividerCount) sigma →
     K.dividerCount = (0 : ℕ) →
      StableColoring (ett'.series.data.tree (Fin.last ett'.rounds).castSucc)
       (TashkinovStoredColors ett'.series.data (Fin.last ett'.rounds)) rho
       sigma) →
  (∀ {input' : PartialEdgeColoring E k} (old new : PartialEdgeColoring E k)
    (ett' : ExtendedTashkinovTree G k e0 input' T old)
    (base' : HierarchyBase ett' old) (K : TashkinovHierarchy ett' base'),
    HierarchyWeaklyStable K (Fin.last K.dividerCount) new →
     IsOneEdgeUncolored old e0 →
      IsOneEdgeUncolored new e0 →
       ∀ (t : Fin (HierarchyStarredStage K (Fin.last K.dividerCount)).length),
        new ((HierarchyStarredStage K (Fin.last K.dividerCount)).edge t) =
         old ((HierarchyStarredStage K (Fin.last K.dividerCount)).edge t)) →
  ∀ (beta : Fin k),
  beta ≠ D.theta →
  let ib : Fin (T.length + (1 : ℕ)) :=
   HierarchyFirstMissingPosition phi T beta;
  T.vertex ib ∈ TreeSequenceVertexSet B →
  let z : V ⊕ E := Sum.inl (T.vertex D.terminalVertexIndex);
  let muOne : PartialEdgeColoring E k :=
   TwoColorComponentSwap G phi beta D.alpha z;
  (∀ (t : Fin T.length),
    A.length ≤ (↑t : ℕ) → muOne (T.edge t) = phi (T.edge t)) →
  ∀
   (POne :
    HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
  POne.coloring = muOne →
  let rho : PartialEdgeColoring E k := POne.coloring;
  let ettOne :
   ExtendedTashkinovTree G k e0 POne.corresponding.replacementInput T
    POne.coloring :=
   POne.corresponding.replacementETT;
  let _ : HierarchyBase POne.corresponding.replacementETT POne.coloring :=
   POne.replacementBase;
  let COne' : HierarchyCounterexample POne.replacementBase :=
   POne.counterexample;
  let _ :
   HierarchyMinimumCounterexampleContext G k e0
    POne.corresponding.replacementInput T POne.coloring
    POne.corresponding.replacementETT POne.replacementBase
    POne.counterexample :=
   POne.minimumContext;
  let HOne :
   TashkinovHierarchy POne.corresponding.replacementETT
    POne.replacementBase :=
   COne'.hierarchy;
  let qOne : Fin (HOne.dividerCount + (1 : ℕ)) :=
   Fin.last HOne.dividerCount;
  ColoredVertexSetElementary G rho (TreeSequenceVertexSet B) →
  D.theta ∈ MissingColors G rho (T.vertex D.penultimateVertexIndex) →
  beta ∈ MissingColors G rho (T.vertex ib) →
  HierarchyFirstMissingPosition rho T beta = ib →
  (∀ (t : Fin T.length),
    A.length ≤ (↑t : ℕ) → rho (T.edge t) ≠ some beta) →
  (beta ∈ TreeMissingColors phi A →
    (0 : ℕ) < HOne.dividerCount ∧
      beta ∈
       TreeMissingColors rho
        (HOne.stage
         (⟨HOne.dividerCount,
           by
           have := GoldbergSeymour.TreeSequence.positive T
           omega⟩ :
          Fin (HOne.dividerCount + (2 : ℕ)))) ∨
     HOne.dividerCount = (0 : ℕ) ∧
      beta ∈
       TreeMissingColors rho
        (ettOne.series.data.tree
         (Fin.last ettOne.rounds).castSucc)) →
  beta ∈ TreeMissingColors rho B ∧
    D.theta ∈ TreeMissingColors rho B →
  Disjoint
    (TwoColorComponent G rho beta D.theta
     (Sum.inl (T.vertex D.terminalVertexIndex)))
    (TwoColorComponent G rho beta D.theta
     (Sum.inl (T.vertex ib))) →
  let muTwo : PartialEdgeColoring E k :=
   TwoColorComponentSwap G rho beta D.theta z;
  TwoColorPathComponent G rho beta D.theta z →
  (∀ w ∈ TreeSequenceVertexSet B,
    MissingColors G (TwoColorComponentSwap G rho beta D.theta z)
      w =
     MissingColors G rho w) →
  (∀ c ∈ HierarchyStoredColorsAt HOne qOne,
    HierarchyFirstMissingPosition muTwo T c =
     HierarchyFirstMissingPosition rho T c) →
  TashkinovAugmentationSequence rho B T →
  (∀ c ∈ HierarchyStoredColorsAt HOne qOne,
    beta ∈ POne.counterexample.good.gamma qOne c ∨
      D.theta ∈ POne.counterexample.good.gamma qOne c →
     (↑(HierarchyFirstMissingPosition rho T c) : ℕ) ≤
      B.length) →
  beta ∈ TreeMissingColors phi A →
  ∃ (corrTwo :
   CorrespondingExtendedTashkinovTree G k e0 ettOne muTwo
    T),
   MaximumProperty corrTwo.replacementETT ∧
    ∃ (baseTwo : HierarchyBase corrTwo.replacementETT muTwo)
     (KTwo :
     TashkinovHierarchy corrTwo.replacementETT baseTwo)
     (goodTwo : GoodHierarchy KTwo),
     SameGoodHierarchy COne'.good goodTwo

private abbrev helperHsameTwo3799Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base)
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
   (D : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
  (∀ {c : Fin k},
    c ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex) → c ∉ TreeMissingColors phi A) →
  let Bshort : TreeSequence G e0 :=
   HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ));
  (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    HierarchyStarredStage P.counterexample.hierarchy
      (Fin.last P.counterexample.hierarchy.dividerCount) =
     A) →
  (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    HierarchyStoredColorsAt H q =
      HierarchyStoredColorsAt P.counterexample.hierarchy
       (Fin.last P.counterexample.hierarchy.dividerCount) ∧
     ∀ eta ∈ HierarchyStoredColorsAt H q,
      C.good.gamma q eta =
       P.counterexample.good.gamma (Fin.last P.counterexample.hierarchy.dividerCount) eta) →
  ∀ beta ∈ TreeMissingColors phi Bshort,
   (∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → phi (T.edge t) ≠ some beta) →
    beta ∉ HierarchyStoredColorsAt H q →
     (H.dividerCount = (0 : ℕ) →
       beta ∈ TreeMissingColors phi A →
        beta ∈ TreeMissingColors phi (ett.series.data.tree (Fin.last ett.rounds).castSucc)) →
      (beta ∉ TreeMissingColors phi A → D.theta ∉ HierarchyStoredColorsAt H q) →
       (∀ eta ∈ HierarchyStoredColorsAt H q,
         beta ∈ C.good.gamma q eta → eta = D.theta ∨ eta ∈ TreeMissingColors phi Bshort) →
        beta ≠ D.alpha →
         beta ≠ D.theta →
          let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
          beta ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T beta)) ∧
            (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ Bshort.length →
           T.vertex ib ∈ TreeSequenceVertexSet B →
            T.vertex ib ≠ T.vertex D.penultimateVertexIndex →
             T.vertex ib ≠ T.vertex D.terminalVertexIndex →
              TreeVertexOrder T (T.vertex ib) (T.vertex D.penultimateVertexIndex) →
               (beta ∉ TreeMissingColors phi A →
                 beta ∉ TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) →
                beta ∈ TreeMissingColors phi B ∧ D.alpha ∈ TreeMissingColors phi B →
                 (let H : TashkinovHierarchy ett base := C.hierarchy;
                  have q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
                  have n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
                  have A : TreeSequence G e0 := HierarchyStarredStage H q;
                  have Tnq : TreeSequence G e0 :=
                   H.stage
                    (⟨H.dividerCount,
                      by
                      have := GoldbergSeymour.TreeSequence.positive T
                      omega⟩ :
                     Fin (H.dividerCount + (2 : ℕ)));
                  have Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
                  have Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
                  have Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q;
                  have va : V := T.vertex (HierarchyFirstMissingPosition phi T beta);
                  have vb : V := T.vertex (HierarchyFirstMissingPosition phi T D.alpha);
                  have sameComponent : Prop :=
                   TwoColorComponent G phi beta D.alpha (Sum.inl va) =
                    TwoColorComponent G phi beta D.alpha (Sum.inl vb);
                  ((0 : ℕ) < H.dividerCount ∧
                     (beta ∈ TreeMissingColors phi Tnq ∨
                      Disjoint (insert beta ({ D.alpha } : Finset (Fin k)) : Finset (Fin k))
                       Dnq) →
                    sameComponent) ∧
                   (H.dividerCount = (0 : ℕ) ∧
                      (beta ∈ TreeMissingColors phi Tn ∨
                       Disjoint (insert beta ({ D.alpha } : Finset (Fin k)) : Finset (Fin k))
                        Dn) →
                     sameComponent) ∧
                    (beta ∈ TreeMissingColors phi A ∧
                      TreeColorSetClosed G phi A ({ beta } : Finset (Fin k)) →
                     sameComponent ∧ TreeInterchangeable G A phi beta D.alpha)) →
                  TwoColorComponent G phi beta D.alpha (Sum.inl (T.vertex ib)) =
                    TwoColorComponent G phi beta D.alpha
                     (Sum.inl (T.vertex D.penultimateVertexIndex)) →
                   let z : V ⊕ E := Sum.inl (T.vertex D.terminalVertexIndex);
                   let muOne : PartialEdgeColoring E k :=
                    TwoColorComponentSwap G phi beta D.alpha z;
                   Disjoint
                     (TwoColorComponent G phi beta D.alpha
                      (Sum.inl (T.vertex D.terminalVertexIndex)))
                     (TwoColorComponent G phi beta D.alpha (Sum.inl (T.vertex ib))) →
                    TwoColorPathComponent G phi beta D.alpha z →
                     Sum.inl (T.vertex ib) ∉ TwoColorComponent G phi beta D.alpha z →
                      Sum.inl (T.vertex D.penultimateVertexIndex) ∉
                        TwoColorComponent G phi beta D.alpha z →
                       (∀ w ∈ TreeSequenceVertexSet B,
                         MissingColors G (TwoColorComponentSwap G phi beta D.alpha z) w =
                          MissingColors G phi w) →
                        (∀ (t : Fin T.length),
                          A.length ≤ (↑t : ℕ) → muOne (T.edge t) = phi (T.edge t)) →
                         (∀ c ∈ HierarchyStoredColorsAt H q,
                           HierarchyFirstMissingPosition muOne T c =
                            HierarchyFirstMissingPosition phi T c) →
                          (beta ∈ TreeMissingColors phi A →
                            (0 : ℕ) < H.dividerCount ∧
                              beta ∈
                               TreeMissingColors phi
                                (H.stage
                                 (⟨H.dividerCount,
                                   by
                                   have := GoldbergSeymour.TreeSequence.positive T
                                   omega⟩ :
                                  Fin (H.dividerCount + (2 : ℕ)))) ∨
                             H.dividerCount = (0 : ℕ) ∧
                              beta ∈
                               TreeMissingColors phi
                                (ett.series.data.tree (Fin.last ett.rounds).castSucc)) →
                           ∀ (corrOne : CorrespondingExtendedTashkinovTree G k e0 ett muOne T),
                            MaximumProperty corrOne.replacementETT →
                             ∀ (baseOne : HierarchyBase corrOne.replacementETT muOne)
                              (KOne : TashkinovHierarchy corrOne.replacementETT baseOne)
                              (goodOne : GoodHierarchy KOne),
                              SameGoodHierarchy C.good goodOne →
                               beta ∈ MissingColors G muOne (T.vertex D.terminalVertexIndex) →
                                ∀
                                 (POne :
                                  HierarchyReplacementPresentation G k e0 input T phi ett base C
                                   ctx),
                                 POne.coloring = muOne →
                                  let rho : PartialEdgeColoring E k := POne.coloring;
                                  let ettOne :
                                   ExtendedTashkinovTree G k e0
                                    POne.corresponding.replacementInput T POne.coloring :=
                                   POne.corresponding.replacementETT;
                                  let baseOne' :
                                   HierarchyBase POne.corresponding.replacementETT
                                    POne.coloring :=
                                   POne.replacementBase;
                                  let COne' : HierarchyCounterexample POne.replacementBase :=
                                   POne.counterexample;
                                  let HOne :
                                   TashkinovHierarchy POne.corresponding.replacementETT
                                    POne.replacementBase :=
                                   COne'.hierarchy;
                                  let qOne : Fin (HOne.dividerCount + (1 : ℕ)) :=
                                   Fin.last HOne.dividerCount;
                                  TreeMissingColors rho A = TreeMissingColors phi A →
                                   beta ∉ HierarchyStoredColorsAt HOne qOne →
                                    beta ∉
                                      MissingColors G rho (T.vertex D.penultimateVertexIndex) →
                                     beta ∈
                                       MissingColors G rho (T.vertex D.terminalVertexIndex) →
                                      beta ∈ MissingColors G rho (T.vertex ib) →
                                       HierarchyFirstMissingPosition rho T beta = ib →
                                        HierarchyFirstMissingPosition rho T D.theta =
                                          D.penultimateVertexIndex →
                                         (∀ (t : Fin T.length),
                                           A.length ≤ (↑t : ℕ) → rho (T.edge t) ≠ some beta) →
                                          (beta ∈ TreeMissingColors phi A →
                                            (0 : ℕ) < HOne.dividerCount ∧
                                              beta ∈
                                               TreeMissingColors rho
                                                (HOne.stage
                                                 (⟨HOne.dividerCount,
                                                   by
                                                   have :=
                                                    GoldbergSeymour.TreeSequence.positive T
                                                   omega⟩ :
                                                  Fin (HOne.dividerCount + (2 : ℕ)))) ∨
                                             HOne.dividerCount = (0 : ℕ) ∧
                                              beta ∈
                                               TreeMissingColors rho
                                                (ettOne.series.data.tree
                                                 (Fin.last ettOne.rounds).castSucc)) →
                                           beta ∈ TreeMissingColors rho B ∧
                                             D.theta ∈ TreeMissingColors rho B →
                                            (let H : TashkinovHierarchy ettOne baseOne' :=
                                              COne'.hierarchy;
                                             have q : Fin (H.dividerCount + (1 : ℕ)) :=
                                              Fin.last H.dividerCount;
                                             have n : Fin (ettOne.rounds + (1 : ℕ)) :=
                                              Fin.last ettOne.rounds;
                                             have A : TreeSequence G e0 :=
                                              HierarchyStarredStage H q;
                                             have Tnq : TreeSequence G e0 :=
                                              H.stage
                                               (⟨H.dividerCount,
                                                 by
                                                 have := GoldbergSeymour.TreeSequence.positive T
                                                 omega⟩ :
                                                Fin (H.dividerCount + (2 : ℕ)));
                                             have Tn : TreeSequence G e0 :=
                                              ettOne.series.data.tree n.castSucc;
                                             have Dn : Finset (Fin k) :=
                                              TashkinovStoredColors ettOne.series.data n;
                                             have Dnq : Finset (Fin k) :=
                                              HierarchyStoredColorsAt H q;
                                             have va : V :=
                                              T.vertex
                                               (HierarchyFirstMissingPosition rho T beta);
                                             have vb : V :=
                                              T.vertex
                                               (HierarchyFirstMissingPosition rho T D.theta);
                                             have sameComponent : Prop :=
                                              TwoColorComponent G rho beta D.theta
                                                (Sum.inl va) =
                                               TwoColorComponent G rho beta D.theta
                                                (Sum.inl vb);
                                             ((0 : ℕ) < H.dividerCount ∧
                                                (beta ∈ TreeMissingColors rho Tnq ∨
                                                 Disjoint
                                                  (insert beta ({ D.theta } : Finset (Fin k)) :
                                                   Finset (Fin k))
                                                  Dnq) →
                                               sameComponent) ∧
                                              (H.dividerCount = (0 : ℕ) ∧
                                                 (beta ∈ TreeMissingColors rho Tn ∨
                                                  Disjoint
                                                   (insert beta ({ D.theta } : Finset (Fin k)) :
                                                    Finset (Fin k))
                                                   Dn) →
                                                sameComponent) ∧
                                               (beta ∈ TreeMissingColors rho A ∧
                                                 TreeColorSetClosed G rho A
                                                  ({ beta } : Finset (Fin k)) →
                                                sameComponent ∧
                                                 TreeInterchangeable G A rho beta D.theta)) →
                                             TwoColorComponent G rho beta D.theta
                                               (Sum.inl (T.vertex ib)) =
                                              TwoColorComponent G rho beta D.theta
                                               (Sum.inl (T.vertex D.penultimateVertexIndex))

private abbrev helperContinuation4157Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base)
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
   (D : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
  (2 : ℕ) ≤ T.length - A.length →
  B.length + (1 : ℕ) = T.length →
  TreeSequenceInitialSegment B T →
  ((0 : ℕ) < H.dividerCount →
    A =
     H.stage
      (⟨H.dividerCount, by
        have := GoldbergSeymour.TreeSequence.positive T
        omega⟩ :
       Fin (H.dividerCount + (2 : ℕ)))) →
  (H.dividerCount = (0 : ℕ) → A = base.core) →
  TreeSequenceInitialSegment A T →
  TreeSequenceInitialSegment A B →
  B.vertex (Fin.last B.length) = T.vertex D.penultimateVertexIndex →
  T.vertex D.penultimateVertexIndex ∈ TreeSequenceVertexSet B →
  ColoredVertexSetElementary G phi (TreeSequenceVertexSet B) →
  HierarchyFirstMissingPosition phi T D.alpha = D.penultimateVertexIndex →
  HierarchyFirstMissingPosition phi T D.theta = D.penultimateVertexIndex →
  (∀ {c : Fin k},
    c ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex) →
     c ∉ TreeMissingColors phi A) →
  D.alpha ∉ TashkinovStoredColors ett.series.data (Fin.last ett.rounds) →
  let Bshort : TreeSequence G e0 :=
   HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ));
  Bshort.length + (2 : ℕ) = T.length →
  TreeSequenceInitialSegment Bshort T →
  TreeSequenceInitialSegment Bshort B →
  (∀ {c : Fin k},
    c ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex) →
     c ∉ TreeMissingColors phi Bshort) →
  Incident G (T.vertex D.terminalVertexIndex) (T.edge D.lastEdgeIndex) →
  (∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → phi (T.edge t) ≠ some D.alpha) →
  (∀ (rho : PartialEdgeColoring E k) (X : TreeSequence G e0),
    TreeSequenceInitialSegment X T →
     ∀ c ∈ TreeMissingColors rho X,
      c ∈
        MissingColors G rho
         (T.vertex (HierarchyFirstMissingPosition rho T c)) ∧
       (↑(HierarchyFirstMissingPosition rho T c) : ℕ) ≤ X.length) →
  (∀ (rho : PartialEdgeColoring E k) (a b : Fin k) (v : V),
    Sum.inl v ∈ TwoColorComponent G rho a b (Sum.inl v)) →
  (∀ (rho : PartialEdgeColoring E k) {X Y : TreeSequence G e0},
    TreeSequenceInitialSegment X Y →
     TreeMissingColors rho X ⊆ TreeMissingColors rho Y) →
  (∀ (rho : PartialEdgeColoring E k) (X Y : TreeSequence G e0),
    ∀
     c ∉
      (TreeSequenceVertexSet X \ TreeSequenceVertexSet Y).biUnion
       fun (v : V) ↦ MissingColors G rho v,
     c ∈ TreeMissingColors rho X → c ∈ TreeMissingColors rho Y) →
  (∀ (rho : PartialEdgeColoring E k) (a b : Fin k),
    a ≠ b →
     IsProperEdgeColoring G rho →
      ∀ (v : V),
       a ∈ MissingColors G rho v ∨ b ∈ MissingColors G rho v →
        ((TwoColorIncidenceGraph G rho a b).neighborSet
          (Sum.inl v)).Subsingleton) →
  (∀ (rho : PartialEdgeColoring E k) (a b : Fin k),
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
  (∀ (z : V ⊕ E) (rho : PartialEdgeColoring E k) (a b : Fin k),
    a ≠ b →
     IsProperEdgeColoring G rho →
      ColoredVertexSetElementary G rho (TreeSequenceVertexSet B) →
       ∀ (u v : V),
        u ∈ TreeSequenceVertexSet B →
         v ∈ TreeSequenceVertexSet B →
          a ∈ MissingColors G rho u →
           b ∈ MissingColors G rho v →
            Sum.inl u ∉ TwoColorComponent G rho a b z →
             Sum.inl v ∉ TwoColorComponent G rho a b z →
              ∀ w ∈ TreeSequenceVertexSet B,
               MissingColors G (TwoColorComponentSwap G rho a b z) w =
                MissingColors G rho w) →
  (∀ (rho sigma : PartialEdgeColoring E k) (c : Fin k),
    ColoredVertexSetElementary G rho (TreeSequenceVertexSet B) →
     (∀ v ∈ TreeSequenceVertexSet B,
       MissingColors G sigma v = MissingColors G rho v) →
      c ∈ TreeMissingColors rho B →
       HierarchyFirstMissingPosition sigma T c =
        HierarchyFirstMissingPosition rho T c) →
  False

private abbrev helperHsameTwo4804Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base)
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
   (D : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
  (∀ {c : Fin k},
    c ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex) → c ∉ TreeMissingColors phi A) →
  let Bshort : TreeSequence G e0 :=
   HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ));
  (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    HierarchyStarredStage P.counterexample.hierarchy
      (Fin.last P.counterexample.hierarchy.dividerCount) =
     A) →
  (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    HierarchyStoredColorsAt H q =
      HierarchyStoredColorsAt P.counterexample.hierarchy
       (Fin.last P.counterexample.hierarchy.dividerCount) ∧
     ∀ eta ∈ HierarchyStoredColorsAt H q,
      C.good.gamma q eta =
       P.counterexample.good.gamma (Fin.last P.counterexample.hierarchy.dividerCount) eta) →
  ∀ beta ∈ TreeMissingColors phi Bshort,
   (∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → phi (T.edge t) ≠ some beta) →
    beta ∉ HierarchyStoredColorsAt H q →
     (H.dividerCount = (0 : ℕ) →
       beta ∈ TreeMissingColors phi A →
        beta ∈ TreeMissingColors phi (ett.series.data.tree (Fin.last ett.rounds).castSucc)) →
      (beta ∉ TreeMissingColors phi A → D.theta ∉ HierarchyStoredColorsAt H q) →
       (∀ eta ∈ HierarchyStoredColorsAt H q,
         beta ∈ C.good.gamma q eta → eta = D.theta ∨ eta ∈ TreeMissingColors phi Bshort) →
        beta ≠ D.alpha →
         beta ≠ D.theta →
          let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
          beta ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T beta)) ∧
            (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ Bshort.length →
           T.vertex ib ∈ TreeSequenceVertexSet B →
            T.vertex ib ≠ T.vertex D.penultimateVertexIndex →
             T.vertex ib ≠ T.vertex D.terminalVertexIndex →
              TreeVertexOrder T (T.vertex ib) (T.vertex D.penultimateVertexIndex) →
               (beta ∉ TreeMissingColors phi A →
                 beta ∉ TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) →
                beta ∈ TreeMissingColors phi B ∧ D.alpha ∈ TreeMissingColors phi B →
                 (let H : TashkinovHierarchy ett base := C.hierarchy;
                  have q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
                  have n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
                  have A : TreeSequence G e0 := HierarchyStarredStage H q;
                  have Tnq : TreeSequence G e0 :=
                   H.stage
                    (⟨H.dividerCount,
                      by
                      have := GoldbergSeymour.TreeSequence.positive T
                      omega⟩ :
                     Fin (H.dividerCount + (2 : ℕ)));
                  have Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
                  have Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
                  have Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q;
                  have va : V := T.vertex (HierarchyFirstMissingPosition phi T beta);
                  have vb : V := T.vertex (HierarchyFirstMissingPosition phi T D.alpha);
                  have sameComponent : Prop :=
                   TwoColorComponent G phi beta D.alpha (Sum.inl va) =
                    TwoColorComponent G phi beta D.alpha (Sum.inl vb);
                  ((0 : ℕ) < H.dividerCount ∧
                     (beta ∈ TreeMissingColors phi Tnq ∨
                      Disjoint (insert beta ({ D.alpha } : Finset (Fin k)) : Finset (Fin k))
                       Dnq) →
                    sameComponent) ∧
                   (H.dividerCount = (0 : ℕ) ∧
                      (beta ∈ TreeMissingColors phi Tn ∨
                       Disjoint (insert beta ({ D.alpha } : Finset (Fin k)) : Finset (Fin k))
                        Dn) →
                     sameComponent) ∧
                    (beta ∈ TreeMissingColors phi A ∧
                      TreeColorSetClosed G phi A ({ beta } : Finset (Fin k)) →
                     sameComponent ∧ TreeInterchangeable G A phi beta D.alpha)) →
                  TwoColorComponent G phi beta D.alpha (Sum.inl (T.vertex ib)) =
                    TwoColorComponent G phi beta D.alpha
                     (Sum.inl (T.vertex D.penultimateVertexIndex)) →
                   let z : V ⊕ E := Sum.inl (T.vertex D.terminalVertexIndex);
                   let muOne : PartialEdgeColoring E k :=
                    TwoColorComponentSwap G phi beta D.alpha z;
                   Disjoint
                     (TwoColorComponent G phi beta D.alpha
                      (Sum.inl (T.vertex D.terminalVertexIndex)))
                     (TwoColorComponent G phi beta D.alpha (Sum.inl (T.vertex ib))) →
                    TwoColorPathComponent G phi beta D.alpha z →
                     Sum.inl (T.vertex ib) ∉ TwoColorComponent G phi beta D.alpha z →
                      Sum.inl (T.vertex D.penultimateVertexIndex) ∉
                        TwoColorComponent G phi beta D.alpha z →
                       (∀ w ∈ TreeSequenceVertexSet B,
                         MissingColors G (TwoColorComponentSwap G phi beta D.alpha z) w =
                          MissingColors G phi w) →
                        (∀ (t : Fin T.length),
                          A.length ≤ (↑t : ℕ) → muOne (T.edge t) = phi (T.edge t)) →
                         (∀ c ∈ HierarchyStoredColorsAt H q,
                           HierarchyFirstMissingPosition muOne T c =
                            HierarchyFirstMissingPosition phi T c) →
                          (beta ∈ TreeMissingColors phi A →
                            (0 : ℕ) < H.dividerCount ∧
                              beta ∈
                               TreeMissingColors phi
                                (H.stage
                                 (⟨H.dividerCount,
                                   by
                                   have := GoldbergSeymour.TreeSequence.positive T
                                   omega⟩ :
                                  Fin (H.dividerCount + (2 : ℕ)))) ∨
                             H.dividerCount = (0 : ℕ) ∧
                              beta ∈
                               TreeMissingColors phi
                                (ett.series.data.tree (Fin.last ett.rounds).castSucc)) →
                           ∀ (corrOne : CorrespondingExtendedTashkinovTree G k e0 ett muOne T),
                            MaximumProperty corrOne.replacementETT →
                             ∀ (baseOne : HierarchyBase corrOne.replacementETT muOne)
                              (KOne : TashkinovHierarchy corrOne.replacementETT baseOne)
                              (goodOne : GoodHierarchy KOne),
                              SameGoodHierarchy C.good goodOne →
                               beta ∈ MissingColors G muOne (T.vertex D.terminalVertexIndex) →
                                ∀
                                 (POne :
                                  HierarchyReplacementPresentation G k e0 input T phi ett base C
                                   ctx),
                                 POne.coloring = muOne →
                                  let rho : PartialEdgeColoring E k := POne.coloring;
                                  let ettOne :
                                   ExtendedTashkinovTree G k e0
                                    POne.corresponding.replacementInput T POne.coloring :=
                                   POne.corresponding.replacementETT;
                                  let baseOne' :
                                   HierarchyBase POne.corresponding.replacementETT
                                    POne.coloring :=
                                   POne.replacementBase;
                                  let COne' : HierarchyCounterexample POne.replacementBase :=
                                   POne.counterexample;
                                  let HOne :
                                   TashkinovHierarchy POne.corresponding.replacementETT
                                    POne.replacementBase :=
                                   COne'.hierarchy;
                                  let qOne : Fin (HOne.dividerCount + (1 : ℕ)) :=
                                   Fin.last HOne.dividerCount;
                                  TreeMissingColors rho A = TreeMissingColors phi A →
                                   beta ∉ HierarchyStoredColorsAt HOne qOne →
                                    beta ∉
                                      MissingColors G rho (T.vertex D.penultimateVertexIndex) →
                                     beta ∈
                                       MissingColors G rho (T.vertex D.terminalVertexIndex) →
                                      beta ∈ MissingColors G rho (T.vertex ib) →
                                       HierarchyFirstMissingPosition rho T beta = ib →
                                        HierarchyFirstMissingPosition rho T D.theta =
                                          D.penultimateVertexIndex →
                                         (∀ (t : Fin T.length),
                                           A.length ≤ (↑t : ℕ) → rho (T.edge t) ≠ some beta) →
                                          (beta ∈ TreeMissingColors phi A →
                                            (0 : ℕ) < HOne.dividerCount ∧
                                              beta ∈
                                               TreeMissingColors rho
                                                (HOne.stage
                                                 (⟨HOne.dividerCount,
                                                   by
                                                   have :=
                                                    GoldbergSeymour.TreeSequence.positive T
                                                   omega⟩ :
                                                  Fin (HOne.dividerCount + (2 : ℕ)))) ∨
                                             HOne.dividerCount = (0 : ℕ) ∧
                                              beta ∈
                                               TreeMissingColors rho
                                                (ettOne.series.data.tree
                                                 (Fin.last ettOne.rounds).castSucc)) →
                                           beta ∈ TreeMissingColors rho B ∧
                                             D.theta ∈ TreeMissingColors rho B →
                                            (let H : TashkinovHierarchy ettOne baseOne' :=
                                              COne'.hierarchy;
                                             have q : Fin (H.dividerCount + (1 : ℕ)) :=
                                              Fin.last H.dividerCount;
                                             have n : Fin (ettOne.rounds + (1 : ℕ)) :=
                                              Fin.last ettOne.rounds;
                                             have A : TreeSequence G e0 :=
                                              HierarchyStarredStage H q;
                                             have Tnq : TreeSequence G e0 :=
                                              H.stage
                                               (⟨H.dividerCount,
                                                 by
                                                 have := GoldbergSeymour.TreeSequence.positive T
                                                 omega⟩ :
                                                Fin (H.dividerCount + (2 : ℕ)));
                                             have Tn : TreeSequence G e0 :=
                                              ettOne.series.data.tree n.castSucc;
                                             have Dn : Finset (Fin k) :=
                                              TashkinovStoredColors ettOne.series.data n;
                                             have Dnq : Finset (Fin k) :=
                                              HierarchyStoredColorsAt H q;
                                             have va : V :=
                                              T.vertex
                                               (HierarchyFirstMissingPosition rho T beta);
                                             have vb : V :=
                                              T.vertex
                                               (HierarchyFirstMissingPosition rho T D.theta);
                                             have sameComponent : Prop :=
                                              TwoColorComponent G rho beta D.theta
                                                (Sum.inl va) =
                                               TwoColorComponent G rho beta D.theta
                                                (Sum.inl vb);
                                             ((0 : ℕ) < H.dividerCount ∧
                                                (beta ∈ TreeMissingColors rho Tnq ∨
                                                 Disjoint
                                                  (insert beta ({ D.theta } : Finset (Fin k)) :
                                                   Finset (Fin k))
                                                  Dnq) →
                                               sameComponent) ∧
                                              (H.dividerCount = (0 : ℕ) ∧
                                                 (beta ∈ TreeMissingColors rho Tn ∨
                                                  Disjoint
                                                   (insert beta ({ D.theta } : Finset (Fin k)) :
                                                    Finset (Fin k))
                                                   Dn) →
                                                sameComponent) ∧
                                               (beta ∈ TreeMissingColors rho A ∧
                                                 TreeColorSetClosed G rho A
                                                  ({ beta } : Finset (Fin k)) →
                                                sameComponent ∧
                                                 TreeInterchangeable G A rho beta D.theta)) →
                                             TwoColorComponent G rho beta D.theta
                                               (Sum.inl (T.vertex ib)) =
                                              TwoColorComponent G rho beta D.theta
                                               (Sum.inl (T.vertex D.penultimateVertexIndex))

private abbrev helperReduction4203Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base)
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
   (D : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
  (2 : ℕ) ≤ T.length - A.length →
  B.length + (1 : ℕ) = T.length →
  TreeSequenceInitialSegment B T →
  ((0 : ℕ) < H.dividerCount →
    A =
     H.stage
      (⟨H.dividerCount,
        have this : (1 : ℕ) ≤ T.length := T.positive;
        Decidable.byContradiction fun (a : ¬H.dividerCount < H.dividerCount + (2 : ℕ)) ↦ by
         omega⟩ :
       Fin (H.dividerCount + (2 : ℕ)))) →
  (H.dividerCount = (0 : ℕ) → A = base.core) →
  TreeSequenceInitialSegment A T →
  TreeSequenceInitialSegment A B →
  B.vertex (Fin.last B.length) = T.vertex D.penultimateVertexIndex →
  T.vertex D.penultimateVertexIndex ∈ TreeSequenceVertexSet B →
  ColoredVertexSetElementary G phi (TreeSequenceVertexSet B) →
  HierarchyFirstMissingPosition phi T D.alpha = D.penultimateVertexIndex →
  HierarchyFirstMissingPosition phi T D.theta = D.penultimateVertexIndex →
  (∀ {c : Fin k},
    c ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex) →
     c ∉ TreeMissingColors phi A) →
  D.alpha ∉ TashkinovStoredColors ett.series.data (Fin.last ett.rounds) →
  let Bshort : TreeSequence G e0 :=
   HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ));
  Bshort.length + (2 : ℕ) = T.length →
  TreeSequenceInitialSegment Bshort T →
  TreeSequenceInitialSegment Bshort B →
  (∀ {c : Fin k},
    c ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex) →
     c ∉ TreeMissingColors phi Bshort) →
  Incident G (T.vertex D.terminalVertexIndex) (T.edge D.lastEdgeIndex) →
  (∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → phi (T.edge t) ≠ some D.alpha) →
  (∀ (rho : PartialEdgeColoring E k) (X : TreeSequence G e0),
    TreeSequenceInitialSegment X T →
     ∀ c ∈ TreeMissingColors rho X,
      c ∈
        MissingColors G rho
         (T.vertex (HierarchyFirstMissingPosition rho T c)) ∧
       (↑(HierarchyFirstMissingPosition rho T c) : ℕ) ≤ X.length) →
  (∀ (rho : PartialEdgeColoring E k) (a b : Fin k) (v : V),
    Sum.inl v ∈ TwoColorComponent G rho a b (Sum.inl v)) →
  (∀ (rho : PartialEdgeColoring E k) {X Y : TreeSequence G e0},
    TreeSequenceInitialSegment X Y →
     TreeMissingColors rho X ⊆ TreeMissingColors rho Y) →
  (∀ (rho : PartialEdgeColoring E k) (a b : Fin k),
    a ≠ b →
     IsProperEdgeColoring G rho →
      ∀ (v : V),
       a ∈ MissingColors G rho v ∨ b ∈ MissingColors G rho v →
        ((TwoColorIncidenceGraph G rho a b).neighborSet
          (Sum.inl v)).Subsingleton) →
  (∀ (rho : PartialEdgeColoring E k) (a b : Fin k),
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
  (∀ (z : V ⊕ E) (rho : PartialEdgeColoring E k) (a b : Fin k),
    a ≠ b →
     IsProperEdgeColoring G rho →
      ColoredVertexSetElementary G rho (TreeSequenceVertexSet B) →
       ∀ (u v : V),
        u ∈ TreeSequenceVertexSet B →
         v ∈ TreeSequenceVertexSet B →
          a ∈ MissingColors G rho u →
           b ∈ MissingColors G rho v →
            Sum.inl u ∉ TwoColorComponent G rho a b z →
             Sum.inl v ∉ TwoColorComponent G rho a b z →
              ∀ w ∈ TreeSequenceVertexSet B,
               MissingColors G (TwoColorComponentSwap G rho a b z) w =
                MissingColors G rho w) →
  (∀ (rho sigma : PartialEdgeColoring E k) (c : Fin k),
    ColoredVertexSetElementary G rho (TreeSequenceVertexSet B) →
     (∀ v ∈ TreeSequenceVertexSet B,
       MissingColors G sigma v = MissingColors G rho v) →
      c ∈ TreeMissingColors rho B →
       HierarchyFirstMissingPosition sigma T c =
        HierarchyFirstMissingPosition rho T c) →
  (∀ (z : V ⊕ E) (rho : PartialEdgeColoring E k) (a b c : Fin k),
    a ≠ b →
     IsProperEdgeColoring G rho →
      c ≠ a →
       c ≠ b →
        HierarchyFirstMissingPosition
          (TwoColorComponentSwap G rho a b z) T c =
         HierarchyFirstMissingPosition rho T c) →
  ∀
   (seriesFacts :
    ∀ (j : Fin (ett.rounds + (1 : ℕ))),
     IsProperEdgeColoring G (ett.series.data.coloring j) ∧
      IsOneEdgeUncolored (ett.series.data.coloring j) e0),
  let corrRefl :
   CorrespondingExtendedTashkinovTree G k e0 ett phi T := by
   exact
    {
     replacementInput := input, replacementSeries := ett.series,
     replacementETT := ett, rungAgreement := rfl,
     seriesPresentation := HEq.rfl,
     finalGeneratingColoring := ett.generatingColoring,
     ladderTreesAgree := fun (x : Fin ett.rounds) ↦ rfl,
     storedColorsAgree := fun (x : Fin (ett.rounds + (1 : ℕ))) ↦ rfl,
     connectingEdgesAgree := fun (x : Fin (ett.rounds + (1 : ℕ))) ↦
      rfl,
     extensionKindsAgree := fun (x : Fin (ett.rounds + (1 : ℕ))) ↦
      rfl,
     replacementProper := fun (j : Fin (ett.rounds + (1 : ℕ))) ↦
      (seriesFacts j).left,
     replacementOneUncolored := fun (j : Fin (ett.rounds + (1 : ℕ))) ↦
      (seriesFacts j).right,
     replacementStable := fun (x : Fin ett.rounds) ↦
      (⟨fun (x_1 : E)
         (x_2 :
          TreeIncidentEdge (ett.series.data.tree x.succ.castSucc) x_1)
         (x_3 :
          ∃
           c ∈
            TreeMissingColors (ett.series.data.coloring x.succ)
              (ett.series.data.tree x.succ.castSucc) ∪
             TashkinovStoredColors ett.series.data x.succ,
           ett.series.data.coloring x.succ x_1 = some c) ↦
        rfl,
        fun (x_1 : V)
         (x_2 :
          x_1 ∈
           TreeSequenceVertexSet
            (ett.series.data.tree x.succ.castSucc)) ↦
        rfl⟩ :
       (∀ (f : E),
         TreeIncidentEdge (ett.series.data.tree x.succ.castSucc) f →
          (∃
            c ∈
             TreeMissingColors (ett.series.data.coloring x.succ)
               (ett.series.data.tree x.succ.castSucc) ∪
              TashkinovStoredColors ett.series.data x.succ,
            ett.series.data.coloring x.succ f = some c) →
           ett.series.data.coloring x.succ f =
            ett.series.data.coloring x.succ f) ∧
        ∀
         v ∈
          TreeSequenceVertexSet
           (ett.series.data.tree x.succ.castSucc),
         MissingColors G (ett.series.data.coloring x.succ) v =
          MissingColors G (ett.series.data.coloring x.succ) v) :
     CorrespondingExtendedTashkinovTree G k e0 ett phi T };
  let PRefl :
   HierarchyReplacementPresentation G k e0 input T phi ett base C
    ctx := by
   exact
    {
     coloring := phi, corresponding := corrRefl,
     maximum := C.maximum, replacementBase := base,
     counterexample := C,
     sameGood :=
      (⟨(⟨rfl,
          (⟨by
            have := GoldbergSeymour.TreeSequence.positive T
            omega,
            (⟨HEq.rfl,
              (⟨HEq.rfl,
                (⟨Iff.rfl,
                  fun
                   (x :
                    ett.series.data.kind (Fin.last ett.rounds) =
                     some TashkinovExtensionKind.PE) ↦
                  rfl⟩ :
                 (ett.series.data.kind (Fin.last ett.rounds) =
                    some TashkinovExtensionKind.PE ↔
                   corrRefl.replacementETT.series.data.kind
                     (Fin.last corrRefl.replacementETT.rounds) =
                    some TashkinovExtensionKind.PE) ∧
                  (ett.series.data.kind (Fin.last ett.rounds) =
                    some TashkinovExtensionKind.PE →
                   base.closure = base.closure))⟩ :
               C.hierarchy.dividerPosition ≍
                 C.hierarchy.dividerPosition ∧
                (ett.series.data.kind (Fin.last ett.rounds) =
                   some TashkinovExtensionKind.PE ↔
                  corrRefl.replacementETT.series.data.kind
                    (Fin.last corrRefl.replacementETT.rounds) =
                   some TashkinovExtensionKind.PE) ∧
                 (ett.series.data.kind (Fin.last ett.rounds) =
                   some TashkinovExtensionKind.PE →
                  base.closure = base.closure))⟩ :
             C.hierarchy.stage ≍ C.hierarchy.stage ∧
              C.hierarchy.dividerPosition ≍
                C.hierarchy.dividerPosition ∧
               (ett.series.data.kind (Fin.last ett.rounds) =
                  some TashkinovExtensionKind.PE ↔
                 corrRefl.replacementETT.series.data.kind
                   (Fin.last corrRefl.replacementETT.rounds) =
                  some TashkinovExtensionKind.PE) ∧
                (ett.series.data.kind (Fin.last ett.rounds) =
                  some TashkinovExtensionKind.PE →
                 base.closure = base.closure))⟩ :
           C.hierarchy.dividerCount = C.hierarchy.dividerCount ∧
            C.hierarchy.stage ≍ C.hierarchy.stage ∧
             C.hierarchy.dividerPosition ≍
               C.hierarchy.dividerPosition ∧
              (ett.series.data.kind (Fin.last ett.rounds) =
                 some TashkinovExtensionKind.PE ↔
                corrRefl.replacementETT.series.data.kind
                  (Fin.last corrRefl.replacementETT.rounds) =
                 some TashkinovExtensionKind.PE) ∧
               (ett.series.data.kind (Fin.last ett.rounds) =
                 some TashkinovExtensionKind.PE →
                base.closure = base.closure))⟩ :
         base.core = base.core ∧
          C.hierarchy.dividerCount = C.hierarchy.dividerCount ∧
           C.hierarchy.stage ≍ C.hierarchy.stage ∧
            C.hierarchy.dividerPosition ≍
              C.hierarchy.dividerPosition ∧
             (ett.series.data.kind (Fin.last ett.rounds) =
                some TashkinovExtensionKind.PE ↔
               corrRefl.replacementETT.series.data.kind
                 (Fin.last corrRefl.replacementETT.rounds) =
                some TashkinovExtensionKind.PE) ∧
              (ett.series.data.kind (Fin.last ett.rounds) =
                some TashkinovExtensionKind.PE →
               base.closure = base.closure)),
        Exists.intro
         (by
          have := GoldbergSeymour.TreeSequence.positive T
          omega)
         fun (x : Fin (C.hierarchy.dividerCount + (1 : ℕ))) ↦
         (⟨rfl,
           fun (x_1 : Fin k)
            (x_2 : x_1 ∈ HierarchyStoredColorsAt C.hierarchy x) ↦
           rfl⟩ :
          HierarchyStoredColorsAt C.hierarchy x =
            HierarchyStoredColorsAt C.hierarchy
             (Fin.cast
              (by
               have :=
                GoldbergSeymour.CorrespondingExtendedTashkinovTree.rungAgreement
                 corrRefl
               have := GoldbergSeymour.TreeSequence.positive T
               omega)
              x) ∧
           ∀ eta ∈ HierarchyStoredColorsAt C.hierarchy x,
            C.good.gamma x eta =
             C.good.gamma
              (Fin.cast
               (by
                have :=
                 GoldbergSeymour.CorrespondingExtendedTashkinovTree.rungAgreement
                  corrRefl
                have := GoldbergSeymour.TreeSequence.positive T
                omega)
               x)
              eta)⟩ :
       SameHierarchyStages C.hierarchy C.hierarchy ∧
        ∃ (hcount :
         C.hierarchy.dividerCount = C.hierarchy.dividerCount),
         ∀ (j : Fin (C.hierarchy.dividerCount + (1 : ℕ))),
          have j₂ : Fin (C.hierarchy.dividerCount + (1 : ℕ)) :=
           Fin.cast
            (by
             have :=
              GoldbergSeymour.CorrespondingExtendedTashkinovTree.rungAgreement
               corrRefl
             have := GoldbergSeymour.TreeSequence.positive T
             omega)
            j;
          HierarchyStoredColorsAt C.hierarchy j =
            HierarchyStoredColorsAt C.hierarchy j₂ ∧
           ∀ eta ∈ HierarchyStoredColorsAt C.hierarchy j,
            C.good.gamma j eta = C.good.gamma j₂ eta),
     minimumContext := ctx :
     HierarchyReplacementPresentation G k e0 input T phi ett base C
      ctx };
  (∀
    (P :
     HierarchyReplacementPresentation G k e0 input T phi ett base C
      ctx),
    HierarchyStarredStage P.counterexample.hierarchy
      (Fin.last P.counterexample.hierarchy.dividerCount) =
     A) →
  (∀
    (P :
     HierarchyReplacementPresentation G k e0 input T phi ett base C
      ctx),
    HierarchyFullTailPrefix P.counterexample
      (HierarchyFullTailLength P.counterexample - (1 : ℕ)) =
     B) →
  (∀
    (P :
     HierarchyReplacementPresentation G k e0 input T phi ett base C
      ctx),
    P.corresponding.replacementETT.series.data.tree
      (Fin.last P.corresponding.replacementETT.rounds).castSucc =
     ett.series.data.tree (Fin.last ett.rounds).castSucc) →
  (∀
    (P :
     HierarchyReplacementPresentation G k e0 input T phi ett base C
      ctx),
    HierarchyStoredColorsAt H q =
      HierarchyStoredColorsAt P.counterexample.hierarchy
       (Fin.last P.counterexample.hierarchy.dividerCount) ∧
     ∀ eta ∈ HierarchyStoredColorsAt H q,
      C.good.gamma q eta =
       P.counterexample.good.gamma
        (Fin.last P.counterexample.hierarchy.dividerCount) eta) →
  (∀ {X Y F : TreeSequence G e0},
    TreeSequenceInitialSegment X F →
     TreeSequenceInitialSegment Y F →
      X.length ≤ Y.length → TreeSequenceInitialSegment X Y) →
  base.core.length ≤ A.length →
  (∀ (X : TreeSequence G e0),
    TreeSequenceInitialSegment X T →
     ∀ (t : Fin T.length),
      (↑t : ℕ) = X.length → TreeIncidentEdge X (T.edge t)) →
  (∀ {input' : PartialEdgeColoring E k}
    (rho sigma : PartialEdgeColoring E k)
    (ett' : ExtendedTashkinovTree G k e0 input' T rho)
    (base' : HierarchyBase ett' rho)
    (K : TashkinovHierarchy ett' base'),
    HierarchyWeaklyStable K (Fin.last K.dividerCount) sigma →
     K.dividerCount = (0 : ℕ) →
      StableColoring
       (ett'.series.data.tree (Fin.last ett'.rounds).castSucc)
       (TashkinovStoredColors ett'.series.data
        (Fin.last ett'.rounds))
       rho sigma) →
  (∀ {input' : PartialEdgeColoring E k}
    (old new : PartialEdgeColoring E k)
    (ett' : ExtendedTashkinovTree G k e0 input' T old)
    (base' : HierarchyBase ett' old)
    (K : TashkinovHierarchy ett' base'),
    HierarchyWeaklyStable K (Fin.last K.dividerCount) new →
     IsOneEdgeUncolored old e0 →
      IsOneEdgeUncolored new e0 →
       ∀
        (t :
         Fin
          (HierarchyStarredStage K
            (Fin.last K.dividerCount)).length),
        new
          ((HierarchyStarredStage K
             (Fin.last K.dividerCount)).edge
           t) =
         old
          ((HierarchyStarredStage K
             (Fin.last K.dividerCount)).edge
           t)) →
  ∀ beta ∈ TreeMissingColors phi Bshort,
   (∀ (t : Fin T.length),
     A.length ≤ (↑t : ℕ) → phi (T.edge t) ≠ some beta) →
    beta ∉ HierarchyStoredColorsAt H q →
     (H.dividerCount = (0 : ℕ) →
       beta ∈ TreeMissingColors phi A →
        beta ∈
         TreeMissingColors phi
          (ett.series.data.tree
           (Fin.last ett.rounds).castSucc)) →
      (beta ∉ TreeMissingColors phi A →
        D.theta ∉ HierarchyStoredColorsAt H q) →
       (∀ eta ∈ HierarchyStoredColorsAt H q,
         beta ∈ C.good.gamma q eta →
          eta = D.theta ∨
           eta ∈ TreeMissingColors phi Bshort) →
        False

private abbrev helperContinuation5379Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base)
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
   (D : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
  (2 : ℕ) ≤ T.length - A.length →
  B.length + (1 : ℕ) = T.length →
  TreeSequenceInitialSegment B T →
  (H.dividerCount = (0 : ℕ) → A = base.core) →
  TreeSequenceInitialSegment A T →
  TreeSequenceInitialSegment A B →
  B.vertex (Fin.last B.length) = T.vertex D.penultimateVertexIndex →
  T.vertex D.penultimateVertexIndex ∈ TreeSequenceVertexSet B →
  ColoredVertexSetElementary G phi (TreeSequenceVertexSet B) →
  HierarchyFirstMissingPosition phi T D.theta = D.penultimateVertexIndex →
  (∀ {c : Fin k},
    c ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex) →
     c ∉ TreeMissingColors phi A) →
  let Bshort : TreeSequence G e0 :=
   HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ));
  TreeSequenceInitialSegment Bshort T →
  TreeSequenceInitialSegment Bshort B →
  Incident G (T.vertex D.terminalVertexIndex) (T.edge D.lastEdgeIndex) →
  (∀ (rho : PartialEdgeColoring E k) (X : TreeSequence G e0),
    TreeSequenceInitialSegment X T →
     ∀ c ∈ TreeMissingColors rho X,
      c ∈ MissingColors G rho (T.vertex (HierarchyFirstMissingPosition rho T c)) ∧
       (↑(HierarchyFirstMissingPosition rho T c) : ℕ) ≤ X.length) →
  (∀ (rho : PartialEdgeColoring E k) (a b : Fin k) (v : V),
    Sum.inl v ∈ TwoColorComponent G rho a b (Sum.inl v)) →
  (∀ (rho : PartialEdgeColoring E k) {X Y : TreeSequence G e0},
    TreeSequenceInitialSegment X Y →
     TreeMissingColors rho X ⊆ TreeMissingColors rho Y) →
  (∀ (rho : PartialEdgeColoring E k) (a b : Fin k),
    a ≠ b →
     IsProperEdgeColoring G rho →
      ∀ (v : V),
       a ∈ MissingColors G rho v ∨ b ∈ MissingColors G rho v →
        ((TwoColorIncidenceGraph G rho a b).neighborSet
          (Sum.inl v)).Subsingleton) →
  (∀ (rho : PartialEdgeColoring E k) (a b : Fin k),
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
  (∀ (z : V ⊕ E) (rho : PartialEdgeColoring E k) (a b : Fin k),
    a ≠ b →
     IsProperEdgeColoring G rho →
      ColoredVertexSetElementary G rho (TreeSequenceVertexSet B) →
       ∀ (u v : V),
        u ∈ TreeSequenceVertexSet B →
         v ∈ TreeSequenceVertexSet B →
          a ∈ MissingColors G rho u →
           b ∈ MissingColors G rho v →
            Sum.inl u ∉ TwoColorComponent G rho a b z →
             Sum.inl v ∉ TwoColorComponent G rho a b z →
              ∀ w ∈ TreeSequenceVertexSet B,
               MissingColors G (TwoColorComponentSwap G rho a b z) w =
                MissingColors G rho w) →
  (∀ (rho sigma : PartialEdgeColoring E k) (c : Fin k),
    ColoredVertexSetElementary G rho (TreeSequenceVertexSet B) →
     (∀ v ∈ TreeSequenceVertexSet B,
       MissingColors G sigma v = MissingColors G rho v) →
      c ∈ TreeMissingColors rho B →
       HierarchyFirstMissingPosition sigma T c =
        HierarchyFirstMissingPosition rho T c) →
  (∀ (z : V ⊕ E) (rho : PartialEdgeColoring E k) (a b c : Fin k),
    a ≠ b →
     IsProperEdgeColoring G rho →
      c ≠ a →
       c ≠ b →
        HierarchyFirstMissingPosition (TwoColorComponentSwap G rho a b z) T
          c =
         HierarchyFirstMissingPosition rho T c) →
  (∀
    (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    HierarchyStarredStage P.counterexample.hierarchy
      (Fin.last P.counterexample.hierarchy.dividerCount) =
     A) →
  (∀
    (P :
     HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    HierarchyFullTailPrefix P.counterexample
      (HierarchyFullTailLength P.counterexample - (1 : ℕ)) =
     B) →
  (∀
    (P :
     HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    P.corresponding.replacementETT.series.data.tree
      (Fin.last P.corresponding.replacementETT.rounds).castSucc =
     ett.series.data.tree (Fin.last ett.rounds).castSucc) →
  (∀
    (P :
     HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    HierarchyStoredColorsAt H q =
      HierarchyStoredColorsAt P.counterexample.hierarchy
       (Fin.last P.counterexample.hierarchy.dividerCount) ∧
     ∀ eta ∈ HierarchyStoredColorsAt H q,
      C.good.gamma q eta =
       P.counterexample.good.gamma
        (Fin.last P.counterexample.hierarchy.dividerCount) eta) →
  (∀ {X Y F : TreeSequence G e0},
    TreeSequenceInitialSegment X F →
     TreeSequenceInitialSegment Y F →
      X.length ≤ Y.length → TreeSequenceInitialSegment X Y) →
  base.core.length ≤ A.length →
  (∀ (X : TreeSequence G e0),
    TreeSequenceInitialSegment X T →
     ∀ (t : Fin T.length),
      (↑t : ℕ) = X.length → TreeIncidentEdge X (T.edge t)) →
  (∀ {input' : PartialEdgeColoring E k}
    (rho sigma : PartialEdgeColoring E k)
    (ett' : ExtendedTashkinovTree G k e0 input' T rho)
    (base' : HierarchyBase ett' rho)
    (K : TashkinovHierarchy ett' base'),
    HierarchyWeaklyStable K (Fin.last K.dividerCount) sigma →
     K.dividerCount = (0 : ℕ) →
      StableColoring
       (ett'.series.data.tree (Fin.last ett'.rounds).castSucc)
       (TashkinovStoredColors ett'.series.data (Fin.last ett'.rounds))
       rho sigma) →
  (∀ {input' : PartialEdgeColoring E k}
    (old new : PartialEdgeColoring E k)
    (ett' : ExtendedTashkinovTree G k e0 input' T old)
    (base' : HierarchyBase ett' old)
    (K : TashkinovHierarchy ett' base'),
    HierarchyWeaklyStable K (Fin.last K.dividerCount) new →
     IsOneEdgeUncolored old e0 →
      IsOneEdgeUncolored new e0 →
       ∀
        (t :
         Fin
          (HierarchyStarredStage K
            (Fin.last K.dividerCount)).length),
        new
          ((HierarchyStarredStage K (Fin.last K.dividerCount)).edge
           t) =
         old
          ((HierarchyStarredStage K (Fin.last K.dividerCount)).edge
           t)) →
  ∀ beta ∈ TreeMissingColors phi Bshort,
   (∀ (t : Fin T.length),
     A.length ≤ (↑t : ℕ) → phi (T.edge t) ≠ some beta) →
    beta ∉ HierarchyStoredColorsAt H q →
     (H.dividerCount = (0 : ℕ) →
       beta ∈ TreeMissingColors phi A →
        beta ∈
         TreeMissingColors phi
          (ett.series.data.tree (Fin.last ett.rounds).castSucc)) →
      (beta ∉ TreeMissingColors phi A →
        D.theta ∉ HierarchyStoredColorsAt H q) →
       (∀ eta ∈ HierarchyStoredColorsAt H q,
         beta ∈ C.good.gamma q eta →
          eta = D.theta ∨ eta ∈ TreeMissingColors phi Bshort) →
        beta ≠ D.alpha →
         beta ≠ D.theta →
          let ib : Fin (T.length + (1 : ℕ)) :=
           HierarchyFirstMissingPosition phi T beta;
          beta ∈
             MissingColors G phi
              (T.vertex
               (HierarchyFirstMissingPosition phi T beta)) ∧
            (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤
             Bshort.length →
           T.vertex ib ∈ TreeSequenceVertexSet B →
            T.vertex ib ≠ T.vertex D.penultimateVertexIndex →
             T.vertex ib ≠ T.vertex D.terminalVertexIndex →
              T.vertex D.penultimateVertexIndex ≠
                T.vertex D.terminalVertexIndex →
               TreeVertexOrder T (T.vertex ib)
                 (T.vertex D.penultimateVertexIndex) →
                (∀ (rho : PartialEdgeColoring E k),
                  ∀
                   c ∈
                    MissingColors G rho
                     (T.vertex
                      (HierarchyFirstMissingPosition rho T c)),
                   c ∉ TreeMissingColors rho A →
                    A.length <
                     (↑(HierarchyFirstMissingPosition rho T c) :
                      ℕ)) →
                 (beta ∉ TreeMissingColors phi A →
                   beta ∉
                    TashkinovStoredColors ett.series.data
                     (Fin.last ett.rounds)) →
                  beta ∈ TreeMissingColors phi B ∧
                    D.alpha ∈ TreeMissingColors phi B →
                   (let H : TashkinovHierarchy ett base :=
                     C.hierarchy;
                    have q : Fin (H.dividerCount + (1 : ℕ)) :=
                     Fin.last H.dividerCount;
                    have n : Fin (ett.rounds + (1 : ℕ)) :=
                     Fin.last ett.rounds;
                    have A : TreeSequence G e0 :=
                     HierarchyStarredStage H q;
                    have Tnq : TreeSequence G e0 :=
                     H.stage
                      (⟨H.dividerCount,
                        by
                        have :=
                         GoldbergSeymour.TreeSequence.positive T
                        omega⟩ :
                       Fin (H.dividerCount + (2 : ℕ)));
                    have Tn : TreeSequence G e0 :=
                     ett.series.data.tree n.castSucc;
                    have Dn : Finset (Fin k) :=
                     TashkinovStoredColors ett.series.data n;
                    have Dnq : Finset (Fin k) :=
                     HierarchyStoredColorsAt H q;
                    have va : V :=
                     T.vertex
                      (HierarchyFirstMissingPosition phi T beta);
                    have vb : V :=
                     T.vertex
                      (HierarchyFirstMissingPosition phi T D.alpha);
                    have sameComponent : Prop :=
                     TwoColorComponent G phi beta D.alpha
                       (Sum.inl va) =
                      TwoColorComponent G phi beta D.alpha
                       (Sum.inl vb);
                    ((0 : ℕ) < H.dividerCount ∧
                       (beta ∈ TreeMissingColors phi Tnq ∨
                        Disjoint
                         (insert beta
                           ({ D.alpha } : Finset (Fin k)) :
                          Finset (Fin k))
                         Dnq) →
                      sameComponent) ∧
                     (H.dividerCount = (0 : ℕ) ∧
                        (beta ∈ TreeMissingColors phi Tn ∨
                         Disjoint
                          (insert beta
                            ({ D.alpha } : Finset (Fin k)) :
                           Finset (Fin k))
                          Dn) →
                       sameComponent) ∧
                      (beta ∈ TreeMissingColors phi A ∧
                        TreeColorSetClosed G phi A
                         ({ beta } : Finset (Fin k)) →
                       sameComponent ∧
                        TreeInterchangeable G A phi beta D.alpha)) →
                    TwoColorComponent G phi beta D.alpha
                       (Sum.inl (T.vertex ib)) =
                      TwoColorComponent G phi beta D.alpha
                       (Sum.inl
                        (T.vertex D.penultimateVertexIndex)) →
                     let z : V ⊕ E :=
                      Sum.inl (T.vertex D.terminalVertexIndex);
                     let muOne : PartialEdgeColoring E k :=
                      TwoColorComponentSwap G phi beta D.alpha z;
                     Disjoint
                       (TwoColorComponent G phi beta D.alpha
                        (Sum.inl (T.vertex D.terminalVertexIndex)))
                       (TwoColorComponent G phi beta D.alpha
                        (Sum.inl (T.vertex ib))) →
                      TwoColorPathComponent G phi beta D.alpha z →
                       Sum.inl (T.vertex ib) ∉
                         TwoColorComponent G phi beta D.alpha z →
                        Sum.inl
                           (T.vertex D.penultimateVertexIndex) ∉
                          TwoColorComponent G phi beta D.alpha z →
                         (∀ w ∈ TreeSequenceVertexSet B,
                           MissingColors G
                             (TwoColorComponentSwap G phi beta
                              D.alpha z)
                             w =
                            MissingColors G phi w) →
                          (∀ (t : Fin T.length),
                            A.length ≤ (↑t : ℕ) →
                             muOne (T.edge t) = phi (T.edge t)) →
                           (∀ c ∈ HierarchyStoredColorsAt H q,
                             HierarchyFirstMissingPosition muOne T
                               c =
                              HierarchyFirstMissingPosition phi T
                               c) →
                            (beta ∈ TreeMissingColors phi A →
                              (0 : ℕ) < H.dividerCount ∧
                                beta ∈
                                 TreeMissingColors phi
                                  (H.stage
                                   (⟨H.dividerCount,
                                     by
                                     have :=
                                      GoldbergSeymour.TreeSequence.positive
                                       T
                                     omega⟩ :
                                    Fin
                                     (H.dividerCount + (2 : ℕ)))) ∨
                               H.dividerCount = (0 : ℕ) ∧
                                beta ∈
                                 TreeMissingColors phi
                                  (ett.series.data.tree
                                   (Fin.last
                                     ett.rounds).castSucc)) →
                             ∀
                              (corrOne :
                               CorrespondingExtendedTashkinovTree G
                                k e0 ett muOne T),
                              MaximumProperty
                                corrOne.replacementETT →
                               ∀
                                (baseOne :
                                 HierarchyBase
                                  corrOne.replacementETT muOne)
                                (KOne :
                                 TashkinovHierarchy
                                  corrOne.replacementETT baseOne)
                                (goodOne : GoodHierarchy KOne),
                                SameGoodHierarchy C.good goodOne →
                                 beta ∈
                                   MissingColors G muOne
                                    (T.vertex
                                     D.terminalVertexIndex) →
                                  ∀
                                   (POne :
                                    HierarchyReplacementPresentation
                                     G k e0 input T phi ett base C
                                     ctx),
                                   POne.coloring = muOne →
                                    let rho :
                                     PartialEdgeColoring E k :=
                                     POne.coloring;
                                    let ettOne :
                                     ExtendedTashkinovTree G k e0
                                      POne.corresponding.replacementInput
                                      T POne.coloring :=
                                     POne.corresponding.replacementETT;
                                    let baseOne' :
                                     HierarchyBase
                                      POne.corresponding.replacementETT
                                      POne.coloring :=
                                     POne.replacementBase;
                                    let COne' :
                                     HierarchyCounterexample
                                      POne.replacementBase :=
                                     POne.counterexample;
                                    let ctxOne :
                                     HierarchyMinimumCounterexampleContext
                                      G k e0
                                      POne.corresponding.replacementInput
                                      T POne.coloring
                                      POne.corresponding.replacementETT
                                      POne.replacementBase
                                      POne.counterexample :=
                                     POne.minimumContext;
                                    let HOne :
                                     TashkinovHierarchy
                                      POne.corresponding.replacementETT
                                      POne.replacementBase :=
                                     COne'.hierarchy;
                                    let qOne :
                                     Fin
                                      (HOne.dividerCount +
                                       (1 : ℕ)) :=
                                     Fin.last HOne.dividerCount;
                                    (∀ v ∈ TreeSequenceVertexSet B,
                                      MissingColors G rho v =
                                       MissingColors G phi v) →
                                     ColoredVertexSetElementary G
                                       rho
                                       (TreeSequenceVertexSet B) →
                                      (∀ (X : TreeSequence G e0),
                                        TreeSequenceInitialSegment X
                                          B →
                                         TreeMissingColors rho X =
                                          TreeMissingColors phi X) →
                                       False

private theorem helper_hBT_115.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base),
    let B : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    B.length + (1 : ℕ) = T.length →
    TreeSequenceInitialSegment B T := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C B hBlen
  refine ⟨?_, ?_, ?_⟩
  · omega
  · intro i
    rfl
  · intro i
    rfl

private theorem helper_hApositive_122.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    (0 : ℕ) < H.dividerCount →
    A =
      H.stage
        (⟨H.dividerCount, by
            have := GoldbergSeymour.TreeSequence.positive T
            omega⟩ :
          Fin (H.dividerCount + (2 : ℕ))) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q A hq
  have hi : q = (⟨H.dividerCount - 1, by omega⟩ : Fin H.dividerCount).succ := by
    apply Fin.ext
    simp [q]
    omega
  change HierarchyStarredStage H q = _
  rw [hi]
  simp only [HierarchyStarredStage, Fin.cases_succ]
  congr 1
  apply Fin.ext
  simp
  omega

private theorem helper_hAT_140.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    ((0 : ℕ) < H.dividerCount →
        A =
          H.stage
            (⟨H.dividerCount,
                by
                have := GoldbergSeymour.TreeSequence.positive T
                omega⟩ :
              Fin (H.dividerCount + (2 : ℕ)))) →
    (H.dividerCount = (0 : ℕ) → A = base.core) →
    TreeSequenceInitialSegment A T := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q A hApositive hAzero
  by_cases hz : H.dividerCount = 0
  · have hi : (⟨1, by omega⟩ : Fin (H.dividerCount + 2)) =
        Fin.last (H.dividerCount + 1) := by apply Fin.ext; simp [hz]
    simpa [hAzero hz, hi, H.terminalStage] using H.coreInsideFirst
  · rw [hApositive (Nat.pos_of_ne_zero hz)]
    have hi : (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + 2)) =
        q.castSucc := Fin.ext rfl
    have hj : H.stage q.succ = T := by
      convert H.terminalStage using 1
      congr 1
    simpa only [hi, hj] using H.nested q

private theorem helper_hAB_152.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let B : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    (2 : ℕ) ≤ T.length - A.length →
    B.length + (1 : ℕ) = T.length →
    ((0 : ℕ) < H.dividerCount →
        A =
          H.stage
            (⟨H.dividerCount,
                by
                have := GoldbergSeymour.TreeSequence.positive T
                omega⟩ :
              Fin (H.dividerCount + (2 : ℕ)))) →
    (H.dividerCount = (0 : ℕ) → A = base.core) →
    TreeSequenceInitialSegment A T →
    TreeSequenceInitialSegment A B := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q A B htail hBlen hApositive hAzero hAT
  refine ⟨by omega, ?_, ?_⟩
  · intro i
    exact hAT.2.1 i
  · intro i
    exact hAT.2.2 i

private theorem helper_hBterminal_158.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
    let B : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    B.length + (1 : ℕ) = T.length →
    TreeSequenceInitialSegment B T →
    B.vertex (Fin.last B.length) = T.vertex D.penultimateVertexIndex := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D B hBlen hBT
  rw [← hBT.2.1 (Fin.last B.length)]
  congr 1
  apply Fin.ext
  have hp := D.penultimateVertexPosition
  simp only [Fin.val_castLE, Fin.val_last]
  omega

private theorem helper_firstAt_172.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
    let B : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    B.length + (1 : ℕ) = T.length →
    T.vertex D.penultimateVertexIndex ∈ TreeSequenceVertexSet B →
    ColoredVertexSetElementary G phi (TreeSequenceVertexSet B) →
    ∀ {c : Fin k},
    c ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex) →
    HierarchyFirstMissingPosition phi T c = D.penultimateVertexIndex := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D B hBlen hyB hElementary c hc
  let candidates := Finset.univ.filter fun i : Fin (T.length + 1) =>
    c ∈ MissingColors G phi (T.vertex i)
  have hy : D.penultimateVertexIndex ∈ candidates := by simp [candidates, hc]
  have hn : candidates.Nonempty := ⟨_, hy⟩
  have hmin := Finset.min'_le candidates _ hy
  have hm : c ∈ MissingColors G phi (T.vertex (candidates.min' hn)) :=
    (Finset.mem_filter.mp (Finset.min'_mem candidates hn)).2
  have hmem : T.vertex (candidates.min' hn) ∈ TreeSequenceVertexSet B := by
    let j : Fin (B.length + 1) := ⟨(candidates.min' hn).val, by
      have hp := D.penultimateVertexPosition
      change (candidates.min' hn).val ≤ D.penultimateVertexIndex.val at hmin
      omega⟩
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨j, ?_⟩
    rfl
  have heq : candidates.min' hn = D.penultimateVertexIndex := by
    by_contra hne
    have hvne := fun h => hne (T.vertex_injective h)
    exact Finset.disjoint_left.mp (hElementary hmem hyB hvne) hm hc
  simpa only [HierarchyFirstMissingPosition, candidates, dite_eq_left hn] using heq

private theorem helper_hnotA_197.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let B : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    (2 : ℕ) ≤ T.length - A.length →
    ((0 : ℕ) < H.dividerCount →
        A =
          H.stage
            (⟨H.dividerCount,
                by
                have := GoldbergSeymour.TreeSequence.positive T
                omega⟩ :
              Fin (H.dividerCount + (2 : ℕ)))) →
    (H.dividerCount = (0 : ℕ) → A = base.core) →
    TreeSequenceInitialSegment A T →
    TreeSequenceInitialSegment A B →
    T.vertex D.penultimateVertexIndex ∈ TreeSequenceVertexSet B →
    ColoredVertexSetElementary G phi (TreeSequenceVertexSet B) →
    HierarchyFirstMissingPosition phi T D.theta = D.penultimateVertexIndex →
    ∀ {c : Fin k},
    c ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex) →
    c ∉ TreeMissingColors phi A := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B htail hApositive hAzero hAT hAB
      hyB hElementary hfirstTheta c hc ha
  rcases Finset.mem_biUnion.mp ha with ⟨v, hv, hvc⟩
  have hvB := TreeSequenceInitialSegmentVertexSetSubset hAB hv
  have hvne : v ≠ T.vertex D.penultimateVertexIndex := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hv
    rcases hv with ⟨i, rfl⟩
    intro he
    have hi := T.vertex_injective ((hAT.2.1 i).trans he)
    have hp := D.penultimateVertexPosition
    have hib := i.isLt
    have hiv := congrArg Fin.val hi
    simp only [Fin.val_castLE] at hiv
    omega
  exact Finset.disjoint_left.mp (hElementary hvB hyB hvne) hvc hc

private theorem helper_hshortB_225.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (_ : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
    let B : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    B.length + (1 : ℕ) = T.length →
    let Bshort : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ));
    Bshort.length + (2 : ℕ) = T.length →
    TreeSequenceInitialSegment Bshort B := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D B hBlen Bshort hshortLen
  refine ⟨by omega, ?_, ?_⟩
  · intro i
    rfl
  · intro i
    rfl

private theorem helper_hnotShort_231.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
    let B : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    T.vertex D.penultimateVertexIndex ∈ TreeSequenceVertexSet B →
    ColoredVertexSetElementary G phi (TreeSequenceVertexSet B) →
    HierarchyFirstMissingPosition phi T D.theta = D.penultimateVertexIndex →
    let Bshort : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ));
    Bshort.length + (2 : ℕ) = T.length →
    TreeSequenceInitialSegment Bshort T →
    TreeSequenceInitialSegment Bshort B →
    ∀ {c : Fin k},
    c ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex) →
    c ∉ TreeMissingColors phi Bshort := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D B hyB hElementary hfirstTheta Bshort
      hshortLen hshortT hshortB c hc hm
  rcases Finset.mem_biUnion.mp hm with ⟨v, hv, hvc⟩
  have hvB := TreeSequenceInitialSegmentVertexSetSubset hshortB hv
  have hne : v ≠ T.vertex D.penultimateVertexIndex := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hv
    rcases hv with ⟨i, rfl⟩
    intro he
    have hi := congrArg Fin.val (T.vertex_injective ((hshortT.2.1 i).trans he))
    have hp := D.penultimateVertexPosition
    have hib := i.isLt
    simp only [Fin.val_castLE] at hi
    omega
  exact Finset.disjoint_left.mp (hElementary hvB hyB hne) hvc hc

private theorem helper_hterminalIncident_247.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
    let Bshort : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ));
    Bshort.length + (2 : ℕ) = T.length →
    Incident G (T.vertex D.terminalVertexIndex) (T.edge D.lastEdgeIndex) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D Bshort hshortLen
  obtain ⟨i, hi⟩ := T.attaches D.lastEdgeIndex
  have hj : D.lastEdgeIndex.succ = D.terminalVertexIndex := by
    apply Fin.ext
    have hl := D.lastEdgePosition
    have ht := D.terminalVertexPosition
    simp only [Fin.val_succ]
    omega
  change _ ∈ G.ends (T.edge D.lastEdgeIndex)
  rw [hi, hj]
  exact Sym2.mem_mk_left _ _

private theorem helper_halphaLast_259.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
    Incident G (T.vertex D.terminalVertexIndex) (T.edge D.lastEdgeIndex) →
    phi (T.edge D.lastEdgeIndex) ≠ some D.alpha := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D hterminalIncident he
  have hm := (Finset.mem_sdiff.mp D.alphaMissingTerminal).2
  apply hm
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, T.edge D.lastEdgeIndex, hterminalIncident, he⟩

private theorem helper_halphaUnused_265.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let B : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    (2 : ℕ) ≤ T.length - A.length →
    B.length + (1 : ℕ) = T.length →
    TreeSequenceInitialSegment B T →
    ((0 : ℕ) < H.dividerCount →
        A =
          H.stage
            (⟨H.dividerCount,
                by
                have := GoldbergSeymour.TreeSequence.positive T
                omega⟩ :
              Fin (H.dividerCount + (2 : ℕ)))) →
    (H.dividerCount = (0 : ℕ) → A = base.core) →
    B.vertex (Fin.last B.length) = T.vertex D.penultimateVertexIndex →
    ColoredVertexSetElementary G phi (TreeSequenceVertexSet B) →
    D.alpha ∉ TashkinovStoredColors ett.series.data (Fin.last ett.rounds) →
    let Bshort : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ));
    Bshort.length + (2 : ℕ) = T.length →
    phi (T.edge D.lastEdgeIndex) ≠ some D.alpha →
    ∀ (t : Fin T.length),
    A.length ≤ (↑t : ℕ) →
    phi (T.edge t) ≠ some D.alpha := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B htail hBlen hBT hApositive hAzero
      hBterminal hElementary halphaNotRaw Bshort hshortLen halphaLast
  have hexclusion := HierarchyTailMissingColorExclusion G k e0 input T phi
    ett base H hElementary (HierarchyFullTailLength C - 1)
    (by change 1 ≤ T.length - A.length - 1; omega)
    (by change T.length - A.length - 1 < T.length - A.length; omega)
    D.alpha (by
      change D.alpha ∈ MissingColors G phi (B.vertex (Fin.last B.length))
      rw [hBterminal]
      exact D.alphaMissingPenultimate)
  intro t ht he
  by_cases hlast : t = D.lastEdgeIndex
  · exact halphaLast (hlast ▸ he)
  · have hb : t.val < B.length := by
      have hp := D.lastEdgePosition
      have hne : t.val ≠ D.lastEdgeIndex.val := fun h => hlast (Fin.ext h)
      have htlt := t.isLt
      omega
    let tB : Fin B.length := ⟨t.val, hb⟩
    have hcast : Fin.castLE hBT.1 tB = t := Fin.ext rfl
    have heB : phi (B.edge tB) = some D.alpha := by
      rw [← hBT.2.2 tB, hcast]
      exact he
    obtain ⟨_, _, _, f, _, _, _, _, _, hs⟩ := hexclusion tB ht
      (by change tB.val < A.length + (T.length - A.length - 1); omega) heB
    exact halphaNotRaw hs

private theorem helper_firstWitness_291.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E)
      (k : ℕ) (e0 : E) (T : TreeSequence G e0) (rho : PartialEdgeColoring E k)
      (X : TreeSequence G e0),
    TreeSequenceInitialSegment X T →
    ∀ c ∈ TreeMissingColors rho X,
    c ∈ MissingColors G rho (T.vertex (HierarchyFirstMissingPosition rho T c)) ∧
      (↑(HierarchyFirstMissingPosition rho T c) : ℕ) ≤ X.length := by
  classical
  intro V E _ _ G k e0 T rho X hXT c hc
  let _ := Fintype.ofFinite V
  as_aux_lemma =>
    rcases Finset.mem_biUnion.mp hc with ⟨v, hv, hvc⟩
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hv
    rcases hv with ⟨i, rfl⟩
    let candidates := Finset.univ.filter fun j : Fin (T.length + 1) =>
      c ∈ MissingColors G rho (T.vertex j)
    have hi : Fin.castLE (Nat.succ_le_succ hXT.1) i ∈ candidates := by
      simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hXT.2.1 i]
      exact hvc
    have hn : candidates.Nonempty := ⟨_, hi⟩
    have hm := (Finset.mem_filter.mp (Finset.min'_mem candidates hn)).2
    have hle := Finset.min'_le candidates _ hi
    have hib := i.isLt
    unfold HierarchyFirstMissingPosition
    change (c ∈ MissingColors G rho (T.vertex (if h : candidates.Nonempty then
      candidates.min' h else Fin.last T.length))) ∧ _
    rw [dite_eq_left hn]
    refine ⟨hm, ?_⟩
    change (candidates.min' hn).val ≤ i.val at hle
    omega

private theorem helper_missingSubset_322.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E)
      (k : ℕ) (e0 : E) (rho : PartialEdgeColoring E k) {X Y : TreeSequence G e0},
    TreeSequenceInitialSegment X Y →
    TreeMissingColors rho X ⊆ TreeMissingColors rho Y := by
  classical
  intro V E _ _ G k e0 rho X Y hXY
  let _ := Fintype.ofFinite V
  as_aux_lemma =>
    intro c hc
    obtain ⟨v, hv, hm⟩ := Finset.mem_biUnion.mp hc
    exact Finset.mem_biUnion.mpr
      ⟨v, TreeSequenceInitialSegmentVertexSetSubset hXY hv, hm⟩

private theorem helper_missingWithoutExtra_331.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] [DecidableEq V]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (rho : PartialEdgeColoring E k)
      (X Y : TreeSequence G e0),
    ∀
      c ∉
        (TreeSequenceVertexSet X \ TreeSequenceVertexSet Y).biUnion fun (v : V) ↦
          MissingColors G rho v,
    c ∈ TreeMissingColors rho X →
    c ∈ TreeMissingColors rho Y := by
  classical
  intro V E _ _ _ G k e0 rho X Y c hc
  let _ := Fintype.ofFinite V
  as_aux_lemma =>
    intro hm
    obtain ⟨v, hv, hvc⟩ := Finset.mem_biUnion.mp hm
    have hvY : v ∈ TreeSequenceVertexSet Y := by
      by_contra hn
      exact hc (Finset.mem_biUnion.mpr ⟨v, Finset.mem_sdiff.mpr ⟨hv, hn⟩, hvc⟩)
    exact Finset.mem_biUnion.mpr ⟨v, hvY, hvc⟩

private theorem helper_leaf_344.{u_1, u_2} :
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

private theorem helper_separate_363.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E)
      (k : ℕ),
    (∀ (rho : PartialEdgeColoring E k) (a b : Fin k) (v : V),
        Sum.inl v ∈ TwoColorComponent G rho a b (Sum.inl v)) →
    (∀ (rho : PartialEdgeColoring E k) (a b : Fin k),
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
  intro V E _ _ G k self leaf rho a b hne hp u v w huv huw hvw hu hv hw hsame
  let _ := Fintype.ofFinite V
  rcases TwoColorComponentsDisjoint G rho a b (Sum.inl w) (Sum.inl u) with he | hd
  · exfalso
    obtain ⟨s, t, p, hpPath, hsupport⟩ :=
      TwoColorComponentSpanningPath G rho a b hp (Sum.inl w)
    have ends (x : V) (hx : Sum.inl x ∈ TwoColorComponent G rho a b (Sum.inl w))
        (hm : a ∈ MissingColors G rho x ∨ b ∈ MissingColors G rho x) :
        Sum.inl x = s ∨ Sum.inl x = t := by
      by_contra hnot
      push Not at hnot
      have hs : Sum.inl x ∈ p.support := by
        change Sum.inl x ∈ {z | z ∈ p.support}
        rw [hsupport]
        exact hx
      exact hpPath.isTrail.notMem_support_of_subsingleton_neighborSet
        hnot.1 hnot.2 (leaf rho a b hne hp x hm) hs
    have hue := ends u (he ▸ self rho a b u) (Or.inl hu)
    have hve := ends v (by rw [he, hsame]; exact self rho a b v) (Or.inr hv)
    have hwe := ends w (self rho a b w) hw
    rcases hue with hu | hu <;> rcases hve with hv | hv <;> rcases hwe with hw | hw
    all_goals first
      | exact huv (Sum.inl.inj (hu.trans hv.symm))
      | exact huw (Sum.inl.inj (hu.trans hw.symm))
      | exact hvw (Sum.inl.inj (hv.trans hw.symm))
  · exact hd

private theorem helper_prefixMissing_397.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base),
    let B : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    ∀ (z : V ⊕ E) (rho : PartialEdgeColoring E k) (a b : Fin k),
    a ≠ b →
    IsProperEdgeColoring G rho →
    ColoredVertexSetElementary G rho (TreeSequenceVertexSet B) →
    ∀ (u v : V),
    u ∈ TreeSequenceVertexSet B →
    v ∈ TreeSequenceVertexSet B →
    a ∈ MissingColors G rho u →
    b ∈ MissingColors G rho v →
    Sum.inl u ∉ TwoColorComponent G rho a b z →
    Sum.inl v ∉ TwoColorComponent G rho a b z →
    ∀ w ∈ TreeSequenceVertexSet B,
    MissingColors G (TwoColorComponentSwap G rho a b z) w = MissingColors G rho w := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C B z rho a b hne hp helem u v huB hvB hu hv hdu hdv
  as_aux_lemma =>
    clear_value B
    clear * - G rho a b hne hp helem u v huB hvB hu hv hdu hdv B z
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

private theorem helper_firstPreserved_455.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base),
    let B : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    TreeSequenceInitialSegment B T →
    (∀ (rho : PartialEdgeColoring E k) (X : TreeSequence G e0),
        TreeSequenceInitialSegment X T →
          ∀ c ∈ TreeMissingColors rho X,
            c ∈ MissingColors G rho (T.vertex (HierarchyFirstMissingPosition rho T c)) ∧
              (↑(HierarchyFirstMissingPosition rho T c) : ℕ) ≤ X.length) →
    ∀ (rho sigma : PartialEdgeColoring E k) (c : Fin k),
    ColoredVertexSetElementary G rho (TreeSequenceVertexSet B) →
    (∀ v ∈ TreeSequenceVertexSet B, MissingColors G sigma v = MissingColors G rho v) →
    c ∈ TreeMissingColors rho B →
    HierarchyFirstMissingPosition sigma T c = HierarchyFirstMissingPosition rho T c := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C B hBT firstWitness rho sigma c helem hmiss hc
  as_aux_lemma =>
    clear_value B
    clear * - G T B rho sigma c helem hmiss hc firstWitness hBT
    have hr := firstWitness rho B hBT c hc
    have hc' : c ∈ TreeMissingColors sigma B := by
      obtain ⟨v, hv, hm⟩ := Finset.mem_biUnion.mp hc
      exact Finset.mem_biUnion.mpr ⟨v, hv, (hmiss v hv).symm ▸ hm⟩
    have hs := firstWitness sigma B hBT c hc'
    have pref (i : Fin (T.length + 1)) (hi : i.val ≤ B.length) :
        T.vertex i ∈ TreeSequenceVertexSet B := by
      let j : Fin (B.length + 1) := ⟨i.val, Nat.lt_succ_of_le hi⟩
      have he : Fin.castLE (Nat.succ_le_succ hBT.1) j = i := Fin.ext rfl
      exact (@Finset.mem_image _ _ (Classical.decEq V)).mpr
        ⟨j, Finset.mem_univ _, (hBT.2.1 j).symm.trans (congrArg T.vertex he)⟩
    by_contra hne
    have hvne : T.vertex (HierarchyFirstMissingPosition sigma T c) ≠
        T.vertex (HierarchyFirstMissingPosition rho T c) :=
      fun he => hne (T.vertex_injective he)
    have hsOld := (hmiss _ (pref _ hs.2)) ▸ hs.1
    exact Finset.disjoint_left.mp (helem (pref _ hs.2) (pref _ hr.2) hvne) hsOld hr.1

private theorem helper_firstUnaffected_480.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E)
      (k : ℕ) (e0 : E) (T : TreeSequence G e0) (z : V ⊕ E) (rho : PartialEdgeColoring E k)
      (a b c : Fin k),
    a ≠ b →
    IsProperEdgeColoring G rho →
    c ≠ a →
    c ≠ b →
    HierarchyFirstMissingPosition (TwoColorComponentSwap G rho a b z) T c =
      HierarchyFirstMissingPosition rho T c := by
  classical
  intro V E _ _ G k e0 T z rho a b c hne hp hca hcb
  let _ := Fintype.ofFinite V
  have hb := TwoColorComponentSwapMissingBehavior G rho a b hne hp z
  have he : (Finset.univ.filter fun i : Fin (T.length + 1) =>
      c ∈ MissingColors G (TwoColorComponentSwap G rho a b z) (T.vertex i)) =
      (Finset.univ.filter fun i : Fin (T.length + 1) =>
        c ∈ MissingColors G rho (T.vertex i)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hb.2.2.2 _ c hca hcb
  unfold HierarchyFirstMissingPosition
  rw [he]

private theorem helper_seriesFacts_495.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (j : Fin (ett.rounds + (1 : ℕ))),
    IsProperEdgeColoring G (ett.series.data.coloring j) ∧
      IsOneEdgeUncolored (ett.series.data.coloring j) e0 := by
  classical
  intro V E _ _ _ G k e0 input T phi ett j
  have certificate := ett.series.certified j
  cases certificate with
  | initial triple seedLength initialColoring initialStored initialEdges initialKind
      initialVertex initialOutside initialDelta initialGamma initialClosure =>
      simpa [initialColoring] using triple.2.2.2
  | SE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
      rw [currentColoring]
      exact ⟨choice.selectedProper, choice.selectedOneUncolored⟩
  | PE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper secondStableOneUncolored
      secondStableRelation exitWitness currentColoring currentProper
      currentOneUncolored currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma closedExtension orderedExtension
      strictExtension =>
      exact ⟨currentProper, currentOneUncolored⟩
  | RE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored currentEdges
      currentKind currentVertex currentOutside currentDelta currentGamma adjoined
      adjoinedExactly closedExtension orderedExtension strictExtension =>
      rw [currentColoring]
      exact ⟨previousProper, previousOneUncolored⟩

private theorem helper_sameStar_549.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    ∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    HierarchyStarredStage P.counterexample.hierarchy
        (Fin.last P.counterexample.hierarchy.dividerCount) =
      A := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx H q A P
  have helper : ∀ (n m : ℕ) (X Y : TreeSequence G e0)
      (s : Fin (n + 2) → TreeSequence G e0) (t : Fin (m + 2) → TreeSequence G e0),
      n = m → X = Y → HEq s t →
      Fin.cases (motive := fun _ => TreeSequence G e0)
        X (fun i : Fin n => s i.succ.castSucc) (Fin.last n) =
        Fin.cases (motive := fun _ => TreeSequence G e0)
          Y (fun i : Fin m => t i.succ.castSucc) (Fin.last m) := by
    intro n m X Y s t hnm hXY hst
    subst m
    have he := eq_of_heq hst
    simp [hXY, he]
  exact (helper _ _ base.core P.replacementBase.core H.stage
    P.counterexample.hierarchy.stage P.sameGood.1.2.1 P.sameGood.1.1
    P.sameGood.1.2.2.1).symm

private theorem helper_commonPrefix_588.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
      {X Y F : TreeSequence G e0},
    TreeSequenceInitialSegment X F →
    TreeSequenceInitialSegment Y F →
    X.length ≤ Y.length →
    TreeSequenceInitialSegment X Y := by
  classical
  intro V E G e0 X Y F hXF hYF hXY
  refine ⟨hXY, ?_, ?_⟩
  · intro i
    exact (hYF.2.1 (Fin.castLE (Nat.succ_le_succ hXY) i)).symm.trans (hXF.2.1 i)
  · intro i
    exact (hYF.2.2 (Fin.castLE hXY i)).symm.trans (hXF.2.2 i)

private theorem helper_hcoreLength_597.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (_ : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    ((0 : ℕ) < H.dividerCount →
        A =
          H.stage
            (⟨H.dividerCount,
                by
                have := GoldbergSeymour.TreeSequence.positive T
                omega⟩ :
              Fin (H.dividerCount + (2 : ℕ)))) →
    (H.dividerCount = (0 : ℕ) → A = base.core) →
    base.core.length ≤ A.length := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A hApositive hAzero
  by_cases hz : H.dividerCount = 0
  · exact le_of_eq (congrArg TreeSequence.length (hAzero hz).symm)
  · rw [hApositive (Nat.pos_of_ne_zero hz)]
    have hm : Monotone (fun i : Fin (H.dividerCount + 2) => (H.stage i).length) :=
      Fin.monotone_iff_le_succ.mpr fun i => (H.nested i).1
    exact H.coreInsideFirst.1.trans (hm (show
      (⟨1, by omega⟩ : Fin (H.dividerCount + 2)) ≤
        ⟨H.dividerCount, by omega⟩ from Nat.pos_of_ne_zero hz))

private theorem helper_predecessorIncident_606.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Finite E] (G : LooplessMultigraph V E)
      (e0 : E) (T X : TreeSequence G e0),
    TreeSequenceInitialSegment X T →
    ∀ (t : Fin T.length),
    (↑t : ℕ) = X.length →
    TreeIncidentEdge X (T.edge t) := by
  classical
  intro V E _ _ G e0 T X hXT t ht
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite E
  obtain ⟨i, hi⟩ := T.attaches t
  let j : Fin (X.length + 1) := ⟨i.val, by have := i.isLt; omega⟩
  have he : Fin.castLE (Nat.succ_le_succ hXT.1) j =
      Fin.castLE (by omega : t.val + 1 ≤ T.length + 1) i := Fin.ext rfl
  refine ⟨X.vertex j, (@Finset.mem_image _ _ (Classical.decEq V)).mpr
    ⟨j, Finset.mem_univ _, rfl⟩, ?_⟩
  rw [← hXT.2.1 j, he, Incident, hi]
  exact Sym2.mem_mk_right _ _

private theorem helper_seedStable_618.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (T : TreeSequence G e0)
      {input' : PartialEdgeColoring E k} (rho sigma : PartialEdgeColoring E k)
      (ett' : ExtendedTashkinovTree G k e0 input' T rho) (base' : HierarchyBase ett' rho)
      (K : TashkinovHierarchy ett' base'),
    HierarchyWeaklyStable K (Fin.last K.dividerCount) sigma →
    K.dividerCount = (0 : ℕ) →
    StableColoring (ett'.series.data.tree (Fin.last ett'.rounds).castSucc)
      (TashkinovStoredColors ett'.series.data (Fin.last ett'.rounds)) rho sigma := by
  classical
  intro V E _ _ _ _ G k e0 T input' rho sigma ett' base' K hw hq
  have hi : (Fin.last K.dividerCount : Fin (K.dividerCount + 1)) = 0 := Fin.ext hq
  rw [hi] at hw
  change (if ett'.series.data.kind (Fin.last ett'.rounds) =
      some TashkinovExtensionKind.PE then _ else _) at hw
  split_ifs at hw with hpe
  · exact hw.1
  · exact hw

private theorem helper_weakEdges_634.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (T : TreeSequence G e0)
      {input' : PartialEdgeColoring E k} (old new : PartialEdgeColoring E k)
      (ett' : ExtendedTashkinovTree G k e0 input' T old) (base' : HierarchyBase ett' old)
      (K : TashkinovHierarchy ett' base'),
    HierarchyWeaklyStable K (Fin.last K.dividerCount) new →
    IsOneEdgeUncolored old e0 →
    IsOneEdgeUncolored new e0 →
    ∀ (t : Fin (HierarchyStarredStage K (Fin.last K.dividerCount)).length),
    new ((HierarchyStarredStage K (Fin.last K.dividerCount)).edge t) =
      old ((HierarchyStarredStage K (Fin.last K.dividerCount)).edge t) := by
  classical
  intro V E _ _ _ _ G k e0 T input' old new ett' base' K hw ho hno
  by_cases hz : K.dividerCount = 0
  · have hi : (Fin.last K.dividerCount : Fin (K.dividerCount + 1)) = 0 := Fin.ext hz
    rw [hi] at hw ⊢
    exact P2813_T1_BaseDisplayedEdges G k e0 input' T old ett' base' new ho hno hw
  · have hi : (Fin.last K.dividerCount : Fin (K.dividerCount + 1)) =
        (⟨K.dividerCount - 1, by omega⟩ : Fin K.dividerCount).succ :=
      Fin.ext (by simp only [Fin.val_last, Fin.val_succ]; omega)
    rw [hi] at hw ⊢
    intro t
    have hinv := hw.2
    by_cases ht : 1 ≤ t.val
    · exact hinv.1 t ht
    · let S := HierarchyStarredStage K
        (⟨K.dividerCount - 1, by omega⟩ : Fin K.dividerCount).succ
      have he : t = ⟨0, S.positive⟩ := Fin.ext (by change t.val = 0; omega)
      rw [he, S.first_edge, hno.1, ho.1]

private theorem helper_hbetaTheta_676.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    (2 : ℕ) ≤ T.length - A.length →
    ∀ (beta : Fin k),
    (∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → phi (T.edge t) ≠ some beta) →
    beta ≠ D.theta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A htail beta hbetaUnused he
  exact hbetaUnused D.lastEdgeIndex (by
    have hp := D.lastEdgePosition
    clear * - hp htail
    omega) (D.thetaOnLastEdge.trans (congrArg some he.symm))

private theorem helper_hby_688.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
    let Bshort : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ));
    Bshort.length + (2 : ℕ) = T.length →
    ∀ (beta : Fin k),
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    beta ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T beta)) ∧
        (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ Bshort.length →
    T.vertex ib ≠ T.vertex D.penultimateVertexIndex := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D Bshort hshortLen beta ib hbFirst he
  have hi := congrArg Fin.val (T.vertex_injective he)
  have hp := D.penultimateVertexPosition
  have hb : ib.val ≤ Bshort.length := hbFirst.2
  clear * - hi hp hb hshortLen
  omega

private theorem helper_hbt_695.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
    let Bshort : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ));
    Bshort.length + (2 : ℕ) = T.length →
    ∀ (beta : Fin k),
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    beta ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T beta)) ∧
        (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ Bshort.length →
    T.vertex ib ≠ T.vertex D.terminalVertexIndex := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D Bshort hshortLen beta ib hbFirst he
  have hi := congrArg Fin.val (T.vertex_injective he)
  have hp := D.terminalVertexPosition
  have hb : ib.val ≤ Bshort.length := hbFirst.2
  clear * - hi hp hb hshortLen
  omega

private theorem helper_hyt_702.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
    T.vertex D.penultimateVertexIndex ≠ T.vertex D.terminalVertexIndex := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D he
  have hi := congrArg Fin.val (T.vertex_injective he)
  have hp := D.penultimateVertexPosition
  have ht := D.terminalVertexPosition
  clear * - hi hp ht
  omega

private theorem helper_firstAfter_715.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    TreeSequenceInitialSegment A T →
    ∀ (rho : PartialEdgeColoring E k),
    ∀ c ∈ MissingColors G rho (T.vertex (HierarchyFirstMissingPosition rho T c)),
    c ∉ TreeMissingColors rho A →
    A.length < (↑(HierarchyFirstMissingPosition rho T c) : ℕ) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q A hAT rho c hc hn
  by_contra h
  have hi : (HierarchyFirstMissingPosition rho T c).val ≤ A.length := Nat.le_of_not_gt h
  let i : Fin (A.length + 1) := ⟨(HierarchyFirstMissingPosition rho T c).val, by omega⟩
  have he : Fin.castLE (Nat.succ_le_succ hAT.1) i =
      HierarchyFirstMissingPosition rho T c := Fin.ext rfl
  apply hn
  refine Finset.mem_biUnion.mpr ⟨A.vertex i, (@Finset.mem_image _ _ (Classical.decEq V)).mpr ⟨i,
      Finset.mem_univ _, rfl⟩, ?_⟩
  rw [← hAT.2.1 i, he]
  exact hc

private theorem helper_hsame_747.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let B : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    HierarchyFirstMissingPosition phi T D.alpha = D.penultimateVertexIndex →
    D.alpha ∉ TashkinovStoredColors ett.series.data (Fin.last ett.rounds) →
    let Bshort : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ));
    ∀ beta ∈ TreeMissingColors phi Bshort,
    (∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → phi (T.edge t) ≠ some beta) →
    beta ∉ HierarchyStoredColorsAt H q →
    (H.dividerCount = (0 : ℕ) →
        beta ∈ TreeMissingColors phi A →
          beta ∈
            TreeMissingColors phi (ett.series.data.tree (Fin.last ett.rounds).castSucc)) →
    (beta ∉ TreeMissingColors phi A → D.theta ∉ HierarchyStoredColorsAt H q) →
    (∀ eta ∈ HierarchyStoredColorsAt H q,
        beta ∈ C.good.gamma q eta → eta = D.theta ∨ eta ∈ TreeMissingColors phi Bshort) →
    beta ≠ D.alpha →
    beta ≠ D.theta →
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    beta ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T beta)) ∧
        (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ Bshort.length →
    T.vertex ib ∈ TreeSequenceVertexSet B →
    T.vertex ib ≠ T.vertex D.penultimateVertexIndex →
    T.vertex ib ≠ T.vertex D.terminalVertexIndex →
    TreeVertexOrder T (T.vertex ib) (T.vertex D.penultimateVertexIndex) →
    (beta ∉ TreeMissingColors phi A →
        beta ∉ TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) →
    beta ∈ TreeMissingColors phi B ∧ D.alpha ∈ TreeMissingColors phi B →
    (let H : TashkinovHierarchy ett base := C.hierarchy;
      have q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
      have n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
      have A : TreeSequence G e0 := HierarchyStarredStage H q;
      have Tnq : TreeSequence G e0 :=
        H.stage
          (⟨H.dividerCount, by
              have := GoldbergSeymour.TreeSequence.positive T
              omega⟩ :
            Fin (H.dividerCount + (2 : ℕ)));
      have Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
      have Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
      have Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q;
      have va : V := T.vertex (HierarchyFirstMissingPosition phi T beta);
      have vb : V := T.vertex (HierarchyFirstMissingPosition phi T D.alpha);
      have sameComponent : Prop :=
        TwoColorComponent G phi beta D.alpha (Sum.inl va) =
          TwoColorComponent G phi beta D.alpha (Sum.inl vb);
      ((0 : ℕ) < H.dividerCount ∧
            (beta ∈ TreeMissingColors phi Tnq ∨
              Disjoint (insert beta ({ D.alpha } : Finset (Fin k)) : Finset (Fin k)) Dnq) →
          sameComponent) ∧
        (H.dividerCount = (0 : ℕ) ∧
              (beta ∈ TreeMissingColors phi Tn ∨
                Disjoint (insert beta ({ D.alpha } : Finset (Fin k)) : Finset (Fin k)) Dn) →
            sameComponent) ∧
          (beta ∈ TreeMissingColors phi A ∧
              TreeColorSetClosed G phi A ({ beta } : Finset (Fin k)) →
            sameComponent ∧ TreeInterchangeable G A phi beta D.alpha)) →
    TwoColorComponent G phi beta D.alpha (Sum.inl (T.vertex ib)) =
      TwoColorComponent G phi beta D.alpha (Sum.inl (T.vertex D.penultimateVertexIndex)) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B hfirstAlpha halphaNotRaw Bshort
      beta hbetaMissing hbetaUnused hbetaStored hzero houtside hcutoff hbetaAlpha hbetaTheta ib
      hbFirst hibB hby hbt horder hrawBeta hmissing hchange
  rw [← hfirstAlpha]
  by_cases hz : H.dividerCount = 0
  · apply hchange.2.1
    refine ⟨hz, ?_⟩
    by_cases hm : beta ∈ TreeMissingColors phi A
    · exact Or.inl (hzero hz hm)
    · right
      rw [Finset.disjoint_left]
      intro c hc hd
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact hrawBeta hm hd
      · exact halphaNotRaw (Finset.mem_singleton.mp hc ▸ hd)
  · apply hchange.1
    refine ⟨Nat.pos_of_ne_zero hz, Or.inr ?_⟩
    rw [Finset.disjoint_left]
    intro c hc hd
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact hbetaStored hd
    · exact D.alphaOutsideStored (Finset.mem_singleton.mp hc ▸ hd)

private theorem helper_branch_815.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let B : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    ∀ (beta : Fin k),
    beta ≠ D.alpha →
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    beta ∈ TreeMissingColors phi B ∧ D.alpha ∈ TreeMissingColors phi B →
    let z : V ⊕ E := Sum.inl (T.vertex D.terminalVertexIndex);
    let muOne : PartialEdgeColoring E k := TwoColorComponentSwap G phi beta D.alpha z;
    Disjoint
        (TwoColorComponent G phi beta D.alpha (Sum.inl (T.vertex D.terminalVertexIndex)))
        (TwoColorComponent G phi beta D.alpha (Sum.inl (T.vertex ib))) →
    TwoColorPathComponent G phi beta D.alpha z →
    (∀ w ∈ TreeSequenceVertexSet B,
        MissingColors G (TwoColorComponentSwap G phi beta D.alpha z) w =
          MissingColors G phi w) →
    (∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → muOne (T.edge t) = phi (T.edge t)) →
    (∀ c ∈ HierarchyStoredColorsAt H q,
        HierarchyFirstMissingPosition muOne T c = HierarchyFirstMissingPosition phi T c) →
    (beta ∈ TreeMissingColors phi A →
        (0 : ℕ) < H.dividerCount ∧
            beta ∈
              TreeMissingColors phi
                (H.stage
                  (⟨H.dividerCount,
                      by
                      have := GoldbergSeymour.TreeSequence.positive T
                      omega⟩ :
                    Fin (H.dividerCount + (2 : ℕ)))) ∨
          H.dividerCount = (0 : ℕ) ∧
            beta ∈
              TreeMissingColors phi (ett.series.data.tree (Fin.last ett.rounds).castSucc)) →
    beta ∈ TreeMissingColors phi A →
    ∃ (corrOne : CorrespondingExtendedTashkinovTree G k e0 ett muOne T),
    MaximumProperty corrOne.replacementETT ∧
      ∃ (baseOne : HierarchyBase corrOne.replacementETT muOne) (KOne :
        TashkinovHierarchy corrOne.replacementETT baseOne) (goodOne : GoodHierarchy KOne),
        SameGoodHierarchy C.good goodOne := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B beta hbetaAlpha ib hmissing z
      muOne hdisjoint hpath hmissingOne hfixedOne hstoredOne hcase hm
  exact (StableChangeCasesOneTwoFullTail G k e0 input T phi ett base C ctx
    beta D.alpha hbetaAlpha hmissing z hpath muOne rfl
    (by dsimp only; rcases hcase hm with hpos | ⟨hz, hn⟩
        · exact Or.inl hpos
        · exact Or.inr ⟨hz, Or.inl hn⟩)
    hdisjoint hfixedOne hmissingOne hstoredOne).2.2.2.2

private theorem helper_branch_821.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let B : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    TreeSequenceInitialSegment A T →
    ColoredVertexSetElementary G phi (TreeSequenceVertexSet B) →
    HierarchyFirstMissingPosition phi T D.alpha = D.penultimateVertexIndex →
    let Bshort : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ));
    ∀ (beta : Fin k),
    (∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → phi (T.edge t) ≠ some beta) →
    beta ∉ HierarchyStoredColorsAt H q →
    beta ≠ D.alpha →
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    beta ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T beta)) ∧
        (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ Bshort.length →
    TreeVertexOrder T (T.vertex ib) (T.vertex D.penultimateVertexIndex) →
    (∀ (rho : PartialEdgeColoring E k),
        ∀ c ∈ MissingColors G rho (T.vertex (HierarchyFirstMissingPosition rho T c)),
          c ∉ TreeMissingColors rho A →
            A.length < (↑(HierarchyFirstMissingPosition rho T c) : ℕ)) →
    beta ∈ TreeMissingColors phi B ∧ D.alpha ∈ TreeMissingColors phi B →
    let z : V ⊕ E := Sum.inl (T.vertex D.terminalVertexIndex);
    let muOne : PartialEdgeColoring E k := TwoColorComponentSwap G phi beta D.alpha z;
    beta ∉ TreeMissingColors phi A →
    ∃ (corrOne : CorrespondingExtendedTashkinovTree G k e0 ett muOne T),
    MaximumProperty corrOne.replacementETT ∧
      ∃ (baseOne : HierarchyBase corrOne.replacementETT muOne) (KOne :
        TashkinovHierarchy corrOne.replacementETT baseOne) (goodOne : GoodHierarchy KOne),
        SameGoodHierarchy C.good goodOne := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B hAT hElementary hfirstAlpha
      Bshort beta hbetaUnused hbetaStored hbetaAlpha ib hbFirst horder firstAfter hmissing z
      muOne hm
  have ha := firstAfter phi beta hbFirst.1 hm
  exact (StableChangeCaseThree G k e0 input T phi ett base C
    ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
    ctx.lexicographicMinimality hElementary ctx.largeMissingSet
    beta D.alpha hbetaAlpha hmissing z muOne rfl
    (by
      intro u hu
      obtain ⟨i, _, rfl⟩ := (@Finset.mem_image _ _ (Classical.decEq V)).mp hu
      exact ⟨Fin.castLE (Nat.succ_le_succ hAT.1) i, ib, hAT.2.1 i, rfl, by
        change i.val < ib.val
        have hi : i.val ≤ A.length := Nat.le_of_lt_succ i.isLt
        exact lt_of_le_of_lt hi ha⟩)
    (by rw [hfirstAlpha]; exact horder)
    ⟨hbetaStored, D.alphaOutsideStored⟩
    (by
      intro hc
      obtain ⟨t, ht, _, he⟩ := (Finset.mem_filter.mp hc).2
      exact hbetaUnused t (by clear * - ha ht; omega) he)).2.2.2.2

private theorem helper_hcaseOne_906.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (_ : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let B : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    B.length + (1 : ℕ) = T.length →
    TreeSequenceInitialSegment B T →
    (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage P.counterexample.hierarchy
            (Fin.last P.counterexample.hierarchy.dividerCount) =
          A) →
    (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        P.corresponding.replacementETT.series.data.tree
            (Fin.last P.corresponding.replacementETT.rounds).castSucc =
          ett.series.data.tree (Fin.last ett.rounds).castSucc) →
    (∀ {X Y F : TreeSequence G e0},
        TreeSequenceInitialSegment X F →
          TreeSequenceInitialSegment Y F →
            X.length ≤ Y.length → TreeSequenceInitialSegment X Y) →
    ∀ (beta : Fin k),
    (H.dividerCount = (0 : ℕ) →
        beta ∈ TreeMissingColors phi A →
          beta ∈
            TreeMissingColors phi (ett.series.data.tree (Fin.last ett.rounds).castSucc)) →
    ∀ (POne : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let rho : PartialEdgeColoring E k := POne.coloring;
    let ettOne :
      ExtendedTashkinovTree G k e0 POne.corresponding.replacementInput T POne.coloring :=
      POne.corresponding.replacementETT;
    let COne' : HierarchyCounterexample POne.replacementBase := POne.counterexample;
    let HOne : TashkinovHierarchy POne.corresponding.replacementETT POne.replacementBase :=
      COne'.hierarchy;
    let _ : Fin (HOne.dividerCount + (1 : ℕ)) := Fin.last HOne.dividerCount;
    (∀ (X : TreeSequence G e0),
        TreeSequenceInitialSegment X B →
          TreeMissingColors rho X = TreeMissingColors phi X) →
    TreeMissingColors rho A = TreeMissingColors phi A →
    beta ∈ TreeMissingColors phi A →
    (0 : ℕ) < HOne.dividerCount ∧
        beta ∈
          TreeMissingColors rho
            (HOne.stage
              (⟨HOne.dividerCount,
                  by
                  have := GoldbergSeymour.TreeSequence.positive T
                  omega⟩ :
                Fin (HOne.dividerCount + (2 : ℕ)))) ∨
      HOne.dividerCount = (0 : ℕ) ∧
        beta ∈
          TreeMissingColors rho (ettOne.series.data.tree (Fin.last ettOne.rounds).castSucc) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B hBlen hBT sameStar sameTn
      commonPrefix beta hzero POne rho ettOne COne' HOne qOne missingEq hmissingA hm
  have hcount : H.dividerCount = HOne.dividerCount := POne.sameGood.1.2.1
  by_cases hz : HOne.dividerCount = 0
  · refine Or.inr ⟨hz, ?_⟩
    rw [sameTn POne]
    have hTnB := commonPrefix ett.abovePenultimate hBT (by
      have hs := ett.strictAbovePenultimate
      clear * - hs hBlen
      omega)
    change TreeSequenceInitialSegment
      (ett.series.data.tree (Fin.last ett.rounds).castSucc) B at hTnB
    rw [missingEq _ hTnB]
    exact hzero (hcount.trans hz) hm
  · refine Or.inl ⟨Nat.pos_of_ne_zero hz, ?_⟩
    have hi : qOne =
        (⟨HOne.dividerCount - 1, by omega⟩ : Fin HOne.dividerCount).succ :=
      Fin.ext (by simp only [qOne, Fin.val_last, Fin.val_succ]; omega)
    have hs := sameStar POne
    change HierarchyStarredStage HOne qOne = A at hs
    rw [hi] at hs
    have hind : (⟨HOne.dividerCount - 1, by omega⟩ : Fin HOne.dividerCount).succ.castSucc =
        (⟨HOne.dividerCount, by omega⟩ : Fin (HOne.dividerCount + 2)) :=
      Fin.ext (by simp only [Fin.val_succ, Fin.val_castSucc]; omega)
    change HOne.stage _ = A at hs
    rw [hind] at hs
    rw [hs, hmissingA]
    exact hm

private theorem helper_hsameTwo_964.{u_1, u_2} :
    helperHsameTwo964Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B hnotA Bshort sameStar sameLast
      beta hbetaMissing hbetaUnused hbetaStored hzero houtside hcutoff hbetaAlpha hbetaTheta ib
      hbFirst hibB hby hbt horder hrawBeta hmissing hchange hsame z muOne hdisjoint hpath
      houtsideBeta houtsideAlpha hmissingOne hfixedOne hstoredOne hcase corrOne hmaxOne baseOne
      KOne goodOne hsameOne hbTerminalOne POne hPOne rho ettOne baseOne' COne' HOne qOne
      hmissingA hbetaStoredOne hgammaPenOne hgammaTermOne hgammaWitnessOne' hfirstGammaOne
      hfirstThetaOne hgammaUnusedOne hcaseOne hmissingPairOne hchangeOne
  rw [← hfirstGammaOne, ← hfirstThetaOne]
  by_cases hm : beta ∈ TreeMissingColors phi A
  · rcases hcaseOne hm with ⟨hp, hb⟩ | ⟨hz, hb⟩
    · exact hchangeOne.1 ⟨hp, Or.inl hb⟩
    · exact hchangeOne.2.1 ⟨hz, Or.inl hb⟩
  · have hnTheta : D.theta ∉ HierarchyStoredColorsAt HOne qOne := by
      rw [← (sameLast POne).1]
      exact houtside hm
    by_cases hz : HOne.dividerCount = 0
    · apply hchangeOne.2.1
      refine ⟨hz, Or.inr ?_⟩
      rw [Finset.disjoint_left]
      intro c hc hd
      rcases Finset.mem_insert.mp hc with rfl | hc
      · apply hbetaStoredOne
        refine Finset.mem_sdiff.mpr ⟨hd, ?_⟩
        rw [sameStar POne, hmissingA]
        exact hm
      · have he : c = D.theta := Finset.mem_singleton.mp hc
        subst c
        apply hnTheta
        refine Finset.mem_sdiff.mpr ⟨hd, ?_⟩
        rw [sameStar POne, hmissingA]
        exact hnotA (c := D.theta) D.thetaMissingPenultimate
    · apply hchangeOne.1
      refine ⟨Nat.pos_of_ne_zero hz, Or.inr ?_⟩
      rw [Finset.disjoint_left]
      intro c hc hd
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact hbetaStoredOne hd
      · exact hnTheta (Finset.mem_singleton.mp hc ▸ hd)

private theorem helper_hstoredTwo_1017.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
    let B : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    (∀ (rho sigma : PartialEdgeColoring E k) (c : Fin k),
        ColoredVertexSetElementary G rho (TreeSequenceVertexSet B) →
          (∀ v ∈ TreeSequenceVertexSet B, MissingColors G sigma v = MissingColors G rho v) →
            c ∈ TreeMissingColors rho B →
              HierarchyFirstMissingPosition sigma T c =
                HierarchyFirstMissingPosition rho T c) →
    (∀ (z : V ⊕ E) (rho : PartialEdgeColoring E k) (a b c : Fin k),
        a ≠ b →
          IsProperEdgeColoring G rho →
            c ≠ a →
              c ≠ b →
                HierarchyFirstMissingPosition (TwoColorComponentSwap G rho a b z) T c =
                  HierarchyFirstMissingPosition rho T c) →
    ∀ (beta : Fin k),
    beta ≠ D.theta →
    let z : V ⊕ E := Sum.inl (T.vertex D.terminalVertexIndex);
    ∀ (POne : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let rho : PartialEdgeColoring E k := POne.coloring;
    let COne' : HierarchyCounterexample POne.replacementBase := POne.counterexample;
    let _ :
      HierarchyMinimumCounterexampleContext G k e0 POne.corresponding.replacementInput T
        POne.coloring POne.corresponding.replacementETT POne.replacementBase
        POne.counterexample :=
      POne.minimumContext;
    let HOne : TashkinovHierarchy POne.corresponding.replacementETT POne.replacementBase :=
      COne'.hierarchy;
    let qOne : Fin (HOne.dividerCount + (1 : ℕ)) := Fin.last HOne.dividerCount;
    ColoredVertexSetElementary G rho (TreeSequenceVertexSet B) →
    beta ∉ HierarchyStoredColorsAt HOne qOne →
    beta ∈ TreeMissingColors rho B ∧ D.theta ∈ TreeMissingColors rho B →
    let muTwo : PartialEdgeColoring E k := TwoColorComponentSwap G rho beta D.theta z;
    (∀ w ∈ TreeSequenceVertexSet B,
        MissingColors G (TwoColorComponentSwap G rho beta D.theta z) w =
          MissingColors G rho w) →
    ∀ c ∈ HierarchyStoredColorsAt HOne qOne,
    HierarchyFirstMissingPosition muTwo T c = HierarchyFirstMissingPosition rho T c := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D B firstPreserved firstUnaffected beta
      hbetaTheta z POne rho COne' ctxOne HOne qOne hElementaryOne hbetaStoredOne hmissingPairOne
      muTwo hmissingTwo c hc
  have hcb : c ≠ beta := fun he => hbetaStoredOne (he ▸ hc)
  by_cases hct : c = D.theta
  · exact hct.symm ▸
      firstPreserved rho muTwo D.theta hElementaryOne hmissingTwo hmissingPairOne.2
  · exact firstUnaffected z rho beta D.theta c hbetaTheta ctxOne.proper hcb hct

private theorem helper_hthetaLastOne_1025.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    (2 : ℕ) ≤ T.length - A.length →
    ∀ (beta : Fin k),
    let z : V ⊕ E := Sum.inl (T.vertex D.terminalVertexIndex);
    let muOne : PartialEdgeColoring E k := TwoColorComponentSwap G phi beta D.alpha z;
    (∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → muOne (T.edge t) = phi (T.edge t)) →
    ∀ (POne : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    POne.coloring = muOne →
    let rho : PartialEdgeColoring E k := POne.coloring;
    rho (T.edge D.lastEdgeIndex) = some D.theta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A htail beta z muOne hfixedOne POne
      hPOne rho
  rw [show rho = muOne from hPOne, hfixedOne D.lastEdgeIndex (by
    have hl := D.lastEdgePosition
    clear * - hl htail
    omega)]
  exact D.thetaOnLastEdge

private theorem helper_hsuffix_1031.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
    let B : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    B.length + (1 : ℕ) = T.length →
    TreeSequenceInitialSegment B T →
    ∀ (beta : Fin k)
      (POne : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let rho : PartialEdgeColoring E k := POne.coloring;
    beta ∈ TreeMissingColors rho B ∧ D.theta ∈ TreeMissingColors rho B →
    rho (T.edge D.lastEdgeIndex) = some D.theta →
    TashkinovAugmentationSequence rho B T := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D B hBlen hBT beta POne rho hmissingPairOne
      hthetaLastOne
  apply Relation.ReflTransGen.single
  refine ⟨hBlen.symm, hBT, D.theta, ?_, hmissingPairOne.2⟩
  have hi : Fin.cast hBlen (Fin.last B.length) = D.lastEdgeIndex :=
    Fin.ext (by
      have hl := D.lastEdgePosition
      simp only [Fin.val_cast, Fin.val_last]
      clear * - hBlen hl
      omega)
  rw [hi]
  exact hthetaLastOne

private theorem helper_hgammaCutoff_1047.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let B : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    ColoredVertexSetElementary G phi (TreeSequenceVertexSet B) →
    (∀ {c : Fin k},
        c ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex) →
          c ∉ TreeMissingColors phi A) →
    let Bshort : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ));
    TreeSequenceInitialSegment Bshort T →
    TreeSequenceInitialSegment Bshort B →
    (∀ (rho : PartialEdgeColoring E k) (X : TreeSequence G e0),
        TreeSequenceInitialSegment X T →
          ∀ c ∈ TreeMissingColors rho X,
            c ∈ MissingColors G rho (T.vertex (HierarchyFirstMissingPosition rho T c)) ∧
              (↑(HierarchyFirstMissingPosition rho T c) : ℕ) ≤ X.length) →
    (∀ (rho : PartialEdgeColoring E k) {X Y : TreeSequence G e0},
        TreeSequenceInitialSegment X Y →
          TreeMissingColors rho X ⊆ TreeMissingColors rho Y) →
    (∀ (rho sigma : PartialEdgeColoring E k) (c : Fin k),
        ColoredVertexSetElementary G rho (TreeSequenceVertexSet B) →
          (∀ v ∈ TreeSequenceVertexSet B, MissingColors G sigma v = MissingColors G rho v) →
            c ∈ TreeMissingColors rho B →
              HierarchyFirstMissingPosition sigma T c =
                HierarchyFirstMissingPosition rho T c) →
    (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStoredColorsAt H q =
            HierarchyStoredColorsAt P.counterexample.hierarchy
              (Fin.last P.counterexample.hierarchy.dividerCount) ∧
          ∀ eta ∈ HierarchyStoredColorsAt H q,
            C.good.gamma q eta =
              P.counterexample.good.gamma (Fin.last P.counterexample.hierarchy.dividerCount)
                eta) →
    ∀ (beta : Fin k),
    (∀ eta ∈ HierarchyStoredColorsAt H q,
        beta ∈ C.good.gamma q eta → eta = D.theta ∨ eta ∈ TreeMissingColors phi Bshort) →
    ∀ (POne : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let rho : PartialEdgeColoring E k := POne.coloring;
    let COne' : HierarchyCounterexample POne.replacementBase := POne.counterexample;
    let HOne : TashkinovHierarchy POne.corresponding.replacementETT POne.replacementBase :=
      COne'.hierarchy;
    let qOne : Fin (HOne.dividerCount + (1 : ℕ)) := Fin.last HOne.dividerCount;
    (∀ v ∈ TreeSequenceVertexSet B, MissingColors G rho v = MissingColors G phi v) →
    (↑(HierarchyFirstMissingPosition rho T D.theta) : ℕ) ≤ B.length →
    ∀ c ∈ HierarchyStoredColorsAt HOne qOne,
    beta ∈ POne.counterexample.good.gamma qOne c ∨
        D.theta ∈ POne.counterexample.good.gamma qOne c →
    (↑(HierarchyFirstMissingPosition rho T c) : ℕ) ≤ B.length := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B hElementary hnotA Bshort hshortT
      hshortB firstWitness missingSubset firstPreserved sameLast beta hcutoff POne rho COne' HOne
      qOne hmissingOne' hthetaBound c hc hpair
  have hcOld : c ∈ HierarchyStoredColorsAt H q :=
    Finset.subset_of_eq (sameLast POne).1.symm hc
  have hpairOld : beta ∈ C.good.gamma q c ∨ D.theta ∈ C.good.gamma q c :=
    ((sameLast POne).2 c hcOld).symm ▸ hpair
  rcases hpairOld with hb | ht
  · rcases hcutoff c hcOld hb with he | hm
    · exact he.symm ▸ hthetaBound
    · have hmB : c ∈ TreeMissingColors phi B := missingSubset (X := Bshort) (Y := B) phi hshortB hm
      exact (le_of_eq (congrArg Fin.val
        (firstPreserved phi rho c hElementary hmissingOne' hmB))).trans
          ((firstWitness phi Bshort hshortT c hm).2.trans hshortB.1)
  · exact False.elim (hnotA (c := D.theta) D.thetaMissingPenultimate
      ((GoodHierarchyReservedDisjoint C.good q).1 c hcOld ht))

private theorem helper_hfixedPrefix_1144.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let B : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    TreeSequenceInitialSegment A T →
    ∀ (beta : Fin k),
    let z : V ⊕ E := Sum.inl (T.vertex D.terminalVertexIndex);
    ∀ (POne : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let rho : PartialEdgeColoring E k := POne.coloring;
    let muTwo : PartialEdgeColoring E k := TwoColorComponentSwap G rho beta D.theta z;
    (∀ (t : Fin T.length),
        A.length ≤ (↑t : ℕ) → (↑t : ℕ) < B.length → muTwo (T.edge t) = rho (T.edge t)) →
    (∀ (t : Fin A.length), muTwo (A.edge t) = rho (A.edge t)) →
    ∀ (t : Fin T.length),
    (↑t : ℕ) < B.length →
    muTwo (T.edge t) = rho (T.edge t) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B hAT beta z POne rho muTwo
      hfixedTailTwo hfixedCore t ht
  by_cases ha : t.val < A.length
  · let ta : Fin A.length := ⟨t.val, ha⟩
    have he : Fin.castLE hAT.1 ta = t := Fin.ext rfl
    rw [← he, hAT.2.2 ta]
    exact hfixedCore ta
  · exact hfixedTailTwo t (Nat.le_of_not_gt ha) ht

private theorem helper_transportRoute_1153.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let B : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    (2 : ℕ) ≤ T.length - A.length →
    TreeSequenceInitialSegment B T →
    (∀ {X Y F : TreeSequence G e0},
        TreeSequenceInitialSegment X F →
          TreeSequenceInitialSegment Y F →
            X.length ≤ Y.length → TreeSequenceInitialSegment X Y) →
    ∀ (beta : Fin k),
    let z : V ⊕ E := Sum.inl (T.vertex D.terminalVertexIndex);
    ∀ (POne : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let rho : PartialEdgeColoring E k := POne.coloring;
    let muTwo : PartialEdgeColoring E k := TwoColorComponentSwap G rho beta D.theta z;
    (∀ w ∈ TreeSequenceVertexSet B,
        MissingColors G (TwoColorComponentSwap G rho beta D.theta z) w =
          MissingColors G rho w) →
    beta ∈ TreeMissingColors phi A →
    (∀ (t : Fin T.length), (↑t : ℕ) < B.length → muTwo (T.edge t) = rho (T.edge t)) →
    ∀ (S : TreeSequence G e0),
    TashkinovAugmentationSequence rho S B →
    TashkinovAugmentationSequence muTwo S B := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B htail hBT commonPrefix beta z
      POne rho muTwo hmissingTwo hm hfixedPrefix S hs
  clear * - G T B rho muTwo hBT hfixedPrefix hmissingTwo commonPrefix hs
  unfold TashkinovAugmentationSequence at hs ⊢
  induction hs using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | @head X Y hstep htail ih =>
    have hYB := TashkinovAugmentationSequenceInitialSegment rho Y B htail
    obtain ⟨hlen, hXY, c, hedge, hm⟩ := hstep
    have hXB : TreeSequenceInitialSegment X B :=
      ⟨hXY.1.trans hYB.1,
        fun i => (hYB.2.1 (Fin.castLE (Nat.succ_le_succ hXY.1) i)).trans (hXY.2.1 i),
        fun i => (hYB.2.2 (Fin.castLE hXY.1 i)).trans (hXY.2.2 i)⟩
    refine Relation.ReflTransGen.head ⟨hlen, hXY, c, ?_, ?_⟩ ih
    · let tY : Fin Y.length := Fin.cast hlen.symm (Fin.last X.length)
      let tB : Fin B.length := Fin.castLE hYB.1 tY
      have hf := hfixedPrefix (Fin.castLE hBT.1 tB) tB.isLt
      rw [hBT.2.2 tB, hYB.2.2 tY] at hf
      exact hf.trans hedge
    · obtain ⟨v, hv, hvc⟩ := Finset.mem_biUnion.mp hm
      exact Finset.mem_biUnion.mpr ⟨v, hv,
        (hmissingTwo v (TreeSequenceInitialSegmentVertexSetSubset hXB hv)).symm ▸ hvc⟩

private theorem helper_hrouteTwo_1176.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let B : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    (2 : ℕ) ≤ T.length - A.length →
    B.length + (1 : ℕ) = T.length →
    TreeSequenceInitialSegment B T →
    (∀ {X Y F : TreeSequence G e0},
        TreeSequenceInitialSegment X F →
          TreeSequenceInitialSegment Y F →
            X.length ≤ Y.length → TreeSequenceInitialSegment X Y) →
    base.core.length ≤ A.length →
    ∀ (beta : Fin k),
    let z : V ⊕ E := Sum.inl (T.vertex D.terminalVertexIndex);
    ∀ (POne : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let rho : PartialEdgeColoring E k := POne.coloring;
    let ettOne :
      ExtendedTashkinovTree G k e0 POne.corresponding.replacementInput T POne.coloring :=
      POne.corresponding.replacementETT;
    let _ : HierarchyBase POne.corresponding.replacementETT POne.coloring :=
      POne.replacementBase;
    let muTwo : PartialEdgeColoring E k := TwoColorComponentSwap G rho beta D.theta z;
    (∀ (S : TreeSequence G e0),
        TashkinovAugmentationSequence rho S B → TashkinovAugmentationSequence muTwo S B) →
    ettOne.series.data.kind (Fin.last ettOne.rounds) = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence muTwo
          (ettOne.series.data.tree (Fin.last ettOne.rounds).castSucc) B ∨
      (ettOne.series.data.kind (Fin.last ettOne.rounds) = some TashkinovExtensionKind.SE ∨
          ettOne.series.data.kind (Fin.last ettOne.rounds) =
            some TashkinovExtensionKind.RE) ∧
        ∃ (f : E) (seed : TreeSequence G e0),
          ettOne.series.data.connectingEdges (Fin.last ettOne.rounds) = ({ f } : Finset E) ∧
            TreeSequenceAdjoinEdge
                (ettOne.series.data.tree (Fin.last ettOne.rounds).castSucc) f seed ∧
              TashkinovAugmentationSequence muTwo seed B := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B htail hBlen hBT commonPrefix
      hcoreLength beta z POne rho ettOne baseOne' muTwo transportRoute
  rcases P2813_T1_TerminalRoute G k e0 POne.corresponding.replacementInput T rho ettOne with
    ⟨hp, hseq⟩ | ⟨hp, f, seed, hedges, hseed, _, _, hseq⟩
  · have hTnB := commonPrefix ettOne.abovePenultimate hBT (by
      have hs := ettOne.strictAbovePenultimate
      clear * - hs hBlen
      omega)
    exact Or.inl ⟨hp, transportRoute _ (TashkinovAugmentationSequenceRestrict rho _ B T
      hseq hTnB hBT)⟩
  · have hseedT := TashkinovAugmentationSequenceInitialSegment rho seed T hseq
    have hTnCore : (ettOne.series.data.tree (Fin.last ettOne.rounds).castSucc).length ≤
        baseOne'.core.length := by
      have hnp : ettOne.series.data.kind (Fin.last ettOne.rounds) ≠
          some TashkinovExtensionKind.PE := by
        intro he
        rcases hp with he' | he' <;> rw [he'] at he <;> cases he
      rw [baseOne'.nonparallel hnp]
    have hcLen : baseOne'.core.length ≤ A.length := by
      rw [← POne.sameGood.1.1]
      exact hcoreLength
    have hsLen : seed.length ≤ B.length := by
      have hl := hseed.1
      change seed.length = (ettOne.series.data.tree (Fin.last ettOne.rounds).castSucc).length + 1
          at hl
      clear * - hl hTnCore hcLen htail hBlen
      omega
    have hseedB := commonPrefix hseedT hBT hsLen
    exact Or.inr ⟨hp, f, seed, hedges, hseed,
      transportRoute seed (TashkinovAugmentationSequenceRestrict rho seed B T hseq hseedB hBT)⟩

private theorem helper_branch_1228.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let B : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    TreeSequenceInitialSegment A T →
    (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage P.counterexample.hierarchy
            (Fin.last P.counterexample.hierarchy.dividerCount) =
          A) →
    (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyFullTailPrefix P.counterexample
            (HierarchyFullTailLength P.counterexample - (1 : ℕ)) =
          B) →
    (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStoredColorsAt H q =
            HierarchyStoredColorsAt P.counterexample.hierarchy
              (Fin.last P.counterexample.hierarchy.dividerCount) ∧
          ∀ eta ∈ HierarchyStoredColorsAt H q,
            C.good.gamma q eta =
              P.counterexample.good.gamma (Fin.last P.counterexample.hierarchy.dividerCount)
                eta) →
    ∀ beta ∉ HierarchyStoredColorsAt H q,
    (beta ∉ TreeMissingColors phi A → D.theta ∉ HierarchyStoredColorsAt H q) →
    beta ≠ D.theta →
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    TreeVertexOrder T (T.vertex ib) (T.vertex D.penultimateVertexIndex) →
    (∀ (rho : PartialEdgeColoring E k),
        ∀ c ∈ MissingColors G rho (T.vertex (HierarchyFirstMissingPosition rho T c)),
          c ∉ TreeMissingColors rho A →
            A.length < (↑(HierarchyFirstMissingPosition rho T c) : ℕ)) →
    let z : V ⊕ E := Sum.inl (T.vertex D.terminalVertexIndex);
    ∀ (POne : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let rho : PartialEdgeColoring E k := POne.coloring;
    let ettOne :
      ExtendedTashkinovTree G k e0 POne.corresponding.replacementInput T POne.coloring :=
      POne.corresponding.replacementETT;
    let _ : HierarchyBase POne.corresponding.replacementETT POne.coloring :=
      POne.replacementBase;
    let COne' : HierarchyCounterexample POne.replacementBase := POne.counterexample;
    let _ :
      HierarchyMinimumCounterexampleContext G k e0 POne.corresponding.replacementInput T
        POne.coloring POne.corresponding.replacementETT POne.replacementBase
        POne.counterexample :=
      POne.minimumContext;
    ColoredVertexSetElementary G rho (TreeSequenceVertexSet B) →
    TreeMissingColors rho A = TreeMissingColors phi A →
    beta ∈ MissingColors G rho (T.vertex ib) →
    HierarchyFirstMissingPosition rho T beta = ib →
    HierarchyFirstMissingPosition rho T D.theta = D.penultimateVertexIndex →
    (∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → rho (T.edge t) ≠ some beta) →
    beta ∈ TreeMissingColors rho B ∧ D.theta ∈ TreeMissingColors rho B →
    let muTwo : PartialEdgeColoring E k := TwoColorComponentSwap G rho beta D.theta z;
    beta ∉ TreeMissingColors phi A →
    ∃ (corrTwo : CorrespondingExtendedTashkinovTree G k e0 ettOne muTwo T),
    MaximumProperty corrTwo.replacementETT ∧
      ∃ (baseTwo : HierarchyBase corrTwo.replacementETT muTwo) (KTwo :
        TashkinovHierarchy corrTwo.replacementETT baseTwo) (goodTwo : GoodHierarchy KTwo),
        SameGoodHierarchy COne'.good goodTwo := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B hAT sameStar samePrefix sameLast
      beta hbetaStored houtside hbetaTheta ib horder firstAfter z POne rho ettOne baseOne' COne'
      ctxOne hElementaryOne hmissingA hgammaWitnessOne' hfirstGammaOne hfirstThetaOne
      hgammaUnusedOne hmissingPairOne muTwo hm
  have hnotAOne : beta ∉ TreeMissingColors rho A := by rw [hmissingA]; exact hm
  have ha := firstAfter rho beta (by rw [hfirstGammaOne]; exact hgammaWitnessOne') hnotAOne
  rw [hfirstGammaOne] at ha
  exact (StableChangeCaseThree G k e0 POne.corresponding.replacementInput T rho ettOne
    baseOne' COne' ctxOne.proper ctxOne.oneEdgeUncolored ctxOne.lowerRung ctxOne.fewerDividers
    ctxOne.lexicographicMinimality
    (by
      change ColoredVertexSetElementary G rho (TreeSequenceVertexSet
        (HierarchyFullTailPrefix COne' (HierarchyFullTailLength COne' - 1)))
      rw [samePrefix POne]
      exact hElementaryOne)
    ctxOne.largeMissingSet beta D.theta hbetaTheta
    (by
      change beta ∈ TreeMissingColors rho
        (HierarchyFullTailPrefix COne' (HierarchyFullTailLength COne' - 1)) ∧
        D.theta ∈ TreeMissingColors rho
          (HierarchyFullTailPrefix COne' (HierarchyFullTailLength COne' - 1))
      rw [samePrefix POne]
      exact hmissingPairOne)
    z muTwo rfl
    (by
      rw [sameStar POne, hfirstGammaOne]
      intro u hu
      obtain ⟨i, _, rfl⟩ := (@Finset.mem_image _ _ (Classical.decEq V)).mp hu
      exact ⟨Fin.castLE (Nat.succ_le_succ hAT.1) i, ib, hAT.2.1 i, rfl,
        lt_of_le_of_lt (Nat.le_of_lt_succ i.isLt) ha⟩)
    (by rw [hfirstGammaOne, hfirstThetaOne]; exact horder)
    (by rw [← (sameLast POne).1]; exact ⟨hbetaStored, houtside hm⟩)
    (by
      rw [hfirstGammaOne]
      intro hc
      obtain ⟨t, ht, _, he⟩ := (Finset.mem_filter.mp hc).2
      exact hgammaUnusedOne t (by clear * - ht ha; omega) he)).2.2.2.2

private theorem helper_hlastComponent_1263.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
    Incident G (T.vertex D.terminalVertexIndex) (T.edge D.lastEdgeIndex) →
    ∀ (beta : Fin k),
    let z : V ⊕ E := Sum.inl (T.vertex D.terminalVertexIndex);
    ∀ (POne : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let rho : PartialEdgeColoring E k := POne.coloring;
    rho (T.edge D.lastEdgeIndex) = some D.theta →
    Sum.inr (T.edge D.lastEdgeIndex) ∈ TwoColorComponent G rho beta D.theta z := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D hterminalIncident beta z POne rho
      hthetaLastOne
  have hadj : (TwoColorIncidenceGraph G rho beta D.theta).Adj
      (Sum.inr (T.edge D.lastEdgeIndex)) z := by
    exact ⟨hterminalIncident, Or.inr hthetaLastOne⟩
  change (TwoColorIncidenceGraph G rho beta D.theta).connectedComponentMk
    (Sum.inr (T.edge D.lastEdgeIndex)) = _
  exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj

private theorem helper_branch_1360.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    (2 : ℕ) ≤ T.length - A.length →
    ((0 : ℕ) < H.dividerCount →
        A =
          H.stage
            (⟨H.dividerCount,
                by
                have := GoldbergSeymour.TreeSequence.positive T
                omega⟩ :
              Fin (H.dividerCount + (2 : ℕ)))) →
    (H.dividerCount = (0 : ℕ) → A = base.core) →
    TreeSequenceInitialSegment A T →
    HierarchyFirstMissingPosition phi T D.theta = D.penultimateVertexIndex →
    let Bshort : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ));
    Bshort.length + (2 : ℕ) = T.length →
    (∀ (rho : PartialEdgeColoring E k) {X Y : TreeSequence G e0},
        TreeSequenceInitialSegment X Y →
          TreeMissingColors rho X ⊆ TreeMissingColors rho Y) →
    (∀ beta ∈ TreeMissingColors phi Bshort,
        (∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → phi (T.edge t) ≠ some beta) →
          beta ∉ HierarchyStoredColorsAt H q →
            (H.dividerCount = (0 : ℕ) →
                beta ∈ TreeMissingColors phi A →
                  beta ∈
                    TreeMissingColors phi
                      (ett.series.data.tree (Fin.last ett.rounds).castSucc)) →
              (beta ∉ TreeMissingColors phi A → D.theta ∉ HierarchyStoredColorsAt H q) →
                (∀ eta ∈ HierarchyStoredColorsAt H q,
                    beta ∈ C.good.gamma q eta →
                      eta = D.theta ∨ eta ∈ TreeMissingColors phi Bshort) →
                  False) →
    D.theta ∈ HierarchyStoredColorsAt H q →
    False := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A htail hApositive hAzero hAT
      hfirstTheta Bshort hshortLen missingSubset reduction hthetaStored
  obtain ⟨epsOne, epsTwo, heps, hpair⟩ := Finset.card_eq_two.mp
    (C.good.twoColors q D.theta hthetaStored)
  have hgammaPair : epsOne ∈ C.good.gamma q D.theta := by
    rw [hpair]
    exact Finset.mem_insert_self _ _
  have hgammaA : epsOne ∈ TreeMissingColors phi A :=
    (GoodHierarchyReservedDisjoint C.good q).1 D.theta hthetaStored hgammaPair
  have hgammaTheta : epsOne ≠ D.theta := by
    intro he
    exact (Finset.mem_sdiff.mp hthetaStored).2 (he ▸ hgammaA)
  have hgammaUnused : ∀ t : Fin T.length, A.length ≤ t.val →
      phi (T.edge t) ≠ some epsOne := by
    intro t ht he
    by_cases hlast : t = D.lastEdgeIndex
    · rw [hlast, D.thetaOnLastEdge] at he
      exact hgammaTheta (Option.some.inj he).symm
    · have hav := (Finset.mem_sdiff.mp
        (C.good.avoidance q D.theta hthetaStored hgammaPair)).2
      apply hav
      unfold HierarchySegmentColors
      simp only
      have hend : H.stage q.succ = T := by
        convert H.terminalStage using 1
        congr 1
      rw [hend, hfirstTheta]
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, t, ht, ?_, he⟩
      have hp := D.penultimateVertexPosition
      have hl := D.lastEdgePosition
      have hvne : t.val ≠ D.lastEdgeIndex.val := fun he => hlast (Fin.ext he)
      have hb := t.isLt
      omega
  have hAS : TreeSequenceInitialSegment A Bshort :=
    ⟨by omega, hAT.2.1, hAT.2.2⟩
  apply reduction epsOne
  · exact missingSubset (X := A) (Y := Bshort) phi hAS hgammaA
  · exact hgammaUnused
  · intro he
    exact Finset.disjoint_left.mp (GoodHierarchyReservedDisjoint C.good q).2
      (Finset.mem_biUnion.mpr ⟨D.theta, hthetaStored, hgammaPair⟩) he
  · intro hz _
    have hi : q = 0 := Fin.ext (by simpa only [q, Fin.val_last, Fin.val_zero] using hz)
    have hm := (Finset.mem_sdiff.mp (C.good.avoidance q D.theta hthetaStored hgammaPair)).1
    rw [hi] at hm
    exact hm
  · intro hn
    exact False.elim (hn hgammaA)
  · intro eta heta hb
    left
    by_contra he
    exact Finset.disjoint_left.mp
      (C.good.disjointPairs q eta D.theta heta hthetaStored he) hb hgammaPair

private theorem helper_hfinalCard_1448.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
    let Bshort : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ));
    ∀ (hshortLen : Bshort.length + (2 : ℕ) = T.length),
    let previousEdge : Fin T.length :=
      (⟨T.length - (2 : ℕ),
          by
          have := GoldbergSeymour.TreeSequence.positive T
          omega⟩ :
        Fin T.length);
    let finalColors : Finset (Fin k) :=
      ({c : Fin k | phi (T.edge previousEdge) = some c} : Finset (Fin k)) ∪
        ({c : Fin k | phi (T.edge D.lastEdgeIndex) = some c} : Finset (Fin k));
    (∀ (f : E), ({c : Fin k | phi f = some c} : Finset (Fin k)).card ≤ (1 : ℕ)) →
    finalColors.card ≤ (2 : ℕ) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D Bshort hshortLen previousEdge finalColors
      singleColorCard
  have hu := Finset.card_union_le
    (Finset.univ.filter fun c => phi (T.edge previousEdge) = some c)
    (Finset.univ.filter fun c => phi (T.edge D.lastEdgeIndex) = some c)
  have hp := singleColorCard (T.edge previousEdge)
  have hl := singleColorCard (T.edge D.lastEdgeIndex)
  dsimp [finalColors]
  omega

private theorem helper_unused_1456.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let Bshort : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ));
    ∀ (hshortLen : Bshort.length + (2 : ℕ) = T.length),
    let prefixUsed : Finset (Fin k) :=
      ({c : Fin k |
          ∃ (t : Fin T.length),
            A.length ≤ (↑t : ℕ) ∧
              (↑t : ℕ) < A.length + (HierarchyFullTailLength C - (2 : ℕ)) ∧
                phi (T.edge t) = some c} :
        Finset (Fin k));
    let previousEdge : Fin T.length :=
      (⟨T.length - (2 : ℕ),
          by
          have := GoldbergSeymour.TreeSequence.positive T
          omega⟩ :
        Fin T.length);
    let finalColors : Finset (Fin k) :=
      ({c : Fin k | phi (T.edge previousEdge) = some c} : Finset (Fin k)) ∪
        ({c : Fin k | phi (T.edge D.lastEdgeIndex) = some c} : Finset (Fin k));
    ∀ {c : Fin k},
    c ∉ prefixUsed →
    c ∉ finalColors →
    ∀ (t : Fin T.length),
    A.length ≤ (↑t : ℕ) →
    phi (T.edge t) ≠ some c := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A Bshort hshortLen prefixUsed
      previousEdge finalColors c hp hf t ht he
  by_cases hb : t.val < A.length + (HierarchyFullTailLength C - 2)
  · exact hp (Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, ht, hb, he⟩)
  · have hlast := D.lastEdgePosition
    have htlt := t.isLt
    have hpositions : t = previousEdge ∨ t = D.lastEdgeIndex := by
      by_cases hprev : t.val = T.length - 2
      · exact Or.inl (Fin.ext hprev)
      · right
        apply Fin.ext
        have hell : HierarchyFullTailLength C = T.length - A.length := rfl
        rw [hell] at hb
        omega
    apply hf
    rcases hpositions with rfl | rfl
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)

private theorem helper_segmentTrans_1475.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
      {X Y Z : TreeSequence G e0},
    TreeSequenceInitialSegment X Y →
    TreeSequenceInitialSegment Y Z →
    TreeSequenceInitialSegment X Z := by
  classical
  intro V E G e0 X Y Z hXY hYZ
  refine ⟨le_trans hXY.1 hYZ.1, ?_, ?_⟩
  · intro i
    exact (hYZ.2.1 (Fin.castLE (Nat.succ_le_succ hXY.1) i)).trans (hXY.2.1 i)
  · intro i
    exact (hYZ.2.2 (Fin.castLE hXY.1 i)).trans (hXY.2.2 i)

private theorem helper_forward_1483.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (_ : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let Bshort : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ));
    ∀ (_ : Bshort.length + (2 : ℕ) = T.length),
    (∀ {X Y Z : TreeSequence G e0},
        TreeSequenceInitialSegment X Y →
          TreeSequenceInitialSegment Y Z → TreeSequenceInitialSegment X Z) →
    ∀ (a d : ℕ) (hb : a + d ≤ H.dividerCount + (1 : ℕ)),
    TreeSequenceInitialSegment
      (H.stage
        (⟨a, by
            have := GoldbergSeymour.TreeSequence.positive T
            omega⟩ :
          Fin (H.dividerCount + (2 : ℕ))))
      (H.stage
        (⟨a + d, by
            have := GoldbergSeymour.TreeSequence.positive T
            omega⟩ :
          Fin (H.dividerCount + (2 : ℕ)))) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H Bshort hshortLen segmentTrans a d
  induction d with
  | zero => intro hb; exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
  | succ d ih =>
    intro hb
    exact segmentTrans (ih (by omega))
      (by
        convert H.nested ⟨a + d, by omega⟩ using 1 <;>
          congr 1 )

private theorem helper_coreStar_1495.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (_ : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let Bshort : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ));
    ∀ (_ : Bshort.length + (2 : ℕ) = T.length),
    (∀ {X Y Z : TreeSequence G e0},
        TreeSequenceInitialSegment X Y →
          TreeSequenceInitialSegment Y Z → TreeSequenceInitialSegment X Z) →
    (∀ (a d : ℕ) (hb : a + d ≤ H.dividerCount + (1 : ℕ)),
        TreeSequenceInitialSegment
          (H.stage
            (⟨a, by
                have := GoldbergSeymour.TreeSequence.positive T
                omega⟩ :
              Fin (H.dividerCount + (2 : ℕ))))
          (H.stage
            (⟨a + d, by
                have := GoldbergSeymour.TreeSequence.positive T
                omega⟩ :
              Fin (H.dividerCount + (2 : ℕ))))) →
    ∀ (j : Fin (H.dividerCount + (1 : ℕ))),
    TreeSequenceInitialSegment base.core (HierarchyStarredStage H j) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H Bshort hshortLen segmentTrans forward j
  refine Fin.cases ?_ (fun i => ?_) j
  · exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
  · exact segmentTrans H.coreInsideFirst
      (by
        change TreeSequenceInitialSegment (H.stage ⟨1, by omega⟩) (H.stage i.succ.castSucc)
        convert forward 1 i.val (by omega) using 1;
          congr 1; apply Fin.ext; simp; omega)

private theorem helper_starA_1505.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (_ : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    ((0 : ℕ) < H.dividerCount →
        A =
          H.stage
            (⟨H.dividerCount,
                by
                have := GoldbergSeymour.TreeSequence.positive T
                omega⟩ :
              Fin (H.dividerCount + (2 : ℕ)))) →
    let Bshort : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ));
    ∀ (_ : Bshort.length + (2 : ℕ) = T.length),
    (∀ (a d : ℕ) (hb : a + d ≤ H.dividerCount + (1 : ℕ)),
        TreeSequenceInitialSegment
          (H.stage
            (⟨a, by
                have := GoldbergSeymour.TreeSequence.positive T
                omega⟩ :
              Fin (H.dividerCount + (2 : ℕ))))
          (H.stage
            (⟨a + d, by
                have := GoldbergSeymour.TreeSequence.positive T
                omega⟩ :
              Fin (H.dividerCount + (2 : ℕ))))) →
    (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
        TreeSequenceInitialSegment base.core (HierarchyStarredStage H j)) →
    ∀ (j : Fin (H.dividerCount + (1 : ℕ))),
    TreeSequenceInitialSegment (HierarchyStarredStage H j) A := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A hApositive Bshort hshortLen forward
      coreStar j
  obtain rfl | ⟨i, rfl⟩ := Fin.eq_zero_or_eq_succ j
  · exact coreStar q
  · have hpos : 0 < H.dividerCount := by have hi := i.isLt; omega
    rw [hApositive hpos]
    convert forward (i.val + 1) (H.dividerCount - (i.val + 1)) (by omega) using 1
    · rfl
    · congr 1
      apply Fin.ext
      change H.dividerCount = i.val + 1 + (H.dividerCount - (i.val + 1))
      have hi := i.isLt
      omega

private theorem helper_hTnCore_1521.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    TreeSequenceInitialSegment Tn base.core := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base n Tn
  by_cases hpe : ett.series.data.kind n = some TashkinovExtensionKind.PE
  · obtain ⟨_, _, ⟨u⟩⟩ := base.parallel hpe
    exact u.leftSegment
  · rw [base.nonparallel hpe]
    exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩

private theorem helper_gammaExtra_1527.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let B : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    TreeSequenceInitialSegment A B →
    ColoredVertexSetElementary G phi (TreeSequenceVertexSet B) →
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let extra : Finset (Fin k) :=
      (TreeSequenceVertexSet base.core \ TreeSequenceVertexSet Tn).biUnion fun (v : V) ↦
        MissingColors G phi v;
    (∀ {X Y Z : TreeSequence G e0},
        TreeSequenceInitialSegment X Y →
          TreeSequenceInitialSegment Y Z → TreeSequenceInitialSegment X Z) →
    (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
        TreeSequenceInitialSegment base.core (HierarchyStarredStage H j)) →
    (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
        TreeSequenceInitialSegment (HierarchyStarredStage H j) A) →
    TreeSequenceInitialSegment base.core B →
    TreeSequenceInitialSegment Tn base.core →
    ∀ (j : Fin (H.dividerCount + (1 : ℕ))),
    ∀ eta ∈ HierarchyStoredColorsAt H j,
    ∀ c ∈ C.good.gamma j eta,
    c ∉ extra := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q A B hAB hElementary n Tn extra segmentTrans
      coreStar starA hcoreB hTnCore
  as_aux_lemma =>
    intro j
    induction j using Fin.induction with
    | zero =>
      intro eta heta c hc he
      have hm := (Finset.mem_sdiff.mp (C.good.avoidance 0 eta heta hc)).1
      change c ∈ TreeMissingColors phi Tn at hm
      rcases Finset.mem_biUnion.mp hm with ⟨u, hu, huc⟩
      rcases Finset.mem_biUnion.mp he with ⟨v, hv, hvc⟩
      have huB := TreeSequenceInitialSegmentVertexSetSubset
        (segmentTrans hTnCore hcoreB) hu
      have hvB := TreeSequenceInitialSegmentVertexSetSubset hcoreB
        (Finset.mem_sdiff.mp hv).1
      have huv : u ≠ v := by
        intro h
        exact (Finset.mem_sdiff.mp hv).2 (h ▸ hu)
      exact Finset.disjoint_left.mp (hElementary huB hvB huv) huc hvc
    | succ i ih =>
      intro eta heta c hc he
      obtain ⟨refresh, hr, _⟩ := C.good.uniqueRefresh i
      by_cases hsame : eta = refresh
      · subst eta
        have hm := hr.2.1 hc
        rcases Finset.mem_biUnion.mp hm with ⟨u, hu, huc⟩
        rcases Finset.mem_biUnion.mp he with ⟨v, hv, hvc⟩
        have huB := TreeSequenceInitialSegmentVertexSetSubset
          (segmentTrans (starA i.succ) hAB) (Finset.mem_sdiff.mp hu).1
        have hvB := TreeSequenceInitialSegmentVertexSetSubset hcoreB
          (Finset.mem_sdiff.mp hv).1
        have huv : u ≠ v := by
          intro h
          apply (Finset.mem_sdiff.mp hu).2
          rw [h]
          exact TreeSequenceInitialSegmentVertexSetSubset (coreStar i.castSucc)
            (Finset.mem_sdiff.mp hv).1
        exact Finset.disjoint_left.mp (hElementary huB hvB huv) huc hvc
      · rw [hr.2.2 eta heta hsame] at hc
        exact ih eta (HierarchyStoredColorsAntitone H i heta) c hc he

private theorem helper_hAshort_1568.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (_ : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    (2 : ℕ) ≤ T.length - A.length →
    ((0 : ℕ) < H.dividerCount →
        A =
          H.stage
            (⟨H.dividerCount,
                by
                have := GoldbergSeymour.TreeSequence.positive T
                omega⟩ :
              Fin (H.dividerCount + (2 : ℕ)))) →
    (H.dividerCount = (0 : ℕ) → A = base.core) →
    TreeSequenceInitialSegment A T →
    let Bshort : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ));
    Bshort.length + (2 : ℕ) = T.length →
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let stored : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let Gamma : Finset (Fin k) := stored.biUnion (C.good.gamma q);
    let extra : Finset (Fin k) :=
      (TreeSequenceVertexSet base.core \ TreeSequenceVertexSet Tn).biUnion fun (v : V) ↦
        MissingColors G phi v;
    let prefixUsed : Finset (Fin k) :=
      ({c : Fin k |
          ∃ (t : Fin T.length),
            A.length ≤ (↑t : ℕ) ∧
              (↑t : ℕ) < A.length + (HierarchyFullTailLength C - (2 : ℕ)) ∧
                phi (T.edge t) = some c} :
        Finset (Fin k));
    let available : Finset (Fin k) := (TreeMissingColors phi Bshort \ extra) \ prefixUsed;
    (2 : ℕ) * ett.rounds + (11 : ℕ) ≤ available.card ∧
        ((available \ (Gamma ∪ stored)).card ≤ (4 : ℕ) →
          ∃ (eta : Fin (7 : ℕ) → Fin k),
            Function.Injective eta ∧
              ∀ (h : Fin (7 : ℕ)),
                eta h ∈ stored ∧
                  eta h ∈ TreeMissingColors phi Bshort ∧
                    Disjoint (C.good.gamma q (eta h) ∪ ({eta h} : Finset (Fin k)))
                      prefixUsed) →
    TreeSequenceInitialSegment A Bshort := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A htail hApositive hAzero hAT Bshort
      hshortLen n Tn stored Gamma extra prefixUsed available hnine
  refine ⟨by omega, ?_, ?_⟩
  · intro i
    exact hAT.2.1 i
  · intro i
    exact hAT.2.2 i

private theorem helper_hchoice_1574.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let Bshort : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ));
    ∀ (hshortLen : Bshort.length + (2 : ℕ) = T.length),
    (∀ (rho : PartialEdgeColoring E k) {X Y : TreeSequence G e0},
        TreeSequenceInitialSegment X Y →
          TreeMissingColors rho X ⊆ TreeMissingColors rho Y) →
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let stored : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let Gamma : Finset (Fin k) := stored.biUnion (C.good.gamma q);
    let extra : Finset (Fin k) :=
      (TreeSequenceVertexSet base.core \ TreeSequenceVertexSet Tn).biUnion fun (v : V) ↦
        MissingColors G phi v;
    let prefixUsed : Finset (Fin k) :=
      ({c : Fin k |
          ∃ (t : Fin T.length),
            A.length ≤ (↑t : ℕ) ∧
              (↑t : ℕ) < A.length + (HierarchyFullTailLength C - (2 : ℕ)) ∧
                phi (T.edge t) = some c} :
        Finset (Fin k));
    let available : Finset (Fin k) := (TreeMissingColors phi Bshort \ extra) \ prefixUsed;
    (2 : ℕ) * ett.rounds + (11 : ℕ) ≤ available.card ∧
        ((available \ (Gamma ∪ stored)).card ≤ (4 : ℕ) →
          ∃ (eta : Fin (7 : ℕ) → Fin k),
            Function.Injective eta ∧
              ∀ (h : Fin (7 : ℕ)),
                eta h ∈ stored ∧
                  eta h ∈ TreeMissingColors phi Bshort ∧
                    Disjoint (C.good.gamma q (eta h) ∪ ({eta h} : Finset (Fin k)))
                      prefixUsed) →
    let previousEdge : Fin T.length :=
      (⟨T.length - (2 : ℕ),
          by
          have := GoldbergSeymour.TreeSequence.positive T
          omega⟩ :
        Fin T.length);
    let finalColors : Finset (Fin k) :=
      ({c : Fin k | phi (T.edge previousEdge) = some c} : Finset (Fin k)) ∪
        ({c : Fin k | phi (T.edge D.lastEdgeIndex) = some c} : Finset (Fin k));
    finalColors.card ≤ (2 : ℕ) →
    (∀ {c : Fin k},
        c ∉ prefixUsed →
          c ∉ finalColors →
            ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → phi (T.edge t) ≠ some c) →
    (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
        ∀ eta ∈ HierarchyStoredColorsAt H j, ∀ c ∈ C.good.gamma j eta, c ∉ extra) →
    TreeSequenceInitialSegment A Bshort →
    ∃ beta ∈ TreeMissingColors phi Bshort,
    beta ∉ extra ∧
      (∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → phi (T.edge t) ≠ some beta) ∧
        beta ∉ stored ∧
          (beta ∉ Gamma ∨
            ∃ eta ∈ stored, eta ∈ TreeMissingColors phi Bshort ∧ beta ∈ C.good.gamma q eta) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A Bshort hshortLen missingSubset n Tn
      stored Gamma extra prefixUsed available hnine previousEdge finalColors hfinalCard unused
      gammaExtra hAshort
  clear_value finalColors
  clear * - G phi T A Bshort C H q stored Gamma extra available prefixUsed
    finalColors hnine hfinalCard unused gammaExtra hAshort missingSubset
  by_cases hsmall : (available \ (Gamma ∪ stored)).card ≤ 4
  · obtain ⟨eta, hinj, heta⟩ := hnine.2 hsmall
    let Q := fun h : Fin 7 => C.good.gamma q (eta h) ∪ {eta h}
    have hGD : Disjoint Gamma stored := (GoodHierarchyReservedDisjoint C.good q).2
    have hQdisjoint : ∀ a b : Fin 7, a ≠ b → Disjoint (Q a) (Q b) := by
      intro a b hab
      have hne : eta a ≠ eta b := fun he => hab (hinj he)
      have hp := C.good.disjointPairs q (eta a) (eta b)
        (heta a).1 (heta b).1 hne
      rw [Finset.disjoint_left]
      intro c hca hcb
      rcases Finset.mem_union.mp hca with hca | hca <;>
        rcases Finset.mem_union.mp hcb with hcb | hcb
      · exact Finset.disjoint_left.mp hp hca hcb
      · apply Finset.disjoint_left.mp hGD
          (Finset.mem_biUnion.mpr ⟨eta a, (heta a).1, hca⟩)
        simpa only [Finset.mem_singleton.mp hcb] using (heta b).1
      · apply Finset.disjoint_left.mp hGD
          (Finset.mem_biUnion.mpr ⟨eta b, (heta b).1, hcb⟩)
        simpa only [Finset.mem_singleton.mp hca] using (heta a).1
      · exact hne ((Finset.mem_singleton.mp hca).symm.trans
          (Finset.mem_singleton.mp hcb))
    let bad := (Finset.univ : Finset (Fin 7)).filter fun h =>
      ∃ c : Fin k, c ∈ Q h ∧ c ∈ finalColors
    have badWitness (h : bad) : ∃ c : Fin k, c ∈ Q h.val ∧ c ∈ finalColors :=
      (Finset.mem_filter.mp h.property).2
    let f : bad → finalColors := fun h =>
      ⟨Classical.choose (badWitness h), (Classical.choose_spec (badWitness h)).2⟩
    have hf (h : bad) : (f h).val ∈ Q h.val :=
      (Classical.choose_spec (badWitness h)).1
    have hfinj : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      by_contra hne
      have hfb := hf b
      rw [← congrArg Subtype.val hab] at hfb
      exact Finset.disjoint_left.mp (hQdisjoint a.val b.val hne) (hf a) hfb
    have hbadCard : bad.card ≤ 2 :=
      (Finset.card_le_card_of_injective hfinj).trans hfinalCard
    have hnot : ¬ (Finset.univ : Finset (Fin 7)) ⊆ bad := by
      intro hs
      have hc := Finset.card_le_card hs
      simp only [Finset.card_univ, Fintype.card_fin] at hc
      clear * - hc hbadCard
      omega
    obtain ⟨h, _, hh⟩ := Finset.not_subset.mp hnot
    have hQFinal : Disjoint (Q h) finalColors := by
      rw [Finset.disjoint_left]
      intro c hc hf
      exact hh (Finset.mem_filter.mpr ⟨Finset.mem_univ _, c, hc, hf⟩)
    obtain ⟨b1, b2, _, hp⟩ := Finset.card_eq_two.mp
      (C.good.twoColors q (eta h) (heta h).1)
    have hb : b1 ∈ C.good.gamma q (eta h) := by rw [hp]; simp
    have hbGamma : b1 ∈ Gamma := Finset.mem_biUnion.mpr ⟨eta h, (heta h).1, hb⟩
    have hbQ : b1 ∈ Q h := Finset.mem_union_left _ hb
    have hbPrefix : b1 ∉ prefixUsed := fun hu =>
      Finset.disjoint_left.mp (heta h).2.2 hbQ hu
    have hbFinal : b1 ∉ finalColors := fun hu => Finset.disjoint_left.mp hQFinal hbQ hu
    have hbA := (GoodHierarchyReservedDisjoint C.good q).1 (eta h) (heta h).1 hb
    have hbShort : b1 ∈ TreeMissingColors phi Bshort := missingSubset (X := A) (Y := Bshort) phi
        hAshort hbA
    exact ⟨b1, hbShort, gammaExtra q (eta h) (heta h).1 b1 hb,
      unused hbPrefix hbFinal, fun hs => Finset.disjoint_left.mp hGD hbGamma hs,
      Or.inr ⟨eta h, (heta h).1, (heta h).2.1, hb⟩⟩
  · have hnot : ¬ available \ (Gamma ∪ stored) ⊆ finalColors := by
      intro hs
      have hc := Finset.card_le_card hs
      clear * - hc hsmall hfinalCard
      omega
    obtain ⟨beta, hb, hf⟩ := Finset.not_subset.mp hnot
    rcases Finset.mem_sdiff.mp hb with ⟨hav, houtside⟩
    rcases Finset.mem_sdiff.mp hav with ⟨hmissExtra, hprefix⟩
    rcases Finset.mem_sdiff.mp hmissExtra with ⟨hmiss, hextra⟩
    exact ⟨beta, hmiss, hextra, unused hprefix hf,
      fun hs => houtside (Finset.mem_union_right _ hs),
      Or.inl (fun hg => houtside (Finset.mem_union_left _ hg))⟩

private theorem helper_hseventeenPositive_1664.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (_ : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    ((0 : ℕ) < H.dividerCount →
        A =
          H.stage
            (⟨H.dividerCount,
                by
                have := GoldbergSeymour.TreeSequence.positive T
                omega⟩ :
              Fin (H.dividerCount + (2 : ℕ)))) →
    let Bshort : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ));
    ∀ (_ : Bshort.length + (2 : ℕ) = T.length),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    let stored : Finset (Fin k) := HierarchyStoredColorsAt H q;
    ∀ beta ∉ stored,
    (0 : ℕ) < H.dividerCount →
    beta ∈
        TreeMissingColors phi
          (H.stage
            (⟨H.dividerCount,
                by
                have := GoldbergSeymour.TreeSequence.positive T
                omega⟩ :
              Fin (H.dividerCount + (2 : ℕ)))) ∨
      beta ∉ Dn := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A hApositive Bshort hshortLen n Dn
      stored beta hbetaStored hq
  by_cases hd : beta ∈ Dn
  · left
    rw [← hApositive hq]
    by_contra hm
    exact hbetaStored (Finset.mem_sdiff.mpr ⟨hd, hm⟩)
  · exact Or.inr hd

private theorem helper_hseventeenZero_1672.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    let stored : Finset (Fin k) := HierarchyStoredColorsAt H q;
    ∀ beta ∉ stored,
    (H.dividerCount = (0 : ℕ) →
        beta ∈ TreeMissingColors phi A → beta ∈ TreeMissingColors phi Tn) →
    H.dividerCount = (0 : ℕ) →
    beta ∈ TreeMissingColors phi Tn ∨ beta ∉ Dn := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q A n Tn Dn stored beta hbetaStored hzeroBeta hq
  by_cases hd : beta ∈ Dn
  · left
    have hm : beta ∈ TreeMissingColors phi A := by
      by_contra hm
      exact hbetaStored (Finset.mem_sdiff.mpr ⟨hd, hm⟩)
    exact hzeroBeta hq hm
  · exact Or.inr hd

private theorem helper_branch_1685.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let Bshort : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ));
    let stored : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let Gamma : Finset (Fin k) := stored.biUnion (C.good.gamma q);
    ∀ (beta : Fin k),
    (beta ∉ Gamma ∨
        ∃ eta ∈ stored, eta ∈ TreeMissingColors phi Bshort ∧ beta ∈ C.good.gamma q eta) →
    ∀ eta ∈ HierarchyStoredColorsAt H q,
    beta ∈ C.good.gamma q eta →
    eta = D.theta ∨ eta ∈ TreeMissingColors phi Bshort := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q Bshort stored Gamma beta hbetaGamma
      eta heta hb
  rcases hbetaGamma with hn | ⟨eta', heta', hm, hb'⟩
  · exact False.elim (hn (Finset.mem_biUnion.mpr ⟨eta, heta, hb⟩))
  · right
    have he : eta = eta' := by
      by_contra hne
      exact Finset.disjoint_left.mp (C.good.disjointPairs q eta eta' heta heta' hne) hb hb'
    exact he ▸ hm

private theorem helper_branch_3242.{u_1, u_2} :
    helperBranch3242Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B htail hBlen hBT hAzero hAT hAB
      hBterminal hyB hElementary hnotA sameStar samePrefix sameTn sameLast commonPrefix
      hcoreLength predecessorIncident seedStable weakEdges beta hbetaTheta ib hibB z muOne
      hfixedOne POne hPOne rho ettOne baseOne' COne' ctxOne HOne qOne hElementaryOne hthetaPenOne
      hgammaWitnessOne' hfirstGammaOne hgammaUnusedOne hcaseOne hmissingPairOne hdisjointTwo
      muTwo hpathTwo hmissingTwo hstoredTwo hsuffix hgammaCutoff hm
  have hstableTwo := StableChangeCasesOneTwo G k e0 POne.corresponding.replacementInput T rho
    ettOne baseOne' COne' ctxOne.proper ctxOne.oneEdgeUncolored ctxOne.lowerRung
    ctxOne.fewerDividers ctxOne.lexicographicMinimality
    (by
      change ColoredVertexSetElementary G rho (TreeSequenceVertexSet
        (HierarchyFullTailPrefix COne' (HierarchyFullTailLength COne' - 1)))
      rw [samePrefix POne]
      exact hElementaryOne)
    ctxOne.largeMissingSet beta D.theta hbetaTheta
    (by
      change beta ∈ TreeMissingColors rho
        (HierarchyFullTailPrefix COne' (HierarchyFullTailLength COne' - 1)) ∧
        D.theta ∈ TreeMissingColors rho
          (HierarchyFullTailPrefix COne' (HierarchyFullTailLength COne' - 1))
      rw [samePrefix POne]
      exact hmissingPairOne)
    z hpathTwo muTwo rfl
    (by dsimp only; rcases hcaseOne hm with hpos | ⟨hz, hb⟩
        · exact Or.inl hpos
        · exact Or.inr ⟨hz, Or.inl hb⟩)
    (by dsimp only; rw [hfirstGammaOne]; exact hdisjointTwo)
  have hthetaExclusion := HierarchyTailMissingColorExclusion G k e0 input T phi
    ett base H hElementary (HierarchyFullTailLength C - 1)
    (by change 1 ≤ T.length - A.length - 1; clear * - htail; omega)
    (by change T.length - A.length - 1 < T.length - A.length; clear * - htail; omega)
    D.theta (by
      change D.theta ∈ MissingColors G phi (B.vertex (Fin.last B.length))
      rw [hBterminal]
      exact D.thetaMissingPenultimate)
  have hfixedTailTwo : ∀ t : Fin T.length, A.length ≤ t.val → t.val < B.length →
      muTwo (T.edge t) = rho (T.edge t) := by
    intro t ht hb
    have hng := hgammaUnusedOne t ht
    by_cases htheta : rho (T.edge t) = some D.theta
    · let tB : Fin B.length := ⟨t.val, hb⟩
      have hcast : Fin.castLE hBT.1 tB = t := Fin.ext rfl
      have heOld : phi (T.edge t) = some D.theta := by
        rw [show rho = muOne from hPOne, hfixedOne t ht] at htheta
        exact htheta
      have heB : phi (B.edge tB) = some D.theta := by
        rw [← hBT.2.2 tB, hcast]
        exact heOld
      obtain ⟨hz, hcore, hpos, f, _, _, _, _, _, hs⟩ :=
        hthetaExclusion tB ht (by
          change tB.val < A.length + (T.length - A.length - 1)
          have hv := tB.isLt
          clear * - hv htail hBlen
          change tB.val < B.length at hv
          omega) heB
      have hzOne : HOne.dividerCount = 0 := POne.sameGood.1.2.1.symm.trans hz
      have htn : ettOne.series.data.tree (Fin.last ettOne.rounds).castSucc = A :=
        (sameTn POne).trans ((hAzero hz).trans hcore).symm
      have hinc : TreeIncidentEdge
          (ettOne.series.data.tree (Fin.last ettOne.rounds).castSucc) (T.edge t) := by
        rw [htn]
        exact predecessorIncident A hAT t hpos
      have hsOld : D.theta ∈ HierarchyStoredColorsAt H q :=
        Finset.mem_sdiff.mpr ⟨hs, hnotA (c := D.theta) D.thetaMissingPenultimate⟩
      have hsOne : D.theta ∈ HierarchyStoredColorsAt HOne qOne :=
        (sameLast POne).1 ▸ hsOld
      exact (seedStable rho muTwo ettOne baseOne' HOne hstableTwo.1 hzOne).1 _ hinc
        ⟨D.theta, Finset.mem_union_right _ (Finset.mem_sdiff.mp hsOne).1, htheta⟩
    · simp only [muTwo, TwoColorComponentSwap, hng, htheta, ite_false, ite_self]
  have hfixedCore := weakEdges rho muTwo ettOne baseOne' HOne hstableTwo.1
    ctxOne.oneEdgeUncolored hstableTwo.2.1.2.1
  change ∀ t : Fin (HierarchyStarredStage POne.counterexample.hierarchy
    (Fin.last POne.counterexample.hierarchy.dividerCount)).length,
    muTwo ((HierarchyStarredStage POne.counterexample.hierarchy
      (Fin.last POne.counterexample.hierarchy.dividerCount)).edge t) =
    rho ((HierarchyStarredStage POne.counterexample.hierarchy
      (Fin.last POne.counterexample.hierarchy.dividerCount)).edge t) at hfixedCore
  rw [sameStar POne] at hfixedCore
  have hfixedPrefix : ∀ t : Fin T.length, t.val < B.length →
      muTwo (T.edge t) = rho (T.edge t) := by
    exact @helper_hfixedPrefix_1144 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@hAT)
        (@beta) (@POne) (@hfixedTailTwo) (@hfixedCore)
  have transportRoute (S : TreeSequence G e0)
      (hs : TashkinovAugmentationSequence rho S B) :
      TashkinovAugmentationSequence muTwo S B := by
    exact @helper_transportRoute_1153 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@htail) (@hBT) (@commonPrefix) (@beta) (@POne) (@hmissingTwo) (@hm) (@hfixedPrefix) (@S)
        (@hs)
  have hrouteTwo :
      (ettOne.series.data.kind (Fin.last ettOne.rounds) = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence muTwo
          (ettOne.series.data.tree (Fin.last ettOne.rounds).castSucc) B) ∨
      ((ettOne.series.data.kind (Fin.last ettOne.rounds) = some TashkinovExtensionKind.SE ∨
          ettOne.series.data.kind (Fin.last ettOne.rounds) = some TashkinovExtensionKind.RE) ∧
        ∃ f seed, ettOne.series.data.connectingEdges (Fin.last ettOne.rounds) = {f} ∧
          TreeSequenceAdjoinEdge (ettOne.series.data.tree (Fin.last ettOne.rounds).castSucc) f
              seed ∧
          TashkinovAugmentationSequence muTwo seed B) := by
    exact @helper_hrouteTwo_1176 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@htail) (@hBlen) (@hBT) (@commonPrefix) (@hcoreLength) (@beta) (@POne) (@transportRoute)
  exact (StableChangeCasesOneTwoSplitTail G k e0 POne.corresponding.replacementInput T rho
    ettOne baseOne' COne' ctxOne beta D.theta hbetaTheta
    (by rw [samePrefix POne]; exact hmissingPairOne)
    z hpathTwo muTwo rfl
    (by dsimp only; rcases hcaseOne hm with hpos | ⟨hz, hb⟩
        · exact Or.inl hpos
        · exact Or.inr ⟨hz, Or.inl hb⟩)
    (by dsimp only; rw [hfirstGammaOne]; exact hdisjointTwo)
    B (by dsimp only; rw [sameStar POne]; exact hAB)
    (by dsimp only; rw [sameStar POne]; clear * - htail hBlen; omega)
    (by rw [samePrefix POne]; exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩)
    (by dsimp only; intro t _ ht; exact hfixedPrefix t ht)
    hrouteTwo hsuffix
    ⟨Finset.mem_biUnion.mpr ⟨_, hibB, (hmissingTwo _ hibB).symm ▸ hgammaWitnessOne'⟩,
      Finset.mem_biUnion.mpr ⟨_, hyB, (hmissingTwo _ hyB).symm ▸ hthetaPenOne⟩⟩
    (by rw [samePrefix POne]; exact hmissingTwo) hstoredTwo hgammaCutoff).2.2

private theorem helper_branch_3441.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let B : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    (2 : ℕ) ≤ T.length - A.length →
    ((0 : ℕ) < H.dividerCount →
        A =
          H.stage
            (⟨H.dividerCount,
                by
                have := GoldbergSeymour.TreeSequence.positive T
                omega⟩ :
              Fin (H.dividerCount + (2 : ℕ)))) →
    (H.dividerCount = (0 : ℕ) → A = base.core) →
    TreeSequenceInitialSegment A T →
    TreeSequenceInitialSegment A B →
    ColoredVertexSetElementary G phi (TreeSequenceVertexSet B) →
    (∀ {c : Fin k},
        c ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex) →
          c ∉ TreeMissingColors phi A) →
    let Bshort : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ));
    Bshort.length + (2 : ℕ) = T.length →
    (∀ (rho : PartialEdgeColoring E k) {X Y : TreeSequence G e0},
        TreeSequenceInitialSegment X Y →
          TreeMissingColors rho X ⊆ TreeMissingColors rho Y) →
    (∀ (rho : PartialEdgeColoring E k) (X Y : TreeSequence G e0),
        ∀
          c ∉
            (TreeSequenceVertexSet X \ TreeSequenceVertexSet Y).biUnion fun (v : V) ↦
              MissingColors G rho v,
          c ∈ TreeMissingColors rho X → c ∈ TreeMissingColors rho Y) →
    (∀ beta ∈ TreeMissingColors phi Bshort,
        (∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → phi (T.edge t) ≠ some beta) →
          beta ∉ HierarchyStoredColorsAt H q →
            (H.dividerCount = (0 : ℕ) →
                beta ∈ TreeMissingColors phi A →
                  beta ∈
                    TreeMissingColors phi
                      (ett.series.data.tree (Fin.last ett.rounds).castSucc)) →
              (beta ∉ TreeMissingColors phi A → D.theta ∉ HierarchyStoredColorsAt H q) →
                (∀ eta ∈ HierarchyStoredColorsAt H q,
                    beta ∈ C.good.gamma q eta →
                      eta = D.theta ∨ eta ∈ TreeMissingColors phi Bshort) →
                  False) →
    D.theta ∉ HierarchyStoredColorsAt H q →
    False := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B htail hApositive hAzero hAT hAB
      hElementary hnotA Bshort hshortLen missingSubset missingWithoutExtra reduction hthetaStored
  have hthetaNotRaw :
      D.theta ∉ TashkinovStoredColors ett.series.data (Fin.last ett.rounds) := by
    intro hc
    exact hthetaStored
      (Finset.mem_sdiff.mpr ⟨hc, hnotA (c := D.theta) D.thetaMissingPenultimate⟩)
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn := ett.series.data.tree n.castSucc
  let Dn := TashkinovStoredColors ett.series.data n
  let stored := HierarchyStoredColorsAt H q
  let Gamma := stored.biUnion (C.good.gamma q)
  let extra := (TreeSequenceVertexSet base.core \ TreeSequenceVertexSet Tn).biUnion
    (fun v => MissingColors G phi v)
  let prefixUsed : Finset (Fin k) := Finset.univ.filter fun c =>
    ∃ t : Fin T.length, A.length ≤ t.val ∧
      t.val < A.length + (HierarchyFullTailLength C - 2) ∧
        phi (T.edge t) = some c
  let available := (TreeMissingColors phi Bshort \ extra) \ prefixUsed
  have hnine := NineN G k e0 input T phi ett C.positive base H C.good
    hElementary ctx.largeMissingSet (HierarchyFullTailLength C - 2)
    (by change T.length - A.length - 2 < T.length - A.length; omega)
  change (2 * ett.rounds + 11 ≤ available.card) ∧
    ((available \ (Gamma ∪ stored)).card ≤ 4 →
      ∃ eta : Fin 7 → Fin k, Function.Injective eta ∧
        ∀ h : Fin 7, eta h ∈ stored ∧ eta h ∈ TreeMissingColors phi Bshort ∧
          Disjoint (C.good.gamma q (eta h) ∪ {eta h}) prefixUsed) at hnine
  have havailable : 2 * ett.rounds + 11 ≤ available.card := hnine.1
  let previousEdge : Fin T.length := ⟨T.length - 2, by omega⟩
  let finalColors : Finset (Fin k) :=
    (Finset.univ.filter fun c => phi (T.edge previousEdge) = some c) ∪
      (Finset.univ.filter fun c => phi (T.edge D.lastEdgeIndex) = some c)
  have singleColorCard (f : E) :
      (Finset.univ.filter fun c => phi f = some c).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    exact Option.some.inj ((Finset.mem_filter.mp ha).2.symm.trans
      (Finset.mem_filter.mp hb).2)
  have hfinalCard : finalColors.card ≤ 2 := by
    exact @helper_hfinalCard_1448 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@hshortLen) (@singleColorCard)
  have unused {c : Fin k} (hp : c ∉ prefixUsed) (hf : c ∉ finalColors) :
      ∀ t : Fin T.length, A.length ≤ t.val → phi (T.edge t) ≠ some c := by
    exact @helper_unused_1456 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@hshortLen) (@c)
        (@hp) (@hf)
  have segmentTrans {X Y Z : TreeSequence G e0}
      (hXY : TreeSequenceInitialSegment X Y) (hYZ : TreeSequenceInitialSegment Y Z) :
      TreeSequenceInitialSegment X Z := by
    exact @helper_segmentTrans_1475 (@V) (@E) (@G) (@e0) (@X) (@Y) (@Z) (@hXY) (@hYZ)
  have forward : ∀ a d : ℕ, ∀ hb : a + d ≤ H.dividerCount + 1,
      TreeSequenceInitialSegment (H.stage ⟨a, by omega⟩)
        (H.stage ⟨a + d, by omega⟩) := by
    exact @helper_forward_1483 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@hshortLen)
        (@segmentTrans)
  have coreStar : ∀ j : Fin (H.dividerCount + 1),
      TreeSequenceInitialSegment base.core (HierarchyStarredStage H j) := by
    exact @helper_coreStar_1495 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@hshortLen)
        (@segmentTrans) (@forward)
  have starA : ∀ j : Fin (H.dividerCount + 1),
      TreeSequenceInitialSegment (HierarchyStarredStage H j) A := by
    exact @helper_starA_1505 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@hApositive)
        (@hshortLen) (@forward) (@coreStar)
  have hcoreB : TreeSequenceInitialSegment base.core B :=
    segmentTrans (coreStar q) hAB
  have hTnCore : TreeSequenceInitialSegment Tn base.core := by
    exact @helper_hTnCore_1521 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base)
  have gammaExtra : ∀ j : Fin (H.dividerCount + 1),
      ∀ eta ∈ HierarchyStoredColorsAt H j,
        ∀ c ∈ C.good.gamma j eta, c ∉ extra := by
    exact @helper_gammaExtra_1527 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hAB)
        (@hElementary) (@segmentTrans) (@coreStar) (@starA) (@hcoreB) (@hTnCore)
  have hAshort : TreeSequenceInitialSegment A Bshort := by
    exact @helper_hAshort_1568 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@htail)
        (@hApositive) (@hAzero) (@hAT) (@hshortLen) (@hnine)
  have hchoice : ∃ beta : Fin k,
      beta ∈ TreeMissingColors phi Bshort ∧ beta ∉ extra ∧
      (∀ t : Fin T.length, A.length ≤ t.val → phi (T.edge t) ≠ some beta) ∧
      beta ∉ stored ∧
      (beta ∉ Gamma ∨ ∃ eta : Fin k,
        eta ∈ stored ∧ eta ∈ TreeMissingColors phi Bshort ∧
          beta ∈ C.good.gamma q eta) := by
    exact @helper_hchoice_1574 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@hshortLen)
        (@missingSubset) (@hnine) (@hfinalCard) (@unused) (@gammaExtra) (@hAshort)
  obtain ⟨beta, hbetaMissing, hbetaExtra, hbetaUnused, hbetaStored, hbetaGamma⟩ := hchoice
  have hzeroBeta (hq : H.dividerCount = 0) (hm : beta ∈ TreeMissingColors phi A) :
      beta ∈ TreeMissingColors phi Tn := by
    rw [hAzero hq] at hm
    exact missingWithoutExtra phi base.core Tn beta hbetaExtra hm
  have hseventeenPositive (hq : 0 < H.dividerCount) :
      beta ∈ TreeMissingColors phi (H.stage ⟨H.dividerCount, by omega⟩) ∨ beta ∉ Dn := by
    exact @helper_hseventeenPositive_1664 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@hApositive) (@hshortLen) (@beta) (@hbetaStored) (@hq)
  have hseventeenZero (hq : H.dividerCount = 0) :
      beta ∈ TreeMissingColors phi Tn ∨ beta ∉ Dn := by
    exact @helper_hseventeenZero_1672 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@beta)
        (@hbetaStored) (@hzeroBeta) (@hq)
  apply reduction beta hbetaMissing hbetaUnused hbetaStored
  · exact hzeroBeta
  · intro _
    exact hthetaStored
  · exact @helper_branch_1685 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@beta) (@hbetaGamma)

private theorem helper_hsame_3634.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let B : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    HierarchyFirstMissingPosition phi T D.alpha = D.penultimateVertexIndex →
    D.alpha ∉ TashkinovStoredColors ett.series.data (Fin.last ett.rounds) →
    let Bshort : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ));
    ∀ beta ∈ TreeMissingColors phi Bshort,
    (∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → phi (T.edge t) ≠ some beta) →
    beta ∉ HierarchyStoredColorsAt H q →
    (H.dividerCount = (0 : ℕ) →
        beta ∈ TreeMissingColors phi A →
          beta ∈
            TreeMissingColors phi (ett.series.data.tree (Fin.last ett.rounds).castSucc)) →
    (beta ∉ TreeMissingColors phi A → D.theta ∉ HierarchyStoredColorsAt H q) →
    (∀ eta ∈ HierarchyStoredColorsAt H q,
        beta ∈ C.good.gamma q eta → eta = D.theta ∨ eta ∈ TreeMissingColors phi Bshort) →
    beta ≠ D.alpha →
    beta ≠ D.theta →
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    beta ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T beta)) ∧
        (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ Bshort.length →
    T.vertex ib ∈ TreeSequenceVertexSet B →
    T.vertex ib ≠ T.vertex D.penultimateVertexIndex →
    T.vertex ib ≠ T.vertex D.terminalVertexIndex →
    TreeVertexOrder T (T.vertex ib) (T.vertex D.penultimateVertexIndex) →
    (beta ∉ TreeMissingColors phi A →
        beta ∉ TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) →
    beta ∈ TreeMissingColors phi B ∧ D.alpha ∈ TreeMissingColors phi B →
    (let H : TashkinovHierarchy ett base := C.hierarchy;
      have q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
      have n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
      have A : TreeSequence G e0 := HierarchyStarredStage H q;
      have Tnq : TreeSequence G e0 :=
        H.stage
          (⟨H.dividerCount, by
              have := GoldbergSeymour.TreeSequence.positive T
              omega⟩ :
            Fin (H.dividerCount + (2 : ℕ)));
      have Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
      have Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
      have Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q;
      have va : V := T.vertex (HierarchyFirstMissingPosition phi T beta);
      have vb : V := T.vertex (HierarchyFirstMissingPosition phi T D.alpha);
      have sameComponent : Prop :=
        TwoColorComponent G phi beta D.alpha (Sum.inl va) =
          TwoColorComponent G phi beta D.alpha (Sum.inl vb);
      ((0 : ℕ) < H.dividerCount ∧
            (beta ∈ TreeMissingColors phi Tnq ∨
              Disjoint (insert beta ({ D.alpha } : Finset (Fin k)) : Finset (Fin k)) Dnq) →
          sameComponent) ∧
        (H.dividerCount = (0 : ℕ) ∧
              (beta ∈ TreeMissingColors phi Tn ∨
                Disjoint (insert beta ({ D.alpha } : Finset (Fin k)) : Finset (Fin k)) Dn) →
            sameComponent) ∧
          (beta ∈ TreeMissingColors phi A ∧
              TreeColorSetClosed G phi A ({ beta } : Finset (Fin k)) →
            sameComponent ∧ TreeInterchangeable G A phi beta D.alpha)) →
    TwoColorComponent G phi beta D.alpha (Sum.inl (T.vertex ib)) =
      TwoColorComponent G phi beta D.alpha (Sum.inl (T.vertex D.penultimateVertexIndex)) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B hfirstAlpha halphaNotRaw Bshort
      beta hbetaMissing hbetaUnused hbetaStored hzero houtside hcutoff hbetaAlpha hbetaTheta ib
      hbFirst hibB hby hbt horder hrawBeta hmissing hchange
  exact @helper_hsame_747 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@hfirstAlpha)
      (@halphaNotRaw) (@beta) (@hbetaMissing) (@hbetaUnused) (@hbetaStored) (@hzero)
      (@houtside) (@hcutoff) (@hbetaAlpha) (@hbetaTheta) (@hbFirst) (@hibB) (@hby) (@hbt)
      (@horder) (@hrawBeta) (@hmissing) (@hchange)

private theorem helper_hsameTwo_3799.{u_1, u_2} :
    helperHsameTwo3799Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B hnotA Bshort sameStar sameLast
      beta hbetaMissing hbetaUnused hbetaStored hzero houtside hcutoff hbetaAlpha hbetaTheta ib
      hbFirst hibB hby hbt horder hrawBeta hmissing hchange hsame z muOne hdisjoint hpath
      houtsideBeta houtsideAlpha hmissingOne hfixedOne hstoredOne hcase corrOne hmaxOne baseOne
      KOne goodOne hsameOne hbTerminalOne POne hPOne rho ettOne baseOne' COne' HOne qOne
      hmissingA hbetaStoredOne hgammaPenOne hgammaTermOne hgammaWitnessOne' hfirstGammaOne
      hfirstThetaOne hgammaUnusedOne hcaseOne hmissingPairOne hchangeOne
  exact @helper_hsameTwo_964 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
      (@hnotA) (@sameStar) (@sameLast) (@beta) (@hbetaMissing) (@hbetaUnused)
      (@hbetaStored) (@hzero) (@houtside) (@hcutoff) (@hbetaAlpha) (@hbetaTheta) (@hbFirst)
      (@hibB) (@hby) (@hbt) (@horder) (@hrawBeta) (@hmissing) (@hchange) (@hsame)
      (@hdisjoint) (@hpath) (@houtsideBeta) (@houtsideAlpha) (@hmissingOne) (@hfixedOne)
      (@hstoredOne) (@hcase) (@corrOne) (@hmaxOne) (@baseOne) (@KOne) (@goodOne)
      (@hsameOne) (@hbTerminalOne) (@POne) (@hPOne) (@hmissingA) (@hbetaStoredOne)
      (@hgammaPenOne) (@hgammaTermOne) (@hgammaWitnessOne') (@hfirstGammaOne)
      (@hfirstThetaOne) (@hgammaUnusedOne) (@hcaseOne) (@hmissingPairOne) (@hchangeOne)

private theorem helper_branch_3865.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let B : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    (2 : ℕ) ≤ T.length - A.length →
    B.length + (1 : ℕ) = T.length →
    TreeSequenceInitialSegment B T →
    (H.dividerCount = (0 : ℕ) → A = base.core) →
    TreeSequenceInitialSegment A T →
    TreeSequenceInitialSegment A B →
    B.vertex (Fin.last B.length) = T.vertex D.penultimateVertexIndex →
    T.vertex D.penultimateVertexIndex ∈ TreeSequenceVertexSet B →
    ColoredVertexSetElementary G phi (TreeSequenceVertexSet B) →
    (∀ {c : Fin k},
        c ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex) →
          c ∉ TreeMissingColors phi A) →
    (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage P.counterexample.hierarchy
            (Fin.last P.counterexample.hierarchy.dividerCount) =
          A) →
    (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyFullTailPrefix P.counterexample
            (HierarchyFullTailLength P.counterexample - (1 : ℕ)) =
          B) →
    (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        P.corresponding.replacementETT.series.data.tree
            (Fin.last P.corresponding.replacementETT.rounds).castSucc =
          ett.series.data.tree (Fin.last ett.rounds).castSucc) →
    (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStoredColorsAt H q =
            HierarchyStoredColorsAt P.counterexample.hierarchy
              (Fin.last P.counterexample.hierarchy.dividerCount) ∧
          ∀ eta ∈ HierarchyStoredColorsAt H q,
            C.good.gamma q eta =
              P.counterexample.good.gamma (Fin.last P.counterexample.hierarchy.dividerCount)
                eta) →
    (∀ {X Y F : TreeSequence G e0},
        TreeSequenceInitialSegment X F →
          TreeSequenceInitialSegment Y F →
            X.length ≤ Y.length → TreeSequenceInitialSegment X Y) →
    base.core.length ≤ A.length →
    (∀ (X : TreeSequence G e0),
        TreeSequenceInitialSegment X T →
          ∀ (t : Fin T.length), (↑t : ℕ) = X.length → TreeIncidentEdge X (T.edge t)) →
    (∀ {input' : PartialEdgeColoring E k} (rho sigma : PartialEdgeColoring E k)
        (ett' : ExtendedTashkinovTree G k e0 input' T rho) (base' : HierarchyBase ett' rho)
        (K : TashkinovHierarchy ett' base'),
        HierarchyWeaklyStable K (Fin.last K.dividerCount) sigma →
          K.dividerCount = (0 : ℕ) →
            StableColoring (ett'.series.data.tree (Fin.last ett'.rounds).castSucc)
              (TashkinovStoredColors ett'.series.data (Fin.last ett'.rounds)) rho sigma) →
    (∀ {input' : PartialEdgeColoring E k} (old new : PartialEdgeColoring E k)
        (ett' : ExtendedTashkinovTree G k e0 input' T old) (base' : HierarchyBase ett' old)
        (K : TashkinovHierarchy ett' base'),
        HierarchyWeaklyStable K (Fin.last K.dividerCount) new →
          IsOneEdgeUncolored old e0 →
            IsOneEdgeUncolored new e0 →
              ∀ (t : Fin (HierarchyStarredStage K (Fin.last K.dividerCount)).length),
                new ((HierarchyStarredStage K (Fin.last K.dividerCount)).edge t) =
                  old ((HierarchyStarredStage K (Fin.last K.dividerCount)).edge t)) →
    ∀ (beta : Fin k),
    beta ≠ D.theta →
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    T.vertex ib ∈ TreeSequenceVertexSet B →
    let z : V ⊕ E := Sum.inl (T.vertex D.terminalVertexIndex);
    let muOne : PartialEdgeColoring E k := TwoColorComponentSwap G phi beta D.alpha z;
    (∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → muOne (T.edge t) = phi (T.edge t)) →
    ∀ (POne : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    POne.coloring = muOne →
    let rho : PartialEdgeColoring E k := POne.coloring;
    let ettOne :
      ExtendedTashkinovTree G k e0 POne.corresponding.replacementInput T POne.coloring :=
      POne.corresponding.replacementETT;
    let COne' : HierarchyCounterexample POne.replacementBase := POne.counterexample;
    let HOne : TashkinovHierarchy POne.corresponding.replacementETT POne.replacementBase :=
      COne'.hierarchy;
    let qOne : Fin (HOne.dividerCount + (1 : ℕ)) := Fin.last HOne.dividerCount;
    ColoredVertexSetElementary G rho (TreeSequenceVertexSet B) →
    D.theta ∈ MissingColors G rho (T.vertex D.penultimateVertexIndex) →
    beta ∈ MissingColors G rho (T.vertex ib) →
    HierarchyFirstMissingPosition rho T beta = ib →
    (∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → rho (T.edge t) ≠ some beta) →
    (beta ∈ TreeMissingColors phi A →
        (0 : ℕ) < HOne.dividerCount ∧
            beta ∈
              TreeMissingColors rho
                (HOne.stage
                  (⟨HOne.dividerCount,
                      by
                      have := GoldbergSeymour.TreeSequence.positive T
                      omega⟩ :
                    Fin (HOne.dividerCount + (2 : ℕ)))) ∨
          HOne.dividerCount = (0 : ℕ) ∧
            beta ∈
              TreeMissingColors rho
                (ettOne.series.data.tree (Fin.last ettOne.rounds).castSucc)) →
    beta ∈ TreeMissingColors rho B ∧ D.theta ∈ TreeMissingColors rho B →
    Disjoint
        (TwoColorComponent G rho beta D.theta (Sum.inl (T.vertex D.terminalVertexIndex)))
        (TwoColorComponent G rho beta D.theta (Sum.inl (T.vertex ib))) →
    let muTwo : PartialEdgeColoring E k := TwoColorComponentSwap G rho beta D.theta z;
    TwoColorPathComponent G rho beta D.theta z →
    (∀ w ∈ TreeSequenceVertexSet B,
        MissingColors G (TwoColorComponentSwap G rho beta D.theta z) w =
          MissingColors G rho w) →
    (∀ c ∈ HierarchyStoredColorsAt HOne qOne,
        HierarchyFirstMissingPosition muTwo T c = HierarchyFirstMissingPosition rho T c) →
    TashkinovAugmentationSequence rho B T →
    (∀ c ∈ HierarchyStoredColorsAt HOne qOne,
        beta ∈ POne.counterexample.good.gamma qOne c ∨
            D.theta ∈ POne.counterexample.good.gamma qOne c →
          (↑(HierarchyFirstMissingPosition rho T c) : ℕ) ≤ B.length) →
    beta ∈ TreeMissingColors phi A →
    ∃ (corrTwo : CorrespondingExtendedTashkinovTree G k e0 ettOne muTwo T),
    MaximumProperty corrTwo.replacementETT ∧
      ∃ (baseTwo : HierarchyBase corrTwo.replacementETT muTwo) (KTwo :
        TashkinovHierarchy corrTwo.replacementETT baseTwo) (goodTwo : GoodHierarchy KTwo),
        SameGoodHierarchy COne'.good goodTwo := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B htail hBlen hBT hAzero hAT hAB
      hBterminal hyB hElementary hnotA sameStar samePrefix sameTn sameLast commonPrefix
      hcoreLength predecessorIncident seedStable weakEdges beta hbetaTheta ib hibB z muOne
      hfixedOne POne hPOne rho ettOne COne' HOne qOne hElementaryOne hthetaPenOne
      hgammaWitnessOne' hfirstGammaOne hgammaUnusedOne hcaseOne hmissingPairOne hdisjointTwo
      muTwo hpathTwo hmissingTwo hstoredTwo hsuffix hgammaCutoff hm
  exact @helper_branch_3242 (@V) (@E) inferInstance inferInstance inferInstance
    inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
    (@htail) (@hBlen) (@hBT) (@hAzero) (@hAT) (@hAB) (@hBterminal) (@hyB) (@hElementary)
    (@hnotA) (@sameStar) (@samePrefix) (@sameTn) (@sameLast) (@commonPrefix)
    (@hcoreLength) (@predecessorIncident) (@seedStable) (@weakEdges) (@beta)
    (@hbetaTheta) (@hibB) (@hfixedOne) (@POne) (@hPOne) (@hElementaryOne) (@hthetaPenOne)
    (@hgammaWitnessOne') (@hfirstGammaOne) (@hgammaUnusedOne) (@hcaseOne)
    (@hmissingPairOne) (@hdisjointTwo) (@hpathTwo) (@hmissingTwo) (@hstoredTwo)
    (@hsuffix) (@hgammaCutoff) (@hm)

private theorem helper_branch_3874.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let B : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    TreeSequenceInitialSegment A T →
    (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage P.counterexample.hierarchy
            (Fin.last P.counterexample.hierarchy.dividerCount) =
          A) →
    (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyFullTailPrefix P.counterexample
            (HierarchyFullTailLength P.counterexample - (1 : ℕ)) =
          B) →
    (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStoredColorsAt H q =
            HierarchyStoredColorsAt P.counterexample.hierarchy
              (Fin.last P.counterexample.hierarchy.dividerCount) ∧
          ∀ eta ∈ HierarchyStoredColorsAt H q,
            C.good.gamma q eta =
              P.counterexample.good.gamma (Fin.last P.counterexample.hierarchy.dividerCount)
                eta) →
    ∀ beta ∉ HierarchyStoredColorsAt H q,
    (beta ∉ TreeMissingColors phi A → D.theta ∉ HierarchyStoredColorsAt H q) →
    beta ≠ D.theta →
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    TreeVertexOrder T (T.vertex ib) (T.vertex D.penultimateVertexIndex) →
    (∀ (rho : PartialEdgeColoring E k),
        ∀ c ∈ MissingColors G rho (T.vertex (HierarchyFirstMissingPosition rho T c)),
          c ∉ TreeMissingColors rho A →
            A.length < (↑(HierarchyFirstMissingPosition rho T c) : ℕ)) →
    let z : V ⊕ E := Sum.inl (T.vertex D.terminalVertexIndex);
    ∀ (POne : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let rho : PartialEdgeColoring E k := POne.coloring;
    let ettOne :
      ExtendedTashkinovTree G k e0 POne.corresponding.replacementInput T POne.coloring :=
      POne.corresponding.replacementETT;
    let COne' : HierarchyCounterexample POne.replacementBase := POne.counterexample;
    ColoredVertexSetElementary G rho (TreeSequenceVertexSet B) →
    TreeMissingColors rho A = TreeMissingColors phi A →
    beta ∈ MissingColors G rho (T.vertex ib) →
    HierarchyFirstMissingPosition rho T beta = ib →
    HierarchyFirstMissingPosition rho T D.theta = D.penultimateVertexIndex →
    (∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → rho (T.edge t) ≠ some beta) →
    beta ∈ TreeMissingColors rho B ∧ D.theta ∈ TreeMissingColors rho B →
    let muTwo : PartialEdgeColoring E k := TwoColorComponentSwap G rho beta D.theta z;
    beta ∉ TreeMissingColors phi A →
    ∃ (corrTwo : CorrespondingExtendedTashkinovTree G k e0 ettOne muTwo T),
    MaximumProperty corrTwo.replacementETT ∧
      ∃ (baseTwo : HierarchyBase corrTwo.replacementETT muTwo) (KTwo :
        TashkinovHierarchy corrTwo.replacementETT baseTwo) (goodTwo : GoodHierarchy KTwo),
        SameGoodHierarchy COne'.good goodTwo := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B hAT sameStar samePrefix sameLast
      beta hbetaStored houtside hbetaTheta ib horder firstAfter z POne rho ettOne COne'
      hElementaryOne hmissingA hgammaWitnessOne' hfirstGammaOne hfirstThetaOne hgammaUnusedOne
      hmissingPairOne muTwo hm
  exact @helper_branch_1228 (@V) (@E) inferInstance inferInstance inferInstance
    inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
    (@hAT) (@sameStar) (@samePrefix) (@sameLast) (@beta) (@hbetaStored) (@houtside)
    (@hbetaTheta) (@horder) (@firstAfter) (@POne) (@hElementaryOne) (@hmissingA)
    (@hgammaWitnessOne') (@hfirstGammaOne) (@hfirstThetaOne) (@hgammaUnusedOne)
    (@hmissingPairOne) (@hm)

private theorem helper_hsame_4639.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let B : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    HierarchyFirstMissingPosition phi T D.alpha = D.penultimateVertexIndex →
    D.alpha ∉ TashkinovStoredColors ett.series.data (Fin.last ett.rounds) →
    let Bshort : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ));
    ∀ beta ∈ TreeMissingColors phi Bshort,
    (∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → phi (T.edge t) ≠ some beta) →
    beta ∉ HierarchyStoredColorsAt H q →
    (H.dividerCount = (0 : ℕ) →
        beta ∈ TreeMissingColors phi A →
          beta ∈
            TreeMissingColors phi (ett.series.data.tree (Fin.last ett.rounds).castSucc)) →
    (beta ∉ TreeMissingColors phi A → D.theta ∉ HierarchyStoredColorsAt H q) →
    (∀ eta ∈ HierarchyStoredColorsAt H q,
        beta ∈ C.good.gamma q eta → eta = D.theta ∨ eta ∈ TreeMissingColors phi Bshort) →
    beta ≠ D.alpha →
    beta ≠ D.theta →
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    beta ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T beta)) ∧
        (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ Bshort.length →
    T.vertex ib ∈ TreeSequenceVertexSet B →
    T.vertex ib ≠ T.vertex D.penultimateVertexIndex →
    T.vertex ib ≠ T.vertex D.terminalVertexIndex →
    TreeVertexOrder T (T.vertex ib) (T.vertex D.penultimateVertexIndex) →
    (beta ∉ TreeMissingColors phi A →
        beta ∉ TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) →
    beta ∈ TreeMissingColors phi B ∧ D.alpha ∈ TreeMissingColors phi B →
    (let H : TashkinovHierarchy ett base := C.hierarchy;
      have q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
      have n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
      have A : TreeSequence G e0 := HierarchyStarredStage H q;
      have Tnq : TreeSequence G e0 :=
        H.stage
          (⟨H.dividerCount, by
              have := GoldbergSeymour.TreeSequence.positive T
              omega⟩ :
            Fin (H.dividerCount + (2 : ℕ)));
      have Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
      have Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
      have Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q;
      have va : V := T.vertex (HierarchyFirstMissingPosition phi T beta);
      have vb : V := T.vertex (HierarchyFirstMissingPosition phi T D.alpha);
      have sameComponent : Prop :=
        TwoColorComponent G phi beta D.alpha (Sum.inl va) =
          TwoColorComponent G phi beta D.alpha (Sum.inl vb);
      ((0 : ℕ) < H.dividerCount ∧
            (beta ∈ TreeMissingColors phi Tnq ∨
              Disjoint (insert beta ({ D.alpha } : Finset (Fin k)) : Finset (Fin k)) Dnq) →
          sameComponent) ∧
        (H.dividerCount = (0 : ℕ) ∧
              (beta ∈ TreeMissingColors phi Tn ∨
                Disjoint (insert beta ({ D.alpha } : Finset (Fin k)) : Finset (Fin k)) Dn) →
            sameComponent) ∧
          (beta ∈ TreeMissingColors phi A ∧
              TreeColorSetClosed G phi A ({ beta } : Finset (Fin k)) →
            sameComponent ∧ TreeInterchangeable G A phi beta D.alpha)) →
    TwoColorComponent G phi beta D.alpha (Sum.inl (T.vertex ib)) =
      TwoColorComponent G phi beta D.alpha (Sum.inl (T.vertex D.penultimateVertexIndex)) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B hfirstAlpha halphaNotRaw Bshort
      beta hbetaMissing hbetaUnused hbetaStored hzero houtside hcutoff hbetaAlpha hbetaTheta ib
      hbFirst hibB hby hbt horder hrawBeta hmissing hchange
  exact @helper_hsame_3634 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
      (@hfirstAlpha) (@halphaNotRaw) (@beta) (@hbetaMissing) (@hbetaUnused) (@hbetaStored)
      (@hzero) (@houtside) (@hcutoff) (@hbetaAlpha) (@hbetaTheta) (@hbFirst) (@hibB) (@hby)
      (@hbt) (@horder) (@hrawBeta) (@hmissing) (@hchange)

private theorem helper_hsameTwo_4804.{u_1, u_2} :
    helperHsameTwo4804Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B hnotA Bshort sameStar sameLast
      beta hbetaMissing hbetaUnused hbetaStored hzero houtside hcutoff hbetaAlpha hbetaTheta ib
      hbFirst hibB hby hbt horder hrawBeta hmissing hchange hsame z muOne hdisjoint hpath
      houtsideBeta houtsideAlpha hmissingOne hfixedOne hstoredOne hcase corrOne hmaxOne baseOne
      KOne goodOne hsameOne hbTerminalOne POne hPOne rho ettOne baseOne' COne' HOne qOne
      hmissingA hbetaStoredOne hgammaPenOne hgammaTermOne hgammaWitnessOne' hfirstGammaOne
      hfirstThetaOne hgammaUnusedOne hcaseOne hmissingPairOne hchangeOne
  exact @helper_hsameTwo_3799 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
      (@hnotA) (@sameStar) (@sameLast) (@beta) (@hbetaMissing) (@hbetaUnused)
      (@hbetaStored) (@hzero) (@houtside) (@hcutoff) (@hbetaAlpha) (@hbetaTheta) (@hbFirst)
      (@hibB) (@hby) (@hbt) (@horder) (@hrawBeta) (@hmissing) (@hchange) (@hsame)
      (@hdisjoint) (@hpath) (@houtsideBeta) (@houtsideAlpha) (@hmissingOne) (@hfixedOne)
      (@hstoredOne) (@hcase) (@corrOne) (@hmaxOne) (@baseOne) (@KOne) (@goodOne)
      (@hsameOne) (@hbTerminalOne) (@POne) (@hPOne) (@hmissingA) (@hbetaStoredOne)
      (@hgammaPenOne) (@hgammaTermOne) (@hgammaWitnessOne') (@hfirstGammaOne)
      (@hfirstThetaOne) (@hgammaUnusedOne) (@hcaseOne) (@hmissingPairOne) (@hchangeOne)

private theorem helper_branch_4870.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let B : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    (2 : ℕ) ≤ T.length - A.length →
    B.length + (1 : ℕ) = T.length →
    TreeSequenceInitialSegment B T →
    (H.dividerCount = (0 : ℕ) → A = base.core) →
    TreeSequenceInitialSegment A T →
    TreeSequenceInitialSegment A B →
    B.vertex (Fin.last B.length) = T.vertex D.penultimateVertexIndex →
    T.vertex D.penultimateVertexIndex ∈ TreeSequenceVertexSet B →
    ColoredVertexSetElementary G phi (TreeSequenceVertexSet B) →
    (∀ {c : Fin k},
        c ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex) →
          c ∉ TreeMissingColors phi A) →
    (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage P.counterexample.hierarchy
            (Fin.last P.counterexample.hierarchy.dividerCount) =
          A) →
    (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyFullTailPrefix P.counterexample
            (HierarchyFullTailLength P.counterexample - (1 : ℕ)) =
          B) →
    (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        P.corresponding.replacementETT.series.data.tree
            (Fin.last P.corresponding.replacementETT.rounds).castSucc =
          ett.series.data.tree (Fin.last ett.rounds).castSucc) →
    (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStoredColorsAt H q =
            HierarchyStoredColorsAt P.counterexample.hierarchy
              (Fin.last P.counterexample.hierarchy.dividerCount) ∧
          ∀ eta ∈ HierarchyStoredColorsAt H q,
            C.good.gamma q eta =
              P.counterexample.good.gamma (Fin.last P.counterexample.hierarchy.dividerCount)
                eta) →
    (∀ {X Y F : TreeSequence G e0},
        TreeSequenceInitialSegment X F →
          TreeSequenceInitialSegment Y F →
            X.length ≤ Y.length → TreeSequenceInitialSegment X Y) →
    base.core.length ≤ A.length →
    (∀ (X : TreeSequence G e0),
        TreeSequenceInitialSegment X T →
          ∀ (t : Fin T.length), (↑t : ℕ) = X.length → TreeIncidentEdge X (T.edge t)) →
    (∀ {input' : PartialEdgeColoring E k} (rho sigma : PartialEdgeColoring E k)
        (ett' : ExtendedTashkinovTree G k e0 input' T rho) (base' : HierarchyBase ett' rho)
        (K : TashkinovHierarchy ett' base'),
        HierarchyWeaklyStable K (Fin.last K.dividerCount) sigma →
          K.dividerCount = (0 : ℕ) →
            StableColoring (ett'.series.data.tree (Fin.last ett'.rounds).castSucc)
              (TashkinovStoredColors ett'.series.data (Fin.last ett'.rounds)) rho sigma) →
    (∀ {input' : PartialEdgeColoring E k} (old new : PartialEdgeColoring E k)
        (ett' : ExtendedTashkinovTree G k e0 input' T old) (base' : HierarchyBase ett' old)
        (K : TashkinovHierarchy ett' base'),
        HierarchyWeaklyStable K (Fin.last K.dividerCount) new →
          IsOneEdgeUncolored old e0 →
            IsOneEdgeUncolored new e0 →
              ∀ (t : Fin (HierarchyStarredStage K (Fin.last K.dividerCount)).length),
                new ((HierarchyStarredStage K (Fin.last K.dividerCount)).edge t) =
                  old ((HierarchyStarredStage K (Fin.last K.dividerCount)).edge t)) →
    ∀ (beta : Fin k),
    beta ≠ D.theta →
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    T.vertex ib ∈ TreeSequenceVertexSet B →
    let z : V ⊕ E := Sum.inl (T.vertex D.terminalVertexIndex);
    let muOne : PartialEdgeColoring E k := TwoColorComponentSwap G phi beta D.alpha z;
    (∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → muOne (T.edge t) = phi (T.edge t)) →
    ∀ (POne : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    POne.coloring = muOne →
    let rho : PartialEdgeColoring E k := POne.coloring;
    let ettOne :
      ExtendedTashkinovTree G k e0 POne.corresponding.replacementInput T POne.coloring :=
      POne.corresponding.replacementETT;
    let COne' : HierarchyCounterexample POne.replacementBase := POne.counterexample;
    let HOne : TashkinovHierarchy POne.corresponding.replacementETT POne.replacementBase :=
      COne'.hierarchy;
    let qOne : Fin (HOne.dividerCount + (1 : ℕ)) := Fin.last HOne.dividerCount;
    ColoredVertexSetElementary G rho (TreeSequenceVertexSet B) →
    D.theta ∈ MissingColors G rho (T.vertex D.penultimateVertexIndex) →
    beta ∈ MissingColors G rho (T.vertex ib) →
    HierarchyFirstMissingPosition rho T beta = ib →
    (∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → rho (T.edge t) ≠ some beta) →
    (beta ∈ TreeMissingColors phi A →
        (0 : ℕ) < HOne.dividerCount ∧
            beta ∈
              TreeMissingColors rho
                (HOne.stage
                  (⟨HOne.dividerCount,
                      by
                      have := GoldbergSeymour.TreeSequence.positive T
                      omega⟩ :
                    Fin (HOne.dividerCount + (2 : ℕ)))) ∨
          HOne.dividerCount = (0 : ℕ) ∧
            beta ∈
              TreeMissingColors rho
                (ettOne.series.data.tree (Fin.last ettOne.rounds).castSucc)) →
    beta ∈ TreeMissingColors rho B ∧ D.theta ∈ TreeMissingColors rho B →
    Disjoint
        (TwoColorComponent G rho beta D.theta (Sum.inl (T.vertex D.terminalVertexIndex)))
        (TwoColorComponent G rho beta D.theta (Sum.inl (T.vertex ib))) →
    let muTwo : PartialEdgeColoring E k := TwoColorComponentSwap G rho beta D.theta z;
    TwoColorPathComponent G rho beta D.theta z →
    (∀ w ∈ TreeSequenceVertexSet B,
        MissingColors G (TwoColorComponentSwap G rho beta D.theta z) w =
          MissingColors G rho w) →
    (∀ c ∈ HierarchyStoredColorsAt HOne qOne,
        HierarchyFirstMissingPosition muTwo T c = HierarchyFirstMissingPosition rho T c) →
    TashkinovAugmentationSequence rho B T →
    (∀ c ∈ HierarchyStoredColorsAt HOne qOne,
        beta ∈ POne.counterexample.good.gamma qOne c ∨
            D.theta ∈ POne.counterexample.good.gamma qOne c →
          (↑(HierarchyFirstMissingPosition rho T c) : ℕ) ≤ B.length) →
    beta ∈ TreeMissingColors phi A →
    ∃ (corrTwo : CorrespondingExtendedTashkinovTree G k e0 ettOne muTwo T),
    MaximumProperty corrTwo.replacementETT ∧
      ∃ (baseTwo : HierarchyBase corrTwo.replacementETT muTwo) (KTwo :
        TashkinovHierarchy corrTwo.replacementETT baseTwo) (goodTwo : GoodHierarchy KTwo),
        SameGoodHierarchy COne'.good goodTwo := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B htail hBlen hBT hAzero hAT hAB
      hBterminal hyB hElementary hnotA sameStar samePrefix sameTn sameLast commonPrefix
      hcoreLength predecessorIncident seedStable weakEdges beta hbetaTheta ib hibB z muOne
      hfixedOne POne hPOne rho ettOne COne' HOne qOne hElementaryOne hthetaPenOne
      hgammaWitnessOne' hfirstGammaOne hgammaUnusedOne hcaseOne hmissingPairOne hdisjointTwo
      muTwo hpathTwo hmissingTwo hstoredTwo hsuffix hgammaCutoff hm
  exact @helper_branch_3865 (@V) (@E) inferInstance inferInstance inferInstance
    inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
    (@htail) (@hBlen) (@hBT) (@hAzero) (@hAT) (@hAB) (@hBterminal) (@hyB) (@hElementary)
    (@hnotA) (@sameStar) (@samePrefix) (@sameTn) (@sameLast) (@commonPrefix)
    (@hcoreLength) (@predecessorIncident) (@seedStable) (@weakEdges) (@beta)
    (@hbetaTheta) (@hibB) (@hfixedOne) (@POne) (@hPOne) (@hElementaryOne) (@hthetaPenOne)
    (@hgammaWitnessOne') (@hfirstGammaOne) (@hgammaUnusedOne) (@hcaseOne)
    (@hmissingPairOne) (@hdisjointTwo) (@hpathTwo) (@hmissingTwo) (@hstoredTwo)
    (@hsuffix) (@hgammaCutoff) (@hm)

private theorem helper_branch_4879.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let B : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    TreeSequenceInitialSegment A T →
    (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage P.counterexample.hierarchy
            (Fin.last P.counterexample.hierarchy.dividerCount) =
          A) →
    (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyFullTailPrefix P.counterexample
            (HierarchyFullTailLength P.counterexample - (1 : ℕ)) =
          B) →
    (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStoredColorsAt H q =
            HierarchyStoredColorsAt P.counterexample.hierarchy
              (Fin.last P.counterexample.hierarchy.dividerCount) ∧
          ∀ eta ∈ HierarchyStoredColorsAt H q,
            C.good.gamma q eta =
              P.counterexample.good.gamma (Fin.last P.counterexample.hierarchy.dividerCount)
                eta) →
    ∀ beta ∉ HierarchyStoredColorsAt H q,
    (beta ∉ TreeMissingColors phi A → D.theta ∉ HierarchyStoredColorsAt H q) →
    beta ≠ D.theta →
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    TreeVertexOrder T (T.vertex ib) (T.vertex D.penultimateVertexIndex) →
    (∀ (rho : PartialEdgeColoring E k),
        ∀ c ∈ MissingColors G rho (T.vertex (HierarchyFirstMissingPosition rho T c)),
          c ∉ TreeMissingColors rho A →
            A.length < (↑(HierarchyFirstMissingPosition rho T c) : ℕ)) →
    let z : V ⊕ E := Sum.inl (T.vertex D.terminalVertexIndex);
    ∀ (POne : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let rho : PartialEdgeColoring E k := POne.coloring;
    let ettOne :
      ExtendedTashkinovTree G k e0 POne.corresponding.replacementInput T POne.coloring :=
      POne.corresponding.replacementETT;
    let COne' : HierarchyCounterexample POne.replacementBase := POne.counterexample;
    ColoredVertexSetElementary G rho (TreeSequenceVertexSet B) →
    TreeMissingColors rho A = TreeMissingColors phi A →
    beta ∈ MissingColors G rho (T.vertex ib) →
    HierarchyFirstMissingPosition rho T beta = ib →
    HierarchyFirstMissingPosition rho T D.theta = D.penultimateVertexIndex →
    (∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → rho (T.edge t) ≠ some beta) →
    beta ∈ TreeMissingColors rho B ∧ D.theta ∈ TreeMissingColors rho B →
    let muTwo : PartialEdgeColoring E k := TwoColorComponentSwap G rho beta D.theta z;
    beta ∉ TreeMissingColors phi A →
    ∃ (corrTwo : CorrespondingExtendedTashkinovTree G k e0 ettOne muTwo T),
    MaximumProperty corrTwo.replacementETT ∧
      ∃ (baseTwo : HierarchyBase corrTwo.replacementETT muTwo) (KTwo :
        TashkinovHierarchy corrTwo.replacementETT baseTwo) (goodTwo : GoodHierarchy KTwo),
        SameGoodHierarchy COne'.good goodTwo := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B hAT sameStar samePrefix sameLast
      beta hbetaStored houtside hbetaTheta ib horder firstAfter z POne rho ettOne COne'
      hElementaryOne hmissingA hgammaWitnessOne' hfirstGammaOne hfirstThetaOne hgammaUnusedOne
      hmissingPairOne muTwo hm
  exact @helper_branch_3874 (@V) (@E) inferInstance inferInstance inferInstance
    inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
    (@hAT) (@sameStar) (@samePrefix) (@sameLast) (@beta) (@hbetaStored) (@houtside)
    (@hbetaTheta) (@horder) (@firstAfter) (@POne) (@hElementaryOne) (@hmissingA)
    (@hgammaWitnessOne') (@hfirstGammaOne) (@hfirstThetaOne) (@hgammaUnusedOne)
    (@hmissingPairOne) (@hm)

private noncomputable abbrev helperTailTwo6007.{u_1, u_2} :
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
                                          HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett
                                            base C ctx) →
                                        let H : TashkinovHierarchy ett base := C.hierarchy;
                                        let q : Fin (H.dividerCount + (1 : ℕ)) :=
                                          Fin.last H.dividerCount;
                                        let A : TreeSequence G e0 := HierarchyStarredStage H q;
                                        (2 : ℕ) ≤ T.length - A.length →
                                          (∀
                                              (P :
                                                HierarchyReplacementPresentation G k e0 input T phi
                                                  ett base C ctx),
                                              HierarchyStarredStage P.counterexample.hierarchy
                                                  (Fin.last
                                                    P.counterexample.hierarchy.dividerCount) =
                                                A) →
                                            (beta : Fin k) →
                                              let z : V ⊕ E :=
                                                Sum.inl (T.vertex D.terminalVertexIndex);
                                              (POne :
                                                  HierarchyReplacementPresentation G k e0 input T
                                                    phi ett base C ctx) →
                                                let rho : PartialEdgeColoring E k := POne.coloring;
                                                let muTwo : PartialEdgeColoring E k :=
                                                  TwoColorComponentSwap G rho beta D.theta z;
                                                muTwo (T.edge D.lastEdgeIndex) = some beta →
                                                  beta ∉
                                                      MissingColors G muTwo
                                                        (T.vertex D.penultimateVertexIndex) →
                                                    (PTwo :
                                                        HierarchyReplacementPresentation G k e0
                                                          input T phi ett base C ctx) →
                                                      PTwo.coloring = muTwo →
                                                        HierarchySituationTwoTailData G k e0
                                                          PTwo.corresponding.replacementInput T
                                                          PTwo.coloring
                                                          PTwo.corresponding.replacementETT
                                                          PTwo.replacementBase PTwo.counterexample
                                                          PTwo.minimumContext := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A htail sameStar beta z POne rho
      muTwo hlastTwo hgammaPenTwo PTwo hPTwo
  exact {
    tailAtLeastTwo := by
      change 2 ≤ T.length - (HierarchyStarredStage PTwo.counterexample.hierarchy
        (Fin.last PTwo.counterexample.hierarchy.dividerCount)).length
      rw [sameStar PTwo]
      exact htail
    pathNumberFull := by
      have hp := D.pathNumberFull
      unfold HierarchyPathNumber HierarchyFullTailLength at hp ⊢
      dsimp only at hp ⊢
      rw [sameStar PTwo]
      exact hp
    lastEdgeIndex := D.lastEdgeIndex
    penultimateVertexIndex := D.penultimateVertexIndex
    terminalVertexIndex := D.terminalVertexIndex
    lastEdgePosition := D.lastEdgePosition
    penultimateVertexPosition := D.penultimateVertexPosition
    terminalVertexPosition := D.terminalVertexPosition
    lastEdgeNotIncidentPenultimate := D.lastEdgeNotIncidentPenultimate
    theta := beta
    thetaOnLastEdge := hPTwo.symm ▸ hlastTwo
    thetaPresentPenultimate := hPTwo.symm ▸ hgammaPenTwo }

private theorem helper_branch_6081.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    ∀ (htail : (2 : ℕ) ≤ T.length - A.length)
      (sameStar :
        ∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
          HierarchyStarredStage P.counterexample.hierarchy
              (Fin.last P.counterexample.hierarchy.dividerCount) =
            A)
      (beta : Fin k),
    let z : V ⊕ E := Sum.inl (T.vertex D.terminalVertexIndex);
    ∀ (POne : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let rho : PartialEdgeColoring E k := POne.coloring;
    let muTwo : PartialEdgeColoring E k := TwoColorComponentSwap G rho beta D.theta z;
    ∀ (hlastTwo : muTwo (T.edge D.lastEdgeIndex) = some beta),
    D.theta ∈ MissingColors G muTwo (T.vertex D.terminalVertexIndex) →
    D.theta ∈ MissingColors G muTwo (T.vertex D.penultimateVertexIndex) →
    ∀ (hgammaPenTwo : beta ∉ MissingColors G muTwo (T.vertex D.penultimateVertexIndex))
      (PTwo : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
      (hPTwo : PTwo.coloring = muTwo),
    let _ :
      HierarchySituationTwoTailData G k e0 PTwo.corresponding.replacementInput T
        PTwo.coloring PTwo.corresponding.replacementETT PTwo.replacementBase
        PTwo.counterexample PTwo.minimumContext :=
      helperTailTwo6007 G k e0 input T phi ett base C ctx D htail sameStar beta POne
        hlastTwo hgammaPenTwo PTwo hPTwo;
    D.theta ∈
        HierarchyStoredColorsAt PTwo.counterexample.hierarchy
          (Fin.last PTwo.counterexample.hierarchy.dividerCount) →
    False := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A htail sameStar beta z POne rho
      muTwo hlastTwo hthetaTermTwo hthetaPenTwo hgammaPenTwo PTwo hPTwo tailTwo hstored
  obtain ⟨g1, g2, hne, hpair⟩ := Finset.card_eq_two.mp
    (PTwo.counterexample.good.twoColors _ D.theta hstored)
  let finalData : HierarchySituationTwoCaseOneData G k e0
      PTwo.corresponding.replacementInput T
      PTwo.coloring PTwo.corresponding.replacementETT PTwo.replacementBase
      PTwo.counterexample PTwo.minimumContext :=
    { toHierarchySituationTwoTailData := tailTwo
      alpha := D.theta
      gammaOne := g1
      gammaTwo := g2
      alphaMissingPenultimate := by
        change D.theta ∈ MissingColors G PTwo.coloring (T.vertex D.penultimateVertexIndex)
        rw [hPTwo]
        exact hthetaPenTwo
      alphaMissingTerminal := by
        change D.theta ∈ MissingColors G PTwo.coloring (T.vertex D.terminalVertexIndex)
        rw [hPTwo]
        exact hthetaTermTwo
      alphaStored := hstored
      gammaPair := hpair
      gammaDistinct := hne }
  exact HierarchySituationTwoSubcaseOneOne G k e0 PTwo.corresponding.replacementInput T
    PTwo.coloring PTwo.corresponding.replacementETT PTwo.replacementBase
    PTwo.counterexample PTwo.minimumContext finalData

private theorem helper_branch_6105.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    ∀ (htail : (2 : ℕ) ≤ T.length - A.length)
      (sameStar :
        ∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
          HierarchyStarredStage P.counterexample.hierarchy
              (Fin.last P.counterexample.hierarchy.dividerCount) =
            A)
      (beta : Fin k),
    let z : V ⊕ E := Sum.inl (T.vertex D.terminalVertexIndex);
    ∀ (POne : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let rho : PartialEdgeColoring E k := POne.coloring;
    let muTwo : PartialEdgeColoring E k := TwoColorComponentSwap G rho beta D.theta z;
    ∀ (hlastTwo : muTwo (T.edge D.lastEdgeIndex) = some beta),
    D.theta ∈ MissingColors G muTwo (T.vertex D.terminalVertexIndex) →
    D.theta ∈ MissingColors G muTwo (T.vertex D.penultimateVertexIndex) →
    ∀ (hgammaPenTwo : beta ∉ MissingColors G muTwo (T.vertex D.penultimateVertexIndex))
      (PTwo : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
      (hPTwo : PTwo.coloring = muTwo),
    let _ :
      HierarchySituationTwoTailData G k e0 PTwo.corresponding.replacementInput T
        PTwo.coloring PTwo.corresponding.replacementETT PTwo.replacementBase
        PTwo.counterexample PTwo.minimumContext :=
      helperTailTwo6007 G k e0 input T phi ett base C ctx D htail sameStar beta POne
        hlastTwo hgammaPenTwo PTwo hPTwo;
    D.theta ∉
        HierarchyStoredColorsAt PTwo.counterexample.hierarchy
          (Fin.last PTwo.counterexample.hierarchy.dividerCount) →
    False := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A htail sameStar beta z POne rho
      muTwo hlastTwo hthetaTermTwo hthetaPenTwo hgammaPenTwo PTwo hPTwo tailTwo hstored
  let finalData : HierarchySituationTwoCaseTwoData G k e0
    PTwo.corresponding.replacementInput T
      PTwo.coloring PTwo.corresponding.replacementETT PTwo.replacementBase
      PTwo.counterexample PTwo.minimumContext :=
    { toHierarchySituationTwoTailData := tailTwo
      alpha := D.theta
      alphaMissingPenultimate := by
        change D.theta ∈ MissingColors G PTwo.coloring (T.vertex D.penultimateVertexIndex)
        rw [hPTwo]
        exact hthetaPenTwo
      alphaMissingTerminal := by
        change D.theta ∈ MissingColors G PTwo.coloring (T.vertex D.terminalVertexIndex)
        rw [hPTwo]
        exact hthetaTermTwo
      alphaOutsideStored := hstored }
  exact HierarchySituationTwoSubcaseTwoOne G k e0 PTwo.corresponding.replacementInput T
    PTwo.coloring PTwo.corresponding.replacementETT PTwo.replacementBase
    PTwo.counterexample PTwo.minimumContext finalData

private theorem helper_continuation_5379.{u_1, u_2} :
    helperContinuation5379Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B htail hBlen hBT hAzero hAT hAB
      hBterminal hyB hElementary hfirstTheta hnotA Bshort hshortT hshortB hterminalIncident
      firstWitness self missingSubset leaf separate prefixMissing firstPreserved firstUnaffected
      sameStar samePrefix sameTn sameLast commonPrefix hcoreLength predecessorIncident seedStable
      weakEdges beta hbetaMissing hbetaUnused hbetaStored hzero houtside hcutoff hbetaAlpha
      hbetaTheta ib hbFirst hibB hby hbt hyt horder firstAfter hrawBeta hmissing hchange hsame z
      muOne hdisjoint hpath houtsideBeta houtsideAlpha hmissingOne hfixedOne hstoredOne hcase
      corrOne hmaxOne baseOne KOne goodOne hsameOne hbTerminalOne POne hPOne rho ettOne baseOne'
      COne' ctxOne HOne qOne hmissingOne' hElementaryOne missingEq
  have hmissingA := missingEq A hAB
  have hbetaStoredOne : beta ∉ HierarchyStoredColorsAt HOne qOne := by
    rw [← (sameLast POne).1]
    exact hbetaStored
  have hthetaPenOne : D.theta ∈ MissingColors G rho (T.vertex D.penultimateVertexIndex) := by
    rw [hmissingOne' _ hyB]
    exact D.thetaMissingPenultimate
  have hgammaPenOne : beta ∉ MissingColors G rho (T.vertex D.penultimateVertexIndex) := by
    rw [hmissingOne' _ hyB]
    intro hm
    exact Finset.disjoint_left.mp (hElementary hibB hyB hby) hbFirst.1 hm
  have hgammaTermOne : beta ∈ MissingColors G rho (T.vertex D.terminalVertexIndex) := by
    rw [show rho = muOne from hPOne]
    exact hbTerminalOne
  have hgammaWitnessOne' : beta ∈ MissingColors G rho (T.vertex ib) := by
    rw [hmissingOne' _ hibB]
    exact hbFirst.1
  have hfirstGammaOne : HierarchyFirstMissingPosition rho T beta = ib :=
    firstPreserved phi rho beta hElementary hmissingOne' hmissing.1
  have hfirstThetaOne : HierarchyFirstMissingPosition rho T D.theta =
      D.penultimateVertexIndex :=
    (firstPreserved phi rho D.theta hElementary hmissingOne'
      (Finset.mem_biUnion.mpr ⟨_, hyB, D.thetaMissingPenultimate⟩)).trans hfirstTheta
  have hgammaUnusedOne : ∀ t : Fin T.length, A.length ≤ t.val →
      rho (T.edge t) ≠ some beta := by
    intro t ht
    rw [show rho = muOne from hPOne, hfixedOne t ht]
    exact hbetaUnused t ht
  have hcaseOne (hm : beta ∈ TreeMissingColors phi A) :
      (0 < HOne.dividerCount ∧ beta ∈ TreeMissingColors rho
        (HOne.stage ⟨HOne.dividerCount, by omega⟩)) ∨
      (HOne.dividerCount = 0 ∧ beta ∈ TreeMissingColors rho
        (ettOne.series.data.tree (Fin.last ettOne.rounds).castSucc)) := by
    exact @helper_hcaseOne_906 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@hBlen) (@hBT) (@sameStar) (@sameTn) (@commonPrefix) (@beta) (@hzero) (@POne)
        (@missingEq) (@hmissingA) (@hm)
  have hmissingPairOne : beta ∈ TreeMissingColors rho B ∧ D.theta ∈ TreeMissingColors rho B :=
    ⟨Finset.mem_biUnion.mpr ⟨_, hibB, hgammaWitnessOne'⟩,
      Finset.mem_biUnion.mpr ⟨_, hyB, hthetaPenOne⟩⟩
  have hchangeOne := ChangeLemma G k e0 POne.corresponding.replacementInput T rho ettOne
    baseOne' COne' ctxOne.proper ctxOne.oneEdgeUncolored ctxOne.lowerRung
    ctxOne.fewerDividers ctxOne.lexicographicMinimality
    (by
      change ColoredVertexSetElementary G rho
        (TreeSequenceVertexSet (HierarchyFullTailPrefix COne' (HierarchyFullTailLength COne'
            - 1)))
      rw [samePrefix POne]
      exact hElementaryOne)
    ctxOne.largeMissingSet beta D.theta hbetaTheta
    (by
      change beta ∈ TreeMissingColors rho
        (HierarchyFullTailPrefix COne' (HierarchyFullTailLength COne' - 1)) ∧
        D.theta ∈ TreeMissingColors rho
          (HierarchyFullTailPrefix COne' (HierarchyFullTailLength COne' - 1))
      rw [samePrefix POne]
      exact hmissingPairOne)
    (by
      dsimp only
      rw [sameStar POne, hfirstGammaOne, hfirstThetaOne]
      intro _
      refine ⟨horder, ?_⟩
      intro hc
      obtain ⟨t, ht, _, he⟩ := (Finset.mem_filter.mp hc).2
      exact hgammaUnusedOne t ht he)
  have hsameTwo : TwoColorComponent G rho beta D.theta (Sum.inl (T.vertex ib)) =
      TwoColorComponent G rho beta D.theta
        (Sum.inl (T.vertex D.penultimateVertexIndex)) := by
    exact @helper_hsameTwo_4804 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@hnotA) (@sameStar)
        (@sameLast) (@beta) (@hbetaMissing) (@hbetaUnused) (@hbetaStored) (@hzero) (@houtside)
        (@hcutoff) (@hbetaAlpha) (@hbetaTheta) (@hbFirst) (@hibB) (@hby) (@hbt) (@horder)
        (@hrawBeta) (@hmissing) (@hchange) (@hsame) (@hdisjoint) (@hpath) (@houtsideBeta)
        (@houtsideAlpha) (@hmissingOne) (@hfixedOne) (@hstoredOne) (@hcase) (@corrOne) (@hmaxOne)
        (@baseOne) (@KOne) (@goodOne) (@hsameOne) (@hbTerminalOne) (@POne) (@hPOne) (@hmissingA)
        (@hbetaStoredOne) (@hgammaPenOne) (@hgammaTermOne) (@hgammaWitnessOne') (@hfirstGammaOne)
        (@hfirstThetaOne) (@hgammaUnusedOne) (@hcaseOne) (@hmissingPairOne) (@hchangeOne)
  have hdisjointTwo := separate rho beta D.theta hbetaTheta ctxOne.proper
    (T.vertex ib) (T.vertex D.penultimateVertexIndex) (T.vertex D.terminalVertexIndex)
    hby hbt hyt hgammaWitnessOne' hthetaPenOne (Or.inl hgammaTermOne) hsameTwo
  let muTwo := TwoColorComponentSwap G rho beta D.theta z
  have hpathTwo : TwoColorPathComponent G rho beta D.theta z :=
    ⟨hbetaTheta, _, self rho beta D.theta _,
      leaf rho beta D.theta hbetaTheta ctxOne.proper _ (Or.inl hgammaTermOne)⟩
  have houtsideBetaTwo : Sum.inl (T.vertex ib) ∉ TwoColorComponent G rho beta D.theta z := by
    intro hm
    exact Set.disjoint_left.mp hdisjointTwo hm (self rho beta D.theta _)
  have houtsideThetaTwo : Sum.inl (T.vertex D.penultimateVertexIndex) ∉
      TwoColorComponent G rho beta D.theta z := by
    intro hm
    apply Set.disjoint_left.mp hdisjointTwo hm
    rw [hsameTwo]
    exact self rho beta D.theta _
  have hmissingTwo := prefixMissing z rho beta D.theta hbetaTheta ctxOne.proper
    hElementaryOne _ _ hibB hyB hgammaWitnessOne' hthetaPenOne
    houtsideBetaTwo houtsideThetaTwo
  have hstoredTwo : ∀ c ∈ HierarchyStoredColorsAt HOne qOne,
      HierarchyFirstMissingPosition muTwo T c = HierarchyFirstMissingPosition rho T c := by
    exact @helper_hstoredTwo_1017 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@firstPreserved) (@firstUnaffected) (@beta) (@hbetaTheta) (@POne) (@hElementaryOne)
        (@hbetaStoredOne) (@hmissingPairOne) (@hmissingTwo)
  have hthetaLastOne : rho (T.edge D.lastEdgeIndex) = some D.theta := by
    exact @helper_hthetaLastOne_1025 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@htail) (@beta) (@hfixedOne) (@POne) (@hPOne)
  have hsuffix : TashkinovAugmentationSequence rho B T := by
    exact @helper_hsuffix_1031 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@hBlen) (@hBT) (@beta) (@POne) (@hmissingPairOne) (@hthetaLastOne)
  have hthetaBound : (HierarchyFirstMissingPosition rho T D.theta).val ≤ B.length := by
    rw [hfirstThetaOne]
    have hp := D.penultimateVertexPosition
    clear * - hp hBlen
    omega
  have hgammaCutoff : ∀ c ∈ HierarchyStoredColorsAt HOne qOne,
      (beta ∈ POne.counterexample.good.gamma qOne c ∨
        D.theta ∈ POne.counterexample.good.gamma qOne c) →
      (HierarchyFirstMissingPosition rho T c).val ≤ B.length := by
    exact @helper_hgammaCutoff_1047 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@hElementary) (@hnotA) (@hshortT) (@hshortB) (@firstWitness) (@missingSubset)
        (@firstPreserved) (@sameLast) (@beta) (@hcutoff) (@POne) (@hmissingOne') (@hthetaBound)
  obtain ⟨corrTwo, hmaxTwo, baseTwo, KTwo, goodTwo, hsameGoodTwo⟩ : ∃ corrTwo :
      CorrespondingExtendedTashkinovTree G k e0 ettOne muTwo T,
      MaximumProperty corrTwo.replacementETT ∧
        ∃ baseTwo : HierarchyBase corrTwo.replacementETT muTwo,
          ∃ KTwo : TashkinovHierarchy corrTwo.replacementETT baseTwo,
            ∃ goodTwo : GoodHierarchy KTwo, SameGoodHierarchy COne'.good goodTwo := by
    by_cases hm : beta ∈ TreeMissingColors phi A
    · exact @helper_branch_4870 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@htail) (@hBlen)
        (@hBT) (@hAzero) (@hAT) (@hAB) (@hBterminal) (@hyB) (@hElementary) (@hnotA) (@sameStar)
        (@samePrefix) (@sameTn) (@sameLast) (@commonPrefix) (@hcoreLength) (@predecessorIncident)
        (@seedStable) (@weakEdges) (@beta) (@hbetaTheta) (@hibB) (@hfixedOne) (@POne) (@hPOne)
        (@hElementaryOne) (@hthetaPenOne) (@hgammaWitnessOne') (@hfirstGammaOne)
        (@hgammaUnusedOne) (@hcaseOne) (@hmissingPairOne) (@hdisjointTwo) (@hpathTwo)
        (@hmissingTwo) (@hstoredTwo) (@hsuffix) (@hgammaCutoff) (@hm)
    · exact @helper_branch_4879 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@hAT) (@sameStar)
        (@samePrefix) (@sameLast) (@beta) (@hbetaStored) (@houtside) (@hbetaTheta) (@horder)
        (@firstAfter) (@POne) (@hElementaryOne) (@hmissingA) (@hgammaWitnessOne')
        (@hfirstGammaOne) (@hfirstThetaOne) (@hgammaUnusedOne) (@hmissingPairOne) (@hm)
  have hlastComponent : Sum.inr (T.edge D.lastEdgeIndex) ∈ TwoColorComponent G rho beta
      D.theta z := by
    exact @helper_hlastComponent_1263 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@hterminalIncident) (@beta) (@POne) (@hthetaLastOne)
  have hlastTwo : muTwo (T.edge D.lastEdgeIndex) = some beta := by
    simp [muTwo, TwoColorComponentSwap, hlastComponent, hthetaLastOne, hbetaTheta.symm]
  have hthetaTermTwo : D.theta ∈ MissingColors G muTwo (T.vertex D.terminalVertexIndex) :=
    (TwoColorComponentSwapMissingBehavior G rho beta D.theta hbetaTheta ctxOne.proper z).2.1
      _ (self rho beta D.theta _) hgammaTermOne
  have hthetaPenTwo : D.theta ∈ MissingColors G muTwo (T.vertex D.penultimateVertexIndex) := by
    rw [hmissingTwo _ hyB]
    exact hthetaPenOne
  have hgammaPenTwo : beta ∉ MissingColors G muTwo (T.vertex D.penultimateVertexIndex) := by
    rw [hmissingTwo _ hyB]
    exact hgammaPenOne
  let CTwo : HierarchyCounterexample baseTwo :=
    { positive := by rw [corrTwo.rungAgreement]; exact COne'.positive
      hierarchy := KTwo
      good := goodTwo
      maximum := hmaxTwo
      notElementary := by
        intro he
        have hy : T.vertex D.penultimateVertexIndex ∈ TreeSequenceVertexSet T := by simp
            [TreeSequenceVertexSet]
        have ht : T.vertex D.terminalVertexIndex ∈ TreeSequenceVertexSet T := by simp
            [TreeSequenceVertexSet]
        exact Finset.disjoint_left.mp (he hy ht hyt) hthetaPenTwo hthetaTermTwo }
  obtain ⟨PTwo, hPTwo⟩ := HierarchyReplacementPresentationTrans G k e0 input T phi
    ett base C ctx POne muTwo corrTwo baseTwo CTwo hsameGoodTwo
  let tailTwo : HierarchySituationTwoTailData G k e0 PTwo.corresponding.replacementInput T
      PTwo.coloring PTwo.corresponding.replacementETT PTwo.replacementBase
      PTwo.counterexample PTwo.minimumContext := by
    exact @helperTailTwo6007 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@htail) (@sameStar)
        (@beta) (@POne) (@hlastTwo) (@hgammaPenTwo) (@PTwo) (@hPTwo)
  by_cases hstored : D.theta ∈ HierarchyStoredColorsAt PTwo.counterexample.hierarchy
      (Fin.last PTwo.counterexample.hierarchy.dividerCount)
  · exact @helper_branch_6081 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@htail) (@sameStar)
      (@beta) (@POne) (@hlastTwo) (@hthetaTermTwo) (@hthetaPenTwo) (@hgammaPenTwo) (@PTwo)
      (@hPTwo) (@hstored)
  · exact @helper_branch_6105 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@htail) (@sameStar)
      (@beta) (@POne) (@hlastTwo) (@hthetaTermTwo) (@hthetaPenTwo) (@hgammaPenTwo) (@PTwo)
      (@hPTwo) (@hstored)
private theorem helper_reduction_4203.{u_1, u_2} :
    helperReduction4203Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B htail hBlen hBT hApositive hAzero
      hAT hAB hBterminal hyB hElementary hfirstAlpha hfirstTheta hnotA halphaNotRaw Bshort
      hshortLen hshortT hshortB hnotShort hterminalIncident halphaUnused firstWitness self
      missingSubset leaf separate prefixMissing firstPreserved firstUnaffected seriesFacts
      corrRefl PRefl sameStar samePrefix sameTn sameLast commonPrefix hcoreLength
      predecessorIncident seedStable weakEdges beta hbetaMissing hbetaUnused hbetaStored hzero
      houtside hcutoff
  as_aux_lemma =>
    have hbetaAlpha : beta ≠ D.alpha := by
      exact ne_of_mem_of_not_mem hbetaMissing (hnotShort (c := D.alpha) D.alphaMissingPenultimate)
    have hbetaTheta : beta ≠ D.theta := by
      exact @helper_hbetaTheta_676 (@V) (@E) inferInstance inferInstance inferInstance
          inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
          (@htail) (@beta) (@hbetaUnused)
    let ib := HierarchyFirstMissingPosition phi T beta
    have hbFirst := firstWitness phi Bshort hshortT beta hbetaMissing
    have hibB : T.vertex ib ∈ TreeSequenceVertexSet B := by
      let i : Fin (Bshort.length + 1) := ⟨ib.val, by have := hbFirst.2; omega⟩
      exact TreeSequenceInitialSegmentVertexSetSubset hshortB
        ((@Finset.mem_image _ _ (Classical.decEq V)).mpr ⟨i, Finset.mem_univ _, rfl⟩)
    have hby : T.vertex ib ≠ T.vertex D.penultimateVertexIndex := by
      exact @helper_hby_688 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
          (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@hshortLen)
          (@beta) (@hbFirst)
    have hbt : T.vertex ib ≠ T.vertex D.terminalVertexIndex := by
      exact @helper_hbt_695 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
          (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@hshortLen)
          (@beta) (@hbFirst)
    have hyt : T.vertex D.penultimateVertexIndex ≠ T.vertex D.terminalVertexIndex := by
      exact @helper_hyt_702 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
          (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
    have horder : TreeVertexOrder T (T.vertex ib) (T.vertex D.penultimateVertexIndex) :=
      ⟨ib, D.penultimateVertexIndex, rfl, rfl, by
        have hb : ib.val ≤ Bshort.length := hbFirst.2
        have hp := D.penultimateVertexPosition
        clear * - hb hp hshortLen
        omega⟩
    have firstAfter (rho : PartialEdgeColoring E k) (c : Fin k)
        (hc : c ∈ MissingColors G rho (T.vertex (HierarchyFirstMissingPosition rho T c)))
        (hn : c ∉ TreeMissingColors rho A) :
        A.length < (HierarchyFirstMissingPosition rho T c).val := by
      exact @helper_firstAfter_715 (@V) (@E) inferInstance inferInstance inferInstance
          inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hAT) (@rho)
          (@c) (@hc) (@hn)
    have hrawBeta (hn : beta ∉ TreeMissingColors phi A) :
        beta ∉ TashkinovStoredColors ett.series.data (Fin.last ett.rounds) := by
      intro hd
      exact hbetaStored (Finset.mem_sdiff.mpr ⟨hd, hn⟩)
    have hmissing : beta ∈ TreeMissingColors phi B ∧ D.alpha ∈ TreeMissingColors phi B :=
      ⟨Finset.mem_biUnion.mpr ⟨_, hibB, hbFirst.1⟩,
        Finset.mem_biUnion.mpr ⟨_, hyB, D.alphaMissingPenultimate⟩⟩
    have hchange := ChangeLemma G k e0 input T phi ett base C ctx.proper
      ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers ctx.lexicographicMinimality
      hElementary ctx.largeMissingSet beta D.alpha hbetaAlpha hmissing
      (by
        dsimp only
        rw [hfirstAlpha]
        intro _
        refine ⟨horder, ?_⟩
        intro hc
        obtain ⟨t, ht, _, he⟩ := (Finset.mem_filter.mp hc).2
        exact hbetaUnused t ht he)
    have hsame : TwoColorComponent G phi beta D.alpha (Sum.inl (T.vertex ib)) =
        TwoColorComponent G phi beta D.alpha
          (Sum.inl (T.vertex D.penultimateVertexIndex)) := by
      exact @helper_hsame_4639 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
          (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@hfirstAlpha)
          (@halphaNotRaw) (@beta) (@hbetaMissing) (@hbetaUnused) (@hbetaStored) (@hzero)
          (@houtside) (@hcutoff) (@hbetaAlpha) (@hbetaTheta) (@hbFirst) (@hibB) (@hby) (@hbt)
          (@horder) (@hrawBeta) (@hmissing) (@hchange)
    let z : Sum V E := Sum.inl (T.vertex D.terminalVertexIndex)
    let muOne := TwoColorComponentSwap G phi beta D.alpha z
    have hdisjoint := separate phi beta D.alpha hbetaAlpha ctx.proper
      (T.vertex ib) (T.vertex D.penultimateVertexIndex) (T.vertex D.terminalVertexIndex)
      hby hbt hyt hbFirst.1 D.alphaMissingPenultimate (Or.inr D.alphaMissingTerminal) hsame
    have hpath : TwoColorPathComponent G phi beta D.alpha z :=
      ⟨hbetaAlpha, _, self phi beta D.alpha _,
        leaf phi beta D.alpha hbetaAlpha ctx.proper _ (Or.inr D.alphaMissingTerminal)⟩
    have houtsideBeta : Sum.inl (T.vertex ib) ∉ TwoColorComponent G phi beta D.alpha z := by
      intro hm
      exact Set.disjoint_left.mp hdisjoint hm (self phi beta D.alpha _)
    have houtsideAlpha : Sum.inl (T.vertex D.penultimateVertexIndex) ∉
        TwoColorComponent G phi beta D.alpha z := by
      intro hm
      apply Set.disjoint_left.mp hdisjoint hm
      rw [hsame]
      exact self phi beta D.alpha _
    have hmissingOne := prefixMissing z phi beta D.alpha hbetaAlpha ctx.proper
      hElementary _ _ hibB hyB hbFirst.1 D.alphaMissingPenultimate houtsideBeta houtsideAlpha
    have hfixedOne : ∀ t : Fin T.length, A.length ≤ t.val →
        muOne (T.edge t) = phi (T.edge t) := by
      intro t ht
      have ha := halphaUnused t ht
      have hb := hbetaUnused t ht
      simp only [muOne, TwoColorComponentSwap, hb, ha, ite_false, ite_self]
    have hstoredOne : ∀ c ∈ HierarchyStoredColorsAt H q,
        HierarchyFirstMissingPosition muOne T c = HierarchyFirstMissingPosition phi T c := by
      intro c hc
      have hcb : c ≠ beta := fun he => hbetaStored (he ▸ hc)
      have hca : c ≠ D.alpha := fun he => D.alphaOutsideStored (he ▸ hc)
      exact firstUnaffected z phi beta D.alpha c hbetaAlpha ctx.proper hcb hca
    have hcase (hm : beta ∈ TreeMissingColors phi A) :
        (0 < H.dividerCount ∧ beta ∈ TreeMissingColors phi
          (H.stage ⟨H.dividerCount, by omega⟩)) ∨
        (H.dividerCount = 0 ∧ beta ∈ TreeMissingColors phi
          (ett.series.data.tree (Fin.last ett.rounds).castSucc)) := by
      by_cases hz : H.dividerCount = 0
      · exact Or.inr ⟨hz, hzero hz hm⟩
      · exact Or.inl ⟨Nat.pos_of_ne_zero hz, hApositive (Nat.pos_of_ne_zero hz) ▸ hm⟩
    obtain ⟨corrOne, hmaxOne, baseOne, KOne, goodOne, hsameOne⟩ : ∃ corrOne :
        CorrespondingExtendedTashkinovTree G k e0 ett muOne T,
        MaximumProperty corrOne.replacementETT ∧
          ∃ baseOne : HierarchyBase corrOne.replacementETT muOne,
            ∃ KOne : TashkinovHierarchy corrOne.replacementETT baseOne,
              ∃ goodOne : GoodHierarchy KOne, SameGoodHierarchy C.good goodOne := by
      by_cases hm : beta ∈ TreeMissingColors phi A
      · exact @helper_branch_815 (@V) (@E) inferInstance inferInstance inferInstance
          inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
          (@beta) (@hbetaAlpha) (@hmissing) (@hdisjoint) (@hpath) (@hmissingOne) (@hfixedOne)
          (@hstoredOne) (@hcase) (@hm)
      · exact @helper_branch_821 (@V) (@E) inferInstance inferInstance inferInstance
          inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
          (@hAT) (@hElementary) (@hfirstAlpha) (@beta) (@hbetaUnused) (@hbetaStored)
          (@hbetaAlpha) (@hbFirst) (@horder) (@firstAfter) (@hmissing) (@hm)
    have hbTerminalOne : beta ∈ MissingColors G muOne (T.vertex D.terminalVertexIndex) :=
      (TwoColorComponentSwapMissingBehavior G phi beta D.alpha hbetaAlpha ctx.proper z).2.2.1
        _ (self phi beta D.alpha _) D.alphaMissingTerminal
    let COne : HierarchyCounterexample baseOne :=
      { positive := by rw [corrOne.rungAgreement]; exact C.positive
        hierarchy := KOne
        good := goodOne
        maximum := hmaxOne
        notElementary := by
          intro he
          have hb : T.vertex ib ∈ TreeSequenceVertexSet T :=
            (@Finset.mem_image _ _ (Classical.decEq V)).mpr ⟨ib, Finset.mem_univ _, rfl⟩
          have ht : T.vertex D.terminalVertexIndex ∈ TreeSequenceVertexSet T :=
            (@Finset.mem_image _ _ (Classical.decEq V)).mpr ⟨_, Finset.mem_univ _, rfl⟩
          exact Finset.disjoint_left.mp (he hb ht hbt)
            ((hmissingOne _ hibB).symm ▸ hbFirst.1) hbTerminalOne }
    obtain ⟨POne, hPOne⟩ := HierarchyReplacementPresentationTrans G k e0 input T phi
      ett base C ctx PRefl muOne corrOne baseOne COne hsameOne
    let rho := POne.coloring
    let ettOne := POne.corresponding.replacementETT
    let baseOne' := POne.replacementBase
    let COne' := POne.counterexample
    let ctxOne := POne.minimumContext
    let HOne := COne'.hierarchy
    let qOne : Fin (HOne.dividerCount + 1) := Fin.last HOne.dividerCount
    have hmissingOne' : ∀ v ∈ TreeSequenceVertexSet B,
        MissingColors G rho v = MissingColors G phi v := by
      rw [show rho = muOne from hPOne]
      exact hmissingOne
    have hElementaryOne : ColoredVertexSetElementary G rho (TreeSequenceVertexSet B) := by
      intro u hu v hv huv
      rw [hmissingOne' u hu, hmissingOne' v hv]
      exact hElementary hu hv huv
    have missingEq (X : TreeSequence G e0) (hXB : TreeSequenceInitialSegment X B) :
        TreeMissingColors rho X = TreeMissingColors phi X := by
      unfold TreeMissingColors
      exact Finset.biUnion_congr rfl (fun v hv =>
        hmissingOne' v (TreeSequenceInitialSegmentVertexSetSubset hXB hv))
    exact @helper_continuation_5379 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@htail) (@hBlen) (@hBT) (@hAzero) (@hAT) (@hAB) (@hBterminal) (@hyB) (@hElementary)
        (@hfirstTheta) (@hnotA) (@hshortT) (@hshortB) (@hterminalIncident) (@firstWitness)
        (@self) (@missingSubset) (@leaf) (@separate) (@prefixMissing) (@firstPreserved)
        (@firstUnaffected) (@sameStar) (@samePrefix) (@sameTn) (@sameLast) (@commonPrefix)
        (@hcoreLength) (@predecessorIncident) (@seedStable) (@weakEdges) (@beta) (@hbetaMissing)
        (@hbetaUnused) (@hbetaStored) (@hzero) (@houtside) (@hcutoff) (@hbetaAlpha) (@hbetaTheta)
        (@hbFirst) (@hibB) (@hby) (@hbt) (@hyt) (@horder) (@firstAfter) (@hrawBeta) (@hmissing)
        (@hchange) (@hsame) (@hdisjoint) (@hpath) (@houtsideBeta) (@houtsideAlpha) (@hmissingOne)
        (@hfixedOne) (@hstoredOne) (@hcase) (@corrOne) (@hmaxOne) (@baseOne) (@KOne) (@goodOne)
        (@hsameOne) (@hbTerminalOne) (@POne) (@hPOne) (@hmissingOne') (@hElementaryOne) (@missingEq)
private theorem helper_continuation_4157.{u_1, u_2} :
    helperContinuation4157Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B htail hBlen hBT hApositive hAzero
      hAT hAB hBterminal hyB hElementary hfirstAlpha hfirstTheta hnotA halphaNotRaw Bshort
      hshortLen hshortT hshortB hnotShort hterminalIncident halphaUnused firstWitness self
      missingSubset missingWithoutExtra leaf separate prefixMissing firstPreserved
  have firstUnaffected (z : Sum V E) (rho : PartialEdgeColoring E k) (a b c : Fin k)
      (hne : a ≠ b) (hp : IsProperEdgeColoring G rho) (hca : c ≠ a) (hcb : c ≠ b) :
      HierarchyFirstMissingPosition (TwoColorComponentSwap G rho a b z) T c =
        HierarchyFirstMissingPosition rho T c := by
    exact @helper_firstUnaffected_480 (@V) (@E) inferInstance inferInstance (@G) (@k) (@e0) (@T)
        (@z) (@rho) (@a) (@b) (@c) (@hne) (@hp) (@hca) (@hcb)
  have seriesFacts : ∀ j : Fin (ett.rounds + 1),
      IsProperEdgeColoring G (ett.series.data.coloring j) ∧
        IsOneEdgeUncolored (ett.series.data.coloring j) e0 := by
    exact @helper_seriesFacts_495 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@phi) (@ett)
  let corrRefl : CorrespondingExtendedTashkinovTree G k e0 ett phi T :=
    { replacementInput := input
      replacementSeries := ett.series
      replacementETT := ett
      rungAgreement := rfl
      seriesPresentation := HEq.rfl
      finalGeneratingColoring := ett.generatingColoring
      ladderTreesAgree := fun _ => rfl
      storedColorsAgree := fun _ => rfl
      connectingEdgesAgree := fun _ => rfl
      extensionKindsAgree := fun _ => rfl
      replacementProper := fun j => (seriesFacts j).1
      replacementOneUncolored := fun j => (seriesFacts j).2
      replacementStable := fun _ => ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩ }
  let PRefl : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx :=
    { coloring := phi
      corresponding := corrRefl
      maximum := C.maximum
      replacementBase := base
      counterexample := C
      sameGood := ⟨⟨rfl, rfl, HEq.rfl, HEq.rfl, Iff.rfl, fun _ => rfl⟩,
        rfl, fun _ => ⟨rfl, fun _ _ => rfl⟩⟩
      minimumContext := ctx }
  have sameStar (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) :
      HierarchyStarredStage P.counterexample.hierarchy
        (Fin.last P.counterexample.hierarchy.dividerCount) = A := by
    exact @helper_sameStar_549 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
  have samePrefix (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) :
      HierarchyFullTailPrefix P.counterexample (HierarchyFullTailLength P.counterexample - 1) = B
         := by
    simp only [HierarchyFullTailPrefix, HierarchyFullTailLength, sameStar P]
    rfl
  have sameTn (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) :
      P.corresponding.replacementETT.series.data.tree
        (Fin.last P.corresponding.replacementETT.rounds).castSucc =
          ett.series.data.tree (Fin.last ett.rounds).castSucc := by
    have hs := (Fin.heq_fun_iff
      (congrArg (fun n => n + 2) P.sameGood.1.2.1)).mp P.sameGood.1.2.2.1 0
    exact P.counterexample.hierarchy.baseStage.symm.trans (hs.symm.trans H.baseStage)
  have sameLast (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) :
      HierarchyStoredColorsAt H q =
        HierarchyStoredColorsAt P.counterexample.hierarchy
          (Fin.last P.counterexample.hierarchy.dividerCount) ∧
      ∀ eta ∈ HierarchyStoredColorsAt H q,
        C.good.gamma q eta = P.counterexample.good.gamma
          (Fin.last P.counterexample.hierarchy.dividerCount) eta := by
    obtain ⟨hc, hd⟩ := P.sameGood.2
    have hi : Fin.cast (congrArg (fun n => n + 1) hc) q =
        Fin.last P.counterexample.hierarchy.dividerCount := Fin.ext hc
    simpa only [hi] using hd q
  have commonPrefix {X Y F : TreeSequence G e0}
      (hXF : TreeSequenceInitialSegment X F) (hYF : TreeSequenceInitialSegment Y F)
      (hXY : X.length ≤ Y.length) : TreeSequenceInitialSegment X Y := by
    exact @helper_commonPrefix_588 (@V) (@E) (@G) (@e0) (@X) (@Y) (@F) (@hXF) (@hYF) (@hXY)
  have hcoreLength : base.core.length ≤ A.length := by
    exact @helper_hcoreLength_597 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@hApositive) (@hAzero)
  have predecessorIncident (X : TreeSequence G e0)
      (hXT : TreeSequenceInitialSegment X T) (t : Fin T.length)
      (ht : t.val = X.length) : TreeIncidentEdge X (T.edge t) := by
    exact @helper_predecessorIncident_606 (@V) (@E) inferInstance inferInstance (@G) (@e0) (@T)
        (@X) (@hXT) (@t) (@ht)
  have seedStable {input' : PartialEdgeColoring E k}
      (rho sigma : PartialEdgeColoring E k)
      (ett' : ExtendedTashkinovTree G k e0 input' T rho)
      (base' : HierarchyBase ett' rho) (K : TashkinovHierarchy ett' base')
      (hw : HierarchyWeaklyStable K (Fin.last K.dividerCount) sigma)
      (hq : K.dividerCount = 0) :
      StableColoring (ett'.series.data.tree (Fin.last ett'.rounds).castSucc)
        (TashkinovStoredColors ett'.series.data (Fin.last ett'.rounds)) rho sigma := by
    exact @helper_seedStable_618 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@T) (@input') (@rho) (@sigma) (@ett') (@base') (@K) (@hw)
        (@hq)
  have weakEdges {input' : PartialEdgeColoring E k}
      (old new : PartialEdgeColoring E k)
      (ett' : ExtendedTashkinovTree G k e0 input' T old)
      (base' : HierarchyBase ett' old) (K : TashkinovHierarchy ett' base')
      (hw : HierarchyWeaklyStable K (Fin.last K.dividerCount) new)
      (ho : IsOneEdgeUncolored old e0) (hno : IsOneEdgeUncolored new e0) :
      ∀ t : Fin (HierarchyStarredStage K (Fin.last K.dividerCount)).length,
        new ((HierarchyStarredStage K (Fin.last K.dividerCount)).edge t) =
          old ((HierarchyStarredStage K (Fin.last K.dividerCount)).edge t) := by
    exact @helper_weakEdges_634 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@T) (@input') (@old) (@new) (@ett') (@base') (@K) (@hw) (@ho) (@hno)
  have reduction (beta : Fin k)
      (hbetaMissing : beta ∈ TreeMissingColors phi Bshort)
      (hbetaUnused : ∀ t : Fin T.length, A.length ≤ t.val →
        phi (T.edge t) ≠ some beta)
      (hbetaStored : beta ∉ HierarchyStoredColorsAt H q)
      (hzero : H.dividerCount = 0 → beta ∈ TreeMissingColors phi A →
        beta ∈ TreeMissingColors phi
          (ett.series.data.tree (Fin.last ett.rounds).castSucc))
      (houtside : beta ∉ TreeMissingColors phi A →
        D.theta ∉ HierarchyStoredColorsAt H q)
      (hcutoff : ∀ eta ∈ HierarchyStoredColorsAt H q,
        beta ∈ C.good.gamma q eta →
          eta = D.theta ∨ eta ∈ TreeMissingColors phi Bshort) : False := by
    exact @helper_reduction_4203 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@htail) (@hBlen) (@hBT) (@hApositive) (@hAzero) (@hAT) (@hAB) (@hBterminal) (@hyB)
        (@hElementary) (@hfirstAlpha) (@hfirstTheta) (@hnotA) (@halphaNotRaw) (@hshortLen)
        (@hshortT) (@hshortB) (@hnotShort) (@hterminalIncident) (@halphaUnused) (@firstWitness)
        (@self) (@missingSubset) (@leaf) (@separate) (@prefixMissing) (@firstPreserved)
        (@firstUnaffected) (@seriesFacts) (@sameStar) (@samePrefix) (@sameTn) (@sameLast)
        (@commonPrefix) (@hcoreLength) (@predecessorIncident) (@seedStable) (@weakEdges) (@beta)
        (@hbetaMissing) (@hbetaUnused) (@hbetaStored) (@hzero) (@houtside) (@hcutoff)
  by_cases hthetaStored : D.theta ∈ HierarchyStoredColorsAt H q
  · exact @helper_branch_1360 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@htail) (@hApositive)
      (@hAzero) (@hAT) (@hfirstTheta) (@hshortLen) (@missingSubset) (@reduction) (@hthetaStored)
  · exact @helper_branch_3441 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@htail) (@hApositive)
      (@hAzero) (@hAT) (@hAB) (@hElementary) (@hnotA) (@hshortLen) (@missingSubset)
      (@missingWithoutExtra) (@reduction) (@hthetaStored)

theorem HierarchySituationTwoSubcaseTwoTwo {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (D : HierarchySituationTwoCaseTwoTwoData
      G k e0 input T phi ett base C ctx) :
    False := by
  classical
  let H := C.hierarchy
  let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
  let A := HierarchyStarredStage H q
  let B := HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1)
  have htail : 2 ≤ T.length - A.length := D.tailAtLeastTwo
  have hBlen : B.length + 1 = T.length := by
    simp only [B, HierarchyFullTailPrefix, HierarchyFullTailLength,
      TreeSequencePrefix]
    change min (A.length + (T.length - A.length - 1)) T.length + 1 = T.length
    omega
  have hBT : TreeSequenceInitialSegment B T := by
    exact @helper_hBT_115 (@V) (@E) inferInstance inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hBlen)
  have hApositive (hq : 0 < H.dividerCount) :
      A = H.stage ⟨H.dividerCount, by omega⟩ := by
    exact @helper_hApositive_122 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hq)
  have hAzero (hq : H.dividerCount = 0) : A = base.core := by
    have hi : q = 0 := by apply Fin.ext; simp [q, hq]
    change HierarchyStarredStage H q = _
    rw [hi]
    rfl
  have hAT : TreeSequenceInitialSegment A T := by
    exact @helper_hAT_140 (@V) (@E) inferInstance inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hApositive) (@hAzero)
  have hAB : TreeSequenceInitialSegment A B := by
    exact @helper_hAB_152 (@V) (@E) inferInstance inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@htail) (@hBlen) (@hApositive)
        (@hAzero) (@hAT)
  have hBterminal : B.vertex (Fin.last B.length) = T.vertex D.penultimateVertexIndex := by
    exact @helper_hBterminal_158 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@hBlen) (@hBT)
  have hyB : T.vertex D.penultimateVertexIndex ∈ TreeSequenceVertexSet B := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨Fin.last B.length, hBterminal⟩
  have hElementary : ColoredVertexSetElementary G phi (TreeSequenceVertexSet B) :=
    HierarchyCounterexamplePenultimateElementary G k e0 input T phi ett base C
      ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
      ctx.lexicographicMinimality ctx.largeMissingSet
  have firstAt {c : Fin k}
      (hc : c ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex)) :
      HierarchyFirstMissingPosition phi T c = D.penultimateVertexIndex := by
    exact @helper_firstAt_172 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@hBlen) (@hyB)
        (@hElementary) (@c) (@hc)
  have hfirstAlpha := firstAt D.alphaMissingPenultimate
  have hfirstTheta := firstAt D.thetaMissingPenultimate
  have hnotA {c : Fin k}
      (hc : c ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex)) :
      c ∉ TreeMissingColors phi A := by
    exact @helper_hnotA_197 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@htail)
        (@hApositive) (@hAzero) (@hAT) (@hAB) (@hyB) (@hElementary) (@hfirstTheta) (@c) (@hc)
  have halphaNotRaw :
      D.alpha ∉ TashkinovStoredColors ett.series.data (Fin.last ett.rounds) := by
    intro hc
    exact D.alphaOutsideStored
      (Finset.mem_sdiff.mpr ⟨hc, hnotA (c := D.alpha) D.alphaMissingPenultimate⟩)
  let Bshort := HierarchyFullTailPrefix C (HierarchyFullTailLength C - 2)
  have hshortLen : Bshort.length + 2 = T.length := by
    change min (A.length + (T.length - A.length - 2)) T.length + 2 = T.length
    omega
  have hshortT : TreeSequenceInitialSegment Bshort T :=
    ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
  have hshortB : TreeSequenceInitialSegment Bshort B := by
    exact @helper_hshortB_225 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@hBlen) (@hshortLen)
  have hnotShort {c : Fin k}
      (hc : c ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex)) :
      c ∉ TreeMissingColors phi Bshort := by
    exact @helper_hnotShort_231 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@hyB)
        (@hElementary) (@hfirstTheta) (@hshortLen) (@hshortT) (@hshortB) (@c) (@hc)
  have hterminalIncident :
      Incident G (T.vertex D.terminalVertexIndex) (T.edge D.lastEdgeIndex) := by
    exact @helper_hterminalIncident_247 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@hshortLen)
  have halphaLast : phi (T.edge D.lastEdgeIndex) ≠ some D.alpha := by
    exact @helper_halphaLast_259 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@hterminalIncident)
  have halphaUnused : ∀ t : Fin T.length, A.length ≤ t.val →
      phi (T.edge t) ≠ some D.alpha := by
    exact @helper_halphaUnused_265 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@htail) (@hBlen) (@hBT) (@hApositive) (@hAzero) (@hBterminal) (@hElementary)
        (@halphaNotRaw) (@hshortLen) (@halphaLast)
  have firstWitness (rho : PartialEdgeColoring E k) (X : TreeSequence G e0)
      (hXT : TreeSequenceInitialSegment X T) (c : Fin k)
      (hc : c ∈ TreeMissingColors rho X) :
      c ∈ MissingColors G rho (T.vertex (HierarchyFirstMissingPosition rho T c)) ∧
      (HierarchyFirstMissingPosition rho T c).val ≤ X.length := by
    exact @helper_firstWitness_291 (@V) (@E) inferInstance inferInstance (@G) (@k) (@e0) (@T)
        (@rho) (@X) (@hXT) (@c) (@hc)
  have self (rho : PartialEdgeColoring E k) (a b : Fin k) (v : V) :
      Sum.inl v ∈ TwoColorComponent G rho a b (Sum.inl v) := by
    change (TwoColorIncidenceGraph G rho a b).connectedComponentMk (Sum.inl v) = _
    rfl
  have missingSubset (rho : PartialEdgeColoring E k) {X Y : TreeSequence G e0}
      (hXY : TreeSequenceInitialSegment X Y) :
      TreeMissingColors rho X ⊆ TreeMissingColors rho Y := by
    exact @helper_missingSubset_322 (@V) (@E) inferInstance inferInstance (@G) (@k) (@e0) (@rho)
        (@X) (@Y) (@hXY)
  have missingWithoutExtra (rho : PartialEdgeColoring E k)
      (X Y : TreeSequence G e0) (c : Fin k)
      (hc : c ∉ (TreeSequenceVertexSet X \ TreeSequenceVertexSet Y).biUnion
        (fun v => MissingColors G rho v)) :
      c ∈ TreeMissingColors rho X → c ∈ TreeMissingColors rho Y := by
    exact @helper_missingWithoutExtra_331 (@V) (@E) inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@rho) (@X) (@Y) (@c) (@hc)
  have leaf (rho : PartialEdgeColoring E k) (a b : Fin k) (hne : a ≠ b)
      (hp : IsProperEdgeColoring G rho) (v : V)
      (hm : a ∈ MissingColors G rho v ∨ b ∈ MissingColors G rho v) :
      Set.Subsingleton ((TwoColorIncidenceGraph G rho a b).neighborSet (Sum.inl v)) := by
    exact @helper_leaf_344 (@V) (@E) inferInstance inferInstance (@G) (@k) (@rho) (@a) (@b)
        (@hne) (@hp) (@v) (@hm)
  have separate (rho : PartialEdgeColoring E k) (a b : Fin k) (hne : a ≠ b)
      (hp : IsProperEdgeColoring G rho) (u v w : V)
      (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
      (hu : a ∈ MissingColors G rho u) (hv : b ∈ MissingColors G rho v)
      (hw : a ∈ MissingColors G rho w ∨ b ∈ MissingColors G rho w)
      (hsame : TwoColorComponent G rho a b (Sum.inl u) =
        TwoColorComponent G rho a b (Sum.inl v)) :
      Disjoint (TwoColorComponent G rho a b (Sum.inl w))
        (TwoColorComponent G rho a b (Sum.inl u)) := by
    exact @helper_separate_363 (@V) (@E) inferInstance inferInstance
        (@G) (@k) (@self) (@leaf) (@rho) (@a) (@b) (@hne) (@hp) (@u) (@v) (@w) (@huv) (@huw)
        (@hvw) (@hu) (@hv) (@hw) (@hsame)
  have prefixMissing (z : Sum V E) (rho : PartialEdgeColoring E k) (a b : Fin k) (hne : a ≠ b)
      (hp : IsProperEdgeColoring G rho)
      (helem : ColoredVertexSetElementary G rho (TreeSequenceVertexSet B))
      (u v : V) (huB : u ∈ TreeSequenceVertexSet B) (hvB : v ∈ TreeSequenceVertexSet B)
      (hu : a ∈ MissingColors G rho u) (hv : b ∈ MissingColors G rho v)
      (hdu : Sum.inl u ∉ TwoColorComponent G rho a b z)
      (hdv : Sum.inl v ∉ TwoColorComponent G rho a b z) :
      ∀ w ∈ TreeSequenceVertexSet B,
        MissingColors G (TwoColorComponentSwap G rho a b z) w = MissingColors G rho w := by
    exact @helper_prefixMissing_397 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@z) (@rho) (@a)
        (@b) (@hne) (@hp) (@helem) (@u) (@v) (@huB) (@hvB) (@hu) (@hv) (@hdu) (@hdv)
  have firstPreserved (rho sigma : PartialEdgeColoring E k) (c : Fin k)
      (helem : ColoredVertexSetElementary G rho (TreeSequenceVertexSet B))
      (hmiss : ∀ v ∈ TreeSequenceVertexSet B, MissingColors G sigma v = MissingColors G rho v)
      (hc : c ∈ TreeMissingColors rho B) :
      HierarchyFirstMissingPosition sigma T c = HierarchyFirstMissingPosition rho T c := by
    exact @helper_firstPreserved_455 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hBT)
        (@firstWitness) (@rho) (@sigma) (@c) (@helem) (@hmiss) (@hc)
  exact @helper_continuation_4157 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@htail)
      (@hBlen) (@hBT) (@hApositive) (@hAzero) (@hAT) (@hAB) (@hBterminal) (@hyB) (@hElementary)
      (@hfirstAlpha) (@hfirstTheta) (@hnotA) (@halphaNotRaw) (@hshortLen) (@hshortT) (@hshortB)
      (@hnotShort) (@hterminalIncident) (@halphaUnused) (@firstWitness) (@self) (@missingSubset)
      (@missingWithoutExtra) (@leaf) (@separate) (@prefixMissing) (@firstPreserved)
end GoldbergSeymour

end
