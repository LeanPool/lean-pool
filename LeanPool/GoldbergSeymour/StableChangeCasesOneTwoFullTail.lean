/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TechnicalTheoremBase
public import LeanPool.GoldbergSeymour.CertifiedETTPredecessor
public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTree
public import LeanPool.GoldbergSeymour.CombinedStableColoring
public import LeanPool.GoldbergSeymour.BoundaryColorEdges
public import LeanPool.GoldbergSeymour.BoundaryEdges
public import LeanPool.GoldbergSeymour.ExtendedTashkinovTree
public import LeanPool.GoldbergSeymour.GoodHierarchy
public import LeanPool.GoldbergSeymour.HierarchyBase
public import LeanPool.GoldbergSeymour.HierarchyCounterexample
public import LeanPool.GoldbergSeymour.HierarchyFirstMissingPosition
public import LeanPool.GoldbergSeymour.HierarchyFirstMissingPositionPrefixCutoff
public import LeanPool.GoldbergSeymour.HierarchyFullTailLength
public import LeanPool.GoldbergSeymour.HierarchyFullTailPrefix
public import LeanPool.GoldbergSeymour.HierarchyMinimumCounterexampleContext
public import LeanPool.GoldbergSeymour.HierarchySegmentColors
public import LeanPool.GoldbergSeymour.HierarchySplitter
public import LeanPool.GoldbergSeymour.HierarchyStageMissingColors
public import LeanPool.GoldbergSeymour.HierarchyStarredStage
public import LeanPool.GoldbergSeymour.HierarchyStoredColorsAt
public import LeanPool.GoldbergSeymour.HierarchyCounterexamplePenultimateElementary
public import LeanPool.GoldbergSeymour.HierarchyCounterexampleTailAtLeastTwo
public import LeanPool.GoldbergSeymour.HierarchyWeaklyStable
public import LeanPool.GoldbergSeymour.MaximumPropertyTransport
public import LeanPool.GoldbergSeymour.MissingColors
public import LeanPool.GoldbergSeymour.ModColoring
public import LeanPool.GoldbergSeymour.OrderedTreeUnion
public import LeanPool.GoldbergSeymour.SameGoodHierarchy
public import LeanPool.GoldbergSeymour.StableColoring
public import LeanPool.GoldbergSeymour.StableChangeCasesOneTwo
public import LeanPool.GoldbergSeymour.TashkinovAugmentation
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequence
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceRestrict
public import LeanPool.GoldbergSeymour.TashkinovClosure
public import LeanPool.GoldbergSeymour.TashkinovHierarchy
public import LeanPool.GoldbergSeymour.TashkinovSeries
public import LeanPool.GoldbergSeymour.TashkinovSeriesStep
public import LeanPool.GoldbergSeymour.TashkinovStoredColors
public import LeanPool.GoldbergSeymour.TreeColorSetMinusClosed
public import LeanPool.GoldbergSeymour.TreeColorSetClosed
public import LeanPool.GoldbergSeymour.TreeColoringInvariant
public import LeanPool.GoldbergSeymour.TreeMissingColors
public import LeanPool.GoldbergSeymour.TreeSequence
public import LeanPool.GoldbergSeymour.TreeSequenceAdjoinEdge
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegment
public import LeanPool.GoldbergSeymour.TreeSequencePrefix
public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet
public import LeanPool.GoldbergSeymour.TwoColorComponentSwap
public import LeanPool.GoldbergSeymour.TwoColorPathComponent
public import LeanPool.GoldbergSeymour.BaseControl
public import LeanPool.GoldbergSeymour.DisplayedEdges
public import LeanPool.GoldbergSeymour.RecoloredPrefixReconstruction
public import LeanPool.GoldbergSeymour.MinusClosedTransport
public import LeanPool.GoldbergSeymour.PrefixSegmentTransport
public import LeanPool.GoldbergSeymour.GoodHierarchyPrefixRepackage
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceColoringTransport
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceSuffix
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequencePosition

/-!
# Stable Change Cases One Two Full Tail

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev helperPositivePackage887Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base)
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (alpha beta : Fin k)
   (hne : alpha ≠ beta) (z : V ⊕ E) (sigma : PartialEdgeColoring E k)
   (hsigma : sigma = TwoColorComponentSwap G phi alpha beta z),
   let H : TashkinovHierarchy ett base := C.hierarchy;
   let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
   let A : TreeSequence G e0 := HierarchyStarredStage H q;
   let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
   let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
   let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
   ∀
    (outside :
     ∀ (r : Fin (C.hierarchy.dividerCount + (1 : ℕ))) (c : Fin k),
      c = alpha ∨ c = beta →
       c ∈ TreeMissingColors phi (HierarchyStarredStage C.hierarchy r) →
        TreeColorSetClosed G phi (HierarchyStarredStage C.hierarchy r) { c } →
         OutsideKempeRecoloring (HierarchyStarredStage C.hierarchy r) phi sigma alpha beta)
    (missingA : ∀ v ∈ TreeSequenceVertexSet A, MissingColors G sigma v = MissingColors G phi v)
    (TnToA : TreeSequenceInitialSegment Tn A)
    (ordinaryToA :
     ∀ (j : Fin (H.dividerCount + (1 : ℕ))), TreeSequenceInitialSegment (H.stage j.castSucc) A)
    (treeMissingEq :
     ∀ (S : TreeSequence G e0),
      TreeSequenceInitialSegment S A → TreeMissingColors sigma S = TreeMissingColors phi S)
    (combined :
     ett.series.data.kind n = some TashkinovExtensionKind.PE →
      CombinedStableColoring Tn base.closure Dn phi sigma)
    (corrT : CorrespondingExtendedTashkinovTree G k e0 ett sigma T),
    MaximumProperty corrT.replacementETT →
     ∀ (baseT : HierarchyBase corrT.replacementETT sigma) (hcoreT : baseT.core = base.core)
      (hclosureT : baseT.closure = base.closure)
      (terminalData :
       corrT.replacementETT.series.data.tree (Fin.last corrT.replacementETT.rounds).castSucc = Tn ∧
        corrT.replacementETT.series.data.kind (Fin.last corrT.replacementETT.rounds) =
          ett.series.data.kind n ∧
         TashkinovStoredColors corrT.replacementETT.series.data
           (Fin.last corrT.replacementETT.rounds) =
          Dn),
      let K : TashkinovHierarchy corrT.replacementETT baseT :=
       {
        dividerCount := H.dividerCount, stage := H.stage,
        baseStage := Eq.trans H.baseStage (Eq.symm terminalData.left),
        terminalStage := H.terminalStage, nested := H.nested, strict := H.strict,
        dividerPosition := H.dividerPosition, dividerPositive := H.dividerPositive,
        dividerIncreasing := H.dividerIncreasing, dividerStage := H.dividerStage,
        coreInsideFirst :=
         Eq.mpr
          (id
           (congrArg
            (fun (_a : TreeSequence G e0) =>
             TreeSequenceInitialSegment _a
              (H.stage (⟨(1 : ℕ), by omega⟩ : Fin (H.dividerCount + (2 : ℕ)))))
            hcoreT))
          H.coreInsideFirst :
        TashkinovHierarchy corrT.replacementETT baseT };
      ∀
       (starredEq :
        ∀ (j : Fin (H.dividerCount + (1 : ℕ))),
         HierarchyStarredStage K j = HierarchyStarredStage H j)
       (storedEq :
        ∀ (j : Fin (H.dividerCount + (1 : ℕ))),
         HierarchyStoredColorsAt K j = HierarchyStoredColorsAt H j)
       (stageMissingEq :
        ∀ (j : Fin (H.dividerCount + (1 : ℕ))),
         HierarchyStageMissingColors K j = HierarchyStageMissingColors H j)
       (segmentEq :
        ∀ (j : Fin (H.dividerCount + (1 : ℕ))),
         ∀ eta ∈ HierarchyStoredColorsAt H j,
          HierarchySegmentColors K j eta = HierarchySegmentColors H j eta)
       (parallelNotClosed :
        ett.series.data.kind n = some TashkinovExtensionKind.PE →
         ¬TreeColorSetMinusClosed G sigma base.core
           ((HierarchyStoredColorsAt H (0 : Fin (H.dividerCount + (1 : ℕ)))).biUnion
            (C.good.gamma (0 : Fin (C.hierarchy.dividerCount + (1 : ℕ)))))),
       let goodT : GoodHierarchy K :=
        {
         gamma := C.good.gamma,
         twoColors :=
          fun (j : Fin (K.dividerCount + (1 : ℕ))) (eta : Fin k)
           (heta : eta ∈ HierarchyStoredColorsAt K j) =>
          C.good.twoColors j eta
           (Eq.mp (congrArg (fun (_a : Finset (Fin k)) => eta ∈ _a) (storedEq j)) heta),
         avoidance :=
          fun (j : Fin (K.dividerCount + (1 : ℕ))) (eta : Fin k)
           (heta : eta ∈ HierarchyStoredColorsAt K j) ⦃c : Fin k⦄ (hc : c ∈ C.good.gamma j eta) =>
          have ho : eta ∈ HierarchyStoredColorsAt H j :=
           Eq.mpr (id (congrArg (fun (_a : Finset (Fin k)) => eta ∈ _a) (Eq.symm (storedEq j))))
            heta;
          Eq.mpr
           (id
            (congrArg (fun (_a : Finset (Fin k)) => c ∈ _a \ HierarchySegmentColors K j eta)
             (stageMissingEq j)))
           (Eq.mpr
            (id
             (congrArg (fun (_a : Finset (Fin k)) => c ∈ HierarchyStageMissingColors H j \ _a)
              (segmentEq j eta ho)))
            (C.good.avoidance j eta ho hc)),
         disjointPairs :=
          fun (j : Fin (K.dividerCount + (1 : ℕ))) (eta theta : Fin k)
           (heta : eta ∈ HierarchyStoredColorsAt K j) (htheta : theta ∈ HierarchyStoredColorsAt K j)
           (hne : eta ≠ theta) =>
          C.good.disjointPairs j eta theta
           (Eq.mp (congrArg (fun (_a : Finset (Fin k)) => eta ∈ _a) (storedEq j)) heta)
           (Eq.mp (congrArg (fun (_a : Finset (Fin k)) => theta ∈ _a) (storedEq j)) htheta) hne,
         uniqueRefresh := fun (i : Fin K.dividerCount) =>
          have hnew :
           ((TreeSequenceVertexSet (H.stage i.succ.castSucc) \
               TreeSequenceVertexSet (HierarchyStarredStage H i.castSucc)).biUnion
             fun (v : V) => MissingColors G sigma v) =
            (TreeSequenceVertexSet (H.stage i.succ.castSucc) \
               TreeSequenceVertexSet (HierarchyStarredStage H i.castSucc)).biUnion
             fun (v : V) => MissingColors G phi v :=
           Finset.biUnion_congr rfl
            fun (v : V)
             (hv :
              v ∈
               TreeSequenceVertexSet (H.stage i.succ.castSucc) \
                TreeSequenceVertexSet (HierarchyStarredStage H i.castSucc)) =>
            missingA v
             (TreeSequenceInitialSegmentVertexSetSubset (ordinaryToA i.succ)
              (Finset.mem_sdiff.mp hv).left);
          id
           (Eq.mpr
            (id
             (congrArg
              (fun (_a : TreeSequence G e0) =>
               ∃! eta : Fin k,
                eta ∈ HierarchyStoredColorsAt K i.succ ∧
                 (C.good.gamma i.succ eta ⊆
                   (TreeSequenceVertexSet (H.stage i.succ.castSucc) \
                      TreeSequenceVertexSet _a).biUnion
                    fun (v : V) => MissingColors G sigma v) ∧
                  ∀ theta ∈ HierarchyStoredColorsAt K i.succ,
                   theta ≠ eta → C.good.gamma i.succ theta = C.good.gamma i.castSucc theta)
              (starredEq i.castSucc)))
            (Eq.mpr
             (id
              (congrArg
               (fun (_a : Finset (Fin k)) =>
                ∃! eta : Fin k,
                 eta ∈ HierarchyStoredColorsAt K i.succ ∧
                  C.good.gamma i.succ eta ⊆ _a ∧
                   ∀ theta ∈ HierarchyStoredColorsAt K i.succ,
                    theta ≠ eta → C.good.gamma i.succ theta = C.good.gamma i.castSucc theta)
               hnew))
             (Eq.mpr
              (id
               (congrArg ExistsUnique
                (funext fun (eta : Fin k) =>
                 congr
                  (congrArg And
                   (congrFun'
                    (congrArg Membership.mem
                     ((fun (j : Fin (H.dividerCount + (1 : ℕ))) => storedEq j) i.succ))
                    eta))
                  (congrArg
                   (And
                    (C.good.gamma i.succ eta ⊆
                     (TreeSequenceVertexSet (H.stage i.succ.castSucc) \
                        TreeSequenceVertexSet (HierarchyStarredStage H i.castSucc)).biUnion
                      fun (v : V) => MissingColors G phi v))
                   (forall_congr fun (theta : Fin k) =>
                    implies_congr
                     (congrFun'
                      (congrArg Membership.mem
                       ((fun (j : Fin (H.dividerCount + (1 : ℕ))) => storedEq j) i.succ))
                      theta)
                     (Eq.refl
                      (theta ≠ eta →
                       C.good.gamma i.succ theta = C.good.gamma i.castSucc theta)))))))
              (C.good.uniqueRefresh i)))),
         parallelBase :=
          id
           fun
            (hp :
             corrT.replacementETT.series.data.kind (Fin.last corrT.replacementETT.rounds) =
              some TashkinovExtensionKind.PE) =>
           have hpOld : ett.series.data.kind n = some TashkinovExtensionKind.PE :=
            Eq.trans (Eq.symm terminalData.right.left) hp;
           (⟨id
              (Eq.mpr
               (id
                (congrArg
                 (fun (_a : TreeSequence G e0) =>
                  ¬TreeColorSetMinusClosed G sigma _a
                    ((HierarchyStoredColorsAt K (0 : Fin (K.dividerCount + (1 : ℕ)))).biUnion
                     (C.good.gamma (0 : Fin (C.hierarchy.dividerCount + (1 : ℕ))))))
                 hcoreT))
               (Eq.mpr
                (id
                 (congrArg
                  (fun (_a : Finset (Fin k)) =>
                   ¬TreeColorSetMinusClosed G sigma base.core
                     (_a.biUnion (C.good.gamma (0 : Fin (C.hierarchy.dividerCount + (1 : ℕ))))))
                  (storedEq (0 : Fin (H.dividerCount + (1 : ℕ))))))
                (parallelNotClosed hpOld))),
             id
              (have closureMissing :
               TreeMissingColors sigma base.closure = TreeMissingColors phi base.closure :=
               id (Finset.biUnion_congr rfl (combined hpOld).right.right);
              Eq.mpr
               (id
                (congrArg
                 (fun (_a : TreeSequence G e0) =>
                  (4 : ℕ) ≤
                   ((TreeMissingColors sigma _a ∩ TreeMissingColors sigma baseT.closure) \
                     (HierarchyStoredColorsAt K (0 : Fin (K.dividerCount + (1 : ℕ)))).biUnion
                      (C.good.gamma (0 : Fin (C.hierarchy.dividerCount + (1 : ℕ))))).card)
                 terminalData.left))
               (Eq.mpr
                (id
                 (congrArg
                  (fun (_a : TreeSequence G e0) =>
                   (4 : ℕ) ≤
                    ((TreeMissingColors sigma Tn ∩ TreeMissingColors sigma _a) \
                      (HierarchyStoredColorsAt K (0 : Fin (K.dividerCount + (1 : ℕ)))).biUnion
                       (C.good.gamma (0 : Fin (C.hierarchy.dividerCount + (1 : ℕ))))).card)
                  hclosureT))
                (Eq.mpr
                 (id
                  (congrArg
                   (fun (_a : Finset (Fin k)) =>
                    (4 : ℕ) ≤
                     ((TreeMissingColors sigma Tn ∩ TreeMissingColors sigma base.closure) \
                       _a.biUnion
                        (C.good.gamma (0 : Fin (C.hierarchy.dividerCount + (1 : ℕ))))).card)
                   (storedEq (0 : Fin (H.dividerCount + (1 : ℕ))))))
                 (Eq.mpr
                  (id
                   (congrArg
                    (fun (_a : Finset (Fin k)) =>
                     (4 : ℕ) ≤
                      ((_a ∩ TreeMissingColors sigma base.closure) \
                        (HierarchyStoredColorsAt H (0 : Fin (H.dividerCount + (1 : ℕ)))).biUnion
                         (C.good.gamma (0 : Fin (C.hierarchy.dividerCount + (1 : ℕ))))).card)
                    (treeMissingEq Tn TnToA)))
                  (Eq.mpr
                   (id
                    (congrArg
                     (fun (_a : Finset (Fin k)) =>
                      (4 : ℕ) ≤
                       ((TreeMissingColors phi Tn ∩ _a) \
                         (HierarchyStoredColorsAt H (0 : Fin (H.dividerCount + (1 : ℕ)))).biUnion
                          (C.good.gamma (0 : Fin (C.hierarchy.dividerCount + (1 : ℕ))))).card)
                     closureMissing))
                   (C.good.parallelBase hpOld).right)))))⟩ :
            ¬TreeColorSetMinusClosed G sigma baseT.core
               ((HierarchyStoredColorsAt K (0 : Fin (K.dividerCount + (1 : ℕ)))).biUnion
                (C.good.gamma (0 : Fin (K.dividerCount + (1 : ℕ))))) ∧
             (4 : ℕ) ≤
              ((TreeMissingColors sigma
                  (corrT.replacementETT.series.data.tree
                   (Fin.last corrT.replacementETT.rounds).castSucc) ∩
                 TreeMissingColors sigma baseT.closure) \
                (HierarchyStoredColorsAt K (0 : Fin (K.dividerCount + (1 : ℕ)))).biUnion
                 (C.good.gamma (0 : Fin (K.dividerCount + (1 : ℕ))))).card),
         minusClosed := fun (i : Fin K.dividerCount) =>
          id
           (Eq.mpr
            (id
             (congrArg
              (fun (_a : Finset (Fin k)) =>
               TreeColorSetMinusClosed G sigma (H.stage i.succ.castSucc)
                (_a.biUnion (C.good.gamma i.castSucc)))
              (storedEq i.succ)))
            (P2813_T1_MinusClosedTransport G k e0 (C.hierarchy.stage i.succ.castSucc) phi sigma
             alpha beta hne z hsigma ctx.proper ctx.oneEdgeUncolored
             ((HierarchyStoredColorsAt C.hierarchy i.succ).biUnion (C.good.gamma i.castSucc))
             (C.good.minusClosed i)
             (fun (v : V) (hv : v ∈ TreeSequenceVertexSet (C.hierarchy.stage i.succ.castSucc)) =>
              missingA v (TreeSequenceInitialSegmentVertexSetSubset (ordinaryToA i.succ) hv))
             (outside i.succ))) :
         GoodHierarchy K };
       (0 : ℕ) < C.hierarchy.dividerCount →
        (1 : ℕ) ≤ (↑q : ℕ) →
         ∀ (U : TreeSequence G e0),
          U = H.stage q.castSucc →
           ∃ (inputA : PartialEdgeColoring E k) (ettA : ExtendedTashkinovTree G k e0 inputA U sigma)
            (baseA : HierarchyBase ettA sigma) (KA : TashkinovHierarchy ettA baseA) (goodA :
            GoodHierarchy KA),
            MaximumProperty ettA ∧
             ∃ (hcount : KA.dividerCount + (1 : ℕ) = H.dividerCount),
              baseA.core = base.core ∧
               baseA.closure = base.closure ∧
                (∀ (j : Fin (KA.dividerCount + (2 : ℕ))),
                  KA.stage j = H.stage (⟨(↑j : ℕ), by omega⟩ : Fin (H.dividerCount + (2 : ℕ)))) ∧
                 (∀ (j : Fin (KA.dividerCount + (1 : ℕ))),
                   let jH : Fin (H.dividerCount + (1 : ℕ)) :=
                    (⟨(↑j : ℕ), by omega⟩ : Fin (H.dividerCount + (1 : ℕ)));
                   HierarchyStoredColorsAt KA j = HierarchyStoredColorsAt H jH ∧
                    ∀ eta ∈ HierarchyStoredColorsAt KA j, goodA.gamma j eta = C.good.gamma jH eta) ∧
                  TreeColorSetMinusClosed G sigma
                   (H.stage (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + (2 : ℕ))))
                   ((HierarchyStoredColorsAt H q).biUnion
                    (C.good.gamma
                     (⟨H.dividerCount - (1 : ℕ),
                       Nat.lt_succ_of_le (Nat.sub_le H.dividerCount (1 : ℕ))⟩ :
                      Fin (C.hierarchy.dividerCount + (1 : ℕ)))))

private abbrev helperContinuation1171Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base),
   HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C →
    ∀ (alpha beta : Fin k),
     alpha ≠ beta →
      ∀ (z : V ⊕ E) (sigma : PartialEdgeColoring E k),
       sigma = TwoColorComponentSwap G phi alpha beta z →
        let H : TashkinovHierarchy ett base := C.hierarchy;
        let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
        let A : TreeSequence G e0 := HierarchyStarredStage H q;
        let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
        let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
        let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
        (2 : ℕ) ≤ T.length - A.length →
         (∀ (r : Fin (C.hierarchy.dividerCount + (1 : ℕ))) (c : Fin k),
           c = alpha ∨ c = beta →
            c ∈ TreeMissingColors phi (HierarchyStarredStage C.hierarchy r) →
             TreeColorSetClosed G phi (HierarchyStarredStage C.hierarchy r) { c } →
              OutsideKempeRecoloring (HierarchyStarredStage C.hierarchy r) phi sigma alpha beta) →
          ModColoring ett sigma →
           (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) =
              ett.series.data.tree (Fin.last ett.rounds).castSucc ∨
             ∃ (corr :
              CorrespondingExtendedTashkinovTree G k e0 ett sigma
               (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount))),
              MaximumProperty corr.replacementETT) →
            (∀ v ∈ TreeSequenceVertexSet A, MissingColors G sigma v = MissingColors G phi v) →
             (∀ {S U W : TreeSequence G e0},
               TreeSequenceInitialSegment S U →
                TreeSequenceInitialSegment U W → TreeSequenceInitialSegment S W) →
              (∀ {S U W : TreeSequence G e0},
                TreeSequenceInitialSegment S W →
                 TreeSequenceInitialSegment U W →
                  S.length ≤ U.length → TreeSequenceInitialSegment S U) →
               (∀ {S U : TreeSequence G e0},
                 TreeSequenceInitialSegment S U → S.length = U.length → S = U) →
                (∀ (j : Fin (H.dividerCount + (2 : ℕ))), TreeSequenceInitialSegment (H.stage j) T) →
                 (H.dividerCount = (0 : ℕ) → A = base.core) →
                  (H.dividerCount ≠ (0 : ℕ) → A = H.stage q.castSucc) →
                   TreeSequenceInitialSegment base.core A →
                    TreeSequenceInitialSegment Tn base.core →
                     TreeSequenceInitialSegment Tn A →
                      TreeSequenceInitialSegment A T →
                       (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
                         TreeSequenceInitialSegment (H.stage j.castSucc) A) →
                        (∀ (t : Fin T.length), sigma (T.edge t) = phi (T.edge t)) →
                         HierarchyWeaklyStable H q sigma →
                          (∀ (S : TreeSequence G e0),
                            TreeSequenceInitialSegment S A →
                             TreeMissingColors sigma S = TreeMissingColors phi S) →
                           (ett.series.data.kind n = some TashkinovExtensionKind.PE →
                             CombinedStableColoring Tn base.closure Dn phi sigma) →
                            ∀ (corrT : CorrespondingExtendedTashkinovTree G k e0 ett sigma T),
                             MaximumProperty corrT.replacementETT →
                              ∀ (baseT : HierarchyBase corrT.replacementETT sigma)
                               (hcoreT : baseT.core = base.core),
                               baseT.closure = base.closure →
                                ∀
                                 (terminalData :
                                  corrT.replacementETT.series.data.tree
                                     (Fin.last corrT.replacementETT.rounds).castSucc =
                                    Tn ∧
                                   corrT.replacementETT.series.data.kind
                                      (Fin.last corrT.replacementETT.rounds) =
                                     ett.series.data.kind n ∧
                                    TashkinovStoredColors corrT.replacementETT.series.data
                                      (Fin.last corrT.replacementETT.rounds) =
                                     Dn),
                                 let K : TashkinovHierarchy corrT.replacementETT baseT :=
                                  {
                                   dividerCount := H.dividerCount, stage := H.stage,
                                   baseStage := Eq.trans H.baseStage (Eq.symm terminalData.left),
                                   terminalStage := H.terminalStage, nested := H.nested,
                                   strict := H.strict, dividerPosition := H.dividerPosition,
                                   dividerPositive := H.dividerPositive,
                                   dividerIncreasing := H.dividerIncreasing,
                                   dividerStage := H.dividerStage,
                                   coreInsideFirst :=
                                    Eq.mpr
                                     (id
                                      (congrArg
                                       (fun (_a : TreeSequence G e0) ↦
                                        TreeSequenceInitialSegment _a
                                         (H.stage
                                          (⟨(1 : ℕ), by omega⟩ : Fin (H.dividerCount + (2 : ℕ)))))
                                       hcoreT))
                                     H.coreInsideFirst :
                                   TashkinovHierarchy corrT.replacementETT baseT };
                                 (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
                                   HierarchyStarredStage K j = HierarchyStarredStage H j) →
                                  (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
                                    HierarchyStoredColorsAt K j = HierarchyStoredColorsAt H j) →
                                   (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
                                     HierarchyStageMissingColors K j =
                                      HierarchyStageMissingColors H j) →
                                    (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
                                      ∀ eta ∈ HierarchyStoredColorsAt H j,
                                       HierarchySegmentColors K j eta =
                                        HierarchySegmentColors H j eta) →
                                     let H : TashkinovHierarchy ett base := C.hierarchy;
                                     let q : Fin (H.dividerCount + (1 : ℕ)) :=
                                      Fin.last H.dividerCount;
                                     let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
                                     let A : TreeSequence G e0 := HierarchyStarredStage H q;
                                     let Tnq : TreeSequence G e0 :=
                                      H.stage
                                       (⟨H.dividerCount, by omega⟩ :
                                        Fin (H.dividerCount + (2 : ℕ)));
                                     let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
                                     let Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q;
                                     HierarchyWeaklyStable H q sigma ∧
                                      ModColoring ett sigma ∧
                                       (A = Tn ∨
                                         ∃ (inputA : PartialEdgeColoring E k) (ettA :
                                          ExtendedTashkinovTree G k e0 inputA A sigma),
                                          MaximumProperty ettA) ∧
                                        ((0 : ℕ) < H.dividerCount →
                                          ∃ (inputA : PartialEdgeColoring E k) (ettA :
                                           ExtendedTashkinovTree G k e0 inputA A sigma) (baseA :
                                           HierarchyBase ettA sigma) (K :
                                           TashkinovHierarchy ettA baseA) (goodA : GoodHierarchy K),
                                           MaximumProperty ettA ∧
                                            ∃ (hcount : K.dividerCount + (1 : ℕ) = H.dividerCount),
                                             baseA.core = base.core ∧
                                              baseA.closure = base.closure ∧
                                               (∀ (j : Fin (K.dividerCount + (2 : ℕ))),
                                                 K.stage j =
                                                  H.stage
                                                   (⟨(↑j : ℕ), by omega⟩ :
                                                    Fin (H.dividerCount + (2 : ℕ)))) ∧
                                                (∀ (j : Fin (K.dividerCount + (1 : ℕ))),
                                                  let jH : Fin (H.dividerCount + (1 : ℕ)) :=
                                                   (⟨(↑j : ℕ), by omega⟩ :
                                                    Fin (H.dividerCount + (1 : ℕ)));
                                                  HierarchyStoredColorsAt K j =
                                                    HierarchyStoredColorsAt H jH ∧
                                                   ∀ eta ∈ HierarchyStoredColorsAt K j,
                                                    goodA.gamma j eta = C.good.gamma jH eta) ∧
                                                 TreeColorSetMinusClosed G sigma Tnq
                                                  (Dnq.biUnion
                                                   (C.good.gamma
                                                    (⟨C.hierarchy.dividerCount - (1 : ℕ), by
                                                      omega⟩ :
                                                     Fin (C.hierarchy.dividerCount + (1 : ℕ)))))) ∧
                                         ∃ (corrT :
                                          CorrespondingExtendedTashkinovTree G k e0 ett sigma T),
                                          MaximumProperty corrT.replacementETT ∧
                                           ∃ (baseT : HierarchyBase corrT.replacementETT sigma) (K :
                                            TashkinovHierarchy corrT.replacementETT baseT) (goodT :
                                            GoodHierarchy K), SameGoodHierarchy C.good goodT

private abbrev helperContinuation1123Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base),
   HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C →
    ∀ (alpha beta : Fin k),
     alpha ≠ beta →
      ∀ (z : V ⊕ E) (sigma : PartialEdgeColoring E k),
       sigma = TwoColorComponentSwap G phi alpha beta z →
        (∀
          v ∈
           TreeSequenceVertexSet (HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ))),
          MissingColors G sigma v = MissingColors G phi v) →
         (let H : TashkinovHierarchy ett base := C.hierarchy;
          let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
          ∀ eta ∈ HierarchyStoredColorsAt H q,
           HierarchyFirstMissingPosition sigma T eta = HierarchyFirstMissingPosition phi T eta) →
          let H : TashkinovHierarchy ett base := C.hierarchy;
          let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
          let A : TreeSequence G e0 := HierarchyStarredStage H q;
          let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
          let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
          let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
          let B : TreeSequence G e0 :=
           HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
          (2 : ℕ) ≤ T.length - A.length →
           (if ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE then
             CombinedStableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
              base.closure (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) phi sigma
            else
             StableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
              (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) phi sigma) →
            IsProperEdgeColoring G sigma →
             IsOneEdgeUncolored sigma e0 →
              (∀ (r : Fin (C.hierarchy.dividerCount + (1 : ℕ))) (c : Fin k),
                c = alpha ∨ c = beta →
                 c ∈ TreeMissingColors phi (HierarchyStarredStage C.hierarchy r) →
                  TreeColorSetClosed G phi (HierarchyStarredStage C.hierarchy r) { c } →
                   OutsideKempeRecoloring (HierarchyStarredStage C.hierarchy r) phi sigma alpha
                    beta) →
               ModColoring ett sigma →
                (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) =
                   ett.series.data.tree (Fin.last ett.rounds).castSucc ∨
                  ∃ (corr :
                   CorrespondingExtendedTashkinovTree G k e0 ett sigma
                    (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount))),
                   MaximumProperty corr.replacementETT) →
                 (∀ (t : Fin A.length), sigma (A.edge t) = phi (A.edge t)) →
                  (∀ v ∈ TreeSequenceVertexSet A, MissingColors G sigma v = MissingColors G phi v) →
                   (∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → sigma (T.edge t) = phi (T.edge t)) →
                    (∀ {S U W : TreeSequence G e0},
                      TreeSequenceInitialSegment S U →
                       TreeSequenceInitialSegment U W → TreeSequenceInitialSegment S W) →
                     (∀ {S U W : TreeSequence G e0},
                       TreeSequenceInitialSegment S W →
                        TreeSequenceInitialSegment U W →
                         S.length ≤ U.length → TreeSequenceInitialSegment S U) →
                      (∀ {S U : TreeSequence G e0},
                        TreeSequenceInitialSegment S U → S.length = U.length → S = U) →
                       (∀ (a d : ℕ) (hbound : a + d ≤ H.dividerCount + (1 : ℕ)),
                         TreeSequenceInitialSegment
                          (H.stage (⟨a, by omega⟩ : Fin (H.dividerCount + (2 : ℕ))))
                          (H.stage (⟨a + d, by omega⟩ : Fin (H.dividerCount + (2 : ℕ))))) →
                        (∀ (j : Fin (H.dividerCount + (2 : ℕ))),
                          TreeSequenceInitialSegment (H.stage j) T) →
                         (H.dividerCount = (0 : ℕ) → A = base.core) →
                          (H.dividerCount ≠ (0 : ℕ) → A = H.stage q.castSucc) →
                           TreeSequenceInitialSegment base.core A →
                            TreeSequenceInitialSegment Tn base.core →
                             TreeSequenceInitialSegment Tn A →
                              TreeSequenceInitialSegment A T →
                               let H : TashkinovHierarchy ett base := C.hierarchy;
                               let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
                               let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
                               let A : TreeSequence G e0 := HierarchyStarredStage H q;
                               let Tnq : TreeSequence G e0 :=
                                H.stage
                                 (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + (2 : ℕ)));
                               let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
                               let Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q;
                               HierarchyWeaklyStable H q sigma ∧
                                ModColoring ett sigma ∧
                                 (A = Tn ∨
                                   ∃ (inputA : PartialEdgeColoring E k) (ettA :
                                    ExtendedTashkinovTree G k e0 inputA A sigma),
                                    MaximumProperty ettA) ∧
                                  ((0 : ℕ) < H.dividerCount →
                                    ∃ (inputA : PartialEdgeColoring E k) (ettA :
                                     ExtendedTashkinovTree G k e0 inputA A sigma) (baseA :
                                     HierarchyBase ettA sigma) (K : TashkinovHierarchy ettA baseA)
                                     (goodA : GoodHierarchy K),
                                     MaximumProperty ettA ∧
                                      ∃ (hcount : K.dividerCount + (1 : ℕ) = H.dividerCount),
                                       baseA.core = base.core ∧
                                        baseA.closure = base.closure ∧
                                         (∀ (j : Fin (K.dividerCount + (2 : ℕ))),
                                           K.stage j =
                                            H.stage
                                             (⟨(↑j : ℕ), by omega⟩ :
                                              Fin (H.dividerCount + (2 : ℕ)))) ∧
                                          (∀ (j : Fin (K.dividerCount + (1 : ℕ))),
                                            let jH : Fin (H.dividerCount + (1 : ℕ)) :=
                                             (⟨(↑j : ℕ), by omega⟩ :
                                              Fin (H.dividerCount + (1 : ℕ)));
                                            HierarchyStoredColorsAt K j =
                                              HierarchyStoredColorsAt H jH ∧
                                             ∀ eta ∈ HierarchyStoredColorsAt K j,
                                              goodA.gamma j eta = C.good.gamma jH eta) ∧
                                           TreeColorSetMinusClosed G sigma Tnq
                                            (Dnq.biUnion
                                             (C.good.gamma
                                              (⟨C.hierarchy.dividerCount - (1 : ℕ), by omega⟩ :
                                               Fin (C.hierarchy.dividerCount + (1 : ℕ)))))) ∧
                                   ∃ (corrT :
                                    CorrespondingExtendedTashkinovTree G k e0 ett sigma T),
                                    MaximumProperty corrT.replacementETT ∧
                                     ∃ (baseT : HierarchyBase corrT.replacementETT sigma) (K :
                                      TashkinovHierarchy corrT.replacementETT baseT) (goodT :
                                      GoodHierarchy K), SameGoodHierarchy C.good goodT

private theorem helper_corrData_383.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base) (sigma : PartialEdgeColoring E k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    TreeSequenceInitialSegment Tn A →
    (∀ (S : TreeSequence G e0),
        TreeSequenceInitialSegment S A →
          TreeMissingColors sigma S = TreeMissingColors phi S) →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma T),
    corr.replacementETT.series.data.tree (Fin.last corr.replacementETT.rounds).castSucc =
        Tn ∧
      corr.replacementETT.series.data.kind (Fin.last corr.replacementETT.rounds) =
          ett.series.data.kind n ∧
        TashkinovStoredColors corr.replacementETT.series.data
            (Fin.last corr.replacementETT.rounds) =
          Dn := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C sigma H q A n Tn Dn TnToA treeMissingEq corr
  rcases corr with ⟨replacementInput, replacementSeries, replacementETT,
    rungAgreement, seriesPresentation, finalGeneratingColoring,
    ladderTreesAgree, storedColorsAgree, connectingEdgesAgree,
    extensionKindsAgree, replacementProper, replacementOneUncolored,
    replacementStable⟩
  cases replacementETT with
  | mk rounds roundsPositive replacementData above strict below generating =>
    cases rungAgreement
    have hs : replacementData = replacementSeries := eq_of_heq seriesPresentation
    cases hs
    let a : Fin ett.rounds := ⟨ett.rounds - 1, by have := ett.roundsPositive; omega⟩
    have ha : a.succ = Fin.last ett.rounds := by
      apply Fin.ext
      change ett.rounds - 1 + 1 = ett.rounds
      have := ett.roundsPositive
      omega
    have ht : replacementSeries.data.tree (Fin.last ett.rounds).castSucc = Tn := by
      change replacementSeries.data.tree (Fin.last ett.rounds).castSucc =
        ett.series.data.tree (Fin.last ett.rounds).castSucc
      rw [← ha]
      exact ladderTreesAgree a
    have hm : TreeMissingColors (replacementSeries.data.coloring (Fin.last ett.rounds))
        (replacementSeries.data.tree (Fin.last ett.rounds).castSucc) = TreeMissingColors phi Tn
           := by
      rw [← finalGeneratingColoring, ht]
      exact treeMissingEq Tn TnToA
    have hmOld : TreeMissingColors (ett.series.data.coloring (Fin.last ett.rounds))
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) = TreeMissingColors phi Tn := by
      rw [← ett.generatingColoring]
    refine ⟨ht, extensionKindsAgree (Fin.last ett.rounds), ?_⟩
    change TashkinovStoredColors replacementSeries.data (Fin.last ett.rounds) =
      TashkinovStoredColors ett.series.data (Fin.last ett.rounds)
    simp only [TashkinovStoredColors, storedColorsAgree, hm, hmOld]

private theorem helper_fullBase_422.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base),
    HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C →
    ∀ (sigma : PartialEdgeColoring E k),
    let _ : TashkinovHierarchy ett base := C.hierarchy;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    IsProperEdgeColoring G sigma →
    IsOneEdgeUncolored sigma e0 →
    ModColoring ett sigma →
    (ett.series.data.kind n = some TashkinovExtensionKind.PE →
        CombinedStableColoring Tn base.closure Dn phi sigma) →
    (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
          TashkinovAugmentationSequence sigma Tn T ∨
        (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
            ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
          ∃ (f : E) (seed : TreeSequence G e0),
            ett.series.data.connectingEdges n = { f } ∧
              TreeSequenceAdjoinEdge Tn f seed ∧
                TashkinovAugmentationSequence sigma seed T) →
    (∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma T),
        corr.replacementETT.series.data.tree
              (Fin.last corr.replacementETT.rounds).castSucc =
            Tn ∧
          corr.replacementETT.series.data.kind (Fin.last corr.replacementETT.rounds) =
              ett.series.data.kind n ∧
            TashkinovStoredColors corr.replacementETT.series.data
                (Fin.last corr.replacementETT.rounds) =
              Dn) →
    ∃ (corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma T),
    MaximumProperty corr.replacementETT ∧
      ∃ (baseT : HierarchyBase corr.replacementETT sigma),
        baseT.core = base.core ∧ baseT.closure = base.closure := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx sigma H n Tn Dn sigmaProper sigmaOne hmod
      combined sigmaRoute corrData
  by_cases hp : ett.series.data.kind n = some TashkinovExtensionKind.PE
  · have hb : TashkinovAugmentationSequence sigma Tn T := by
      rcases sigmaRoute with ⟨_, hseq⟩ | ⟨hk, rest⟩
      · exact hseq
      · rcases hk with hk | hk <;> rw [hp] at hk <;> cases hk
    obtain ⟨corr, hMP, baseT, K0, hsame⟩ := HierarchySplitter G k e0 input T phi sigma
      ett C.maximum C.positive ctx.lowerRung base H hp ctx.proper ctx.oneEdgeUncolored
      sigmaProper sigmaOne (combined hp) hb
    exact ⟨corr, hMP, baseT, hsame.1.symm, (hsame.2.2.2.2.2 hp).symm⟩
  · obtain ⟨corr⟩ := hmod.2.2 T ett.abovePenultimate ett.strictAbovePenultimate sigmaRoute
    have hd := corrData corr
    let pos : Fin ((corr.replacementETT.series.data.tree
        (Fin.last corr.replacementETT.rounds).castSucc).length + 1) :=
      Fin.cast (congrArg (fun W : TreeSequence G e0 => W.length + 1) hd.1.symm)
        base.supportPosition
    let baseT : HierarchyBase corr.replacementETT sigma := {
      core := base.core
      closure := base.closure
      supportPosition := pos
      supportPositive := by simpa [pos] using base.supportPositive
      terminalMissingColors := rfl
      parallel := by
        dsimp only
        intro hPE
        exact False.elim (hp (hd.2.1.symm.trans hPE))
      nonparallel := by
        dsimp only
        intro _
        exact (base.nonparallel hp).trans hd.1.symm }
    exact ⟨corr, MaximumPropertyTransport G k e0 ett sigma hmod T corr C.maximum,
      baseT, rfl, rfl⟩

private theorem helper_segmentEq_489.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (sigma : PartialEdgeColoring E k),
    (let H : TashkinovHierarchy ett base := C.hierarchy;
      let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
      ∀ eta ∈ HierarchyStoredColorsAt H q,
        HierarchyFirstMissingPosition sigma T eta =
          HierarchyFirstMissingPosition phi T eta) →
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    (∀ (t : Fin A.length), sigma (A.edge t) = phi (A.edge t)) →
    (∀ v ∈ TreeSequenceVertexSet A, MissingColors G sigma v = MissingColors G phi v) →
    (∀ (j : Fin (H.dividerCount + (2 : ℕ))), TreeSequenceInitialSegment (H.stage j) T) →
    TreeSequenceInitialSegment A T →
    (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
        TreeSequenceInitialSegment (H.stage j.castSucc) A) →
    (∀ (t : Fin T.length), sigma (T.edge t) = phi (T.edge t)) →
    ∀ (corrT : CorrespondingExtendedTashkinovTree G k e0 ett sigma T)
      (baseT : HierarchyBase corrT.replacementETT sigma) (hcoreT : baseT.core = base.core)
      (terminalData :
        corrT.replacementETT.series.data.tree
              (Fin.last corrT.replacementETT.rounds).castSucc =
            Tn ∧
          corrT.replacementETT.series.data.kind (Fin.last corrT.replacementETT.rounds) =
              ett.series.data.kind n ∧
            TashkinovStoredColors corrT.replacementETT.series.data
                (Fin.last corrT.replacementETT.rounds) =
              Dn),
    let K : TashkinovHierarchy corrT.replacementETT baseT :=
      { dividerCount := H.dividerCount, stage := H.stage,
        baseStage := Eq.trans H.baseStage (Eq.symm terminalData.left),
        terminalStage := H.terminalStage, nested := H.nested, strict := H.strict,
        dividerPosition := H.dividerPosition, dividerPositive := H.dividerPositive,
        dividerIncreasing := H.dividerIncreasing, dividerStage := H.dividerStage,
        coreInsideFirst :=
          Eq.mpr
            (id
              (congrArg
                (fun (_a : TreeSequence G e0) =>
                  TreeSequenceInitialSegment _a
                    (H.stage (⟨(1 : ℕ), by omega⟩ : Fin (H.dividerCount + (2 : ℕ)))))
                hcoreT))
            H.coreInsideFirst :
        TashkinovHierarchy corrT.replacementETT baseT };
    (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
        HierarchyStarredStage K j = HierarchyStarredStage H j) →
    ∀ (j : Fin (H.dividerCount + (1 : ℕ))),
    ∀ eta ∈ HierarchyStoredColorsAt H j,
    HierarchySegmentColors K j eta = HierarchySegmentColors H j eta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C sigma hstoredFirst H q A n Tn Dn fixedA
      missingA stageToT AToT ordinaryToA fixedT corrT baseT hcoreT terminalData K starredEq j eta
      heta
  by_cases hj : j.val < H.dividerCount
  · have hjA : TreeSequenceInitialSegment (H.stage j.succ) A := by
      let js : Fin (H.dividerCount + 1) := ⟨j.val + 1, by omega⟩
      have he : js.castSucc = j.succ := Fin.ext rfl
      simpa only [he] using ordinaryToA js
    have hcut := HierarchyFirstMissingPositionPrefixCutoff sigma A T AToT eta
      (H.stage j.succ).length hjA.1
    have hseg := P2813_T1_PrefixSegmentTransport phi sigma (H.stage j.succ) A T
      hjA AToT fixedA missingA eta (HierarchyStarredStage H j).length
    unfold HierarchySegmentColors
    dsimp only
    rw [starredEq j, ← hcut]
    exact hseg
  · have he : j = q := Fin.ext (by simp [q]; have := j.isLt; omega)
    subst j
    unfold HierarchySegmentColors
    dsimp only
    rw [starredEq q, hstoredFirst eta heta]
    apply Finset.filter_congr
    intro c _
    constructor <;> rintro ⟨t, hlo, hhi, hc⟩ <;> refine ⟨t, hlo, hhi, ?_⟩
    · change sigma ((H.stage q.succ).edge t) = some c at hc
      have hf : sigma ((H.stage q.succ).edge t) = phi ((H.stage q.succ).edge t) := by
        rw [← (stageToT q.succ).2.2 t]
        exact fixedT _
      exact hf.symm.trans hc
    · have hf : sigma ((H.stage q.succ).edge t) = phi ((H.stage q.succ).edge t) := by
        rw [← (stageToT q.succ).2.2 t]
        exact fixedT _
      exact hf.trans hc

private theorem helper_parallelNotClosed_549.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (sigma : PartialEdgeColoring E k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    (∀ {S U W : TreeSequence G e0},
        TreeSequenceInitialSegment S U →
          TreeSequenceInitialSegment U W → TreeSequenceInitialSegment S W) →
    (∀ {S U W : TreeSequence G e0},
        TreeSequenceInitialSegment S W →
          TreeSequenceInitialSegment U W →
            S.length ≤ U.length → TreeSequenceInitialSegment S U) →
    (∀ {S U : TreeSequence G e0},
        TreeSequenceInitialSegment S U → S.length = U.length → S = U) →
    (∀ (j : Fin (H.dividerCount + (2 : ℕ))), TreeSequenceInitialSegment (H.stage j) T) →
    TreeSequenceInitialSegment base.core A →
    TreeSequenceInitialSegment Tn base.core →
    TreeSequenceInitialSegment A T →
    (∀ (t : Fin T.length), sigma (T.edge t) = phi (T.edge t)) →
    (∀ (S : TreeSequence G e0),
        TreeSequenceInitialSegment S A →
          TreeMissingColors sigma S = TreeMissingColors phi S) →
    base.core.length <
        (H.stage (⟨(1 : ℕ), by omega⟩ : Fin (H.dividerCount + (2 : ℕ)))).length →
    ett.series.data.kind n = some TashkinovExtensionKind.PE →
    ¬TreeColorSetMinusClosed G sigma base.core
        ((HierarchyStoredColorsAt H (0 : Fin (H.dividerCount + (1 : ℕ)))).biUnion
          (C.good.gamma (0 : Fin (C.hierarchy.dividerCount + (1 : ℕ))))) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C sigma H q A n Tn segTrans commonPrefix
      equalTrees stageToT coreToA TnToCore AToT fixedT treeMissingEq coreStrict hp
  have hseq : TashkinovAugmentationSequence phi Tn T := by
    rcases P2813_T1_TerminalRoute G k e0 input T phi ett with
      ⟨_, hseq⟩ | ⟨hk, rest⟩
    · exact hseq
    · rcases hk with hk | hk <;> rw [hp] at hk <;> cases hk
  have coreToT := segTrans coreToA AToT
  have suffix := TashkinovAugmentationSequenceSuffix phi Tn base.core T
    hseq TnToCore coreToT
  let t : Fin T.length := ⟨base.core.length, by
    have := (stageToT ⟨1, by omega⟩).1
    omega⟩
  let S := TreeSequencePrefix T t.val base.core.positive (Nat.le_of_lt t.isLt)
  let U := TreeSequencePrefix T (t.val + 1) (by have := base.core.positive; omega)
    (Nat.succ_le_of_lt t.isLt)
  have hS : S = base.core := by
    apply (equalTrees (commonPrefix coreToT
      (show TreeSequenceInitialSegment S T from
        ⟨Nat.le_of_lt t.isLt, fun _ => rfl, fun _ => rfl⟩) le_rfl) rfl).symm
  have aug := (TashkinovAugmentationSequencePosition phi base.core T suffix t le_rfl).1
  change TashkinovAugmentation phi S U at aug
  obtain ⟨hlen, hSU, c, hcol, hcm⟩ := aug
  have hcolT : phi (T.edge t) = some c := by
    have he : U.edge (Fin.cast hlen.symm (Fin.last S.length)) = T.edge t := by
      change T.edge _ = T.edge t
      apply congrArg T.edge
      apply Fin.ext
      rfl
    rw [← he]
    exact hcol
  have hcmCore : c ∈ TreeMissingColors phi base.core := hS ▸ hcm
  have hcSigma : c ∈ TreeMissingColors sigma base.core := by
    rw [treeMissingEq base.core coreToA]; exact hcmCore
  have hreserved : c ∉ (HierarchyStoredColorsAt H 0).biUnion (C.good.gamma 0) := by
    intro hc
    obtain ⟨eta, heta, hcg⟩ := Finset.mem_biUnion.mp hc
    have hn : eta ∉ TreeMissingColors phi base.core := (Finset.mem_sdiff.mp heta).2
    have hfirst : base.core.length < (HierarchyFirstMissingPosition phi T eta).val := by
      let candidates := Finset.univ.filter fun j : Fin (T.length + 1) =>
        eta ∈ MissingColors G phi (T.vertex j)
      unfold HierarchyFirstMissingPosition
      change base.core.length < (if h : candidates.Nonempty then candidates.min' h
        else Fin.last T.length).val
      split
      · rename_i hnon
        by_contra hh
        have hle : (candidates.min' hnon).val ≤ base.core.length := by omega
        let j : Fin (base.core.length + 1) := ⟨(candidates.min' hnon).val, by omega⟩
        have he : Fin.castLE (Nat.succ_le_succ coreToT.1) j = candidates.min' hnon := Fin.ext rfl
        have hm := (Finset.mem_filter.mp (Finset.min'_mem candidates hnon)).2
        apply hn
        refine Finset.mem_biUnion.mpr ⟨base.core.vertex j, ?_, ?_⟩
        · simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
          exact ⟨j, rfl⟩
        · rw [← coreToT.2.1 j, he]; exact hm
      · exact t.isLt
    have hseg : c ∈ HierarchySegmentColors H 0 eta := by
      let r : Fin (H.stage (0 : Fin (H.dividerCount + 1)).succ).length :=
        ⟨base.core.length, coreStrict⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, r, le_rfl, Nat.lt_min.mpr ⟨hfirst, coreStrict⟩, ?_⟩
      have he : Fin.castLE (stageToT (0 : Fin (H.dividerCount + 1)).succ).1 r = t := Fin.ext rfl
      rw [← (stageToT (0 : Fin (H.dividerCount + 1)).succ).2.2 r, he]
      exact hcolT
    exact (Finset.mem_sdiff.mp (C.good.avoidance 0 eta heta hcg)).2 hseg
  have hboundary : T.edge t ∈ BoundaryEdges G (TreeSequenceVertexSet base.core) := by
    clear * - T t base coreToT
    obtain ⟨i, hi⟩ := T.attaches t
    let old : Fin (base.core.length + 1) := ⟨i.val, i.isLt⟩
    let it : Fin (T.length + 1) := Fin.castLE (Nat.succ_le_succ coreToT.1) old
    have hOld : T.vertex it = base.core.vertex old := coreToT.2.1 old
    have hNew : T.vertex t.succ ∉ TreeSequenceVertexSet base.core := by
      intro hv
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hv
      obtain ⟨j, hj⟩ := hv
      have he := T.vertex_injective (hj.symm.trans (coreToT.2.1 j).symm)
      have hval := congrArg Fin.val he
      have := j.isLt
      change base.core.length + 1 = j.val at hval
      omega
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨T.vertex it, ?_, T.vertex t.succ, hNew, ?_⟩
    · rw [hOld]
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨old, rfl⟩
    · have he : Fin.castLT i (Nat.lt_trans i.isLt (Nat.succ_lt_succ t.isLt)) = it := Fin.ext rfl
      rw [hi, he]
      exact Sym2.eq_swap
  intro hclosed
  have hf : T.edge t ∈ BoundaryColorEdges G sigma (TreeSequenceVertexSet base.core) c :=
    Finset.mem_filter.mpr ⟨hboundary, (fixedT t).trans hcolT⟩
  rw [hclosed c (Finset.mem_sdiff.mpr ⟨hcSigma, hreserved⟩)] at hf
  exact Finset.notMem_empty _ hf

private theorem helper_coreStrict_772.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    (2 : ℕ) ≤ T.length - A.length →
    (∀ {S U : TreeSequence G e0},
        TreeSequenceInitialSegment S U → S.length = U.length → S = U) →
    (H.dividerCount = (0 : ℕ) → A = base.core) →
    base.core.length <
      (H.stage (⟨(1 : ℕ), by omega⟩ : Fin (H.dividerCount + (2 : ℕ)))).length := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q A htwo equalTrees lastZero
  by_cases hz : H.dividerCount = 0
  · have he : (⟨1, by omega⟩ : Fin (H.dividerCount + 2)) =
        Fin.last (H.dividerCount + 1) := Fin.ext (by simp [hz])
    rw [he, H.terminalStage]
    change 2 ≤ T.length - A.length at htwo
    rw [lastZero hz] at htwo
    omega
  · by_contra hnot
    have hlen : base.core.length = (H.stage ⟨1, by omega⟩).length := by
      have := H.coreInsideFirst.1
      omega
    have he := equalTrees H.coreInsideFirst hlen
    let i : Fin H.dividerCount := ⟨0, by omega⟩
    obtain ⟨eta, ⟨heta, hgamma, _⟩, _⟩ := C.good.uniqueRefresh i
    have hstage : H.stage i.succ.castSucc = base.core := by
      exact he.symm
    have hstar : HierarchyStarredStage H i.castSucc = base.core := rfl
    rw [hstage, hstar, Finset.sdiff_self, Finset.biUnion_empty] at hgamma
    have hempty : C.good.gamma i.succ eta = ∅ := Finset.subset_empty.mp hgamma
    have hcard := C.good.twoColors i.succ eta heta
    rw [hempty, Finset.card_empty] at hcard
    omega

private theorem helper_positivePackage_887.{u_1, u_2} :
    helperPositivePackage887Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx alpha beta hne z sigma hsigma H q A n Tn Dn
      outside missingA TnToA ordinaryToA treeMissingEq combined corrT hmaximumT baseT hcoreT
      hclosureT terminalData K starredEq storedEq stageMissingEq segmentEq parallelNotClosed
      goodT hq hqK U hU
  subst U
  obtain ⟨ettA, hMPA, hrA, hsA, baseA, hcoreA, hclosureA, hsupportA,
      KA, hcount, hstages, hdividers, goodA, hgammaA, hminusA⟩ :=
    GoodHierarchyPrefixRepackage G k e0 corrT.replacementInput T sigma sigma
      corrT.replacementETT hmaximumT baseT K goodT q hqK
  refine ⟨corrT.replacementInput, ettA, baseA, KA, goodA, hMPA, ?_⟩
  have hcount' : KA.dividerCount + 1 = H.dividerCount := by
    change KA.dividerCount = H.dividerCount - 1 at hcount
    change 0 < H.dividerCount at hq
    omega
  refine ⟨hcount', hcoreA.trans hcoreT, hclosureA.trans hclosureT, ?_, ?_, ?_⟩
  · intro j
    let jp : Fin (q.val + 1) := ⟨j.val, by dsimp [q]; have := j.isLt; omega⟩
    have he : Fin.cast (by omega) jp = j := Fin.ext rfl
    simpa only [he] using hstages jp
  · intro j
    let jp : Fin q.val := ⟨j.val, by dsimp [q]; have := j.isLt; omega⟩
    have he : Fin.cast (by omega) jp = j := Fin.ext rfl
    have hg := hgammaA jp
    simp only [he] at hg
    refine ⟨hg.1.trans (storedEq _), ?_⟩
    intro eta heta
    exact hg.2 eta
  · have he : (Fin.last H.dividerCount).castSucc =
        (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + 2)) := Fin.ext rfl
    simpa [K, goodT, storedEq, q, he] using hminusA

private theorem helper_preStepElementary_896.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C →
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let i : Fin ett.rounds :=
      (⟨ett.rounds - (1 : ℕ), by have this : (0 : ℕ) < ett.rounds := C.positive; omega⟩ :
        Fin ett.rounds);
    ColoredVertexSetElementary G (ett.series.data.coloring i.castSucc)
      (TreeSequenceVertexSet Tn) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx n Tn
  dsimp only
  by_cases hn : ett.rounds = 1
  · have hcolor : (⟨ett.rounds - 1, by have := C.positive; omega⟩ : Fin ett.rounds).castSucc = 0 :=
      Fin.ext (by simp [hn])
    have htree : n.castSucc = (⟨1, by omega⟩ : Fin (ett.rounds + 2)) :=
      Fin.ext (by simp [n, hn])
    dsimp only [Tn]
    rw [hcolor, htree]
    exact (TechnicalTheoremBase G k ett.rounds e0 input ett.series).1
  · have hmore : 1 < ett.rounds := by have := C.positive; omega
    obtain ⟨predecessor, hr, hmaximum, _, _⟩ :=
      CertifiedETTPredecessor G k e0 input T phi ett C.maximum hmore
    have htree : n.castSucc = (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2)) :=
      Fin.ext rfl
    dsimp only [Tn]
    rw [htree]
    exact (ctx.lowerRung predecessor (by omega) (by omega) hmaximum).1

private theorem helper_equalTrees_948.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
      {S U : TreeSequence G e0},
    TreeSequenceInitialSegment S U →
    S.length = U.length →
    S = U := by
  classical
  intro V E G e0 S U hSU hlen
  cases S with
  | mk ls ps vs es vis eis fs aas =>
    cases U with
    | mk lu pu vu eu viu eiu fu aau =>
      simp only at hlen
      subst lu
      rw [TreeSequence.mk.injEq]
      refine ⟨rfl, ?_, ?_⟩
      · apply heq_of_eq
        funext i
        simpa only [Fin.castLE] using (hSU.2.1 i).symm
      · apply heq_of_eq
        funext i
        simpa only [Fin.castLE] using (hSU.2.2 i).symm

private theorem helper_ordinaryToA_1012.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    (∀ (a d : ℕ) (hbound : a + d ≤ H.dividerCount + (1 : ℕ)),
        TreeSequenceInitialSegment
          (H.stage (⟨a, by omega⟩ : Fin (H.dividerCount + (2 : ℕ))))
          (H.stage (⟨a + d, by omega⟩ : Fin (H.dividerCount + (2 : ℕ))))) →
    (H.dividerCount ≠ (0 : ℕ) → A = H.stage q.castSucc) →
    TreeSequenceInitialSegment Tn A →
    ∀ (j : Fin (H.dividerCount + (1 : ℕ))),
    TreeSequenceInitialSegment (H.stage j.castSucc) A := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q A n Tn stageSegment lastPositive TnToA j
  by_cases hj : j.val = 0
  · have he : j.castSucc = (0 : Fin (H.dividerCount + 2)) := Fin.ext hj
    rw [he, H.baseStage]; exact TnToA
  · have hz : H.dividerCount ≠ 0 := by have := j.isLt; omega
    rw [lastPositive hz]
    have hs := stageSegment j.val (H.dividerCount - j.val) (by omega)
    have he : (⟨j.val + (H.dividerCount - j.val), by omega⟩ :
        Fin (H.dividerCount + 2)) = q.castSucc := Fin.ext (by simp [q]; omega)
    rw [he] at hs
    convert hs using 1
    apply congrArg H.stage
    apply Fin.ext
    rfl

private theorem helper_sigmaRoute_1064.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base) (sigma : PartialEdgeColoring E k),
    (∀
        v ∈
          TreeSequenceVertexSet
            (HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ))),
        MissingColors G sigma v = MissingColors G phi v) →
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let _ : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    let B : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    (if ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE then
        CombinedStableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
          base.closure (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) phi
          sigma
      else
        StableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
          (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) phi sigma) →
    TreeSequenceInitialSegment B T →
    T.length = B.length + (1 : ℕ) →
    (∀ (t : Fin T.length), sigma (T.edge t) = phi (T.edge t)) →
    ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence sigma Tn T ∨
      (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
          ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
        ∃ (f : E) (seed : TreeSequence G e0),
          ett.series.data.connectingEdges n = { f } ∧
            TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence sigma seed T := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C sigma hpenultimateMissing n Tn Dn B hbase BToT
      hBlen fixedT
  rcases P2813_T1_TerminalRoute G k e0 input T phi ett with
    ⟨hp, hseq⟩ | ⟨hp, f, seed, hedges, hseed, hincident, hcontrol, hseq⟩
  · exact Or.inl ⟨hp, TashkinovAugmentationSequenceColoringTransport phi sigma
      Tn B T hseq BToT hBlen (fun t _ => fixedT t) hpenultimateMissing⟩
  · obtain ⟨c, hc, hcol⟩ := hcontrol
    have seedFixed : sigma f = phi f := by
      have hs : StableColoring Tn Dn phi sigma := by
        change (if ett.series.data.kind n = some TashkinovExtensionKind.PE then
          CombinedStableColoring Tn base.closure Dn phi sigma else StableColoring Tn Dn phi
              sigma) at hbase
        split at hbase
        · exact hbase.1
        · exact hbase
      exact hs.1 f hincident ⟨c, hc, hcol⟩
    exact Or.inr ⟨hp, f, seed, hedges, hseed,
      TashkinovAugmentationSequenceColoringTransport phi sigma seed B T
        hseq BToT hBlen (fun t _ => fixedT t) hpenultimateMissing⟩

private theorem helper_continuation_1171.{u_1, u_2} :
    helperContinuation1171Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx alpha beta hne z sigma hsigma H q A n Tn Dn
      htwo outside hmod prefixPresentation missingA segTrans commonPrefix equalTrees stageToT
      lastZero lastPositive coreToA TnToCore TnToA AToT ordinaryToA fixedT weak treeMissingEq
      combined corrT hmaximumT baseT hcoreT hclosureT terminalData K starredEq storedEq
      stageMissingEq segmentEq
  have coreStrict := @helper_coreStrict_772 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 input T phi ett base C htwo equalTrees lastZero
  have parallelNotClosed := @helper_parallelNotClosed_549 V E inferInstance inferInstance
      inferInstance inferInstance G k e0 input T phi ett base C sigma segTrans commonPrefix
      equalTrees stageToT coreToA TnToCore AToT fixedT treeMissingEq coreStrict
  let goodT : GoodHierarchy K := {
    gamma := C.good.gamma
    twoColors := by
      intro j eta heta
      exact C.good.twoColors j eta (by rw [storedEq j] at heta; exact heta)
    avoidance := by
      intro j eta heta c hc
      have ho : eta ∈ HierarchyStoredColorsAt H j := by rw [← storedEq j]; exact heta
      rw [stageMissingEq j, segmentEq j eta ho]
      exact C.good.avoidance j eta ho hc
    disjointPairs := by
      intro j eta theta heta htheta hne
      exact C.good.disjointPairs j eta theta
        (by rw [storedEq j] at heta; exact heta)
        (by rw [storedEq j] at htheta; exact htheta) hne
    uniqueRefresh := by
      intro i
      have hnew :
          ((TreeSequenceVertexSet (H.stage i.succ.castSucc) \
            TreeSequenceVertexSet (HierarchyStarredStage H i.castSucc)).biUnion
              fun v => MissingColors G sigma v) =
          ((TreeSequenceVertexSet (H.stage i.succ.castSucc) \
            TreeSequenceVertexSet (HierarchyStarredStage H i.castSucc)).biUnion
              fun v => MissingColors G phi v) := by
        apply Finset.biUnion_congr rfl
        intro v hv
        exact missingA v (TreeSequenceInitialSegmentVertexSetSubset (ordinaryToA i.succ)
          (Finset.mem_sdiff.mp hv).1)
      change ∃! eta : Fin k,
        eta ∈ HierarchyStoredColorsAt K i.succ ∧
          C.good.gamma i.succ eta ⊆
            ((TreeSequenceVertexSet (H.stage i.succ.castSucc) \
              TreeSequenceVertexSet (HierarchyStarredStage K i.castSucc)).biUnion
                fun v => MissingColors G sigma v) ∧
          ∀ theta ∈ HierarchyStoredColorsAt K i.succ, theta ≠ eta →
            C.good.gamma i.succ theta = C.good.gamma i.castSucc theta
      rw [starredEq i.castSucc, hnew]
      simp only [storedEq]
      exact C.good.uniqueRefresh i
    parallelBase := by
      dsimp only
      intro hp
      have hpOld : ett.series.data.kind n = some TashkinovExtensionKind.PE :=
        terminalData.2.1.symm.trans hp
      constructor
      · change ¬ TreeColorSetMinusClosed G sigma baseT.core
          ((HierarchyStoredColorsAt K 0).biUnion (C.good.gamma 0))
        rw [hcoreT, storedEq 0]
        exact parallelNotClosed hpOld
      · change 4 ≤ ((TreeMissingColors sigma
          (corrT.replacementETT.series.data.tree
            (Fin.last corrT.replacementETT.rounds).castSucc) ∩
          TreeMissingColors sigma baseT.closure) \
            (HierarchyStoredColorsAt K 0).biUnion (C.good.gamma 0)).card
        have closureMissing : TreeMissingColors sigma base.closure =
            TreeMissingColors phi base.closure := by
          unfold TreeMissingColors
          exact Finset.biUnion_congr rfl (combined hpOld).2.2
        rw [terminalData.1, hclosureT, storedEq 0, treeMissingEq Tn TnToA, closureMissing]
        exact (C.good.parallelBase hpOld).2
    minusClosed := by
      intro i
      change TreeColorSetMinusClosed G sigma (H.stage i.succ.castSucc)
        ((HierarchyStoredColorsAt K i.succ).biUnion (C.good.gamma i.castSucc))
      rw [storedEq i.succ]
      apply P2813_T1_MinusClosedTransport G k e0 _ phi sigma alpha beta hne z hsigma
        ctx.proper ctx.oneEdgeUncolored _ (C.good.minusClosed i)
      · intro v hv
        exact missingA v (TreeSequenceInitialSegmentVertexSetSubset (ordinaryToA i.succ) hv)
      · exact outside i.succ }
  have same : SameGoodHierarchy C.good goodT := by
    refine ⟨?_, rfl, ?_⟩
    · refine ⟨hcoreT.symm, rfl, HEq.rfl, HEq.rfl, ?_, fun _ => hclosureT.symm⟩
      exact ⟨fun hp => terminalData.2.1.trans hp, fun hp => terminalData.2.1.symm.trans hp⟩
    · intro j
      exact ⟨(storedEq j).symm, fun _ _ => rfl⟩
  have prefixMaximum : A = Tn ∨
      ∃ inputA : PartialEdgeColoring E k,
        ∃ ettA : ExtendedTashkinovTree G k e0 inputA A sigma, MaximumProperty ettA := by
    rcases prefixPresentation with he | ⟨corrA, hMPA⟩
    · exact Or.inl he
    · exact Or.inr ⟨corrA.replacementInput, corrA.replacementETT, hMPA⟩
  refine ⟨weak, hmod, prefixMaximum, ?_, corrT, hmaximumT, baseT, K, goodT, same⟩
  intro hq
  have hqK : 1 ≤ q.val := by change 0 < H.dividerCount at hq; dsimp [q]; omega
  have hqpos : H.dividerCount ≠ 0 := by change 0 < H.dividerCount at hq; omega
  have hA : A = H.stage q.castSucc := lastPositive hqpos
  have positivePackage := @helper_positivePackage_887 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 input T phi ett base C ctx alpha beta hne z sigma hsigma outside missingA
      TnToA ordinaryToA treeMissingEq combined corrT hmaximumT baseT hcoreT hclosureT terminalData
      starredEq storedEq stageMissingEq segmentEq parallelNotClosed hq hqK
  exact positivePackage A hA

private theorem helper_continuation_1123.{u_1, u_2} :
    helperContinuation1123Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx alpha beta hne z sigma hsigma
      hpenultimateMissing hstoredFirst H q A n Tn Dn B htwo hbase sigmaProper sigmaOne outside
      hmod prefixPresentation fixedA missingA htailEdges segTrans commonPrefix equalTrees
      stageSegment stageToT lastZero lastPositive coreToA TnToCore TnToA AToT
  have ordinaryToA := @helper_ordinaryToA_1012 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 input T phi ett base C stageSegment lastPositive TnToA
  have starredToA (j : Fin (H.dividerCount + 1)) :
      TreeSequenceInitialSegment (HierarchyStarredStage H j) A := by
    exact Fin.cases coreToA (fun i => ordinaryToA i.succ) j
  have BToT : TreeSequenceInitialSegment B T :=
    ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
  have hBlen : T.length = B.length + 1 := by
    change 2 ≤ T.length - A.length at htwo
    change T.length = min (A.length + ((T.length - A.length) - 1)) T.length + 1
    have := AToT.1
    omega
  have fixedT (t : Fin T.length) : sigma (T.edge t) = phi (T.edge t) := by
    by_cases ht : t.val < A.length
    · let ta : Fin A.length := ⟨t.val, ht⟩
      have he : Fin.castLE AToT.1 ta = t := Fin.ext rfl
      rw [← he, AToT.2.2 ta]
      exact fixedA ta
    · exact htailEdges t (by omega)
  have weak : HierarchyWeaklyStable H q sigma := by
    have allWeak (j : Fin (H.dividerCount + 1)) : HierarchyWeaklyStable H j sigma := by
      refine Fin.cases hbase (fun i => ⟨hbase, ?_⟩) j
      refine ⟨?_, ?_⟩
      · intro t _
        rw [← (ordinaryToA i.succ).2.2 t]
        exact fixedA _
      · intro v hv
        exact missingA v (TreeSequenceInitialSegmentVertexSetSubset (ordinaryToA i.succ) hv)
    exact allWeak q
  have treeMissingEq (S : TreeSequence G e0) (hSA : TreeSequenceInitialSegment S A) :
      TreeMissingColors sigma S = TreeMissingColors phi S := by
    unfold TreeMissingColors
    exact Finset.biUnion_congr rfl (fun v hv =>
      missingA v (TreeSequenceInitialSegmentVertexSetSubset hSA hv))
  have combined (hp : ett.series.data.kind n = some TashkinovExtensionKind.PE) :
      CombinedStableColoring Tn base.closure Dn phi sigma := by
    change (if ett.series.data.kind n = some TashkinovExtensionKind.PE then
      CombinedStableColoring Tn base.closure Dn phi sigma else
        StableColoring Tn Dn phi sigma) at hbase
    simpa only [hp, ite_true] using hbase
  have sigmaRoute := @helper_sigmaRoute_1064 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 input T phi ett base C sigma hpenultimateMissing hbase BToT hBlen fixedT
  have corrData := @helper_corrData_383 V E inferInstance inferInstance inferInstance inferInstance
      G k e0 input T phi ett base C sigma TnToA treeMissingEq
  have fullBase := @helper_fullBase_422 V E inferInstance inferInstance inferInstance inferInstance
      G k e0 input T phi ett base C ctx sigma sigmaProper sigmaOne hmod combined sigmaRoute corrData
  obtain ⟨corrT, hmaximumT, baseT, hcoreT, hclosureT⟩ := fullBase
  have terminalData := corrData corrT
  let K : TashkinovHierarchy corrT.replacementETT baseT := {
    dividerCount := H.dividerCount
    stage := H.stage
    baseStage := H.baseStage.trans terminalData.1.symm
    terminalStage := H.terminalStage
    nested := H.nested
    strict := H.strict
    dividerPosition := H.dividerPosition
    dividerPositive := H.dividerPositive
    dividerIncreasing := H.dividerIncreasing
    dividerStage := H.dividerStage
    coreInsideFirst := by rw [hcoreT]; exact H.coreInsideFirst }
  have starredEq (j : Fin (H.dividerCount + 1)) :
      HierarchyStarredStage K j = HierarchyStarredStage H j :=
    Fin.cases hcoreT (fun _ => rfl) j
  have storedEq (j : Fin (H.dividerCount + 1)) :
      HierarchyStoredColorsAt K j = HierarchyStoredColorsAt H j := by
    unfold HierarchyStoredColorsAt
    dsimp only
    rw [terminalData.2.2, starredEq j, treeMissingEq _ (starredToA j)]
  have stageMissingEq (j : Fin (H.dividerCount + 1)) :
      HierarchyStageMissingColors K j = HierarchyStageMissingColors H j := by
    refine Fin.cases ?_ (fun i => ?_) j
    · change TreeMissingColors sigma
        (corrT.replacementETT.series.data.tree
          (Fin.last corrT.replacementETT.rounds).castSucc) = TreeMissingColors phi Tn
      rw [terminalData.1]
      exact treeMissingEq Tn TnToA
    · exact treeMissingEq _ (ordinaryToA i.succ)
  have segmentEq := @helper_segmentEq_489 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 input T phi ett base C sigma hstoredFirst fixedA missingA stageToT AToT
      ordinaryToA fixedT corrT baseT hcoreT terminalData starredEq
  -- The first refresh prevents the core from being the whole first stage.
  exact @helper_continuation_1171 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 input T phi ett base C ctx alpha beta hne z sigma hsigma htwo outside hmod
      prefixPresentation missingA segTrans commonPrefix equalTrees stageToT lastZero lastPositive
      coreToA TnToCore TnToA AToT ordinaryToA fixedT weak treeMissingEq combined corrT hmaximumT
      baseT hcoreT hclosureT terminalData starredEq storedEq stageMissingEq segmentEq
theorem StableChangeCasesOneTwoFullTail {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (alpha beta : Fin k) (hne : alpha ≠ beta)
    (hmissingPrefix :
      alpha ∈ TreeMissingColors phi
          (HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1)) ∧
        beta ∈ TreeMissingColors phi
          (HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1)))
    (z : Sum V E) (hpath : TwoColorPathComponent G phi alpha beta z)
    (sigma : PartialEdgeColoring E k)
    (hsigma : sigma = TwoColorComponentSwap G phi alpha beta z)
    (hcase :
      let H := C.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
      let A := HierarchyStarredStage H q
      let Tnq := H.stage ⟨H.dividerCount, by omega⟩
      let Tn := ett.series.data.tree n.castSucc
      let Dn := TashkinovStoredColors ett.series.data n
      (0 < H.dividerCount ∧ alpha ∈ TreeMissingColors phi Tnq) ∨
        (H.dividerCount = 0 ∧
          (alpha ∈ TreeMissingColors phi Tn ∨
            (alpha ∈ TreeMissingColors phi A ∧
              alpha ∉ Dn ∧ beta ∉ Dn))))
    (hdisjoint :
      let va := T.vertex (HierarchyFirstMissingPosition phi T alpha)
      Disjoint (TwoColorComponent G phi alpha beta z)
        (TwoColorComponent G phi alpha beta (Sum.inl va)))
    (htailEdges :
      let H := C.hierarchy
      let A := HierarchyStarredStage H (Fin.last H.dividerCount)
      ∀ t : Fin T.length, A.length ≤ t.val →
        sigma (T.edge t) = phi (T.edge t))
    (hpenultimateMissing :
      ∀ v, v ∈ TreeSequenceVertexSet
          (HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1)) →
        MissingColors G sigma v = MissingColors G phi v)
    (hstoredFirst :
      let H := C.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      ∀ eta, eta ∈ HierarchyStoredColorsAt H q →
        HierarchyFirstMissingPosition sigma T eta =
          HierarchyFirstMissingPosition phi T eta) :
    let H := C.hierarchy
    let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let A := HierarchyStarredStage H q
    let Tnq := H.stage ⟨H.dividerCount, by omega⟩
    let Tn := ett.series.data.tree n.castSucc
    let Dnq := HierarchyStoredColorsAt H q
    HierarchyWeaklyStable H q sigma ∧
      ModColoring ett sigma ∧
        (A = Tn ∨
            ∃ inputA : PartialEdgeColoring E k,
              ∃ ettA : ExtendedTashkinovTree G k e0 inputA A sigma, MaximumProperty ettA) ∧
          (∀ hq : 0 < H.dividerCount,
              ∃ inputA : PartialEdgeColoring E k,
                ∃ ettA : ExtendedTashkinovTree G k e0 inputA A sigma,
                  ∃ baseA : HierarchyBase ettA sigma,
                    ∃ K : TashkinovHierarchy ettA baseA,
                      ∃ goodA : GoodHierarchy K,
                        MaximumProperty ettA ∧
                          ∃ hcount : K.dividerCount + 1 = H.dividerCount,
                            baseA.core = base.core ∧
                              baseA.closure = base.closure ∧
                                (∀ j : Fin (K.dividerCount + 2),
                                    K.stage j = H.stage ⟨j.val, by omega⟩) ∧
                                  (∀ j : Fin (K.dividerCount + 1),
                                      let jH : Fin (H.dividerCount + 1) := ⟨j.val, by omega⟩
                                      HierarchyStoredColorsAt K j =
                                          HierarchyStoredColorsAt H jH ∧
                                        ∀ eta ∈ HierarchyStoredColorsAt K j,
                                          goodA.gamma j eta = C.good.gamma jH eta) ∧
                                    TreeColorSetMinusClosed G sigma Tnq
                                      (Dnq.biUnion
                                        (C.good.gamma
                                          ⟨C.hierarchy.dividerCount - 1, by omega⟩))) ∧
            (∃ corrT : CorrespondingExtendedTashkinovTree G k e0 ett sigma T,
              MaximumProperty corrT.replacementETT ∧
                ∃ baseT : HierarchyBase corrT.replacementETT sigma,
                  ∃ K : TashkinovHierarchy corrT.replacementETT baseT,
                    ∃ goodT : GoodHierarchy K, SameGoodHierarchy C.good goodT) := by
  classical
  let H := C.hierarchy
  let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
  let A := HierarchyStarredStage H q
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn := ett.series.data.tree n.castSucc
  let Dn := TashkinovStoredColors ett.series.data n
  let B := HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1)
  have helem : ColoredVertexSetElementary G phi (TreeSequenceVertexSet B) :=
    HierarchyCounterexamplePenultimateElementary G k e0 input T phi
    ett base C ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
    ctx.lexicographicMinimality ctx.largeMissingSet
  have htwo : 2 ≤ T.length - A.length :=
    HierarchyCounterexampleTailAtLeastTwo G k e0 input T phi
    ett base C ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
    ctx.lexicographicMinimality ctx.largeMissingSet
  obtain ⟨hbase, missingA, sigmaProper, sigmaOne, outside⟩ :=
    P2813_T1_BaseControl G k e0 input T phi ett base C ctx helem
      alpha beta hne hmissingPrefix z hpath sigma hsigma hcase hdisjoint
  have preStepElementary := @helper_preStepElementary_896 V E inferInstance inferInstance
      inferInstance inferInstance G k e0 input T phi ett base C ctx
  have fixedA := P2813_T1_DisplayedEdges G k e0 input T phi ett base H C.good
    ctx.proper ctx.oneEdgeUncolored preStepElementary helem alpha beta z sigma hsigma
    sigmaOne hbase outside
  obtain ⟨hmod, prefixPresentation⟩ := P2813_T1_PrefixReconstruction
    G k e0 input T phi ett base C ctx sigma sigmaProper sigmaOne hbase fixedA missingA
  change (∀ t : Fin A.length, sigma (A.edge t) = phi (A.edge t)) at fixedA
  change (∀ v ∈ TreeSequenceVertexSet A,
    MissingColors G sigma v = MissingColors G phi v) at missingA
  change (∀ t : Fin T.length, A.length ≤ t.val →
    sigma (T.edge t) = phi (T.edge t)) at htailEdges
  have segRefl (S : TreeSequence G e0) : TreeSequenceInitialSegment S S :=
    ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
  have segTrans {S U W : TreeSequence G e0}
      (hSU : TreeSequenceInitialSegment S U) (hUW : TreeSequenceInitialSegment U W) :
      TreeSequenceInitialSegment S W := by
    clear * - hSU hUW
    refine ⟨hSU.1.trans hUW.1, ?_, ?_⟩
    · intro i
      exact (hUW.2.1 (Fin.castLE (Nat.succ_le_succ hSU.1) i)).trans (hSU.2.1 i)
    · intro i
      exact (hUW.2.2 (Fin.castLE hSU.1 i)).trans (hSU.2.2 i)
  have commonPrefix {S U W : TreeSequence G e0}
      (hSW : TreeSequenceInitialSegment S W) (hUW : TreeSequenceInitialSegment U W)
      (hlen : S.length ≤ U.length) : TreeSequenceInitialSegment S U := by
    clear * - hSW hUW hlen
    refine ⟨hlen, ?_, ?_⟩
    · intro i
      exact (hUW.2.1 (Fin.castLE (Nat.succ_le_succ hlen) i)).symm.trans (hSW.2.1 i)
    · intro i
      exact (hUW.2.2 (Fin.castLE hlen i)).symm.trans (hSW.2.2 i)
  have equalTrees := @helper_equalTrees_948 V E G e0
  have stageSegment (a d : ℕ) (hbound : a + d ≤ H.dividerCount + 1) :
      TreeSequenceInitialSegment (H.stage ⟨a, by omega⟩)
        (H.stage ⟨a + d, by omega⟩) := by
    clear * - H a d hbound segRefl segTrans
    induction d with
    | zero => simpa using segRefl (H.stage ⟨a, by omega⟩)
    | succ d ih =>
      exact segTrans (ih (by omega)) (H.nested ⟨a + d, by omega⟩)
  have stageToT (j : Fin (H.dividerCount + 2)) :
      TreeSequenceInitialSegment (H.stage j) T := by
    have hs := stageSegment j.val (H.dividerCount + 1 - j.val) (by omega)
    have he : (⟨j.val + (H.dividerCount + 1 - j.val), by omega⟩ :
        Fin (H.dividerCount + 2)) = Fin.last (H.dividerCount + 1) :=
      Fin.ext (by have := j.isLt; simp only [Fin.val_last]; omega)
    simpa [he, H.terminalStage] using hs
  have lastZero (hz : H.dividerCount = 0) : A = base.core := by
    have hq : q = 0 := Fin.ext (by simpa [q] using hz)
    simp only [A, hq, HierarchyStarredStage]
    rfl
  have lastPositive (hz : H.dividerCount ≠ 0) : A = H.stage q.castSucc := by
    have hq : q ≠ 0 := by
      intro he
      have := congrArg Fin.val he
      simp only [q, Fin.val_last, Fin.val_zero] at this
      exact hz this
    dsimp only [A]
    rw [← Fin.succ_pred q hq]
    rfl
  have coreToA : TreeSequenceInitialSegment base.core A := by
    by_cases hz : H.dividerCount = 0
    · rw [lastZero hz]; exact segRefl _
    · rw [lastPositive hz]
      have hs := stageSegment 1 (H.dividerCount - 1) (by omega)
      have he : (⟨1 + (H.dividerCount - 1), by omega⟩ :
          Fin (H.dividerCount + 2)) = q.castSucc := Fin.ext (by simp [q]; omega)
      rw [he] at hs
      exact segTrans H.coreInsideFirst hs
  have TnToCore : TreeSequenceInitialSegment Tn base.core := by
    by_cases hp : ett.series.data.kind n = some TashkinovExtensionKind.PE
    · exact (base.parallel hp).2.2.some.leftSegment
    · rw [base.nonparallel hp]; exact segRefl _
  have TnToA := segTrans TnToCore coreToA
  have AToT : TreeSequenceInitialSegment A T := by
    by_cases hz : H.dividerCount = 0
    · rw [lastZero hz]
      exact segTrans H.coreInsideFirst (stageToT _)
    · rw [lastPositive hz]; exact stageToT _
  exact @helper_continuation_1123 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 input T phi ett base C ctx alpha beta hne z sigma hsigma hpenultimateMissing
      hstoredFirst htwo hbase sigmaProper sigmaOne outside hmod prefixPresentation fixedA
      missingA htailEdges segTrans commonPrefix equalTrees stageSegment stageToT lastZero
      lastPositive coreToA TnToCore TnToA AToT
end GoldbergSeymour

end
