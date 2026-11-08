/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyTreeFacts

public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentFacts

public import LeanPool.GoldbergSeymour.TreeSequenceColoringFacts

public import LeanPool.GoldbergSeymour.ChangeLemmaBothInside
public import LeanPool.GoldbergSeymour.HierarchyCounterexampleLess
public import LeanPool.GoldbergSeymour.HierarchyCounterexampleMeasure
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequencePosition
public import LeanPool.GoldbergSeymour.LowerRoundInductionHypothesis
public import LeanPool.GoldbergSeymour.OneAdditionPreparatoryLemmas

/-!
# Hierarchy Counterexample One Addition Positive Divider Impossible

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open OneAdditionPreparatoryLemmas

private abbrev helperBranch654Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base) (hpositive : (0 : ℕ) < C.hierarchy.dividerCount),
   let H : TashkinovHierarchy ett base := C.hierarchy;
   let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
   let i : Fin H.dividerCount :=
    (⟨H.dividerCount - (1 : ℕ),
      id
       (fun (hpositive : (0 : ℕ) < H.dividerCount) ↦
        Decidable.byContradiction fun (a : ¬H.dividerCount - (1 : ℕ) < H.dividerCount) ↦ by omega)
       hpositive⟩ :
     Fin H.dividerCount);
   let A : TreeSequence G e0 := HierarchyStarredStage H q;
   let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
   let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
   ∀ (_ : TreeSequenceInitialSegment A T),
    let y : V := T.vertex (Fin.last T.length);
    ∀ alpha ∈ TreeMissingColors phi A,
     alpha ∈ MissingColors G phi y →
      ∀ (gamma eta theta : Fin k),
       theta ∈ C.good.gamma i.succ eta →
        (theta ∈
          (TreeSequenceVertexSet (C.hierarchy.stage i.succ.castSucc) \
             TreeSequenceVertexSet (HierarchyStarredStage C.hierarchy i.castSucc)).biUnion
           fun (v : V) ↦ MissingColors G phi v) →
         ∀ (x : V),
          theta ∈ MissingColors G phi x →
           theta ∈ TreeMissingColors phi A →
            TreeColorSetClosed G phi A { theta } →
             theta ≠ gamma →
              (∀ (beta : Fin k), theta ≠ beta → TreeInterchangeable G A phi theta beta) →
               theta ≠ alpha →
                (∀ v ∈ TreeSequenceVertexSet A,
                  Sum.inl v ∉ TwoColorComponent G phi theta alpha (Sum.inl y)) →
                 let sigma : PartialEdgeColoring E k :=
                  TwoColorComponentSwap G phi theta alpha (Sum.inl y);
                 OutsideKempeRecoloring A phi sigma theta alpha →
                  (IsProperEdgeColoring G sigma ∧
                    IsOneEdgeUncolored sigma e0 ∧
                     StableColoring A (TashkinovStoredColors ett.series.data n) phi sigma ∧
                      TreeColoringInvariant A phi sigma ∧
                       ∀ (f : E), TreeIncidentEdge A f → sigma f = phi f) →
                   StableColoring Tn (TashkinovStoredColors ett.series.data n)
                     (ett.series.data.coloring n) sigma →
                    ModColoring ett sigma →
                     (∀ (t : Fin T.length), sigma (T.edge t) = phi (T.edge t)) →
                      (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
                         TashkinovAugmentationSequence sigma Tn T ∨
                        (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
                          ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
                         ∃ (edge : E) (seed : TreeSequence G e0),
                          ett.series.data.connectingEdges n = { edge } ∧
                           TreeSequenceAdjoinEdge Tn edge seed ∧
                            TashkinovAugmentationSequence sigma seed T) →
                       ∀ (corrT : CorrespondingExtendedTashkinovTree G k e0 ett sigma T),
                        MaximumProperty corrT.replacementETT →
                         ¬ColoredVertexSetElementary G sigma (TreeSequenceVertexSet T) →
                          OutsideKempeRecoloring (H.stage q.castSucc) phi sigma theta alpha →
                           ∀ (positivePrefix : (1 : ℕ) ≤ ett.rounds)
                            (abovePrefix :
                             TreeSequenceInitialSegment
                              (ett.series.data.tree
                               (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + (2 : ℕ))))
                              (H.stage q.castSucc))
                            (strictPrefix :
                             (ett.series.data.tree
                                (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + (2 : ℕ)))).length <
                              (H.stage q.castSucc).length)
                            (belowPrefix :
                             TreeSequenceInitialSegment (H.stage q.castSucc)
                              (ett.series.data.tree (Fin.last (ett.rounds + (1 : ℕ)))))
                            (generatingPrefix :
                             phi = ett.series.data.coloring (Fin.last ett.rounds))
                            (basePrefix :
                             HierarchyBase
                              {
                               rounds := ett.rounds, roundsPositive := positivePrefix,
                               series := ett.series, abovePenultimate := abovePrefix,
                               strictAbovePenultimate := strictPrefix, belowFinal := belowPrefix,
                               generatingColoring := generatingPrefix :
                               ExtendedTashkinovTree G k e0 input (H.stage q.castSucc) phi }
                              phi)
                            (HP :
                             TashkinovHierarchy
                              {
                               rounds := ett.rounds, roundsPositive := positivePrefix,
                               series := ett.series, abovePenultimate := abovePrefix,
                               strictAbovePenultimate := strictPrefix, belowFinal := belowPrefix,
                               generatingColoring := generatingPrefix :
                               ExtendedTashkinovTree G k e0 input (H.stage q.castSucc) phi }
                              basePrefix)
                            (goodPrefix : GoodHierarchy HP),
                            (have n :
                              Fin
                               ({ rounds := ett.rounds, roundsPositive := positivePrefix,
                                  series := ett.series, abovePenultimate := abovePrefix,
                                  strictAbovePenultimate := strictPrefix, belowFinal := belowPrefix,
                                  generatingColoring := generatingPrefix :
                                  ExtendedTashkinovTree G k e0 input (H.stage q.castSucc)
                                   phi }.rounds +
                                (1 : ℕ)) :=
                              Fin.last
                               { rounds := ett.rounds, roundsPositive := positivePrefix,
                                 series := ett.series, abovePenultimate := abovePrefix,
                                 strictAbovePenultimate := strictPrefix, belowFinal := belowPrefix,
                                 generatingColoring := generatingPrefix :
                                 ExtendedTashkinovTree G k e0 input (H.stage q.castSucc)
                                  phi }.rounds;
                             have Dn : Finset (Fin k) :=
                              TashkinovStoredColors
                               { rounds := ett.rounds, roundsPositive := positivePrefix,
                                 series := ett.series, abovePenultimate := abovePrefix,
                                 strictAbovePenultimate := strictPrefix, belowFinal := belowPrefix,
                                 generatingColoring := generatingPrefix :
                                 ExtendedTashkinovTree G k e0 input (H.stage q.castSucc)
                                  phi }.series.data
                               n;
                             IsProperEdgeColoring G sigma ∧
                              IsOneEdgeUncolored sigma e0 ∧
                               StableColoring (H.stage q.castSucc) Dn phi sigma ∧
                                TreeColoringInvariant (H.stage q.castSucc) phi sigma ∧
                                 ∃ (corr :
                                  CorrespondingExtendedTashkinovTree G k e0
                                   {
                                    rounds := ett.rounds, roundsPositive := positivePrefix,
                                    series := ett.series, abovePenultimate := abovePrefix,
                                    strictAbovePenultimate := strictPrefix,
                                    belowFinal := belowPrefix,
                                    generatingColoring := generatingPrefix :
                                    ExtendedTashkinovTree G k e0 input (H.stage q.castSucc) phi }
                                   sigma (H.stage q.castSucc)),
                                  MaximumProperty corr.replacementETT ∧
                                   ∃ (baseSigma : HierarchyBase corr.replacementETT sigma) (K :
                                    TashkinovHierarchy corr.replacementETT baseSigma) (goodSigma :
                                    GoodHierarchy K),
                                    SameGoodHierarchy goodPrefix goodSigma ∧
                                     (TreeColorSetMinusClosed G phi (H.stage q.castSucc)
                                       ((HierarchyTerminalStoredColors HP).biUnion
                                        (goodPrefix.gamma (Fin.last HP.dividerCount))) →
                                      TreeColorSetMinusClosed G sigma (H.stage q.castSucc)
                                       ((HierarchyTerminalStoredColors HP).biUnion
                                        (goodPrefix.gamma (Fin.last HP.dividerCount))))) →
                             ∀
                              (corrPrefix :
                               CorrespondingExtendedTashkinovTree G k e0
                                {
                                 rounds := ett.rounds, roundsPositive := positivePrefix,
                                 series := ett.series, abovePenultimate := abovePrefix,
                                 strictAbovePenultimate := strictPrefix, belowFinal := belowPrefix,
                                 generatingColoring := generatingPrefix :
                                 ExtendedTashkinovTree G k e0 input (H.stage q.castSucc) phi }
                                sigma (H.stage q.castSucc)),
                              MaximumProperty corrPrefix.replacementETT →
                               ∀ (basePrefixSigma : HierarchyBase corrPrefix.replacementETT sigma)
                                (KP : TashkinovHierarchy corrPrefix.replacementETT basePrefixSigma)
                                (goodPrefixSigma : GoodHierarchy KP),
                                SameGoodHierarchy goodPrefix goodPrefixSigma →
                                 (TreeColorSetMinusClosed G phi (H.stage q.castSucc)
                                    ((HierarchyTerminalStoredColors HP).biUnion
                                     (goodPrefix.gamma (Fin.last HP.dividerCount))) →
                                   TreeColorSetMinusClosed G sigma (H.stage q.castSucc)
                                    ((HierarchyTerminalStoredColors HP).biUnion
                                     (goodPrefix.gamma (Fin.last HP.dividerCount)))) →
                                  ∀ (baseT : HierarchyBase corrT.replacementETT sigma),
                                   baseT.core = basePrefixSigma.core →
                                    baseT.closure = basePrefixSigma.closure →
                                     (↑baseT.supportPosition : ℕ) =
                                       (↑basePrefixSigma.supportPosition : ℕ) →
                                      ∀ (hcoreT : baseT.core = base.core)
                                       (hterminalTree :
                                        corrT.replacementETT.series.data.tree
                                          (Fin.last corrT.replacementETT.rounds).castSucc =
                                         Tn),
                                       let K : TashkinovHierarchy corrT.replacementETT baseT :=
                                        {
                                         dividerCount := H.dividerCount, stage := H.stage,
                                         baseStage := Eq.trans H.baseStage (Eq.symm hterminalTree),
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
                                                (⟨(1 : ℕ), by omega⟩ :
                                                 Fin (H.dividerCount + (2 : ℕ)))))
                                             hcoreT))
                                           H.coreInsideFirst :
                                         TashkinovHierarchy corrT.replacementETT baseT };
                                       (∀ (B : TreeSequence G e0),
                                         TreeSequenceVertexSet B ⊆ TreeSequenceVertexSet A →
                                          TreeMissingColors sigma B = TreeMissingColors phi B) →
                                        (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
                                          HierarchyStarredStage K j = HierarchyStarredStage H j) →
                                         corrT.replacementETT.series.data.kind
                                             (Fin.last corrT.replacementETT.rounds) =
                                            ett.series.data.kind n ∧
                                           TashkinovStoredColors corrT.replacementETT.series.data
                                             (Fin.last corrT.replacementETT.rounds) =
                                            TashkinovStoredColors ett.series.data n →
                                          (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
                                            HierarchyStoredColorsAt K j =
                                             HierarchyStoredColorsAt H j) →
                                           (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
                                             HierarchyStageMissingColors K j =
                                              HierarchyStageMissingColors H j) →
                                            (∀ (psi : PartialEdgeColoring E k),
                                              ∀ c ∈ TreeMissingColors psi A,
                                               (↑(HierarchyFirstMissingPosition psi T c) : ℕ) ≤
                                                A.length) →
                                             ∀ (c : Fin k),
                                              (have C : Set (V ⊕ E) :=
                                                TwoColorComponent G phi theta alpha (Sum.inl y);
                                               have phi' : PartialEdgeColoring E k :=
                                                TwoColorComponentSwap G phi theta alpha (Sum.inl y);
                                               (∀ (v : V),
                                                 Sum.inl v ∉ C →
                                                  MissingColors G phi' v = MissingColors G phi v) ∧
                                                (∀ (v : V),
                                                  Sum.inl v ∈ C →
                                                   theta ∈ MissingColors G phi v →
                                                    alpha ∈ MissingColors G phi' v) ∧
                                                 (∀ (v : V),
                                                   Sum.inl v ∈ C →
                                                    alpha ∈ MissingColors G phi v →
                                                     theta ∈ MissingColors G phi' v) ∧
                                                  ∀ (v : V) (c : Fin k),
                                                   c ≠ theta →
                                                    c ≠ alpha →
                                                     (c ∈ MissingColors G phi' v ↔
                                                      c ∈ MissingColors G phi v)) →
                                               c = theta ∨ c = alpha →
                                                HierarchyFirstMissingPosition sigma T c =
                                                 HierarchyFirstMissingPosition phi T c

private abbrev helperFirstMissingEq961Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base) (_ : IsProperEdgeColoring G phi)
   (hpositive : (0 : ℕ) < C.hierarchy.dividerCount),
   let H : TashkinovHierarchy ett base := C.hierarchy;
   let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
   let i : Fin H.dividerCount :=
    (⟨H.dividerCount - (1 : ℕ),
      id
       (fun (hpositive : (0 : ℕ) < H.dividerCount) ↦
        Decidable.byContradiction fun (a : ¬H.dividerCount - (1 : ℕ) < H.dividerCount) ↦ by omega)
       hpositive⟩ :
     Fin H.dividerCount);
   let A : TreeSequence G e0 := HierarchyStarredStage H q;
   let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
   let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
   ∀ (_ : TreeSequenceInitialSegment A T),
    let y : V := T.vertex (Fin.last T.length);
    ∀ alpha ∈ TreeMissingColors phi A,
     alpha ∈ MissingColors G phi y →
      ∀ (gamma eta theta : Fin k),
       theta ∈ C.good.gamma i.succ eta →
        (theta ∈
          (TreeSequenceVertexSet (C.hierarchy.stage i.succ.castSucc) \
             TreeSequenceVertexSet (HierarchyStarredStage C.hierarchy i.castSucc)).biUnion
           fun (v : V) ↦ MissingColors G phi v) →
         ∀ (x : V),
          theta ∈ MissingColors G phi x →
           theta ∈ TreeMissingColors phi A →
            TreeColorSetClosed G phi A { theta } →
             theta ≠ gamma →
              (∀ (beta : Fin k), theta ≠ beta → TreeInterchangeable G A phi theta beta) →
               theta ≠ alpha →
                (∀ v ∈ TreeSequenceVertexSet A,
                  Sum.inl v ∉ TwoColorComponent G phi theta alpha (Sum.inl y)) →
                 let sigma : PartialEdgeColoring E k :=
                  TwoColorComponentSwap G phi theta alpha (Sum.inl y);
                 OutsideKempeRecoloring A phi sigma theta alpha →
                  (IsProperEdgeColoring G sigma ∧
                    IsOneEdgeUncolored sigma e0 ∧
                     StableColoring A (TashkinovStoredColors ett.series.data n) phi sigma ∧
                      TreeColoringInvariant A phi sigma ∧
                       ∀ (f : E), TreeIncidentEdge A f → sigma f = phi f) →
                   StableColoring Tn (TashkinovStoredColors ett.series.data n)
                     (ett.series.data.coloring n) sigma →
                    ModColoring ett sigma →
                     (∀ (t : Fin T.length), sigma (T.edge t) = phi (T.edge t)) →
                      (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
                         TashkinovAugmentationSequence sigma Tn T ∨
                        (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
                          ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
                         ∃ (edge : E) (seed : TreeSequence G e0),
                          ett.series.data.connectingEdges n = { edge } ∧
                           TreeSequenceAdjoinEdge Tn edge seed ∧
                            TashkinovAugmentationSequence sigma seed T) →
                       ∀ (corrT : CorrespondingExtendedTashkinovTree G k e0 ett sigma T),
                        MaximumProperty corrT.replacementETT →
                         ¬ColoredVertexSetElementary G sigma (TreeSequenceVertexSet T) →
                          OutsideKempeRecoloring (H.stage q.castSucc) phi sigma theta alpha →
                           ∀ (positivePrefix : (1 : ℕ) ≤ ett.rounds)
                            (abovePrefix :
                             TreeSequenceInitialSegment
                              (ett.series.data.tree
                               (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + (2 : ℕ))))
                              (H.stage q.castSucc))
                            (strictPrefix :
                             (ett.series.data.tree
                                (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + (2 : ℕ)))).length <
                              (H.stage q.castSucc).length)
                            (belowPrefix :
                             TreeSequenceInitialSegment (H.stage q.castSucc)
                              (ett.series.data.tree (Fin.last (ett.rounds + (1 : ℕ)))))
                            (generatingPrefix :
                             phi = ett.series.data.coloring (Fin.last ett.rounds))
                            (basePrefix :
                             HierarchyBase
                              {
                               rounds := ett.rounds, roundsPositive := positivePrefix,
                               series := ett.series, abovePenultimate := abovePrefix,
                               strictAbovePenultimate := strictPrefix, belowFinal := belowPrefix,
                               generatingColoring := generatingPrefix :
                               ExtendedTashkinovTree G k e0 input (H.stage q.castSucc) phi }
                              phi)
                            (HP :
                             TashkinovHierarchy
                              {
                               rounds := ett.rounds, roundsPositive := positivePrefix,
                               series := ett.series, abovePenultimate := abovePrefix,
                               strictAbovePenultimate := strictPrefix, belowFinal := belowPrefix,
                               generatingColoring := generatingPrefix :
                               ExtendedTashkinovTree G k e0 input (H.stage q.castSucc) phi }
                              basePrefix)
                            (goodPrefix : GoodHierarchy HP),
                            (have n :
                              Fin
                               ({ rounds := ett.rounds, roundsPositive := positivePrefix,
                                  series := ett.series, abovePenultimate := abovePrefix,
                                  strictAbovePenultimate := strictPrefix, belowFinal := belowPrefix,
                                  generatingColoring := generatingPrefix :
                                  ExtendedTashkinovTree G k e0 input (H.stage q.castSucc)
                                   phi }.rounds +
                                (1 : ℕ)) :=
                              Fin.last
                               { rounds := ett.rounds, roundsPositive := positivePrefix,
                                 series := ett.series, abovePenultimate := abovePrefix,
                                 strictAbovePenultimate := strictPrefix, belowFinal := belowPrefix,
                                 generatingColoring := generatingPrefix :
                                 ExtendedTashkinovTree G k e0 input (H.stage q.castSucc)
                                  phi }.rounds;
                             have Dn : Finset (Fin k) :=
                              TashkinovStoredColors
                               { rounds := ett.rounds, roundsPositive := positivePrefix,
                                 series := ett.series, abovePenultimate := abovePrefix,
                                 strictAbovePenultimate := strictPrefix, belowFinal := belowPrefix,
                                 generatingColoring := generatingPrefix :
                                 ExtendedTashkinovTree G k e0 input (H.stage q.castSucc)
                                  phi }.series.data
                               n;
                             IsProperEdgeColoring G sigma ∧
                              IsOneEdgeUncolored sigma e0 ∧
                               StableColoring (H.stage q.castSucc) Dn phi sigma ∧
                                TreeColoringInvariant (H.stage q.castSucc) phi sigma ∧
                                 ∃ (corr :
                                  CorrespondingExtendedTashkinovTree G k e0
                                   {
                                    rounds := ett.rounds, roundsPositive := positivePrefix,
                                    series := ett.series, abovePenultimate := abovePrefix,
                                    strictAbovePenultimate := strictPrefix,
                                    belowFinal := belowPrefix,
                                    generatingColoring := generatingPrefix :
                                    ExtendedTashkinovTree G k e0 input (H.stage q.castSucc) phi }
                                   sigma (H.stage q.castSucc)),
                                  MaximumProperty corr.replacementETT ∧
                                   ∃ (baseSigma : HierarchyBase corr.replacementETT sigma) (K :
                                    TashkinovHierarchy corr.replacementETT baseSigma) (goodSigma :
                                    GoodHierarchy K),
                                    SameGoodHierarchy goodPrefix goodSigma ∧
                                     (TreeColorSetMinusClosed G phi (H.stage q.castSucc)
                                       ((HierarchyTerminalStoredColors HP).biUnion
                                        (goodPrefix.gamma (Fin.last HP.dividerCount))) →
                                      TreeColorSetMinusClosed G sigma (H.stage q.castSucc)
                                       ((HierarchyTerminalStoredColors HP).biUnion
                                        (goodPrefix.gamma (Fin.last HP.dividerCount))))) →
                             ∀
                              (corrPrefix :
                               CorrespondingExtendedTashkinovTree G k e0
                                {
                                 rounds := ett.rounds, roundsPositive := positivePrefix,
                                 series := ett.series, abovePenultimate := abovePrefix,
                                 strictAbovePenultimate := strictPrefix, belowFinal := belowPrefix,
                                 generatingColoring := generatingPrefix :
                                 ExtendedTashkinovTree G k e0 input (H.stage q.castSucc) phi }
                                sigma (H.stage q.castSucc)),
                              MaximumProperty corrPrefix.replacementETT →
                               ∀ (basePrefixSigma : HierarchyBase corrPrefix.replacementETT sigma)
                                (KP : TashkinovHierarchy corrPrefix.replacementETT basePrefixSigma)
                                (goodPrefixSigma : GoodHierarchy KP),
                                SameGoodHierarchy goodPrefix goodPrefixSigma →
                                 (TreeColorSetMinusClosed G phi (H.stage q.castSucc)
                                    ((HierarchyTerminalStoredColors HP).biUnion
                                     (goodPrefix.gamma (Fin.last HP.dividerCount))) →
                                   TreeColorSetMinusClosed G sigma (H.stage q.castSucc)
                                    ((HierarchyTerminalStoredColors HP).biUnion
                                     (goodPrefix.gamma (Fin.last HP.dividerCount)))) →
                                  let _ :
                                   CorrespondingExtendedTashkinovTree G k e0 ett sigma
                                    (H.stage q.castSucc) :=
                                   {
                                    replacementInput := corrPrefix.replacementInput,
                                    replacementSeries := corrPrefix.replacementSeries,
                                    replacementETT := corrPrefix.replacementETT,
                                    rungAgreement := corrPrefix.rungAgreement,
                                    seriesPresentation := corrPrefix.seriesPresentation,
                                    finalGeneratingColoring := corrPrefix.finalGeneratingColoring,
                                    ladderTreesAgree := corrPrefix.ladderTreesAgree,
                                    storedColorsAgree := corrPrefix.storedColorsAgree,
                                    connectingEdgesAgree := corrPrefix.connectingEdgesAgree,
                                    extensionKindsAgree := corrPrefix.extensionKindsAgree,
                                    replacementProper := corrPrefix.replacementProper,
                                    replacementOneUncolored := corrPrefix.replacementOneUncolored,
                                    replacementStable := corrPrefix.replacementStable :
                                    CorrespondingExtendedTashkinovTree G k e0 ett sigma
                                     (H.stage q.castSucc) };
                                  ∀ (baseT : HierarchyBase corrT.replacementETT sigma),
                                   baseT.core = basePrefixSigma.core →
                                    baseT.closure = basePrefixSigma.closure →
                                     (↑baseT.supportPosition : ℕ) =
                                       (↑basePrefixSigma.supportPosition : ℕ) →
                                      ∀ (hcoreT : baseT.core = base.core)
                                       (hterminalTree :
                                        corrT.replacementETT.series.data.tree
                                          (Fin.last corrT.replacementETT.rounds).castSucc =
                                         Tn),
                                       let K : TashkinovHierarchy corrT.replacementETT baseT :=
                                        {
                                         dividerCount := H.dividerCount, stage := H.stage,
                                         baseStage := Eq.trans H.baseStage (Eq.symm hterminalTree),
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
                                                (⟨(1 : ℕ), by omega⟩ :
                                                 Fin (H.dividerCount + (2 : ℕ)))))
                                             hcoreT))
                                           H.coreInsideFirst :
                                         TashkinovHierarchy corrT.replacementETT baseT };
                                       (∀ (B : TreeSequence G e0),
                                         TreeSequenceVertexSet B ⊆ TreeSequenceVertexSet A →
                                          TreeMissingColors sigma B = TreeMissingColors phi B) →
                                        (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
                                          HierarchyStarredStage K j = HierarchyStarredStage H j) →
                                         corrT.replacementETT.series.data.kind
                                             (Fin.last corrT.replacementETT.rounds) =
                                            ett.series.data.kind n ∧
                                           TashkinovStoredColors corrT.replacementETT.series.data
                                             (Fin.last corrT.replacementETT.rounds) =
                                            TashkinovStoredColors ett.series.data n →
                                          (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
                                            HierarchyStoredColorsAt K j =
                                             HierarchyStoredColorsAt H j) →
                                           (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
                                             HierarchyStageMissingColors K j =
                                              HierarchyStageMissingColors H j) →
                                            (∀ (psi : PartialEdgeColoring E k),
                                              ∀ c ∈ TreeMissingColors psi A,
                                               (↑(HierarchyFirstMissingPosition psi T c) : ℕ) ≤
                                                A.length) →
                                             ∀ (c : Fin k),
                                              HierarchyFirstMissingPosition sigma T c =
                                               HierarchyFirstMissingPosition phi T c

private abbrev helperContinuation2653Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base) (_ : IsProperEdgeColoring G phi)
   (_ : LowerRoundInductionHypothesis G k e0 ett.rounds)
   (_ :
    (∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
     {generating' : PartialEdgeColoring E k}
     (other : ExtendedTashkinovTree G k e0 input' T' generating') (_ : other.rounds = ett.rounds)
     (_ : MaximumProperty other) (base' : HierarchyBase other generating')
     (K : TashkinovHierarchy other base') (_ : GoodHierarchy K)
     (_ : K.dividerCount < C.hierarchy.dividerCount),
     ColoredVertexSetElementary G generating' (TreeSequenceVertexSet T')))
   (_ :
    (∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
     {generating' : PartialEdgeColoring E k}
     {other : ExtendedTashkinovTree G k e0 input' T' generating'}
     {base' : HierarchyBase other generating'} (C' : HierarchyCounterexample base')
     (_ : other.rounds = ett.rounds) (_ : C'.hierarchy.dividerCount = C.hierarchy.dividerCount),
     ¬HierarchyCounterexampleLess (HierarchyCounterexampleMeasure C')
       (HierarchyCounterexampleMeasure C)))
   (_ :
    (let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    (2 : ℕ) * ett.rounds + (11 : ℕ) ≤ (TreeMissingColors phi Tn).card))
   (_ : (0 : ℕ) < C.hierarchy.dividerCount),
   let H : TashkinovHierarchy ett base := C.hierarchy;
   let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
   let A : TreeSequence G e0 := HierarchyStarredStage H q;
   let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
   let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
   ∀ (hlen : T.length = A.length + (1 : ℕ))
    (_ :
     (∀ {X Y Z : TreeSequence G e0} (_ : TreeSequenceInitialSegment X Z)
      (_ : TreeSequenceInitialSegment Y Z) (_ : X.length ≤ Y.length),
      TreeSequenceInitialSegment X Y))
    (_ :
     (∀ {X Y : TreeSequence G e0} (_ : TreeSequenceInitialSegment X Y) (_ : X.length = Y.length),
      X = Y))
    (_ : TreeSequenceInitialSegment A T) (hTnA : TreeSequenceInitialSegment Tn A)
    (_ :
     (∀ (m : ℕ) (hm : (1 : ℕ) ≤ m) (hmT : m ≤ T.length),
      TreeSequenceInitialSegment (TreeSequencePrefix T m hm hmT) T))
    (_ : ColoredVertexSetElementary G phi (TreeSequenceVertexSet A)),
    let r : Fin T.length := (⟨A.length, by omega⟩ : Fin T.length);
    let f : E := T.edge r;
    let y : V := T.vertex (Fin.last T.length);
    ∀ (_ : y ∉ TreeSequenceVertexSet A),
     ∀ alpha ∈ MissingColors G phi y,
      ∀ gamma ∈ TreeMissingColors phi A,
       phi f = some gamma →
        (∃ u ∈ TreeSequenceVertexSet A, G.ends f = s(u, y)) →
         ∀ (_ theta : Fin k),
          theta ∈ TreeMissingColors phi A →
           TreeColorSetClosed G phi A { theta } →
            theta ≠ gamma →
             (∀ (psi : PartialEdgeColoring E k),
               IsProperEdgeColoring G psi →
                ∀ (c d : Fin k),
                 c ≠ d →
                  c ∈ TreeMissingColors psi A →
                   d ∈ TreeMissingColors psi A →
                    ∀ w ∉ TreeSequenceVertexSet A,
                     c ∈ MissingColors G psi w ∨ d ∈ MissingColors G psi w →
                      TreeInterchangeable G A psi c d →
                       ∀ v ∈ TreeSequenceVertexSet A,
                        Sum.inl v ∉ TwoColorComponent G psi c d (Sum.inl w)) →
              theta ≠ alpha →
               let sigma : PartialEdgeColoring E k :=
                TwoColorComponentSwap G phi theta alpha (Sum.inl y);
               ∀
                (hstableA :
                 IsProperEdgeColoring G sigma ∧
                  IsOneEdgeUncolored sigma e0 ∧
                   StableColoring A (TashkinovStoredColors ett.series.data n) phi sigma ∧
                    TreeColoringInvariant A phi sigma ∧
                     ∀ (f : E), TreeIncidentEdge A f → sigma f = phi f),
                (∀ c ∈ TreeMissingColors phi A,
                  c ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T c)) ∧
                   T.vertex (HierarchyFirstMissingPosition phi T c) ∈ TreeSequenceVertexSet A) →
                 (∀ (t : Fin T.length), sigma (T.edge t) = phi (T.edge t)) →
                  ∀ (corrT : CorrespondingExtendedTashkinovTree G k e0 ett sigma T),
                   MaximumProperty corrT.replacementETT →
                    ¬ColoredVertexSetElementary G sigma (TreeSequenceVertexSet T) →
                     ∀ (positivePrefix : (1 : ℕ) ≤ ett.rounds)
                      (abovePrefix :
                       TreeSequenceInitialSegment
                        (ett.series.data.tree (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + (2 : ℕ))))
                        (H.stage q.castSucc))
                      (strictPrefix :
                       (ett.series.data.tree
                          (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + (2 : ℕ)))).length <
                        (H.stage q.castSucc).length)
                      (belowPrefix :
                       TreeSequenceInitialSegment (H.stage q.castSucc)
                        (ett.series.data.tree (Fin.last (ett.rounds + (1 : ℕ)))))
                      (generatingPrefix : phi = ett.series.data.coloring (Fin.last ett.rounds))
                      (corrPrefix :
                       CorrespondingExtendedTashkinovTree G k e0
                        {
                         rounds := ett.rounds, roundsPositive := positivePrefix,
                         series := ett.series, abovePenultimate := abovePrefix,
                         strictAbovePenultimate := strictPrefix, belowFinal := belowPrefix,
                         generatingColoring := generatingPrefix :
                         ExtendedTashkinovTree G k e0 input (H.stage q.castSucc) phi }
                        sigma (H.stage q.castSucc))
                      (_ : HierarchyBase corrPrefix.replacementETT sigma)
                      (baseT : HierarchyBase corrT.replacementETT sigma)
                      (hcoreT : baseT.core = base.core)
                      (hterminalTree :
                       corrT.replacementETT.series.data.tree
                         (Fin.last corrT.replacementETT.rounds).castSucc =
                        Tn),
                      let K : TashkinovHierarchy corrT.replacementETT baseT :=
                       {
                        dividerCount := H.dividerCount, stage := H.stage,
                        baseStage := Eq.trans H.baseStage (Eq.symm hterminalTree),
                        terminalStage := H.terminalStage, nested := H.nested, strict := H.strict,
                        dividerPosition := H.dividerPosition, dividerPositive := H.dividerPositive,
                        dividerIncreasing := H.dividerIncreasing, dividerStage := H.dividerStage,
                        coreInsideFirst :=
                         Eq.mpr
                          (id
                           (congrArg
                            (fun (_a : TreeSequence G e0) ↦
                             TreeSequenceInitialSegment _a
                              (H.stage (⟨(1 : ℕ), by omega⟩ : Fin (H.dividerCount + (2 : ℕ)))))
                            hcoreT))
                          H.coreInsideFirst :
                        TashkinovHierarchy corrT.replacementETT baseT };
                      ∀
                       (missingTree :
                        ∀ (B : TreeSequence G e0),
                         TreeSequenceVertexSet B ⊆ TreeSequenceVertexSet A →
                          TreeMissingColors sigma B = TreeMissingColors phi B)
                       (stageInsideA :
                        ∀ (j : Fin (H.dividerCount + (1 : ℕ))),
                         TreeSequenceInitialSegment (H.stage j.castSucc) A)
                       (coreInsideA : TreeSequenceVertexSet base.core ⊆ TreeSequenceVertexSet A)
                       (starredEq :
                        ∀ (j : Fin (H.dividerCount + (1 : ℕ))),
                         HierarchyStarredStage K j = HierarchyStarredStage H j)
                       (terminalColors :
                        corrT.replacementETT.series.data.kind
                           (Fin.last corrT.replacementETT.rounds) =
                          ett.series.data.kind n ∧
                         TashkinovStoredColors corrT.replacementETT.series.data
                           (Fin.last corrT.replacementETT.rounds) =
                          TashkinovStoredColors ett.series.data n)
                       (storedEq :
                        ∀ (j : Fin (H.dividerCount + (1 : ℕ))),
                         HierarchyStoredColorsAt K j = HierarchyStoredColorsAt H j)
                       (stageMissingEq :
                        ∀ (j : Fin (H.dividerCount + (1 : ℕ))),
                         HierarchyStageMissingColors K j = HierarchyStageMissingColors H j),
                       (∀ (c : Fin k),
                         HierarchyFirstMissingPosition sigma T c =
                          HierarchyFirstMissingPosition phi T c) →
                        ∀
                         (segmentEq :
                          ∀ (j : Fin (H.dividerCount + (1 : ℕ))) (c : Fin k),
                           HierarchySegmentColors K j c = HierarchySegmentColors H j c),
                         (∀ (B : TreeSequence G e0),
                           TreeSequenceVertexSet B ⊆ TreeSequenceVertexSet A →
                            ∀ (c : Fin k),
                             BoundaryColorEdges G sigma (TreeSequenceVertexSet B) c =
                              BoundaryColorEdges G phi (TreeSequenceVertexSet B) c) →
                          ∀
                           (minusEq :
                            ∀ (B : TreeSequence G e0),
                             TreeSequenceVertexSet B ⊆ TreeSequenceVertexSet A →
                              ∀ (R : Finset (Fin k)),
                               TreeColorSetMinusClosed G sigma B R ↔
                                TreeColorSetMinusClosed G phi B R)
                           (closureEq :
                            corrT.replacementETT.series.data.kind
                               (Fin.last corrT.replacementETT.rounds) =
                              some TashkinovExtensionKind.PE →
                             baseT.closure = base.closure),
                           let _ : GoodHierarchy K :=
                            {
                             gamma := C.good.gamma,
                             twoColors :=
                              fun (j : Fin (K.dividerCount + (1 : ℕ))) (c : Fin k)
                               (hc : c ∈ HierarchyStoredColorsAt K j) ↦
                              C.good.twoColors j c
                               (Eq.mp (congrArg (fun (_a : Finset (Fin k)) ↦ c ∈ _a) (storedEq j))
                                hc),
                             avoidance :=
                              fun (j : Fin (K.dividerCount + (1 : ℕ))) (c : Fin k)
                               (hc : c ∈ HierarchyStoredColorsAt K j) ↦
                              Eq.mpr
                               (id
                                (congrArg
                                 (fun (_a : Finset (Fin k)) ↦
                                  C.good.gamma j c ⊆ _a \ HierarchySegmentColors K j c)
                                 (stageMissingEq j)))
                               (Eq.mpr
                                (id
                                 (congrArg
                                  (fun (_a : Finset (Fin k)) ↦
                                   C.good.gamma j c ⊆ HierarchyStageMissingColors H j \ _a)
                                  (segmentEq j c)))
                                (C.good.avoidance j c
                                 (Eq.mp (congrArg (fun (_a : Finset (Fin k)) ↦ c ∈ _a) (storedEq j))
                                  hc))),
                             disjointPairs :=
                              fun (j : Fin (K.dividerCount + (1 : ℕ))) (c d : Fin k)
                               (hc : c ∈ HierarchyStoredColorsAt K j)
                               (hd : d ∈ HierarchyStoredColorsAt K j) (hne : c ≠ d) ↦
                              C.good.disjointPairs j c d
                               (Eq.mp (congrArg (fun (_a : Finset (Fin k)) ↦ c ∈ _a) (storedEq j))
                                hc)
                               (Eq.mp (congrArg (fun (_a : Finset (Fin k)) ↦ d ∈ _a) (storedEq j))
                                hd)
                               hne,
                             uniqueRefresh := fun (a : Fin K.dividerCount) ↦
                              have hnew :
                               ((TreeSequenceVertexSet (H.stage a.succ.castSucc) \
                                   TreeSequenceVertexSet
                                    (HierarchyStarredStage H a.castSucc)).biUnion
                                 fun (v : V) ↦ MissingColors G sigma v) =
                                (TreeSequenceVertexSet (H.stage a.succ.castSucc) \
                                   TreeSequenceVertexSet
                                    (HierarchyStarredStage H a.castSucc)).biUnion
                                 fun (v : V) ↦ MissingColors G phi v :=
                               helper_hnew_2064 G k e0 input T phi ett base C alpha theta hstableA
                                corrT baseT hcoreT hterminalTree stageInsideA a;
                              id
                               (Eq.mpr
                                (id
                                 (congrArg
                                  (fun (_a : TreeSequence G e0) ↦
                                   ∃! c : Fin k,
                                    c ∈ HierarchyStoredColorsAt K a.succ ∧
                                     (C.good.gamma a.succ c ⊆
                                       (TreeSequenceVertexSet (H.stage a.succ.castSucc) \
                                          TreeSequenceVertexSet _a).biUnion
                                        fun (v : V) ↦ MissingColors G sigma v) ∧
                                      ∀ d ∈ HierarchyStoredColorsAt K a.succ,
                                       d ≠ c → C.good.gamma a.succ d = C.good.gamma a.castSucc d)
                                  (starredEq a.castSucc)))
                                (Eq.mpr
                                 (id
                                  (congrArg
                                   (fun (_a : Finset (Fin k)) ↦
                                    ∃! c : Fin k,
                                     c ∈ HierarchyStoredColorsAt K a.succ ∧
                                      C.good.gamma a.succ c ⊆ _a ∧
                                       ∀ d ∈ HierarchyStoredColorsAt K a.succ,
                                        d ≠ c → C.good.gamma a.succ d = C.good.gamma a.castSucc d)
                                   hnew))
                                 (Eq.mpr
                                  (id
                                   (congrArg ExistsUnique
                                    (funext fun (c : Fin k) ↦
                                     congr
                                      (congrArg And
                                       (congrFun'
                                        (congrArg Membership.mem
                                         ((fun (j : Fin (H.dividerCount + (1 : ℕ))) ↦ storedEq j)
                                          a.succ))
                                        c))
                                      (congrArg
                                       (And
                                        (C.good.gamma a.succ c ⊆
                                         (TreeSequenceVertexSet (H.stage a.succ.castSucc) \
                                            TreeSequenceVertexSet
                                             (HierarchyStarredStage H a.castSucc)).biUnion
                                          fun (v : V) ↦ MissingColors G phi v))
                                       (forall_congr fun (d : Fin k) ↦
                                        implies_congr
                                         (congrFun'
                                          (congrArg Membership.mem
                                           ((fun (j : Fin (H.dividerCount + (1 : ℕ))) ↦ storedEq j)
                                            a.succ))
                                          d)
                                         (Eq.refl
                                          (d ≠ c →
                                           C.good.gamma a.succ d = C.good.gamma a.castSucc d)))))))
                                  (C.good.uniqueRefresh a)))),
                             parallelBase :=
                              id
                               fun
                                (hpe :
                                 corrT.replacementETT.series.data.kind
                                   (Fin.last corrT.replacementETT.rounds) =
                                  some TashkinovExtensionKind.PE) ↦
                               have hpeOld :
                                ett.series.data.kind n = some TashkinovExtensionKind.PE :=
                                Eq.mpr
                                 (id
                                  (congrArg
                                   (fun (_a : Option TashkinovExtensionKind) ↦
                                    _a = some TashkinovExtensionKind.PE)
                                   (Eq.symm terminalColors.left)))
                                 hpe;
                               have hcl :
                                TreeSequenceVertexSet base.closure ⊆ TreeSequenceVertexSet A :=
                                And.casesOn (base.parallel hpeOld)
                                 fun
                                  (_ :
                                   ett.series.data.chosenVertex (Fin.last ett.rounds) =
                                    some
                                     ((ett.series.data.tree (Fin.last ett.rounds).castSucc).vertex
                                      base.supportPosition))
                                  (right :
                                   TashkinovClosure phi
                                     (TreeSequencePrefix
                                      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
                                      (↑base.supportPosition : ℕ) base.supportPositive
                                      (Nat.le_of_lt_succ base.supportPosition.isLt))
                                     base.closure ∧
                                    Nonempty
                                     (OrderedTreeUnion
                                      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
                                      base.closure base.core)) ↦
                                 And.casesOn right
                                  fun
                                   (_ :
                                    TashkinovClosure phi
                                     (TreeSequencePrefix
                                      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
                                      (↑base.supportPosition : ℕ) base.supportPositive
                                      (Nat.le_of_lt_succ base.supportPosition.isLt))
                                     base.closure)
                                   (right :
                                    Nonempty
                                     (OrderedTreeUnion
                                      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
                                      base.closure base.core)) ↦
                                  Nonempty.casesOn right
                                   fun
                                    (ordered :
                                     OrderedTreeUnion
                                      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
                                      base.closure base.core)
                                    ⦃v : V⦄ (hv : v ∈ TreeSequenceVertexSet base.closure) ↦
                                   coreInsideA
                                    (Eq.mpr
                                     (id
                                      (congrArg (fun (_a : Finset V) ↦ v ∈ _a) ordered.vertexSet))
                                     (Finset.mem_union_right
                                      (TreeSequenceVertexSet
                                       (ett.series.data.tree (Fin.last ett.rounds).castSucc))
                                      hv));
                               And.casesOn (C.good.parallelBase hpeOld)
                                fun
                                 (hnot :
                                  ¬TreeColorSetMinusClosed G phi base.core
                                    ((HierarchyStoredColorsAt C.hierarchy
                                       (0 : Fin (C.hierarchy.dividerCount + (1 : ℕ)))).biUnion
                                     (C.good.gamma (0 : Fin (C.hierarchy.dividerCount + (1 : ℕ))))))
                                 (hcard :
                                  (4 : ℕ) ≤
                                   ((TreeMissingColors phi
                                       (ett.series.data.tree (Fin.last ett.rounds).castSucc) ∩
                                      TreeMissingColors phi base.closure) \
                                     (HierarchyStoredColorsAt C.hierarchy
                                        (0 : Fin (C.hierarchy.dividerCount + (1 : ℕ)))).biUnion
                                      (C.good.gamma
                                       (0 : Fin (C.hierarchy.dividerCount + (1 : ℕ))))).card) ↦
                                (⟨id
                                   (Eq.mpr
                                    (id
                                     (congrArg
                                      (fun (_a : TreeSequence G e0) ↦
                                       ¬TreeColorSetMinusClosed G sigma _a
                                         ((HierarchyStoredColorsAt K
                                            (0 : Fin (K.dividerCount + (1 : ℕ)))).biUnion
                                          (C.good.gamma
                                           (0 : Fin (C.hierarchy.dividerCount + (1 : ℕ))))))
                                      hcoreT))
                                    (Eq.mpr
                                     (id
                                      (congrArg
                                       (fun (_a : Finset (Fin k)) ↦
                                        ¬TreeColorSetMinusClosed G sigma base.core
                                          (_a.biUnion
                                           (C.good.gamma
                                            (0 : Fin (C.hierarchy.dividerCount + (1 : ℕ))))))
                                       (storedEq (0 : Fin (H.dividerCount + (1 : ℕ))))))
                                     (Eq.mpr
                                      (id
                                       (congrArg (fun (_a : Prop) ↦ ¬_a)
                                        (propext
                                         (minusEq base.core coreInsideA
                                          ((HierarchyStoredColorsAt H
                                             (0 : Fin (H.dividerCount + (1 : ℕ)))).biUnion
                                           (C.good.gamma
                                            (0 : Fin (C.hierarchy.dividerCount + (1 : ℕ)))))))))
                                      hnot))),
                                  id
                                   (Eq.mpr
                                    (id
                                     (congrArg
                                      (fun (_a : TreeSequence G e0) ↦
                                       (4 : ℕ) ≤
                                        ((TreeMissingColors sigma _a ∩
                                           TreeMissingColors sigma baseT.closure) \
                                          (HierarchyStoredColorsAt K
                                             (0 : Fin (K.dividerCount + (1 : ℕ)))).biUnion
                                           (C.good.gamma
                                            (0 : Fin (C.hierarchy.dividerCount + (1 : ℕ))))).card)
                                      hterminalTree))
                                    (Eq.mpr
                                     (id
                                      (congrArg
                                       (fun (_a : TreeSequence G e0) ↦
                                        (4 : ℕ) ≤
                                         ((TreeMissingColors sigma Tn ∩
                                            TreeMissingColors sigma _a) \
                                           (HierarchyStoredColorsAt K
                                              (0 : Fin (K.dividerCount + (1 : ℕ)))).biUnion
                                            (C.good.gamma
                                             (0 : Fin (C.hierarchy.dividerCount + (1 : ℕ))))).card)
                                       (closureEq hpe)))
                                     (Eq.mpr
                                      (id
                                       (congrArg
                                        (fun (_a : Finset (Fin k)) ↦
                                         (4 : ℕ) ≤
                                          ((TreeMissingColors sigma Tn ∩
                                             TreeMissingColors sigma base.closure) \
                                            _a.biUnion
                                             (C.good.gamma
                                              (0 : Fin (C.hierarchy.dividerCount + (1 : ℕ))))).card)
                                        (storedEq (0 : Fin (H.dividerCount + (1 : ℕ))))))
                                      (Eq.mpr
                                       (id
                                        (congrArg
                                         (fun (_a : Finset (Fin k)) ↦
                                          (4 : ℕ) ≤
                                           ((_a ∩ TreeMissingColors sigma base.closure) \
                                             (HierarchyStoredColorsAt H
                                                (0 : Fin (H.dividerCount + (1 : ℕ)))).biUnion
                                              (C.good.gamma
                                               (0 :
                                                Fin (C.hierarchy.dividerCount + (1 : ℕ))))).card)
                                         (missingTree Tn
                                          (TreeSequenceInitialSegmentVertexSetSubset hTnA))))
                                       (Eq.mpr
                                        (id
                                         (congrArg
                                          (fun (_a : Finset (Fin k)) ↦
                                           (4 : ℕ) ≤
                                            ((TreeMissingColors phi Tn ∩ _a) \
                                              (HierarchyStoredColorsAt H
                                                 (0 : Fin (H.dividerCount + (1 : ℕ)))).biUnion
                                               (C.good.gamma
                                                (0 :
                                                 Fin (C.hierarchy.dividerCount + (1 : ℕ))))).card)
                                          (missingTree base.closure hcl)))
                                        hcard)))))⟩ :
                                 ¬TreeColorSetMinusClosed G sigma baseT.core
                                    ((HierarchyStoredColorsAt K
                                       (0 : Fin (K.dividerCount + (1 : ℕ)))).biUnion
                                     (C.good.gamma (0 : Fin (K.dividerCount + (1 : ℕ))))) ∧
                                  (4 : ℕ) ≤
                                   ((TreeMissingColors sigma
                                       (corrT.replacementETT.series.data.tree
                                        (Fin.last corrT.replacementETT.rounds).castSucc) ∩
                                      TreeMissingColors sigma baseT.closure) \
                                     (HierarchyStoredColorsAt K
                                        (0 : Fin (K.dividerCount + (1 : ℕ)))).biUnion
                                      (C.good.gamma (0 : Fin (K.dividerCount + (1 : ℕ))))).card),
                             minusClosed := fun (a : Fin K.dividerCount) ↦
                              id
                               (Eq.mpr
                                (id
                                 (congrArg
                                  (fun (_a : Finset (Fin k)) ↦
                                   TreeColorSetMinusClosed G sigma (H.stage a.succ.castSucc)
                                    (_a.biUnion (C.good.gamma a.castSucc)))
                                  (storedEq a.succ)))
                                (Eq.mpr
                                 (id
                                  (congrArg (fun (_a : Prop) ↦ _a)
                                   (propext
                                    (minusEq (H.stage a.succ.castSucc)
                                     (TreeSequenceInitialSegmentVertexSetSubset
                                      (stageInsideA a.succ))
                                     ((HierarchyStoredColorsAt H a.succ).biUnion
                                      (C.good.gamma a.castSucc))))))
                                 (C.good.minusClosed a))) :
                             GoodHierarchy K };
                           False

private abbrev helperContinuation2177Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base) (_ : IsProperEdgeColoring G phi)
   (_ : LowerRoundInductionHypothesis G k e0 ett.rounds)
   (_ :
    (∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
     {generating' : PartialEdgeColoring E k}
     (other : ExtendedTashkinovTree G k e0 input' T' generating') (_ : other.rounds = ett.rounds)
     (_ : MaximumProperty other) (base' : HierarchyBase other generating')
     (K : TashkinovHierarchy other base') (_ : GoodHierarchy K)
     (_ : K.dividerCount < C.hierarchy.dividerCount),
     ColoredVertexSetElementary G generating' (TreeSequenceVertexSet T')))
   (_ :
    (∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
     {generating' : PartialEdgeColoring E k}
     {other : ExtendedTashkinovTree G k e0 input' T' generating'}
     {base' : HierarchyBase other generating'} (C' : HierarchyCounterexample base')
     (_ : other.rounds = ett.rounds) (_ : C'.hierarchy.dividerCount = C.hierarchy.dividerCount),
     ¬HierarchyCounterexampleLess (HierarchyCounterexampleMeasure C')
       (HierarchyCounterexampleMeasure C)))
   (_ :
    (let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    (2 : ℕ) * ett.rounds + (11 : ℕ) ≤ (TreeMissingColors phi Tn).card))
   (hpositive : (0 : ℕ) < C.hierarchy.dividerCount),
   let H : TashkinovHierarchy ett base := C.hierarchy;
   let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
   let i : Fin H.dividerCount :=
    (⟨H.dividerCount - (1 : ℕ),
      id
       (fun (hpositive : (0 : ℕ) < H.dividerCount) ↦
        Decidable.byContradiction fun (a : ¬H.dividerCount - (1 : ℕ) < H.dividerCount) ↦ by omega)
       hpositive⟩ :
     Fin H.dividerCount);
   let A : TreeSequence G e0 := HierarchyStarredStage H q;
   let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
   let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
   ∀ (hlen : T.length = A.length + (1 : ℕ))
    (_ :
     (∀ {X Y Z : TreeSequence G e0} (_ : TreeSequenceInitialSegment X Z)
      (_ : TreeSequenceInitialSegment Y Z) (_ : X.length ≤ Y.length),
      TreeSequenceInitialSegment X Y))
    (_ :
     (∀ {X Y : TreeSequence G e0} (_ : TreeSequenceInitialSegment X Y) (_ : X.length = Y.length),
      X = Y))
    (_ : TreeSequenceInitialSegment A T)
    (_ :
     (∀ (a b : Fin (H.dividerCount + (2 : ℕ))) (_ : (↑a : ℕ) ≤ (↑b : ℕ)),
      TreeSequenceInitialSegment (H.stage a) (H.stage b)))
    (_ : TreeSequenceInitialSegment Tn A)
    (_ :
     (∀ (m : ℕ) (hm : (1 : ℕ) ≤ m) (hmT : m ≤ T.length),
      TreeSequenceInitialSegment (TreeSequencePrefix T m hm hmT) T))
    (_ : ColoredVertexSetElementary G phi (TreeSequenceVertexSet A)),
    let r : Fin T.length := (⟨A.length, by omega⟩ : Fin T.length);
    let f : E := T.edge r;
    let y : V := T.vertex (Fin.last T.length);
    ∀ (_ : y ∉ TreeSequenceVertexSet A),
     ∀ alpha ∈ TreeMissingColors phi A,
      alpha ∈ MissingColors G phi y →
       ∀ gamma ∈ TreeMissingColors phi A,
        phi f = some gamma →
         (∃ u ∈ TreeSequenceVertexSet A, G.ends f = s(u, y)) →
          ∀ (eta : Fin k),
           (C.good.gamma i.succ eta).card = (2 : ℕ) →
            ∀ theta ∈ C.good.gamma i.succ eta,
             (theta ∈
               (TreeSequenceVertexSet (C.hierarchy.stage i.succ.castSucc) \
                  TreeSequenceVertexSet (HierarchyStarredStage C.hierarchy i.castSucc)).biUnion
                fun (v : V) ↦ MissingColors G phi v) →
              ∀ (x : V),
               theta ∈ MissingColors G phi x →
                theta ∈ TreeMissingColors phi A →
                 TreeColorSetClosed G phi A { theta } →
                  theta ≠ gamma →
                   (∀ (psi : PartialEdgeColoring E k),
                     IsProperEdgeColoring G psi →
                      ∀ (c d : Fin k),
                       c ≠ d →
                        c ∈ TreeMissingColors psi A →
                         d ∈ TreeMissingColors psi A →
                          ∀ w ∉ TreeSequenceVertexSet A,
                           c ∈ MissingColors G psi w ∨ d ∈ MissingColors G psi w →
                            TreeInterchangeable G A psi c d →
                             ∀ v ∈ TreeSequenceVertexSet A,
                              Sum.inl v ∉ TwoColorComponent G psi c d (Sum.inl w)) →
                    (∀ (beta : Fin k), theta ≠ beta → TreeInterchangeable G A phi theta beta) →
                     theta ≠ alpha →
                      (∀ v ∈ TreeSequenceVertexSet A,
                        Sum.inl v ∉ TwoColorComponent G phi theta alpha (Sum.inl y)) →
                       let sigma : PartialEdgeColoring E k :=
                        TwoColorComponentSwap G phi theta alpha (Sum.inl y);
                       OutsideKempeRecoloring A phi sigma theta alpha →
                        (IsProperEdgeColoring G sigma ∧
                          IsOneEdgeUncolored sigma e0 ∧
                           StableColoring A (TashkinovStoredColors ett.series.data n) phi sigma ∧
                            TreeColoringInvariant A phi sigma ∧
                             ∀ (f : E), TreeIncidentEdge A f → sigma f = phi f) →
                         (∀ c ∈ TreeMissingColors phi A,
                           c ∈
                             MissingColors G phi
                              (T.vertex (HierarchyFirstMissingPosition phi T c)) ∧
                            T.vertex (HierarchyFirstMissingPosition phi T c) ∈
                             TreeSequenceVertexSet A) →
                          StableColoring Tn (TashkinovStoredColors ett.series.data n)
                            (ett.series.data.coloring n) sigma →
                           ModColoring ett sigma →
                            (∀ (t : Fin T.length), sigma (T.edge t) = phi (T.edge t)) →
                             (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
                                TashkinovAugmentationSequence sigma Tn T ∨
                               (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
                                 ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
                                ∃ (edge : E) (seed : TreeSequence G e0),
                                 ett.series.data.connectingEdges n = { edge } ∧
                                  TreeSequenceAdjoinEdge Tn edge seed ∧
                                   TashkinovAugmentationSequence sigma seed T) →
                              ∀ (corrT : CorrespondingExtendedTashkinovTree G k e0 ett sigma T),
                               MaximumProperty corrT.replacementETT →
                                ¬ColoredVertexSetElementary G sigma (TreeSequenceVertexSet T) →
                                 OutsideKempeRecoloring (H.stage q.castSucc) phi sigma theta alpha →
                                  ∀ (positivePrefix : (1 : ℕ) ≤ ett.rounds)
                                   (abovePrefix :
                                    TreeSequenceInitialSegment
                                     (ett.series.data.tree
                                      (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + (2 : ℕ))))
                                     (H.stage q.castSucc))
                                   (strictPrefix :
                                    (ett.series.data.tree
                                       (⟨ett.rounds, by omega⟩ :
                                        Fin (ett.rounds + (2 : ℕ)))).length <
                                     (H.stage q.castSucc).length)
                                   (belowPrefix :
                                    TreeSequenceInitialSegment (H.stage q.castSucc)
                                     (ett.series.data.tree (Fin.last (ett.rounds + (1 : ℕ)))))
                                   (generatingPrefix :
                                    phi = ett.series.data.coloring (Fin.last ett.rounds))
                                   (basePrefix :
                                    HierarchyBase
                                     {
                                      rounds := ett.rounds, roundsPositive := positivePrefix,
                                      series := ett.series, abovePenultimate := abovePrefix,
                                      strictAbovePenultimate := strictPrefix,
                                      belowFinal := belowPrefix,
                                      generatingColoring := generatingPrefix :
                                      ExtendedTashkinovTree G k e0 input (H.stage q.castSucc) phi }
                                     phi),
                                   basePrefix.closure = base.closure →
                                    ∀
                                     (HP :
                                      TashkinovHierarchy
                                       {
                                        rounds := ett.rounds, roundsPositive := positivePrefix,
                                        series := ett.series, abovePenultimate := abovePrefix,
                                        strictAbovePenultimate := strictPrefix,
                                        belowFinal := belowPrefix,
                                        generatingColoring := generatingPrefix :
                                        ExtendedTashkinovTree G k e0 input (H.stage q.castSucc)
                                         phi }
                                       basePrefix)
                                     (goodPrefix : GoodHierarchy HP),
                                     (have n :
                                       Fin
                                        ({ rounds := ett.rounds, roundsPositive := positivePrefix,
                                           series := ett.series, abovePenultimate := abovePrefix,
                                           strictAbovePenultimate := strictPrefix,
                                           belowFinal := belowPrefix,
                                           generatingColoring := generatingPrefix :
                                           ExtendedTashkinovTree G k e0 input (H.stage q.castSucc)
                                            phi }.rounds +
                                         (1 : ℕ)) :=
                                       Fin.last
                                        { rounds := ett.rounds, roundsPositive := positivePrefix,
                                          series := ett.series, abovePenultimate := abovePrefix,
                                          strictAbovePenultimate := strictPrefix,
                                          belowFinal := belowPrefix,
                                          generatingColoring := generatingPrefix :
                                          ExtendedTashkinovTree G k e0 input (H.stage q.castSucc)
                                           phi }.rounds;
                                      have Dn : Finset (Fin k) :=
                                       TashkinovStoredColors
                                        { rounds := ett.rounds, roundsPositive := positivePrefix,
                                          series := ett.series, abovePenultimate := abovePrefix,
                                          strictAbovePenultimate := strictPrefix,
                                          belowFinal := belowPrefix,
                                          generatingColoring := generatingPrefix :
                                          ExtendedTashkinovTree G k e0 input (H.stage q.castSucc)
                                           phi }.series.data
                                        n;
                                      IsProperEdgeColoring G sigma ∧
                                       IsOneEdgeUncolored sigma e0 ∧
                                        StableColoring (H.stage q.castSucc) Dn phi sigma ∧
                                         TreeColoringInvariant (H.stage q.castSucc) phi sigma ∧
                                          ∃ (corr :
                                           CorrespondingExtendedTashkinovTree G k e0
                                            {
                                             rounds := ett.rounds,
                                             roundsPositive := positivePrefix, series := ett.series,
                                             abovePenultimate := abovePrefix,
                                             strictAbovePenultimate := strictPrefix,
                                             belowFinal := belowPrefix,
                                             generatingColoring := generatingPrefix :
                                             ExtendedTashkinovTree G k e0 input (H.stage q.castSucc)
                                              phi }
                                            sigma (H.stage q.castSucc)),
                                           MaximumProperty corr.replacementETT ∧
                                            ∃ (baseSigma : HierarchyBase corr.replacementETT sigma)
                                             (K : TashkinovHierarchy corr.replacementETT baseSigma)
                                             (goodSigma : GoodHierarchy K),
                                             SameGoodHierarchy goodPrefix goodSigma ∧
                                              (TreeColorSetMinusClosed G phi (H.stage q.castSucc)
                                                ((HierarchyTerminalStoredColors HP).biUnion
                                                 (goodPrefix.gamma (Fin.last HP.dividerCount))) →
                                               TreeColorSetMinusClosed G sigma (H.stage q.castSucc)
                                                ((HierarchyTerminalStoredColors HP).biUnion
                                                 (goodPrefix.gamma (Fin.last HP.dividerCount))))) →
                                      ∀
                                       (corrPrefix :
                                        CorrespondingExtendedTashkinovTree G k e0
                                         {
                                          rounds := ett.rounds, roundsPositive := positivePrefix,
                                          series := ett.series, abovePenultimate := abovePrefix,
                                          strictAbovePenultimate := strictPrefix,
                                          belowFinal := belowPrefix,
                                          generatingColoring := generatingPrefix :
                                          ExtendedTashkinovTree G k e0 input (H.stage q.castSucc)
                                           phi }
                                         sigma (H.stage q.castSucc)),
                                       MaximumProperty corrPrefix.replacementETT →
                                        ∀
                                         (basePrefixSigma :
                                          HierarchyBase corrPrefix.replacementETT sigma)
                                         (KP :
                                          TashkinovHierarchy corrPrefix.replacementETT
                                           basePrefixSigma)
                                         (goodPrefixSigma : GoodHierarchy KP),
                                         SameGoodHierarchy goodPrefix goodPrefixSigma →
                                          (TreeColorSetMinusClosed G phi (H.stage q.castSucc)
                                             ((HierarchyTerminalStoredColors HP).biUnion
                                              (goodPrefix.gamma (Fin.last HP.dividerCount))) →
                                            TreeColorSetMinusClosed G sigma (H.stage q.castSucc)
                                             ((HierarchyTerminalStoredColors HP).biUnion
                                              (goodPrefix.gamma (Fin.last HP.dividerCount)))) →
                                           let _ :
                                            CorrespondingExtendedTashkinovTree G k e0 ett sigma
                                             (H.stage q.castSucc) :=
                                            {
                                             replacementInput := corrPrefix.replacementInput,
                                             replacementSeries := corrPrefix.replacementSeries,
                                             replacementETT := corrPrefix.replacementETT,
                                             rungAgreement := corrPrefix.rungAgreement,
                                             seriesPresentation := corrPrefix.seriesPresentation,
                                             finalGeneratingColoring :=
                                              corrPrefix.finalGeneratingColoring,
                                             ladderTreesAgree := corrPrefix.ladderTreesAgree,
                                             storedColorsAgree := corrPrefix.storedColorsAgree,
                                             connectingEdgesAgree :=
                                              corrPrefix.connectingEdgesAgree,
                                             extensionKindsAgree := corrPrefix.extensionKindsAgree,
                                             replacementProper := corrPrefix.replacementProper,
                                             replacementOneUncolored :=
                                              corrPrefix.replacementOneUncolored,
                                             replacementStable := corrPrefix.replacementStable :
                                             CorrespondingExtendedTashkinovTree G k e0 ett sigma
                                              (H.stage q.castSucc) };
                                           ∀ (baseT : HierarchyBase corrT.replacementETT sigma),
                                            baseT.core = basePrefixSigma.core →
                                             baseT.closure = basePrefixSigma.closure →
                                              (↑baseT.supportPosition : ℕ) =
                                                (↑basePrefixSigma.supportPosition : ℕ) →
                                               ∀ (hcoreT : baseT.core = base.core)
                                                (hterminalTree :
                                                 corrT.replacementETT.series.data.tree
                                                   (Fin.last corrT.replacementETT.rounds).castSucc =
                                                  Tn),
                                                let K :
                                                 TashkinovHierarchy corrT.replacementETT baseT :=
                                                 {
                                                  dividerCount := H.dividerCount, stage := H.stage,
                                                  baseStage :=
                                                   Eq.trans H.baseStage (Eq.symm hterminalTree),
                                                  terminalStage := H.terminalStage,
                                                  nested := H.nested, strict := H.strict,
                                                  dividerPosition := H.dividerPosition,
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
                                                         (⟨(1 : ℕ), by omega⟩ :
                                                          Fin (H.dividerCount + (2 : ℕ)))))
                                                      hcoreT))
                                                    H.coreInsideFirst :
                                                  TashkinovHierarchy corrT.replacementETT baseT };
                                                (∀ (B : TreeSequence G e0),
                                                  TreeSequenceVertexSet B ⊆
                                                    TreeSequenceVertexSet A →
                                                   TreeMissingColors sigma B =
                                                    TreeMissingColors phi B) →
                                                 (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
                                                   TreeSequenceInitialSegment (H.stage j.castSucc)
                                                    A) →
                                                  TreeSequenceVertexSet base.core ⊆
                                                    TreeSequenceVertexSet A →
                                                   (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
                                                     HierarchyStarredStage K j =
                                                      HierarchyStarredStage H j) →
                                                    corrT.replacementETT.series.data.kind
                                                        (Fin.last corrT.replacementETT.rounds) =
                                                       ett.series.data.kind n ∧
                                                      TashkinovStoredColors
                                                        corrT.replacementETT.series.data
                                                        (Fin.last corrT.replacementETT.rounds) =
                                                       TashkinovStoredColors ett.series.data n →
                                                     (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
                                                       HierarchyStoredColorsAt K j =
                                                        HierarchyStoredColorsAt H j) →
                                                      False

private abbrev helperContinuation2110Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base) (_ : IsProperEdgeColoring G phi)
   (_ : IsOneEdgeUncolored phi e0) (_ : LowerRoundInductionHypothesis G k e0 ett.rounds)
   (_ :
    (∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
     {generating' : PartialEdgeColoring E k}
     (other : ExtendedTashkinovTree G k e0 input' T' generating') (_ : other.rounds = ett.rounds)
     (_ : MaximumProperty other) (base' : HierarchyBase other generating')
     (K : TashkinovHierarchy other base') (_ : GoodHierarchy K)
     (_ : K.dividerCount < C.hierarchy.dividerCount),
     ColoredVertexSetElementary G generating' (TreeSequenceVertexSet T')))
   (_ :
    (∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
     {generating' : PartialEdgeColoring E k}
     {other : ExtendedTashkinovTree G k e0 input' T' generating'}
     {base' : HierarchyBase other generating'} (C' : HierarchyCounterexample base')
     (_ : other.rounds = ett.rounds) (_ : C'.hierarchy.dividerCount = C.hierarchy.dividerCount),
     ¬HierarchyCounterexampleLess (HierarchyCounterexampleMeasure C')
       (HierarchyCounterexampleMeasure C)))
   (_ :
    (let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    (2 : ℕ) * ett.rounds + (11 : ℕ) ≤ (TreeMissingColors phi Tn).card))
   (hpositive : (0 : ℕ) < C.hierarchy.dividerCount),
   let H : TashkinovHierarchy ett base := C.hierarchy;
   let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
   let i : Fin H.dividerCount :=
    (⟨H.dividerCount - (1 : ℕ),
      id
       (fun (hpositive : (0 : ℕ) < H.dividerCount) ↦
        Decidable.byContradiction fun (a : ¬H.dividerCount - (1 : ℕ) < H.dividerCount) ↦ by omega)
       hpositive⟩ :
     Fin H.dividerCount);
   let A : TreeSequence G e0 := HierarchyStarredStage H q;
   let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
   let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
   ∀ (_ : (0 : ℕ) < H.dividerCount) (_ : A = H.stage q.castSucc)
    (hlen : T.length = A.length + (1 : ℕ))
    (_ :
     (∀ {X Y Z : TreeSequence G e0} (_ : TreeSequenceInitialSegment X Y)
      (_ : TreeSequenceInitialSegment Y Z), TreeSequenceInitialSegment X Z))
    (_ :
     (∀ {X Y Z : TreeSequence G e0} (_ : TreeSequenceInitialSegment X Z)
      (_ : TreeSequenceInitialSegment Y Z) (_ : X.length ≤ Y.length),
      TreeSequenceInitialSegment X Y))
    (_ :
     (∀ {X Y : TreeSequence G e0} (_ : TreeSequenceInitialSegment X Y) (_ : X.length = Y.length),
      X = Y))
    (_ : TreeSequenceInitialSegment A T)
    (_ :
     (∀ (a b : Fin (H.dividerCount + (2 : ℕ))) (_ : (↑a : ℕ) ≤ (↑b : ℕ)),
      TreeSequenceInitialSegment (H.stage a) (H.stage b)))
    (_ : TreeSequenceInitialSegment Tn A)
    (_ :
     (∀ (m : ℕ) (hm : (1 : ℕ) ≤ m) (hmT : m ≤ T.length),
      TreeSequenceInitialSegment (TreeSequencePrefix T m hm hmT) T))
    (_ : ColoredVertexSetElementary G phi (TreeSequenceVertexSet A)),
    let r : Fin T.length := (⟨A.length, by omega⟩ : Fin T.length);
    let f : E := T.edge r;
    let y : V := T.vertex (Fin.last T.length);
    ∀ (_ : y ∉ TreeSequenceVertexSet A),
     ∀ alpha ∈ TreeMissingColors phi A,
      alpha ∈ MissingColors G phi y →
       ∀ gamma ∈ TreeMissingColors phi A,
        phi f = some gamma →
         (∃ u ∈ TreeSequenceVertexSet A, G.ends f = s(u, y)) →
          ∀ (eta : Fin k),
           (C.good.gamma i.succ eta).card = (2 : ℕ) →
            ∀ theta ∈ C.good.gamma i.succ eta,
             (theta ∈
               (TreeSequenceVertexSet (C.hierarchy.stage i.succ.castSucc) \
                  TreeSequenceVertexSet (HierarchyStarredStage C.hierarchy i.castSucc)).biUnion
                fun (v : V) ↦ MissingColors G phi v) →
              ∀ (x : V),
               theta ∈ MissingColors G phi x →
                theta ∈ TreeMissingColors phi A →
                 TreeColorSetClosed G phi A { theta } →
                  theta ≠ gamma →
                   (∀ (psi : PartialEdgeColoring E k),
                     IsProperEdgeColoring G psi →
                      ∀ (c d : Fin k),
                       c ≠ d →
                        c ∈ TreeMissingColors psi A →
                         d ∈ TreeMissingColors psi A →
                          ∀ w ∉ TreeSequenceVertexSet A,
                           c ∈ MissingColors G psi w ∨ d ∈ MissingColors G psi w →
                            TreeInterchangeable G A psi c d →
                             ∀ v ∈ TreeSequenceVertexSet A,
                              Sum.inl v ∉ TwoColorComponent G psi c d (Sum.inl w)) →
                    (∀ (beta : Fin k), theta ≠ beta → TreeInterchangeable G A phi theta beta) →
                     theta ≠ alpha →
                      (∀ v ∈ TreeSequenceVertexSet A,
                        Sum.inl v ∉ TwoColorComponent G phi theta alpha (Sum.inl y)) →
                       let sigma : PartialEdgeColoring E k :=
                        TwoColorComponentSwap G phi theta alpha (Sum.inl y);
                       OutsideKempeRecoloring A phi sigma theta alpha →
                        (IsProperEdgeColoring G sigma ∧
                          IsOneEdgeUncolored sigma e0 ∧
                           StableColoring A (TashkinovStoredColors ett.series.data n) phi sigma ∧
                            TreeColoringInvariant A phi sigma ∧
                             ∀ (f : E), TreeIncidentEdge A f → sigma f = phi f) →
                         (∀ c ∈ TreeMissingColors phi A,
                           c ∈
                             MissingColors G phi
                              (T.vertex (HierarchyFirstMissingPosition phi T c)) ∧
                            T.vertex (HierarchyFirstMissingPosition phi T c) ∈
                             TreeSequenceVertexSet A) →
                          StableColoring Tn (TashkinovStoredColors ett.series.data n)
                            (ett.series.data.coloring n) sigma →
                           ModColoring ett sigma →
                            (∀ (t : Fin T.length), sigma (T.edge t) = phi (T.edge t)) →
                             (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
                                TashkinovAugmentationSequence sigma Tn T ∨
                               (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
                                 ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
                                ∃ (edge : E) (seed : TreeSequence G e0),
                                 ett.series.data.connectingEdges n = { edge } ∧
                                  TreeSequenceAdjoinEdge Tn edge seed ∧
                                   TashkinovAugmentationSequence sigma seed T) →
                              ∀ (corrT : CorrespondingExtendedTashkinovTree G k e0 ett sigma T),
                               MaximumProperty corrT.replacementETT →
                                ¬ColoredVertexSetElementary G sigma (TreeSequenceVertexSet T) →
                                 False

private theorem helper_branch_654.{u_1, u_2} :
    helperBranch654Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hpositive H q i A n Tn hAT y alpha halphaA
      halphay gamma eta theta hthetaPair hthetaNew x hthetax hthetaA hthetaClosed hthetaGamma
      stepInterchange hthetaAlpha hcomponentOutside sigma hrecolorA hstableA hstableLadder hmod
      hfixedEdges hsigmaRoute corrT hmaximumT hnotElementarySigma hrecolorPrefix positivePrefix
      abovePrefix strictPrefix belowPrefix generatingPrefix basePrefix HP goodPrefix
      hprefixTransport corrPrefix hmaximumPrefixSigma basePrefixSigma KP goodPrefixSigma
      hsamePrefixSigma hminusPrefixSigma baseT hcoreTA hclosureTA hsupportTA hcoreT hterminalTree
      K missingTree starredEq terminalColors storedEq stageMissingEq firstBound c hswap hc
  have hcA : c ∈ TreeMissingColors phi A := by
    rcases hc with rfl | rfl
    · exact hthetaA
    · exact halphaA
  exact TreeSequenceFirstMissingPositionCongrOfPrefix hAT hstableA.2.2.2.1.2 hcA

private theorem helper_firstMissingEq_961.{u_1, u_2} :
    helperFirstMissingEq961Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hproper hpositive H q i A n Tn hAT y alpha
      halphaA halphay gamma eta theta hthetaPair hthetaNew x hthetax hthetaA hthetaClosed
      hthetaGamma stepInterchange hthetaAlpha hcomponentOutside sigma hrecolorA hstableA
      hstableLadder hmod hfixedEdges hsigmaRoute corrT hmaximumT hnotElementarySigma
      hrecolorPrefix positivePrefix abovePrefix strictPrefix belowPrefix generatingPrefix
      basePrefix HP goodPrefix hprefixTransport corrPrefix hmaximumPrefixSigma basePrefixSigma KP
      goodPrefixSigma hsamePrefixSigma hminusPrefixSigma corrA baseT hcoreTA hclosureTA
      hsupportTA hcoreT hterminalTree K missingTree starredEq terminalColors storedEq
      stageMissingEq firstBound c
  have hswap := TwoColorComponentSwapMissingBehavior G phi theta alpha
    hthetaAlpha hproper (Sum.inl y)
  by_cases hc : c = theta ∨ c = alpha
  · exact @helper_branch_654 V E inferInstance inferInstance inferInstance inferInstance G k e0
      input T phi ett base C hpositive hAT alpha halphaA halphay gamma eta theta hthetaPair
      hthetaNew x hthetax hthetaA hthetaClosed hthetaGamma stepInterchange hthetaAlpha
      hcomponentOutside hrecolorA hstableA hstableLadder hmod hfixedEdges hsigmaRoute corrT
      hmaximumT hnotElementarySigma hrecolorPrefix positivePrefix abovePrefix strictPrefix
      belowPrefix generatingPrefix basePrefix HP goodPrefix hprefixTransport corrPrefix
      hmaximumPrefixSigma basePrefixSigma KP goodPrefixSigma hsamePrefixSigma hminusPrefixSigma
      baseT hcoreTA hclosureTA hsupportTA hcoreT hterminalTree missingTree starredEq
      terminalColors storedEq stageMissingEq firstBound c hswap hc
  · apply TreeSequenceFirstMissingPositionMembershipCongr
    intro index
    exact hswap.2.2.2 (T.vertex index) c
      (fun equal => hc (Or.inl equal)) (fun equal => hc (Or.inr equal))
private theorem helper_hvertices_896.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base) (_ : (0 : ℕ) < C.hierarchy.dividerCount),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    ∀ (_ : T.length = A.length + (1 : ℕ)) (_ : TreeSequenceInitialSegment A T),
    let y : V := T.vertex (Fin.last T.length);
    TreeSequenceVertexSet T = insert y (TreeSequenceVertexSet A) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hpositive H q A hlen hAT y
  ext v
  constructor
  · intro hv
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hv
    obtain ⟨j, rfl⟩ := hv
    by_cases hj : j.val ≤ A.length
    · apply Finset.mem_insert_of_mem
      let ja : Fin (A.length + 1) := ⟨j.val, by omega⟩
      have he : Fin.castLE (Nat.succ_le_succ hAT.1) ja = j := Fin.ext rfl
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨ja, by rw [← hAT.2.1 ja, he]⟩
    · have he : j = Fin.last T.length := by
        apply Fin.ext
        simp only [Fin.val_last]
        omega
      rw [he]
      exact Finset.mem_insert_self _ _
  · intro hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨Fin.last T.length, rfl⟩
    · exact TreeSequenceInitialSegmentVertexSetSubset hAT hv

private theorem helper_terminalRoute_936.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (j : Fin (ett.rounds + (1 : ℕ))),
    (0 : ℕ) < (↑j : ℕ) →
    ett.series.data.kind j = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence (ett.series.data.coloring j)
          (ett.series.data.tree j.castSucc) (ett.series.data.tree j.succ) ∨
      (ett.series.data.kind j = some TashkinovExtensionKind.SE ∨
          ett.series.data.kind j = some TashkinovExtensionKind.RE) ∧
        ∃ (edge : E) (seed : TreeSequence G e0),
          ett.series.data.connectingEdges j = { edge } ∧
            TreeSequenceAdjoinEdge (ett.series.data.tree j.castSucc) edge seed ∧
              TashkinovAugmentationSequence (ett.series.data.coloring j) seed
                (ett.series.data.tree j.succ) := by
  classical
  intro V E _ _ _ G k e0 input T phi ett j hj
  have cert := ett.series.certified j
  cases cert with
  | initial => simp at hj
  | SE a previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    exact Or.inr ⟨Or.inl currentKind, choice.edge, adjoined,
      currentEdges, adjoinedExactly, closedExtension.1⟩
  | PE a previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper secondStableOneUncolored
      secondStableRelation exitWitness currentColoring currentProper
      currentOneUncolored currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma closedExtension orderedExtension
      strictExtension =>
    exact Or.inl ⟨currentKind, closedExtension.1⟩
  | RE a previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    exact Or.inr ⟨Or.inr currentKind, available.edge, adjoined,
      currentEdges, adjoinedExactly, closedExtension.1⟩

private theorem helper_hthetaAlpha_1167.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (_ : IsProperEdgeColoring G phi) (_ : (0 : ℕ) < C.hierarchy.dividerCount),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    ∀ (hlen : T.length = A.length + (1 : ℕ)),
    let r : Fin T.length := (⟨A.length, by omega⟩ : Fin T.length);
    let f : E := T.edge r;
    let y : V := T.vertex (Fin.last T.length);
    ∀ (_ : y ∉ TreeSequenceVertexSet A),
    ∀ alpha ∈ MissingColors G phi y,
    ∀ gamma ∈ TreeMissingColors phi A,
    phi f = some gamma →
    (∃ u ∈ TreeSequenceVertexSet A, G.ends f = s(u, y)) →
    ∀ theta ∈ TreeMissingColors phi A,
    theta ≠ gamma →
    (∀ (psi : PartialEdgeColoring E k),
        IsProperEdgeColoring G psi →
          ∀ (c d : Fin k),
            c ≠ d →
              c ∈ TreeMissingColors psi A →
                d ∈ TreeMissingColors psi A →
                  ∀ w ∉ TreeSequenceVertexSet A,
                    c ∈ MissingColors G psi w ∨ d ∈ MissingColors G psi w →
                      TreeInterchangeable G A psi c d →
                        ∀ v ∈ TreeSequenceVertexSet A,
                          Sum.inl v ∉ TwoColorComponent G psi c d (Sum.inl w)) →
    (∀ (beta : Fin k), theta ≠ beta → TreeInterchangeable G A phi theta beta) →
    theta ≠ alpha := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hproper hpositive H q A hlen r f y hyOutside
      alpha halphay gamma hgammaA hgammaf hfEnds theta hthetaA hthetaGamma
      outsideMissingComponent stepInterchange he
  have hthetay : theta ∈ MissingColors G phi y := by rw [he]; exact halphay
  have hout := outsideMissingComponent phi hproper theta gamma hthetaGamma hthetaA hgammaA
    y hyOutside (Or.inl hthetay) (stepInterchange gamma hthetaGamma)
  obtain ⟨u, huA, hends⟩ := hfEnds
  have hyf : (TwoColorIncidenceGraph G phi theta gamma).Adj (Sum.inl y) (Sum.inr f) := by
    refine ⟨?_, Or.inr hgammaf⟩
    change y ∈ G.ends f
    rw [hends]
    exact Sym2.mem_mk_right _ _
  have hfu : (TwoColorIncidenceGraph G phi theta gamma).Adj (Sum.inr f) (Sum.inl u) := by
    refine ⟨?_, Or.inr hgammaf⟩
    change u ∈ G.ends f
    rw [hends]
    exact Sym2.mem_mk_left _ _
  apply hout u huA
  change (TwoColorIncidenceGraph G phi theta gamma).connectedComponentMk (Sum.inl u) =
    (TwoColorIncidenceGraph G phi theta gamma).connectedComponentMk (Sum.inl y)
  exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hfu).symm.trans
    (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hyf).symm

private theorem helper_hfixedEdges_1244.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (_ : (0 : ℕ) < C.hierarchy.dividerCount),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    ∀ (hlen : T.length = A.length + (1 : ℕ)) (_ : TreeSequenceInitialSegment A T),
    let r : Fin T.length := (⟨A.length, by omega⟩ : Fin T.length);
    let f : E := T.edge r;
    let y : V := T.vertex (Fin.last T.length);
    ∀ (alpha : Fin k) (_ : (∃ u ∈ TreeSequenceVertexSet A, G.ends f = s(u, y)))
      (_ theta : Fin k),
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi theta alpha (Sum.inl y);
    ∀
      (_ :
        (IsProperEdgeColoring G sigma ∧
          IsOneEdgeUncolored sigma e0 ∧
            StableColoring A (TashkinovStoredColors ett.series.data n) phi sigma ∧
              TreeColoringInvariant A phi sigma ∧
                ∀ (f : E), TreeIncidentEdge A f → sigma f = phi f))
      (t : Fin T.length),
    sigma (T.edge t) = phi (T.edge t) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hpositive H q A n hlen hAT r f y alpha hfEnds
      eta theta sigma hstableA t
  apply hstableA.2.2.2.2
  by_cases ht : t.val < A.length
  · let ta : Fin A.length := ⟨t.val, ht⟩
    have he : Fin.castLE hAT.1 ta = t := Fin.ext rfl
    obtain ⟨j, hj⟩ := A.attaches ta
    refine ⟨A.vertex ta.succ, ?_, ?_⟩
    · simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨ta.succ, rfl⟩
    · change A.vertex ta.succ ∈ G.ends (T.edge t)
      rw [← he, hAT.2.2 ta, hj]
      exact Sym2.mem_mk_left _ _
  · have he : t = r := by
      apply Fin.ext
      have := t.isLt
      dsimp [r]
      omega
    rw [he]
    obtain ⟨u, huA, hends⟩ := hfEnds
    refine ⟨u, huA, ?_⟩
    change u ∈ G.ends f
    rw [hends]
    exact Sym2.mem_mk_left _ _

private theorem helper_hcommon_1589.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    ∀ (_ : ColoredVertexSetElementary G phi (TreeSequenceVertexSet A)),
    let y : V := T.vertex (Fin.last T.length);
    ∀ (_ : TreeSequenceVertexSet T = insert y (TreeSequenceVertexSet A)),
    ∃ alpha ∈ TreeMissingColors phi A,
    alpha ∈ MissingColors G phi y := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q A hAElem y hvertices
  have hnot := C.notElementary
  unfold ColoredVertexSetElementary at hnot
  push Not at hnot
  obtain ⟨u, hu, v, hv, huv, hdisjoint⟩ := hnot
  obtain ⟨alpha, hau, hav⟩ := Finset.not_disjoint_iff.mp hdisjoint
  rw [hvertices] at hu hv
  rcases Finset.mem_insert.mp hu with rfl | hu
  · have hvA : v ∈ TreeSequenceVertexSet A :=
      (Finset.mem_insert.mp hv).resolve_left (Ne.symm huv)
    exact ⟨alpha, Finset.mem_biUnion.mpr ⟨v, hvA, hav⟩, hau⟩
  · rcases Finset.mem_insert.mp hv with rfl | hv
    · exact ⟨alpha, Finset.mem_biUnion.mpr ⟨u, hu, hau⟩, hav⟩
    · exact False.elim (Finset.disjoint_left.mp (hAElem hu hv huv) hau hav)

private theorem helper_hAtoT_1620.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base) (_ : (0 : ℕ) < C.hierarchy.dividerCount),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Tnext : TreeSequence G e0 := ett.series.data.tree n.succ;
    ∀
      (_ :
        (∀ {X Y Z : TreeSequence G e0} (_ : TreeSequenceInitialSegment X Y)
          (_ : TreeSequenceInitialSegment Y Z), TreeSequenceInitialSegment X Z))
      (_ :
        (∀ {X Y Z : TreeSequence G e0} (_ : TreeSequenceInitialSegment X Z)
          (_ : TreeSequenceInitialSegment Y Z) (_ : X.length ≤ Y.length),
          TreeSequenceInitialSegment X Y))
      (_ : TreeSequenceInitialSegment A T) (_ : TreeSequenceInitialSegment Tn A)
      (_ : Tn.length < A.length) (_ : TreeSequenceInitialSegment T Tnext)
      (_ : TreeSequenceInitialSegment A Tnext)
      (_ :
        (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
            TashkinovAugmentationSequence phi (ett.series.data.tree n.castSucc)
              (ett.series.data.tree n.succ) ∨
          (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
              ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
            ∃ (edge : E) (seed : TreeSequence G e0),
              ett.series.data.connectingEdges n = { edge } ∧
                TreeSequenceAdjoinEdge (ett.series.data.tree n.castSucc) edge seed ∧
                  TashkinovAugmentationSequence phi seed (ett.series.data.tree n.succ))),
    TashkinovAugmentationSequence phi A T := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hpositive H q A n Tn Tnext segmentTrans
      commonPrefix hAT hTnA hTnStrictA hTTnext hATnext hroute
  rcases hroute with ⟨hkind, hseq⟩ | ⟨hkind, edge, seed, hedges, hseed, hseq⟩
  · have hTnT := segmentTrans hTnA hAT
    have htoT := TashkinovAugmentationSequenceRestrict phi Tn T Tnext
      hseq hTnT hTTnext
    exact TashkinovAugmentationSequenceSuffix phi Tn A T htoT hTnA hAT
  · have hseedFinal := TashkinovAugmentationSequenceInitialSegment phi seed Tnext hseq
    have hseedA : TreeSequenceInitialSegment seed A :=
      commonPrefix hseedFinal hATnext (by
        have hseedLen : seed.length = Tn.length + 1 := hseed.1
        omega)
    have hseedT := segmentTrans hseedA hAT
    have htoT := TashkinovAugmentationSequenceRestrict phi seed T Tnext
      hseq hseedT hTTnext
    exact TashkinovAugmentationSequenceSuffix phi seed A T htoT hseedA hAT

private theorem helper_hfEnds_1651.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (_ : (0 : ℕ) < C.hierarchy.dividerCount),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    ∀ (hlen : T.length = A.length + (1 : ℕ)) (_ : TreeSequenceInitialSegment A T),
    let r : Fin T.length := (⟨A.length, by omega⟩ : Fin T.length);
    let f : E := T.edge r;
    let y : V := T.vertex (Fin.last T.length);
    ∃ u ∈ TreeSequenceVertexSet A,
    G.ends f = s(u, y) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hpositive H q A hlen hAT r f y
  obtain ⟨a, ha⟩ := T.attaches r
  let aa : Fin (A.length + 1) := ⟨a.val, by have := a.isLt; dsimp [r] at this; omega⟩
  have hv : T.vertex (Fin.castLT a
      (Nat.lt_trans a.isLt (Nat.succ_lt_succ r.isLt))) = A.vertex aa := by
    have he : Fin.castLT a (Nat.lt_trans a.isLt (Nat.succ_lt_succ r.isLt)) =
        Fin.castLE (Nat.succ_le_succ hAT.1) aa := Fin.ext rfl
    rw [he]
    exact hAT.2.1 aa
  have hr : r.succ = Fin.last T.length := by
    apply Fin.ext
    change A.length + 1 = T.length
    exact hlen.symm
  have he : G.ends f = Sym2.mk y (A.vertex aa) := by
    simpa only [f, hr, hv] using ha
  have haa : A.vertex aa ∈ TreeSequenceVertexSet A := by
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨aa, rfl⟩
  exact ⟨A.vertex aa, haa, he.trans Sym2.eq_swap⟩

private theorem helper_hgammaTerminalExcluded_1690.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (_ : (0 : ℕ) < C.hierarchy.dividerCount),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    ∀ (hlen : T.length = A.length + (1 : ℕ)),
    let r : Fin T.length := (⟨A.length, by omega⟩ : Fin T.length);
    let f : E := T.edge r;
    ∀ (gamma : Fin k) (_ : phi f = some gamma)
      (_ :
        (∀ eta ∉ TreeMissingColors phi A,
          (↑(HierarchyFirstMissingPosition phi T eta) : ℕ) = T.length)),
    ∀ eta ∈ HierarchyStoredColorsAt H q,
    gamma ∉ C.good.gamma q eta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hpositive H q A hlen r f gamma hgammaf
      firstMissingAfter eta heta hgamma
  have hetaMissing : eta ∉ TreeMissingColors phi A :=
    (Finset.mem_sdiff.mp heta).2
  have hcutoff := firstMissingAfter eta hetaMissing
  have hseg : gamma ∈ HierarchySegmentColors H q eta := by
    unfold HierarchySegmentColors
    dsimp only
    have ht : H.stage q.succ = T := H.terminalStage
    rw [ht]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, r, le_rfl, ?_, hgammaf⟩
    rw [hcutoff]
    dsimp [r]
    omega
  exact (Finset.mem_sdiff.mp (C.good.avoidance q eta heta hgamma)).2 hseg

private theorem helper_hsigmaRoute_1829.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base) (_ : (0 : ℕ) < C.hierarchy.dividerCount),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Tnext : TreeSequence G e0 := ett.series.data.tree n.succ;
    ∀ (_ : T.length = A.length + (1 : ℕ))
      (_ :
        (∀ {X Y Z : TreeSequence G e0} (_ : TreeSequenceInitialSegment X Y)
          (_ : TreeSequenceInitialSegment Y Z), TreeSequenceInitialSegment X Z))
      (_ :
        (∀ {X Y Z : TreeSequence G e0} (_ : TreeSequenceInitialSegment X Z)
          (_ : TreeSequenceInitialSegment Y Z) (_ : X.length ≤ Y.length),
          TreeSequenceInitialSegment X Y))
      (_ : TreeSequenceInitialSegment A T) (_ : TreeSequenceInitialSegment Tn A)
      (_ : Tn.length < A.length) (_ : TreeSequenceInitialSegment T Tnext)
      (_ : TreeSequenceInitialSegment A Tnext),
    let y : V := T.vertex (Fin.last T.length);
    ∀ (alpha : Fin k)
      (_ :
        (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
            TashkinovAugmentationSequence phi (ett.series.data.tree n.castSucc)
              (ett.series.data.tree n.succ) ∨
          (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
              ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
            ∃ (edge : E) (seed : TreeSequence G e0),
              ett.series.data.connectingEdges n = { edge } ∧
                TreeSequenceAdjoinEdge (ett.series.data.tree n.castSucc) edge seed ∧
                  TashkinovAugmentationSequence phi seed (ett.series.data.tree n.succ)))
      (_ theta : Fin k),
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi theta alpha (Sum.inl y);
    ∀
      (_ :
        (IsProperEdgeColoring G sigma ∧
          IsOneEdgeUncolored sigma e0 ∧
            StableColoring A (TashkinovStoredColors ett.series.data n) phi sigma ∧
              TreeColoringInvariant A phi sigma ∧
                ∀ (f : E), TreeIncidentEdge A f → sigma f = phi f))
      (_ : (∀ (t : Fin T.length), sigma (T.edge t) = phi (T.edge t))),
    ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence sigma Tn T ∨
      (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
          ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
        ∃ (edge : E) (seed : TreeSequence G e0),
          ett.series.data.connectingEdges n = { edge } ∧
            TreeSequenceAdjoinEdge Tn edge seed ∧ TashkinovAugmentationSequence sigma seed T := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hpositive H q A n Tn Tnext hlen segmentTrans
      commonPrefix hAT hTnA hTnStrictA hTTnext hATnext y alpha hroute eta theta sigma hstableA
      hfixedEdges
  rcases hroute with ⟨hkind, hseq⟩ | ⟨hkind, edge, seed, hedges, hseed, hseq⟩
  · have hTnT := segmentTrans hTnA hAT
    have htoT := TashkinovAugmentationSequenceRestrict phi Tn T Tnext
      hseq hTnT hTTnext
    exact Or.inl ⟨hkind, TashkinovAugmentationSequenceColoringTransport
      phi sigma Tn A T htoT hAT hlen (fun t _ => hfixedEdges t)
      hstableA.2.2.2.1.2⟩
  · have hseedFinal := TashkinovAugmentationSequenceInitialSegment phi seed Tnext hseq
    have hseedA : TreeSequenceInitialSegment seed A :=
      commonPrefix hseedFinal hATnext (by
        have hseedLen : seed.length = Tn.length + 1 := hseed.1
        omega)
    have htoT := TashkinovAugmentationSequenceRestrict phi seed T Tnext
      hseq (segmentTrans hseedA hAT) hTTnext
    exact Or.inr ⟨hkind, edge, seed, hedges, hseed,
      TashkinovAugmentationSequenceColoringTransport phi sigma seed A T
        htoT hAT hlen (fun t _ => hfixedEdges t) hstableA.2.2.2.1.2⟩

private theorem helper_hnotElementarySigma_1858.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base) (_ : IsProperEdgeColoring G phi),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    ∀ (_ : TreeSequenceInitialSegment A T),
    let y : V := T.vertex (Fin.last T.length);
    ∀ (_ : y ∉ TreeSequenceVertexSet A),
    ∀ alpha ∈ MissingColors G phi y,
    ∀ (theta : Fin k) (x : V),
    theta ∈ MissingColors G phi x →
    x ∈ TreeSequenceVertexSet A →
    theta ≠ alpha →
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi theta alpha (Sum.inl y);
    (IsProperEdgeColoring G sigma ∧
        IsOneEdgeUncolored sigma e0 ∧
          StableColoring A (TashkinovStoredColors ett.series.data n) phi sigma ∧
            TreeColoringInvariant A phi sigma ∧
              ∀ (f : E), TreeIncidentEdge A f → sigma f = phi f) →
    ¬ColoredVertexSetElementary G sigma (TreeSequenceVertexSet T) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hproper H q A n hAT y hyOutside alpha halphay
      theta x hthetax hxA hthetaAlpha sigma hstableA
  have hswap := TwoColorComponentSwapMissingBehavior G phi theta alpha
    hthetaAlpha hproper (Sum.inl y)
  have hthetay : theta ∈ MissingColors G sigma y := hswap.2.2.1 y rfl halphay
  have hthetaxSigma : theta ∈ MissingColors G sigma x := by
    rw [hstableA.2.2.2.1.2 x hxA]
    exact hthetax
  have hxT := TreeSequenceInitialSegmentVertexSetSubset hAT hxA
  have hyT : y ∈ TreeSequenceVertexSet T := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨Fin.last T.length, rfl⟩
  have hxy : x ≠ y := fun he => hyOutside (he ▸ hxA)
  intro helem
  exact Finset.disjoint_left.mp (helem hxT hyT hxy) hthetaxSigma hthetay

private theorem helper_boundaryEq_2016.{u_1, u_2} :
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
    let y : V := T.vertex (Fin.last T.length);
    ∀ (alpha theta : Fin k),
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi theta alpha (Sum.inl y);
    ∀
      (_ :
        (IsProperEdgeColoring G sigma ∧
          IsOneEdgeUncolored sigma e0 ∧
            StableColoring A (TashkinovStoredColors ett.series.data n) phi sigma ∧
              TreeColoringInvariant A phi sigma ∧
                ∀ (f : E), TreeIncidentEdge A f → sigma f = phi f))
      (B : TreeSequence G e0) (_ : TreeSequenceVertexSet B ⊆ TreeSequenceVertexSet A)
      (c : Fin k),
    BoundaryColorEdges G sigma (TreeSequenceVertexSet B) c =
      BoundaryColorEdges G phi (TreeSequenceVertexSet B) c := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q A n y alpha theta sigma hstableA B hBA c
  ext edge
  simp only [BoundaryColorEdges, Finset.mem_filter]
  have hfixed : edge ∈ BoundaryEdges G (TreeSequenceVertexSet B) → sigma edge = phi edge := by
    intro he
    obtain ⟨u, hu, v, hv, hends⟩ := by simpa [BoundaryEdges] using he
    apply hstableA.2.2.2.2
    refine ⟨u, hBA hu, ?_⟩
    change u ∈ G.ends edge
    rw [hends]
    exact Sym2.mem_mk_left _ _
  constructor <;> rintro ⟨he, hc⟩
  · exact ⟨he, by rw [← hfixed he]; exact hc⟩
  · exact ⟨he, by rw [hfixed he]; exact hc⟩

private theorem helper_continuation_2653.{u_1, u_2} :
    helperContinuation2653Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hproper hlower hfewer hminimal hlarge hpositive
      H q A n Tn hlen commonPrefix equalTrees hAT hTnA prefixSegment hAElem r f y hyOutside alpha
      halphay gamma hgammaA hgammaf hfEnds eta theta hthetaA hthetaClosed hthetaGamma
      outsideMissingComponent hthetaAlpha sigma hstableA missingFirstInA hfixedEdges corrT
      hmaximumT hnotElementarySigma positivePrefix abovePrefix strictPrefix belowPrefix
      generatingPrefix corrPrefix basePrefixSigma baseT hcoreT hterminalTree K missingTree
      stageInsideA coreInsideA starredEq terminalColors storedEq stageMissingEq firstMissingEq
      segmentEq boundaryEq minusEq closureEq goodT
  let Cs : HierarchyCounterexample baseT := by
    exact {
      positive := by rw [corrT.rungAgreement]; exact C.positive
      hierarchy := K
      good := goodT
      maximum := hmaximumT
      notElementary := hnotElementarySigma }
  have hstarK : HierarchyStarredStage K (Fin.last K.dividerCount) = A := starredEq q
  have pathNumberEq : HierarchyPathNumber K = HierarchyPathNumber H := by
    unfold HierarchyPathNumber
    dsimp only
    rw [starredEq q]
  have measureEq : HierarchyCounterexampleMeasure Cs = HierarchyCounterexampleMeasure C := by
    change (HierarchyPathNumber K,
      T.length - (K.stage ⟨K.dividerCount, by omega⟩).length) =
      (HierarchyPathNumber H,
        T.length - (H.stage ⟨H.dividerCount, by omega⟩).length)
    rw [pathNumberEq]
  have hAElemSigma : ColoredVertexSetElementary G sigma (TreeSequenceVertexSet A) := by
    intro u hu v hv huv
    rw [hstableA.2.2.2.1.2 u hu, hstableA.2.2.2.1.2 v hv]
    exact hAElem hu hv huv
  have hprefixK :
      TreeSequencePrefix T
        (min ((HierarchyStarredStage K (Fin.last K.dividerCount)).length +
          (T.length - (HierarchyStarredStage K (Fin.last K.dividerCount)).length - 1))
          T.length)
        (by
          have := (HierarchyStarredStage K (Fin.last K.dividerCount)).positive
          have := T.positive
          omega)
        (Nat.min_le_right _ _) = A := by
    have hlengthStar := congrArg TreeSequence.length hstarK
    apply equalTrees
    · apply commonPrefix (prefixSegment _ _ _) hAT
      change min ((HierarchyStarredStage K (Fin.last K.dividerCount)).length +
        (T.length - (HierarchyStarredStage K (Fin.last K.dividerCount)).length - 1))
        T.length ≤ A.length
      omega
    · change min ((HierarchyStarredStage K (Fin.last K.dividerCount)).length +
        (T.length - (HierarchyStarredStage K (Fin.last K.dividerCount)).length - 1))
        T.length = A.length
      omega
  have hprefixSigma :
      let A' := HierarchyStarredStage K (Fin.last K.dividerCount)
      let ell' := T.length - A'.length
      let U := TreeSequencePrefix T
        (min (A'.length + (ell' - 1)) T.length)
        (by have := A'.positive; have := T.positive; omega)
        (Nat.min_le_right _ _)
      ColoredVertexSetElementary G sigma (TreeSequenceVertexSet U) := by
    dsimp only
    rw [hprefixK]
    exact hAElemSigma
  have hlargeSigma : 2 * corrT.replacementETT.rounds + 11 ≤
      (TreeMissingColors sigma (corrT.replacementETT.series.data.tree
        (Fin.last corrT.replacementETT.rounds).castSucc)).card := by
    rw [hterminalTree, missingTree Tn (TreeSequenceInitialSegmentVertexSetSubset hTnA),
      corrT.rungAgreement]
    exact hlarge
  have hthetaSigmaA : theta ∈ TreeMissingColors sigma A := by
    rw [missingTree A (fun _ h => h)]
    exact hthetaA
  have hgammaSigmaA : gamma ∈ TreeMissingColors sigma A := by
    rw [missingTree A (fun _ h => h)]
    exact hgammaA
  have hthetaClosedSigma : TreeColorSetClosed G sigma A {theta} := by
    intro c hc
    rw [boundaryEq A (fun _ h => h) c]
    exact hthetaClosed c hc
  have hresult := ChangeLemmaBothInside G k e0 corrT.replacementInput T sigma
    corrT.replacementETT baseT Cs hstableA.1 hstableA.2.1
    (fun lower hp hl hm =>
      hlower lower hp (lt_of_lt_of_eq hl corrT.rungAgreement) hm)
    (fun other hr hm b J g hj =>
      hfewer other (hr.trans corrT.rungAgreement) hm b J g hj)
    (fun C' hr hq => by
      rw [measureEq]
      exact hminimal C' (hr.trans corrT.rungAgreement) hq)
    hprefixSigma hlargeSigma theta gamma hthetaGamma
    (by
      dsimp only
      change theta ∈ TreeMissingColors sigma
          (TreeSequencePrefix T
            (min ((HierarchyStarredStage K (Fin.last K.dividerCount)).length +
              (T.length - (HierarchyStarredStage K (Fin.last K.dividerCount)).length - 1))
              T.length) _ _) ∧
        gamma ∈ TreeMissingColors sigma
          (TreeSequencePrefix T
            (min ((HierarchyStarredStage K (Fin.last K.dividerCount)).length +
              (T.length - (HierarchyStarredStage K (Fin.last K.dividerCount)).length - 1))
              T.length) _ _)
      rw [hprefixK]
      exact ⟨hthetaSigmaA, hgammaSigmaA⟩)
    (by
      dsimp only
      change (theta ∉ TreeMissingColors sigma
          (HierarchyStarredStage K (Fin.last K.dividerCount)) ∨
        gamma ∉ TreeMissingColors sigma
          (HierarchyStarredStage K (Fin.last K.dividerCount))) → _
      rw [hstarK]
      intro hbad
      exact False.elim (hbad.elim (fun h => h hthetaSigmaA) (fun h => h hgammaSigmaA)))
    (by
      change T.vertex (HierarchyFirstMissingPosition sigma T theta) ∈
          TreeSequenceVertexSet (HierarchyStarredStage K (Fin.last K.dividerCount)) ∧
        T.vertex (HierarchyFirstMissingPosition sigma T gamma) ∈
          TreeSequenceVertexSet (HierarchyStarredStage K (Fin.last K.dividerCount))
      rw [hstarK, firstMissingEq theta, firstMissingEq gamma]
      exact ⟨(missingFirstInA theta hthetaA).2, (missingFirstInA gamma hgammaA).2⟩)
  have hinterSigma : TreeInterchangeable G A sigma theta gamma := by
    have hh := hresult.2.2
    change (theta ∈ TreeMissingColors sigma (HierarchyStarredStage K (Fin.last K.dividerCount)) ∧
      TreeColorSetClosed G sigma (HierarchyStarredStage K (Fin.last K.dividerCount)) {theta}) → _
          at hh
    rw [hstarK] at hh
    exact (hh ⟨hthetaSigmaA, hthetaClosedSigma⟩).2
  have hswap := TwoColorComponentSwapMissingBehavior G phi theta alpha
    hthetaAlpha hproper (Sum.inl y)
  have hthetaySigma : theta ∈ MissingColors G sigma y := hswap.2.2.1 y rfl halphay
  have hout := outsideMissingComponent sigma hstableA.1 theta gamma hthetaGamma
    hthetaSigmaA hgammaSigmaA y hyOutside (Or.inl hthetaySigma) hinterSigma
  have hgammafSigma : sigma f = some gamma := (hfixedEdges r).trans hgammaf
  obtain ⟨u, huA, hends⟩ := hfEnds
  have hyf : (TwoColorIncidenceGraph G sigma theta gamma).Adj (Sum.inl y) (Sum.inr f) := by
    refine ⟨?_, Or.inr hgammafSigma⟩
    change y ∈ G.ends f
    rw [hends]
    exact Sym2.mem_mk_right _ _
  have hfu : (TwoColorIncidenceGraph G sigma theta gamma).Adj (Sum.inr f) (Sum.inl u) := by
    refine ⟨?_, Or.inr hgammafSigma⟩
    change u ∈ G.ends f
    rw [hends]
    exact Sym2.mem_mk_left _ _
  apply hout u huA
  change (TwoColorIncidenceGraph G sigma theta gamma).connectedComponentMk (Sum.inl u) =
    (TwoColorIncidenceGraph G sigma theta gamma).connectedComponentMk (Sum.inl y)
  exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hfu).symm.trans
    (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hyf).symm

private theorem helper_continuation_2177.{u_1, u_2} :
    helperContinuation2177Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hproper hlower hfewer hminimal hlarge hpositive
      H q i A n Tn hlen commonPrefix equalTrees hAT stagesNested hTnA prefixSegment hAElem r f y
      hyOutside alpha halphaA halphay gamma hgammaA hgammaf hfEnds eta hcard theta hthetaPair
      hthetaNew x hthetax hthetaA hthetaClosed hthetaGamma outsideMissingComponent
      stepInterchange hthetaAlpha hcomponentOutside sigma hrecolorA hstableA missingFirstInA
      hstableLadder hmod hfixedEdges hsigmaRoute corrT hmaximumT hnotElementarySigma
      hrecolorPrefix positivePrefix abovePrefix strictPrefix belowPrefix generatingPrefix
      basePrefix hclosurePrefix HP goodPrefix hprefixTransport corrPrefix hmaximumPrefixSigma
      basePrefixSigma KP goodPrefixSigma hsamePrefixSigma hminusPrefixSigma corrA baseT hcoreTA
      hclosureTA hsupportTA hcoreT hterminalTree K missingTree stageInsideA coreInsideA starredEq
      terminalColors storedEq
  have stageMissingEq (j : Fin (H.dividerCount + 1)) :
      HierarchyStageMissingColors K j = HierarchyStageMissingColors H j := by
    refine Fin.cases ?_ (fun a => ?_) j
    · change TreeMissingColors sigma
        (corrT.replacementETT.series.data.tree
          (Fin.last corrT.replacementETT.rounds).castSucc) = TreeMissingColors phi Tn
      rw [hterminalTree]
      exact missingTree Tn (TreeSequenceInitialSegmentVertexSetSubset hTnA)
    · exact missingTree _ (TreeSequenceInitialSegmentVertexSetSubset (stageInsideA a.succ))
  have firstBound (psi : PartialEdgeColoring E k) (c : Fin k)
      (hc : c ∈ TreeMissingColors psi A) :
      (HierarchyFirstMissingPosition psi T c).val ≤ A.length := by
    exact TreeSequenceFirstMissingPositionLePrefix hAT hc
  have firstMissingEq (c : Fin k) :
      HierarchyFirstMissingPosition sigma T c = HierarchyFirstMissingPosition phi T c := by
    exact @helper_firstMissingEq_961 V E inferInstance inferInstance inferInstance inferInstance
        G k e0 input T phi ett base C hproper hpositive hAT alpha halphaA halphay gamma eta theta
        hthetaPair hthetaNew x hthetax hthetaA hthetaClosed hthetaGamma stepInterchange
        hthetaAlpha hcomponentOutside hrecolorA hstableA hstableLadder hmod hfixedEdges
        hsigmaRoute corrT hmaximumT hnotElementarySigma hrecolorPrefix positivePrefix abovePrefix
        strictPrefix belowPrefix generatingPrefix basePrefix HP goodPrefix hprefixTransport
        corrPrefix hmaximumPrefixSigma basePrefixSigma KP goodPrefixSigma hsamePrefixSigma
        hminusPrefixSigma baseT hcoreTA hclosureTA hsupportTA hcoreT hterminalTree missingTree
        starredEq terminalColors storedEq stageMissingEq firstBound c
  have stageFixed (j : Fin (H.dividerCount + 1)) (t : Fin (H.stage j.succ).length) :
      sigma ((H.stage j.succ).edge t) = phi ((H.stage j.succ).edge t) := by
    have hs := stagesNested j.succ (Fin.last (H.dividerCount + 1)) (Fin.le_last _)
    rw [H.terminalStage] at hs
    have he := hs.2.2 t
    rw [← he]
    exact hfixedEdges _
  have segmentEq (j : Fin (H.dividerCount + 1)) (c : Fin k) :
      HierarchySegmentColors K j c = HierarchySegmentColors H j c := by
    unfold HierarchySegmentColors
    dsimp only
    rw [starredEq j, firstMissingEq c]
    simp only [K, stageFixed]
  have boundaryEq (B : TreeSequence G e0)
      (hBA : TreeSequenceVertexSet B ⊆ TreeSequenceVertexSet A) (c : Fin k) :
      BoundaryColorEdges G sigma (TreeSequenceVertexSet B) c =
        BoundaryColorEdges G phi (TreeSequenceVertexSet B) c := by
    exact @helper_boundaryEq_2016 V E inferInstance inferInstance inferInstance inferInstance G k
        e0 input T phi ett base C alpha theta hstableA B hBA c
  have minusEq (B : TreeSequence G e0)
      (hBA : TreeSequenceVertexSet B ⊆ TreeSequenceVertexSet A) (R : Finset (Fin k)) :
      TreeColorSetMinusClosed G sigma B R ↔ TreeColorSetMinusClosed G phi B R := by
    unfold TreeColorSetMinusClosed TreeColorSetClosed
    rw [missingTree B hBA]
    simp only [boundaryEq B hBA]
  have closureEq (hpe : corrT.replacementETT.series.data.kind
      (Fin.last corrT.replacementETT.rounds) = some TashkinovExtensionKind.PE) :
      baseT.closure = base.closure := by
    have hpeOld : ett.series.data.kind n = some TashkinovExtensionKind.PE := by
      rw [← terminalColors.1]
      exact hpe
    exact hclosureTA.trans
      ((hsamePrefixSigma.1.2.2.2.2.2 hpeOld).symm.trans hclosurePrefix)
  exact @helper_continuation_2653 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 input T phi ett base C hproper hlower hfewer hminimal hlarge hpositive hlen commonPrefix
      equalTrees hAT hTnA prefixSegment hAElem hyOutside alpha halphay gamma hgammaA hgammaf
      hfEnds eta theta hthetaA hthetaClosed hthetaGamma outsideMissingComponent hthetaAlpha
      hstableA missingFirstInA hfixedEdges corrT hmaximumT hnotElementarySigma positivePrefix
      abovePrefix strictPrefix belowPrefix generatingPrefix corrPrefix basePrefixSigma baseT
      hcoreT hterminalTree missingTree stageInsideA coreInsideA starredEq terminalColors storedEq
      stageMissingEq firstMissingEq segmentEq boundaryEq minusEq closureEq
private theorem helper_continuation_2110.{u_1, u_2} :
    helperContinuation2110Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hproper hone hlower hfewer hminimal hlarge
      hpositive H q i A n Tn hqpos hA hlen segmentTrans commonPrefix equalTrees hAT stagesNested
      hTnA prefixSegment hAElem r f y hyOutside alpha halphaA halphay gamma hgammaA hgammaf
      hfEnds eta hcard theta hthetaPair hthetaNew x hthetax hthetaA hthetaClosed hthetaGamma
      outsideMissingComponent stepInterchange hthetaAlpha hcomponentOutside sigma hrecolorA
      hstableA missingFirstInA hstableLadder hmod hfixedEdges hsigmaRoute corrT hmaximumT
      hnotElementarySigma
  obtain ⟨ettPrefix, hmaximumPrefix, hrungPrefix, hseriesPrefix,
      basePrefix, hcorePrefix, hclosurePrefix, hsupportPrefix,
      HP, hcountPrefix, hstagesPrefix, hdividersPrefix,
      goodPrefix, hcolorsPrefix, hminusPrefix⟩ :=
    GoodHierarchyPrefixRepackage G k e0 input T phi phi ett C.maximum
      base H C.good q (by change 1 ≤ H.dividerCount; omega)
  have hrecolorPrefix : OutsideKempeRecoloring (H.stage q.castSucc)
      phi sigma theta alpha := by
    rw [← hA]
    exact hrecolorA
  have hprefixTransport := HierarchyLEMStable G k e0 input (H.stage q.castSucc)
    phi sigma ettPrefix hmaximumPrefix (by rw [hrungPrefix]; exact C.positive)
    (fun lower hp hl hm => hlower lower hp (lt_of_lt_of_eq hl hrungPrefix) hm)
    basePrefix HP goodPrefix hproper hone theta alpha hrecolorPrefix
  obtain ⟨corrPrefix, hmaximumPrefixSigma, basePrefixSigma, KP,
      goodPrefixSigma, hsamePrefixSigma, hminusPrefixSigma⟩ :=
    hprefixTransport.2.2.2.2
  -- Both certificates below are tied to the original certified series.
  -- No equality between independently chosen replacement certificates is used.
  rcases ettPrefix with ⟨roundsPrefix, positivePrefix, seriesPrefix,
    abovePrefix, strictPrefix, belowPrefix, generatingPrefix⟩
  dsimp only at hrungPrefix hseriesPrefix
  cases hrungPrefix
  have hseriesEq : seriesPrefix = ett.series := eq_of_heq hseriesPrefix
  cases hseriesEq
  let corrA : CorrespondingExtendedTashkinovTree G k e0 ett sigma
      (H.stage q.castSucc) := by
    exact {
      replacementInput := corrPrefix.replacementInput
      replacementSeries := corrPrefix.replacementSeries
      replacementETT := corrPrefix.replacementETT
      rungAgreement := corrPrefix.rungAgreement
      seriesPresentation := corrPrefix.seriesPresentation
      finalGeneratingColoring := corrPrefix.finalGeneratingColoring
      ladderTreesAgree := corrPrefix.ladderTreesAgree
      storedColorsAgree := corrPrefix.storedColorsAgree
      connectingEdgesAgree := corrPrefix.connectingEdgesAgree
      extensionKindsAgree := corrPrefix.extensionKindsAgree
      replacementProper := corrPrefix.replacementProper
      replacementOneUncolored := corrPrefix.replacementOneUncolored
      replacementStable := corrPrefix.replacementStable }
  obtain ⟨baseT, hcoreTA, hclosureTA, hsupportTA⟩ :=
    GoodHierarchyCommonOriginalBaseTransport G k e0 input T phi sigma ett
      (H.stage q.castSucc) T corrA basePrefixSigma corrT
  have hcoreT : baseT.core = base.core :=
    hcoreTA.trans (hsamePrefixSigma.1.1.symm.trans hcorePrefix)
  have hterminalTree :
      corrT.replacementETT.series.data.tree
        (Fin.last corrT.replacementETT.rounds).castSucc = Tn := by
    exact corrT.terminalData.1
  let K : TashkinovHierarchy corrT.replacementETT baseT := by
    exact {
      dividerCount := H.dividerCount
      stage := H.stage
      baseStage := H.baseStage.trans hterminalTree.symm
      terminalStage := H.terminalStage
      nested := H.nested
      strict := H.strict
      dividerPosition := H.dividerPosition
      dividerPositive := H.dividerPositive
      dividerIncreasing := H.dividerIncreasing
      dividerStage := H.dividerStage
      coreInsideFirst := by rw [hcoreT]; exact H.coreInsideFirst }
  have missingTree (B : TreeSequence G e0)
      (hBA : TreeSequenceVertexSet B ⊆ TreeSequenceVertexSet A) :
      TreeMissingColors sigma B = TreeMissingColors phi B := by
    ext c
    simp only [TreeMissingColors, Finset.mem_biUnion]
    constructor <;> rintro ⟨v, hv, hc⟩
    · exact ⟨v, hv, by rw [← hstableA.2.2.2.1.2 v (hBA hv)]; exact hc⟩
    · exact ⟨v, hv, by rw [hstableA.2.2.2.1.2 v (hBA hv)]; exact hc⟩
  have stageInsideA (j : Fin (H.dividerCount + 1)) :
      TreeSequenceInitialSegment (H.stage j.castSucc) A := by
    rw [hA]
    exact stagesNested j.castSucc q.castSucc (Fin.le_last j)
  have coreInsideA : TreeSequenceVertexSet base.core ⊆ TreeSequenceVertexSet A :=
    TreeSequenceInitialSegmentVertexSetSubset
      (segmentTrans H.coreInsideFirst
        (by
          rw [hA]
          exact stagesNested ⟨1, by omega⟩ q.castSucc (by change 1 ≤ H.dividerCount; omega)))
  have starredInsideA (j : Fin (H.dividerCount + 1)) :
      TreeSequenceVertexSet (HierarchyStarredStage H j) ⊆ TreeSequenceVertexSet A := by
    refine Fin.cases ?_ (fun a => ?_) j
    · exact coreInsideA
    · exact TreeSequenceInitialSegmentVertexSetSubset (stageInsideA a.succ)
  have starredEq (j : Fin (H.dividerCount + 1)) :
      HierarchyStarredStage K j = HierarchyStarredStage H j := by
    refine Fin.cases ?_ (fun a => ?_) j
    · exact hcoreT
    · rfl
  have terminalColors :
      corrT.replacementETT.series.data.kind (Fin.last corrT.replacementETT.rounds) =
        ett.series.data.kind n ∧
      TashkinovStoredColors corrT.replacementETT.series.data
          (Fin.last corrT.replacementETT.rounds) =
        TashkinovStoredColors ett.series.data n := by
    exact ⟨corrT.terminalData.2.1, corrT.terminalData.2.2⟩
  have storedEq (j : Fin (H.dividerCount + 1)) :
      HierarchyStoredColorsAt K j = HierarchyStoredColorsAt H j := by
    unfold HierarchyStoredColorsAt
    dsimp only
    rw [terminalColors.2, starredEq j, missingTree _ (starredInsideA j)]
  exact @helper_continuation_2177 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 input T phi ett base C hproper hlower hfewer hminimal hlarge hpositive hlen commonPrefix
      equalTrees hAT stagesNested hTnA prefixSegment hAElem hyOutside alpha halphaA halphay gamma
      hgammaA hgammaf hfEnds eta hcard theta hthetaPair hthetaNew x hthetax hthetaA hthetaClosed
      hthetaGamma outsideMissingComponent stepInterchange hthetaAlpha hcomponentOutside hrecolorA
      hstableA missingFirstInA hstableLadder hmod hfixedEdges hsigmaRoute corrT hmaximumT
      hnotElementarySigma hrecolorPrefix positivePrefix abovePrefix strictPrefix belowPrefix
      generatingPrefix basePrefix hclosurePrefix HP goodPrefix hprefixTransport corrPrefix
      hmaximumPrefixSigma basePrefixSigma KP goodPrefixSigma hsamePrefixSigma hminusPrefixSigma
      baseT hcoreTA hclosureTA hsupportTA hcoreT hterminalTree missingTree stageInsideA
      coreInsideA starredEq terminalColors storedEq
private theorem helper_continuation_2074.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (_ : IsProperEdgeColoring G phi) (_ : IsOneEdgeUncolored phi e0)
      (_ : LowerRoundInductionHypothesis G k e0 ett.rounds)
      (_ :
        (∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
          {generating' : PartialEdgeColoring E k}
          (other : ExtendedTashkinovTree G k e0 input' T' generating')
          (_ : other.rounds = ett.rounds) (_ : MaximumProperty other)
          (base' : HierarchyBase other generating') (K : TashkinovHierarchy other base')
          (_ : GoodHierarchy K) (_ : K.dividerCount < C.hierarchy.dividerCount),
          ColoredVertexSetElementary G generating' (TreeSequenceVertexSet T')))
      (_ :
        (∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
          {generating' : PartialEdgeColoring E k}
          {other : ExtendedTashkinovTree G k e0 input' T' generating'}
          {base' : HierarchyBase other generating'} (C' : HierarchyCounterexample base')
          (_ : other.rounds = ett.rounds)
          (_ : C'.hierarchy.dividerCount = C.hierarchy.dividerCount),
          ¬HierarchyCounterexampleLess (HierarchyCounterexampleMeasure C')
              (HierarchyCounterexampleMeasure C)))
      (_ :
        (let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
        let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
        (2 : ℕ) * ett.rounds + (11 : ℕ) ≤ (TreeMissingColors phi Tn).card))
      (hpositive : (0 : ℕ) < C.hierarchy.dividerCount),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let i : Fin H.dividerCount :=
      (⟨H.dividerCount - (1 : ℕ),
          id
            (fun (hpositive : (0 : ℕ) < H.dividerCount) ↦
              Decidable.byContradiction
                fun (a : ¬H.dividerCount - (1 : ℕ) < H.dividerCount) ↦ by omega)
            hpositive⟩ :
        Fin H.dividerCount);
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Tnext : TreeSequence G e0 := ett.series.data.tree n.succ;
    ∀ (_ : (0 : ℕ) < H.dividerCount) (_ : i.succ = q) (_ : A = H.stage q.castSucc)
      (hlen : T.length = A.length + (1 : ℕ))
      (_ :
        (∀ {X Y Z : TreeSequence G e0} (_ : TreeSequenceInitialSegment X Y)
          (_ : TreeSequenceInitialSegment Y Z), TreeSequenceInitialSegment X Z))
      (_ :
        (∀ {X Y Z : TreeSequence G e0} (_ : TreeSequenceInitialSegment X Z)
          (_ : TreeSequenceInitialSegment Y Z) (_ : X.length ≤ Y.length),
          TreeSequenceInitialSegment X Y))
      (_ :
        (∀ {X Y : TreeSequence G e0} (_ : TreeSequenceInitialSegment X Y)
          (_ : X.length = Y.length), X = Y))
      (_ : TreeSequenceInitialSegment A T)
      (_ :
        (∀ (a b : Fin (H.dividerCount + (2 : ℕ))) (_ : (↑a : ℕ) ≤ (↑b : ℕ)),
          TreeSequenceInitialSegment (H.stage a) (H.stage b)))
      (_ : TreeSequenceInitialSegment Tn A) (_ : Tn.length < A.length)
      (_ : TreeSequenceInitialSegment T Tnext) (_ : TreeSequenceInitialSegment A Tnext)
      (_ :
        (∀ (m : ℕ) (hm : (1 : ℕ) ≤ m) (hmT : m ≤ T.length),
          TreeSequenceInitialSegment (TreeSequencePrefix T m hm hmT) T))
      (_ : ColoredVertexSetElementary G phi (TreeSequenceVertexSet A)),
    let r : Fin T.length := (⟨A.length, by omega⟩ : Fin T.length);
    let f : E := T.edge r;
    let y : V := T.vertex (Fin.last T.length);
    ∀ (_ : y ∉ TreeSequenceVertexSet A),
    ∀ alpha ∈ TreeMissingColors phi A,
    alpha ∈ MissingColors G phi y →
    (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
          TashkinovAugmentationSequence phi (ett.series.data.tree n.castSucc)
            (ett.series.data.tree n.succ) ∨
        (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
            ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
          ∃ (edge : E) (seed : TreeSequence G e0),
            ett.series.data.connectingEdges n = { edge } ∧
              TreeSequenceAdjoinEdge (ett.series.data.tree n.castSucc) edge seed ∧
                TashkinovAugmentationSequence phi seed (ett.series.data.tree n.succ)) →
    ∀ gamma ∈ TreeMissingColors phi A,
    phi f = some gamma →
    (∃ u ∈ TreeSequenceVertexSet A, G.ends f = s(u, y)) →
    (∀ eta ∈ HierarchyStoredColorsAt H q, gamma ∉ C.good.gamma q eta) →
    ∀ eta ∈ HierarchyStoredColorsAt C.hierarchy i.succ,
    (C.good.gamma i.succ eta).card = (2 : ℕ) →
    ∀ theta ∈ C.good.gamma i.succ eta,
    (theta ∈
        (TreeSequenceVertexSet (C.hierarchy.stage i.succ.castSucc) \
              TreeSequenceVertexSet (HierarchyStarredStage C.hierarchy i.castSucc)).biUnion
          fun (v : V) ↦ MissingColors G phi v) →
    ∀ (x : V),
    theta ∈ MissingColors G phi x →
    x ∈ TreeSequenceVertexSet A →
    theta ∈ TreeMissingColors phi A →
    TreeColorSetClosed G phi A { theta } →
    False := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hproper hone hlower hfewer hminimal hlarge
      hpositive H q i A n Tn Tnext hqpos hiq hA hlen segmentTrans commonPrefix equalTrees hAT
      stagesNested hTnA hTnStrictA hTTnext hATnext prefixSegment hAElem r f y hyOutside alpha
      halphaA halphay hroute gamma hgammaA hgammaf hfEnds hgammaTerminalExcluded eta heta hcard
      theta hthetaPair hthetaNew x hthetax hxA hthetaA hthetaClosed
  have hthetaGamma : theta ≠ gamma := by
    intro he
    have hp : theta ∈ C.good.gamma q eta := by
      simpa only [hiq] using hthetaPair
    have heStored : eta ∈ HierarchyStoredColorsAt H q := by
      simpa only [hiq] using heta
    exact hgammaTerminalExcluded eta heStored (he ▸ hp)
  have outsideMissingComponent (psi : PartialEdgeColoring E k)
      (hpsi : IsProperEdgeColoring G psi) (c d : Fin k) (hcd : c ≠ d)
      (hcA : c ∈ TreeMissingColors psi A) (hdA : d ∈ TreeMissingColors psi A)
      (w : V) (hwOutside : w ∉ TreeSequenceVertexSet A)
      (hcw : c ∈ MissingColors G psi w ∨ d ∈ MissingColors G psi w)
      (hinter : TreeInterchangeable G A psi c d) :
      ∀ v ∈ TreeSequenceVertexSet A,
        Sum.inl v ∉ TwoColorComponent G psi c d (Sum.inl w) := by
    exact hinter.outside_missing_component hpsi hcd hcA hdA w hwOutside hcw
  have stepInterchange (beta : Fin k) (hne : theta ≠ beta) :
      TreeInterchangeable G A phi theta beta := by
    have hstage : H.stage i.succ.castSucc = A := by rw [hiq, ← hA]
    have hm : theta ∈ TreeMissingColors phi (H.stage i.succ.castSucc) := by
      rw [hstage]
      exact hthetaA
    have hc : TreeColorSetClosed G phi (H.stage i.succ.castSucc) {theta} := by
      rw [hstage]
      exact hthetaClosed
    have hi := step1 G k e0 input T phi ett C.maximum C.positive hproper hone
      hlower base H C.good hfewer hlarge i theta beta hm hne hc
    rw [hstage] at hi
    exact hi
  have hthetaAlpha : theta ≠ alpha := by
    exact @helper_hthetaAlpha_1167 V E inferInstance inferInstance inferInstance inferInstance G
        k e0 input T phi ett base C hproper hpositive hlen hyOutside alpha halphay gamma hgammaA
        hgammaf hfEnds theta hthetaA hthetaGamma outsideMissingComponent stepInterchange
  have hcomponentOutside : ∀ v ∈ TreeSequenceVertexSet A,
      Sum.inl v ∉ TwoColorComponent G phi theta alpha (Sum.inl y) :=
    outsideMissingComponent phi hproper theta alpha hthetaAlpha hthetaA halphaA y hyOutside
      (Or.inr halphay) (stepInterchange alpha hthetaAlpha)
  let sigma := TwoColorComponentSwap G phi theta alpha (Sum.inl y)
  have hrecolorA : OutsideKempeRecoloring A phi sigma theta alpha := by
    refine ⟨hthetaAlpha, {Sum.inl y}, ?_, ?_⟩
    · intro z hz v hv hvA
      have he : z = Sum.inl y := Finset.mem_singleton.mp hz
      subst z
      exact hcomponentOutside v hvA hv
    · intro edge
      simp only [sigma, TwoColorComponentSwap, Finset.mem_singleton, exists_eq_left]
  have hstableA := OutsideKempeRecoloringStable G e0 A
    (TashkinovStoredColors ett.series.data n) phi sigma theta alpha
    hproper hone hrecolorA
  have missingFirstInA (c : Fin k) (hc : c ∈ TreeMissingColors phi A) :
      c ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T c)) ∧
        T.vertex (HierarchyFirstMissingPosition phi T c) ∈ TreeSequenceVertexSet A := by
    exact ⟨(TreeSequenceFirstMissingPositionPrefixWitness hAT hc).1,
      TreeSequenceFirstMissingVertexMemOfPrefix hAT hc⟩
  have hstableLadder : StableColoring Tn
      (TashkinovStoredColors ett.series.data n)
      (ett.series.data.coloring n) sigma := by
    have hsub := TreeSequenceInitialSegmentVertexSetSubset hTnA
    constructor
    · intro edge he _
      rw [← ett.generatingColoring]
      apply hstableA.2.2.2.2 edge
      obtain ⟨v, hv, hinc⟩ := he
      exact ⟨v, hsub hv, hinc⟩
    · intro v hv
      rw [← ett.generatingColoring]
      exact hstableA.2.2.1.2 v (hsub hv)
  have hmod : ModColoring ett sigma := Td G k e0 input T phi ett C.maximum
    C.positive hlower sigma hstableA.1 hstableA.2.1 hstableLadder
  have hfixedEdges : ∀ t : Fin T.length, sigma (T.edge t) = phi (T.edge t) := by
    exact @helper_hfixedEdges_1244 V E inferInstance inferInstance inferInstance inferInstance G
        k e0 input T phi ett base C hpositive hlen hAT alpha hfEnds eta theta hstableA
  have hsigmaRoute :
      (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence sigma Tn T) ∨
      ((ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
          ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
        ∃ (edge : E) (seed : TreeSequence G e0),
          ett.series.data.connectingEdges n = {edge} ∧
          TreeSequenceAdjoinEdge Tn edge seed ∧
          TashkinovAugmentationSequence sigma seed T) := by
    exact @helper_hsigmaRoute_1829 V E inferInstance inferInstance inferInstance inferInstance G
        k e0 input T phi ett base C hpositive hlen segmentTrans commonPrefix hAT hTnA hTnStrictA
        hTTnext hATnext alpha hroute eta theta hstableA hfixedEdges
  obtain ⟨corrT⟩ := hmod.2.2 T ett.abovePenultimate ett.strictAbovePenultimate hsigmaRoute
  have hmaximumT : MaximumProperty corrT.replacementETT :=
    MaximumPropertyTransport G k e0 ett sigma hmod T corrT C.maximum
  have hnotElementarySigma : ¬ ColoredVertexSetElementary G sigma
      (TreeSequenceVertexSet T) := by
    exact @helper_hnotElementarySigma_1858 V E inferInstance inferInstance inferInstance
        inferInstance G k e0 input T phi ett base C hproper hAT hyOutside alpha halphay theta x
        hthetax hxA hthetaAlpha hstableA
  exact @helper_continuation_2110 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 input T phi ett base C hproper hone hlower hfewer hminimal hlarge hpositive hqpos hA
      hlen segmentTrans commonPrefix equalTrees hAT stagesNested hTnA prefixSegment hAElem
      hyOutside alpha halphaA halphay gamma hgammaA hgammaf hfEnds eta hcard theta hthetaPair
      hthetaNew x hthetax hthetaA hthetaClosed hthetaGamma outsideMissingComponent
      stepInterchange hthetaAlpha hcomponentOutside hrecolorA hstableA missingFirstInA
      hstableLadder hmod hfixedEdges hsigmaRoute corrT hmaximumT hnotElementarySigma
private theorem helper_continuation_2056.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (_ : IsProperEdgeColoring G phi) (_ : IsOneEdgeUncolored phi e0)
      (_ : LowerRoundInductionHypothesis G k e0 ett.rounds)
      (_ :
        (∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
          {generating' : PartialEdgeColoring E k}
          (other : ExtendedTashkinovTree G k e0 input' T' generating')
          (_ : other.rounds = ett.rounds) (_ : MaximumProperty other)
          (base' : HierarchyBase other generating') (K : TashkinovHierarchy other base')
          (_ : GoodHierarchy K) (_ : K.dividerCount < C.hierarchy.dividerCount),
          ColoredVertexSetElementary G generating' (TreeSequenceVertexSet T')))
      (_ :
        (∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
          {generating' : PartialEdgeColoring E k}
          {other : ExtendedTashkinovTree G k e0 input' T' generating'}
          {base' : HierarchyBase other generating'} (C' : HierarchyCounterexample base')
          (_ : other.rounds = ett.rounds)
          (_ : C'.hierarchy.dividerCount = C.hierarchy.dividerCount),
          ¬HierarchyCounterexampleLess (HierarchyCounterexampleMeasure C')
              (HierarchyCounterexampleMeasure C)))
      (_ :
        (let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
        let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
        (2 : ℕ) * ett.rounds + (11 : ℕ) ≤ (TreeMissingColors phi Tn).card))
      (hpositive : (0 : ℕ) < C.hierarchy.dividerCount),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let i : Fin H.dividerCount :=
      (⟨H.dividerCount - (1 : ℕ),
          id
            (fun (hpositive : (0 : ℕ) < H.dividerCount) ↦
              Decidable.byContradiction
                fun (a : ¬H.dividerCount - (1 : ℕ) < H.dividerCount) ↦ by omega)
            hpositive⟩ :
        Fin H.dividerCount);
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Tnext : TreeSequence G e0 := ett.series.data.tree n.succ;
    ∀ (_ : (0 : ℕ) < H.dividerCount) (_ : i.succ = q) (_ : A = H.stage q.castSucc)
      (hlen : T.length = A.length + (1 : ℕ))
      (_ :
        (∀ {X Y Z : TreeSequence G e0} (_ : TreeSequenceInitialSegment X Y)
          (_ : TreeSequenceInitialSegment Y Z), TreeSequenceInitialSegment X Z))
      (_ :
        (∀ {X Y Z : TreeSequence G e0} (_ : TreeSequenceInitialSegment X Z)
          (_ : TreeSequenceInitialSegment Y Z) (_ : X.length ≤ Y.length),
          TreeSequenceInitialSegment X Y))
      (_ :
        (∀ {X Y : TreeSequence G e0} (_ : TreeSequenceInitialSegment X Y)
          (_ : X.length = Y.length), X = Y))
      (_ : TreeSequenceInitialSegment A T)
      (_ :
        (∀ (a b : Fin (H.dividerCount + (2 : ℕ))) (_ : (↑a : ℕ) ≤ (↑b : ℕ)),
          TreeSequenceInitialSegment (H.stage a) (H.stage b)))
      (_ : TreeSequenceInitialSegment Tn A) (_ : Tn.length < A.length)
      (_ : TreeSequenceInitialSegment T Tnext) (_ : TreeSequenceInitialSegment A Tnext)
      (_ :
        (∀ (m : ℕ) (hm : (1 : ℕ) ≤ m) (hmT : m ≤ T.length),
          TreeSequenceInitialSegment (TreeSequencePrefix T m hm hmT) T))
      (_ : ColoredVertexSetElementary G phi (TreeSequenceVertexSet A)),
    let _ : Fin T.length := (⟨A.length, by omega⟩ : Fin T.length);
    False := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hproper hone hlower hfewer hminimal hlarge
      hpositive H q i A n Tn Tnext hqpos hiq hA hlen segmentTrans commonPrefix equalTrees hAT
      stagesNested hTnA hTnStrictA hTTnext hATnext prefixSegment hAElem r
  let f : E := T.edge r
  let y : V := T.vertex (Fin.last T.length)
  have hyOutside : y ∉ TreeSequenceVertexSet A := by
    intro hy
    obtain ⟨j, hj⟩ : ∃ j, A.vertex j = y := by
      simpa only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] using hy
    have he := hAT.2.1 j
    have hjy : T.vertex (Fin.castLE (Nat.succ_le_succ hAT.1) j) =
        T.vertex (Fin.last T.length) := he.trans hj
    have hidx := congrArg Fin.val (T.vertex_injective hjy)
    have hjlt := j.isLt
    simp only [Fin.val_castLE, Fin.val_last] at hidx
    omega
  have hvertices : TreeSequenceVertexSet T = insert y (TreeSequenceVertexSet A) := by
    exact @helper_hvertices_896 V E inferInstance inferInstance inferInstance inferInstance G k
        e0 input T phi ett base C hpositive hlen hAT
  have hcommon : ∃ alpha : Fin k,
      alpha ∈ TreeMissingColors phi A ∧ alpha ∈ MissingColors G phi y := by
    exact @helper_hcommon_1589 V E inferInstance inferInstance inferInstance inferInstance G k e0
        input T phi ett base C hAElem hvertices
  obtain ⟨alpha, halphaA, halphay⟩ := hcommon
  -- Retain the actual PE route or the exact SE/RE connecting seed.
  have terminalRoute : ∀ j : Fin (ett.rounds + 1), 0 < j.val →
      (ett.series.data.kind j = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence (ett.series.data.coloring j)
          (ett.series.data.tree j.castSucc) (ett.series.data.tree j.succ)) ∨
      ((ett.series.data.kind j = some TashkinovExtensionKind.SE ∨
          ett.series.data.kind j = some TashkinovExtensionKind.RE) ∧
        ∃ (edge : E) (seed : TreeSequence G e0),
          ett.series.data.connectingEdges j = {edge} ∧
          TreeSequenceAdjoinEdge (ett.series.data.tree j.castSucc) edge seed ∧
          TashkinovAugmentationSequence (ett.series.data.coloring j)
            seed (ett.series.data.tree j.succ)) := by
    exact @helper_terminalRoute_936 V E inferInstance inferInstance inferInstance G k e0 input T
        phi ett
  have hroute := terminalRoute n (by dsimp [n]; have := ett.roundsPositive; omega)
  rw [← ett.generatingColoring] at hroute
  have hAtoT : TashkinovAugmentationSequence phi A T := by
    exact @helper_hAtoT_1620 V E inferInstance inferInstance inferInstance inferInstance G k e0
        input T phi ett base C hpositive segmentTrans commonPrefix hAT hTnA hTnStrictA hTTnext
        hATnext hroute
  have hfinalAugmentation : TashkinovAugmentation phi A T := by
    have hpos := (TashkinovAugmentationSequencePosition phi A T hAtoT r
      (by rfl)).1
    have hpreA : TreeSequencePrefix T r.val A.positive (Nat.le_of_lt r.isLt) = A := by
      apply equalTrees
      · exact commonPrefix (prefixSegment _ _ _) hAT (le_refl _)
      · rfl
    have hpreT : TreeSequencePrefix T (r.val + 1) (by have := A.positive; omega)
        (Nat.succ_le_of_lt r.isLt) = T := by
      exact equalTrees (prefixSegment _ _ _) hlen.symm
    rw [hpreA, hpreT] at hpos
    exact hpos
  obtain ⟨hauglen, haugseg, gamma, hgammaEdge, hgammaA⟩ := hfinalAugmentation
  have hgammaf : phi f = some gamma := by
    have he : Fin.cast hauglen.symm (Fin.last A.length) = r := Fin.ext rfl
    simpa only [he] using hgammaEdge
  have hfEnds : ∃ u ∈ TreeSequenceVertexSet A, G.ends f = Sym2.mk u y := by
    exact @helper_hfEnds_1651 V E inferInstance inferInstance inferInstance inferInstance G k e0
        input T phi ett base C hpositive hlen hAT
  have firstMissingAfter (eta : Fin k) (heta : eta ∉ TreeMissingColors phi A) :
      (HierarchyFirstMissingPosition phi T eta).val = T.length := by
    exact congrArg Fin.val
      (TreeSequenceFirstMissingPositionEqLastOfNotMemPrefix hAT hlen.le heta)
  have hgammaTerminalExcluded : ∀ eta ∈ HierarchyStoredColorsAt H q,
      gamma ∉ C.good.gamma q eta := by
    exact @helper_hgammaTerminalExcluded_1690 V E inferInstance inferInstance inferInstance
        inferInstance G k e0 input T phi ett base C hpositive hlen gamma hgammaf firstMissingAfter
  obtain ⟨eta, ⟨heta, hrefresh, hother⟩, hunique⟩ := C.good.uniqueRefresh i
  have hcard := C.good.twoColors i.succ eta heta
  obtain ⟨theta, hthetaPair⟩ : (C.good.gamma i.succ eta).Nonempty :=
    Finset.card_pos.mp (by omega)
  have hthetaNew := hrefresh hthetaPair
  obtain ⟨x, hxNew, hthetax⟩ := Finset.mem_biUnion.mp hthetaNew
  have hxA : x ∈ TreeSequenceVertexSet A := by
    have hx := (Finset.mem_sdiff.mp hxNew).1
    change x ∈ TreeSequenceVertexSet (H.stage i.succ.castSucc) at hx
    rw [hiq, ← hA] at hx
    exact hx
  have hthetaA : theta ∈ TreeMissingColors phi A :=
    Finset.mem_biUnion.mpr ⟨x, hxA, hthetax⟩
  have hthetaClosed : TreeColorSetClosed G phi A {theta} := by
    have hstage : H.stage i.succ.castSucc = A := by rw [hiq, ← hA]
    have helem : ColoredVertexSetElementary G phi
        (TreeSequenceVertexSet (H.stage i.succ.castSucc)) := by
      rw [hstage]
      exact hAElem
    have hc := GoodHierarchyNewMissingClosed C.good i helem theta hthetaNew
    rw [hstage] at hc
    intro c hc'
    have he : c = theta := Finset.mem_singleton.mp hc'
    simpa only [he] using hc
  exact @helper_continuation_2074 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 input T phi ett base C hproper hone hlower hfewer hminimal hlarge hpositive hqpos hiq hA
      hlen segmentTrans commonPrefix equalTrees hAT stagesNested hTnA hTnStrictA hTTnext hATnext
      prefixSegment hAElem hyOutside alpha halphaA halphay hroute gamma hgammaA hgammaf hfEnds
      hgammaTerminalExcluded eta heta hcard theta hthetaPair hthetaNew x hthetax hxA hthetaA
      hthetaClosed
theorem HierarchyCounterexampleOneAdditionPositiveDividerImpossible
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (hproper : IsProperEdgeColoring G phi)
    (hone : IsOneEdgeUncolored phi e0)
    (hlower : LowerRoundInductionHypothesis G k e0 ett.rounds)
    (hfewer : ∀ {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      (other : ExtendedTashkinovTree G k e0 input' T' generating'),
      other.rounds = ett.rounds → MaximumProperty other →
      ∀ (base' : HierarchyBase other generating')
        (K : TashkinovHierarchy other base'),
        GoodHierarchy K → K.dividerCount < C.hierarchy.dividerCount →
        ColoredVertexSetElementary G generating'
          (TreeSequenceVertexSet T'))
    (hminimal : ∀ {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      {other : ExtendedTashkinovTree G k e0 input' T' generating'}
      {base' : HierarchyBase other generating'}
      (C' : HierarchyCounterexample base'),
      other.rounds = ett.rounds →
      C'.hierarchy.dividerCount = C.hierarchy.dividerCount →
      ¬ HierarchyCounterexampleLess
        (HierarchyCounterexampleMeasure C')
        (HierarchyCounterexampleMeasure C))
    (hlarge :
      let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
      let Tn := ett.series.data.tree n.castSucc
      2 * ett.rounds + 11 ≤ (TreeMissingColors phi Tn).card)
    (honeAddition :
      let H := C.hierarchy
      let A := HierarchyStarredStage H (Fin.last H.dividerCount)
      T.length - A.length = 1)
    (hprefixElementary :
      let H := C.hierarchy
      let A := HierarchyStarredStage H (Fin.last H.dividerCount)
      let ell := T.length - A.length
      let Ty := TreeSequencePrefix T
        (min (A.length + (ell - 1)) T.length)
        (by have hA := A.positive; have hT := T.positive; omega)
        (Nat.min_le_right _ _)
      ColoredVertexSetElementary G phi (TreeSequenceVertexSet Ty))
    (hpositive : 0 < C.hierarchy.dividerCount) :
    False := by
  classical
  let H := C.hierarchy
  let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
  let i : Fin H.dividerCount := ⟨H.dividerCount - 1, by
    change 0 < H.dividerCount at hpositive
    omega⟩
  let A := HierarchyStarredStage H q
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn := ett.series.data.tree n.castSucc
  let Tnext := ett.series.data.tree n.succ
  have hqpos : 0 < H.dividerCount := hpositive
  have hiq : i.succ = q := by
    apply Fin.ext
    dsimp [i, q]
    omega
  have hA : A = H.stage q.castSucc := by
    dsimp [A]
    rw [← hiq]
    rfl
  have hlen : T.length = A.length + 1 := by
    have hs := H.strict q
    have ht : H.stage q.succ = T := H.terminalStage
    rw [ht, ← hA] at hs
    change T.length - A.length = 1 at honeAddition
    omega
  have segmentTrans {X Y Z : TreeSequence G e0}
      (hXY : TreeSequenceInitialSegment X Y)
      (hYZ : TreeSequenceInitialSegment Y Z) :
      TreeSequenceInitialSegment X Z := by
    apply TreeSequenceInitialSegment.trans <;> assumption
  have commonPrefix {X Y Z : TreeSequence G e0}
      (hXZ : TreeSequenceInitialSegment X Z)
      (hYZ : TreeSequenceInitialSegment Y Z)
      (hXY : X.length ≤ Y.length) :
      TreeSequenceInitialSegment X Y := by
    exact hYZ.of_common_extension hXZ hXY
  have equalTrees {X Y : TreeSequence G e0}
      (hXY : TreeSequenceInitialSegment X Y)
      (hlenXY : X.length = Y.length) : X = Y := by
    exact hXY.eq_of_length_eq hlenXY
  have hAT : TreeSequenceInitialSegment A T := by
    rw [hA]
    have ht : H.stage q.succ = T := H.terminalStage
    have h := H.nested q
    rw [ht] at h
    exact h
  have stagesNested : ∀ a b : Fin (H.dividerCount + 2),
      a.val ≤ b.val → TreeSequenceInitialSegment (H.stage a) (H.stage b) := by
    intro first last ordered
    exact H.stageInitialSegmentOfLE first last ordered
  have hTnA : TreeSequenceInitialSegment Tn A := by
    rw [hA]
    have h := stagesNested 0 q.castSucc (by simp)
    simpa only [H.baseStage] using h
  have hTnStrictA : Tn.length < A.length := by
    have hfirst := H.strict 0
    have hz : (0 : Fin (H.dividerCount + 1)).castSucc =
        (0 : Fin (H.dividerCount + 2)) := Fin.ext (by simp)
    have ho : (0 : Fin (H.dividerCount + 1)).succ =
        (⟨1, by omega⟩ : Fin (H.dividerCount + 2)) := Fin.ext (by simp)
    rw [hz, ho, H.baseStage] at hfirst
    have hfirstA := stagesNested ⟨1, by omega⟩ q.castSucc (by
      change 1 ≤ H.dividerCount
      omega)
    rw [hA]
    exact lt_of_lt_of_le hfirst hfirstA.1
  have hTnext : Tnext = ett.series.data.tree (Fin.last (ett.rounds + 1)) := rfl
  have hTTnext : TreeSequenceInitialSegment T Tnext := ett.belowFinal
  have hATnext := segmentTrans hAT hTTnext
  have prefixSegment (m : ℕ) (hm : 1 ≤ m) (hmT : m ≤ T.length) :
      TreeSequenceInitialSegment (TreeSequencePrefix T m hm hmT) T := by
    exact ⟨hmT, fun _ => rfl, fun _ => rfl⟩
  have hprefixEq :
      TreeSequencePrefix T
        (min (A.length + (T.length - A.length - 1)) T.length)
        (by have := A.positive; have := T.positive; omega)
        (Nat.min_le_right _ _) = A := by
    apply equalTrees
    · apply commonPrefix
        (prefixSegment _ _ _) hAT
      change min (A.length + (T.length - A.length - 1)) T.length ≤ A.length
      omega
    · change min (A.length + (T.length - A.length - 1)) T.length = A.length
      omega
  have hAElem : ColoredVertexSetElementary G phi (TreeSequenceVertexSet A) := by
    change ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet (TreeSequencePrefix T
        (min (A.length + (T.length - A.length - 1)) T.length) _ _)) at hprefixElementary
    rw [hprefixEq] at hprefixElementary
    exact hprefixElementary
  let r : Fin T.length := ⟨A.length, by omega⟩
  exact @helper_continuation_2056 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 input T phi ett base C hproper hone hlower hfewer hminimal hlarge hpositive hqpos hiq hA
      hlen segmentTrans commonPrefix equalTrees hAT stagesNested hTnA hTnStrictA hTTnext hATnext
      prefixSegment hAElem
end GoldbergSeymour

end
