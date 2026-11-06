/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module



public import LeanPool.GoldbergSeymour.TerminalSeriesRebuildTransport
public import LeanPool.GoldbergSeymour.TdReplacementPrefixExact

/-!
# Td Terminal SEPERebuild

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open TerminalSeriesRebuild

private abbrev helperCaseContinuation422Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E]
   (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
   (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds)
   (sigma : PartialEdgeColoring E k),
   IsProperEdgeColoring G sigma →
    IsOneEdgeUncolored sigma e0 →
     StableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
       (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
       (ett.series.data.coloring (Fin.last ett.rounds)) sigma →
      ∀ (Tstar : TreeSequence G e0),
       TreeSequenceInitialSegment (ett.series.data.tree (Fin.last ett.rounds).castSucc) Tstar →
        (ett.series.data.tree (Fin.last ett.rounds).castSucc).length < Tstar.length →
         ∀ (closureTree : TreeSequence G e0),
          TreeSequenceInitialSegment Tstar closureTree →
           let q : Fin ett.rounds :=
            (⟨ett.rounds - (1 : ℕ), Nat.sub_lt (Nat.zero_lt_of_lt hpositive) (by omega)⟩ :
             Fin ett.rounds);
           q.succ = Fin.last ett.rounds →
            ∀
             (choice :
              MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
               (TashkinovStoredColors ett.series.data q.castSucc)
               (ett.series.data.coloring q.castSucc)),
             ett.series.data.stored q.succ = ({ choice.color } : Finset (Fin k)) →
              ett.series.data.connectingEdges q.succ = ({ choice.edge } : Finset E) →
               ett.series.data.kind q.succ = some TashkinovExtensionKind.SE →
                ∀ (sigmaPrev : PartialEdgeColoring E k),
                 (1 : ℕ) < ett.rounds →
                  ∀
                   (originalPrefix :
                    ExtendedTashkinovTree G k e0 input
                     (ett.series.data.tree (Fin.last ett.rounds).castSucc)
                     (ett.series.data.coloring
                      (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin (ett.rounds + (1 : ℕ)))))
                   (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ)),
                   (∀ (i : Fin (originalPrefix.rounds + (2 : ℕ))),
                     originalPrefix.series.data.tree i =
                      ett.series.data.tree (Fin.castLE (by omega) i)) →
                    (∀ (i : Fin (originalPrefix.rounds + (1 : ℕ))),
                      originalPrefix.series.data.coloring i =
                        ett.series.data.coloring (Fin.castLE (by omega) i) ∧
                       originalPrefix.series.data.stored i =
                         ett.series.data.stored (Fin.castLE (by omega) i) ∧
                        originalPrefix.series.data.connectingEdges i =
                          ett.series.data.connectingEdges (Fin.castLE (by omega) i) ∧
                         originalPrefix.series.data.kind i =
                           ett.series.data.kind (Fin.castLE (by omega) i) ∧
                          TashkinovStoredColors originalPrefix.series.data i =
                           TashkinovStoredColors ett.series.data (Fin.castLE (by omega) i)) →
                     ∀
                      (corr :
                       CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
                        (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
                      let replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) :=
                       Fin.last originalPrefix.rounds;
                      (0 : ℕ) < originalPrefix.rounds →
                       corr.replacementSeries.data.tree replacementLast.succ =
                         ett.series.data.tree q.succ.castSucc →
                        let newStored : Finset (Fin k) := ({ choice.color } : Finset (Fin k));
                        let newEdges : Finset E := ({ choice.edge } : Finset E);
                        let newKind : Option TashkinovExtensionKind :=
                         some TashkinovExtensionKind.SE;
                        let newVertex : Option V := some choice.vertex;
                        let newOutside : Option V := some choice.otherEndpoint;
                        let newDelta : Option (Fin k) := some choice.color;
                        let newGamma : Option (Fin k) := none;
                        let appendedData :
                         TashkinovSeriesData G k (originalPrefix.rounds + (1 : ℕ)) e0 :=
                         TashkinovSeriesDataAppend corr.replacementSeries.data closureTree sigma
                          newStored newEdges newKind newVertex newOutside newDelta newGamma;
                        TashkinovSeriesStep G k (originalPrefix.rounds + (1 : ℕ)) e0
                          corr.replacementInput appendedData
                          (Fin.last (originalPrefix.rounds + (1 : ℕ))) →
                         Nonempty (CorrespondingExtendedTashkinovTree G k e0 ett sigma Tstar)

private abbrev helperCaseContinuation1078Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E]
   (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
   (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds)
   (sigma : PartialEdgeColoring E k),
   IsProperEdgeColoring G sigma →
    IsOneEdgeUncolored sigma e0 →
     StableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
       (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
       (ett.series.data.coloring (Fin.last ett.rounds)) sigma →
      ∀ (Tstar : TreeSequence G e0),
       TreeSequenceInitialSegment (ett.series.data.tree (Fin.last ett.rounds).castSucc) Tstar →
        (ett.series.data.tree (Fin.last ett.rounds).castSucc).length < Tstar.length →
         ∀ (closureTree : TreeSequence G e0),
          TreeSequenceInitialSegment Tstar closureTree →
           let q : Fin ett.rounds :=
            (⟨ett.rounds - (1 : ℕ), Nat.sub_lt (Nat.zero_lt_of_lt hpositive) (by omega)⟩ :
             Fin ett.rounds);
           q.succ = Fin.last ett.rounds →
            ∀ (gamma : Fin k)
             (choice :
              MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
               (TashkinovStoredColors ett.series.data q.castSucc)
               (ett.series.data.coloring q.castSucc)),
             ett.series.data.stored q.succ =
               (insert choice.color ({ gamma } : Finset (Fin k)) : Finset (Fin k)) →
              ett.series.data.connectingEdges q.succ = ({ choice.edge } : Finset E) →
               ett.series.data.kind q.succ = some TashkinovExtensionKind.PE →
                ∀ (sigmaPrev : PartialEdgeColoring E k),
                 let H : SimpleGraph (V ⊕ E) :=
                  TwoColorIncidenceGraph G sigmaPrev gamma choice.color;
                 ∀ (a b : V ⊕ E) (u : V) (p : H.Walk (Sum.inl choice.vertex) (Sum.inl u)),
                  (1 : ℕ) < ett.rounds →
                   ∀
                    (originalPrefix :
                     ExtendedTashkinovTree G k e0 input
                      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
                      (ett.series.data.coloring
                       (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin (ett.rounds + (1 : ℕ)))))
                    (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ)),
                    (∀ (i : Fin (originalPrefix.rounds + (2 : ℕ))),
                      originalPrefix.series.data.tree i =
                       ett.series.data.tree (Fin.castLE (by omega) i)) →
                     (∀ (i : Fin (originalPrefix.rounds + (1 : ℕ))),
                       originalPrefix.series.data.coloring i =
                         ett.series.data.coloring (Fin.castLE (by omega) i) ∧
                        originalPrefix.series.data.stored i =
                          ett.series.data.stored (Fin.castLE (by omega) i) ∧
                         originalPrefix.series.data.connectingEdges i =
                           ett.series.data.connectingEdges (Fin.castLE (by omega) i) ∧
                          originalPrefix.series.data.kind i =
                            ett.series.data.kind (Fin.castLE (by omega) i) ∧
                           TashkinovStoredColors originalPrefix.series.data i =
                            TashkinovStoredColors ett.series.data (Fin.castLE (by omega) i)) →
                      ∀
                       (corr :
                        CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
                         (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
                       let replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) :=
                        Fin.last originalPrefix.rounds;
                       (0 : ℕ) < originalPrefix.rounds →
                        corr.replacementSeries.data.tree replacementLast.succ =
                          ett.series.data.tree q.succ.castSucc →
                         let newStored : Finset (Fin k) :=
                          (insert choice.color ({ gamma } : Finset (Fin k)) : Finset (Fin k));
                         let newEdges : Finset E := ({ choice.edge } : Finset E);
                         let newKind : Option TashkinovExtensionKind :=
                          some TashkinovExtensionKind.PE;
                         let newVertex : Option V := some choice.vertex;
                         let newOutside : Option V := some choice.otherEndpoint;
                         let newDelta : Option (Fin k) := some choice.color;
                         let newGamma : Option (Fin k) := some gamma;
                         let appendedData :
                          TashkinovSeriesData G k (originalPrefix.rounds + (1 : ℕ)) e0 :=
                          TashkinovSeriesDataAppend corr.replacementSeries.data closureTree sigma
                           newStored newEdges newKind newVertex newOutside newDelta newGamma;
                         TashkinovSeriesStep G k (originalPrefix.rounds + (1 : ℕ)) e0
                           corr.replacementInput appendedData
                           (Fin.last (originalPrefix.rounds + (1 : ℕ))) →
                          Nonempty (CorrespondingExtendedTashkinovTree G k e0 ett sigma Tstar)

private abbrev helperBranch1075Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E]
   (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
   (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds)
   (sigma : PartialEdgeColoring E k),
   IsProperEdgeColoring G sigma →
    IsOneEdgeUncolored sigma e0 →
     StableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
       (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
       (ett.series.data.coloring (Fin.last ett.rounds)) sigma →
      ∀ (Tstar : TreeSequence G e0),
       TreeSequenceInitialSegment (ett.series.data.tree (Fin.last ett.rounds).castSucc) Tstar →
        (ett.series.data.tree (Fin.last ett.rounds).castSucc).length < Tstar.length →
         ∀ (closureTree : TreeSequence G e0),
          TashkinovClosure sigma Tstar closureTree →
           TreeSequenceInitialSegment Tstar closureTree →
            TreeSequenceInitialSegment (ett.series.data.tree (Fin.last ett.rounds).castSucc)
              closureTree →
             let q : Fin ett.rounds :=
              (⟨ett.rounds - (1 : ℕ), Nat.sub_lt (Nat.zero_lt_of_lt hpositive) (by omega)⟩ :
               Fin ett.rounds);
             q.succ = Fin.last ett.rounds →
              ∀ (gamma : Fin k) (secondStable : PartialEdgeColoring E k)
               (previousProper : IsProperEdgeColoring G (ett.series.data.coloring q.castSucc))
               (previousOneUncolored : IsOneEdgeUncolored (ett.series.data.coloring q.castSucc) e0)
               (choice :
                MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
                 (TashkinovStoredColors ett.series.data q.castSucc)
                 (ett.series.data.coloring q.castSucc)),
               ett.series.data.stored q.succ =
                 (insert choice.color ({ gamma } : Finset (Fin k)) : Finset (Fin k)) →
                ett.series.data.connectingEdges q.succ = ({ choice.edge } : Finset E) →
                 ett.series.data.kind q.succ = some TashkinovExtensionKind.PE →
                  ∀ (sigmaPrev : PartialEdgeColoring E k)
                   (hsigmaPrevProper : IsProperEdgeColoring G sigmaPrev)
                   (hsigmaPrevOne : IsOneEdgeUncolored sigmaPrev e0)
                   (hsigmaPrevStableQ :
                    StableColoring (ett.series.data.tree q.succ.castSucc)
                     (TashkinovStoredColors ett.series.data q.castSucc)
                     (ett.series.data.coloring q.castSucc) sigmaPrev)
                   (hchoiceDefective :
                    DefectiveColor G sigmaPrev
                     (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) choice.color)
                   (hchoiceEdgeNew :
                    choice.edge ∈
                     BoundaryColorEdges G sigmaPrev
                      (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) choice.color)
                   (hsigmaPrevSelf :
                    StableColoring (ett.series.data.tree q.succ.castSucc)
                     (TashkinovStoredColors ett.series.data q.castSucc) sigmaPrev sigmaPrev),
                   ColoredVertexSetClosed G sigmaPrev
                     (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) →
                    ¬ColoredVertexSetStronglyClosed G sigmaPrev
                       (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) →
                     sigma =
                       TwoColorComponentSwap G sigmaPrev gamma choice.color
                        (Sum.inl choice.vertex) →
                      let H : SimpleGraph (V ⊕ E) :=
                       TwoColorIncidenceGraph G sigmaPrev gamma choice.color;
                      ∀ (a b : V ⊕ E) (u : V) (p : H.Walk (Sum.inl choice.vertex) (Sum.inl u)),
                       TreeExit (ett.series.data.tree q.succ.castSucc) sigmaPrev gamma choice.color
                         choice.vertex →
                        (1 : ℕ) < ett.rounds →
                         ∀
                          (originalPrefix :
                           ExtendedTashkinovTree G k e0 input
                            (ett.series.data.tree (Fin.last ett.rounds).castSucc)
                            (ett.series.data.coloring
                             (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin (ett.rounds + (1 : ℕ)))))
                          (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ)),
                          (∀ (i : Fin (originalPrefix.rounds + (2 : ℕ))),
                            originalPrefix.series.data.tree i =
                             ett.series.data.tree (Fin.castLE (by omega) i)) →
                           (∀ (i : Fin (originalPrefix.rounds + (1 : ℕ))),
                             originalPrefix.series.data.coloring i =
                               ett.series.data.coloring (Fin.castLE (by omega) i) ∧
                              originalPrefix.series.data.stored i =
                                ett.series.data.stored (Fin.castLE (by omega) i) ∧
                               originalPrefix.series.data.connectingEdges i =
                                 ett.series.data.connectingEdges (Fin.castLE (by omega) i) ∧
                                originalPrefix.series.data.kind i =
                                  ett.series.data.kind (Fin.castLE (by omega) i) ∧
                                 TashkinovStoredColors originalPrefix.series.data i =
                                  TashkinovStoredColors ett.series.data (Fin.castLE (by omega) i)) →
                            ∀
                             (corr :
                              CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
                               (ett.series.data.tree (Fin.last ett.rounds).castSucc))
                             (hcorrFinalColor :
                              corr.replacementSeries.data.coloring
                                (Fin.last originalPrefix.rounds) =
                               sigmaPrev),
                             let replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) :=
                              Fin.last originalPrefix.rounds;
                             (0 : ℕ) < originalPrefix.rounds →
                              ∀
                               (hreplacementCurrentTree :
                                corr.replacementSeries.data.tree replacementLast.succ =
                                 ett.series.data.tree q.succ.castSucc)
                               (hreplacementStored :
                                TashkinovStoredColors corr.replacementSeries.data replacementLast =
                                 TashkinovStoredColors ett.series.data q.castSucc),
                               let replacementChoice :
                                MaximumDefectiveChoice G e0
                                 (corr.replacementSeries.data.tree replacementLast.succ)
                                 (TashkinovStoredColors corr.replacementSeries.data replacementLast)
                                 (corr.replacementSeries.data.coloring replacementLast) :=
                                helperReplacementChoice5196 G k e0 input T generating ett hpositive
                                  previousProper previousOneUncolored choice sigmaPrev
                                 hsigmaPrevProper hsigmaPrevOne hsigmaPrevStableQ hchoiceDefective
                                 hchoiceEdgeNew hsigmaPrevSelf originalPrefix corr hcorrFinalColor
                                 hreplacementCurrentTree hreplacementStored;
                               ¬Nonempty
                                  (RevisitingExtensionCertificate corr.replacementSeries.data
                                   replacementLast) →
                                (∃ (rho : PartialEdgeColoring E k),
                                  IsProperEdgeColoring G rho ∧
                                   IsOneEdgeUncolored rho e0 ∧
                                    StableColoring
                                      (corr.replacementSeries.data.tree replacementLast.succ)
                                      (insert replacementChoice.color
                                        (TashkinovStoredColors corr.replacementSeries.data
                                         replacementLast) :
                                       Finset (Fin k))
                                      replacementChoice.selected rho ∧
                                     ¬Disjoint (MissingColors G rho replacementChoice.otherEndpoint)
                                       (TreeMissingColors rho
                                        (corr.replacementSeries.data.tree replacementLast.succ))) →
                                 ParallelExtensionColor corr.replacementSeries.data replacementLast
                                   replacementChoice.selected replacementChoice.vertex gamma →
                                  ett.series.data.kind (Fin.last ett.rounds) =
                                     some TashkinovExtensionKind.PE ∧
                                    TashkinovAugmentationSequence sigma
                                     (ett.series.data.tree (Fin.last ett.rounds).castSucc) Tstar →
                                   Nonempty
                                    (CorrespondingExtendedTashkinovTree G k e0 ett sigma Tstar)

private abbrev helperCaseContinuation1201Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T generating),
   MaximumProperty ett →
    ∀ (hpositive : (0 : ℕ) < ett.rounds),
     LowerRoundInductionHypothesis G k e0 ett.rounds →
      ∀ (sigma : PartialEdgeColoring E k),
       IsProperEdgeColoring G sigma →
        IsOneEdgeUncolored sigma e0 →
         StableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
           (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
           (ett.series.data.coloring (Fin.last ett.rounds)) sigma →
          ∀ (Tstar : TreeSequence G e0),
           TreeSequenceInitialSegment (ett.series.data.tree (Fin.last ett.rounds).castSucc) Tstar →
            (ett.series.data.tree (Fin.last ett.rounds).castSucc).length < Tstar.length →
             (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE ∧
                TashkinovAugmentationSequence sigma
                 (ett.series.data.tree (Fin.last ett.rounds).castSucc) Tstar ∨
               (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.SE ∨
                 ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.RE) ∧
                ∃ (f : E) (seed : TreeSequence G e0),
                 ett.series.data.connectingEdges (Fin.last ett.rounds) = ({ f } : Finset E) ∧
                  TreeSequenceAdjoinEdge (ett.series.data.tree (Fin.last ett.rounds).castSucc) f
                    seed ∧
                   TashkinovAugmentationSequence sigma seed Tstar) →
              ∀ (closureTree : TreeSequence G e0),
               TashkinovClosure sigma Tstar closureTree →
                TreeSequenceInitialSegment Tstar closureTree →
                 TreeSequenceInitialSegment (ett.series.data.tree (Fin.last ett.rounds).castSucc)
                   closureTree →
                  let q : Fin ett.rounds :=
                   (⟨ett.rounds - (1 : ℕ), Nat.sub_lt (Nat.zero_lt_of_lt hpositive) (by omega)⟩ :
                    Fin ett.rounds);
                  q.succ = Fin.last ett.rounds →
                   ∀ (gamma : Fin k) (secondStable : PartialEdgeColoring E k)
                    (previousProper : IsProperEdgeColoring G (ett.series.data.coloring q.castSucc))
                    (previousOneUncolored :
                     IsOneEdgeUncolored (ett.series.data.coloring q.castSucc) e0),
                    ¬Nonempty (RevisitingExtensionCertificate ett.series.data q.castSucc) →
                     ∀
                      (choice :
                       MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
                        (TashkinovStoredColors ett.series.data q.castSucc)
                        (ett.series.data.coloring q.castSucc)),
                      ParallelExtensionColor ett.series.data q.castSucc choice.selected
                        choice.vertex gamma →
                       ett.series.data.stored q.succ =
                         (insert choice.color ({ gamma } : Finset (Fin k)) : Finset (Fin k)) →
                        ett.series.data.connectingEdges q.succ = ({ choice.edge } : Finset E) →
                         ett.series.data.kind q.succ = some TashkinovExtensionKind.PE →
                          ett.series.data.kind q.succ = some TashkinovExtensionKind.PE →
                           ∀ (sigmaPrev : PartialEdgeColoring E k)
                            (hsigmaPrevProper : IsProperEdgeColoring G sigmaPrev)
                            (hsigmaPrevOne : IsOneEdgeUncolored sigmaPrev e0),
                            ((ett.rounds = (1 : ℕ) ∧
                               ∃ (prefixInput : PartialEdgeColoring E k) (zeroPrefix :
                                TashkinovSeries G k (0 : ℕ) e0 prefixInput),
                                zeroPrefix.data.tree (Fin.last (1 : ℕ)) =
                                  ett.series.data.tree (Fin.last ett.rounds).castSucc ∧
                                 zeroPrefix.data.coloring (Fin.last (0 : ℕ)) = sigmaPrev) ∨
                              (1 : ℕ) < ett.rounds ∧
                               ∃ (originalPrefix :
                                ExtendedTashkinovTree G k e0 input
                                 (ett.series.data.tree (Fin.last ett.rounds).castSucc)
                                 (ett.series.data.coloring
                                  (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin (ett.rounds + (1 : ℕ)))))
                                (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ)),
                                MaximumProperty originalPrefix ∧
                                 (∀ (i : Fin (originalPrefix.rounds + (2 : ℕ))),
                                   originalPrefix.series.data.tree i =
                                    ett.series.data.tree (Fin.castLE (by omega) i)) ∧
                                  (∀ (i : Fin (originalPrefix.rounds + (1 : ℕ))),
                                    originalPrefix.series.data.coloring i =
                                      ett.series.data.coloring (Fin.castLE (by omega) i) ∧
                                     originalPrefix.series.data.stored i =
                                       ett.series.data.stored (Fin.castLE (by omega) i) ∧
                                      originalPrefix.series.data.connectingEdges i =
                                        ett.series.data.connectingEdges (Fin.castLE (by omega) i) ∧
                                       originalPrefix.series.data.kind i =
                                         ett.series.data.kind (Fin.castLE (by omega) i) ∧
                                        TashkinovStoredColors originalPrefix.series.data i =
                                         TashkinovStoredColors ett.series.data
                                          (Fin.castLE (by omega) i)) ∧
                                   ∃ (corr :
                                    CorrespondingExtendedTashkinovTree G k e0 originalPrefix
                                     sigmaPrev
                                     (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
                                    corr.replacementSeries.data.tree
                                       (Fin.last (originalPrefix.rounds + (1 : ℕ))) =
                                      ett.series.data.tree (Fin.last ett.rounds).castSucc ∧
                                     corr.replacementSeries.data.coloring
                                        (Fin.last originalPrefix.rounds) =
                                       sigmaPrev ∧
                                      MaximumProperty corr.replacementETT) →
                             ∀
                              (hsigmaPrevStableQ :
                               StableColoring (ett.series.data.tree q.succ.castSucc)
                                (TashkinovStoredColors ett.series.data q.castSucc)
                                (ett.series.data.coloring q.castSucc) sigmaPrev),
                              choice.vertex ∈
                                TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc) →
                               sigmaPrev =
                                 TwoColorComponentSwap G sigma gamma choice.color
                                  (Sum.inl choice.vertex) →
                                ∀
                                 (hchoiceDefective :
                                  DefectiveColor G sigmaPrev
                                   (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc))
                                   choice.color)
                                 (hchoiceEdgeNew :
                                  choice.edge ∈
                                   BoundaryColorEdges G sigmaPrev
                                    (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc))
                                    choice.color)
                                 (hsigmaPrevSelf :
                                  StableColoring (ett.series.data.tree q.succ.castSucc)
                                   (TashkinovStoredColors ett.series.data q.castSucc) sigmaPrev
                                   sigmaPrev),
                                 let newChoice :
                                  MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
                                   (TashkinovStoredColors ett.series.data q.castSucc) sigmaPrev :=
                                  helperNewChoice4049 G k e0 input T generating ett hpositive
                                   previousProper previousOneUncolored choice sigmaPrev
                                   hsigmaPrevProper hsigmaPrevOne hsigmaPrevStableQ hchoiceDefective
                                   hchoiceEdgeNew hsigmaPrevSelf;
                                 ColoredVertexSetClosed G sigmaPrev
                                   (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) →
                                  ¬ColoredVertexSetStronglyClosed G sigmaPrev
                                     (TreeSequenceVertexSet
                                      (ett.series.data.tree q.succ.castSucc)) →
                                   (∃ (rho : PartialEdgeColoring E k),
                                     IsProperEdgeColoring G rho ∧
                                      IsOneEdgeUncolored rho e0 ∧
                                       StableColoring (ett.series.data.tree q.succ.castSucc)
                                         (insert newChoice.color
                                           (TashkinovStoredColors ett.series.data q.castSucc) :
                                          Finset (Fin k))
                                         newChoice.selected rho ∧
                                        ¬Disjoint (MissingColors G rho newChoice.otherEndpoint)
                                          (TreeMissingColors rho
                                           (ett.series.data.tree q.succ.castSucc))) →
                                    gamma ≠ choice.color →
                                     (∀ (f : E),
                                       Sum.inr f ∈
                                         TwoColorComponent G sigma gamma choice.color
                                          (Sum.inl choice.vertex) →
                                        sigma f = some gamma ∨ sigma f = some choice.color) →
                                      gamma ∈ MissingColors G sigmaPrev choice.vertex →
                                       TwoColorIncidenceGraph G sigmaPrev gamma choice.color =
                                         TwoColorIncidenceGraph G sigma gamma choice.color →
                                        (∀
                                          w ∈
                                           TreeSequenceVertexSet
                                            (ett.series.data.tree q.succ.castSucc),
                                          Sum.inl w ∈
                                            TwoColorComponent G sigmaPrev gamma choice.color
                                             (Sum.inl choice.vertex) ↔
                                           w = choice.vertex) →
                                         Nonempty
                                          (CorrespondingExtendedTashkinovTree G k e0 ett sigma
                                           Tstar)

private abbrev helperBranch1497Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E]
   (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
   (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds)
   (sigma : PartialEdgeColoring E k),
   IsProperEdgeColoring G sigma →
    IsOneEdgeUncolored sigma e0 →
     StableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
       (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
       (ett.series.data.coloring (Fin.last ett.rounds)) sigma →
      ∀ (Tstar : TreeSequence G e0),
       TreeSequenceInitialSegment (ett.series.data.tree (Fin.last ett.rounds).castSucc) Tstar →
        (ett.series.data.tree (Fin.last ett.rounds).castSucc).length < Tstar.length →
         ∀ (closureTree : TreeSequence G e0),
          TashkinovClosure sigma Tstar closureTree →
           TreeSequenceInitialSegment Tstar closureTree →
            TreeSequenceInitialSegment (ett.series.data.tree (Fin.last ett.rounds).castSucc)
              closureTree →
             let q : Fin ett.rounds :=
              (⟨ett.rounds - (1 : ℕ), Nat.sub_lt (Nat.zero_lt_of_lt hpositive) (by omega)⟩ :
               Fin ett.rounds);
             q.succ = Fin.last ett.rounds →
              ∀ (adjoined : TreeSequence G e0)
               (previousProper : IsProperEdgeColoring G (ett.series.data.coloring q.castSucc))
               (previousOneUncolored : IsOneEdgeUncolored (ett.series.data.coloring q.castSucc) e0)
               (choice :
                MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
                 (TashkinovStoredColors ett.series.data q.castSucc)
                 (ett.series.data.coloring q.castSucc)),
               ett.series.data.stored q.succ = ({ choice.color } : Finset (Fin k)) →
                ett.series.data.connectingEdges q.succ = ({ choice.edge } : Finset E) →
                 ett.series.data.kind q.succ = some TashkinovExtensionKind.SE →
                  ∀ (sigmaPrev : PartialEdgeColoring E k)
                   (hsigmaPrevProper : IsProperEdgeColoring G sigmaPrev)
                   (hsigmaPrevOne : IsOneEdgeUncolored sigmaPrev e0)
                   (hsigmaPrevStableQ :
                    StableColoring (ett.series.data.tree q.succ.castSucc)
                     (TashkinovStoredColors ett.series.data q.castSucc)
                     (ett.series.data.coloring q.castSucc) sigmaPrev),
                   sigmaPrev = sigma →
                    ∀
                     (hchoiceDefective :
                      DefectiveColor G sigmaPrev
                       (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) choice.color)
                     (hchoiceEdgeNew :
                      choice.edge ∈
                       BoundaryColorEdges G sigmaPrev
                        (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) choice.color)
                     (hsigmaPrevSelf :
                      StableColoring (ett.series.data.tree q.succ.castSucc)
                       (TashkinovStoredColors ett.series.data q.castSucc) sigmaPrev sigmaPrev),
                     ColoredVertexSetClosed G sigmaPrev
                       (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) →
                      ¬ColoredVertexSetStronglyClosed G sigmaPrev
                         (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) →
                       (1 : ℕ) < ett.rounds →
                        ∀
                         (originalPrefix :
                          ExtendedTashkinovTree G k e0 input
                           (ett.series.data.tree (Fin.last ett.rounds).castSucc)
                           (ett.series.data.coloring
                            (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin (ett.rounds + (1 : ℕ)))))
                         (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ)),
                         (∀ (i : Fin (originalPrefix.rounds + (2 : ℕ))),
                           originalPrefix.series.data.tree i =
                            ett.series.data.tree (Fin.castLE (by omega) i)) →
                          (∀ (i : Fin (originalPrefix.rounds + (1 : ℕ))),
                            originalPrefix.series.data.coloring i =
                              ett.series.data.coloring (Fin.castLE (by omega) i) ∧
                             originalPrefix.series.data.stored i =
                               ett.series.data.stored (Fin.castLE (by omega) i) ∧
                              originalPrefix.series.data.connectingEdges i =
                                ett.series.data.connectingEdges (Fin.castLE (by omega) i) ∧
                               originalPrefix.series.data.kind i =
                                 ett.series.data.kind (Fin.castLE (by omega) i) ∧
                                TashkinovStoredColors originalPrefix.series.data i =
                                 TashkinovStoredColors ett.series.data (Fin.castLE (by omega) i)) →
                           ∀
                            (corr :
                             CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
                              (ett.series.data.tree (Fin.last ett.rounds).castSucc))
                            (hcorrFinalColor :
                             corr.replacementSeries.data.coloring (Fin.last originalPrefix.rounds) =
                              sigmaPrev),
                            let replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) :=
                             Fin.last originalPrefix.rounds;
                            (0 : ℕ) < originalPrefix.rounds →
                             ∀
                              (hreplacementCurrentTree :
                               corr.replacementSeries.data.tree replacementLast.succ =
                                ett.series.data.tree q.succ.castSucc)
                              (hreplacementStored :
                               TashkinovStoredColors corr.replacementSeries.data replacementLast =
                                TashkinovStoredColors ett.series.data q.castSucc),
                              let replacementChoice :
                               MaximumDefectiveChoice G e0
                                (corr.replacementSeries.data.tree replacementLast.succ)
                                (TashkinovStoredColors corr.replacementSeries.data replacementLast)
                                (corr.replacementSeries.data.coloring replacementLast) :=
                               helperReplacementChoice3411 G k e0 input T generating ett hpositive
                                 previousProper previousOneUncolored choice sigmaPrev
                                hsigmaPrevProper hsigmaPrevOne hsigmaPrevStableQ hchoiceDefective
                                hchoiceEdgeNew hsigmaPrevSelf originalPrefix corr hcorrFinalColor
                                hreplacementCurrentTree hreplacementStored;
                              ¬Nonempty
                                 (RevisitingExtensionCertificate corr.replacementSeries.data
                                  replacementLast) →
                               (∀ (pi : PartialEdgeColoring E k),
                                 IsProperEdgeColoring G pi →
                                  IsOneEdgeUncolored pi e0 →
                                   StableColoring
                                     (corr.replacementSeries.data.tree replacementLast.succ)
                                     (insert replacementChoice.color
                                       (TashkinovStoredColors corr.replacementSeries.data
                                        replacementLast) :
                                      Finset (Fin k))
                                     replacementChoice.selected pi →
                                    Disjoint (MissingColors G pi replacementChoice.otherEndpoint)
                                     (TreeMissingColors pi
                                      (corr.replacementSeries.data.tree replacementLast.succ))) →
                                ((ett.series.data.kind (Fin.last ett.rounds) =
                                    some TashkinovExtensionKind.SE ∨
                                   ett.series.data.kind (Fin.last ett.rounds) =
                                    some TashkinovExtensionKind.RE) ∧
                                  ∃ (f : E) (seed : TreeSequence G e0),
                                   ett.series.data.connectingEdges (Fin.last ett.rounds) =
                                     ({ f } : Finset E) ∧
                                    TreeSequenceAdjoinEdge
                                      (ett.series.data.tree (Fin.last ett.rounds).castSucc) f seed ∧
                                     TashkinovAugmentationSequence sigma seed Tstar) →
                                 Nonempty
                                  (CorrespondingExtendedTashkinovTree G k e0 ett sigma Tstar)

private abbrev helperBranch1661Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T generating),
   MaximumProperty ett →
    ∀ (hpositive : (0 : ℕ) < ett.rounds),
     LowerRoundInductionHypothesis G k e0 ett.rounds →
      ∀ (sigma : PartialEdgeColoring E k),
       IsProperEdgeColoring G sigma →
        IsOneEdgeUncolored sigma e0 →
         StableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
           (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
           (ett.series.data.coloring (Fin.last ett.rounds)) sigma →
          ∀ (Tstar : TreeSequence G e0),
           TreeSequenceInitialSegment (ett.series.data.tree (Fin.last ett.rounds).castSucc) Tstar →
            (ett.series.data.tree (Fin.last ett.rounds).castSucc).length < Tstar.length →
             (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE ∧
                TashkinovAugmentationSequence sigma
                 (ett.series.data.tree (Fin.last ett.rounds).castSucc) Tstar ∨
               (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.SE ∨
                 ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.RE) ∧
                ∃ (f : E) (seed : TreeSequence G e0),
                 ett.series.data.connectingEdges (Fin.last ett.rounds) = ({ f } : Finset E) ∧
                  TreeSequenceAdjoinEdge (ett.series.data.tree (Fin.last ett.rounds).castSucc) f
                    seed ∧
                   TashkinovAugmentationSequence sigma seed Tstar) →
              ∀ (closureTree : TreeSequence G e0),
               TashkinovClosure sigma Tstar closureTree →
                TreeSequenceInitialSegment Tstar closureTree →
                 TreeSequenceInitialSegment (ett.series.data.tree (Fin.last ett.rounds).castSucc)
                   closureTree →
                  let q : Fin ett.rounds :=
                   (⟨ett.rounds - (1 : ℕ), Nat.sub_lt (Nat.zero_lt_of_lt hpositive) (by omega)⟩ :
                    Fin ett.rounds);
                  q.succ = Fin.last ett.rounds →
                   q.castSucc = (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin (ett.rounds + (1 : ℕ))) →
                    StableColoring (ett.series.data.tree q.succ.castSucc)
                      (TashkinovStoredColors ett.series.data q.succ)
                      (ett.series.data.coloring q.succ) sigma →
                     ∀ (i : Fin ett.rounds),
                      IsProperEdgeColoring G (ett.series.data.coloring i.castSucc) →
                       IsOneEdgeUncolored (ett.series.data.coloring i.castSucc) e0 →
                        ColoredVertexSetClosed G (ett.series.data.coloring i.castSucc)
                          (TreeSequenceVertexSet (ett.series.data.tree i.succ.castSucc)) →
                         ¬ColoredVertexSetStronglyClosed G (ett.series.data.coloring i.castSucc)
                            (TreeSequenceVertexSet (ett.series.data.tree i.succ.castSucc)) →
                          ¬Nonempty (RevisitingExtensionCertificate ett.series.data i.castSucc) →
                           ∀
                            (choice :
                             MaximumDefectiveChoice G e0 (ett.series.data.tree i.succ.castSucc)
                              (TashkinovStoredColors ett.series.data i.castSucc)
                              (ett.series.data.coloring i.castSucc)),
                            (∃ (rho : PartialEdgeColoring E k),
                              IsProperEdgeColoring G rho ∧
                               IsOneEdgeUncolored rho e0 ∧
                                StableColoring (ett.series.data.tree i.succ.castSucc)
                                  (insert choice.color
                                    (TashkinovStoredColors ett.series.data i.castSucc) :
                                   Finset (Fin k))
                                  choice.selected rho ∧
                                 ¬Disjoint (MissingColors G rho choice.otherEndpoint)
                                   (TreeMissingColors rho (ett.series.data.tree i.succ.castSucc))) →
                             ∀ (gamma : Fin k),
                              ParallelExtensionColor ett.series.data i.castSucc choice.selected
                                choice.vertex gamma →
                               ∀ (secondStable : PartialEdgeColoring E k),
                                IsProperEdgeColoring G secondStable →
                                 IsOneEdgeUncolored secondStable e0 →
                                  StableColoring (ett.series.data.tree i.succ.castSucc)
                                    (insert choice.color
                                      (TashkinovStoredColors ett.series.data i.castSucc) :
                                     Finset (Fin k))
                                    choice.selected secondStable →
                                   TreeExit (ett.series.data.tree i.succ.castSucc) secondStable
                                     gamma choice.color choice.vertex →
                                    ett.series.data.coloring i.succ =
                                      TwoColorComponentSwap G secondStable gamma choice.color
                                       (Sum.inl choice.vertex) →
                                     IsProperEdgeColoring G (ett.series.data.coloring i.succ) →
                                      IsOneEdgeUncolored (ett.series.data.coloring i.succ) e0 →
                                       ett.series.data.stored i.succ =
                                         (insert choice.color ({ gamma } : Finset (Fin k)) :
                                          Finset (Fin k)) →
                                        ett.series.data.connectingEdges i.succ =
                                          ({ choice.edge } : Finset E) →
                                         ett.series.data.kind i.succ =
                                           some TashkinovExtensionKind.PE →
                                          ett.series.data.chosenVertex i.succ = some choice.vertex →
                                           ett.series.data.outsideVertex i.succ =
                                             some choice.otherEndpoint →
                                            ett.series.data.delta i.succ = some choice.color →
                                             ett.series.data.gamma i.succ = some gamma →
                                              TashkinovClosure (ett.series.data.coloring i.succ)
                                                (ett.series.data.tree i.succ.castSucc)
                                                (ett.series.data.tree i.succ.succ) →
                                               TreeSequenceInitialSegment
                                                 (ett.series.data.tree i.succ.castSucc)
                                                 (ett.series.data.tree i.succ.succ) →
                                                (ett.series.data.tree i.succ.castSucc).length <
                                                  (ett.series.data.tree i.succ.succ).length →
                                                 Fin.last ett.rounds = i.succ →
                                                  Nonempty
                                                   (CorrespondingExtendedTashkinovTree G k e0 ett
                                                    sigma Tstar)

private abbrev helperBranch2237Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T generating),
   MaximumProperty ett →
    ∀ (hpositive : (0 : ℕ) < ett.rounds),
     LowerRoundInductionHypothesis G k e0 ett.rounds →
      ∀ (sigma : PartialEdgeColoring E k),
       IsProperEdgeColoring G sigma →
        IsOneEdgeUncolored sigma e0 →
         StableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
           (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
           (ett.series.data.coloring (Fin.last ett.rounds)) sigma →
          ∀ (Tstar : TreeSequence G e0),
           TreeSequenceInitialSegment (ett.series.data.tree (Fin.last ett.rounds).castSucc) Tstar →
            (ett.series.data.tree (Fin.last ett.rounds).castSucc).length < Tstar.length →
             (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE ∧
                TashkinovAugmentationSequence sigma
                 (ett.series.data.tree (Fin.last ett.rounds).castSucc) Tstar ∨
               (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.SE ∨
                 ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.RE) ∧
                ∃ (f : E) (seed : TreeSequence G e0),
                 ett.series.data.connectingEdges (Fin.last ett.rounds) = ({ f } : Finset E) ∧
                  TreeSequenceAdjoinEdge (ett.series.data.tree (Fin.last ett.rounds).castSucc) f
                    seed ∧
                   TashkinovAugmentationSequence sigma seed Tstar) →
              ∀ (closureTree : TreeSequence G e0),
               TashkinovClosure sigma Tstar closureTree →
                TreeSequenceInitialSegment Tstar closureTree →
                 TreeSequenceInitialSegment (ett.series.data.tree (Fin.last ett.rounds).castSucc)
                   closureTree →
                  let q : Fin ett.rounds :=
                   (⟨ett.rounds - (1 : ℕ), Nat.sub_lt (Nat.zero_lt_of_lt hpositive) (by omega)⟩ :
                    Fin ett.rounds);
                  q.succ = Fin.last ett.rounds →
                   q.castSucc = (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin (ett.rounds + (1 : ℕ))) →
                    StableColoring (ett.series.data.tree q.succ.castSucc)
                      (TashkinovStoredColors ett.series.data q.succ)
                      (ett.series.data.coloring q.succ) sigma →
                     ∀ (i : Fin ett.rounds),
                      IsProperEdgeColoring G (ett.series.data.coloring i.castSucc) →
                       IsOneEdgeUncolored (ett.series.data.coloring i.castSucc) e0 →
                        ColoredVertexSetClosed G (ett.series.data.coloring i.castSucc)
                          (TreeSequenceVertexSet (ett.series.data.tree i.succ.castSucc)) →
                         ¬ColoredVertexSetStronglyClosed G (ett.series.data.coloring i.castSucc)
                            (TreeSequenceVertexSet (ett.series.data.tree i.succ.castSucc)) →
                          ¬Nonempty (RevisitingExtensionCertificate ett.series.data i.castSucc) →
                           ∀
                            (choice :
                             MaximumDefectiveChoice G e0 (ett.series.data.tree i.succ.castSucc)
                              (TashkinovStoredColors ett.series.data i.castSucc)
                              (ett.series.data.coloring i.castSucc)),
                            (∀ (pi : PartialEdgeColoring E k),
                              IsProperEdgeColoring G pi →
                               IsOneEdgeUncolored pi e0 →
                                StableColoring (ett.series.data.tree i.succ.castSucc)
                                  (insert choice.color
                                    (TashkinovStoredColors ett.series.data i.castSucc) :
                                   Finset (Fin k))
                                  choice.selected pi →
                                 Disjoint (MissingColors G pi choice.otherEndpoint)
                                  (TreeMissingColors pi (ett.series.data.tree i.succ.castSucc))) →
                             ett.series.data.coloring i.succ = choice.selected →
                              ett.series.data.stored i.succ = ({ choice.color } : Finset (Fin k)) →
                               ett.series.data.connectingEdges i.succ =
                                 ({ choice.edge } : Finset E) →
                                ett.series.data.kind i.succ = some TashkinovExtensionKind.SE →
                                 ett.series.data.chosenVertex i.succ = some choice.vertex →
                                  ett.series.data.outsideVertex i.succ = some choice.otherEndpoint →
                                   ett.series.data.delta i.succ = some choice.color →
                                    ett.series.data.gamma i.succ = none →
                                     ∀ (adjoined : TreeSequence G e0),
                                      TreeSequenceAdjoinEdge (ett.series.data.tree i.succ.castSucc)
                                        choice.edge adjoined →
                                       TashkinovClosure (ett.series.data.coloring i.succ) adjoined
                                         (ett.series.data.tree i.succ.succ) →
                                        TreeSequenceInitialSegment
                                          (ett.series.data.tree i.succ.castSucc)
                                          (ett.series.data.tree i.succ.succ) →
                                         (ett.series.data.tree i.succ.castSucc).length <
                                           (ett.series.data.tree i.succ.succ).length →
                                          Fin.last ett.rounds = i.succ →
                                           Nonempty
                                            (CorrespondingExtendedTashkinovTree G k e0 ett sigma
                                             Tstar)

private abbrev helperContinuation1015Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E]
   (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
   (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds)
   (sigma : PartialEdgeColoring E k) (hsigmaProper : IsProperEdgeColoring G sigma)
   (hsigmaOne : IsOneEdgeUncolored sigma e0)
   (hsigmaStable :
    StableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
     (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
     (ett.series.data.coloring (Fin.last ett.rounds)) sigma)
   (Tstar : TreeSequence G e0)
   (hTnTstar :
    TreeSequenceInitialSegment (ett.series.data.tree (Fin.last ett.rounds).castSucc) Tstar)
   (hstrict : (ett.series.data.tree (Fin.last ett.rounds).castSucc).length < Tstar.length)
   (closureTree : TreeSequence G e0) (hTstarClosure : TreeSequenceInitialSegment Tstar closureTree),
   let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin ett.rounds);
   ∀ (hqSucc : q.succ = Fin.last ett.rounds)
    (choice :
     MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
      (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
    (currentStored : ett.series.data.stored q.succ = ({ choice.color } : Finset (Fin k)))
    (currentEdges : ett.series.data.connectingEdges q.succ = ({ choice.edge } : Finset E))
    (currentKind : ett.series.data.kind q.succ = some TashkinovExtensionKind.SE)
    (sigmaPrev : PartialEdgeColoring E k) (hroundLarge : (1 : ℕ) < ett.rounds)
    (originalPrefix :
     ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin (ett.rounds + (1 : ℕ)))))
    (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ))
    (hprefixTrees :
     ∀ (i : Fin (originalPrefix.rounds + (2 : ℕ))),
      originalPrefix.series.data.tree i = ett.series.data.tree (Fin.castLE (by omega) i))
    (hprefixData :
     ∀ (i : Fin (originalPrefix.rounds + (1 : ℕ))),
      originalPrefix.series.data.coloring i = ett.series.data.coloring (Fin.castLE (by omega) i) ∧
       originalPrefix.series.data.stored i = ett.series.data.stored (Fin.castLE (by omega) i) ∧
        originalPrefix.series.data.connectingEdges i =
          ett.series.data.connectingEdges (Fin.castLE (by omega) i) ∧
         originalPrefix.series.data.kind i = ett.series.data.kind (Fin.castLE (by omega) i) ∧
          TashkinovStoredColors originalPrefix.series.data i =
           TashkinovStoredColors ett.series.data (Fin.castLE (by omega) i))
    (corr :
     CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
      (ett.series.data.tree (Fin.last ett.rounds).castSucc))
    (horiginalPositive : (0 : ℕ) < originalPrefix.rounds),
    let newStored : Finset (Fin k) := ({ choice.color } : Finset (Fin k));
    let newEdges : Finset E := ({ choice.edge } : Finset E);
    let newKind : Option TashkinovExtensionKind := some TashkinovExtensionKind.SE;
    let newVertex : Option V := some choice.vertex;
    let newOutside : Option V := some choice.otherEndpoint;
    let newDelta : Option (Fin k) := some choice.color;
    let newGamma : Option (Fin k) := none;
    ∀
     (extendedSeries :
      TashkinovSeries G k (originalPrefix.rounds + (1 : ℕ)) e0 corr.replacementInput)
     (hextendedData :
      extendedSeries.data =
       TashkinovSeriesDataAppend corr.replacementSeries.data closureTree sigma newStored newEdges
        newKind newVertex newOutside newDelta newGamma)
     (hroundsEq : originalPrefix.rounds + (1 : ℕ) = ett.rounds),
     let castSeries :
      {a b : ℕ} →
       (h : a = b) →
        (S : TashkinovSeries G k a e0 corr.replacementInput) →
         TashkinovSeries G k b e0 corr.replacementInput :=
      fun {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 corr.replacementInput) ↦ (h ▸ S);
     ∀
      (castSeriesTree :
       ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 corr.replacementInput)
        (i : Fin (b + (2 : ℕ))), (castSeries h S).data.tree i = S.data.tree (Fin.cast (by omega) i))
      (castSeriesColoring :
       ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 corr.replacementInput)
        (i : Fin (b + (1 : ℕ))),
        (castSeries h S).data.coloring i = S.data.coloring (Fin.cast (by omega) i))
      (castSeriesStored :
       ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 corr.replacementInput)
        (i : Fin (b + (1 : ℕ))),
        (castSeries h S).data.stored i = S.data.stored (Fin.cast (by omega) i))
      (castSeriesEdges :
       ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 corr.replacementInput)
        (i : Fin (b + (1 : ℕ))),
        (castSeries h S).data.connectingEdges i = S.data.connectingEdges (Fin.cast (by omega) i))
      (castSeriesKind :
       ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 corr.replacementInput)
        (i : Fin (b + (1 : ℕ))),
        (castSeries h S).data.kind i = S.data.kind (Fin.cast (by omega) i)),
      let finalSeries : TashkinovSeries G k ett.rounds e0 corr.replacementInput :=
       castSeries hroundsEq extendedSeries;
      ∀
       (hfinalPenultimateTree :
        finalSeries.data.tree (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + (2 : ℕ))) =
         ett.series.data.tree (Fin.last ett.rounds).castSucc)
       (hfinalTree : finalSeries.data.tree (Fin.last (ett.rounds + (1 : ℕ))) = closureTree),
       Nonempty (CorrespondingExtendedTashkinovTree G k e0 ett sigma Tstar)

private abbrev helperContinuation1218Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E]
   (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
   (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds)
   (sigma : PartialEdgeColoring E k) (hsigmaProper : IsProperEdgeColoring G sigma)
   (hsigmaOne : IsOneEdgeUncolored sigma e0)
   (hsigmaStable :
    StableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
     (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
     (ett.series.data.coloring (Fin.last ett.rounds)) sigma)
   (Tstar : TreeSequence G e0)
   (hTnTstar :
    TreeSequenceInitialSegment (ett.series.data.tree (Fin.last ett.rounds).castSucc) Tstar)
   (hstrict : (ett.series.data.tree (Fin.last ett.rounds).castSucc).length < Tstar.length)
   (closureTree : TreeSequence G e0) (hTstarClosure : TreeSequenceInitialSegment Tstar closureTree),
   let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin ett.rounds);
   ∀ (hqSucc : q.succ = Fin.last ett.rounds) (gamma : Fin k)
    (choice :
     MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
      (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
    (currentStored :
     ett.series.data.stored q.succ =
      (insert choice.color ({ gamma } : Finset (Fin k)) : Finset (Fin k)))
    (currentEdges : ett.series.data.connectingEdges q.succ = ({ choice.edge } : Finset E))
    (currentKind : ett.series.data.kind q.succ = some TashkinovExtensionKind.PE)
    (sigmaPrev : PartialEdgeColoring E k),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G sigmaPrev gamma choice.color;
    ∀ (u : V) (p : H.Walk (Sum.inl choice.vertex) (Sum.inl u)) (hroundLarge : (1 : ℕ) < ett.rounds)
     (originalPrefix :
      ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
       (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin (ett.rounds + (1 : ℕ)))))
     (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ))
     (hprefixTrees :
      ∀ (i : Fin (originalPrefix.rounds + (2 : ℕ))),
       originalPrefix.series.data.tree i = ett.series.data.tree (Fin.castLE (by omega) i))
     (hprefixData :
      ∀ (i : Fin (originalPrefix.rounds + (1 : ℕ))),
       originalPrefix.series.data.coloring i = ett.series.data.coloring (Fin.castLE (by omega) i) ∧
        originalPrefix.series.data.stored i = ett.series.data.stored (Fin.castLE (by omega) i) ∧
         originalPrefix.series.data.connectingEdges i =
           ett.series.data.connectingEdges (Fin.castLE (by omega) i) ∧
          originalPrefix.series.data.kind i = ett.series.data.kind (Fin.castLE (by omega) i) ∧
           TashkinovStoredColors originalPrefix.series.data i =
            TashkinovStoredColors ett.series.data (Fin.castLE (by omega) i))
     (corr :
      CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
       (ett.series.data.tree (Fin.last ett.rounds).castSucc))
     (horiginalPositive : (0 : ℕ) < originalPrefix.rounds),
     let newStored : Finset (Fin k) :=
      (insert choice.color ({ gamma } : Finset (Fin k)) : Finset (Fin k));
     let newEdges : Finset E := ({ choice.edge } : Finset E);
     let newKind : Option TashkinovExtensionKind := some TashkinovExtensionKind.PE;
     let newVertex : Option V := some choice.vertex;
     let newOutside : Option V := some choice.otherEndpoint;
     let newDelta : Option (Fin k) := some choice.color;
     let newGamma : Option (Fin k) := some gamma;
     ∀
      (extendedSeries :
       TashkinovSeries G k (originalPrefix.rounds + (1 : ℕ)) e0 corr.replacementInput)
      (hextendedData :
       extendedSeries.data =
        TashkinovSeriesDataAppend corr.replacementSeries.data closureTree sigma newStored newEdges
         newKind newVertex newOutside newDelta newGamma)
      (hroundsEq : originalPrefix.rounds + (1 : ℕ) = ett.rounds),
      let castSeries :
       {a b : ℕ} →
        (h : a = b) →
         (S : TashkinovSeries G k a e0 corr.replacementInput) →
          TashkinovSeries G k b e0 corr.replacementInput :=
       fun {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 corr.replacementInput) ↦ (h ▸ S);
      ∀
       (castSeriesTree :
        ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 corr.replacementInput)
         (i : Fin (b + (2 : ℕ))),
         (castSeries h S).data.tree i = S.data.tree (Fin.cast (by omega) i))
       (castSeriesColoring :
        ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 corr.replacementInput)
         (i : Fin (b + (1 : ℕ))),
         (castSeries h S).data.coloring i = S.data.coloring (Fin.cast (by omega) i))
       (castSeriesStored :
        ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 corr.replacementInput)
         (i : Fin (b + (1 : ℕ))),
         (castSeries h S).data.stored i = S.data.stored (Fin.cast (by omega) i))
       (castSeriesEdges :
        ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 corr.replacementInput)
         (i : Fin (b + (1 : ℕ))),
         (castSeries h S).data.connectingEdges i = S.data.connectingEdges (Fin.cast (by omega) i))
       (castSeriesKind :
        ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 corr.replacementInput)
         (i : Fin (b + (1 : ℕ))),
         (castSeries h S).data.kind i = S.data.kind (Fin.cast (by omega) i)),
       let finalSeries : TashkinovSeries G k ett.rounds e0 corr.replacementInput :=
        castSeries hroundsEq extendedSeries;
       ∀
        (hfinalPenultimateTree :
         finalSeries.data.tree (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + (2 : ℕ))) =
          ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (hfinalTree : finalSeries.data.tree (Fin.last (ett.rounds + (1 : ℕ))) = closureTree),
        Nonempty (CorrespondingExtendedTashkinovTree G k e0 ett sigma Tstar)

private abbrev helperContinuation1431Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E]
   (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
   (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds)
   (sigma : PartialEdgeColoring E k) (hsigmaProper : IsProperEdgeColoring G sigma)
   (hsigmaOne : IsOneEdgeUncolored sigma e0)
   (hsigmaStable :
    StableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
     (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
     (ett.series.data.coloring (Fin.last ett.rounds)) sigma)
   (Tstar : TreeSequence G e0)
   (hTnTstar :
    TreeSequenceInitialSegment (ett.series.data.tree (Fin.last ett.rounds).castSucc) Tstar)
   (hstrict : (ett.series.data.tree (Fin.last ett.rounds).castSucc).length < Tstar.length)
   (closureTree : TreeSequence G e0) (hTstarClosure : TreeSequenceInitialSegment Tstar closureTree)
   (hTnClosure :
    TreeSequenceInitialSegment (ett.series.data.tree (Fin.last ett.rounds).castSucc) closureTree),
   let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin ett.rounds);
   ∀ (hqSucc : q.succ = Fin.last ett.rounds) (gamma : Fin k)
    (secondStable : PartialEdgeColoring E k)
    (previousProper : IsProperEdgeColoring G (ett.series.data.coloring q.castSucc))
    (previousOneUncolored : IsOneEdgeUncolored (ett.series.data.coloring q.castSucc) e0)
    (choice :
     MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
      (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
    (currentStored :
     ett.series.data.stored q.succ =
      (insert choice.color ({ gamma } : Finset (Fin k)) : Finset (Fin k)))
    (currentEdges : ett.series.data.connectingEdges q.succ = ({ choice.edge } : Finset E))
    (currentKind : ett.series.data.kind q.succ = some TashkinovExtensionKind.PE)
    (sigmaPrev : PartialEdgeColoring E k) (hsigmaPrevProper : IsProperEdgeColoring G sigmaPrev)
    (hsigmaPrevOne : IsOneEdgeUncolored sigmaPrev e0)
    (hsigmaPrevStableQ :
     StableColoring (ett.series.data.tree q.succ.castSucc)
      (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)
      sigmaPrev)
    (hchoiceDefective :
     DefectiveColor G sigmaPrev (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc))
      choice.color)
    (hchoiceEdgeNew :
     choice.edge ∈
      BoundaryColorEdges G sigmaPrev (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc))
       choice.color)
    (hsigmaPrevSelf :
     StableColoring (ett.series.data.tree q.succ.castSucc)
      (TashkinovStoredColors ett.series.data q.castSucc) sigmaPrev sigmaPrev)
    (hclosedPrev :
     ColoredVertexSetClosed G sigmaPrev
      (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)))
    (hnotStrongPrev :
     ¬ColoredVertexSetStronglyClosed G sigmaPrev
       (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)))
    (hsigmaRecovered :
     sigma = TwoColorComponentSwap G sigmaPrev gamma choice.color (Sum.inl choice.vertex)),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G sigmaPrev gamma choice.color;
    ∀ (a b : V ⊕ E) (u : V) (p : H.Walk (Sum.inl choice.vertex) (Sum.inl u))
     (hnewExit :
      TreeExit (ett.series.data.tree q.succ.castSucc) sigmaPrev gamma choice.color choice.vertex)
     (hroundLarge : (1 : ℕ) < ett.rounds)
     (originalPrefix :
      ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
       (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin (ett.rounds + (1 : ℕ)))))
     (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ))
     (hprefixTrees :
      ∀ (i : Fin (originalPrefix.rounds + (2 : ℕ))),
       originalPrefix.series.data.tree i = ett.series.data.tree (Fin.castLE (by omega) i))
     (hprefixData :
      ∀ (i : Fin (originalPrefix.rounds + (1 : ℕ))),
       originalPrefix.series.data.coloring i = ett.series.data.coloring (Fin.castLE (by omega) i) ∧
        originalPrefix.series.data.stored i = ett.series.data.stored (Fin.castLE (by omega) i) ∧
         originalPrefix.series.data.connectingEdges i =
           ett.series.data.connectingEdges (Fin.castLE (by omega) i) ∧
          originalPrefix.series.data.kind i = ett.series.data.kind (Fin.castLE (by omega) i) ∧
           TashkinovStoredColors originalPrefix.series.data i =
            TashkinovStoredColors ett.series.data (Fin.castLE (by omega) i))
     (corr :
      CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
       (ett.series.data.tree (Fin.last ett.rounds).castSucc))
     (hcorrFinalColor :
      corr.replacementSeries.data.coloring (Fin.last originalPrefix.rounds) = sigmaPrev),
     let replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last originalPrefix.rounds;
     ∀ (horiginalPositive : (0 : ℕ) < originalPrefix.rounds)
      (hreplacementCurrentTree :
       corr.replacementSeries.data.tree replacementLast.succ = ett.series.data.tree q.succ.castSucc)
      (hreplacementStored :
       TashkinovStoredColors corr.replacementSeries.data replacementLast =
        TashkinovStoredColors ett.series.data q.castSucc),
      let replacementChoice :
       MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree replacementLast.succ)
        (TashkinovStoredColors corr.replacementSeries.data replacementLast)
        (corr.replacementSeries.data.coloring replacementLast) :=
       helperReplacementChoice5196 G k e0 input T generating ett hpositive previousProper
        previousOneUncolored choice sigmaPrev hsigmaPrevProper hsigmaPrevOne hsigmaPrevStableQ
        hchoiceDefective hchoiceEdgeNew hsigmaPrevSelf originalPrefix corr hcorrFinalColor
        hreplacementCurrentTree hreplacementStored;
      ∀
       (hpeGammaRuleReplacement :
        ParallelExtensionColor corr.replacementSeries.data replacementLast
         replacementChoice.selected replacementChoice.vertex gamma)
       (hterminalClosure :
        TashkinovClosure sigma (ett.series.data.tree (Fin.last ett.rounds).castSucc) closureTree),
       let newStored : Finset (Fin k) :=
        (insert choice.color ({ gamma } : Finset (Fin k)) : Finset (Fin k));
       let newEdges : Finset E := ({ choice.edge } : Finset E);
       let newKind : Option TashkinovExtensionKind := some TashkinovExtensionKind.PE;
       let newVertex : Option V := some choice.vertex;
       let newOutside : Option V := some choice.otherEndpoint;
       let newDelta : Option (Fin k) := some choice.color;
       let newGamma : Option (Fin k) := some gamma;
       let appendedData : TashkinovSeriesData G k (originalPrefix.rounds + (1 : ℕ)) e0 :=
        TashkinovSeriesDataAppend corr.replacementSeries.data closureTree sigma newStored newEdges
         newKind newVertex newOutside newDelta newGamma;
       ∀
        (happendedTree :
         appendedData.tree replacementLast.succ.castSucc =
          corr.replacementSeries.data.tree replacementLast.succ)
        (happendedStored :
         TashkinovStoredColors appendedData replacementLast.castSucc =
          TashkinovStoredColors corr.replacementSeries.data replacementLast)
        (happendedColor :
         appendedData.coloring replacementLast.castSucc =
          corr.replacementSeries.data.coloring replacementLast),
        let appendedChoice :
         MaximumDefectiveChoice G e0 (appendedData.tree replacementLast.succ.castSucc)
          (TashkinovStoredColors appendedData replacementLast.castSucc)
          (appendedData.coloring replacementLast.castSucc) :=
         {
          selected := replacementChoice.selected,
          selectedProper := replacementChoice.selectedProper,
          selectedOneUncolored := replacementChoice.selectedOneUncolored,
          selectedStable :=
           ((Eq.symm
             (id
              (congrArg
               (fun (_a : TreeSequence G e0) ↦
                StableColoring _a (TashkinovStoredColors appendedData replacementLast.castSucc)
                 (appendedData.coloring replacementLast.castSucc) replacementChoice.selected)
               happendedTree))) ▸
            ((Eq.symm
              (id
               (congrArg
                (fun (_a : Finset (Fin k)) ↦
                 StableColoring (corr.replacementSeries.data.tree replacementLast.succ) _a
                  (appendedData.coloring replacementLast.castSucc) replacementChoice.selected)
                happendedStored))) ▸
             ((Eq.symm
               (id
                (congrArg
                 (fun (_a : PartialEdgeColoring E k) ↦
                  StableColoring (corr.replacementSeries.data.tree replacementLast.succ)
                   (TashkinovStoredColors corr.replacementSeries.data replacementLast) _a
                   replacementChoice.selected)
                 happendedColor))) ▸
              replacementChoice.selectedStable))),
          vertex := replacementChoice.vertex,
          vertexDefective :=
           ((Eq.symm
             (id
              (congrArg
               (fun (_a : TreeSequence G e0) ↦
                DefectiveVertex G replacementChoice.selected (TreeSequenceVertexSet _a)
                 replacementChoice.vertex)
               happendedTree))) ▸
            replacementChoice.vertexDefective),
          maximal :=
           fun (pi : PartialEdgeColoring E k) (w : V) (hpiProper : IsProperEdgeColoring G pi)
            (hpiOne : IsOneEdgeUncolored pi e0)
            (hpiStable :
             StableColoring (appendedData.tree replacementLast.succ.castSucc)
              (TashkinovStoredColors appendedData replacementLast.castSucc)
              (appendedData.coloring replacementLast.castSucc) pi)
            (hw :
             DefectiveVertex G pi
              (TreeSequenceVertexSet (appendedData.tree replacementLast.succ.castSucc)) w) ↦
           ((Eq.symm
             (id
              (congrArg
               (fun (_a : TreeSequence G e0) ↦
                w = replacementChoice.vertex ∨ TreeVertexOrder _a w replacementChoice.vertex)
               happendedTree))) ▸
            replacementChoice.maximal pi w hpiProper hpiOne
             (congrArg
               (fun (_a : PartialEdgeColoring E k) ↦
                StableColoring (corr.replacementSeries.data.tree replacementLast.succ)
                 (TashkinovStoredColors corr.replacementSeries.data replacementLast) _a pi)
               happendedColor ▸
              (congrArg
                (fun (_a : Finset (Fin k)) ↦
                 StableColoring (corr.replacementSeries.data.tree replacementLast.succ) _a
                  (appendedData.coloring replacementLast.castSucc) pi)
                happendedStored ▸
               (congrArg
                 (fun (_a : TreeSequence G e0) ↦
                  StableColoring _a (TashkinovStoredColors appendedData replacementLast.castSucc)
                   (appendedData.coloring replacementLast.castSucc) pi)
                 happendedTree ▸
                hpiStable)))
             (congrArg
               (fun (_a : TreeSequence G e0) ↦ DefectiveVertex G pi (TreeSequenceVertexSet _a) w)
               happendedTree ▸
              hw)),
          edge := replacementChoice.edge,
          edgeDefective :=
           ((Eq.symm
             (id
              (congrArg
               (fun (_a : TreeSequence G e0) ↦
                DefectiveEdge G replacementChoice.selected (TreeSequenceVertexSet _a)
                 replacementChoice.edge)
               happendedTree))) ▸
            replacementChoice.edgeDefective),
          edgeIncident := replacementChoice.edgeIncident,
          otherEndpoint := replacementChoice.otherEndpoint,
          otherOutside :=
           ((Eq.symm
             (id
              (congrArg
               (fun (_a : TreeSequence G e0) ↦
                replacementChoice.otherEndpoint ∉ TreeSequenceVertexSet _a)
               happendedTree))) ▸
            replacementChoice.otherOutside),
          edgeEnds := replacementChoice.edgeEnds, color := replacementChoice.color,
          edgeColor := replacementChoice.edgeColor :
          MaximumDefectiveChoice G e0 (appendedData.tree replacementLast.succ.castSucc)
           (TashkinovStoredColors appendedData replacementLast.castSucc)
           (appendedData.coloring replacementLast.castSucc) };
        ∀
         (hnoRevisitingAppended :
          ¬Nonempty (RevisitingExtensionCertificate appendedData replacementLast.castSucc))
         (hpeAlternativeAppended :
          ∃ (rho : PartialEdgeColoring E k),
           IsProperEdgeColoring G rho ∧
            IsOneEdgeUncolored rho e0 ∧
             StableColoring (appendedData.tree replacementLast.succ.castSucc)
               (insert appendedChoice.color
                 (TashkinovStoredColors appendedData replacementLast.castSucc) :
                Finset (Fin k))
               appendedChoice.selected rho ∧
              ¬Disjoint (MissingColors G rho appendedChoice.otherEndpoint)
                (TreeMissingColors rho (appendedData.tree replacementLast.succ.castSucc))),
         Nonempty (CorrespondingExtendedTashkinovTree G k e0 ett sigma Tstar)

private abbrev helperContinuation1943Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T generating) (hMP : MaximumProperty ett)
   (hpositive : (0 : ℕ) < ett.rounds) (hlower : LowerRoundInductionHypothesis G k e0 ett.rounds)
   (sigma : PartialEdgeColoring E k) (hsigmaProper : IsProperEdgeColoring G sigma)
   (hsigmaOne : IsOneEdgeUncolored sigma e0)
   (hsigmaStable :
    StableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
     (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
     (ett.series.data.coloring (Fin.last ett.rounds)) sigma)
   (Tstar : TreeSequence G e0)
   (hTnTstar :
    TreeSequenceInitialSegment (ett.series.data.tree (Fin.last ett.rounds).castSucc) Tstar)
   (hstrict : (ett.series.data.tree (Fin.last ett.rounds).castSucc).length < Tstar.length)
   (heligible :
    ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE ∧
      TashkinovAugmentationSequence sigma (ett.series.data.tree (Fin.last ett.rounds).castSucc)
       Tstar ∨
     (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.SE ∨
       ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.RE) ∧
      ∃ (f : E) (seed : TreeSequence G e0),
       ett.series.data.connectingEdges (Fin.last ett.rounds) = ({ f } : Finset E) ∧
        TreeSequenceAdjoinEdge (ett.series.data.tree (Fin.last ett.rounds).castSucc) f seed ∧
         TashkinovAugmentationSequence sigma seed Tstar)
   (closureTree : TreeSequence G e0) (hclosure : TashkinovClosure sigma Tstar closureTree)
   (hTstarClosure : TreeSequenceInitialSegment Tstar closureTree)
   (hTnClosure :
    TreeSequenceInitialSegment (ett.series.data.tree (Fin.last ett.rounds).castSucc) closureTree),
   let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin ett.rounds);
   ∀ (hqSucc : q.succ = Fin.last ett.rounds) (gamma : Fin k)
    (secondStable : PartialEdgeColoring E k)
    (previousProper : IsProperEdgeColoring G (ett.series.data.coloring q.castSucc))
    (previousOneUncolored : IsOneEdgeUncolored (ett.series.data.coloring q.castSucc) e0)
    (noRevisiting : ¬Nonempty (RevisitingExtensionCertificate ett.series.data q.castSucc))
    (choice :
     MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
      (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
    (gammaRule :
     ParallelExtensionColor ett.series.data q.castSucc choice.selected choice.vertex gamma)
    (currentStored :
     ett.series.data.stored q.succ =
      (insert choice.color ({ gamma } : Finset (Fin k)) : Finset (Fin k)))
    (currentEdges : ett.series.data.connectingEdges q.succ = ({ choice.edge } : Finset E))
    (currentKind hpeKind : ett.series.data.kind q.succ = some TashkinovExtensionKind.PE)
    (sigmaPrev : PartialEdgeColoring E k) (hsigmaPrevProper : IsProperEdgeColoring G sigmaPrev)
    (hsigmaPrevOne : IsOneEdgeUncolored sigmaPrev e0)
    (hprefixCases :
     (ett.rounds = (1 : ℕ) ∧
       ∃ (prefixInput : PartialEdgeColoring E k) (zeroPrefix :
        TashkinovSeries G k (0 : ℕ) e0 prefixInput),
        zeroPrefix.data.tree (Fin.last (1 : ℕ)) =
          ett.series.data.tree (Fin.last ett.rounds).castSucc ∧
         zeroPrefix.data.coloring (Fin.last (0 : ℕ)) = sigmaPrev) ∨
      (1 : ℕ) < ett.rounds ∧
       ∃ (originalPrefix :
        ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
         (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin (ett.rounds + (1 : ℕ)))))
        (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ)),
        MaximumProperty originalPrefix ∧
         (∀ (i : Fin (originalPrefix.rounds + (2 : ℕ))),
           originalPrefix.series.data.tree i = ett.series.data.tree (Fin.castLE (by omega) i)) ∧
          (∀ (i : Fin (originalPrefix.rounds + (1 : ℕ))),
            originalPrefix.series.data.coloring i =
              ett.series.data.coloring (Fin.castLE (by omega) i) ∧
             originalPrefix.series.data.stored i =
               ett.series.data.stored (Fin.castLE (by omega) i) ∧
              originalPrefix.series.data.connectingEdges i =
                ett.series.data.connectingEdges (Fin.castLE (by omega) i) ∧
               originalPrefix.series.data.kind i = ett.series.data.kind (Fin.castLE (by omega) i) ∧
                TashkinovStoredColors originalPrefix.series.data i =
                 TashkinovStoredColors ett.series.data (Fin.castLE (by omega) i)) ∧
           ∃ (corr :
            CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
             (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
            corr.replacementSeries.data.tree (Fin.last (originalPrefix.rounds + (1 : ℕ))) =
              ett.series.data.tree (Fin.last ett.rounds).castSucc ∧
             corr.replacementSeries.data.coloring (Fin.last originalPrefix.rounds) = sigmaPrev ∧
              MaximumProperty corr.replacementETT)
    (hsigmaPrevStableQ :
     StableColoring (ett.series.data.tree q.succ.castSucc)
      (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)
      sigmaPrev)
    (hchoiceDefective :
     DefectiveColor G sigmaPrev (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc))
      choice.color)
    (hchoiceEdgeNew :
     choice.edge ∈
      BoundaryColorEdges G sigmaPrev (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc))
       choice.color)
    (hsigmaPrevSelf :
     StableColoring (ett.series.data.tree q.succ.castSucc)
      (TashkinovStoredColors ett.series.data q.castSucc) sigmaPrev sigmaPrev),
    let newChoice :
     MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
      (TashkinovStoredColors ett.series.data q.castSucc) sigmaPrev :=
     helperNewChoice4049 G k e0 input T generating ett hpositive previousProper previousOneUncolored
      choice sigmaPrev hsigmaPrevProper hsigmaPrevOne hsigmaPrevStableQ hchoiceDefective
      hchoiceEdgeNew hsigmaPrevSelf;
    ∀
     (hclosedPrev :
      ColoredVertexSetClosed G sigmaPrev
       (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)))
     (hnotStrongPrev :
      ¬ColoredVertexSetStronglyClosed G sigmaPrev
        (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)))
     (hnewAlternativeFails :
      ∃ (rho : PartialEdgeColoring E k),
       IsProperEdgeColoring G rho ∧
        IsOneEdgeUncolored rho e0 ∧
         StableColoring (ett.series.data.tree q.succ.castSucc)
           (insert newChoice.color (TashkinovStoredColors ett.series.data q.castSucc) :
            Finset (Fin k))
           newChoice.selected rho ∧
          ¬Disjoint (MissingColors G rho newChoice.otherEndpoint)
            (TreeMissingColors rho (ett.series.data.tree q.succ.castSucc)))
     (hgammaPrevMissing : gamma ∈ MissingColors G sigmaPrev choice.vertex)
     (hsigmaRecovered :
      sigma = TwoColorComponentSwap G sigmaPrev gamma choice.color (Sum.inl choice.vertex)),
     let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G sigmaPrev gamma choice.color;
     ∀
      (hedgeComponent :
       Sum.inr choice.edge ∈
        TwoColorComponent G sigmaPrev gamma choice.color (Sum.inl choice.vertex))
      (a b : V ⊕ E) (p_1 : (TwoColorIncidenceGraph G sigmaPrev gamma choice.color).Walk a b)
      (hp_1 : p_1.IsPath) (u : V) (p : H.Walk (Sum.inl choice.vertex) (Sum.inl u)) (hp : p.IsPath)
      (hnewExit :
       TreeExit (ett.series.data.tree q.succ.castSucc) sigmaPrev gamma choice.color choice.vertex),
      Nonempty (CorrespondingExtendedTashkinovTree G k e0 ett sigma Tstar)

private abbrev helperContinuation2339Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T generating) (hMP : MaximumProperty ett)
   (hpositive : (0 : ℕ) < ett.rounds) (hlower : LowerRoundInductionHypothesis G k e0 ett.rounds)
   (sigma : PartialEdgeColoring E k) (hsigmaProper : IsProperEdgeColoring G sigma)
   (hsigmaOne : IsOneEdgeUncolored sigma e0)
   (hsigmaStable :
    StableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
     (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
     (ett.series.data.coloring (Fin.last ett.rounds)) sigma)
   (Tstar : TreeSequence G e0)
   (hTnTstar :
    TreeSequenceInitialSegment (ett.series.data.tree (Fin.last ett.rounds).castSucc) Tstar)
   (hstrict : (ett.series.data.tree (Fin.last ett.rounds).castSucc).length < Tstar.length)
   (heligible :
    ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE ∧
      TashkinovAugmentationSequence sigma (ett.series.data.tree (Fin.last ett.rounds).castSucc)
       Tstar ∨
     (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.SE ∨
       ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.RE) ∧
      ∃ (f : E) (seed : TreeSequence G e0),
       ett.series.data.connectingEdges (Fin.last ett.rounds) = ({ f } : Finset E) ∧
        TreeSequenceAdjoinEdge (ett.series.data.tree (Fin.last ett.rounds).castSucc) f seed ∧
         TashkinovAugmentationSequence sigma seed Tstar)
   (closureTree : TreeSequence G e0) (hclosure : TashkinovClosure sigma Tstar closureTree)
   (hTstarClosure : TreeSequenceInitialSegment Tstar closureTree)
   (hTnClosure :
    TreeSequenceInitialSegment (ett.series.data.tree (Fin.last ett.rounds).castSucc) closureTree),
   let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin ett.rounds);
   ∀ (hqSucc : q.succ = Fin.last ett.rounds)
    (hsigmaStableQ :
     StableColoring (ett.series.data.tree q.succ.castSucc)
      (TashkinovStoredColors ett.series.data q.succ) (ett.series.data.coloring q.succ) sigma)
    (gamma : Fin k) (secondStable : PartialEdgeColoring E k)
    (secondStableProper : IsProperEdgeColoring G secondStable)
    (previousProper : IsProperEdgeColoring G (ett.series.data.coloring q.castSucc))
    (previousOneUncolored : IsOneEdgeUncolored (ett.series.data.coloring q.castSucc) e0)
    (previousClosed :
     ColoredVertexSetClosed G (ett.series.data.coloring q.castSucc)
      (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)))
    (noRevisiting : ¬Nonempty (RevisitingExtensionCertificate ett.series.data q.castSucc))
    (choice :
     MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
      (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
    (seriesAlternativeFails :
     ∃ (rho : PartialEdgeColoring E k),
      IsProperEdgeColoring G rho ∧
       IsOneEdgeUncolored rho e0 ∧
        StableColoring (ett.series.data.tree q.succ.castSucc)
          (insert choice.color (TashkinovStoredColors ett.series.data q.castSucc) : Finset (Fin k))
          choice.selected rho ∧
         ¬Disjoint (MissingColors G rho choice.otherEndpoint)
           (TreeMissingColors rho (ett.series.data.tree q.succ.castSucc)))
    (gammaRule :
     ParallelExtensionColor ett.series.data q.castSucc choice.selected choice.vertex gamma)
    (secondStableRelation :
     StableColoring (ett.series.data.tree q.succ.castSucc)
      (insert choice.color (TashkinovStoredColors ett.series.data q.castSucc) : Finset (Fin k))
      choice.selected secondStable)
    (currentColoring :
     ett.series.data.coloring q.succ =
      TwoColorComponentSwap G secondStable gamma choice.color (Sum.inl choice.vertex))
    (currentStored :
     ett.series.data.stored q.succ =
      (insert choice.color ({ gamma } : Finset (Fin k)) : Finset (Fin k)))
    (currentEdges : ett.series.data.connectingEdges q.succ = ({ choice.edge } : Finset E))
    (currentKind hpeKind : ett.series.data.kind q.succ = some TashkinovExtensionKind.PE)
    (sigmaPrev : PartialEdgeColoring E k) (hsigmaPrevProper : IsProperEdgeColoring G sigmaPrev)
    (hsigmaPrevOne : IsOneEdgeUncolored sigmaPrev e0)
    (hprefixCases :
     (ett.rounds = (1 : ℕ) ∧
       ∃ (prefixInput : PartialEdgeColoring E k) (zeroPrefix :
        TashkinovSeries G k (0 : ℕ) e0 prefixInput),
        zeroPrefix.data.tree (Fin.last (1 : ℕ)) =
          ett.series.data.tree (Fin.last ett.rounds).castSucc ∧
         zeroPrefix.data.coloring (Fin.last (0 : ℕ)) = sigmaPrev) ∨
      (1 : ℕ) < ett.rounds ∧
       ∃ (originalPrefix :
        ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
         (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin (ett.rounds + (1 : ℕ)))))
        (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ)),
        MaximumProperty originalPrefix ∧
         (∀ (i : Fin (originalPrefix.rounds + (2 : ℕ))),
           originalPrefix.series.data.tree i = ett.series.data.tree (Fin.castLE (by omega) i)) ∧
          (∀ (i : Fin (originalPrefix.rounds + (1 : ℕ))),
            originalPrefix.series.data.coloring i =
              ett.series.data.coloring (Fin.castLE (by omega) i) ∧
             originalPrefix.series.data.stored i =
               ett.series.data.stored (Fin.castLE (by omega) i) ∧
              originalPrefix.series.data.connectingEdges i =
                ett.series.data.connectingEdges (Fin.castLE (by omega) i) ∧
               originalPrefix.series.data.kind i = ett.series.data.kind (Fin.castLE (by omega) i) ∧
                TashkinovStoredColors originalPrefix.series.data i =
                 TashkinovStoredColors ett.series.data (Fin.castLE (by omega) i)) ∧
           ∃ (corr :
            CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
             (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
            corr.replacementSeries.data.tree (Fin.last (originalPrefix.rounds + (1 : ℕ))) =
              ett.series.data.tree (Fin.last ett.rounds).castSucc ∧
             corr.replacementSeries.data.coloring (Fin.last originalPrefix.rounds) = sigmaPrev ∧
              MaximumProperty corr.replacementETT)
    (hsigmaPrevStableQ :
     StableColoring (ett.series.data.tree q.succ.castSucc)
      (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)
      sigmaPrev)
    (hchoiceVertex : choice.vertex ∈ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc))
    (hcomponent :
     ∀ w ∈ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc),
      Sum.inl w ∈ TwoColorComponent G sigma gamma choice.color (Sum.inl choice.vertex) ↔
       w = choice.vertex)
    (hsigmaPrevFormula :
     sigmaPrev = TwoColorComponentSwap G sigma gamma choice.color (Sum.inl choice.vertex))
    (hsigmaPrevEnlarged :
     StableColoring (ett.series.data.tree q.succ.castSucc)
      (insert choice.color (TashkinovStoredColors ett.series.data q.castSucc) : Finset (Fin k))
      choice.selected sigmaPrev)
    (hchoiceDefective :
     DefectiveColor G sigmaPrev (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc))
      choice.color)
    (hchoiceEdgeNew :
     choice.edge ∈
      BoundaryColorEdges G sigmaPrev (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc))
       choice.color),
    Nonempty (CorrespondingExtendedTashkinovTree G k e0 ett sigma Tstar)

private abbrev helperContinuation2265Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T generating) (hMP : MaximumProperty ett)
   (hpositive : (0 : ℕ) < ett.rounds) (hlower : LowerRoundInductionHypothesis G k e0 ett.rounds)
   (sigma : PartialEdgeColoring E k) (hsigmaProper : IsProperEdgeColoring G sigma)
   (hsigmaOne : IsOneEdgeUncolored sigma e0)
   (hsigmaStable :
    StableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
     (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
     (ett.series.data.coloring (Fin.last ett.rounds)) sigma)
   (Tstar : TreeSequence G e0)
   (hTnTstar :
    TreeSequenceInitialSegment (ett.series.data.tree (Fin.last ett.rounds).castSucc) Tstar)
   (hstrict : (ett.series.data.tree (Fin.last ett.rounds).castSucc).length < Tstar.length)
   (heligible :
    ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE ∧
      TashkinovAugmentationSequence sigma (ett.series.data.tree (Fin.last ett.rounds).castSucc)
       Tstar ∨
     (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.SE ∨
       ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.RE) ∧
      ∃ (f : E) (seed : TreeSequence G e0),
       ett.series.data.connectingEdges (Fin.last ett.rounds) = ({ f } : Finset E) ∧
        TreeSequenceAdjoinEdge (ett.series.data.tree (Fin.last ett.rounds).castSucc) f seed ∧
         TashkinovAugmentationSequence sigma seed Tstar)
   (closureTree : TreeSequence G e0) (hclosure : TashkinovClosure sigma Tstar closureTree)
   (hTstarClosure : TreeSequenceInitialSegment Tstar closureTree)
   (hTnClosure :
    TreeSequenceInitialSegment (ett.series.data.tree (Fin.last ett.rounds).castSucc) closureTree),
   let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin ett.rounds);
   ∀ (hqSucc : q.succ = Fin.last ett.rounds) (adjoined : TreeSequence G e0)
    (previousProper : IsProperEdgeColoring G (ett.series.data.coloring q.castSucc))
    (previousOneUncolored : IsOneEdgeUncolored (ett.series.data.coloring q.castSucc) e0)
    (noRevisiting : ¬Nonempty (RevisitingExtensionCertificate ett.series.data q.castSucc))
    (choice :
     MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
      (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
    (currentStored : ett.series.data.stored q.succ = ({ choice.color } : Finset (Fin k)))
    (currentEdges : ett.series.data.connectingEdges q.succ = ({ choice.edge } : Finset E))
    (currentKind hseKind : ett.series.data.kind q.succ = some TashkinovExtensionKind.SE)
    (sigmaPrev : PartialEdgeColoring E k) (hsigmaPrevProper : IsProperEdgeColoring G sigmaPrev)
    (hsigmaPrevOne : IsOneEdgeUncolored sigmaPrev e0)
    (hprefixCases :
     (ett.rounds = (1 : ℕ) ∧
       ∃ (prefixInput : PartialEdgeColoring E k) (zeroPrefix :
        TashkinovSeries G k (0 : ℕ) e0 prefixInput),
        zeroPrefix.data.tree (Fin.last (1 : ℕ)) =
          ett.series.data.tree (Fin.last ett.rounds).castSucc ∧
         zeroPrefix.data.coloring (Fin.last (0 : ℕ)) = sigmaPrev) ∨
      (1 : ℕ) < ett.rounds ∧
       ∃ (originalPrefix :
        ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
         (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin (ett.rounds + (1 : ℕ)))))
        (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ)),
        MaximumProperty originalPrefix ∧
         (∀ (i : Fin (originalPrefix.rounds + (2 : ℕ))),
           originalPrefix.series.data.tree i = ett.series.data.tree (Fin.castLE (by omega) i)) ∧
          (∀ (i : Fin (originalPrefix.rounds + (1 : ℕ))),
            originalPrefix.series.data.coloring i =
              ett.series.data.coloring (Fin.castLE (by omega) i) ∧
             originalPrefix.series.data.stored i =
               ett.series.data.stored (Fin.castLE (by omega) i) ∧
              originalPrefix.series.data.connectingEdges i =
                ett.series.data.connectingEdges (Fin.castLE (by omega) i) ∧
               originalPrefix.series.data.kind i = ett.series.data.kind (Fin.castLE (by omega) i) ∧
                TashkinovStoredColors originalPrefix.series.data i =
                 TashkinovStoredColors ett.series.data (Fin.castLE (by omega) i)) ∧
           ∃ (corr :
            CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
             (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
            corr.replacementSeries.data.tree (Fin.last (originalPrefix.rounds + (1 : ℕ))) =
              ett.series.data.tree (Fin.last ett.rounds).castSucc ∧
             corr.replacementSeries.data.coloring (Fin.last originalPrefix.rounds) = sigmaPrev ∧
              MaximumProperty corr.replacementETT)
    (hsigmaPrevStableQ :
     StableColoring (ett.series.data.tree q.succ.castSucc)
      (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)
      sigmaPrev)
    (hsigmaPrevSigma : sigmaPrev = sigma)
    (hchoiceDefective :
     DefectiveColor G sigmaPrev (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc))
      choice.color)
    (hchoiceEdgeNew :
     choice.edge ∈
      BoundaryColorEdges G sigmaPrev (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc))
       choice.color)
    (hsigmaPrevSelf :
     StableColoring (ett.series.data.tree q.succ.castSucc)
      (TashkinovStoredColors ett.series.data q.castSucc) sigmaPrev sigmaPrev),
    let newChoice :
     MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
      (TashkinovStoredColors ett.series.data q.castSucc) sigmaPrev :=
     helperNewChoice2409 G k e0 input T generating ett hpositive previousProper previousOneUncolored
      choice sigmaPrev hsigmaPrevProper hsigmaPrevOne hsigmaPrevStableQ hchoiceDefective
      hchoiceEdgeNew hsigmaPrevSelf;
    ∀
     (hclosedPrev :
      ColoredVertexSetClosed G sigmaPrev
       (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)))
     (hnotStrongPrev :
      ¬ColoredVertexSetStronglyClosed G sigmaPrev
        (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)))
     (hnewAlternative :
      ∀ (pi : PartialEdgeColoring E k),
       IsProperEdgeColoring G pi →
        IsOneEdgeUncolored pi e0 →
         StableColoring (ett.series.data.tree q.succ.castSucc)
           (insert newChoice.color (TashkinovStoredColors ett.series.data q.castSucc) :
            Finset (Fin k))
           newChoice.selected pi →
          Disjoint (MissingColors G pi newChoice.otherEndpoint)
           (TreeMissingColors pi (ett.series.data.tree q.succ.castSucc))),
     Nonempty (CorrespondingExtendedTashkinovTree G k e0 ett sigma Tstar)

private theorem helper_continuation_1015.{u_1, u_2} :
    helperContinuation1015Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma hsigmaProper hsigmaOne
      hsigmaStable Tstar hTnTstar hstrict closureTree hTstarClosure q hqSucc choice currentStored
      currentEdges currentKind sigmaPrev hroundLarge originalPrefix hr hprefixTrees hprefixData
      corr horiginalPositive newStored newEdges newKind newVertex newOutside newDelta newGamma
      extendedSeries hextendedData hroundsEq castSeries castSeriesTree castSeriesColoring
      castSeriesStored castSeriesEdges castSeriesKind finalSeries hfinalPenultimateTree hfinalTree
  let rawFinalColor : Fin (originalPrefix.rounds + 2) :=
    Fin.cast
      (congrArg (fun m : ℕ => m + 1) hroundsEq.symm)
      (Fin.last ett.rounds)
  have hrawFinalColor : rawFinalColor =
      Fin.last (originalPrefix.rounds + 1) := by
    apply Fin.ext
    simp [rawFinalColor]
  have hfinalColor : finalSeries.data.coloring
        (Fin.last ett.rounds) = sigma := by
    exact @helper_hfinalColor_4432 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@Tstar) (@closureTree)
        (@choice) (@sigmaPrev) (@originalPrefix) (@corr) (@extendedSeries) (@hextendedData)
        (@hroundsEq) (@castSeriesColoring) (@hrawFinalColor)
  let rawDataIndex (i : Fin (ett.rounds + 1)) :
      Fin (originalPrefix.rounds + 2) :=
    Fin.cast
      (congrArg (fun m : ℕ => m + 1) hroundsEq.symm) i
  have hseriesDataAgree : ∀ i : Fin (ett.rounds + 1),
      finalSeries.data.stored i = ett.series.data.stored i ∧
      finalSeries.data.connectingEdges i =
        ett.series.data.connectingEdges i ∧
      finalSeries.data.kind i = ett.series.data.kind i := by
    intro i
    by_cases hi : i.val < ett.rounds
    · exact @helper_branch_4454 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@Tstar) (@closureTree)
        (@choice) (@sigmaPrev) (@hroundLarge) (@originalPrefix) (@hr) (@hprefixData) (@corr)
        (@horiginalPositive) (@extendedSeries) (@hextendedData) (@hroundsEq) (@castSeriesStored)
        (@castSeriesEdges) (@castSeriesKind) (@i) (@hi)
    · exact @helper_branch_4512 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@Tstar) (@closureTree)
        (@hqSucc) (@choice) (@currentStored) (@currentEdges) (@currentKind) (@sigmaPrev)
        (@hroundLarge) (@originalPrefix) (@hr) (@corr) (@horiginalPositive) (@extendedSeries)
        (@hextendedData) (@hroundsEq) (@castSeriesStored) (@castSeriesEdges) (@castSeriesKind)
        (@i) (@hi)
  let rawTreeIndex (i : Fin (ett.rounds + 2)) :
      Fin (originalPrefix.rounds + 3) :=
    Fin.cast
      (congrArg (fun m : ℕ => m + 2) hroundsEq.symm) i
  have hseriesTreeAgree : ∀ i : Fin ett.rounds,
      finalSeries.data.tree i.succ.castSucc =
        ett.series.data.tree i.succ.castSucc := by
    exact @helper_hseriesTreeAgree_4578 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@Tstar)
        (@closureTree) (@choice) (@sigmaPrev) (@hroundLarge) (@originalPrefix) (@hr)
        (@hprefixTrees) (@corr) (@horiginalPositive) (@extendedSeries) (@hextendedData)
        (@hroundsEq) (@castSeriesTree) (@hfinalPenultimateTree)
  have hseriesColorProperties : ∀ i : Fin (ett.rounds + 1),
      IsProperEdgeColoring G (finalSeries.data.coloring i) ∧
        IsOneEdgeUncolored (finalSeries.data.coloring i) e0 := by
    exact finalSeries.coloringProperties
  have hseriesStable : ∀ i : Fin ett.rounds,
      StableColoring
        (ett.series.data.tree i.succ.castSucc)
        (TashkinovStoredColors ett.series.data i.succ)
        (ett.series.data.coloring i.succ)
        (finalSeries.data.coloring i.succ) := by
    exact TashkinovSeriesData.stabilityOfPrefix
      ett.series.data finalSeries.data.coloring originalPrefix.series.data
      corr.replacementSeries.data.coloring hroundsEq hprefixTrees
      (fun j => (hprefixData j).2.2.2.2) (fun j => (hprefixData j).1)
      (TashkinovSeriesData.prefixColoringOfCast hroundsEq
        corr.replacementSeries.data.coloring sigma finalSeries.data.coloring (by
          intro j
          calc
            finalSeries.data.coloring j = extendedSeries.data.coloring
                (Fin.cast (congrArg (fun n => n + 1) hroundsEq.symm) j) :=
              castSeriesColoring hroundsEq extendedSeries j
            _ = _ := by rw [hextendedData]; rfl))
      corr.replacementStable (by rw [hfinalColor]; exact hsigmaStable)
  let replacementETT : ExtendedTashkinovTree G k e0
      corr.replacementInput Tstar sigma := by
    exact {
      rounds := ett.rounds
      roundsPositive := ett.roundsPositive
      series := finalSeries
      abovePenultimate := by
        rw [hfinalPenultimateTree]
        exact hTnTstar
      strictAbovePenultimate := by
        rw [hfinalPenultimateTree]
        exact hstrict
      belowFinal := by
        rw [hfinalTree]
        exact hTstarClosure
      generatingColoring := hfinalColor.symm
  }
  refine ⟨{
    replacementInput := corr.replacementInput
    replacementSeries := finalSeries
    replacementETT := replacementETT
    rungAgreement := rfl
    seriesPresentation := by dsimp [replacementETT]; rfl
    finalGeneratingColoring := hfinalColor.symm
    ladderTreesAgree := hseriesTreeAgree
    storedColorsAgree := fun i => (hseriesDataAgree i).1
    connectingEdgesAgree := fun i => (hseriesDataAgree i).2.1
    extensionKindsAgree := fun i => (hseriesDataAgree i).2.2
    replacementProper := fun i =>
      (hseriesColorProperties i).1
    replacementOneUncolored := fun i =>
      (hseriesColorProperties i).2
    replacementStable := hseriesStable
  }⟩

private theorem helper_caseContinuation_422.{u_1, u_2} :
    helperCaseContinuation422Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma hsigmaProper hsigmaOne
      hsigmaStable Tstar hTnTstar hstrict closureTree hTstarClosure q hqSucc choice currentStored
      currentEdges currentKind sigmaPrev hroundLarge originalPrefix hr hprefixTrees hprefixData
      corr replacementLast horiginalPositive hreplacementCurrentTree newStored newEdges newKind
      newVertex newOutside newDelta newGamma appendedData lastStep
  obtain ⟨extendedSeries, hextendedData⟩ :=
    TashkinovSeriesAppend G k originalPrefix.rounds e0
      corr.replacementInput corr.replacementSeries closureTree sigma
      newStored newEdges newKind newVertex newOutside newDelta newGamma
      lastStep
  have hroundsEq : originalPrefix.rounds + 1 = ett.rounds := by
    rw [hr]
    omega
  let castSeries {a b : ℕ} (h : a = b)
      (S : TashkinovSeries G k a e0 corr.replacementInput) :
      TashkinovSeries G k b e0 corr.replacementInput := by
    subst b
    exact S
  have castSeriesTree : ∀ {a b : ℕ} (h : a = b)
      (S : TashkinovSeries G k a e0 corr.replacementInput)
      (i : Fin (b + 2)),
      (castSeries h S).data.tree i =
        S.data.tree
          (Fin.cast (congrArg (fun m : ℕ => m + 2) h.symm) i) := by
    intro a b h S i
    subst b
    rfl
  have castSeriesColoring : ∀ {a b : ℕ} (h : a = b)
      (S : TashkinovSeries G k a e0 corr.replacementInput)
      (i : Fin (b + 1)),
      (castSeries h S).data.coloring i =
        S.data.coloring
          (Fin.cast (congrArg (fun m : ℕ => m + 1) h.symm) i) := by
    intro a b h S i
    subst b
    rfl
  have castSeriesStored : ∀ {a b : ℕ} (h : a = b)
      (S : TashkinovSeries G k a e0 corr.replacementInput)
      (i : Fin (b + 1)),
      (castSeries h S).data.stored i =
        S.data.stored
          (Fin.cast (congrArg (fun m : ℕ => m + 1) h.symm) i) := by
    intro a b h S i
    subst b
    rfl
  have castSeriesEdges : ∀ {a b : ℕ} (h : a = b)
      (S : TashkinovSeries G k a e0 corr.replacementInput)
      (i : Fin (b + 1)),
      (castSeries h S).data.connectingEdges i =
        S.data.connectingEdges
          (Fin.cast (congrArg (fun m : ℕ => m + 1) h.symm) i) := by
    intro a b h S i
    subst b
    rfl
  have castSeriesKind : ∀ {a b : ℕ} (h : a = b)
      (S : TashkinovSeries G k a e0 corr.replacementInput)
      (i : Fin (b + 1)),
      (castSeries h S).data.kind i =
        S.data.kind
          (Fin.cast (congrArg (fun m : ℕ => m + 1) h.symm) i) := by
    intro a b h S i
    subst b
    rfl
  let finalSeries : TashkinovSeries G k ett.rounds e0
      corr.replacementInput :=
    castSeries hroundsEq extendedSeries
  let rawPenultimate : Fin (originalPrefix.rounds + 3) :=
    Fin.cast
      (congrArg (fun m : ℕ => m + 2) hroundsEq.symm)
      (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2))
  have hrawPenultimate : rawPenultimate =
      replacementLast.succ.castSucc := by
    apply Fin.ext
    simp [rawPenultimate, replacementLast]
    omega
  have hfinalPenultimateTree : finalSeries.data.tree
        (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2)) =
      ett.series.data.tree
        (Fin.last ett.rounds).castSucc := by
    exact @helper_hfinalPenultimateTree_4384 (@V) (@E) inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@Tstar)
        (@closureTree) (@hqSucc) (@choice) (@sigmaPrev) (@hroundLarge) (@originalPrefix) (@hr)
        (@corr) (@horiginalPositive) (@hreplacementCurrentTree) (@extendedSeries)
        (@hextendedData) (@hroundsEq) (@castSeriesTree) (@hrawPenultimate)
  let rawFinalTree : Fin (originalPrefix.rounds + 3) :=
    Fin.cast
      (congrArg (fun m : ℕ => m + 2) hroundsEq.symm)
      (Fin.last (ett.rounds + 1))
  have hrawFinalTree : rawFinalTree =
      Fin.last (originalPrefix.rounds + 2) := by
    apply Fin.ext
    simp [rawFinalTree]
  have hfinalTree : finalSeries.data.tree
        (Fin.last (ett.rounds + 1)) = closureTree := by
    exact @helper_hfinalTree_4414 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@Tstar) (@closureTree)
        (@choice) (@sigmaPrev) (@originalPrefix) (@corr) (@extendedSeries) (@hextendedData)
        (@hroundsEq) (@castSeriesTree) (@hrawFinalTree)
  exact @helper_continuation_1015 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
      (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@hsigmaProper) (@hsigmaOne)
      (@hsigmaStable) (@Tstar) (@hTnTstar) (@hstrict) (@closureTree) (@hTstarClosure) (@hqSucc)
      (@choice) (@currentStored) (@currentEdges) (@currentKind) (@sigmaPrev) (@hroundLarge)
      (@originalPrefix) (@hr) (@hprefixTrees) (@hprefixData) (@corr) (@horiginalPositive)
      (@extendedSeries) (@hextendedData) (@hroundsEq) (@castSeriesTree) (@castSeriesColoring)
      (@castSeriesStored) (@castSeriesEdges) (@castSeriesKind) (@hfinalPenultimateTree)
      (@hfinalTree)
private theorem helper_continuation_1218.{u_1, u_2} :
    helperContinuation1218Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma hsigmaProper hsigmaOne
      hsigmaStable Tstar hTnTstar hstrict closureTree hTstarClosure q hqSucc gamma choice
      currentStored currentEdges currentKind sigmaPrev H u p hroundLarge originalPrefix hr
      hprefixTrees hprefixData corr horiginalPositive newStored newEdges newKind newVertex
      newOutside newDelta newGamma extendedSeries hextendedData hroundsEq castSeries
      castSeriesTree castSeriesColoring castSeriesStored castSeriesEdges castSeriesKind
      finalSeries hfinalPenultimateTree hfinalTree
  let rawFinalColor : Fin (originalPrefix.rounds + 2) :=
    Fin.cast
      (congrArg (fun m : ℕ => m + 1) hroundsEq.symm)
      (Fin.last ett.rounds)
  have hrawFinalColor : rawFinalColor =
      Fin.last (originalPrefix.rounds + 1) := by
    apply Fin.ext
    simp [rawFinalColor]
  have hfinalColor : finalSeries.data.coloring
        (Fin.last ett.rounds) = sigma := by
    exact @helper_hfinalColor_6721 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@Tstar) (@closureTree)
        (@gamma) (@choice) (@sigmaPrev) (@originalPrefix) (@corr) (@extendedSeries)
        (@hextendedData) (@hroundsEq) (@castSeriesColoring) (@hrawFinalColor)
  let rawDataIndex (i : Fin (ett.rounds + 1)) :
      Fin (originalPrefix.rounds + 2) :=
    Fin.cast
      (congrArg (fun m : ℕ => m + 1) hroundsEq.symm) i
  have hseriesDataAgree : ∀ i : Fin (ett.rounds + 1),
      finalSeries.data.stored i = ett.series.data.stored i ∧
      finalSeries.data.connectingEdges i =
        ett.series.data.connectingEdges i ∧
      finalSeries.data.kind i = ett.series.data.kind i := by
    intro i
    by_cases hi : i.val < ett.rounds
    · exact @helper_branch_6743 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@Tstar) (@closureTree)
        (@gamma) (@choice) (@sigmaPrev) (@u) (@p) (@hroundLarge) (@originalPrefix) (@hr)
        (@hprefixData) (@corr) (@horiginalPositive) (@extendedSeries) (@hextendedData)
        (@hroundsEq) (@castSeriesStored) (@castSeriesEdges) (@castSeriesKind) (@i) (@hi)
    · exact @helper_branch_6801 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@Tstar) (@closureTree)
        (@hqSucc) (@gamma) (@choice) (@currentStored) (@currentEdges) (@currentKind) (@sigmaPrev)
        (@u) (@p) (@hroundLarge) (@originalPrefix) (@hr) (@corr) (@horiginalPositive)
        (@extendedSeries) (@hextendedData) (@hroundsEq) (@castSeriesStored) (@castSeriesEdges)
        (@castSeriesKind) (@i) (@hi)
  let rawTreeIndex (i : Fin (ett.rounds + 2)) :
      Fin (originalPrefix.rounds + 3) :=
    Fin.cast
      (congrArg (fun m : ℕ => m + 2) hroundsEq.symm) i
  have hseriesTreeAgree : ∀ i : Fin ett.rounds,
      finalSeries.data.tree i.succ.castSucc =
        ett.series.data.tree i.succ.castSucc := by
    exact @helper_hseriesTreeAgree_6867 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@Tstar)
        (@closureTree) (@gamma) (@choice) (@sigmaPrev) (@u) (@p) (@hroundLarge) (@originalPrefix)
        (@hr) (@hprefixTrees) (@corr) (@horiginalPositive) (@extendedSeries) (@hextendedData)
        (@hroundsEq) (@castSeriesTree) (@hfinalPenultimateTree)
  have hseriesColorProperties : ∀ i : Fin (ett.rounds + 1),
      IsProperEdgeColoring G (finalSeries.data.coloring i) ∧
        IsOneEdgeUncolored (finalSeries.data.coloring i) e0 := by
    exact finalSeries.coloringProperties
  have hseriesStable : ∀ i : Fin ett.rounds,
      StableColoring
        (ett.series.data.tree i.succ.castSucc)
        (TashkinovStoredColors ett.series.data i.succ)
        (ett.series.data.coloring i.succ)
        (finalSeries.data.coloring i.succ) := by
    exact TashkinovSeriesData.stabilityOfPrefix
      ett.series.data finalSeries.data.coloring originalPrefix.series.data
      corr.replacementSeries.data.coloring hroundsEq hprefixTrees
      (fun j => (hprefixData j).2.2.2.2) (fun j => (hprefixData j).1)
      (TashkinovSeriesData.prefixColoringOfCast hroundsEq
        corr.replacementSeries.data.coloring sigma finalSeries.data.coloring (by
          intro j
          calc
            finalSeries.data.coloring j = extendedSeries.data.coloring
                (Fin.cast (congrArg (fun n => n + 1) hroundsEq.symm) j) :=
              castSeriesColoring hroundsEq extendedSeries j
            _ = _ := by rw [hextendedData]; rfl))
      corr.replacementStable (by rw [hfinalColor]; exact hsigmaStable)
  let replacementETT : ExtendedTashkinovTree G k e0
      corr.replacementInput Tstar sigma := by
    exact {
      rounds := ett.rounds
      roundsPositive := ett.roundsPositive
      series := finalSeries
      abovePenultimate := by
        rw [hfinalPenultimateTree]
        exact hTnTstar
      strictAbovePenultimate := by
        rw [hfinalPenultimateTree]
        exact hstrict
      belowFinal := by
        rw [hfinalTree]
        exact hTstarClosure
      generatingColoring := hfinalColor.symm
  }
  refine ⟨{
    replacementInput := corr.replacementInput
    replacementSeries := finalSeries
    replacementETT := replacementETT
    rungAgreement := rfl
    seriesPresentation := by dsimp [replacementETT]; rfl
    finalGeneratingColoring := hfinalColor.symm
    ladderTreesAgree := hseriesTreeAgree
    storedColorsAgree := fun i => (hseriesDataAgree i).1
    connectingEdgesAgree := fun i => (hseriesDataAgree i).2.1
    extensionKindsAgree := fun i => (hseriesDataAgree i).2.2
    replacementProper := fun i =>
      (hseriesColorProperties i).1
    replacementOneUncolored := fun i =>
      (hseriesColorProperties i).2
    replacementStable := hseriesStable
  }⟩

private theorem helper_caseContinuation_1078.{u_1, u_2} :
    helperCaseContinuation1078Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma hsigmaProper hsigmaOne
      hsigmaStable Tstar hTnTstar hstrict closureTree hTstarClosure q hqSucc gamma choice
      currentStored currentEdges currentKind sigmaPrev H a b u p hroundLarge originalPrefix hr
      hprefixTrees hprefixData corr replacementLast horiginalPositive hreplacementCurrentTree
      newStored newEdges newKind newVertex newOutside newDelta newGamma appendedData lastStep
  obtain ⟨extendedSeries, hextendedData⟩ :=
    TashkinovSeriesAppend G k originalPrefix.rounds e0
      corr.replacementInput corr.replacementSeries closureTree sigma
      newStored newEdges newKind newVertex newOutside newDelta newGamma
      lastStep
  have hroundsEq : originalPrefix.rounds + 1 = ett.rounds := by
    rw [hr]
    omega
  let castSeries {a b : ℕ} (h : a = b)
      (S : TashkinovSeries G k a e0 corr.replacementInput) :
      TashkinovSeries G k b e0 corr.replacementInput := by
    subst b
    exact S
  have castSeriesTree : ∀ {a b : ℕ} (h : a = b)
      (S : TashkinovSeries G k a e0 corr.replacementInput)
      (i : Fin (b + 2)),
      (castSeries h S).data.tree i =
        S.data.tree
          (Fin.cast (congrArg (fun m : ℕ => m + 2) h.symm) i) := by
    intro a b h S i
    subst b
    rfl
  have castSeriesColoring : ∀ {a b : ℕ} (h : a = b)
      (S : TashkinovSeries G k a e0 corr.replacementInput)
      (i : Fin (b + 1)),
      (castSeries h S).data.coloring i =
        S.data.coloring
          (Fin.cast (congrArg (fun m : ℕ => m + 1) h.symm) i) := by
    intro a b h S i
    subst b
    rfl
  have castSeriesStored : ∀ {a b : ℕ} (h : a = b)
      (S : TashkinovSeries G k a e0 corr.replacementInput)
      (i : Fin (b + 1)),
      (castSeries h S).data.stored i =
        S.data.stored
          (Fin.cast (congrArg (fun m : ℕ => m + 1) h.symm) i) := by
    intro a b h S i
    subst b
    rfl
  have castSeriesEdges : ∀ {a b : ℕ} (h : a = b)
      (S : TashkinovSeries G k a e0 corr.replacementInput)
      (i : Fin (b + 1)),
      (castSeries h S).data.connectingEdges i =
        S.data.connectingEdges
          (Fin.cast (congrArg (fun m : ℕ => m + 1) h.symm) i) := by
    intro a b h S i
    subst b
    rfl
  have castSeriesKind : ∀ {a b : ℕ} (h : a = b)
      (S : TashkinovSeries G k a e0 corr.replacementInput)
      (i : Fin (b + 1)),
      (castSeries h S).data.kind i =
        S.data.kind
          (Fin.cast (congrArg (fun m : ℕ => m + 1) h.symm) i) := by
    intro a b h S i
    subst b
    rfl
  let finalSeries : TashkinovSeries G k ett.rounds e0
      corr.replacementInput :=
    castSeries hroundsEq extendedSeries
  let rawPenultimate : Fin (originalPrefix.rounds + 3) :=
    Fin.cast
      (congrArg (fun m : ℕ => m + 2) hroundsEq.symm)
      (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2))
  have hrawPenultimate : rawPenultimate =
      replacementLast.succ.castSucc := by
    apply Fin.ext
    simp [rawPenultimate, replacementLast]
    omega
  have hfinalPenultimateTree : finalSeries.data.tree
        (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2)) =
      ett.series.data.tree
        (Fin.last ett.rounds).castSucc := by
    exact @helper_hfinalPenultimateTree_6673 (@V) (@E) inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@Tstar)
        (@closureTree) (@hqSucc) (@gamma) (@choice) (@sigmaPrev) (@u) (@p) (@hroundLarge)
        (@originalPrefix) (@hr) (@corr) (@horiginalPositive) (@hreplacementCurrentTree)
        (@extendedSeries) (@hextendedData) (@hroundsEq) (@castSeriesTree) (@hrawPenultimate)
  let rawFinalTree : Fin (originalPrefix.rounds + 3) :=
    Fin.cast
      (congrArg (fun m : ℕ => m + 2) hroundsEq.symm)
      (Fin.last (ett.rounds + 1))
  have hrawFinalTree : rawFinalTree =
      Fin.last (originalPrefix.rounds + 2) := by
    apply Fin.ext
    simp [rawFinalTree]
  have hfinalTree : finalSeries.data.tree
        (Fin.last (ett.rounds + 1)) = closureTree := by
    exact @helper_hfinalTree_6703 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@Tstar) (@closureTree)
        (@gamma) (@choice) (@sigmaPrev) (@originalPrefix) (@corr) (@extendedSeries)
        (@hextendedData) (@hroundsEq) (@castSeriesTree) (@hrawFinalTree)
  exact @helper_continuation_1218 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
      (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@hsigmaProper) (@hsigmaOne)
      (@hsigmaStable) (@Tstar) (@hTnTstar) (@hstrict) (@closureTree) (@hTstarClosure) (@hqSucc)
      (@gamma) (@choice) (@currentStored) (@currentEdges) (@currentKind) (@sigmaPrev) (@u) (@p)
      (@hroundLarge) (@originalPrefix) (@hr) (@hprefixTrees) (@hprefixData) (@corr)
      (@horiginalPositive) (@extendedSeries) (@hextendedData) (@hroundsEq) (@castSeriesTree)
      (@castSeriesColoring) (@castSeriesStored) (@castSeriesEdges) (@castSeriesKind)
      (@hfinalPenultimateTree) (@hfinalTree)
private theorem helper_continuation_1431.{u_1, u_2} :
    helperContinuation1431Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma hsigmaProper hsigmaOne
      hsigmaStable Tstar hTnTstar hstrict closureTree hTstarClosure hTnClosure q hqSucc gamma
      secondStable previousProper previousOneUncolored choice currentStored currentEdges
      currentKind sigmaPrev hsigmaPrevProper hsigmaPrevOne hsigmaPrevStableQ hchoiceDefective
      hchoiceEdgeNew hsigmaPrevSelf hclosedPrev hnotStrongPrev hsigmaRecovered H a b u p hnewExit
      hroundLarge originalPrefix hr hprefixTrees hprefixData corr hcorrFinalColor replacementLast
      horiginalPositive hreplacementCurrentTree hreplacementStored replacementChoice
      hpeGammaRuleReplacement hterminalClosure newStored newEdges newKind newVertex newOutside
      newDelta newGamma appendedData happendedTree happendedStored happendedColor appendedChoice
      hnoRevisitingAppended hpeAlternativeAppended
  have hpeGammaRuleAppended : ParallelExtensionColor appendedData
      replacementLast.castSucc appendedChoice.selected
      appendedChoice.vertex gamma := by
    rw [ParallelExtensionColorAppend corr.replacementSeries.data
      closureTree sigma newStored newEdges newKind newVertex newOutside
      newDelta newGamma replacementLast appendedChoice.selected
      appendedChoice.vertex gamma]
    simpa [appendedChoice, replacementChoice] using
      hpeGammaRuleReplacement
  have hstrictClosure :
      (ett.series.data.tree
          (Fin.last ett.rounds).castSucc).length <
        closureTree.length :=
    lt_of_lt_of_le hstrict hTstarClosure.1
  have lastStep : TashkinovSeriesStep G k
      (originalPrefix.rounds + 1) e0 corr.replacementInput
      appendedData (Fin.last (originalPrefix.rounds + 1)) := by
    have hlast : replacementLast.succ =
        Fin.last (originalPrefix.rounds + 1) := by
      apply Fin.ext
      simp [replacementLast]
    rw [← hlast]
    apply TashkinovSeriesStep.PE (i := replacementLast)
      (choice := appendedChoice) (gamma := gamma)
      (secondStable := sigmaPrev)
    · rw [happendedColor, hcorrFinalColor]
      exact hsigmaPrevProper
    · rw [happendedColor, hcorrFinalColor]
      exact hsigmaPrevOne
    · rw [happendedColor, happendedTree, hcorrFinalColor,
        hreplacementCurrentTree]
      exact hclosedPrev
    · rw [happendedColor, happendedTree, hcorrFinalColor,
        hreplacementCurrentTree]
      exact hnotStrongPrev
    · exact hnoRevisitingAppended
    · exact hpeAlternativeAppended
    · exact hpeGammaRuleAppended
    · exact hsigmaPrevProper
    · exact hsigmaPrevOne
    · exact (sc2 G e0
        (appendedData.tree replacementLast.succ.castSucc)
        (insert appendedChoice.color
          (TashkinovStoredColors appendedData
            replacementLast.castSucc))).refl
        ⟨sigmaPrev, hsigmaPrevProper, hsigmaPrevOne⟩
    · change TreeExit
        (appendedData.tree replacementLast.succ.castSucc) sigmaPrev
        gamma choice.color choice.vertex
      rw [happendedTree, hreplacementCurrentTree]
      exact hnewExit
    · simp [appendedChoice, replacementChoice, appendedData,
        TashkinovSeriesDataAppend,
        hlast, hsigmaRecovered]
    · simpa [appendedData, TashkinovSeriesDataAppend, hlast] using
        hsigmaProper
    · simpa [appendedData, TashkinovSeriesDataAppend, hlast] using
        hsigmaOne
    · simp [appendedChoice, replacementChoice, appendedData,
        TashkinovSeriesDataAppend, newStored, hlast]
    · simp [appendedChoice, replacementChoice, appendedData,
        TashkinovSeriesDataAppend, newEdges, hlast]
    · simp [appendedData, TashkinovSeriesDataAppend, newKind, hlast]
    · simp [appendedChoice, replacementChoice, appendedData,
        TashkinovSeriesDataAppend, newVertex, hlast]
    · simp [appendedChoice, replacementChoice, appendedData,
        TashkinovSeriesDataAppend, newOutside, hlast]
    · simp [appendedChoice, replacementChoice, appendedData,
        TashkinovSeriesDataAppend, newDelta, hlast]
    · simp [appendedData, TashkinovSeriesDataAppend, newGamma, hlast]
    · rw [happendedTree, hreplacementCurrentTree]
      simpa [appendedData, TashkinovSeriesDataAppend, hlast, hqSucc]
        using hterminalClosure
    · change TreeSequenceInitialSegment
        (appendedData.tree replacementLast.succ.castSucc)
        (appendedData.tree (Fin.last (originalPrefix.rounds + 2)))
      rw [happendedTree, hreplacementCurrentTree]
      simpa [appendedData, TashkinovSeriesDataAppend, hqSucc] using
        hTnClosure
    · change (appendedData.tree replacementLast.succ.castSucc).length <
        (appendedData.tree
          (Fin.last (originalPrefix.rounds + 2))).length
      rw [happendedTree, hreplacementCurrentTree]
      simpa [appendedData, TashkinovSeriesDataAppend, hqSucc] using
        hstrictClosure
  exact @helper_caseContinuation_1078 (@V) (@E) inferInstance inferInstance inferInstance (@G)
      (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@hsigmaProper)
      (@hsigmaOne) (@hsigmaStable) (@Tstar) (@hTnTstar) (@hstrict) (@closureTree)
      (@hTstarClosure) (@hqSucc) (@gamma) (@choice) (@currentStored) (@currentEdges)
      (@currentKind) (@sigmaPrev) (@a) (@b) (@u) (@p) (@hroundLarge) (@originalPrefix) (@hr)
      (@hprefixTrees) (@hprefixData) (@corr) (@horiginalPositive) (@hreplacementCurrentTree)
      (@lastStep)

private theorem helper_branch_1075.{u_1, u_2} :
    helperBranch1075Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma hsigmaProper hsigmaOne
      hsigmaStable Tstar hTnTstar hstrict closureTree hclosure hTstarClosure hTnClosure q hqSucc
      gamma secondStable previousProper previousOneUncolored choice currentStored currentEdges
      currentKind sigmaPrev hsigmaPrevProper hsigmaPrevOne hsigmaPrevStableQ hchoiceDefective
      hchoiceEdgeNew hsigmaPrevSelf hclosedPrev hnotStrongPrev hsigmaRecovered H a b u p hnewExit
      hroundLarge originalPrefix hr hprefixTrees hprefixData corr hcorrFinalColor replacementLast
      horiginalPositive hreplacementCurrentTree hreplacementStored replacementChoice
      hnoRevisitingReplacement hpeAlternativeReplacement hpeGammaRuleReplacement hparallel
  have hrouteClosure : TashkinovAugmentationSequence sigma
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      closureTree := hparallel.2.trans hclosure.1
  have hterminalClosure : TashkinovClosure sigma
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      closureTree := ⟨hrouteClosure, hclosure.2⟩
  let newStored : Finset (Fin k) := {choice.color, gamma}
  let newEdges : Finset E := {choice.edge}
  let newKind : Option TashkinovExtensionKind :=
    some TashkinovExtensionKind.PE
  let newVertex : Option V := some choice.vertex
  let newOutside : Option V := some choice.otherEndpoint
  let newDelta : Option (Fin k) := some choice.color
  let newGamma : Option (Fin k) := some gamma
  let appendedData := TashkinovSeriesDataAppend
    corr.replacementSeries.data closureTree sigma newStored newEdges
    newKind newVertex newOutside newDelta newGamma
  have happendedTree :
      appendedData.tree replacementLast.succ.castSucc =
        corr.replacementSeries.data.tree replacementLast.succ := by
    simp only [appendedData, TashkinovSeriesDataAppend]
    exact Fin.lastCases_castSucc replacementLast.succ
  have happendedStored : TashkinovStoredColors appendedData
        replacementLast.castSucc =
      TashkinovStoredColors corr.replacementSeries.data
        replacementLast :=
    TashkinovStoredColorsAppend corr.replacementSeries.data
      closureTree sigma newStored newEdges newKind newVertex newOutside
      newDelta newGamma replacementLast
  have happendedColor : appendedData.coloring
        replacementLast.castSucc =
      corr.replacementSeries.data.coloring replacementLast := by
    simp [appendedData, TashkinovSeriesDataAppend]
  let appendedChoice : MaximumDefectiveChoice G e0
      (appendedData.tree replacementLast.succ.castSucc)
      (TashkinovStoredColors appendedData replacementLast.castSucc)
      (appendedData.coloring replacementLast.castSucc) := by
    exact {
      selected := replacementChoice.selected
      selectedProper := replacementChoice.selectedProper
      selectedOneUncolored := replacementChoice.selectedOneUncolored
      selectedStable := by
        rw [happendedTree, happendedStored, happendedColor]
        exact replacementChoice.selectedStable
      vertex := replacementChoice.vertex
      vertexDefective := by
        rw [happendedTree]
        exact replacementChoice.vertexDefective
      maximal := by
        intro pi w hpiProper hpiOne hpiStable hw
        rw [happendedTree, happendedStored, happendedColor] at hpiStable
        rw [happendedTree] at hw ⊢
        exact replacementChoice.maximal pi w hpiProper hpiOne hpiStable hw
      edge := replacementChoice.edge
      edgeDefective := by
        rw [happendedTree]
        exact replacementChoice.edgeDefective
      edgeIncident := replacementChoice.edgeIncident
      otherEndpoint := replacementChoice.otherEndpoint
      otherOutside := by
        rw [happendedTree]
        exact replacementChoice.otherOutside
      edgeEnds := replacementChoice.edgeEnds
      color := replacementChoice.color
      edgeColor := replacementChoice.edgeColor }
  have hnoRevisitingAppended : ¬ Nonempty
      (RevisitingExtensionCertificate appendedData
        replacementLast.castSucc) := by
    exact @helper_hnoRevisitingAppended_6477 (@V) (@E) inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@Tstar)
        (@closureTree) (@gamma) (@choice) (@sigmaPrev) (@originalPrefix) (@corr)
        (@hnoRevisitingReplacement)
  have hpeAlternativeAppended : ∃ rho : PartialEdgeColoring E k,
      IsProperEdgeColoring G rho ∧ IsOneEdgeUncolored rho e0 ∧
        StableColoring
          (appendedData.tree replacementLast.succ.castSucc)
          (insert appendedChoice.color
            (TashkinovStoredColors appendedData
              replacementLast.castSucc)) appendedChoice.selected rho ∧
        ¬ Disjoint
          (MissingColors G rho appendedChoice.otherEndpoint)
          (TreeMissingColors rho
            (appendedData.tree replacementLast.succ.castSucc)) := by
    rcases hpeAlternativeReplacement with
      ⟨rho, hrhoProper, hrhoOne, hrhoStable, hrhoNotDisjoint⟩
    refine ⟨rho, hrhoProper, hrhoOne, ?_, ?_⟩
    · change StableColoring
        (appendedData.tree replacementLast.succ.castSucc)
        (insert replacementChoice.color
          (TashkinovStoredColors appendedData
            replacementLast.castSucc)) replacementChoice.selected rho
      rw [happendedTree, happendedStored]
      exact hrhoStable
    · change ¬ Disjoint
        (MissingColors G rho replacementChoice.otherEndpoint)
        (TreeMissingColors rho
          (appendedData.tree replacementLast.succ.castSucc))
      rw [happendedTree]
      exact hrhoNotDisjoint
  exact @helper_continuation_1431 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
      (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@hsigmaProper) (@hsigmaOne)
      (@hsigmaStable) (@Tstar) (@hTnTstar) (@hstrict) (@closureTree) (@hTstarClosure)
      (@hTnClosure) (@hqSucc) (@gamma) (@secondStable) (@previousProper) (@previousOneUncolored)
      (@choice) (@currentStored) (@currentEdges) (@currentKind) (@sigmaPrev) (@hsigmaPrevProper)
      (@hsigmaPrevOne) (@hsigmaPrevStableQ) (@hchoiceDefective) (@hchoiceEdgeNew)
      (@hsigmaPrevSelf) (@hclosedPrev) (@hnotStrongPrev) (@hsigmaRecovered) (@a) (@b) (@u) (@p)
      (@hnewExit) (@hroundLarge) (@originalPrefix) (@hr) (@hprefixTrees) (@hprefixData) (@corr)
      (@hcorrFinalColor) (@horiginalPositive) (@hreplacementCurrentTree) (@hreplacementStored)
      (@hpeGammaRuleReplacement) (@hterminalClosure) (@happendedTree) (@happendedStored)
      (@happendedColor) (@hnoRevisitingAppended) (@hpeAlternativeAppended)
private theorem helper_continuation_1943.{u_1, u_2} :
    helperContinuation1943Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hMP hpositive hlower sigma hsigmaProper
      hsigmaOne hsigmaStable Tstar hTnTstar hstrict heligible closureTree hclosure hTstarClosure
      hTnClosure q hqSucc gamma secondStable previousProper previousOneUncolored noRevisiting
      choice gammaRule currentStored currentEdges currentKind hpeKind sigmaPrev hsigmaPrevProper
      hsigmaPrevOne hprefixCases hsigmaPrevStableQ hchoiceDefective hchoiceEdgeNew hsigmaPrevSelf
      newChoice hclosedPrev hnotStrongPrev hnewAlternativeFails hgammaPrevMissing hsigmaRecovered
      H hedgeComponent a b _ _ u p hp hnewExit
  rcases hprefixCases with hzero | hpositivePrefix
  · exact @helper_branch_13492 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
      (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@hsigmaProper) (@hsigmaOne)
      (@hsigmaStable) (@Tstar) (@hTnTstar) (@hstrict) (@heligible) (@closureTree) (@hclosure)
      (@hTstarClosure) (@hTnClosure) (@hqSucc) (@gamma) (@secondStable) (@previousProper)
      (@previousOneUncolored) (@choice) (@currentStored) (@currentEdges) (@currentKind)
      (@hpeKind) (@sigmaPrev) (@hsigmaPrevProper) (@hsigmaPrevOne) (@hsigmaPrevStableQ)
      (@hchoiceDefective) (@hchoiceEdgeNew) (@hsigmaPrevSelf) (@hclosedPrev) (@hnotStrongPrev)
      (@hnewAlternativeFails) (@hgammaPrevMissing) (@hsigmaRecovered) (@a) (@b) _ (by assumption)
      (@u) (@p) (@hp) (@hnewExit) (@hzero)
  · rcases hpositivePrefix with ⟨hroundLarge, originalPrefix, hr,
        hprefixMP, hprefixTrees, hprefixData, corr, hcorrFinalTree,
        hcorrFinalColor, hcorrMP⟩
    let replacementLast : Fin (originalPrefix.rounds + 1) :=
      Fin.last originalPrefix.rounds
    have horiginalPositive : 0 < originalPrefix.rounds := by
      rw [hr]
      omega
    let previousReplacement : Fin originalPrefix.rounds :=
      ⟨originalPrefix.rounds - 1,
        Nat.sub_lt horiginalPositive (by omega)⟩
    have hpreviousSucc : previousReplacement.succ = replacementLast := by
      apply Fin.ext
      simp [previousReplacement, replacementLast]
      omega
    have hlastMap : Fin.castLE (by omega) replacementLast =
        q.castSucc := by
      apply Fin.ext
      simp [replacementLast, q, hr]
    have hreplacementCurrentTree :
        corr.replacementSeries.data.tree replacementLast.succ =
          ett.series.data.tree q.succ.castSucc := by
      exact @helper_hreplacementCurrentTree_5844 (@V) (@E) inferInstance inferInstance
          inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@Tstar)
          (@hqSucc) (@sigmaPrev) (@originalPrefix) (@corr) (@hcorrFinalTree)
    have horiginalCurrentTree :
        originalPrefix.series.data.tree replacementLast.castSucc =
          ett.series.data.tree q.castSucc.castSucc := by
      exact @helper_horiginalCurrentTree_5852 (@V) (@E) inferInstance inferInstance inferInstance
          (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@Tstar) (@gamma)
          (@choice) (@sigmaPrev) (@u) (@p) (@hroundLarge) (@originalPrefix) (@hr) (@hprefixTrees)
          (@horiginalPositive)
    have htreeMissingEq : TreeMissingColors
          (corr.replacementSeries.data.coloring replacementLast)
          (corr.replacementSeries.data.tree replacementLast.castSucc) =
        TreeMissingColors
          (originalPrefix.series.data.coloring replacementLast)
          (originalPrefix.series.data.tree replacementLast.castSucc) := by
      exact @helper_htreeMissingEq_5864 (@V) (@E) inferInstance inferInstance inferInstance (@G)
          (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@Tstar) (@gamma) (@choice)
          (@sigmaPrev) (@u) (@p) (@originalPrefix) (@corr) (@horiginalPositive) (@hpreviousSucc)
    have hreplacementStored : TashkinovStoredColors
          corr.replacementSeries.data replacementLast =
        TashkinovStoredColors ett.series.data q.castSucc := by
      exact @helper_hreplacementStored_5882 (@V) (@E) inferInstance inferInstance inferInstance
          (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@Tstar) (@gamma)
          (@choice) (@sigmaPrev) (@u) (@p) (@hroundLarge) (@originalPrefix) (@hr) (@hprefixData)
          (@corr) (@horiginalPositive) (@hlastMap) (@htreeMissingEq)
    let replacementChoice : MaximumDefectiveChoice G e0
        (corr.replacementSeries.data.tree replacementLast.succ)
        (TashkinovStoredColors corr.replacementSeries.data replacementLast)
        (corr.replacementSeries.data.coloring replacementLast) := by
      exact @helperReplacementChoice5196 (@V) (@E) inferInstance inferInstance
          inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive)
           (@previousProper) (@previousOneUncolored) (@choice) (@sigmaPrev)
          (@hsigmaPrevProper) (@hsigmaPrevOne) (@hsigmaPrevStableQ) (@hchoiceDefective)
          (@hchoiceEdgeNew) (@hsigmaPrevSelf) (@originalPrefix) (@corr) (@hcorrFinalColor)
          (@hreplacementCurrentTree) (@hreplacementStored)
    have hnoRevisitingReplacement : ¬ Nonempty
        (RevisitingExtensionCertificate corr.replacementSeries.data
          replacementLast) := by
      exact @helper_hnoRevisitingReplacement_5934 (@V) (@E) inferInstance inferInstance
           inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hMP)
          (@hpositive) (@hlower) (@Tstar) (@gamma) (@previousProper) (@previousOneUncolored)
          (@noRevisiting) (@choice) (@sigmaPrev) (@hsigmaPrevProper) (@hsigmaPrevOne)
          (@hsigmaPrevStableQ) (@u) (@p) (@hp) (@hroundLarge) (@originalPrefix) (@hr)
          (@hprefixMP) (@hprefixTrees) (@hprefixData) (@corr) (@hcorrFinalTree)
          (@hcorrFinalColor) (@hcorrMP)
    have hpeAlternativeReplacement : ∃ rho : PartialEdgeColoring E k,
        IsProperEdgeColoring G rho ∧ IsOneEdgeUncolored rho e0 ∧
          StableColoring
            (corr.replacementSeries.data.tree replacementLast.succ)
            (insert replacementChoice.color
              (TashkinovStoredColors corr.replacementSeries.data
                replacementLast)) replacementChoice.selected rho ∧
          ¬ Disjoint
            (MissingColors G rho replacementChoice.otherEndpoint)
            (TreeMissingColors rho
              (corr.replacementSeries.data.tree replacementLast.succ)) := by
      exact @helper_hpeAlternativeReplacement_5946 (@V) (@E) inferInstance inferInstance
          inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive)
          (@previousProper) (@previousOneUncolored) (@choice) (@sigmaPrev) (@hsigmaPrevProper)
          (@hsigmaPrevOne) (@hsigmaPrevStableQ) (@hchoiceDefective) (@hchoiceEdgeNew)
          (@hsigmaPrevSelf) (@hnewAlternativeFails) (@originalPrefix) (@corr) (@hcorrFinalColor)
          (@hreplacementCurrentTree) (@hreplacementStored)
    have hpeGammaRuleReplacement : ParallelExtensionColor
        corr.replacementSeries.data replacementLast
        replacementChoice.selected replacementChoice.vertex gamma := by
      exact @helper_hpeGammaRuleReplacement_13982 (@V) (@E) inferInstance inferInstance
          inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@Tstar)
          (@gamma) (@previousProper) (@previousOneUncolored) (@choice) (@gammaRule) (@sigmaPrev)
          (@hsigmaPrevProper) (@hsigmaPrevOne) (@hsigmaPrevStableQ) (@hchoiceDefective)
          (@hchoiceEdgeNew) (@hsigmaPrevSelf) (@hgammaPrevMissing) (@hedgeComponent) (@u) (@p)
          (@hroundLarge) (@originalPrefix) (@hr) (@hprefixTrees) (@hprefixData) (@corr)
          (@hcorrFinalColor) (@horiginalPositive) (@hreplacementCurrentTree) (@hreplacementStored)
    rcases heligible with hparallel | hsimple
    · exact @helper_branch_1075 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@hsigmaProper)
        (@hsigmaOne) (@hsigmaStable) (@Tstar) (@hTnTstar) (@hstrict) (@closureTree) (@hclosure)
        (@hTstarClosure) (@hTnClosure) (@hqSucc) (@gamma) (@secondStable) (@previousProper)
        (@previousOneUncolored) (@choice) (@currentStored) (@currentEdges) (@currentKind)
        (@sigmaPrev) (@hsigmaPrevProper) (@hsigmaPrevOne) (@hsigmaPrevStableQ)
        (@hchoiceDefective) (@hchoiceEdgeNew) (@hsigmaPrevSelf) (@hclosedPrev) (@hnotStrongPrev)
        (@hsigmaRecovered) (@a) (@b) (@u) (@p) (@hnewExit) (@hroundLarge) (@originalPrefix) (@hr)
        (@hprefixTrees) (@hprefixData) (@corr) (@hcorrFinalColor) (@horiginalPositive)
        (@hreplacementCurrentTree) (@hreplacementStored) (@hnoRevisitingReplacement)
        (@hpeAlternativeReplacement) (@hpeGammaRuleReplacement) (@hparallel)
    · exact @helper_branch_7068 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@Tstar) (@hqSucc)
        (@hpeKind) (@hsimple)

private theorem helper_caseContinuation_1201.{u_1, u_2} :
    helperCaseContinuation1201Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hMP hpositive hlower sigma hsigmaProper
      hsigmaOne hsigmaStable Tstar hTnTstar hstrict heligible closureTree hclosure hTstarClosure
      hTnClosure q hqSucc gamma secondStable previousProper previousOneUncolored noRevisiting
      choice gammaRule currentStored currentEdges currentKind hpeKind sigmaPrev hsigmaPrevProper
      hsigmaPrevOne hprefixCases hsigmaPrevStableQ hchoiceVertex hsigmaPrevFormula
      hchoiceDefective hchoiceEdgeNew hsigmaPrevSelf newChoice hclosedPrev hnotStrongPrev
      hnewAlternativeFails hgammaDeltaNe hsigmaComponentColor hgammaPrevMissing hswapGraph
      hcomponentPrev
  have hsigmaRecovered : sigma =
      TwoColorComponentSwap G sigmaPrev gamma choice.color
        (Sum.inl choice.vertex) := by
    exact @helper_hsigmaRecovered_2774 (@V) (@E) inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@Tstar)
        (@gamma) (@choice) (@sigmaPrev) (@hsigmaPrevFormula) (@hgammaDeltaNe)
        (@hsigmaComponentColor) (@hswapGraph)
  let H := TwoColorIncidenceGraph G sigmaPrev gamma choice.color
  have hrootLeaf : Set.Subsingleton
      (H.neighborSet (Sum.inl choice.vertex)) := by
    exact @helper_hrootLeaf_5339 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@Tstar) (@gamma) (@choice)
        (@sigmaPrev) (@hsigmaPrevProper) (@hgammaDeltaNe) (@hgammaPrevMissing)
  have hrootComponent : Sum.inl choice.vertex ∈
      TwoColorComponent G sigmaPrev gamma choice.color
        (Sum.inl choice.vertex) := by
    change H.connectedComponentMk (Sum.inl choice.vertex) =
      H.connectedComponentMk (Sum.inl choice.vertex)
    rfl
  have hedgeComponent : Sum.inr choice.edge ∈
      TwoColorComponent G sigmaPrev gamma choice.color
        (Sum.inl choice.vertex) := by
    apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    simp [TwoColorIncidenceGraph, choice.edgeIncident,
      (Finset.mem_filter.mp hchoiceEdgeNew).2]
  obtain ⟨a, b, p, hp, hps⟩ :=
    TwoColorComponentSpanningPath G sigmaPrev gamma choice.color
      hsigmaPrevProper (Sum.inl choice.vertex)
  have hrootSupport : Sum.inl choice.vertex ∈ p.support := by
    change Sum.inl choice.vertex ∈ {z | z ∈ p.support}
    rw [hps]
    exact hrootComponent
  have hrootEnd : Sum.inl choice.vertex = a ∨
      Sum.inl choice.vertex = b := by
    by_contra hn
    push Not at hn
    exact (hp.isTrail.notMem_support_of_subsingleton_neighborSet
      hn.1 hn.2 hrootLeaf) hrootSupport
  obtain ⟨b, p, hp, hps⟩ : ∃ (b : Sum V E)
      (p : H.Walk (Sum.inl choice.vertex) b),
      p.IsPath ∧ {z | z ∈ p.support} =
        TwoColorComponent G sigmaPrev gamma choice.color
          (Sum.inl choice.vertex) := by
    rcases hrootEnd with ha | hb
    · subst a
      exact ⟨b, p, hp, hps⟩
    · exact @helper_branch_5387 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@Tstar) (@gamma) (@choice)
        (@sigmaPrev) (@a) (@b) (@p) (@hp) (@hps) (@hrootSupport) (@hb)
  have hpNotNil : ¬ p.Nil := by
    exact @helper_hpNotNil_5395 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@Tstar) (@gamma) (@choice)
        (@sigmaPrev) (@hedgeComponent) (@b) (@p) (@hps)
  have hendNeighbor : ∀ y, H.Adj b y →
      y = p.getVert (p.length - 1) := by
    exact @helper_hendNeighbor_2869 (@V) (@E) inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@Tstar)
        (@gamma) (@choice) (@sigmaPrev) (@hsigmaPrevProper) (@hrootLeaf) (@a) _ _ (by assumption)
        (by assumption) (@b) (@p) (@hp) (@hps) (@hpNotNil)
  have hendLeaf : Set.Subsingleton (H.neighborSet b) := by
    intro y hy z hz
    exact (hendNeighbor y hy).trans (hendNeighbor z hz).symm
  have hpPos : 0 < p.length :=
    SimpleGraph.Walk.not_nil_iff_lt_length.mp hpNotNil
  have hendVertex : ∃ u : V, b = Sum.inl u := by
    exact @helper_hendVertex_2974 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@Tstar) (@gamma) (@choice)
        (@sigmaPrev) (@a) _ (by assumption) (@b) (@p) (@hendLeaf) (@hpPos)
  obtain ⟨u, hu⟩ := hendVertex
  subst b
  have hvu : choice.vertex ≠ u := by
    intro hvu
    apply hpNotNil
    exact hp.nil_iff_eq.mpr (by simp [hvu])
  have hendMissing : gamma ∈ MissingColors G sigmaPrev u ∨
      choice.color ∈ MissingColors G sigmaPrev u := by
    exact @helper_hendMissing_3025 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@Tstar) (@gamma)
        (@choice) (@sigmaPrev) (@hgammaDeltaNe) (@u) (@hendLeaf)
  have huComponent : Sum.inl u ∈
      TwoColorComponent G sigmaPrev gamma choice.color
        (Sum.inl choice.vertex) := by
    rw [← hps]
    change Sum.inl u ∈ p.support
    simpa only [p.getVert_length] using p.getVert_mem_support p.length
  have huOutside : u ∉ TreeSequenceVertexSet
      (ett.series.data.tree q.succ.castSucc) := by
    intro huTree
    exact hvu.symm ((hcomponentPrev u huTree).mp huComponent)
  have hpNotOne : p.length ≠ 1 := by
    exact @helper_hpNotOne_5434 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@Tstar) (@gamma) (@choice)
        (@sigmaPrev) (@u) (@p) (@hpPos)
  have hnewExit : TreeExit
      (ett.series.data.tree q.succ.castSucc) sigmaPrev gamma
        choice.color choice.vertex := by
    exact @helper_hnewExit_3069 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@Tstar) (@gamma) (@choice)
        (@sigmaPrev) (@hchoiceVertex) (@hcomponentPrev) (@a) (@b) _ (by assumption)
        (by assumption) (@u) (@p) (@hp) (@hps) (@hpPos) (@hendMissing) (@huOutside) (@hpNotOne)
  exact @helper_continuation_1943 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hMP) (@hpositive)
      (@hlower) (@sigma) (@hsigmaProper) (@hsigmaOne) (@hsigmaStable) (@Tstar) (@hTnTstar)
      (@hstrict) (@heligible) (@closureTree) (@hclosure) (@hTstarClosure) (@hTnClosure) (@hqSucc)
      (@gamma) (@secondStable) (@previousProper) (@previousOneUncolored) (@noRevisiting)
      (@choice) (@gammaRule) (@currentStored) (@currentEdges) (@currentKind) (@hpeKind)
      (@sigmaPrev) (@hsigmaPrevProper) (@hsigmaPrevOne) (@hprefixCases) (@hsigmaPrevStableQ)
      (@hchoiceDefective) (@hchoiceEdgeNew) (@hsigmaPrevSelf) (@hclosedPrev) (@hnotStrongPrev)
      (@hnewAlternativeFails) (@hgammaPrevMissing) (@hsigmaRecovered) (@hedgeComponent) (@a) (@b)
      _ (by
    assumption) (@u) (@p) (@hp) (@hnewExit)
private theorem helper_branch_1497.{u_1, u_2} :
    helperBranch1497Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma hsigmaProper hsigmaOne
      hsigmaStable Tstar hTnTstar hstrict closureTree hclosure hTstarClosure hTnClosure q hqSucc
      adjoined previousProper previousOneUncolored choice currentStored currentEdges currentKind
      sigmaPrev hsigmaPrevProper hsigmaPrevOne hsigmaPrevStableQ hsigmaPrevSigma hchoiceDefective
      hchoiceEdgeNew hsigmaPrevSelf hclosedPrev hnotStrongPrev hroundLarge originalPrefix hr
      hprefixTrees hprefixData corr hcorrFinalColor replacementLast horiginalPositive
      hreplacementCurrentTree hreplacementStored replacementChoice hnoRevisitingReplacement
      hnewAlternativeReplacement hsimple
  rcases hsimple with ⟨hkind, fstar, seed, hfinalEdges,
      hadjoin, hroute⟩
  have hfstar : fstar = choice.edge := by
    apply Finset.mem_singleton.mp
    rw [← currentEdges, hqSucc, hfinalEdges]
    exact Finset.mem_singleton_self fstar
  have hrouteClosure : TashkinovAugmentationSequence sigma seed
      closureTree := hroute.trans hclosure.1
  have hseedClosure : TashkinovClosure sigma seed closureTree :=
    ⟨hrouteClosure, hclosure.2⟩
  let newStored : Finset (Fin k) := {choice.color}
  let newEdges : Finset E := {choice.edge}
  let newKind : Option TashkinovExtensionKind :=
    some TashkinovExtensionKind.SE
  let newVertex : Option V := some choice.vertex
  let newOutside : Option V := some choice.otherEndpoint
  let newDelta : Option (Fin k) := some choice.color
  let newGamma : Option (Fin k) := none
  let appendedData := TashkinovSeriesDataAppend
    corr.replacementSeries.data closureTree sigma newStored newEdges
    newKind newVertex newOutside newDelta newGamma
  have happendedTree :
      appendedData.tree replacementLast.succ.castSucc =
        corr.replacementSeries.data.tree replacementLast.succ := by
    simp only [appendedData, TashkinovSeriesDataAppend]
    exact Fin.lastCases_castSucc replacementLast.succ
  have happendedStored : TashkinovStoredColors appendedData
        replacementLast.castSucc =
      TashkinovStoredColors corr.replacementSeries.data
        replacementLast :=
    TashkinovStoredColorsAppend corr.replacementSeries.data
      closureTree sigma newStored newEdges newKind newVertex newOutside
      newDelta newGamma replacementLast
  have happendedColor : appendedData.coloring
        replacementLast.castSucc =
      corr.replacementSeries.data.coloring replacementLast := by
    simp [appendedData, TashkinovSeriesDataAppend]
  let appendedChoice : MaximumDefectiveChoice G e0
      (appendedData.tree replacementLast.succ.castSucc)
      (TashkinovStoredColors appendedData replacementLast.castSucc)
      (appendedData.coloring replacementLast.castSucc) := by
    exact {
      selected := replacementChoice.selected
      selectedProper := replacementChoice.selectedProper
      selectedOneUncolored := replacementChoice.selectedOneUncolored
      selectedStable := by
        rw [happendedTree, happendedStored, happendedColor]
        exact replacementChoice.selectedStable
      vertex := replacementChoice.vertex
      vertexDefective := by
        rw [happendedTree]
        exact replacementChoice.vertexDefective
      maximal := by
        intro pi w hpiProper hpiOne hpiStable hw
        rw [happendedTree, happendedStored, happendedColor] at hpiStable
        rw [happendedTree] at hw ⊢
        exact replacementChoice.maximal pi w hpiProper hpiOne hpiStable hw
      edge := replacementChoice.edge
      edgeDefective := by
        rw [happendedTree]
        exact replacementChoice.edgeDefective
      edgeIncident := replacementChoice.edgeIncident
      otherEndpoint := replacementChoice.otherEndpoint
      otherOutside := by
        rw [happendedTree]
        exact replacementChoice.otherOutside
      edgeEnds := replacementChoice.edgeEnds
      color := replacementChoice.color
      edgeColor := replacementChoice.edgeColor }
  have hnoRevisitingAppended : ¬ Nonempty
      (RevisitingExtensionCertificate appendedData
        replacementLast.castSucc) := by
    exact @helper_hnoRevisitingAppended_4214 (@V) (@E) inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@Tstar)
        (@closureTree) (@choice) (@sigmaPrev) (@originalPrefix) (@corr) (@hnoRevisitingReplacement)
  have hnewAlternativeAppended : ∀ pi : PartialEdgeColoring E k,
      IsProperEdgeColoring G pi → IsOneEdgeUncolored pi e0 →
      StableColoring
        (appendedData.tree replacementLast.succ.castSucc)
        (insert appendedChoice.color
          (TashkinovStoredColors appendedData
            replacementLast.castSucc)) appendedChoice.selected pi →
      Disjoint
        (MissingColors G pi appendedChoice.otherEndpoint)
        (TreeMissingColors pi
          (appendedData.tree replacementLast.succ.castSucc)) := by
    intro pi hpiProper hpiOne hpiStable
    have hpiStable' := hpiStable
    change StableColoring
      (appendedData.tree replacementLast.succ.castSucc)
      (insert replacementChoice.color
        (TashkinovStoredColors appendedData
          replacementLast.castSucc)) replacementChoice.selected pi
        at hpiStable'
    rw [happendedTree, happendedStored] at hpiStable'
    have hresult := hnewAlternativeReplacement pi hpiProper hpiOne
      hpiStable'
    change Disjoint
      (MissingColors G pi replacementChoice.otherEndpoint)
      (TreeMissingColors pi
        (appendedData.tree replacementLast.succ.castSucc))
    rw [happendedTree]
    exact hresult
  have hstrictClosure :
      (ett.series.data.tree
          (Fin.last ett.rounds).castSucc).length <
        closureTree.length :=
    lt_of_lt_of_le hstrict hTstarClosure.1
  have lastStep : TashkinovSeriesStep G k
      (originalPrefix.rounds + 1) e0 corr.replacementInput
      appendedData (Fin.last (originalPrefix.rounds + 1)) := by
    have hlast : replacementLast.succ =
        Fin.last (originalPrefix.rounds + 1) := by
      apply Fin.ext
      simp [replacementLast]
    rw [← hlast]
    apply TashkinovSeriesStep.SE (i := replacementLast)
      (choice := appendedChoice) (adjoined := seed)
    · rw [happendedColor, hcorrFinalColor]
      exact hsigmaPrevProper
    · rw [happendedColor, hcorrFinalColor]
      exact hsigmaPrevOne
    · rw [happendedColor, happendedTree, hcorrFinalColor,
        hreplacementCurrentTree]
      exact hclosedPrev
    · rw [happendedColor, happendedTree, hcorrFinalColor,
        hreplacementCurrentTree]
      exact hnotStrongPrev
    · exact hnoRevisitingAppended
    · exact hnewAlternativeAppended
    · simp [appendedChoice, replacementChoice, appendedData,
        TashkinovSeriesDataAppend,
        hlast, hsigmaPrevSigma]
    · simp [appendedChoice, replacementChoice, appendedData,
        TashkinovSeriesDataAppend, newStored, hlast]
    · simp [appendedChoice, replacementChoice, appendedData,
        TashkinovSeriesDataAppend, newEdges, hlast]
    · simp [appendedData, TashkinovSeriesDataAppend, newKind, hlast]
    · simp [appendedChoice, replacementChoice, appendedData,
        TashkinovSeriesDataAppend, newVertex, hlast]
    · simp [appendedChoice, replacementChoice, appendedData,
        TashkinovSeriesDataAppend, newOutside, hlast]
    · simp [appendedChoice, replacementChoice, appendedData,
        TashkinovSeriesDataAppend, newDelta, hlast]
    · simp [appendedData, TashkinovSeriesDataAppend, newGamma, hlast]
    · change TreeSequenceAdjoinEdge
        (appendedData.tree replacementLast.succ.castSucc)
        choice.edge seed
      rw [happendedTree, hreplacementCurrentTree]
      simpa [appendedChoice, replacementChoice, hqSucc, hfstar] using
        hadjoin
    · simpa [appendedData, TashkinovSeriesDataAppend, hlast] using
        hseedClosure
    · change TreeSequenceInitialSegment
        (appendedData.tree replacementLast.succ.castSucc)
        (appendedData.tree (Fin.last (originalPrefix.rounds + 2)))
      rw [happendedTree, hreplacementCurrentTree]
      simpa [appendedData, TashkinovSeriesDataAppend, hqSucc] using
        hTnClosure
    · change (appendedData.tree replacementLast.succ.castSucc).length <
        (appendedData.tree
          (Fin.last (originalPrefix.rounds + 2))).length
      rw [happendedTree, hreplacementCurrentTree]
      simpa [appendedData, TashkinovSeriesDataAppend, hqSucc] using
        hstrictClosure
  exact @helper_caseContinuation_422 (@V) (@E) inferInstance inferInstance inferInstance (@G)
      (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@hsigmaProper)
      (@hsigmaOne) (@hsigmaStable) (@Tstar) (@hTnTstar) (@hstrict) (@closureTree)
      (@hTstarClosure) (@hqSucc) (@choice) (@currentStored) (@currentEdges) (@currentKind)
      (@sigmaPrev) (@hroundLarge) (@originalPrefix) (@hr) (@hprefixTrees) (@hprefixData) (@corr)
      (@horiginalPositive) (@hreplacementCurrentTree) (@lastStep)

private theorem helper_continuation_2339.{u_1, u_2} :
    helperContinuation2339Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hMP hpositive hlower sigma hsigmaProper
      hsigmaOne hsigmaStable Tstar hTnTstar hstrict heligible closureTree hclosure hTstarClosure
      hTnClosure q hqSucc hsigmaStableQ gamma secondStable secondStableProper previousProper
      previousOneUncolored previousClosed noRevisiting choice seriesAlternativeFails gammaRule
      secondStableRelation currentColoring currentStored currentEdges currentKind hpeKind
      sigmaPrev hsigmaPrevProper hsigmaPrevOne hprefixCases hsigmaPrevStableQ hchoiceVertex
      hcomponent hsigmaPrevFormula hsigmaPrevEnlarged hchoiceDefective hchoiceEdgeNew
  have hsigmaPrevSelf : StableColoring
      (ett.series.data.tree q.succ.castSucc)
      (TashkinovStoredColors ett.series.data q.castSucc)
      sigmaPrev sigmaPrev := by
    exact (sc2 G e0 (ett.series.data.tree q.succ.castSucc)
      (TashkinovStoredColors ett.series.data q.castSucc)).refl
      ⟨sigmaPrev, hsigmaPrevProper, hsigmaPrevOne⟩
  let newChoice : MaximumDefectiveChoice G e0
      (ett.series.data.tree q.succ.castSucc)
      (TashkinovStoredColors ett.series.data q.castSucc) sigmaPrev := by
    exact @helperNewChoice4049 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@previousProper)
        (@previousOneUncolored) (@choice) (@sigmaPrev) (@hsigmaPrevProper) (@hsigmaPrevOne)
        (@hsigmaPrevStableQ) (@hchoiceDefective) (@hchoiceEdgeNew) (@hsigmaPrevSelf)
  have hclosedPrev : ColoredVertexSetClosed G sigmaPrev
      (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) := by
    exact @helper_hclosedPrev_2545 (@V) (@E) inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive)
        (@Tstar) (@previousProper) (@previousOneUncolored) (@previousClosed) (@sigmaPrev)
        (@hsigmaPrevProper) (@hsigmaPrevOne) (@hsigmaPrevStableQ)
  have hnotStrongPrev : ¬ ColoredVertexSetStronglyClosed G sigmaPrev
      (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) := by
    exact @helper_hnotStrongPrev_5207 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@Tstar) (@choice)
        (@sigmaPrev) (@hchoiceDefective)
  have hnewAlternativeFails : ∃ rho : PartialEdgeColoring E k,
      IsProperEdgeColoring G rho ∧ IsOneEdgeUncolored rho e0 ∧
        StableColoring (ett.series.data.tree q.succ.castSucc)
          (insert newChoice.color
            (TashkinovStoredColors ett.series.data q.castSucc))
          newChoice.selected rho ∧
        ¬ Disjoint (MissingColors G rho newChoice.otherEndpoint)
          (TreeMissingColors rho
            (ett.series.data.tree q.succ.castSucc)) := by
    exact @helper_hnewAlternativeFails_5223 (@V) (@E) inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@Tstar)
        (@previousProper) (@previousOneUncolored) (@choice) (@seriesAlternativeFails)
        (@sigmaPrev) (@hsigmaPrevProper) (@hsigmaPrevOne) (@hsigmaPrevStableQ)
        (@hsigmaPrevEnlarged) (@hchoiceDefective) (@hchoiceEdgeNew) (@hsigmaPrevSelf)
  have hgammaSecond : gamma ∈ MissingColors G secondStable
      choice.vertex := by
    rw [secondStableRelation.2 choice.vertex choice.vertexDefective.1]
    exact gammaRule.1
  have hchoiceSecond : secondStable choice.edge = some choice.color := by
    exact @helper_hchoiceSecond_5266 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@Tstar) (@secondStable)
        (@choice) (@secondStableRelation)
  have hgammaDeltaNe : gamma ≠ choice.color := by
    exact @helper_hgammaDeltaNe_5272 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@Tstar) (@gamma)
        (@secondStable) (@choice) (@hgammaSecond) (@hchoiceSecond)
  have hchoiceSecondComponent : Sum.inr choice.edge ∈
      TwoColorComponent G secondStable gamma choice.color
        (Sum.inl choice.vertex) := by
    apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    simp [TwoColorIncidenceGraph, choice.edgeIncident, hchoiceSecond]
  have hdeltaCurrentMissing : choice.color ∈ MissingColors G
      (ett.series.data.coloring q.succ) choice.vertex := by
    exact @helper_hdeltaCurrentMissing_2652 (@V) (@E) inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive)
        (@Tstar) (@gamma) (@secondStable) (@secondStableProper) (@choice) (@currentColoring)
        (@hgammaSecond) (@hchoiceSecond) (@hgammaDeltaNe) (@hchoiceSecondComponent)
  have hdeltaSigmaMissing : choice.color ∈ MissingColors G sigma
      choice.vertex := by
    rw [hsigmaStableQ.2 choice.vertex hchoiceVertex]
    exact hdeltaCurrentMissing
  have hsigmaComponentColor : ∀ f,
      Sum.inr f ∈ TwoColorComponent G sigma gamma choice.color
          (Sum.inl choice.vertex) →
        sigma f = some gamma ∨ sigma f = some choice.color := by
    exact @helper_hsigmaComponentColor_5296 (@V) (@E) inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@Tstar)
        (@gamma) (@choice)
  have hgammaPrevMissing : gamma ∈ MissingColors G sigmaPrev
      choice.vertex := by
    exact @helper_hgammaPrevMissing_2707 (@V) (@E) inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@Tstar)
        (@gamma) (@choice) (@sigmaPrev) (@hsigmaPrevFormula) (@hgammaDeltaNe)
        (@hdeltaSigmaMissing) (@hsigmaComponentColor)
  have hswapGraph : TwoColorIncidenceGraph G sigmaPrev gamma choice.color =
      TwoColorIncidenceGraph G sigma gamma choice.color := by
    exact @helper_hswapGraph_2737 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@Tstar) (@gamma)
        (@choice) (@sigmaPrev) (@hsigmaPrevFormula) (@hgammaDeltaNe) (@hsigmaComponentColor)
  have hcomponentPrev : ∀ w,
      w ∈ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc) →
      (Sum.inl w ∈ TwoColorComponent G sigmaPrev gamma choice.color
          (Sum.inl choice.vertex) ↔ w = choice.vertex) := by
    intro w hw
    unfold TwoColorComponent
    rw [hswapGraph]
    exact hcomponent w hw
  exact @helper_caseContinuation_1201 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hMP) (@hpositive)
      (@hlower) (@sigma) (@hsigmaProper) (@hsigmaOne) (@hsigmaStable) (@Tstar) (@hTnTstar)
      (@hstrict) (@heligible) (@closureTree) (@hclosure) (@hTstarClosure) (@hTnClosure) (@hqSucc)
      (@gamma) (@secondStable) (@previousProper) (@previousOneUncolored) (@noRevisiting)
      (@choice) (@gammaRule) (@currentStored) (@currentEdges) (@currentKind) (@hpeKind)
      (@sigmaPrev) (@hsigmaPrevProper) (@hsigmaPrevOne) (@hprefixCases) (@hsigmaPrevStableQ)
      (@hchoiceVertex) (@hsigmaPrevFormula) (@hchoiceDefective) (@hchoiceEdgeNew)
      (@hsigmaPrevSelf) (@hclosedPrev) (@hnotStrongPrev) (@hnewAlternativeFails) (@hgammaDeltaNe)
      (@hsigmaComponentColor) (@hgammaPrevMissing) (@hswapGraph) (@hcomponentPrev)

private theorem helper_branch_1661.{u_1, u_2} :
    helperBranch1661Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hMP hpositive hlower sigma hsigmaProper
      hsigmaOne hsigmaStable Tstar hTnTstar hstrict heligible closureTree hclosure hTstarClosure
      hTnClosure q hqSucc hqCast hsigmaStableQ i previousProper previousOneUncolored
      previousClosed previousNotStronglyClosed noRevisiting choice seriesAlternativeFails gamma
      gammaRule secondStable secondStableProper secondStableOneUncolored secondStableRelation
      exitWitness currentColoring currentProper currentOneUncolored currentStored currentEdges
      currentKind currentVertex currentOutside currentDelta currentGamma closedExtension
      orderedExtension strictExtension htarget
  have hi : i = q := by
    exact @helper_hi_4786 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@input) (@T) (@generating) (@ett) (@hpositive) (@Tstar) (@i) (@htarget)
  subst i
  have hpeKind : ett.series.data.kind q.succ =
      some TashkinovExtensionKind.PE := by
    simpa [htarget] using currentKind
  have hprefix := TdReplacementPrefixExact G k e0 input T generating ett
    hMP hpositive hlower sigma hsigmaProper hsigmaOne
    (by simpa [hqSucc] using hsigmaStable)
  obtain ⟨sigmaPrev, hsigmaPrevProper, hsigmaPrevOne,
      hsigmaPrevStable, hsigmaPrevEq, hparallelPrev, hprefixCases⟩ := hprefix
  have hsigmaPrevStableQ : StableColoring
      (ett.series.data.tree q.succ.castSucc)
      (TashkinovStoredColors ett.series.data q.castSucc)
      (ett.series.data.coloring q.castSucc) sigmaPrev := by
    simpa [hqSucc, hqCast] using hsigmaPrevStable
  have hchoiceVertex : choice.vertex ∈ TreeSequenceVertexSet
      (ett.series.data.tree q.succ.castSucc) :=
    choice.vertexDefective.1
  have hcomponent : ∀ w,
      w ∈ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc) →
      (Sum.inl w ∈ TwoColorComponent G sigma gamma choice.color
          (Sum.inl choice.vertex) ↔ w = choice.vertex) := by
    exact @helper_hcomponent_4809 (@V) (@E) inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hMP) (@hpositive)
        (@hlower) (@sigma) (@hsigmaProper) (@hsigmaOne) (@hsigmaStable) (@Tstar) (@hqSucc)
        (@gamma) (@choice) (@currentVertex) (@currentDelta) (@currentGamma) (@hpeKind)
  obtain ⟨parallelVertex, parallelGamma, parallelDelta,
      hparallelVertex, hparallelGamma, hparallelDelta,
      hsigmaPrevSwitch⟩ := hparallelPrev (by simpa [hqSucc] using hpeKind)
  have hparallelVertexEq : parallelVertex = choice.vertex := by
    apply Option.some.inj
    exact hparallelVertex.symm.trans (by simpa [hqSucc] using currentVertex)
  have hparallelGammaEq : parallelGamma = gamma := by
    apply Option.some.inj
    exact hparallelGamma.symm.trans (by simpa [hqSucc] using currentGamma)
  have hparallelDeltaEq : parallelDelta = choice.color := by
    apply Option.some.inj
    exact hparallelDelta.symm.trans (by simpa [hqSucc] using currentDelta)
  subst parallelVertex
  subst parallelGamma
  subst parallelDelta
  have hsigmaPrevFormula : sigmaPrev =
      TwoColorComponentSwap G sigma gamma choice.color
        (Sum.inl choice.vertex) := hsigmaPrevSwitch
  have hsigmaPrevEnlarged : StableColoring
      (ett.series.data.tree q.succ.castSucc)
      (insert choice.color
        (TashkinovStoredColors ett.series.data q.castSucc))
      choice.selected sigmaPrev := by
    exact @helper_hsigmaPrevEnlarged_12232 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma)
        (@hsigmaProper) (@hsigmaOne) (@Tstar) (@hsigmaStableQ) (@gamma) (@secondStable)
        (@secondStableProper) (@secondStableOneUncolored) (@choice) (@gammaRule)
        (@secondStableRelation) (@exitWitness) (@currentColoring) (@currentProper)
        (@currentOneUncolored) (@currentStored) (@sigmaPrev) (@hchoiceVertex) (@hcomponent)
        (@hsigmaPrevFormula)
  have hdeltaBoundary : BoundaryColorEdges G choice.selected
        (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc))
        choice.color =
      BoundaryColorEdges G sigmaPrev
        (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc))
        choice.color := by
    exact @helper_hdeltaBoundary_2443 (@V) (@E) inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive)
        (@Tstar) (@choice) (@sigmaPrev) (@hsigmaPrevProper) (@hsigmaPrevOne)
        (@hsigmaPrevEnlarged)
  have hchoiceDefective : DefectiveColor G sigmaPrev
      (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc))
      choice.color := by
    exact @helper_hchoiceDefective_5167 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@Tstar) (@choice)
        (@sigmaPrev) (@hdeltaBoundary)
  have hchoiceEdgeNew : choice.edge ∈ BoundaryColorEdges G sigmaPrev
      (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc))
      choice.color := by
    exact @helper_hchoiceEdgeNew_5178 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@Tstar) (@choice)
        (@sigmaPrev) (@hdeltaBoundary)
  exact @helper_continuation_2339 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hMP) (@hpositive)
      (@hlower) (@sigma) (@hsigmaProper) (@hsigmaOne) (@hsigmaStable) (@Tstar) (@hTnTstar)
      (@hstrict) (@heligible) (@closureTree) (@hclosure) (@hTstarClosure) (@hTnClosure) (@hqSucc)
      (@hsigmaStableQ) (@gamma) (@secondStable) (@secondStableProper) (@previousProper)
      (@previousOneUncolored) (@previousClosed) (@noRevisiting) (@choice)
      (@seriesAlternativeFails) (@gammaRule) (@secondStableRelation) (@currentColoring)
      (@currentStored) (@currentEdges) (@currentKind) (@hpeKind) (@sigmaPrev) (@hsigmaPrevProper)
      (@hsigmaPrevOne) (@hprefixCases) (@hsigmaPrevStableQ) (@hchoiceVertex) (@hcomponent)
      (@hsigmaPrevFormula) (@hsigmaPrevEnlarged) (@hchoiceDefective) (@hchoiceEdgeNew)
private theorem helper_continuation_2265.{u_1, u_2} :
    helperContinuation2265Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hMP hpositive hlower sigma hsigmaProper
      hsigmaOne hsigmaStable Tstar hTnTstar hstrict heligible closureTree hclosure hTstarClosure
      hTnClosure q hqSucc adjoined previousProper previousOneUncolored noRevisiting choice
      currentStored currentEdges currentKind hseKind sigmaPrev hsigmaPrevProper hsigmaPrevOne
      hprefixCases hsigmaPrevStableQ hsigmaPrevSigma hchoiceDefective hchoiceEdgeNew
      hsigmaPrevSelf newChoice hclosedPrev hnotStrongPrev hnewAlternative
  rcases hprefixCases with hzero | hpositivePrefix
  · exact @helper_branch_12854 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
      (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@hsigmaProper) (@hsigmaOne)
      (@hsigmaStable) (@Tstar) (@hTnTstar) (@hstrict) (@heligible) (@closureTree) (@hclosure)
      (@hTstarClosure) (@hTnClosure) (@hqSucc) (@adjoined) (@previousProper)
      (@previousOneUncolored) (@choice) (@currentStored) (@currentEdges) (@currentKind)
      (@hseKind) (@sigmaPrev) (@hsigmaPrevProper) (@hsigmaPrevOne) (@hsigmaPrevStableQ)
      (@hsigmaPrevSigma) (@hchoiceDefective) (@hchoiceEdgeNew) (@hsigmaPrevSelf) (@hclosedPrev)
      (@hnotStrongPrev) (@hnewAlternative) (@hzero)
  · rcases hpositivePrefix with ⟨hroundLarge, originalPrefix, hr,
        hprefixMP, hprefixTrees, hprefixData, corr, hcorrFinalTree,
        hcorrFinalColor, hcorrMP⟩
    let replacementLast : Fin (originalPrefix.rounds + 1) :=
      Fin.last originalPrefix.rounds
    have horiginalPositive : 0 < originalPrefix.rounds := by
      rw [hr]
      omega
    let previousReplacement : Fin originalPrefix.rounds :=
      ⟨originalPrefix.rounds - 1,
        Nat.sub_lt horiginalPositive (by omega)⟩
    have hpreviousSucc : previousReplacement.succ = replacementLast := by
      apply Fin.ext
      simp [previousReplacement, replacementLast]
      omega
    have hlastMap : Fin.castLE (by omega) replacementLast =
        q.castSucc := by
      apply Fin.ext
      simp [replacementLast, q, hr]
    have hreplacementCurrentTree :
        corr.replacementSeries.data.tree replacementLast.succ =
          ett.series.data.tree q.succ.castSucc := by
      exact @helper_hreplacementCurrentTree_4014 (@V) (@E) inferInstance inferInstance
          inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@Tstar)
          (@hqSucc) (@sigmaPrev) (@originalPrefix) (@corr) (@hcorrFinalTree)
    have horiginalCurrentTree :
        originalPrefix.series.data.tree replacementLast.castSucc =
          ett.series.data.tree q.castSucc.castSucc := by
      exact @helper_horiginalCurrentTree_4022 (@V) (@E) inferInstance inferInstance inferInstance
          (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@Tstar) (@hroundLarge)
          (@originalPrefix) (@hr) (@hprefixTrees) (@horiginalPositive)
    have htreeMissingEq : TreeMissingColors
          (corr.replacementSeries.data.coloring replacementLast)
          (corr.replacementSeries.data.tree replacementLast.castSucc) =
        TreeMissingColors
          (originalPrefix.series.data.coloring replacementLast)
          (originalPrefix.series.data.tree replacementLast.castSucc) := by
      exact @helper_htreeMissingEq_4034 (@V) (@E) inferInstance inferInstance inferInstance (@G)
          (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@Tstar) (@sigmaPrev)
          (@originalPrefix) (@corr) (@horiginalPositive) (@hpreviousSucc)
    have hreplacementStored : TashkinovStoredColors
          corr.replacementSeries.data replacementLast =
        TashkinovStoredColors ett.series.data q.castSucc := by
      exact @helper_hreplacementStored_4052 (@V) (@E) inferInstance inferInstance inferInstance
          (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@Tstar) (@sigmaPrev)
          (@hroundLarge) (@originalPrefix) (@hr) (@hprefixData) (@corr) (@horiginalPositive)
          (@hlastMap) (@htreeMissingEq)
    let replacementChoice : MaximumDefectiveChoice G e0
        (corr.replacementSeries.data.tree replacementLast.succ)
        (TashkinovStoredColors corr.replacementSeries.data replacementLast)
        (corr.replacementSeries.data.coloring replacementLast) := by
      exact @helperReplacementChoice3411 (@V) (@E) inferInstance inferInstance
          inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive)
           (@previousProper) (@previousOneUncolored) (@choice) (@sigmaPrev)
          (@hsigmaPrevProper) (@hsigmaPrevOne) (@hsigmaPrevStableQ) (@hchoiceDefective)
          (@hchoiceEdgeNew) (@hsigmaPrevSelf) (@originalPrefix) (@corr) (@hcorrFinalColor)
          (@hreplacementCurrentTree) (@hreplacementStored)
    have hnoRevisitingReplacement : ¬ Nonempty
        (RevisitingExtensionCertificate corr.replacementSeries.data
          replacementLast) := by
      exact @helper_hnoRevisitingReplacement_4104 (@V) (@E) inferInstance inferInstance
           inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hMP)
          (@hpositive) (@hlower) (@Tstar) (@previousProper) (@previousOneUncolored)
          (@noRevisiting) (@sigmaPrev) (@hsigmaPrevProper) (@hsigmaPrevOne) (@hsigmaPrevStableQ)
          (@hroundLarge) (@originalPrefix) (@hr) (@hprefixMP) (@hprefixTrees) (@hprefixData)
          (@corr) (@hcorrFinalTree) (@hcorrFinalColor) (@hcorrMP)
    have hnewAlternativeReplacement : ∀ pi : PartialEdgeColoring E k,
        IsProperEdgeColoring G pi → IsOneEdgeUncolored pi e0 →
        StableColoring
          (corr.replacementSeries.data.tree replacementLast.succ)
          (insert replacementChoice.color
            (TashkinovStoredColors corr.replacementSeries.data
              replacementLast)) replacementChoice.selected pi →
        Disjoint (MissingColors G pi replacementChoice.otherEndpoint)
          (TreeMissingColors pi
            (corr.replacementSeries.data.tree replacementLast.succ)) := by
      exact @helper_hnewAlternativeReplacement_4116 (@V) (@E) inferInstance inferInstance
          inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive)
          (@previousProper) (@previousOneUncolored) (@choice) (@sigmaPrev) (@hsigmaPrevProper)
          (@hsigmaPrevOne) (@hsigmaPrevStableQ) (@hchoiceDefective) (@hchoiceEdgeNew)
          (@hsigmaPrevSelf) (@hnewAlternative) (@originalPrefix) (@corr) (@hcorrFinalColor)
          (@hreplacementCurrentTree) (@hreplacementStored)
    rcases heligible with hparallel | hsimple
    · have hbad := hparallel.1.symm.trans
        (by simpa [hqSucc] using hseKind)
      cases hbad
    · exact @helper_branch_1497 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@hsigmaProper)
        (@hsigmaOne) (@hsigmaStable) (@Tstar) (@hTnTstar) (@hstrict) (@closureTree) (@hclosure)
        (@hTstarClosure) (@hTnClosure) (@hqSucc) (@adjoined) (@previousProper)
        (@previousOneUncolored) (@choice) (@currentStored) (@currentEdges) (@currentKind)
        (@sigmaPrev) (@hsigmaPrevProper) (@hsigmaPrevOne) (@hsigmaPrevStableQ) (@hsigmaPrevSigma)
        (@hchoiceDefective) (@hchoiceEdgeNew) (@hsigmaPrevSelf) (@hclosedPrev) (@hnotStrongPrev)
        (@hroundLarge) (@originalPrefix) (@hr) (@hprefixTrees) (@hprefixData) (@corr)
        (@hcorrFinalColor) (@horiginalPositive) (@hreplacementCurrentTree) (@hreplacementStored)
        (@hnoRevisitingReplacement) (@hnewAlternativeReplacement) (@hsimple)

private theorem helper_branch_2237.{u_1, u_2} :
    helperBranch2237Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hMP hpositive hlower sigma hsigmaProper
      hsigmaOne hsigmaStable Tstar hTnTstar hstrict heligible closureTree hclosure hTstarClosure
      hTnClosure q hqSucc hqCast hsigmaStableQ i previousProper previousOneUncolored
      previousClosed previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex currentOutside
      currentDelta currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension htarget
  have hi : i = q := by
    exact @helper_hi_3469 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@input) (@T) (@generating) (@ett) (@hpositive) (@Tstar) (@i) (@htarget)
  subst i
  have hseKind : ett.series.data.kind q.succ =
      some TashkinovExtensionKind.SE := by
    simpa [htarget] using currentKind
  have hprefix := TdReplacementPrefixExact G k e0 input T generating ett
    hMP hpositive hlower sigma hsigmaProper hsigmaOne
    (by simpa [hqSucc] using hsigmaStable)
  obtain ⟨sigmaPrev, hsigmaPrevProper, hsigmaPrevOne,
      hsigmaPrevStable, hsigmaPrevEq, hparallelPrev, hprefixCases⟩ := hprefix
  have hsigmaPrevStableQ : StableColoring
      (ett.series.data.tree q.succ.castSucc)
      (TashkinovStoredColors ett.series.data q.castSucc)
      (ett.series.data.coloring q.castSucc) sigmaPrev := by
    simpa [hqSucc, hqCast] using hsigmaPrevStable
  have hsigmaPrevSigma : sigmaPrev = sigma :=
    hsigmaPrevEq (Or.inl (by simpa [hqSucc] using hseKind))
  have hpreviousControl :
      TreeMissingColors (ett.series.data.coloring q.castSucc)
            (ett.series.data.tree q.succ.castSucc) ∪
          TashkinovStoredColors ett.series.data q.castSucc ⊆
        TreeMissingColors (ett.series.data.coloring q.succ)
            (ett.series.data.tree q.succ.castSucc) ∪
          TashkinovStoredColors ett.series.data q.succ :=
    (HkuMissingStoredMonotone G k ett.rounds e0 input ett.series q).1
  have hdeltaCurrentControl : choice.color ∈
      TreeMissingColors (ett.series.data.coloring q.succ)
            (ett.series.data.tree q.succ.castSucc) ∪
          TashkinovStoredColors ett.series.data q.succ := by
    exact @helper_hdeltaCurrentControl_3499 (@V) (@E) inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@Tstar) (@choice)
        (@currentStored)
  have henlargedControl :
      TreeMissingColors choice.selected
            (ett.series.data.tree q.succ.castSucc) ∪
          insert choice.color
            (TashkinovStoredColors ett.series.data q.castSucc) ⊆
        TreeMissingColors (ett.series.data.coloring q.succ)
            (ett.series.data.tree q.succ.castSucc) ∪
          TashkinovStoredColors ett.series.data q.succ := by
    exact @helper_henlargedControl_3516 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@Tstar) (@choice)
        (@currentColoring) (@hpreviousControl) (@hdeltaCurrentControl)
  have hsigmaPrevEnlarged : StableColoring
      (ett.series.data.tree q.succ.castSucc)
      (insert choice.color
        (TashkinovStoredColors ett.series.data q.castSucc))
      choice.selected sigmaPrev := by
    exact @helper_hsigmaPrevEnlarged_3532 (@V) (@E) inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@Tstar)
        (@hsigmaStableQ) (@choice) (@currentColoring) (@sigmaPrev) (@hsigmaPrevSigma)
        (@henlargedControl)
  have hdeltaBoundary : BoundaryColorEdges G choice.selected
        (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc))
        choice.color =
      BoundaryColorEdges G sigmaPrev
        (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc))
        choice.color := by
    exact @helper_hdeltaBoundary_254 (@V) (@E) inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive)
        (@Tstar) (@choice) (@sigmaPrev) (@hsigmaPrevProper) (@hsigmaPrevOne)
        (@hsigmaPrevEnlarged)
  have hchoiceDefective : DefectiveColor G sigmaPrev
      (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc))
      choice.color := by
    exact @helper_hchoiceDefective_3555 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@Tstar) (@choice)
        (@sigmaPrev) (@hdeltaBoundary)
  have hchoiceEdgeNew : choice.edge ∈ BoundaryColorEdges G sigmaPrev
      (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc))
      choice.color := by
    exact @helper_hchoiceEdgeNew_3566 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@Tstar) (@choice)
        (@sigmaPrev) (@hdeltaBoundary)
  have hsigmaPrevSelf : StableColoring
      (ett.series.data.tree q.succ.castSucc)
      (TashkinovStoredColors ett.series.data q.castSucc)
      sigmaPrev sigmaPrev := by
    exact (sc2 G e0 (ett.series.data.tree q.succ.castSucc)
      (TashkinovStoredColors ett.series.data q.castSucc)).refl
      ⟨sigmaPrev, hsigmaPrevProper, hsigmaPrevOne⟩
  let newChoice : MaximumDefectiveChoice G e0
      (ett.series.data.tree q.succ.castSucc)
      (TashkinovStoredColors ett.series.data q.castSucc) sigmaPrev := by
    exact @helperNewChoice2409 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@previousProper)
        (@previousOneUncolored) (@choice) (@sigmaPrev) (@hsigmaPrevProper) (@hsigmaPrevOne)
        (@hsigmaPrevStableQ) (@hchoiceDefective) (@hchoiceEdgeNew) (@hsigmaPrevSelf)
  have hclosedPrev : ColoredVertexSetClosed G sigmaPrev
      (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) := by
    exact @helper_hclosedPrev_356 (@V) (@E) inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive)
        (@Tstar) (@previousProper) (@previousOneUncolored) (@previousClosed) (@sigmaPrev)
        (@hsigmaPrevProper) (@hsigmaPrevOne) (@hsigmaPrevStableQ)
  have hnotStrongPrev : ¬ ColoredVertexSetStronglyClosed G sigmaPrev
      (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) := by
    exact @helper_hnotStrongPrev_3595 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@Tstar) (@choice)
        (@sigmaPrev) (@hchoiceDefective)
  have hnewAlternative : ∀ pi : PartialEdgeColoring E k,
      IsProperEdgeColoring G pi → IsOneEdgeUncolored pi e0 →
      StableColoring (ett.series.data.tree q.succ.castSucc)
        (insert newChoice.color
          (TashkinovStoredColors ett.series.data q.castSucc))
        newChoice.selected pi →
      Disjoint (MissingColors G pi newChoice.otherEndpoint)
        (TreeMissingColors pi
          (ett.series.data.tree q.succ.castSucc)) := by
    exact @helper_hnewAlternative_3611 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@Tstar) (@previousProper)
        (@previousOneUncolored) (@choice) (@seriesAlternative) (@sigmaPrev) (@hsigmaPrevProper)
        (@hsigmaPrevOne) (@hsigmaPrevStableQ) (@hsigmaPrevEnlarged) (@hchoiceDefective)
        (@hchoiceEdgeNew) (@hsigmaPrevSelf)
  exact @helper_continuation_2265 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hMP) (@hpositive)
      (@hlower) (@sigma) (@hsigmaProper) (@hsigmaOne) (@hsigmaStable) (@Tstar) (@hTnTstar)
      (@hstrict) (@heligible) (@closureTree) (@hclosure) (@hTstarClosure) (@hTnClosure) (@hqSucc)
      (@adjoined) (@previousProper) (@previousOneUncolored) (@noRevisiting) (@choice)
      (@currentStored) (@currentEdges) (@currentKind) (@hseKind) (@sigmaPrev) (@hsigmaPrevProper)
      (@hsigmaPrevOne) (@hprefixCases) (@hsigmaPrevStableQ) (@hsigmaPrevSigma)
      (@hchoiceDefective) (@hchoiceEdgeNew) (@hsigmaPrevSelf) (@hclosedPrev) (@hnotStrongPrev)
      (@hnewAlternative)
theorem TdTerminalSEPERebuild {V E : Type*} [Fintype V] [Fintype E]
     [DecidableEq E] (G : LooplessMultigraph V E)
    (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
    (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hMP : MaximumProperty ett)
    (hpositive : 0 < ett.rounds)
    (hlower : LowerRoundInductionHypothesis G k e0 ett.rounds) :
    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
    (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
      ett.series.data.kind n = some TashkinovExtensionKind.PE) →
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc
    ∀ sigma : PartialEdgeColoring E k,
      IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
      StableColoring Tn
        (TashkinovStoredColors ett.series.data n)
        (ett.series.data.coloring n) sigma →
      ModColoring ett sigma := by
  classical
  dsimp
  intro hterminal sigma hsigmaProper hsigmaOne hsigmaStable
  refine ⟨hsigmaProper, hsigmaOne, ?_⟩
  intro Tstar hTnTstar hstrict heligible
  obtain ⟨closureTree, hclosure⟩ := TashkinovClosureExists sigma Tstar
  have hTstarClosure : TreeSequenceInitialSegment Tstar closureTree :=
    TashkinovAugmentationSequenceInitialSegment sigma Tstar closureTree hclosure.1
  have hTnClosure : TreeSequenceInitialSegment
      (ett.series.data.tree (Fin.last ett.rounds).castSucc) closureTree := by
    exact @helper_hTnClosure_112 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@Tstar) (@hTnTstar) (@closureTree)
        (@hTstarClosure)
  let q : Fin ett.rounds :=
    ⟨ett.rounds - 1,
      Nat.sub_lt (Nat.zero_lt_of_lt hpositive) (by omega)⟩
  have hqSucc : q.succ = Fin.last ett.rounds := by
    apply Fin.ext
    simp [q]
    omega
  have hqCast : q.castSucc =
      (⟨ett.rounds - 1, by omega⟩ : Fin (ett.rounds + 1)) := by
    apply Fin.ext
    rfl
  have hsigmaStableQ : StableColoring
      (ett.series.data.tree q.succ.castSucc)
      (TashkinovStoredColors ett.series.data q.succ)
      (ett.series.data.coloring q.succ) sigma := by
    simpa [hqSucc] using hsigmaStable
  have hfinalStep := ett.series.certified (Fin.last ett.rounds)
  generalize htarget : (Fin.last ett.rounds : Fin (ett.rounds + 1)) =
    target at hfinalStep
  cases hfinalStep with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
      have hv := congrArg Fin.val htarget
      simp at hv
      omega
  | RE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
          exact @helper_branch_3453 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
              (@e0) (@input) (@T) (@generating) (@ett) (@hterminal) (@sigma) (@Tstar) (@i)
              (@currentKind) (@htarget)
  | SE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
          exact @helper_branch_2237 (@V) (@E) inferInstance inferInstance inferInstance
              inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hMP)
              (@hpositive) (@hlower) (@sigma) (@hsigmaProper) (@hsigmaOne) (@hsigmaStable)
              (@Tstar) (@hTnTstar) (@hstrict) (@heligible) (@closureTree) (@hclosure)
              (@hTstarClosure) (@hTnClosure) (@hqSucc) (@hqCast) (@hsigmaStableQ) (@i)
              (@previousProper) (@previousOneUncolored) (@previousClosed)
              (@previousNotStronglyClosed) (@noRevisiting) (@choice) (@seriesAlternative)
              (@currentColoring) (@currentStored) (@currentEdges) (@currentKind) (@currentVertex)
              (@currentOutside) (@currentDelta) (@currentGamma) (@adjoined) (@adjoinedExactly)
              (@closedExtension) (@orderedExtension) (@strictExtension) (@htarget)
  | PE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper secondStableOneUncolored
      secondStableRelation exitWitness currentColoring currentProper
      currentOneUncolored currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma closedExtension orderedExtension
      strictExtension =>
          exact @helper_branch_1661 (@V) (@E) inferInstance inferInstance inferInstance
              inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hMP)
              (@hpositive) (@hlower) (@sigma) (@hsigmaProper) (@hsigmaOne) (@hsigmaStable)
              (@Tstar) (@hTnTstar) (@hstrict) (@heligible) (@closureTree) (@hclosure)
              (@hTstarClosure) (@hTnClosure) (@hqSucc) (@hqCast) (@hsigmaStableQ) (@i)
              (@previousProper) (@previousOneUncolored) (@previousClosed)
              (@previousNotStronglyClosed) (@noRevisiting) (@choice) (@seriesAlternativeFails)
              (@gamma) (@gammaRule) (@secondStable) (@secondStableProper)
              (@secondStableOneUncolored) (@secondStableRelation) (@exitWitness)
              (@currentColoring) (@currentProper) (@currentOneUncolored) (@currentStored)
              (@currentEdges) (@currentKind) (@currentVertex) (@currentOutside) (@currentDelta)
              (@currentGamma) (@closedExtension) (@orderedExtension) (@strictExtension) (@htarget)
end GoldbergSeymour

end
