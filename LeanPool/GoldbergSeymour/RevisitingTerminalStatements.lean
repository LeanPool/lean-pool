/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/

module

public import LeanPool.GoldbergSeymour.RevisitingTerminalPreparation
public import LeanPool.GoldbergSeymour.TashkinovSeriesDataAppend

/-!
# Dependent statements for a revisiting terminal rebuild

Supporting material for the Goldberg–Seymour revisiting construction.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
-/

@[expose] public section

namespace GoldbergSeymour.TerminalRebuild

open scoped Sym2

/-- Dependent contract shared by the revisiting terminal reconstruction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev terminalLastStepStatement.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [ DecidableEq V]
   [inst_3 : DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds)
   (sigma : PartialEdgeColoring E k) (_ : IsProperEdgeColoring G sigma)
   (_ : IsOneEdgeUncolored sigma e0) (Tstar : TreeSequence G e0) (fstar : E)
   (seed : TreeSequence G e0)
   (_ : TreeSequenceAdjoinEdge (ett.series.data.tree (Fin.last ett.rounds).castSucc) fstar seed)
   (closureTree : TreeSequence G e0) (_ : TashkinovClosure sigma seed closureTree)
   (_ :
    TreeSequenceInitialSegment (ett.series.data.tree (Fin.last ett.rounds).castSucc) closureTree),
   let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin ett.rounds);
   ∀ (_ : q.succ = Fin.last ett.rounds)
    (hqCast : q.castSucc = (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin (ett.rounds + (1 : ℕ))))
    (_ : TreeSequence G e0) (_ : IsProperEdgeColoring G (ett.series.data.coloring q.castSucc))
    (_ : IsOneEdgeUncolored (ett.series.data.coloring q.castSucc) e0)
    (_ :
     ColoredVertexSetClosed G (ett.series.data.coloring q.castSucc)
      (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)))
    (available : RevisitingExtensionCertificate ett.series.data q.castSucc)
    (hroundLarge : (1 : ℕ) < ett.rounds)
    (originalPrefix :
     ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin (ett.rounds + (1 : ℕ)))))
    (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ))
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
     CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigma
      (ett.series.data.tree (Fin.last ett.rounds).castSucc))
    (_ :
     corr.replacementSeries.data.tree (Fin.last (originalPrefix.rounds + (1 : ℕ))) =
      ett.series.data.tree (Fin.last ett.rounds).castSucc)
    (earlierPrefixBound : (↑available.earlier : ℕ) < originalPrefix.rounds + (1 : ℕ)),
    let earlierPrefix : Fin (originalPrefix.rounds + (1 : ℕ)) :=
     (⟨(↑available.earlier : ℕ), earlierPrefixBound⟩ : Fin (originalPrefix.rounds + (1 : ℕ)));
    ∀ (hearlierMap : Fin.castLE (by omega) earlierPrefix = available.earlier)
     (hearlierPositive : (0 : ℕ) < (↑earlierPrefix : ℕ))
     (hreplacementEarlierKind :
      corr.replacementSeries.data.kind earlierPrefix = some TashkinovExtensionKind.PE)
     (oldi : Fin ett.rounds)
     (oldChoice :
      MaximumDefectiveChoice G e0 (ett.series.data.tree oldi.succ.castSucc)
       (TashkinovStoredColors ett.series.data oldi.castSucc)
       (ett.series.data.coloring oldi.castSucc))
     (oldGamma : Fin k) (_ : available.earlier = oldi.succ) (newi : Fin originalPrefix.rounds)
     (newChoice :
      MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree newi.succ.castSucc)
       (TashkinovStoredColors corr.replacementSeries.data newi.castSucc)
       (corr.replacementSeries.data.coloring newi.castSucc))
     (newGamma_1 : Fin k)
     (newCurrentDelta : corr.replacementSeries.data.delta newi.succ = some newChoice.color)
     (newCurrentGamma : corr.replacementSeries.data.gamma newi.succ = some newGamma_1)
     (hnewIndex : newi.succ = earlierPrefix)
     (htree :
      corr.replacementSeries.data.tree newi.succ.castSucc =
       ett.series.data.tree oldi.succ.castSucc),
     let oldChoiceOnNew :
      MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree newi.succ.castSucc)
       (TashkinovStoredColors ett.series.data oldi.castSucc)
       (ett.series.data.coloring oldi.castSucc) :=
      transportDefectiveChoice (Eq.symm htree) oldChoice;
     ∀ (holdColorCast : oldChoiceOnNew.color = oldChoice.color)
      (_ :
       s(oldChoiceOnNew.vertex, oldChoiceOnNew.otherEndpoint) =
        s(newChoice.vertex, newChoice.otherEndpoint))
      (holdColorNe : oldGamma ≠ oldChoice.color) (hnewColorNe : newGamma_1 ≠ newChoice.color)
      (hidentifiedDelta : newChoice.color = oldChoiceOnNew.color)
      (hidentifiedGamma : newGamma_1 = oldGamma)
      (holdDeltaAvailable : oldChoice.color = available.delta)
      (holdGammaAvailable : oldGamma = available.gamma)
      (hnewDeltaAvailable : newChoice.color = available.delta)
      (hnewGammaAvailable : newGamma_1 = available.gamma),
      let replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last originalPrefix.rounds;
      ∀ (hreplacementLastMap : Fin.castLE (by omega) replacementLast = q.castSucc)
       (hgammaDeltaNe : available.gamma ≠ available.delta)
       (_ :
        StableColoring (ett.series.data.tree q.succ.castSucc)
         (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)
         sigma),
       let sigmaReturnGraph : SimpleGraph (V ⊕ E) :=
        TwoColorIncidenceGraph G sigma available.gamma available.delta;
       ∀
        (returnEdgeTransfer : ∀ edge ∈ available.returnPath.edges, edge ∈ sigmaReturnGraph.edgeSet),
        let sigmaReturnPath :
         sigmaReturnGraph.Walk (Sum.inr available.edge) (Sum.inl available.returnVertex) :=
         available.returnPath.transfer sigmaReturnGraph returnEdgeTransfer;
        ∀ (hsigmaReturnIsPath : sigmaReturnPath.IsPath)
         (hsigmaReturnSupport :
          ∀ (z : V ⊕ E), z ∈ sigmaReturnPath.support ↔ z ∈ available.returnPath.support)
         (hreturnInNewEarlier :
          available.returnVertex ∈
           TreeSequenceVertexSet (corr.replacementSeries.data.tree earlierPrefix.castSucc))
         (replacementCycle : TwoColorCycle G sigma available.gamma available.delta)
         (hcycleFull :
          ∀ (x : V ⊕ E),
           x ∈ replacementCycle.walk.support ↔
            x ∈ TwoColorComponent G sigma available.gamma available.delta (Sum.inr available.edge))
         (_ :
          ColoredVertexSetClosed G sigma
           (TreeSequenceVertexSet (ett.series.data.tree (Fin.last ett.rounds).castSucc)))
         (hreplacementCurrentTree :
          have replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) :=
           Fin.last originalPrefix.rounds;
          corr.replacementSeries.data.tree replacementLast.succ =
           ett.series.data.tree (Fin.last ett.rounds).castSucc)
         (havailableCurrentTree :
          ett.series.data.tree q.castSucc.succ =
           ett.series.data.tree (Fin.last ett.rounds).castSucc),
         let currentTree : Finset V := TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc);
         ∀ (hreturnCycle : Sum.inl available.returnVertex ∈ replacementCycle.walk.support)
          (houtsideCycle : Sum.inl available.outsideEndpoint ∈ replacementCycle.walk.support),
          let rootedCycle :
           (TwoColorIncidenceGraph G sigma available.gamma available.delta).Walk
            (Sum.inl available.returnVertex) (Sum.inl available.returnVertex) :=
           replacementCycle.walk.rotate (Sum.inl available.returnVertex) hreturnCycle;
          let outsideIndices : Finset (Fin (rootedCycle.length + (1 : ℕ))) :=
           ({i : Fin (rootedCycle.length + (1 : ℕ)) |
             ∃ (v : V), rootedCycle.getVert (↑i : ℕ) = Sum.inl v ∧ v ∉ currentTree} :
            Finset (Fin (rootedCycle.length + (1 : ℕ))));
          ∀ (outsideIndicesNonempty : outsideIndices.Nonempty),
           let firstOutside : Fin (rootedCycle.length + (1 : ℕ)) :=
            outsideIndices.min' outsideIndicesNonempty;
           ∀ (firstOutsideNotOne : (↑firstOutside : ℕ) ≠ (1 : ℕ))
            (firstOutsideAtLeastTwo : (2 : ℕ) ≤ (↑firstOutside : ℕ))
            (firstCrossingIndex : (↑firstOutside : ℕ) - (1 : ℕ) + (1 : ℕ) = (↑firstOutside : ℕ))
            (beforeFirstCrossingIndex :
             (↑firstOutside : ℕ) - (2 : ℕ) + (1 : ℕ) = (↑firstOutside : ℕ) - (1 : ℕ)),
            let laterInsideIndices : Finset (Fin (rootedCycle.length + (1 : ℕ))) :=
             ({idx : Fin (rootedCycle.length + (1 : ℕ)) |
               (↑firstOutside : ℕ) < (↑idx : ℕ) ∧
                ∃ (v : V), rootedCycle.getVert (↑idx : ℕ) = Sum.inl v ∧ v ∈ currentTree} :
              Finset (Fin (rootedCycle.length + (1 : ℕ))));
            ∀ (laterInsideNonempty : laterInsideIndices.Nonempty),
             let firstReturn : Fin (rootedCycle.length + (1 : ℕ)) :=
              laterInsideIndices.min' laterInsideNonempty;
             ∀ (hreturnNotNext : (↑firstReturn : ℕ) ≠ (↑firstOutside : ℕ) + (1 : ℕ))
              (hreturnGap : (↑firstOutside : ℕ) + (2 : ℕ) ≤ (↑firstReturn : ℕ))
              (returnCrossingIndex : (↑firstReturn : ℕ) - (1 : ℕ) + (1 : ℕ) = (↑firstReturn : ℕ))
              (beforeReturnCrossingIndex :
               (↑firstReturn : ℕ) - (2 : ℕ) + (1 : ℕ) = (↑firstReturn : ℕ) - (1 : ℕ))
              (_ : ¬ColoredVertexSetStronglyClosed G sigma currentTree)
              (hreplacementColor : corr.replacementSeries.data.coloring replacementLast = sigma),
              let castReturnWalk :
               (phi psi : PartialEdgeColoring E k) →
                (hphi : phi = psi) →
                 (P :
                   (TwoColorIncidenceGraph G psi available.gamma available.delta).Walk
                    (Sum.inr available.edge) (Sum.inl available.returnVertex)) →
                  (TwoColorIncidenceGraph G phi available.gamma available.delta).Walk
                   (Sum.inr available.edge) (Sum.inl available.returnVertex) :=
               fun (phi psi : PartialEdgeColoring E k) (hphi : phi = psi)
                (P :
                 (TwoColorIncidenceGraph G psi available.gamma available.delta).Walk
                  (Sum.inr available.edge) (Sum.inl available.returnVertex)) ↦
               @Eq.ndrec (PartialEdgeColoring E k) phi
                (fun (psi : PartialEdgeColoring E k) ↦
                 (P :
                   @SimpleGraph.Walk (Sum V E)
                    (@TwoColorIncidenceGraph V E G k psi
                     (@RevisitingExtensionCertificate.gamma V E inst inst_1 G k
                      (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
                       generating ett)
                      e0
                      (@TashkinovSeries.data V E inst inst_1 inst_3 G k
                       (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
                        generating ett)
                       e0 input
                       (@ExtendedTashkinovTree.series V E inst inst_1 inst_3 G k e0 input T
                        generating ett))
                      (@Fin.castSucc
                       (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
                        generating ett)
                       q)
                      available)
                     (@RevisitingExtensionCertificate.delta V E inst inst_1 G k
                      (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
                       generating ett)
                      e0
                      (@TashkinovSeries.data V E inst inst_1 inst_3 G k
                       (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
                        generating ett)
                       e0 input
                       (@ExtendedTashkinovTree.series V E inst inst_1 inst_3 G k e0 input T
                        generating ett))
                      (@Fin.castSucc
                       (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
                        generating ett)
                       q)
                      available))
                    (@Sum.inr V E
                     (@RevisitingExtensionCertificate.edge V E inst inst_1 G k
                      (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
                       generating ett)
                      e0
                      (@TashkinovSeries.data V E inst inst_1 inst_3 G k
                       (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
                        generating ett)
                       e0 input
                       (@ExtendedTashkinovTree.series V E inst inst_1 inst_3 G k e0 input T
                        generating ett))
                      (@Fin.castSucc
                       (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
                        generating ett)
                       q)
                      available))
                    (@Sum.inl V E
                     (@RevisitingExtensionCertificate.returnVertex V E inst inst_1 G k
                      (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
                       generating ett)
                      e0
                      (@TashkinovSeries.data V E inst inst_1 inst_3 G k
                       (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
                        generating ett)
                       e0 input
                       (@ExtendedTashkinovTree.series V E inst inst_1 inst_3 G k e0 input T
                        generating ett))
                      (@Fin.castSucc
                       (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
                        generating ett)
                       q)
                      available))) →
                  @SimpleGraph.Walk (Sum V E)
                   (@TwoColorIncidenceGraph V E G k phi
                    (@RevisitingExtensionCertificate.gamma V E inst inst_1 G k
                     (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T generating
                      ett)
                     e0
                     (@TashkinovSeries.data V E inst inst_1 inst_3 G k
                      (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
                       generating ett)
                      e0 input
                      (@ExtendedTashkinovTree.series V E inst inst_1 inst_3 G k e0 input T
                       generating ett))
                     (@Fin.castSucc
                      (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
                       generating ett)
                      q)
                     available)
                    (@RevisitingExtensionCertificate.delta V E inst inst_1 G k
                     (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T generating
                      ett)
                     e0
                     (@TashkinovSeries.data V E inst inst_1 inst_3 G k
                      (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
                       generating ett)
                      e0 input
                      (@ExtendedTashkinovTree.series V E inst inst_1 inst_3 G k e0 input T
                       generating ett))
                     (@Fin.castSucc
                      (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
                       generating ett)
                      q)
                     available))
                   (@Sum.inr V E
                    (@RevisitingExtensionCertificate.edge V E inst inst_1 G k
                     (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T generating
                      ett)
                     e0
                     (@TashkinovSeries.data V E inst inst_1 inst_3 G k
                      (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
                       generating ett)
                      e0 input
                      (@ExtendedTashkinovTree.series V E inst inst_1 inst_3 G k e0 input T
                       generating ett))
                     (@Fin.castSucc
                      (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
                       generating ett)
                      q)
                     available))
                   (@Sum.inl V E
                    (@RevisitingExtensionCertificate.returnVertex V E inst inst_1 G k
                     (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T generating
                      ett)
                     e0
                     (@TashkinovSeries.data V E inst inst_1 inst_3 G k
                      (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
                       generating ett)
                      e0 input
                      (@ExtendedTashkinovTree.series V E inst inst_1 inst_3 G k e0 input T
                       generating ett))
                     (@Fin.castSucc
                      (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
                       generating ett)
                      q)
                     available)))
                (fun
                  (P :
                   @SimpleGraph.Walk (Sum V E)
                    (@TwoColorIncidenceGraph V E G k phi
                     (@RevisitingExtensionCertificate.gamma V E inst inst_1 G k
                      (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
                       generating ett)
                      e0
                      (@TashkinovSeries.data V E inst inst_1 inst_3 G k
                       (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
                        generating ett)
                       e0 input
                       (@ExtendedTashkinovTree.series V E inst inst_1 inst_3 G k e0 input T
                        generating ett))
                      (@Fin.castSucc
                       (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
                        generating ett)
                       q)
                      available)
                     (@RevisitingExtensionCertificate.delta V E inst inst_1 G k
                      (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
                       generating ett)
                      e0
                      (@TashkinovSeries.data V E inst inst_1 inst_3 G k
                       (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
                        generating ett)
                       e0 input
                       (@ExtendedTashkinovTree.series V E inst inst_1 inst_3 G k e0 input T
                        generating ett))
                      (@Fin.castSucc
                       (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
                        generating ett)
                       q)
                      available))
                    (@Sum.inr V E
                     (@RevisitingExtensionCertificate.edge V E inst inst_1 G k
                      (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
                       generating ett)
                      e0
                      (@TashkinovSeries.data V E inst inst_1 inst_3 G k
                       (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
                        generating ett)
                       e0 input
                       (@ExtendedTashkinovTree.series V E inst inst_1 inst_3 G k e0 input T
                        generating ett))
                      (@Fin.castSucc
                       (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
                        generating ett)
                       q)
                      available))
                    (@Sum.inl V E
                     (@RevisitingExtensionCertificate.returnVertex V E inst inst_1 G k
                      (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
                       generating ett)
                      e0
                      (@TashkinovSeries.data V E inst inst_1 inst_3 G k
                       (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
                        generating ett)
                       e0 input
                       (@ExtendedTashkinovTree.series V E inst inst_1 inst_3 G k e0 input T
                        generating ett))
                      (@Fin.castSucc
                       (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
                        generating ett)
                       q)
                      available))) ↦
                 P)
                psi hphi P;
              ∀
               (castReturnWalkIsPath :
                ∀ (phi psi : PartialEdgeColoring E k) (hphi : phi = psi)
                 (P :
                  (TwoColorIncidenceGraph G psi available.gamma available.delta).Walk
                   (Sum.inr available.edge) (Sum.inl available.returnVertex)),
                 P.IsPath → (castReturnWalk phi psi hphi P).IsPath)
               (castReturnWalkSupport :
                ∀ (phi psi : PartialEdgeColoring E k) (hphi : phi = psi)
                 (P :
                  (TwoColorIncidenceGraph G psi available.gamma available.delta).Walk
                   (Sum.inr available.edge) (Sum.inl available.returnVertex))
                 (z : V ⊕ E), z ∈ (castReturnWalk phi psi hphi P).support ↔ z ∈ P.support),
               let castCycle :
                (phi psi : PartialEdgeColoring E k) →
                 (hphi : phi = psi) →
                  (C : TwoColorCycle G psi available.gamma available.delta) →
                   TwoColorCycle G phi available.gamma available.delta :=
                fun (phi psi : PartialEdgeColoring E k) (hphi : phi = psi)
                 (C : TwoColorCycle G psi available.gamma available.delta) ↦
                @Eq.ndrec (PartialEdgeColoring E k) phi
                 (fun (psi : PartialEdgeColoring E k) ↦
                  (C :
                    @TwoColorCycle V E G k psi
                     (@RevisitingExtensionCertificate.gamma V E inst inst_1 G k
                      (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
                       generating ett)
                      e0
                      (@TashkinovSeries.data V E inst inst_1 inst_3 G k
                       (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
                        generating ett)
                       e0 input
                       (@ExtendedTashkinovTree.series V E inst inst_1 inst_3 G k e0 input T
                        generating ett))
                      (@Fin.castSucc
                       (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
                        generating ett)
                       q)
                      available)
                     (@RevisitingExtensionCertificate.delta V E inst inst_1 G k
                      (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
                       generating ett)
                      e0
                      (@TashkinovSeries.data V E inst inst_1 inst_3 G k
                       (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
                        generating ett)
                       e0 input
                       (@ExtendedTashkinovTree.series V E inst inst_1 inst_3 G k e0 input T
                        generating ett))
                      (@Fin.castSucc
                       (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
                        generating ett)
                       q)
                      available)) →
                   @TwoColorCycle V E G k phi
                    (@RevisitingExtensionCertificate.gamma V E inst inst_1 G k
                     (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T generating
                      ett)
                     e0
                     (@TashkinovSeries.data V E inst inst_1 inst_3 G k
                      (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
                       generating ett)
                      e0 input
                      (@ExtendedTashkinovTree.series V E inst inst_1 inst_3 G k e0 input T
                       generating ett))
                     (@Fin.castSucc
                      (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
                       generating ett)
                      q)
                     available)
                    (@RevisitingExtensionCertificate.delta V E inst inst_1 G k
                     (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T generating
                      ett)
                     e0
                     (@TashkinovSeries.data V E inst inst_1 inst_3 G k
                      (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
                       generating ett)
                      e0 input
                      (@ExtendedTashkinovTree.series V E inst inst_1 inst_3 G k e0 input T
                       generating ett))
                     (@Fin.castSucc
                      (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
                       generating ett)
                      q)
                     available))
                 (fun
                   (C :
                    @TwoColorCycle V E G k phi
                     (@RevisitingExtensionCertificate.gamma V E inst inst_1 G k
                      (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
                       generating ett)
                      e0
                      (@TashkinovSeries.data V E inst inst_1 inst_3 G k
                       (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
                        generating ett)
                       e0 input
                       (@ExtendedTashkinovTree.series V E inst inst_1 inst_3 G k e0 input T
                        generating ett))
                      (@Fin.castSucc
                       (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
                        generating ett)
                       q)
                      available)
                     (@RevisitingExtensionCertificate.delta V E inst inst_1 G k
                      (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
                       generating ett)
                      e0
                      (@TashkinovSeries.data V E inst inst_1 inst_3 G k
                       (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
                        generating ett)
                       e0 input
                       (@ExtendedTashkinovTree.series V E inst inst_1 inst_3 G k e0 input T
                        generating ett))
                      (@Fin.castSucc
                       (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
                        generating ett)
                       q)
                      available)) ↦
                  C)
                 psi hphi C;
               ∀
                (castCycleSupport :
                 ∀ (phi psi : PartialEdgeColoring E k) (hphi : phi = psi)
                  (C : TwoColorCycle G psi available.gamma available.delta) (z : V ⊕ E),
                  z ∈ (castCycle phi psi hphi C).walk.support ↔ z ∈ C.walk.support),
                let replacementCycleForPrefix :
                 TwoColorCycle G (corr.replacementSeries.data.coloring replacementLast)
                  available.gamma available.delta :=
                 castCycle (corr.replacementSeries.data.coloring replacementLast) sigma
                  hreplacementColor replacementCycle;
                let replacementReturnPath :
                 (TwoColorIncidenceGraph G (corr.replacementSeries.data.coloring replacementLast)
                    available.gamma available.delta).Walk
                  (Sum.inr available.edge) (Sum.inl available.returnVertex) :=
                 castReturnWalk (corr.replacementSeries.data.coloring replacementLast) sigma
                  hreplacementColor sigmaReturnPath;
                ∀
                 (hsigmaPathOnCycle :
                  ∀ z ∈ sigmaReturnPath.support, z ∈ replacementCycle.walk.support),
                 let replacementCertificate :
                  RevisitingExtensionCertificate corr.replacementSeries.data replacementLast :=
                  {
                   earlier := earlierPrefix, earlierPositive := hearlierPositive,
                   earlierAtMost := Nat.le_of_lt_succ earlierPrefix.isLt,
                   earlierPE := hreplacementEarlierKind,
                   interveningRevisiting :=
                    helper_interveningRevisiting_4368 G k e0 input T generating ett hpositive sigma
                     Tstar hqCast available hroundLarge originalPrefix hr hprefixData corr
                     earlierPrefixBound hearlierMap oldi oldChoice oldGamma newi newChoice
                     newGamma_1 htree holdColorCast holdColorNe hnewColorNe hidentifiedDelta
                     hidentifiedGamma holdDeltaAvailable holdGammaAvailable hreplacementLastMap
                     hgammaDeltaNe replacementCycle hreturnCycle outsideIndicesNonempty
                     firstOutsideNotOne firstOutsideAtLeastTwo firstCrossingIndex
                     beforeFirstCrossingIndex laterInsideNonempty hreturnNotNext hreturnGap
                     returnCrossingIndex beforeReturnCrossingIndex,
                   gamma := available.gamma, delta := available.delta,
                   earlierGamma :=
                    ((Eq.symm
                      (id
                       (congrArg
                        (fun (_a : Fin (originalPrefix.rounds + (1 : ℕ))) ↦
                         corr.replacementSeries.data.gamma _a = some available.gamma)
                        (Eq.symm hnewIndex)))) ▸
                     ((Eq.symm
                       (id
                        (congrArg (fun (_a : Option (Fin k)) ↦ _a = some available.gamma)
                         newCurrentGamma))) ▸
                      ((Eq.symm
                        (id
                         (congrArg (fun (_a : Fin k) ↦ some _a = some available.gamma)
                          hnewGammaAvailable))) ▸
                       Eq.refl (some available.gamma)))),
                   earlierDelta :=
                    ((Eq.symm
                      (id
                       (congrArg
                        (fun (_a : Fin (originalPrefix.rounds + (1 : ℕ))) ↦
                         corr.replacementSeries.data.delta _a = some available.delta)
                        (Eq.symm hnewIndex)))) ▸
                     ((Eq.symm
                       (id
                        (congrArg (fun (_a : Option (Fin k)) ↦ _a = some available.delta)
                         newCurrentDelta))) ▸
                      ((Eq.symm
                        (id
                         (congrArg (fun (_a : Fin k) ↦ some _a = some available.delta)
                          hnewDeltaAvailable))) ▸
                       Eq.refl (some available.delta)))),
                   cycle := replacementCycleForPrefix,
                   meetsEarlier :=
                    Exists.intro available.returnVertex
                     (⟨hreturnInNewEarlier,
                       (castCycleSupport (corr.replacementSeries.data.coloring replacementLast)
                          sigma hreplacementColor replacementCycle
                          (Sum.inl available.returnVertex)).mpr
                        hreturnCycle⟩ :
                      available.returnVertex ∈
                        TreeSequenceVertexSet
                         (corr.replacementSeries.data.tree earlierPrefix.castSucc) ∧
                       Sum.inl available.returnVertex ∈ replacementCycleForPrefix.walk.support),
                   leavesCurrent :=
                    helper_leavesCurrent_4395 G k e0 input T generating ett hpositive sigma Tstar
                     available hroundLarge originalPrefix corr replacementCycle
                     hreplacementCurrentTree havailableCurrentTree houtsideCycle hreplacementColor
                     castCycleSupport,
                   edge := available.edge,
                   edgeOnCycle :=
                    (castCycleSupport (corr.replacementSeries.data.coloring replacementLast) sigma
                       hreplacementColor replacementCycle (Sum.inr available.edge)).mpr
                     ((hcycleFull (Sum.inr available.edge)).mpr rfl),
                   edgeBoundary :=
                    ((Eq.symm
                      (id
                       (congrArg
                        (fun (_a : TreeSequence G e0) ↦
                         available.edge ∈ BoundaryEdges G (TreeSequenceVertexSet _a))
                        hreplacementCurrentTree))) ▸
                     ((Eq.symm
                       (id
                        (congrArg
                         (fun (_a : TreeSequence G e0) ↦
                          available.edge ∈ BoundaryEdges G (TreeSequenceVertexSet _a))
                         (Eq.symm havailableCurrentTree)))) ▸
                      available.edgeBoundary)),
                   insideEndpoint := available.insideEndpoint,
                   outsideEndpoint := available.outsideEndpoint,
                   insideInCurrent :=
                    ((Eq.symm
                      (id
                       (congrArg
                        (fun (_a : TreeSequence G e0) ↦
                         available.insideEndpoint ∈ TreeSequenceVertexSet _a)
                        hreplacementCurrentTree))) ▸
                     ((Eq.symm
                       (id
                        (congrArg
                         (fun (_a : TreeSequence G e0) ↦
                          available.insideEndpoint ∈ TreeSequenceVertexSet _a)
                         (Eq.symm havailableCurrentTree)))) ▸
                      available.insideInCurrent)),
                   outsideNotCurrent :=
                    ((Eq.symm
                      (id
                       (congrArg
                        (fun (_a : TreeSequence G e0) ↦
                         available.outsideEndpoint ∉ TreeSequenceVertexSet _a)
                        hreplacementCurrentTree))) ▸
                     ((Eq.symm
                       (id
                        (congrArg
                         (fun (_a : TreeSequence G e0) ↦
                          available.outsideEndpoint ∉ TreeSequenceVertexSet _a)
                         (Eq.symm havailableCurrentTree)))) ▸
                      available.outsideNotCurrent)),
                   edgeEnds := available.edgeEnds, returnVertex := available.returnVertex,
                   returnInEarlier := hreturnInNewEarlier, returnPath := replacementReturnPath,
                   returnPathIsPath :=
                    castReturnWalkIsPath (corr.replacementSeries.data.coloring replacementLast)
                     sigma hreplacementColor sigmaReturnPath hsigmaReturnIsPath,
                   returnPathOnCycle :=
                    helper_returnPathOnCycle_4421 G k e0 input T generating ett hpositive sigma
                     Tstar available hroundLarge originalPrefix corr returnEdgeTransfer
                     replacementCycle hreplacementColor castReturnWalkSupport castCycleSupport
                     hsigmaPathOnCycle,
                   returnPathInternal :=
                    helper_returnPathInternal_4428 G k e0 input T generating ett hpositive sigma
                     Tstar available hroundLarge originalPrefix corr returnEdgeTransfer
                     hsigmaReturnSupport hreplacementCurrentTree havailableCurrentTree
                     hreplacementColor castReturnWalkSupport :
                   RevisitingExtensionCertificate corr.replacementSeries.data replacementLast };
                 ∀ (_ : fstar = available.edge),
                  let newStored : Finset (Fin k) :=
                   (insert available.delta ({ available.gamma } : Finset (Fin k)) : Finset (Fin k));
                  let newEdges : Finset E := ({ available.edge } : Finset E);
                  let newKind : Option TashkinovExtensionKind := some TashkinovExtensionKind.RE;
                  let newVertex : Option V := some available.insideEndpoint;
                  let newOutside : Option V := some available.outsideEndpoint;
                  let newDelta : Option (Fin k) := some available.delta;
                  let newGamma : Option (Fin k) := some available.gamma;
                  let appendedData : TashkinovSeriesData G k (originalPrefix.rounds + (1 : ℕ)) e0 :=
                   TashkinovSeriesDataAppend corr.replacementSeries.data closureTree sigma newStored
                    newEdges newKind newVertex newOutside newDelta newGamma;
                  ∀
                   (appendedCertificate :
                    RevisitingExtensionCertificate
                     (TashkinovSeriesDataAppend corr.replacementSeries.data closureTree sigma
                      newStored newEdges newKind newVertex newOutside newDelta newGamma)
                     replacementLast.castSucc)
                   (_ : appendedCertificate.gamma = replacementCertificate.gamma)
                   (_ : appendedCertificate.delta = replacementCertificate.delta)
                   (_ : appendedCertificate.edge = replacementCertificate.edge)
                   (_ : appendedCertificate.insideEndpoint = replacementCertificate.insideEndpoint)
                   (_ :
                    appendedCertificate.outsideEndpoint = replacementCertificate.outsideEndpoint)
                   (_ :
                    (ett.series.data.tree (Fin.last ett.rounds).castSucc).length <
                     closureTree.length),
                   TashkinovSeriesStep G k (originalPrefix.rounds + (1 : ℕ)) e0
                    corr.replacementInput appendedData (Fin.last (originalPrefix.rounds + (1 : ℕ)))

/-- Dependent contract shared by the revisiting terminal reconstruction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev terminalContinuationStatement.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds)
   (_ : LowerRoundInductionHypothesis G k e0 ett.rounds) (sigma : PartialEdgeColoring E k)
   (_ : IsProperEdgeColoring G sigma) (_ : IsOneEdgeUncolored sigma e0)
   (_ :
    StableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
     (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
     (ett.series.data.coloring (Fin.last ett.rounds)) sigma)
   (Tstar : TreeSequence G e0)
   (_ : TreeSequenceInitialSegment (ett.series.data.tree (Fin.last ett.rounds).castSucc) Tstar)
   (_ : (ett.series.data.tree (Fin.last ett.rounds).castSucc).length < Tstar.length) (fstar : E)
   (seed : TreeSequence G e0)
   (_ : ett.series.data.connectingEdges (Fin.last ett.rounds) = ({ fstar } : Finset E))
   (_ : TreeSequenceAdjoinEdge (ett.series.data.tree (Fin.last ett.rounds).castSucc) fstar seed)
   (closureTree : TreeSequence G e0) (_ : TashkinovClosure sigma seed closureTree)
   (_ : TreeSequenceInitialSegment Tstar closureTree)
   (_ :
    TreeSequenceInitialSegment (ett.series.data.tree (Fin.last ett.rounds).castSucc) closureTree),
   let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin ett.rounds);
   ∀ (_ : q.succ = Fin.last ett.rounds)
    (_ : q.castSucc = (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin (ett.rounds + (1 : ℕ))))
    (_ : TreeSequence G e0) (_ : IsProperEdgeColoring G (ett.series.data.coloring q.castSucc))
    (_ : IsOneEdgeUncolored (ett.series.data.coloring q.castSucc) e0)
    (_ :
     ColoredVertexSetClosed G (ett.series.data.coloring q.castSucc)
      (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)))
    (available : RevisitingExtensionCertificate ett.series.data q.castSucc)
    (_ :
     ett.series.data.stored q.succ =
      (insert available.delta ({ available.gamma } : Finset (Fin k)) : Finset (Fin k)))
    (_ : ett.series.data.connectingEdges q.succ = ({ available.edge } : Finset E))
    (_ : ett.series.data.kind q.succ = some TashkinovExtensionKind.RE)
    (hroundLarge : (1 : ℕ) < ett.rounds)
    (originalPrefix :
     ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin (ett.rounds + (1 : ℕ)))))
    (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ))
    (_ :
     ∀ (i : Fin (originalPrefix.rounds + (2 : ℕ))),
      originalPrefix.series.data.tree i =
       ett.series.data.tree
        (Fin.castLE
         (Decidable.byContradiction
          fun (a : ¬originalPrefix.rounds + (2 : ℕ) ≤ ett.rounds + (2 : ℕ)) ↦ (by omega))
         i))
    (_ :
     ∀ (i : Fin (originalPrefix.rounds + (1 : ℕ))),
      originalPrefix.series.data.coloring i =
        ett.series.data.coloring
         (Fin.castLE
          (Decidable.byContradiction
           fun (a : ¬originalPrefix.rounds + (1 : ℕ) ≤ ett.rounds + (1 : ℕ)) ↦ (by omega))
          i) ∧
       originalPrefix.series.data.stored i =
         ett.series.data.stored
          (Fin.castLE
           (Decidable.byContradiction
            fun (a : ¬originalPrefix.rounds + (1 : ℕ) ≤ ett.rounds + (1 : ℕ)) ↦ (by omega))
           i) ∧
        originalPrefix.series.data.connectingEdges i =
          ett.series.data.connectingEdges
           (Fin.castLE
            (Decidable.byContradiction
             fun (a : ¬originalPrefix.rounds + (1 : ℕ) ≤ ett.rounds + (1 : ℕ)) ↦ (by omega))
            i) ∧
         originalPrefix.series.data.kind i =
           ett.series.data.kind
            (Fin.castLE
             (Decidable.byContradiction
              fun (a : ¬originalPrefix.rounds + (1 : ℕ) ≤ ett.rounds + (1 : ℕ)) ↦ (by omega))
             i) ∧
          TashkinovStoredColors originalPrefix.series.data i =
           TashkinovStoredColors ett.series.data
            (Fin.castLE
             (Decidable.byContradiction
              fun (a : ¬originalPrefix.rounds + (1 : ℕ) ≤ ett.rounds + (1 : ℕ)) ↦ (by omega))
             i))
    (corr :
     CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigma
      (ett.series.data.tree (Fin.last ett.rounds).castSucc))
    (_ :
     corr.replacementSeries.data.tree (Fin.last (originalPrefix.rounds + (1 : ℕ))) =
      ett.series.data.tree (Fin.last ett.rounds).castSucc)
    (_ : corr.replacementSeries.data.coloring (Fin.last originalPrefix.rounds) = sigma)
    (_ : MaximumProperty corr.replacementETT)
    (earlierPrefixBound : (↑available.earlier : ℕ) < originalPrefix.rounds + (1 : ℕ)),
    let earlierPrefix : Fin (originalPrefix.rounds + (1 : ℕ)) :=
     (⟨(↑available.earlier : ℕ), earlierPrefixBound⟩ : Fin (originalPrefix.rounds + (1 : ℕ)));
    ∀
     (_ :
      Fin.castLE
        (Decidable.byContradiction
         fun (a : ¬originalPrefix.rounds + (1 : ℕ) ≤ ett.rounds + (1 : ℕ)) ↦ (by omega))
        earlierPrefix =
       available.earlier)
     (_ : (0 : ℕ) < (↑earlierPrefix : ℕ))
     (_ : corr.replacementSeries.data.kind earlierPrefix = some TashkinovExtensionKind.PE)
     (oldi : Fin ett.rounds)
     (oldChoice :
      MaximumDefectiveChoice G e0 (ett.series.data.tree oldi.succ.castSucc)
       (TashkinovStoredColors ett.series.data oldi.castSucc)
       (ett.series.data.coloring oldi.castSucc))
     (oldGamma : Fin k) (_ : available.earlier = oldi.succ) (newi : Fin originalPrefix.rounds)
     (newChoice :
      MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree newi.succ.castSucc)
       (TashkinovStoredColors corr.replacementSeries.data newi.castSucc)
       (corr.replacementSeries.data.coloring newi.castSucc))
     (newGamma : Fin k) (_ : corr.replacementSeries.data.delta newi.succ = some newChoice.color)
     (_ : corr.replacementSeries.data.gamma newi.succ = some newGamma)
     (_ : newi.succ = earlierPrefix)
     (htree :
      corr.replacementSeries.data.tree newi.succ.castSucc =
       ett.series.data.tree oldi.succ.castSucc),
     let oldChoiceOnNew :
      MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree newi.succ.castSucc)
       (TashkinovStoredColors ett.series.data oldi.castSucc)
       (ett.series.data.coloring oldi.castSucc) :=
      transportDefectiveChoice (Eq.symm htree) oldChoice;
     ∀ (holdColorCast : oldChoiceOnNew.color = oldChoice.color)
      (_ :
       s(oldChoiceOnNew.vertex, oldChoiceOnNew.otherEndpoint) =
        s(newChoice.vertex, newChoice.otherEndpoint))
      (holdColorNe : oldGamma ≠ oldChoice.color) (hnewColorNe : newGamma ≠ newChoice.color)
      (hidentifiedDelta : newChoice.color = oldChoiceOnNew.color)
      (hidentifiedGamma : newGamma = oldGamma)
      (holdDeltaAvailable : oldChoice.color = available.delta)
      (holdGammaAvailable : oldGamma = available.gamma) (_ : newChoice.color = available.delta)
      (_ : newGamma = available.gamma),
      let replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last originalPrefix.rounds;
      ∀
       (_ :
        Fin.castLE
          (Decidable.byContradiction
           fun (a : ¬originalPrefix.rounds + (1 : ℕ) ≤ ett.rounds + (1 : ℕ)) ↦ (by omega))
          replacementLast =
         q.castSucc)
       (_ : available.delta ∈ MissingColors G sigma newChoice.vertex)
       (_ : available.gamma ≠ available.delta)
       (_ :
        newChoice.vertex ∈
         TreeSequenceVertexSet (ett.series.data.tree (Fin.last ett.rounds).castSucc))
       (_ :
        TwoColorNontrivialPathComponent G sigma available.gamma available.delta
         (Sum.inl newChoice.vertex))
       (_ :
        ∃ v ∈ TreeSequenceVertexSet (ett.series.data.tree (Fin.last ett.rounds).castSucc),
         Sum.inl v ∈
          TwoColorComponent G sigma available.gamma available.delta (Sum.inl newChoice.vertex))
       (_ :
        StableColoring (ett.series.data.tree q.succ.castSucc)
         (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)
         sigma),
       let sigmaReturnGraph : SimpleGraph (V ⊕ E) :=
        TwoColorIncidenceGraph G sigma available.gamma available.delta;
       ∀
        (returnEdgeTransfer : ∀ edge ∈ available.returnPath.edges, edge ∈ sigmaReturnGraph.edgeSet),
        let sigmaReturnPath :
         sigmaReturnGraph.Walk (Sum.inr available.edge) (Sum.inl available.returnVertex) :=
         available.returnPath.transfer sigmaReturnGraph returnEdgeTransfer;
        ∀ (_ : sigmaReturnPath.IsPath)
         (_ : ∀ (z : V ⊕ E), z ∈ sigmaReturnPath.support ↔ z ∈ available.returnPath.support)
         (_ :
          Sum.inl available.returnVertex ∈
           TwoColorComponent G sigma available.gamma available.delta (Sum.inr available.edge))
         (_ :
          Sum.inl available.outsideEndpoint ∈
           TwoColorComponent G sigma available.gamma available.delta (Sum.inr available.edge))
         (_ :
          available.returnVertex ∈
           TreeSequenceVertexSet (corr.replacementSeries.data.tree earlierPrefix.castSucc))
         (_ :
          available.returnVertex ∈
           TreeSequenceVertexSet (ett.series.data.tree (Fin.last ett.rounds).castSucc))
         (_ :
          TwoColorComponent G sigma available.gamma available.delta (Sum.inl newChoice.vertex) ≠
           TwoColorComponent G sigma available.gamma available.delta (Sum.inr available.edge)),
         Nonempty (CorrespondingExtendedTashkinovTree G k e0 ett sigma Tstar)

end GoldbergSeymour.TerminalRebuild

end
