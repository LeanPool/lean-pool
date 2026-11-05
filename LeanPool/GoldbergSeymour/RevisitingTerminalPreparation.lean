/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/

module

public import LeanPool.GoldbergSeymour.TwoColorNontrivialPathComponent
public import LeanPool.GoldbergSeymour.StableColoringIncidentEdgeCriterion
public import LeanPool.GoldbergSeymour.LowerRoundInductionHypothesis
public import LeanPool.GoldbergSeymour.TashkinovSeriesDataAppend
public import LeanPool.GoldbergSeymour.TwoColorComponentSwapMissingBehavior
public import LeanPool.GoldbergSeymour.MissingColorIncidenceEndpoint
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentVertexSetSubset

/-!
# Preparation for a revisiting terminal rebuild

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
abbrev helperBranch4795Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (hlower :
        LowerRoundInductionHypothesis G k e0 ett.rounds) (sigma : PartialEdgeColoring E k)
        (hsigmaProper : IsProperEdgeColoring G sigma) (hsigmaOne : IsOneEdgeUncolored sigma e0)
        (hsigmaStable : StableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) (ett.series.data.coloring
        (Fin.last ett.rounds)) sigma) (Tstar : TreeSequence G e0) (hTnTstar :
        TreeSequenceInitialSegment (ett.series.data.tree (Fin.last ett.rounds).castSucc) Tstar)
        (hstrict : (ett.series.data.tree (Fin.last ett.rounds).castSucc).length < Tstar.length)
        (fstar : E) (seed : TreeSequence G e0) (hfinalEdges : ett.series.data.connectingEdges
        (Fin.last ett.rounds) = ({ fstar } : Finset E)) (hadjoin : TreeSequenceAdjoinEdge
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) fstar seed) (closureTree :
        TreeSequence G e0) (hseedClosure : TashkinovClosure sigma seed closureTree) (hTstarClosure
        : TreeSequenceInitialSegment Tstar closureTree) (hTnClosure : TreeSequenceInitialSegment
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) closureTree),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), Nat.sub_lt (Nat.zero_lt_of_lt hpositive) (
    by omega
    )⟩ : Fin ett.rounds);
    ∀ (hqSucc : q.succ = Fin.last ett.rounds) (hqCast : q.castSucc = (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ)))) (adjoined : TreeSequence G e0) (previousProper :
        IsProperEdgeColoring G (ett.series.data.coloring q.castSucc)) (previousOneUncolored :
        IsOneEdgeUncolored (ett.series.data.coloring q.castSucc) e0) (previousClosed :
        ColoredVertexSetClosed G (ett.series.data.coloring q.castSucc) (TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc))) (available : RevisitingExtensionCertificate
        ett.series.data q.castSucc) (currentStored : ett.series.data.stored q.succ = (insert
        available.delta ({ available.gamma } : Finset (Fin k)) : Finset (Fin k))) (currentEdges :
        ett.series.data.connectingEdges q.succ = ({ available.edge } : Finset E)) (currentKind :
        ett.series.data.kind q.succ = some TashkinovExtensionKind.RE) (adjoinedExactly :
        TreeSequenceAdjoinEdge (ett.series.data.tree q.succ.castSucc) available.edge adjoined)
        (hsigmaPrevStable : StableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (TashkinovStoredColors ett.series.data (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ)))) (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ)))) sigma) (hroundLarge : (1 : ℕ) < ett.rounds) (originalPrefix :
        ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ))
        (hprefixTrees :
    ∀ (i : Fin (originalPrefix.rounds + (2 : ℕ))), originalPrefix.series.data.tree i =
        ett.series.data.tree (Fin.castLE (
    by omega
    ) i)) (hprefixData :
    ∀ (i : Fin (originalPrefix.rounds + (1 : ℕ))), originalPrefix.series.data.coloring i =
        ett.series.data.coloring (Fin.castLE (
    by omega
    ) i) ∧ originalPrefix.series.data.stored i = ett.series.data.stored (Fin.castLE (
    by omega
    ) i) ∧ originalPrefix.series.data.connectingEdges i = ett.series.data.connectingEdges
        (Fin.castLE (
    by omega
    ) i) ∧ originalPrefix.series.data.kind i = ett.series.data.kind (Fin.castLE (
    by omega
    ) i) ∧ TashkinovStoredColors originalPrefix.series.data i = TashkinovStoredColors
        ett.series.data (Fin.castLE (
    by omega
    ) i)) (corr : CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigma
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)) (hcorrFinalTree :
        corr.replacementSeries.data.tree (Fin.last (originalPrefix.rounds + (1 : ℕ))) =
        ett.series.data.tree (Fin.last ett.rounds).castSucc) (hcorrFinalColor :
        corr.replacementSeries.data.coloring (Fin.last originalPrefix.rounds) = sigma) (hcorrMP :
        MaximumProperty corr.replacementETT) (earlierPrefixBound : (↑available.earlier : ℕ) <
        originalPrefix.rounds + (1 : ℕ)),
    let earlierPrefix : Fin (originalPrefix.rounds + (1 : ℕ)) := (⟨(↑available.earlier : ℕ),
        earlierPrefixBound⟩ : Fin (originalPrefix.rounds + (1 : ℕ)));
    ∀ (hearlierMap : Fin.castLE (
    by omega
    ) earlierPrefix = available.earlier) (hearlierPositive : (0 : ℕ) < (↑earlierPrefix : ℕ))
        (hreplacementEarlierKind : corr.replacementSeries.data.kind earlierPrefix = some
        TashkinovExtensionKind.PE) (oldi : Fin ett.rounds) (oldChoice : MaximumDefectiveChoice G
        e0 (ett.series.data.tree oldi.succ.castSucc) (TashkinovStoredColors ett.series.data
        oldi.castSucc) (ett.series.data.coloring oldi.castSucc)) (oldGamma : Fin k) (oldGammaRule
        : ParallelExtensionColor ett.series.data oldi.castSucc oldChoice.selected oldChoice.vertex
        oldGamma) (oldSecond : PartialEdgeColoring E k) (oldSecondProper : IsProperEdgeColoring G
        oldSecond) (oldSecondStable : StableColoring (ett.series.data.tree oldi.succ.castSucc)
        (insert oldChoice.color (TashkinovStoredColors ett.series.data oldi.castSucc) : Finset
        (Fin k)) oldChoice.selected oldSecond) (oldCurrentColoring : ett.series.data.coloring
        oldi.succ = TwoColorComponentSwap G oldSecond oldGamma oldChoice.color (Sum.inl
        oldChoice.vertex)) (oldCurrentStored : ett.series.data.stored oldi.succ = (insert
        oldChoice.color ({ oldGamma } : Finset (Fin k)) : Finset (Fin k))) (oldCurrentEdges :
        ett.series.data.connectingEdges oldi.succ = ({ oldChoice.edge } : Finset E))
        (oldCurrentDelta : ett.series.data.delta oldi.succ = some oldChoice.color)
        (oldCurrentGamma : ett.series.data.gamma oldi.succ = some oldGamma) (holdTarget :
        available.earlier = oldi.succ) (holdIndex : oldi.succ = available.earlier) (newi : Fin
        originalPrefix.rounds) (newChoice : MaximumDefectiveChoice G e0
        (corr.replacementSeries.data.tree newi.succ.castSucc) (TashkinovStoredColors
        corr.replacementSeries.data newi.castSucc) (corr.replacementSeries.data.coloring
        newi.castSucc)) (newGamma : Fin k) (newGammaRule : ParallelExtensionColor
        corr.replacementSeries.data newi.castSucc newChoice.selected newChoice.vertex newGamma)
        (newSecond : PartialEdgeColoring E k) (newSecondProper : IsProperEdgeColoring G newSecond)
        (newSecondStable : StableColoring (corr.replacementSeries.data.tree newi.succ.castSucc)
        (insert newChoice.color (TashkinovStoredColors corr.replacementSeries.data newi.castSucc)
        : Finset (Fin k)) newChoice.selected newSecond) (newExit : TreeExit
        (corr.replacementSeries.data.tree newi.succ.castSucc) newSecond newGamma newChoice.color
        newChoice.vertex) (newCurrentColoring : corr.replacementSeries.data.coloring newi.succ =
        TwoColorComponentSwap G newSecond newGamma newChoice.color (Sum.inl newChoice.vertex))
        (newCurrentStored : corr.replacementSeries.data.stored newi.succ = (insert newChoice.color
        ({ newGamma } : Finset (Fin k)) : Finset (Fin k))) (newCurrentEdges :
        corr.replacementSeries.data.connectingEdges newi.succ = ({ newChoice.edge } : Finset E))
        (newCurrentDelta : corr.replacementSeries.data.delta newi.succ = some newChoice.color)
        (newCurrentGamma : corr.replacementSeries.data.gamma newi.succ = some newGamma)
        (hnewTarget : earlierPrefix = newi.succ), Nonempty (CorrespondingExtendedTashkinovTree G k
        e0 ett sigma Tstar)

/-- Dependent contract shared by the revisiting terminal reconstruction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperBranch5611Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (hlower :
        LowerRoundInductionHypothesis G k e0 ett.rounds) (sigma : PartialEdgeColoring E k)
        (hsigmaProper : IsProperEdgeColoring G sigma) (hsigmaOne : IsOneEdgeUncolored sigma e0)
        (hsigmaStable : StableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) (ett.series.data.coloring
        (Fin.last ett.rounds)) sigma) (Tstar : TreeSequence G e0) (hTnTstar :
        TreeSequenceInitialSegment (ett.series.data.tree (Fin.last ett.rounds).castSucc) Tstar)
        (hstrict : (ett.series.data.tree (Fin.last ett.rounds).castSucc).length < Tstar.length)
        (fstar : E) (seed : TreeSequence G e0) (hfinalEdges : ett.series.data.connectingEdges
        (Fin.last ett.rounds) = ({ fstar } : Finset E)) (hadjoin : TreeSequenceAdjoinEdge
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) fstar seed) (closureTree :
        TreeSequence G e0) (hseedClosure : TashkinovClosure sigma seed closureTree) (hTstarClosure
        : TreeSequenceInitialSegment Tstar closureTree) (hTnClosure : TreeSequenceInitialSegment
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) closureTree),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), Nat.sub_lt (Nat.zero_lt_of_lt hpositive) (
    by omega
    )⟩ : Fin ett.rounds);
    ∀ (hqSucc : q.succ = Fin.last ett.rounds) (hqCast : q.castSucc = (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ)))) (adjoined : TreeSequence G e0) (previousProper :
        IsProperEdgeColoring G (ett.series.data.coloring q.castSucc)) (previousOneUncolored :
        IsOneEdgeUncolored (ett.series.data.coloring q.castSucc) e0) (previousClosed :
        ColoredVertexSetClosed G (ett.series.data.coloring q.castSucc) (TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc))) (available : RevisitingExtensionCertificate
        ett.series.data q.castSucc) (currentStored : ett.series.data.stored q.succ = (insert
        available.delta ({ available.gamma } : Finset (Fin k)) : Finset (Fin k))) (currentEdges :
        ett.series.data.connectingEdges q.succ = ({ available.edge } : Finset E)) (currentKind :
        ett.series.data.kind q.succ = some TashkinovExtensionKind.RE) (adjoinedExactly :
        TreeSequenceAdjoinEdge (ett.series.data.tree q.succ.castSucc) available.edge adjoined)
        (hsigmaPrevStable : StableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (TashkinovStoredColors ett.series.data (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ)))) (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ)))) sigma) (hpositivePrefix : (1 : ℕ) < ett.rounds ∧
    ∃ (originalPrefix : ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last
        ett.rounds).castSucc) (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ)),
        MaximumProperty originalPrefix ∧ (
    ∀ (i : Fin (originalPrefix.rounds + (2 : ℕ))), originalPrefix.series.data.tree i =
        ett.series.data.tree (Fin.castLE (
    by omega
    ) i)) ∧ (
    ∀ (i : Fin (originalPrefix.rounds + (1 : ℕ))), originalPrefix.series.data.coloring i =
        ett.series.data.coloring (Fin.castLE (
    by omega
    ) i) ∧ originalPrefix.series.data.stored i = ett.series.data.stored (Fin.castLE (
    by omega
    ) i) ∧ originalPrefix.series.data.connectingEdges i = ett.series.data.connectingEdges
        (Fin.castLE (
    by omega
    ) i) ∧ originalPrefix.series.data.kind i = ett.series.data.kind (Fin.castLE (
    by omega
    ) i) ∧ TashkinovStoredColors originalPrefix.series.data i = TashkinovStoredColors
        ett.series.data (Fin.castLE (
    by omega
    ) i)) ∧
    ∃ (corr : CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigma (ett.series.data.tree
        (Fin.last ett.rounds).castSucc)), corr.replacementSeries.data.tree (Fin.last
        (originalPrefix.rounds + (1 : ℕ))) = ett.series.data.tree (Fin.last ett.rounds).castSucc ∧
        corr.replacementSeries.data.coloring (Fin.last originalPrefix.rounds) = sigma ∧
        MaximumProperty corr.replacementETT), Nonempty (CorrespondingExtendedTashkinovTree G k e0
        ett sigma Tstar)

/-- Dependent contract shared by the revisiting terminal reconstruction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperReturnPathOnCycle4421Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [inst_3 : DecidableEq
        E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (Tstar : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (available : RevisitingExtensionCertificate ett.series.data q.castSucc) (hroundLarge : (1 :
        ℕ) < ett.rounds) (originalPrefix : ExtendedTashkinovTree G k e0 input
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) (ett.series.data.coloring
        (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (corr : CorrespondingExtendedTashkinovTree G k e0
        originalPrefix sigma (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
    let replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last originalPrefix.rounds;
    let sigmaReturnGraph : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G sigma available.gamma
        available.delta;
    ∀ (returnEdgeTransfer :
    ∀ edge ∈ available.returnPath.edges, edge ∈ sigmaReturnGraph.edgeSet),
    let sigmaReturnPath : sigmaReturnGraph.Walk (Sum.inr available.edge) (Sum.inl
        available.returnVertex) := available.returnPath.transfer sigmaReturnGraph
        returnEdgeTransfer;
    ∀ (replacementCycle : TwoColorCycle G sigma available.gamma available.delta)
        (hreplacementColor : corr.replacementSeries.data.coloring replacementLast = sigma),
    let castReturnWalk : (phi psi : PartialEdgeColoring E k) → (hphi : phi = psi) → (P :
        (TwoColorIncidenceGraph G psi available.gamma available.delta).Walk (Sum.inr
        available.edge) (Sum.inl available.returnVertex)) → (TwoColorIncidenceGraph G phi
        available.gamma available.delta).Walk (Sum.inr available.edge) (Sum.inl
        available.returnVertex) := fun (phi psi : PartialEdgeColoring E k) (hphi : phi = psi) (P :
        (TwoColorIncidenceGraph G psi available.gamma available.delta).Walk (Sum.inr
        available.edge) (Sum.inl available.returnVertex)) ↦ @Eq.ndrec (PartialEdgeColoring E k)
        phi (fun (psi : PartialEdgeColoring E k) ↦ (P : @SimpleGraph.Walk (Sum V E)
        (@TwoColorIncidenceGraph V E G k psi (@RevisitingExtensionCertificate.gamma V E inst
        inst_1 G k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T generating
        ett) e0 (@TashkinovSeries.data V E inst inst_1 inst_3 G k (@ExtendedTashkinovTree.rounds V
        E inst inst_1 inst_3 G k e0 input T generating ett) e0 input
        (@ExtendedTashkinovTree.series V E inst inst_1 inst_3 G k e0 input T generating ett))
        (@Fin.castSucc (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
        generating ett) q) available) (@RevisitingExtensionCertificate.delta V E inst inst_1 G k
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T generating ett) e0
        (@TashkinovSeries.data V E inst inst_1 inst_3 G k (@ExtendedTashkinovTree.rounds V E inst
        inst_1 inst_3 G k e0 input T generating ett) e0 input (@ExtendedTashkinovTree.series V E
        inst inst_1 inst_3 G k e0 input T generating ett)) (@Fin.castSucc
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T generating ett) q)
        available)) (@Sum.inr V E (@RevisitingExtensionCertificate.edge V E inst inst_1 G k
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T generating ett) e0
        (@TashkinovSeries.data V E inst inst_1 inst_3 G k (@ExtendedTashkinovTree.rounds V E inst
        inst_1 inst_3 G k e0 input T generating ett) e0 input (@ExtendedTashkinovTree.series V E
        inst inst_1 inst_3 G k e0 input T generating ett)) (@Fin.castSucc
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T generating ett) q)
        available)) (@Sum.inl V E (@RevisitingExtensionCertificate.returnVertex V E inst inst_1 G
        k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T generating ett) e0
        (@TashkinovSeries.data V E inst inst_1 inst_3 G k (@ExtendedTashkinovTree.rounds V E inst
        inst_1 inst_3 G k e0 input T generating ett) e0 input (@ExtendedTashkinovTree.series V E
        inst inst_1 inst_3 G k e0 input T generating ett)) (@Fin.castSucc
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T generating ett) q)
        available))) → @SimpleGraph.Walk (Sum V E) (@TwoColorIncidenceGraph V E G k phi
        (@RevisitingExtensionCertificate.gamma V E inst inst_1 G k (@ExtendedTashkinovTree.rounds
        V E inst inst_1 inst_3 G k e0 input T generating ett) e0 (@TashkinovSeries.data V E inst
        inst_1 inst_3 G k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
        generating ett) e0 input (@ExtendedTashkinovTree.series V E inst inst_1 inst_3 G k e0
        input T generating ett)) (@Fin.castSucc (@ExtendedTashkinovTree.rounds V E inst inst_1
        inst_3 G k e0 input T generating ett) q) available) (@RevisitingExtensionCertificate.delta
        V E inst inst_1 G k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
        generating ett) e0 (@TashkinovSeries.data V E inst inst_1 inst_3 G k
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T generating ett) e0
        input (@ExtendedTashkinovTree.series V E inst inst_1 inst_3 G k e0 input T generating
        ett)) (@Fin.castSucc (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
        generating ett) q) available)) (@Sum.inr V E (@RevisitingExtensionCertificate.edge V E
        inst inst_1 G k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
        generating ett) e0 (@TashkinovSeries.data V E inst inst_1 inst_3 G k
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T generating ett) e0
        input (@ExtendedTashkinovTree.series V E inst inst_1 inst_3 G k e0 input T generating
        ett)) (@Fin.castSucc (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
        generating ett) q) available)) (@Sum.inl V E (@RevisitingExtensionCertificate.returnVertex
        V E inst inst_1 G k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
        generating ett) e0 (@TashkinovSeries.data V E inst inst_1 inst_3 G k
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T generating ett) e0
        input (@ExtendedTashkinovTree.series V E inst inst_1 inst_3 G k e0 input T generating
        ett)) (@Fin.castSucc (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
        generating ett) q) available))) (fun (P : @SimpleGraph.Walk (Sum V E)
        (@TwoColorIncidenceGraph V E G k phi (@RevisitingExtensionCertificate.gamma V E inst
        inst_1 G k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T generating
        ett) e0 (@TashkinovSeries.data V E inst inst_1 inst_3 G k (@ExtendedTashkinovTree.rounds V
        E inst inst_1 inst_3 G k e0 input T generating ett) e0 input
        (@ExtendedTashkinovTree.series V E inst inst_1 inst_3 G k e0 input T generating ett))
        (@Fin.castSucc (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
        generating ett) q) available) (@RevisitingExtensionCertificate.delta V E inst inst_1 G k
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T generating ett) e0
        (@TashkinovSeries.data V E inst inst_1 inst_3 G k (@ExtendedTashkinovTree.rounds V E inst
        inst_1 inst_3 G k e0 input T generating ett) e0 input (@ExtendedTashkinovTree.series V E
        inst inst_1 inst_3 G k e0 input T generating ett)) (@Fin.castSucc
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T generating ett) q)
        available)) (@Sum.inr V E (@RevisitingExtensionCertificate.edge V E inst inst_1 G k
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T generating ett) e0
        (@TashkinovSeries.data V E inst inst_1 inst_3 G k (@ExtendedTashkinovTree.rounds V E inst
        inst_1 inst_3 G k e0 input T generating ett) e0 input (@ExtendedTashkinovTree.series V E
        inst inst_1 inst_3 G k e0 input T generating ett)) (@Fin.castSucc
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T generating ett) q)
        available)) (@Sum.inl V E (@RevisitingExtensionCertificate.returnVertex V E inst inst_1 G
        k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T generating ett) e0
        (@TashkinovSeries.data V E inst inst_1 inst_3 G k (@ExtendedTashkinovTree.rounds V E inst
        inst_1 inst_3 G k e0 input T generating ett) e0 input (@ExtendedTashkinovTree.series V E
        inst inst_1 inst_3 G k e0 input T generating ett)) (@Fin.castSucc
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T generating ett) q)
        available))) ↦ P) psi hphi P;
    ∀ (castReturnWalkSupport :
    ∀ (phi psi : PartialEdgeColoring E k) (hphi : phi = psi) (P : (TwoColorIncidenceGraph G psi
        available.gamma available.delta).Walk (Sum.inr available.edge) (Sum.inl
        available.returnVertex)) (z : V ⊕ E), z ∈ (castReturnWalk phi psi hphi P).support ↔ z ∈
        P.support),
    let castCycle : (phi psi : PartialEdgeColoring E k) → (hphi : phi = psi) → (C : TwoColorCycle
        G psi available.gamma available.delta) → TwoColorCycle G phi available.gamma
        available.delta := fun (phi psi : PartialEdgeColoring E k) (hphi : phi = psi) (C :
        TwoColorCycle G psi available.gamma available.delta) ↦ @Eq.ndrec (PartialEdgeColoring E k)
        phi (fun (psi : PartialEdgeColoring E k) ↦ (C : @TwoColorCycle V E G k psi
        (@RevisitingExtensionCertificate.gamma V E inst inst_1 G k (@ExtendedTashkinovTree.rounds
        V E inst inst_1 inst_3 G k e0 input T generating ett) e0 (@TashkinovSeries.data V E inst
        inst_1 inst_3 G k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
        generating ett) e0 input (@ExtendedTashkinovTree.series V E inst inst_1 inst_3 G k e0
        input T generating ett)) (@Fin.castSucc (@ExtendedTashkinovTree.rounds V E inst inst_1
        inst_3 G k e0 input T generating ett) q) available) (@RevisitingExtensionCertificate.delta
        V E inst inst_1 G k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
        generating ett) e0 (@TashkinovSeries.data V E inst inst_1 inst_3 G k
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T generating ett) e0
        input (@ExtendedTashkinovTree.series V E inst inst_1 inst_3 G k e0 input T generating
        ett)) (@Fin.castSucc (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
        generating ett) q) available)) → @TwoColorCycle V E G k phi
        (@RevisitingExtensionCertificate.gamma V E inst inst_1 G k (@ExtendedTashkinovTree.rounds
        V E inst inst_1 inst_3 G k e0 input T generating ett) e0 (@TashkinovSeries.data V E inst
        inst_1 inst_3 G k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
        generating ett) e0 input (@ExtendedTashkinovTree.series V E inst inst_1 inst_3 G k e0
        input T generating ett)) (@Fin.castSucc (@ExtendedTashkinovTree.rounds V E inst inst_1
        inst_3 G k e0 input T generating ett) q) available) (@RevisitingExtensionCertificate.delta
        V E inst inst_1 G k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
        generating ett) e0 (@TashkinovSeries.data V E inst inst_1 inst_3 G k
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T generating ett) e0
        input (@ExtendedTashkinovTree.series V E inst inst_1 inst_3 G k e0 input T generating
        ett)) (@Fin.castSucc (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
        generating ett) q) available)) (fun (C : @TwoColorCycle V E G k phi
        (@RevisitingExtensionCertificate.gamma V E inst inst_1 G k (@ExtendedTashkinovTree.rounds
        V E inst inst_1 inst_3 G k e0 input T generating ett) e0 (@TashkinovSeries.data V E inst
        inst_1 inst_3 G k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
        generating ett) e0 input (@ExtendedTashkinovTree.series V E inst inst_1 inst_3 G k e0
        input T generating ett)) (@Fin.castSucc (@ExtendedTashkinovTree.rounds V E inst inst_1
        inst_3 G k e0 input T generating ett) q) available) (@RevisitingExtensionCertificate.delta
        V E inst inst_1 G k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
        generating ett) e0 (@TashkinovSeries.data V E inst inst_1 inst_3 G k
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T generating ett) e0
        input (@ExtendedTashkinovTree.series V E inst inst_1 inst_3 G k e0 input T generating
        ett)) (@Fin.castSucc (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
        generating ett) q) available)) ↦ C) psi hphi C;
    ∀ (castCycleSupport :
    ∀ (phi psi : PartialEdgeColoring E k) (hphi : phi = psi) (C : TwoColorCycle G psi
        available.gamma available.delta) (z : V ⊕ E), z ∈ (castCycle phi psi hphi C).walk.support
        ↔ z ∈ C.walk.support),
    let replacementCycleForPrefix : TwoColorCycle G (corr.replacementSeries.data.coloring
        replacementLast) available.gamma available.delta := castCycle
        (corr.replacementSeries.data.coloring replacementLast) sigma hreplacementColor
        replacementCycle;
    let replacementReturnPath : (TwoColorIncidenceGraph G (corr.replacementSeries.data.coloring
        replacementLast) available.gamma available.delta).Walk (Sum.inr available.edge) (Sum.inl
        available.returnVertex) := castReturnWalk (corr.replacementSeries.data.coloring
        replacementLast) sigma hreplacementColor sigmaReturnPath;
    ∀ (hsigmaPathOnCycle :
    ∀ z ∈ sigmaReturnPath.support, z ∈ replacementCycle.walk.support),
    ∀ z ∈ replacementReturnPath.support, z ∈ replacementCycleForPrefix.walk.support

/-- Typed data construction shared by the revisiting terminal reconstruction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev transportDefectiveChoice {V E : Type*} [Fintype V] [Fintype E] {G : LooplessMultigraph V E}
    {k : ℕ} {e0 : E} {A B : TreeSequence G e0} (equality : A = B) {colors : Finset (Fin k)}
    {coloring : PartialEdgeColoring E k} (choice : MaximumDefectiveChoice G e0 A colors coloring) :
    MaximumDefectiveChoice G e0 B colors coloring :=
  equality ▸ choice

/-- Dependent contract shared by the revisiting terminal reconstruction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev returnPathInternalStatement.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [inst_3 : DecidableEq
        E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (available : RevisitingExtensionCertificate ett.series.data q.castSucc) (hroundLarge : (1 :
        ℕ) < ett.rounds) (originalPrefix : ExtendedTashkinovTree G k e0 input
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) (ett.series.data.coloring
        (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (corr : CorrespondingExtendedTashkinovTree G k e0
        originalPrefix sigma (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
    let replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last originalPrefix.rounds;
    let sigmaReturnGraph : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G sigma available.gamma
        available.delta;
    ∀ (returnEdgeTransfer :
    ∀ edge ∈ available.returnPath.edges, edge ∈ sigmaReturnGraph.edgeSet),
    let sigmaReturnPath : sigmaReturnGraph.Walk (Sum.inr available.edge) (Sum.inl
        available.returnVertex) := available.returnPath.transfer sigmaReturnGraph
        returnEdgeTransfer;
    ∀ (_ :
    ∀ (z : V ⊕ E), z ∈ sigmaReturnPath.support ↔ z ∈ available.returnPath.support) (_ :
    have replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last
        originalPrefix.rounds; corr.replacementSeries.data.tree replacementLast.succ =
        ett.series.data.tree (Fin.last ett.rounds).castSucc) (_ : ett.series.data.tree
        q.castSucc.succ = ett.series.data.tree (Fin.last ett.rounds).castSucc) (hreplacementColor
        : corr.replacementSeries.data.coloring replacementLast = sigma),
    let castReturnWalk : (phi psi : PartialEdgeColoring E k) → (hphi : phi = psi) → (P :
        (TwoColorIncidenceGraph G psi available.gamma available.delta).Walk (Sum.inr
        available.edge) (Sum.inl available.returnVertex)) → (TwoColorIncidenceGraph G phi
        available.gamma available.delta).Walk (Sum.inr available.edge) (Sum.inl
        available.returnVertex) := fun (phi psi : PartialEdgeColoring E k) (hphi : phi = psi) (P :
        (TwoColorIncidenceGraph G psi available.gamma available.delta).Walk (Sum.inr
        available.edge) (Sum.inl available.returnVertex)) ↦ @Eq.ndrec (PartialEdgeColoring E k)
        phi (fun (psi : PartialEdgeColoring E k) ↦ (P : @SimpleGraph.Walk (Sum V E)
        (@TwoColorIncidenceGraph V E G k psi (@RevisitingExtensionCertificate.gamma V E inst
        inst_1 G k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T generating
        ett) e0 (@TashkinovSeries.data V E inst inst_1 inst_3 G k (@ExtendedTashkinovTree.rounds V
        E inst inst_1 inst_3 G k e0 input T generating ett) e0 input
        (@ExtendedTashkinovTree.series V E inst inst_1 inst_3 G k e0 input T generating ett))
        (@Fin.castSucc (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
        generating ett) q) available) (@RevisitingExtensionCertificate.delta V E inst inst_1 G k
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T generating ett) e0
        (@TashkinovSeries.data V E inst inst_1 inst_3 G k (@ExtendedTashkinovTree.rounds V E inst
        inst_1 inst_3 G k e0 input T generating ett) e0 input (@ExtendedTashkinovTree.series V E
        inst inst_1 inst_3 G k e0 input T generating ett)) (@Fin.castSucc
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T generating ett) q)
        available)) (@Sum.inr V E (@RevisitingExtensionCertificate.edge V E inst inst_1 G k
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T generating ett) e0
        (@TashkinovSeries.data V E inst inst_1 inst_3 G k (@ExtendedTashkinovTree.rounds V E inst
        inst_1 inst_3 G k e0 input T generating ett) e0 input (@ExtendedTashkinovTree.series V E
        inst inst_1 inst_3 G k e0 input T generating ett)) (@Fin.castSucc
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T generating ett) q)
        available)) (@Sum.inl V E (@RevisitingExtensionCertificate.returnVertex V E inst inst_1 G
        k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T generating ett) e0
        (@TashkinovSeries.data V E inst inst_1 inst_3 G k (@ExtendedTashkinovTree.rounds V E inst
        inst_1 inst_3 G k e0 input T generating ett) e0 input (@ExtendedTashkinovTree.series V E
        inst inst_1 inst_3 G k e0 input T generating ett)) (@Fin.castSucc
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T generating ett) q)
        available))) → @SimpleGraph.Walk (Sum V E) (@TwoColorIncidenceGraph V E G k phi
        (@RevisitingExtensionCertificate.gamma V E inst inst_1 G k (@ExtendedTashkinovTree.rounds
        V E inst inst_1 inst_3 G k e0 input T generating ett) e0 (@TashkinovSeries.data V E inst
        inst_1 inst_3 G k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
        generating ett) e0 input (@ExtendedTashkinovTree.series V E inst inst_1 inst_3 G k e0
        input T generating ett)) (@Fin.castSucc (@ExtendedTashkinovTree.rounds V E inst inst_1
        inst_3 G k e0 input T generating ett) q) available) (@RevisitingExtensionCertificate.delta
        V E inst inst_1 G k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
        generating ett) e0 (@TashkinovSeries.data V E inst inst_1 inst_3 G k
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T generating ett) e0
        input (@ExtendedTashkinovTree.series V E inst inst_1 inst_3 G k e0 input T generating
        ett)) (@Fin.castSucc (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
        generating ett) q) available)) (@Sum.inr V E (@RevisitingExtensionCertificate.edge V E
        inst inst_1 G k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
        generating ett) e0 (@TashkinovSeries.data V E inst inst_1 inst_3 G k
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T generating ett) e0
        input (@ExtendedTashkinovTree.series V E inst inst_1 inst_3 G k e0 input T generating
        ett)) (@Fin.castSucc (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
        generating ett) q) available)) (@Sum.inl V E (@RevisitingExtensionCertificate.returnVertex
        V E inst inst_1 G k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
        generating ett) e0 (@TashkinovSeries.data V E inst inst_1 inst_3 G k
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T generating ett) e0
        input (@ExtendedTashkinovTree.series V E inst inst_1 inst_3 G k e0 input T generating
        ett)) (@Fin.castSucc (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
        generating ett) q) available))) (fun (P : @SimpleGraph.Walk (Sum V E)
        (@TwoColorIncidenceGraph V E G k phi (@RevisitingExtensionCertificate.gamma V E inst
        inst_1 G k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T generating
        ett) e0 (@TashkinovSeries.data V E inst inst_1 inst_3 G k (@ExtendedTashkinovTree.rounds V
        E inst inst_1 inst_3 G k e0 input T generating ett) e0 input
        (@ExtendedTashkinovTree.series V E inst inst_1 inst_3 G k e0 input T generating ett))
        (@Fin.castSucc (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
        generating ett) q) available) (@RevisitingExtensionCertificate.delta V E inst inst_1 G k
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T generating ett) e0
        (@TashkinovSeries.data V E inst inst_1 inst_3 G k (@ExtendedTashkinovTree.rounds V E inst
        inst_1 inst_3 G k e0 input T generating ett) e0 input (@ExtendedTashkinovTree.series V E
        inst inst_1 inst_3 G k e0 input T generating ett)) (@Fin.castSucc
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T generating ett) q)
        available)) (@Sum.inr V E (@RevisitingExtensionCertificate.edge V E inst inst_1 G k
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T generating ett) e0
        (@TashkinovSeries.data V E inst inst_1 inst_3 G k (@ExtendedTashkinovTree.rounds V E inst
        inst_1 inst_3 G k e0 input T generating ett) e0 input (@ExtendedTashkinovTree.series V E
        inst inst_1 inst_3 G k e0 input T generating ett)) (@Fin.castSucc
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T generating ett) q)
        available)) (@Sum.inl V E (@RevisitingExtensionCertificate.returnVertex V E inst inst_1 G
        k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T generating ett) e0
        (@TashkinovSeries.data V E inst inst_1 inst_3 G k (@ExtendedTashkinovTree.rounds V E inst
        inst_1 inst_3 G k e0 input T generating ett) e0 input (@ExtendedTashkinovTree.series V E
        inst inst_1 inst_3 G k e0 input T generating ett)) (@Fin.castSucc
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T generating ett) q)
        available))) ↦ P) psi hphi P;
    ∀ (_ :
    ∀ (phi psi : PartialEdgeColoring E k) (hphi : phi = psi) (P : (TwoColorIncidenceGraph G psi
        available.gamma available.delta).Walk (Sum.inr available.edge) (Sum.inl
        available.returnVertex)) (z : V ⊕ E), z ∈ (castReturnWalk phi psi hphi P).support ↔ z ∈
        P.support),
    let replacementReturnPath : (TwoColorIncidenceGraph G (corr.replacementSeries.data.coloring
        replacementLast) available.gamma available.delta).Walk (Sum.inr available.edge) (Sum.inl
        available.returnVertex) := castReturnWalk (corr.replacementSeries.data.coloring
        replacementLast) sigma hreplacementColor sigmaReturnPath;
    ∀ (v : V), Sum.inl v ∈ replacementReturnPath.support → v ∈ TreeSequenceVertexSet
        (corr.replacementSeries.data.tree replacementLast.succ)

/-- Dependent contract shared by the revisiting terminal reconstruction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperCaseContinuation2517Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds), LowerRoundInductionHypothesis G
        k e0 ett.rounds →
    ∀ (sigma : PartialEdgeColoring E k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma
        e0 → StableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) (ett.series.data.coloring
        (Fin.last ett.rounds)) sigma →
    ∀ (Tstar : TreeSequence G e0), TreeSequenceInitialSegment (ett.series.data.tree (Fin.last
        ett.rounds).castSucc) Tstar → (ett.series.data.tree (Fin.last ett.rounds).castSucc).length
        < Tstar.length →
    ∀ (fstar : E) (seed : TreeSequence G e0), ett.series.data.connectingEdges (Fin.last
        ett.rounds) = ({ fstar } : Finset E) → TreeSequenceAdjoinEdge (ett.series.data.tree
        (Fin.last ett.rounds).castSucc) fstar seed →
    ∀ (closureTree : TreeSequence G e0), TashkinovClosure sigma seed closureTree →
        TreeSequenceInitialSegment Tstar closureTree → TreeSequenceInitialSegment
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) closureTree →
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), Nat.sub_lt (Nat.zero_lt_of_lt hpositive) (
    by omega
    )⟩ : Fin ett.rounds); q.succ = Fin.last ett.rounds → q.castSucc = (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))) →
    ∀ (adjoined : TreeSequence G e0), IsProperEdgeColoring G (ett.series.data.coloring q.castSucc)
        → IsOneEdgeUncolored (ett.series.data.coloring q.castSucc) e0 → ColoredVertexSetClosed G
        (ett.series.data.coloring q.castSucc) (TreeSequenceVertexSet (ett.series.data.tree
        q.succ.castSucc)) →
    ∀ (available : RevisitingExtensionCertificate ett.series.data q.castSucc),
        ett.series.data.stored q.succ = (insert available.delta ({ available.gamma } : Finset (Fin
        k)) : Finset (Fin k)) → ett.series.data.connectingEdges q.succ = ({ available.edge } :
        Finset E) → ett.series.data.kind q.succ = some TashkinovExtensionKind.RE →
        TreeSequenceAdjoinEdge (ett.series.data.tree q.succ.castSucc) available.edge adjoined →
        StableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (TashkinovStoredColors ett.series.data (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ)))) (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ)))) sigma →
    ∀ (hroundLarge : (1 : ℕ) < ett.rounds) (originalPrefix : ExtendedTashkinovTree G k e0 input
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) (ett.series.data.coloring
        (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ)), (
    ∀ (i : Fin (originalPrefix.rounds + (2 : ℕ))), originalPrefix.series.data.tree i =
        ett.series.data.tree (Fin.castLE (
    by omega
    ) i)) → (
    ∀ (i : Fin (originalPrefix.rounds + (1 : ℕ))), originalPrefix.series.data.coloring i =
        ett.series.data.coloring (Fin.castLE (
    by omega
    ) i) ∧ originalPrefix.series.data.stored i = ett.series.data.stored (Fin.castLE (
    by omega
    ) i) ∧ originalPrefix.series.data.connectingEdges i = ett.series.data.connectingEdges
        (Fin.castLE (
    by omega
    ) i) ∧ originalPrefix.series.data.kind i = ett.series.data.kind (Fin.castLE (
    by omega
    ) i) ∧ TashkinovStoredColors originalPrefix.series.data i = TashkinovStoredColors
        ett.series.data (Fin.castLE (
    by omega
    ) i)) →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigma (ett.series.data.tree
        (Fin.last ett.rounds).castSucc)), corr.replacementSeries.data.tree (Fin.last
        (originalPrefix.rounds + (1 : ℕ))) = ett.series.data.tree (Fin.last ett.rounds).castSucc →
        corr.replacementSeries.data.coloring (Fin.last originalPrefix.rounds) = sigma →
        MaximumProperty corr.replacementETT →
    ∀ (earlierPrefixBound : (↑available.earlier : ℕ) < originalPrefix.rounds + (1 : ℕ)),
    let earlierPrefix : Fin (originalPrefix.rounds + (1 : ℕ)) := (⟨(↑available.earlier : ℕ),
        earlierPrefixBound⟩ : Fin (originalPrefix.rounds + (1 : ℕ))); Fin.castLE (
    by omega
    ) earlierPrefix = available.earlier → (0 : ℕ) < (↑earlierPrefix : ℕ) →
        corr.replacementSeries.data.kind earlierPrefix = some TashkinovExtensionKind.PE →
    ∀ (oldi : Fin ett.rounds) (oldChoice : MaximumDefectiveChoice G e0 (ett.series.data.tree
        oldi.succ.castSucc) (TashkinovStoredColors ett.series.data oldi.castSucc)
        (ett.series.data.coloring oldi.castSucc)) (oldGamma : Fin k) (oldSecond :
        PartialEdgeColoring E k), ett.series.data.coloring oldi.succ = TwoColorComponentSwap G
        oldSecond oldGamma oldChoice.color (Sum.inl oldChoice.vertex) → ett.series.data.stored
        oldi.succ = (insert oldChoice.color ({ oldGamma } : Finset (Fin k)) : Finset (Fin k)) →
        ett.series.data.delta oldi.succ = some oldChoice.color → ett.series.data.gamma oldi.succ =
        some oldGamma → available.earlier = oldi.succ → oldi.succ = available.earlier →
    ∀ (newi : Fin originalPrefix.rounds) (newChoice : MaximumDefectiveChoice G e0
        (corr.replacementSeries.data.tree newi.succ.castSucc) (TashkinovStoredColors
        corr.replacementSeries.data newi.castSucc) (corr.replacementSeries.data.coloring
        newi.castSucc)) (newGamma : Fin k), ParallelExtensionColor corr.replacementSeries.data
        newi.castSucc newChoice.selected newChoice.vertex newGamma →
    ∀ (newSecond : PartialEdgeColoring E k), IsProperEdgeColoring G newSecond → StableColoring
        (corr.replacementSeries.data.tree newi.succ.castSucc) (insert newChoice.color
        (TashkinovStoredColors corr.replacementSeries.data newi.castSucc) : Finset (Fin k))
        newChoice.selected newSecond → TreeExit (corr.replacementSeries.data.tree
        newi.succ.castSucc) newSecond newGamma newChoice.color newChoice.vertex →
        corr.replacementSeries.data.coloring newi.succ = TwoColorComponentSwap G newSecond
        newGamma newChoice.color (Sum.inl newChoice.vertex) → corr.replacementSeries.data.delta
        newi.succ = some newChoice.color → corr.replacementSeries.data.gamma newi.succ = some
        newGamma → earlierPrefix = newi.succ → newi.succ = earlierPrefix →
    ∀ (htree : corr.replacementSeries.data.tree newi.succ.castSucc = ett.series.data.tree
        oldi.succ.castSucc),
    let oldChoiceOnNew : MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree
        newi.succ.castSucc) (TashkinovStoredColors ett.series.data oldi.castSucc)
        (ett.series.data.coloring oldi.castSucc) := transportDefectiveChoice (Eq.symm htree)
        oldChoice; oldChoiceOnNew.vertex = oldChoice.vertex → oldChoiceOnNew.otherEndpoint =
        oldChoice.otherEndpoint → oldChoiceOnNew.color = oldChoice.color →
        ({ oldChoiceOnNew.edge } : Finset E) = ({ newChoice.edge } : Finset E) → (insert
        oldChoiceOnNew.color ({ oldGamma } : Finset (Fin k)) : Finset (Fin k)) = (insert
        newChoice.color ({ newGamma } : Finset (Fin k)) : Finset (Fin k)) →
        s(oldChoiceOnNew.vertex, oldChoiceOnNew.otherEndpoint) = s(newChoice.vertex,
        newChoice.otherEndpoint) → newChoice.vertex = oldChoiceOnNew.vertex → (
    ∀ (X : TreeSequence G e0) (C : Finset (Fin k)) (phi : PartialEdgeColoring E k) (ch :
        MaximumDefectiveChoice G e0 X C phi) (g : Fin k) (second : PartialEdgeColoring E k),
        IsProperEdgeColoring G second → StableColoring X (insert ch.color C : Finset (Fin k))
        ch.selected second → g ∈ MissingColors G ch.selected ch.vertex →
    let post : PartialEdgeColoring E k := TwoColorComponentSwap G second g ch.color (Sum.inl
        ch.vertex); ch.color ∈ MissingColors G post ch.vertex ∧ g ∉ MissingColors G post ch.vertex
        ∧ g ≠ ch.color) → oldChoice.color ∈ MissingColors G (TwoColorComponentSwap G oldSecond
        oldGamma oldChoice.color (Sum.inl oldChoice.vertex)) oldChoice.vertex → oldGamma ∉
        MissingColors G (TwoColorComponentSwap G oldSecond oldGamma oldChoice.color (Sum.inl
        oldChoice.vertex)) oldChoice.vertex → oldGamma ≠ oldChoice.color → Nonempty
        (CorrespondingExtendedTashkinovTree G k e0 ett sigma Tstar)

/-- Dependent contract shared by the revisiting terminal reconstruction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperContinuation2808Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (hlower :
        LowerRoundInductionHypothesis G k e0 ett.rounds) (sigma : PartialEdgeColoring E k)
        (hsigmaProper : IsProperEdgeColoring G sigma) (hsigmaOne : IsOneEdgeUncolored sigma e0)
        (hsigmaStable : StableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) (ett.series.data.coloring
        (Fin.last ett.rounds)) sigma) (Tstar : TreeSequence G e0) (hTnTstar :
        TreeSequenceInitialSegment (ett.series.data.tree (Fin.last ett.rounds).castSucc) Tstar)
        (hstrict : (ett.series.data.tree (Fin.last ett.rounds).castSucc).length < Tstar.length)
        (fstar : E) (seed : TreeSequence G e0) (hfinalEdges : ett.series.data.connectingEdges
        (Fin.last ett.rounds) = ({ fstar } : Finset E)) (hadjoin : TreeSequenceAdjoinEdge
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) fstar seed) (closureTree :
        TreeSequence G e0) (hseedClosure : TashkinovClosure sigma seed closureTree) (hTstarClosure
        : TreeSequenceInitialSegment Tstar closureTree) (hTnClosure : TreeSequenceInitialSegment
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) closureTree),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), Nat.sub_lt (Nat.zero_lt_of_lt hpositive) (
    by omega
    )⟩ : Fin ett.rounds);
    ∀ (hqSucc : q.succ = Fin.last ett.rounds) (hqCast : q.castSucc = (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ)))) (adjoined : TreeSequence G e0) (previousProper :
        IsProperEdgeColoring G (ett.series.data.coloring q.castSucc)) (previousOneUncolored :
        IsOneEdgeUncolored (ett.series.data.coloring q.castSucc) e0) (previousClosed :
        ColoredVertexSetClosed G (ett.series.data.coloring q.castSucc) (TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc))) (available : RevisitingExtensionCertificate
        ett.series.data q.castSucc) (currentStored : ett.series.data.stored q.succ = (insert
        available.delta ({ available.gamma } : Finset (Fin k)) : Finset (Fin k))) (currentEdges :
        ett.series.data.connectingEdges q.succ = ({ available.edge } : Finset E)) (currentKind :
        ett.series.data.kind q.succ = some TashkinovExtensionKind.RE) (adjoinedExactly :
        TreeSequenceAdjoinEdge (ett.series.data.tree q.succ.castSucc) available.edge adjoined)
        (hsigmaPrevStable : StableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (TashkinovStoredColors ett.series.data (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ)))) (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ)))) sigma) (hroundLarge : (1 : ℕ) < ett.rounds) (originalPrefix :
        ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ))
        (hprefixTrees :
    ∀ (i : Fin (originalPrefix.rounds + (2 : ℕ))), originalPrefix.series.data.tree i =
        ett.series.data.tree (Fin.castLE (
    by omega
    ) i)) (hprefixData :
    ∀ (i : Fin (originalPrefix.rounds + (1 : ℕ))), originalPrefix.series.data.coloring i =
        ett.series.data.coloring (Fin.castLE (
    by omega
    ) i) ∧ originalPrefix.series.data.stored i = ett.series.data.stored (Fin.castLE (
    by omega
    ) i) ∧ originalPrefix.series.data.connectingEdges i = ett.series.data.connectingEdges
        (Fin.castLE (
    by omega
    ) i) ∧ originalPrefix.series.data.kind i = ett.series.data.kind (Fin.castLE (
    by omega
    ) i) ∧ TashkinovStoredColors originalPrefix.series.data i = TashkinovStoredColors
        ett.series.data (Fin.castLE (
    by omega
    ) i)) (corr : CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigma
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)) (hcorrFinalTree :
        corr.replacementSeries.data.tree (Fin.last (originalPrefix.rounds + (1 : ℕ))) =
        ett.series.data.tree (Fin.last ett.rounds).castSucc) (hcorrFinalColor :
        corr.replacementSeries.data.coloring (Fin.last originalPrefix.rounds) = sigma) (hcorrMP :
        MaximumProperty corr.replacementETT) (earlierPrefixBound : (↑available.earlier : ℕ) <
        originalPrefix.rounds + (1 : ℕ)),
    let earlierPrefix : Fin (originalPrefix.rounds + (1 : ℕ)) := (⟨(↑available.earlier : ℕ),
        earlierPrefixBound⟩ : Fin (originalPrefix.rounds + (1 : ℕ)));
    ∀ (hearlierMap : Fin.castLE (
    by omega
    ) earlierPrefix = available.earlier) (hearlierPositive : (0 : ℕ) < (↑earlierPrefix : ℕ))
        (hreplacementEarlierKind : corr.replacementSeries.data.kind earlierPrefix = some
        TashkinovExtensionKind.PE) (oldi : Fin ett.rounds) (oldChoice : MaximumDefectiveChoice G
        e0 (ett.series.data.tree oldi.succ.castSucc) (TashkinovStoredColors ett.series.data
        oldi.castSucc) (ett.series.data.coloring oldi.castSucc)) (oldGamma : Fin k)
        (oldCurrentStored : ett.series.data.stored oldi.succ = (insert oldChoice.color
        ({ oldGamma } : Finset (Fin k)) : Finset (Fin k))) (holdTarget : available.earlier =
        oldi.succ) (holdIndex : oldi.succ = available.earlier) (newi : Fin originalPrefix.rounds)
        (newChoice : MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree
        newi.succ.castSucc) (TashkinovStoredColors corr.replacementSeries.data newi.castSucc)
        (corr.replacementSeries.data.coloring newi.castSucc)) (newGamma : Fin k) (newGammaRule :
        ParallelExtensionColor corr.replacementSeries.data newi.castSucc newChoice.selected
        newChoice.vertex newGamma) (newSecond : PartialEdgeColoring E k) (newSecondProper :
        IsProperEdgeColoring G newSecond) (newSecondStable : StableColoring
        (corr.replacementSeries.data.tree newi.succ.castSucc) (insert newChoice.color
        (TashkinovStoredColors corr.replacementSeries.data newi.castSucc) : Finset (Fin k))
        newChoice.selected newSecond) (newExit : TreeExit (corr.replacementSeries.data.tree
        newi.succ.castSucc) newSecond newGamma newChoice.color newChoice.vertex)
        (newCurrentColoring : corr.replacementSeries.data.coloring newi.succ =
        TwoColorComponentSwap G newSecond newGamma newChoice.color (Sum.inl newChoice.vertex))
        (newCurrentDelta : corr.replacementSeries.data.delta newi.succ = some newChoice.color)
        (newCurrentGamma : corr.replacementSeries.data.gamma newi.succ = some newGamma)
        (hnewTarget : earlierPrefix = newi.succ) (hnewIndex : newi.succ = earlierPrefix) (htree :
        corr.replacementSeries.data.tree newi.succ.castSucc = ett.series.data.tree
        oldi.succ.castSucc),
    let oldChoiceOnNew : MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree
        newi.succ.castSucc) (TashkinovStoredColors ett.series.data oldi.castSucc)
        (ett.series.data.coloring oldi.castSucc) := transportDefectiveChoice (Eq.symm htree)
        oldChoice;
    ∀ (holdColorCast : oldChoiceOnNew.color = oldChoice.color) (hends : s(oldChoiceOnNew.vertex,
        oldChoiceOnNew.otherEndpoint) = s(newChoice.vertex, newChoice.otherEndpoint))
        (holdDeltaMissing : oldChoice.color ∈ MissingColors G (ett.series.data.coloring oldi.succ)
        oldChoice.vertex) (holdColorNe : oldGamma ≠ oldChoice.color) (hnewDeltaMissing :
        newChoice.color ∈ MissingColors G (corr.replacementSeries.data.coloring newi.succ)
        newChoice.vertex) (hnewGammaNotMissing : newGamma ∉ MissingColors G
        (corr.replacementSeries.data.coloring newi.succ) newChoice.vertex) (hnewColorNe : newGamma
        ≠ newChoice.color) (hidentifiedDelta : newChoice.color = oldChoiceOnNew.color)
        (hidentifiedGamma : newGamma = oldGamma) (holdDeltaAvailable : oldChoice.color =
        available.delta) (holdGammaAvailable : oldGamma = available.gamma) (hnewDeltaAvailable :
        newChoice.color = available.delta) (hnewGammaAvailable : newGamma = available.gamma)
        (hnewVertexOld : newChoice.vertex = oldChoice.vertex) (holdColorConstant :
        ett.series.data.coloring q.castSucc = ett.series.data.coloring oldi.succ),
    let replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last originalPrefix.rounds;
    ∀ (hreplacementLastMap : Fin.castLE (
    by omega
    ) replacementLast = q.castSucc) (hreplacementColorConstant :
        corr.replacementSeries.data.coloring replacementLast =
        corr.replacementSeries.data.coloring newi.succ), Nonempty
        (CorrespondingExtendedTashkinovTree G k e0 ett sigma Tstar)

/-- Dependent contract shared by the revisiting terminal reconstruction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperContinuation3509Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (hlower :
        LowerRoundInductionHypothesis G k e0 ett.rounds) (sigma : PartialEdgeColoring E k)
        (hsigmaProper : IsProperEdgeColoring G sigma) (hsigmaOne : IsOneEdgeUncolored sigma e0)
        (hsigmaStable : StableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) (ett.series.data.coloring
        (Fin.last ett.rounds)) sigma) (Tstar : TreeSequence G e0) (hTnTstar :
        TreeSequenceInitialSegment (ett.series.data.tree (Fin.last ett.rounds).castSucc) Tstar)
        (hstrict : (ett.series.data.tree (Fin.last ett.rounds).castSucc).length < Tstar.length)
        (fstar : E) (seed : TreeSequence G e0) (hfinalEdges : ett.series.data.connectingEdges
        (Fin.last ett.rounds) = ({ fstar } : Finset E)) (hadjoin : TreeSequenceAdjoinEdge
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) fstar seed) (closureTree :
        TreeSequence G e0) (hseedClosure : TashkinovClosure sigma seed closureTree) (hTstarClosure
        : TreeSequenceInitialSegment Tstar closureTree) (hTnClosure : TreeSequenceInitialSegment
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) closureTree),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), Nat.sub_lt (Nat.zero_lt_of_lt hpositive) (
    by omega
    )⟩ : Fin ett.rounds);
    ∀ (hqSucc : q.succ = Fin.last ett.rounds) (hqCast : q.castSucc = (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ)))) (adjoined : TreeSequence G e0) (previousProper :
        IsProperEdgeColoring G (ett.series.data.coloring q.castSucc)) (previousOneUncolored :
        IsOneEdgeUncolored (ett.series.data.coloring q.castSucc) e0) (previousClosed :
        ColoredVertexSetClosed G (ett.series.data.coloring q.castSucc) (TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc))) (available : RevisitingExtensionCertificate
        ett.series.data q.castSucc) (currentStored : ett.series.data.stored q.succ = (insert
        available.delta ({ available.gamma } : Finset (Fin k)) : Finset (Fin k))) (currentEdges :
        ett.series.data.connectingEdges q.succ = ({ available.edge } : Finset E)) (currentKind :
        ett.series.data.kind q.succ = some TashkinovExtensionKind.RE) (hroundLarge : (1 : ℕ) <
        ett.rounds) (originalPrefix : ExtendedTashkinovTree G k e0 input (ett.series.data.tree
        (Fin.last ett.rounds).castSucc) (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ))
        (hprefixTrees :
    ∀ (i : Fin (originalPrefix.rounds + (2 : ℕ))), originalPrefix.series.data.tree i =
        ett.series.data.tree (Fin.castLE (
    by omega
    ) i)) (hprefixData :
    ∀ (i : Fin (originalPrefix.rounds + (1 : ℕ))), originalPrefix.series.data.coloring i =
        ett.series.data.coloring (Fin.castLE (
    by omega
    ) i) ∧ originalPrefix.series.data.stored i = ett.series.data.stored (Fin.castLE (
    by omega
    ) i) ∧ originalPrefix.series.data.connectingEdges i = ett.series.data.connectingEdges
        (Fin.castLE (
    by omega
    ) i) ∧ originalPrefix.series.data.kind i = ett.series.data.kind (Fin.castLE (
    by omega
    ) i) ∧ TashkinovStoredColors originalPrefix.series.data i = TashkinovStoredColors
        ett.series.data (Fin.castLE (
    by omega
    ) i)) (corr : CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigma
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)) (hcorrFinalTree :
        corr.replacementSeries.data.tree (Fin.last (originalPrefix.rounds + (1 : ℕ))) =
        ett.series.data.tree (Fin.last ett.rounds).castSucc) (hcorrFinalColor :
        corr.replacementSeries.data.coloring (Fin.last originalPrefix.rounds) = sigma) (hcorrMP :
        MaximumProperty corr.replacementETT) (earlierPrefixBound : (↑available.earlier : ℕ) <
        originalPrefix.rounds + (1 : ℕ)),
    let earlierPrefix : Fin (originalPrefix.rounds + (1 : ℕ)) := (⟨(↑available.earlier : ℕ),
        earlierPrefixBound⟩ : Fin (originalPrefix.rounds + (1 : ℕ)));
    ∀ (hearlierMap : Fin.castLE (
    by omega
    ) earlierPrefix = available.earlier) (hearlierPositive : (0 : ℕ) < (↑earlierPrefix : ℕ))
        (hreplacementEarlierKind : corr.replacementSeries.data.kind earlierPrefix = some
        TashkinovExtensionKind.PE) (oldi : Fin ett.rounds) (oldChoice : MaximumDefectiveChoice G
        e0 (ett.series.data.tree oldi.succ.castSucc) (TashkinovStoredColors ett.series.data
        oldi.castSucc) (ett.series.data.coloring oldi.castSucc)) (oldGamma : Fin k) (holdTarget :
        available.earlier = oldi.succ) (holdIndex : oldi.succ = available.earlier) (newi : Fin
        originalPrefix.rounds) (newChoice : MaximumDefectiveChoice G e0
        (corr.replacementSeries.data.tree newi.succ.castSucc) (TashkinovStoredColors
        corr.replacementSeries.data newi.castSucc) (corr.replacementSeries.data.coloring
        newi.castSucc)) (newGamma : Fin k) (newGammaRule : ParallelExtensionColor
        corr.replacementSeries.data newi.castSucc newChoice.selected newChoice.vertex newGamma)
        (newSecond : PartialEdgeColoring E k) (newSecondProper : IsProperEdgeColoring G newSecond)
        (newSecondStable : StableColoring (corr.replacementSeries.data.tree newi.succ.castSucc)
        (insert newChoice.color (TashkinovStoredColors corr.replacementSeries.data newi.castSucc)
        : Finset (Fin k)) newChoice.selected newSecond) (newExit : TreeExit
        (corr.replacementSeries.data.tree newi.succ.castSucc) newSecond newGamma newChoice.color
        newChoice.vertex) (newCurrentColoring : corr.replacementSeries.data.coloring newi.succ =
        TwoColorComponentSwap G newSecond newGamma newChoice.color (Sum.inl newChoice.vertex))
        (newCurrentDelta : corr.replacementSeries.data.delta newi.succ = some newChoice.color)
        (newCurrentGamma : corr.replacementSeries.data.gamma newi.succ = some newGamma) (hnewIndex
        : newi.succ = earlierPrefix) (htree : corr.replacementSeries.data.tree newi.succ.castSucc
        = ett.series.data.tree oldi.succ.castSucc),
    let oldChoiceOnNew : MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree
        newi.succ.castSucc) (TashkinovStoredColors ett.series.data oldi.castSucc)
        (ett.series.data.coloring oldi.castSucc) := transportDefectiveChoice (Eq.symm htree)
        oldChoice;
    ∀ (holdColorCast : oldChoiceOnNew.color = oldChoice.color) (hends : s(oldChoiceOnNew.vertex,
        oldChoiceOnNew.otherEndpoint) = s(newChoice.vertex, newChoice.otherEndpoint))
        (holdDeltaMissing : oldChoice.color ∈ MissingColors G (ett.series.data.coloring oldi.succ)
        oldChoice.vertex) (holdColorNe : oldGamma ≠ oldChoice.color) (hnewColorNe : newGamma ≠
        newChoice.color) (hidentifiedDelta : newChoice.color = oldChoiceOnNew.color)
        (hidentifiedGamma : newGamma = oldGamma) (holdDeltaAvailable : oldChoice.color =
        available.delta) (holdGammaAvailable : oldGamma = available.gamma) (hnewDeltaAvailable :
        newChoice.color = available.delta) (hnewGammaAvailable : newGamma = available.gamma)
        (hnewVertexOld : newChoice.vertex = oldChoice.vertex) (holdColorConstant :
        ett.series.data.coloring q.castSucc = ett.series.data.coloring oldi.succ),
    let replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last originalPrefix.rounds;
    ∀ (hreplacementLastMap : Fin.castLE (
    by omega
    ) replacementLast = q.castSucc) (hnewPostSigma : corr.replacementSeries.data.coloring
        newi.succ = sigma) (hnewDeltaSigma : available.delta ∈ MissingColors G sigma
        newChoice.vertex) (hgammaDeltaNe : available.gamma ≠ available.delta) (hnewTreeFinal :
        TreeSequenceInitialSegment (corr.replacementSeries.data.tree newi.succ.castSucc)
        (corr.replacementSeries.data.tree (Fin.last (originalPrefix.rounds + (1 : ℕ)))))
        (hnewVertexTn : newChoice.vertex ∈ TreeSequenceVertexSet (ett.series.data.tree (Fin.last
        ett.rounds).castSucc)) (hpathComponent : TwoColorNontrivialPathComponent G sigma
        available.gamma available.delta (Sum.inl newChoice.vertex)) (hpathMeetsTn :
    ∃ v ∈ TreeSequenceVertexSet (ett.series.data.tree (Fin.last ett.rounds).castSucc), Sum.inl v ∈
        TwoColorComponent G sigma available.gamma available.delta (Sum.inl newChoice.vertex))
        (hsigmaPrevStableQ : StableColoring (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)
        sigma) (hgammaEarlierStored : available.gamma ∈ ett.series.data.stored available.earlier)
        (hdeltaEarlierStored : available.delta ∈ ett.series.data.stored available.earlier)
        (colorControlAtQ :
    ∀ (c : Fin k) (hc : c ∈ ett.series.data.stored available.earlier), c ∈ TreeMissingColors
        (ett.series.data.coloring q.castSucc) (ett.series.data.tree q.succ.castSucc) ∪
        TashkinovStoredColors ett.series.data q.castSucc), Nonempty
        (CorrespondingExtendedTashkinovTree G k e0 ett sigma Tstar)

/-- Dependent contract shared by the revisiting terminal reconstruction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperInterveningRevisiting4368Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (Tstar : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (hqCast : q.castSucc = (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ)))) (available : RevisitingExtensionCertificate ett.series.data
        q.castSucc) (hroundLarge : (1 : ℕ) < ett.rounds) (originalPrefix : ExtendedTashkinovTree G
        k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc) (ett.series.data.coloring
        (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ))
        (hprefixData :
    ∀ (i : Fin (originalPrefix.rounds + (1 : ℕ))), originalPrefix.series.data.coloring i =
        ett.series.data.coloring (Fin.castLE (
    by omega
    ) i) ∧ originalPrefix.series.data.stored i = ett.series.data.stored (Fin.castLE (
    by omega
    ) i) ∧ originalPrefix.series.data.connectingEdges i = ett.series.data.connectingEdges
        (Fin.castLE (
    by omega
    ) i) ∧ originalPrefix.series.data.kind i = ett.series.data.kind (Fin.castLE (
    by omega
    ) i) ∧ TashkinovStoredColors originalPrefix.series.data i = TashkinovStoredColors
        ett.series.data (Fin.castLE (
    by omega
    ) i)) (corr : CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigma
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)) (earlierPrefixBound :
        (↑available.earlier : ℕ) < originalPrefix.rounds + (1 : ℕ)),
    let earlierPrefix : Fin (originalPrefix.rounds + (1 : ℕ)) := (⟨(↑available.earlier : ℕ),
        earlierPrefixBound⟩ : Fin (originalPrefix.rounds + (1 : ℕ)));
    ∀ (hearlierMap : Fin.castLE (
    by omega
    ) earlierPrefix = available.earlier) (oldi : Fin ett.rounds) (oldChoice :
        MaximumDefectiveChoice G e0 (ett.series.data.tree oldi.succ.castSucc)
        (TashkinovStoredColors ett.series.data oldi.castSucc) (ett.series.data.coloring
        oldi.castSucc)) (oldGamma : Fin k) (newi : Fin originalPrefix.rounds) (newChoice :
        MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree newi.succ.castSucc)
        (TashkinovStoredColors corr.replacementSeries.data newi.castSucc)
        (corr.replacementSeries.data.coloring newi.castSucc)) (newGamma : Fin k) (htree :
        corr.replacementSeries.data.tree newi.succ.castSucc = ett.series.data.tree
        oldi.succ.castSucc),
    let oldChoiceOnNew : MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree
        newi.succ.castSucc) (TashkinovStoredColors ett.series.data oldi.castSucc)
        (ett.series.data.coloring oldi.castSucc) := transportDefectiveChoice (Eq.symm htree)
        oldChoice;
    ∀ (holdColorCast : oldChoiceOnNew.color = oldChoice.color) (holdColorNe : oldGamma ≠
        oldChoice.color) (hnewColorNe : newGamma ≠ newChoice.color) (hidentifiedDelta :
        newChoice.color = oldChoiceOnNew.color) (hidentifiedGamma : newGamma = oldGamma)
        (holdDeltaAvailable : oldChoice.color = available.delta) (holdGammaAvailable : oldGamma =
        available.gamma),
    let replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last originalPrefix.rounds;
    ∀ (hreplacementLastMap : Fin.castLE (
    by omega
    ) replacementLast = q.castSucc) (hgammaDeltaNe : available.gamma ≠ available.delta)
        (replacementCycle : TwoColorCycle G sigma available.gamma available.delta),
    let currentTree : Finset V := TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc);
    ∀ (hreturnCycle : Sum.inl available.returnVertex ∈ replacementCycle.walk.support),
    let rootedCycle : (TwoColorIncidenceGraph G sigma available.gamma available.delta).Walk
        (Sum.inl available.returnVertex) (Sum.inl available.returnVertex) :=
        replacementCycle.walk.rotate (Sum.inl available.returnVertex) hreturnCycle;
    let outsideIndices : Finset (Fin (rootedCycle.length + (1 : ℕ))) := ({i : Fin
        (rootedCycle.length + (1 : ℕ)) |
    ∃ (v : V), rootedCycle.getVert (↑i : ℕ) = Sum.inl v ∧ v ∉ currentTree} : Finset (Fin
        (rootedCycle.length + (1 : ℕ))));
    ∀ (outsideIndicesNonempty : outsideIndices.Nonempty),
    let firstOutside : Fin (rootedCycle.length + (1 : ℕ)) := outsideIndices.min'
        outsideIndicesNonempty;
    ∀ (firstOutsideNotOne : (↑firstOutside : ℕ) ≠ (1 : ℕ)) (firstOutsideAtLeastTwo : (2 : ℕ) ≤
        (↑firstOutside : ℕ)) (firstCrossingIndex : (↑firstOutside : ℕ) - (1 : ℕ) + (1 : ℕ) =
        (↑firstOutside : ℕ)) (beforeFirstCrossingIndex : (↑firstOutside : ℕ) - (2 : ℕ) + (1 : ℕ) =
        (↑firstOutside : ℕ) - (1 : ℕ)),
    let laterInsideIndices : Finset (Fin (rootedCycle.length + (1 : ℕ))) := ({idx : Fin
        (rootedCycle.length + (1 : ℕ)) | (↑firstOutside : ℕ) < (↑idx : ℕ) ∧
    ∃ (v : V), rootedCycle.getVert (↑idx : ℕ) = Sum.inl v ∧ v ∈ currentTree} : Finset (Fin
        (rootedCycle.length + (1 : ℕ))));
    ∀ (laterInsideNonempty : laterInsideIndices.Nonempty),
    let firstReturn : Fin (rootedCycle.length + (1 : ℕ)) := laterInsideIndices.min'
        laterInsideNonempty;
    ∀ (hreturnNotNext : (↑firstReturn : ℕ) ≠ (↑firstOutside : ℕ) + (1 : ℕ)) (hreturnGap :
        (↑firstOutside : ℕ) + (2 : ℕ) ≤ (↑firstReturn : ℕ)) (returnCrossingIndex : (↑firstReturn :
        ℕ) - (1 : ℕ) + (1 : ℕ) = (↑firstReturn : ℕ)) (beforeReturnCrossingIndex : (↑firstReturn :
        ℕ) - (2 : ℕ) + (1 : ℕ) = (↑firstReturn : ℕ) - (1 : ℕ)) (j : Fin (originalPrefix.rounds +
        (1 : ℕ))), (0 : ℕ) < (↑j : ℕ) → (↑earlierPrefix : ℕ) < (↑j : ℕ) → (↑j : ℕ) ≤
        (↑replacementLast : ℕ) → corr.replacementSeries.data.kind j = some
        TashkinovExtensionKind.RE

theorem helper_hTnClosure_110.{u_1, u_2} :
    open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
        (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
        (ett : ExtendedTashkinovTree G k e0 input T generating) (Tstar : TreeSequence G e0),
        TreeSequenceInitialSegment (ett.series.data.tree (Fin.last ett.rounds).castSucc) Tstar →
          ∀ (closureTree : TreeSequence G e0),
            TreeSequenceInitialSegment Tstar closureTree →
              TreeSequenceInitialSegment (ett.series.data.tree (Fin.last ett.rounds).castSucc)
                closureTree := by
  classical
  intro V E _ _ _ G k e0 input T generating ett Tstar hTnTstar closureTree hTstarClosure
  rcases hTnTstar with ⟨hlenAB, hvertexAB, hedgeAB⟩
  rcases hTstarClosure with ⟨hlenBC, hvertexBC, hedgeBC⟩
  refine ⟨Nat.le_trans hlenAB hlenBC, ?_, ?_⟩
  · intro j
    calc
      closureTree.vertex (Fin.castLE (Nat.succ_le_succ (Nat.le_trans hlenAB hlenBC)) j) =
          closureTree.vertex
            (Fin.castLE (Nat.succ_le_succ hlenBC) (Fin.castLE (Nat.succ_le_succ hlenAB) j)) :=
        by congr 1
      _ = Tstar.vertex (Fin.castLE (Nat.succ_le_succ hlenAB) j) := hvertexBC _
      _ = (ett.series.data.tree (Fin.last ett.rounds).castSucc).vertex j := hvertexAB j
  · intro j
    calc
      closureTree.edge (Fin.castLE (Nat.le_trans hlenAB hlenBC) j) =
          closureTree.edge (Fin.castLE hlenBC (Fin.castLE hlenAB j)) :=
        by congr 1
      _ = Tstar.edge (Fin.castLE hlenAB j) := hedgeBC _
      _ = (ett.series.data.tree (Fin.last ett.rounds).castSucc).edge j := hedgeAB j

theorem helper_reStepColoring_588.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (adjoined : TreeSequence G e0) (available : RevisitingExtensionCertificate ett.series.data
        q.castSucc), TreeSequenceAdjoinEdge (ett.series.data.tree q.succ.castSucc) available.edge
        adjoined → (1 : ℕ) < ett.rounds →
    ∀ (originalPrefix : ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last
        ett.rounds).castSucc) (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))), originalPrefix.rounds = ett.rounds - (1 : ℕ) →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigma (ett.series.data.tree
        (Fin.last ett.rounds).castSucc)) (oldi : Fin ett.rounds) (_ : MaximumDefectiveChoice G e0
        (ett.series.data.tree oldi.succ.castSucc) (TashkinovStoredColors ett.series.data
        oldi.castSucc) (ett.series.data.coloring oldi.castSucc)) (_ : Fin k) (newi : Fin
        originalPrefix.rounds) (_ : MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree
        newi.succ.castSucc) (TashkinovStoredColors corr.replacementSeries.data newi.castSucc)
        (corr.replacementSeries.data.coloring newi.castSucc)) (_ : Fin k),
        corr.replacementSeries.data.tree newi.succ.castSucc = ett.series.data.tree
        oldi.succ.castSucc →
    ∀ {rounds' : ℕ} {input' : PartialEdgeColoring E k} (series : TashkinovSeries G k rounds' e0
        input') (j : Fin rounds'), series.data.kind j.succ = some TashkinovExtensionKind.RE →
        series.data.coloring j.succ = series.data.coloring j.castSucc := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma _ q adjoined available
    adjoinedExactly hroundLarge originalPrefix hr corr oldi oldChoice oldGamma newi newChoice
    newGamma htree rounds' input' series j hj
  have hstep := series.certified j.succ
  generalize hslot : j.succ = slot at hstep
  cases hstep with
  | initial triple seedLength initialColoring initialStored initialEdges initialKind initialVertex
    initialOutside initialDelta initialGamma initialClosure => exact (Fin.succ_ne_zero j hslot).elim
  | SE i prevProper prevOne prevClosed prevNotStrong noRE choice alternative coloring stored edges
    kind vertex outside delta gamma adjoined adjoinedExactly closed ordered
    strict =>
    have hbad := kind.symm.trans (by simpa [hslot] using hj)
    cases hbad
  | PE i prevProper prevOne prevClosed prevNotStrong noRE choice alternativeFails gamma gammaRule
    second secondProper secondOne secondStable exit coloring coloringProper coloringOne stored edges
    kind vertex outside delta gammaValue closed ordered
    strict =>
    have hbad := kind.symm.trans (by simpa [hslot] using hj)
    cases hbad
  | RE i prevProper prevOne prevClosed prevNotStrong cert coloring stored edges kind vertex outside
    delta gamma adjoined adjoinedExactly closed ordered
    strict =>
    have hi : i = j := by
      apply Fin.ext
      have hv := congrArg Fin.val hslot
      simp only [Fin.val_succ] at hv
      omega
    subst i
    simpa [hslot] using coloring

theorem helper_reIntervalColoring_625.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (_ : RevisitingExtensionCertificate ett.series.data q.castSucc), (1 : ℕ) < ett.rounds →
    ∀ (originalPrefix : ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last
        ett.rounds).castSucc) (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))), originalPrefix.rounds = ett.rounds - (1 : ℕ) →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigma (ett.series.data.tree
        (Fin.last ett.rounds).castSucc)) (oldi : Fin ett.rounds) (_ : MaximumDefectiveChoice G e0
        (ett.series.data.tree oldi.succ.castSucc) (TashkinovStoredColors ett.series.data
        oldi.castSucc) (ett.series.data.coloring oldi.castSucc)) (_ : Fin k) (newi : Fin
        originalPrefix.rounds) (_ : MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree
        newi.succ.castSucc) (TashkinovStoredColors corr.replacementSeries.data newi.castSucc)
        (corr.replacementSeries.data.coloring newi.castSucc)) (_ : Fin k),
        corr.replacementSeries.data.tree newi.succ.castSucc = ett.series.data.tree
        oldi.succ.castSucc → (
    ∀ {rounds' : ℕ} {input' : PartialEdgeColoring E k} (series : TashkinovSeries G k rounds' e0
        input') (j : Fin rounds'), series.data.kind j.succ = some TashkinovExtensionKind.RE →
        series.data.coloring j.succ = series.data.coloring j.castSucc) →
    ∀ {rounds' : ℕ} {input' : PartialEdgeColoring E k} (series : TashkinovSeries G k rounds' e0
        input') (a b : Fin (rounds' + (1 : ℕ))), (↑a : ℕ) ≤ (↑b : ℕ) → (
    ∀ (j : Fin (rounds' + (1 : ℕ))), (↑a : ℕ) < (↑j : ℕ) → (↑j : ℕ) ≤ (↑b : ℕ) → series.data.kind
        j = some TashkinovExtensionKind.RE) → series.data.coloring b = series.data.coloring a := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma _ q available hroundLarge
    originalPrefix hr corr oldi oldChoice oldGamma newi newChoice newGamma htree reStepColoring
    rounds' input' series a b hab hbetween
  have coloringAlong :
    ∀ m : ℕ, a.val ≤ m → m ≤ b.val →
    ∀ x : Fin (rounds' + 1), x.val = m → series.data.coloring x = series.data.coloring a := by
    intro m ham
    induction m, ham using Nat.le_induction with
    | base =>
      intro hmb x hx
      have hxa : x = a := by
        apply Fin.ext
        omega
      rw [hxa]
    | succ m ham ih =>
      intro hmb x hx
      let j : Fin rounds' :=
        ⟨m, by
          have hbLt := b.isLt
          omega⟩
      have hjKind : series.data.kind j.succ = some TashkinovExtensionKind.RE := by
        apply hbetween j.succ
        · simp [j]
          omega
        · simp [j]
          omega
      have hstep := reStepColoring series j hjKind
      have hxj : x = j.succ := by
        apply Fin.ext
        simp [j, hx]
      calc
        series.data.coloring x = series.data.coloring j.succ := by rw [hxj]
        _ = series.data.coloring j.castSucc := hstep
        _ = series.data.coloring a := ih (by omega) j.castSucc (by simp [j])
  exact coloringAlong b.val hab le_rfl b rfl

theorem helper_holdColorConstant_669.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds); q.castSucc = (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))) →
    ∀ (available : RevisitingExtensionCertificate ett.series.data q.castSucc), (1 : ℕ) <
        ett.rounds →
    ∀ (originalPrefix : ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last
        ett.rounds).castSucc) (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))), originalPrefix.rounds = ett.rounds - (1 : ℕ) →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigma (ett.series.data.tree
        (Fin.last ett.rounds).castSucc)) (oldi : Fin ett.rounds) (_ : MaximumDefectiveChoice G e0
        (ett.series.data.tree oldi.succ.castSucc) (TashkinovStoredColors ett.series.data
        oldi.castSucc) (ett.series.data.coloring oldi.castSucc)) (_ : Fin k), available.earlier =
        oldi.succ → oldi.succ = available.earlier →
    ∀ (newi : Fin originalPrefix.rounds) (_ : MaximumDefectiveChoice G e0
        (corr.replacementSeries.data.tree newi.succ.castSucc) (TashkinovStoredColors
        corr.replacementSeries.data newi.castSucc) (corr.replacementSeries.data.coloring
        newi.castSucc)) (_ : Fin k), corr.replacementSeries.data.tree newi.succ.castSucc =
        ett.series.data.tree oldi.succ.castSucc → (
    ∀ {rounds' : ℕ} {input' : PartialEdgeColoring E k} (series : TashkinovSeries G k rounds' e0
        input') (a b : Fin (rounds' + (1 : ℕ))), (↑a : ℕ) ≤ (↑b : ℕ) → (
    ∀ (j : Fin (rounds' + (1 : ℕ))), (↑a : ℕ) < (↑j : ℕ) → (↑j : ℕ) ≤ (↑b : ℕ) → series.data.kind
        j = some TashkinovExtensionKind.RE) → series.data.coloring b = series.data.coloring a) →
        ett.series.data.coloring q.castSucc = ett.series.data.coloring oldi.succ := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma _ q hqCast available hroundLarge
    originalPrefix hr corr oldi oldChoice oldGamma holdTarget holdIndex newi newChoice newGamma
    htree reIntervalColoring
  apply reIntervalColoring ett.series oldi.succ q.castSucc
  · have hvals := congrArg Fin.val holdIndex
    have hle := available.earlierAtMost
    simp only [Fin.val_succ] at hvals
    omega
  · intro j hjLower hjUpper
    apply available.interveningRevisiting j
    · have holdPositive := available.earlierPositive
      have hvals := congrArg Fin.val holdIndex
      simp only [Fin.val_succ] at hvals
      omega
    · have hvals := congrArg Fin.val holdIndex
      simp only [Fin.val_succ] at hvals
      omega
    · exact hjUpper

theorem helper_segmentTrans_778.{u_1, u_2} :
    open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
        (A B C : TreeSequence G e0),
        TreeSequenceInitialSegment A B →
          TreeSequenceInitialSegment B C → TreeSequenceInitialSegment A C := by
  classical
  intro V E G e0 A B C hAB hBC
  rcases hAB with ⟨hlenAB, hvertexAB, hedgeAB⟩
  rcases hBC with ⟨hlenBC, hvertexBC, hedgeBC⟩
  refine ⟨hlenAB.trans hlenBC, ?_, ?_⟩
  · intro x
    calc
      C.vertex (Fin.castLE (Nat.succ_le_succ (hlenAB.trans hlenBC)) x) =
          C.vertex
            (Fin.castLE (Nat.succ_le_succ hlenBC) (Fin.castLE (Nat.succ_le_succ hlenAB) x)) :=
        by congr 1
      _ = B.vertex (Fin.castLE (Nat.succ_le_succ hlenAB) x) := hvertexBC _
      _ = A.vertex x := hvertexAB x
  · intro x
    calc
      C.edge (Fin.castLE (hlenAB.trans hlenBC) x) =
          C.edge (Fin.castLE hlenBC (Fin.castLE hlenAB x)) :=
        by congr 1
      _ = B.edge (Fin.castLE hlenAB x) := hedgeBC _
      _ = A.edge x := hedgeAB x

theorem helper_oldReturnEdgeData_978.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (available : RevisitingExtensionCertificate ett.series.data q.castSucc),
        ¬available.returnPath.Nil →
    ∀ (f : E), Sum.inr f ∈ available.returnPath.support → TreeIncidentEdge (ett.series.data.tree
        q.succ.castSucc) f ∧ (ett.series.data.coloring q.castSucc f = some available.gamma ∨
        ett.series.data.coloring q.castSucc f = some available.delta) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ q available hreturnNotNil f hf
  obtain ⟨node, hnode, hadj⟩ :=
    SimpleGraph.adj_of_mem_walk_support available.returnPath hreturnNotNil hf
  cases node with
  | inl
    v =>
    have hdata :
      Incident G v f ∧
        (ett.series.data.coloring q.castSucc f = some available.gamma ∨
          ett.series.data.coloring q.castSucc f = some available.delta) :=
      by simpa [TwoColorIncidenceGraph] using hadj
    exact ⟨⟨v, available.returnPathInternal v hnode, hdata.1⟩, hdata.2⟩
  | inr g => simp [TwoColorIncidenceGraph] at hadj

theorem helper_returnEdgeTransfer_1018.{u_1, u_2} :
    open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
        [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
        (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
        (generating : PartialEdgeColoring E k)
        (ett : ExtendedTashkinovTree G k e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds)
        (sigma : PartialEdgeColoring E k) (_ : TreeSequence G e0),
        let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin ett.rounds);
        ∀ (available : RevisitingExtensionCertificate ett.series.data q.castSucc),
          (∀ (f : E),
              Sum.inr f ∈ available.returnPath.support →
                sigma f = ett.series.data.coloring q.castSucc f) →
            let _ : SimpleGraph (V ⊕ E) :=
              TwoColorIncidenceGraph G (ett.series.data.coloring q.castSucc) available.gamma
                available.delta;
            let sigmaReturnGraph : SimpleGraph (V ⊕ E) :=
              TwoColorIncidenceGraph G sigma available.gamma available.delta;
            ∀ edge ∈ available.returnPath.edges, edge ∈ sigmaReturnGraph.edgeSet := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma _ q available copyReturnEdge
    oldReturnGraph sigmaReturnGraph edge hedge
  induction edge using Sym2.inductionOn with
  | _ a b =>
    have haSupport := available.returnPath.fst_mem_support_of_mem_edges hedge
    have hbSupport := available.returnPath.snd_mem_support_of_mem_edges hedge
    have habOld : oldReturnGraph.Adj a b := by
      simpa [oldReturnGraph] using available.returnPath.edges_subset_edgeSet hedge
    cases a with
    | inl v =>
      cases b with
      | inl w => simp [oldReturnGraph, TwoColorIncidenceGraph] at habOld
      | inr
        f =>
        have hdata :
          Incident G v f ∧
            (ett.series.data.coloring q.castSucc f = some available.gamma ∨
              ett.series.data.coloring q.castSucc f = some available.delta) :=
          by simpa [oldReturnGraph, TwoColorIncidenceGraph] using habOld
        have hcopy := copyReturnEdge f hbSupport
        simpa [sigmaReturnGraph, TwoColorIncidenceGraph, hcopy] using hdata
    | inr f =>
      cases b with
      | inl
        v =>
        have hdata :
          Incident G v f ∧
            (ett.series.data.coloring q.castSucc f = some available.gamma ∨
              ett.series.data.coloring q.castSucc f = some available.delta) :=
          by simpa [oldReturnGraph, TwoColorIncidenceGraph] using habOld
        have hcopy := copyReturnEdge f haSupport
        simpa [sigmaReturnGraph, TwoColorIncidenceGraph, hcopy] using hdata
      | inr g => simp [oldReturnGraph, TwoColorIncidenceGraph] at habOld

theorem helper_correspondingTerminalTree_1299.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (originalPrefix : ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last
        ett.rounds).castSucc) (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (C : CorrespondingExtendedTashkinovTree G k e0
        originalPrefix sigma (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
        C.replacementETT.series.data.tree (Fin.last (C.replacementETT.rounds + (1 : ℕ))) =
        C.replacementSeries.data.tree (Fin.last (originalPrefix.rounds + (1 : ℕ))) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma originalPrefix C
  rcases C with
    ⟨replacementInput, replacementSeries, replacementETT, rungAgreement, seriesPresentation,
      finalGeneratingColoring, ladderTreesAgree, storedColorsAgree, connectingEdgesAgree,
      extensionKindsAgree, replacementProper, replacementOneUncolored, replacementStable⟩
  cases replacementETT with
  | mk rounds roundsPositive replacementData above strict below
    generatingColoring =>
    cases rungAgreement
    have hseries : replacementData = replacementSeries := eq_of_heq seriesPresentation
    cases hseries
    rfl

theorem helper_endpointIdentity_1568.{u_1, u_2} :
    open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) {f : E} {a b : V},
        Incident G a f → Incident G b f → a ≠ b → G.ends f = s(a, b) := by
  classical
  intro V E G f a b ha hb hab
  have endsEq : ∀ {z : Sym2 V} {x y : V}, x ∈ z → y ∈ z → x ≠ y → z = s(x, y) := by
    as_aux_lemma =>
      intro z x y hx hy hxy
      induction z using Sym2.inductionOn with
      | _ u v =>
        simp only [Sym2.mem_iff] at hx hy
        rcases hx with rfl | rfl
        · rcases hy with rfl | rfl
          · exact (hxy rfl).elim
          · rfl
        · rcases hy with rfl | rfl
          · exact Sym2.eq_swap
          · exact (hxy rfl).elim
  exact endsEq ha hb hab

theorem helper_holdLeafDegree_1372.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds); IsProperEdgeColoring G (ett.series.data.coloring q.castSucc) →
    ∀ (available : RevisitingExtensionCertificate ett.series.data q.castSucc) (originalPrefix :
        ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (corr : CorrespondingExtendedTashkinovTree G k e0
        originalPrefix sigma (ett.series.data.tree (Fin.last ett.rounds).castSucc)) (newi : Fin
        originalPrefix.rounds) (newChoice : MaximumDefectiveChoice G e0
        (corr.replacementSeries.data.tree newi.succ.castSucc) (TashkinovStoredColors
        corr.replacementSeries.data newi.castSucc) (corr.replacementSeries.data.coloring
        newi.castSucc)), available.gamma ≠ available.delta → available.delta ∈ MissingColors G
        (ett.series.data.coloring q.castSucc) newChoice.vertex → (TwoColorIncidenceGraph G
        (ett.series.data.coloring q.castSucc) available.gamma available.delta).degree (Sum.inl
        newChoice.vertex) ≤ (1 : ℕ) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma _ q previousProper available
    originalPrefix corr newi newChoice hgammaDeltaNe holdDeltaAtNewVertex
  have hgraphSwapOrder :
    TwoColorIncidenceGraph G (ett.series.data.coloring q.castSucc) available.delta available.gamma =
      TwoColorIncidenceGraph G (ett.series.data.coloring q.castSucc) available.gamma
        available.delta := by
    ext x y
    cases x <;> cases y <;> simp [TwoColorIncidenceGraph, or_comm]
  rw [← hgraphSwapOrder]
  simpa only [← SimpleGraph.card_neighborSet_eq_degree, Fintype.card_eq_nat_card] using
    (MissingColorIncidenceEndpoint G (ett.series.data.coloring q.castSucc) available.delta
      available.gamma hgammaDeltaNe.symm previousProper newChoice.vertex holdDeltaAtNewVertex)

theorem helper_hreturnNeNew_1406.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (available : RevisitingExtensionCertificate ett.series.data q.castSucc) (originalPrefix :
        ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (corr : CorrespondingExtendedTashkinovTree G k e0
        originalPrefix sigma (ett.series.data.tree (Fin.last ett.rounds).castSucc)) (newi : Fin
        originalPrefix.rounds) (newChoice : MaximumDefectiveChoice G e0
        (corr.replacementSeries.data.tree newi.succ.castSucc) (TashkinovStoredColors
        corr.replacementSeries.data newi.castSucc) (corr.replacementSeries.data.coloring
        newi.castSucc)), ((TwoColorIncidenceGraph G (ett.series.data.coloring q.castSucc)
        available.gamma available.delta).neighborSet (Sum.inl newChoice.vertex)).Subsingleton →
        available.returnVertex ≠ newChoice.vertex := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma _ q available originalPrefix
    corr newi newChoice holdLeaf heq
  have hsupport : Sum.inl newChoice.vertex ∈ available.cycle.walk.support := by
    rw [← heq]
    apply available.returnPathOnCycle
    simp
  let rotated := available.cycle.walk.rotate (Sum.inl newChoice.vertex) hsupport
  have hrotated : rotated.IsCycle := available.cycle.isCycle.rotate hsupport
  have hfirst :
    (TwoColorIncidenceGraph G (ett.series.data.coloring q.castSucc) available.gamma
          available.delta).Adj
      (Sum.inl newChoice.vertex) rotated.snd :=
    rotated.adj_snd hrotated.not_nil
  have hlast :
    (TwoColorIncidenceGraph G (ett.series.data.coloring q.castSucc) available.gamma
          available.delta).Adj
      (Sum.inl newChoice.vertex) rotated.penultimate :=
    (rotated.adj_penultimate hrotated.not_nil).symm
  exact hrotated.snd_ne_penultimate (holdLeaf hfirst hlast)

theorem helper_hswapGraph_1429.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (originalPrefix : ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last
        ett.rounds).castSucc) (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (corr : CorrespondingExtendedTashkinovTree G k e0
        originalPrefix sigma (ett.series.data.tree (Fin.last ett.rounds).castSucc)) (newi : Fin
        originalPrefix.rounds) (newChoice : MaximumDefectiveChoice G e0
        (corr.replacementSeries.data.tree newi.succ.castSucc) (TashkinovStoredColors
        corr.replacementSeries.data newi.castSucc) (corr.replacementSeries.data.coloring
        newi.castSucc)) (newGamma : Fin k) (newSecond : PartialEdgeColoring E k),
        TwoColorIncidenceGraph G (TwoColorComponentSwap G newSecond newGamma newChoice.color
        (Sum.inl newChoice.vertex)) newGamma newChoice.color = TwoColorIncidenceGraph G newSecond
        newGamma newChoice.color := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma originalPrefix corr newi newChoice
    newGamma newSecond
  ext x y
  cases x with
  | inl v =>
    cases y with
    | inl w => simp [TwoColorIncidenceGraph]
    | inr
      f =>
      by_cases hf :
        Sum.inr f ∈
          TwoColorComponent G newSecond newGamma newChoice.color (Sum.inl newChoice.vertex)
      · by_cases hfg : newSecond f = some newGamma
        · simp [TwoColorIncidenceGraph, TwoColorComponentSwap, hf, hfg]
        · by_cases hfd : newSecond f = some newChoice.color
          · simp [TwoColorIncidenceGraph, TwoColorComponentSwap, hf, hfd]
          · simp [TwoColorIncidenceGraph, TwoColorComponentSwap, hf, hfg, hfd]
      · simp [TwoColorIncidenceGraph, TwoColorComponentSwap, hf]
  | inr f =>
    cases y with
    | inl
      v =>
      by_cases hf :
        Sum.inr f ∈
          TwoColorComponent G newSecond newGamma newChoice.color (Sum.inl newChoice.vertex)
      · by_cases hfg : newSecond f = some newGamma
        · simp [TwoColorIncidenceGraph, TwoColorComponentSwap, hf, hfg]
        · by_cases hfd : newSecond f = some newChoice.color
          · simp [TwoColorIncidenceGraph, TwoColorComponentSwap, hf, hfd]
          · simp [TwoColorIncidenceGraph, TwoColorComponentSwap, hf, hfg, hfd]
      · simp [TwoColorIncidenceGraph, TwoColorComponentSwap, hf]
    | inr g => simp [TwoColorIncidenceGraph]

theorem helper_hsigmaExitGraph_1471.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (available : RevisitingExtensionCertificate ett.series.data q.castSucc) (originalPrefix :
        ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (corr : CorrespondingExtendedTashkinovTree G k e0
        originalPrefix sigma (ett.series.data.tree (Fin.last ett.rounds).castSucc)) (newi : Fin
        originalPrefix.rounds) (newChoice : MaximumDefectiveChoice G e0
        (corr.replacementSeries.data.tree newi.succ.castSucc) (TashkinovStoredColors
        corr.replacementSeries.data newi.castSucc) (corr.replacementSeries.data.coloring
        newi.castSucc)) (newGamma : Fin k) (newSecond : PartialEdgeColoring E k),
        corr.replacementSeries.data.coloring newi.succ = TwoColorComponentSwap G newSecond
        newGamma newChoice.color (Sum.inl newChoice.vertex) → newChoice.color = available.delta →
        newGamma = available.gamma → corr.replacementSeries.data.coloring newi.succ = sigma →
        TwoColorIncidenceGraph G (TwoColorComponentSwap G newSecond newGamma newChoice.color
        (Sum.inl newChoice.vertex)) newGamma newChoice.color = TwoColorIncidenceGraph G newSecond
        newGamma newChoice.color → TwoColorIncidenceGraph G sigma available.gamma available.delta
        = TwoColorIncidenceGraph G newSecond newGamma newChoice.color := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma _ q available originalPrefix
    corr newi newChoice newGamma newSecond newCurrentColoring hnewDeltaAvailable hnewGammaAvailable
    hnewPostSigma hswapGraph
  calc
    TwoColorIncidenceGraph G sigma available.gamma available.delta =
        TwoColorIncidenceGraph G (corr.replacementSeries.data.coloring newi.succ) available.gamma
          available.delta :=
      congrArg (fun phi => TwoColorIncidenceGraph G phi available.gamma available.delta)
        hnewPostSigma.symm
    _ =
        TwoColorIncidenceGraph G
          (TwoColorComponentSwap G newSecond newGamma newChoice.color (Sum.inl newChoice.vertex))
          available.gamma available.delta :=
      congrArg (fun phi => TwoColorIncidenceGraph G phi available.gamma available.delta)
        newCurrentColoring
    _ =
        TwoColorIncidenceGraph G
          (TwoColorComponentSwap G newSecond newGamma newChoice.color (Sum.inl newChoice.vertex))
          newGamma newChoice.color :=
      by rw [hnewGammaAvailable, hnewDeltaAvailable]
    _ = TwoColorIncidenceGraph G newSecond newGamma newChoice.color := hswapGraph

theorem helper_hi_768.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ⟩ : Fin ett.rounds);
    ∀ (i : Fin ett.rounds), Fin.last ett.rounds = i.succ → i = q := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ q i htarget
  apply Fin.ext
  have hv : ett.rounds = i.val + 1 := by simpa using congrArg Fin.val htarget
  change i.val = ett.rounds - 1
  omega

theorem helper_branch_787.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (Tstar : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ⟩ : Fin ett.rounds); q.castSucc = (⟨ett.rounds - (1 : ℕ),
    by
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))) →
    ∀ (_ : RevisitingExtensionCertificate ett.series.data q.castSucc), (ett.rounds = (1 : ℕ) ∧
    ∃ (prefixInput : PartialEdgeColoring E k) (zeroPrefix : TashkinovSeries G k (0 : ℕ) e0
        prefixInput), zeroPrefix.data.tree (Fin.last (1 : ℕ)) = ett.series.data.tree (Fin.last
        ett.rounds).castSucc ∧ zeroPrefix.data.coloring (Fin.last (0 : ℕ)) = sigma) → Nonempty
        (CorrespondingExtendedTashkinovTree G k e0 ett sigma Tstar) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma _ q hqCast available hzero
  rcases hzero with ⟨hroundOne, prefixInput, zeroPrefix, hzeroTree, hzeroColor⟩
  have : available.earlier.val ≤ 0 := by
    have hqzero : q.castSucc.val = 0 := by simp [q, hroundOne]
    have hle := available.earlierAtMost
    omega
  have hearlierPositive := available.earlierPositive
  omega

theorem helper_hne_1035.{u_1, u_2} :
    open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (X : TreeSequence G e0) (C : Finset (Fin k)) (phi : PartialEdgeColoring E k)
        (ch : MaximumDefectiveChoice G e0 X C phi) (g : Fin k) (second : PartialEdgeColoring E k),
        g ∈ MissingColors G second ch.vertex → second ch.edge = some ch.color → g ≠ ch.color := by
  classical
  intro V E _ _ G k e0 X C phi ch g second hgSecond hedgeSecond heq
  have hpresent : g ∈ PresentColors G second ch.vertex := by
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨ch.edge, ch.edgeIncident, by simpa [heq] using hedgeSecond⟩
  have hnotPresent : g ∉ PresentColors G second ch.vertex := by simpa [MissingColors] using hgSecond
  exact hnotPresent hpresent

theorem helper_hbaseTree_1084.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (originalPrefix : ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last
        ett.rounds).castSucc) (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by
                  have := GoldbergSeymour.TreeSequence.positive T
                  omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (corr : CorrespondingExtendedTashkinovTree G k e0
        originalPrefix sigma (ett.series.data.tree (Fin.last ett.rounds).castSucc)) (oldi : Fin
        ett.rounds) (newi : Fin originalPrefix.rounds), corr.replacementSeries.data.tree
        newi.succ.castSucc = ett.series.data.tree oldi.succ.castSucc →
        originalPrefix.series.data.tree newi.succ.castSucc = ett.series.data.tree
        oldi.succ.castSucc := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma originalPrefix corr oldi newi htree
  calc
    originalPrefix.series.data.tree newi.succ.castSucc =
        corr.replacementSeries.data.tree newi.succ.castSucc :=
      (corr.ladderTreesAgree newi).symm
    _ = ett.series.data.tree oldi.succ.castSucc := htree

theorem helper_hmissingSameVertex_1108.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (originalPrefix : ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last
        ett.rounds).castSucc) (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by
                  have := GoldbergSeymour.TreeSequence.positive T
                  omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (corr : CorrespondingExtendedTashkinovTree G k e0
        originalPrefix sigma (ett.series.data.tree (Fin.last ett.rounds).castSucc)) (oldi : Fin
        ett.rounds) (oldChoice : MaximumDefectiveChoice G e0 (ett.series.data.tree
        oldi.succ.castSucc) (TashkinovStoredColors ett.series.data oldi.castSucc)
        (ett.series.data.coloring oldi.castSucc)) (newi : Fin originalPrefix.rounds),
        originalPrefix.series.data.tree newi.succ.castSucc = ett.series.data.tree
        oldi.succ.castSucc → originalPrefix.series.data.coloring newi.succ =
        ett.series.data.coloring oldi.succ → MissingColors G (ett.series.data.coloring oldi.succ)
        oldChoice.vertex = MissingColors G (corr.replacementSeries.data.coloring newi.succ)
        oldChoice.vertex :=
  by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma originalPrefix corr oldi oldChoice
    newi hbaseTree hbaseColor
  have hvBase :
    oldChoice.vertex ∈ TreeSequenceVertexSet (originalPrefix.series.data.tree newi.succ.castSucc) :=
    by
    rw [hbaseTree]
    exact oldChoice.vertexDefective.1
  have hs := (corr.replacementStable newi).2 oldChoice.vertex hvBase
  rw [hbaseColor] at hs
  exact hs.symm

theorem helper_hnewVertexTn_1347.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (originalPrefix : ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last
        ett.rounds).castSucc) (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by
                  have := GoldbergSeymour.TreeSequence.positive T
                  omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (corr : CorrespondingExtendedTashkinovTree G k e0
        originalPrefix sigma (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
        corr.replacementSeries.data.tree (Fin.last (originalPrefix.rounds + (1 : ℕ))) =
        ett.series.data.tree (Fin.last ett.rounds).castSucc →
    ∀ (newi : Fin originalPrefix.rounds) (newChoice : MaximumDefectiveChoice G e0
        (corr.replacementSeries.data.tree newi.succ.castSucc) (TashkinovStoredColors
        corr.replacementSeries.data newi.castSucc) (corr.replacementSeries.data.coloring
        newi.castSucc)), TreeSequenceInitialSegment (corr.replacementSeries.data.tree
        newi.succ.castSucc) (corr.replacementSeries.data.tree (Fin.last (originalPrefix.rounds +
        (1 : ℕ)))) → newChoice.vertex ∈ TreeSequenceVertexSet (ett.series.data.tree (Fin.last
        ett.rounds).castSucc) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma originalPrefix corr hcorrFinalTree
    newi newChoice hnewTreeFinal
  have hvFinal :
    newChoice.vertex ∈
      TreeSequenceVertexSet
        (corr.replacementSeries.data.tree (Fin.last (originalPrefix.rounds + 1))) :=
    TreeSequenceInitialSegmentVertexSetSubset hnewTreeFinal newChoice.vertexDefective.1
  exact
    Eq.mp (congrArg (fun X => newChoice.vertex ∈ TreeSequenceVertexSet X) hcorrFinalTree) hvFinal

theorem helper_missingPreviousToTn_1435.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ⟩ : Fin ett.rounds); TreeSequenceInitialSegment (ett.series.data.tree q.castSucc.castSucc)
        (ett.series.data.tree q.succ.castSucc) →
    ∀ c ∈ TreeMissingColors (ett.series.data.coloring q.castSucc) (ett.series.data.tree
        q.castSucc.castSucc), c ∈ TreeMissingColors (ett.series.data.coloring q.castSucc)
        (ett.series.data.tree q.succ.castSucc) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ q hpreviousToTn c hc
  simp only [TreeMissingColors, Finset.mem_biUnion] at hc ⊢
  obtain ⟨v, hv, hvc⟩ := hc
  exact ⟨v, TreeSequenceInitialSegmentVertexSetSubset hpreviousToTn hv, hvc⟩

theorem helper_copyReturnEdge_1482.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ⟩ : Fin ett.rounds);
    ∀ (available : RevisitingExtensionCertificate ett.series.data q.castSucc), StableColoring
        (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors ett.series.data q.castSucc)
        (ett.series.data.coloring q.castSucc) sigma → available.gamma ∈ ett.series.data.stored
        available.earlier → available.delta ∈ ett.series.data.stored available.earlier → (
    ∀ c ∈ ett.series.data.stored available.earlier, c ∈ TreeMissingColors
        (ett.series.data.coloring q.castSucc) (ett.series.data.tree q.succ.castSucc) ∪
        TashkinovStoredColors ett.series.data q.castSucc) → (
    ∀ (f : E), Sum.inr f ∈ available.returnPath.support → TreeIncidentEdge (ett.series.data.tree
        q.succ.castSucc) f ∧ (ett.series.data.coloring q.castSucc f = some available.gamma ∨
        ett.series.data.coloring q.castSucc f = some available.delta)) →
    ∀ (f : E), Sum.inr f ∈ available.returnPath.support → sigma f = ett.series.data.coloring
        q.castSucc f := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma _ q available hsigmaPrevStableQ
    hgammaEarlierStored hdeltaEarlierStored colorControlAtQ oldReturnEdgeData f hf
  obtain ⟨hfIncident, hcolor⟩ := oldReturnEdgeData f hf
  apply hsigmaPrevStableQ.1 f hfIncident
  rcases hcolor with hgamma | hdelta
  · exact ⟨available.gamma, colorControlAtQ available.gamma hgammaEarlierStored, hgamma⟩
  · exact ⟨available.delta, colorControlAtQ available.delta hdeltaEarlierStored, hdelta⟩

theorem helper_hreturnInQ_1513.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ⟩ : Fin ett.rounds);
    ∀ (available : RevisitingExtensionCertificate ett.series.data q.castSucc),
    let sigmaReturnGraph : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G sigma available.gamma
        available.delta;
    ∀ (returnEdgeTransfer :
    ∀ edge ∈ available.returnPath.edges, edge ∈ sigmaReturnGraph.edgeSet),
    let _ : sigmaReturnGraph.Walk (Sum.inr available.edge) (Sum.inl available.returnVertex) :=
        available.returnPath.transfer sigmaReturnGraph returnEdgeTransfer; Sum.inl
        available.returnVertex ∈ TwoColorComponent G sigma available.gamma available.delta
        (Sum.inr available.edge) :=
  by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma _ q available sigmaReturnGraph
    returnEdgeTransfer sigmaReturnPath
  change
    sigmaReturnGraph.connectedComponentMk (Sum.inl available.returnVertex) =
      sigmaReturnGraph.connectedComponentMk (Sum.inr available.edge)
  exact (SimpleGraph.ConnectedComponent.sound sigmaReturnPath.reachable).symm

theorem helper_hedgeSigmaActive_1522.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ⟩ : Fin ett.rounds);
    ∀ (available : RevisitingExtensionCertificate ett.series.data q.castSucc), (
    ∀ (f : E), Sum.inr f ∈ available.returnPath.support → TreeIncidentEdge (ett.series.data.tree
        q.succ.castSucc) f ∧ (ett.series.data.coloring q.castSucc f = some available.gamma ∨
        ett.series.data.coloring q.castSucc f = some available.delta)) → (
    ∀ (f : E), Sum.inr f ∈ available.returnPath.support → sigma f = ett.series.data.coloring
        q.castSucc f) → sigma available.edge = some available.gamma ∨ sigma available.edge = some
        available.delta := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma _ q available oldReturnEdgeData
    copyReturnEdge
  have hsupport : Sum.inr available.edge ∈ available.returnPath.support := by simp
  have hold := (oldReturnEdgeData available.edge hsupport).2
  rw [copyReturnEdge available.edge hsupport]
  exact hold

theorem helper_houtsideInQ_1530.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ⟩ : Fin ett.rounds);
    ∀ (available : RevisitingExtensionCertificate ett.series.data q.castSucc), sigma
        available.edge = some available.gamma ∨ sigma available.edge = some available.delta →
        Sum.inl available.outsideEndpoint ∈ TwoColorComponent G sigma available.gamma
        available.delta (Sum.inr available.edge) :=
  by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma _ q available hedgeSigmaActive
  apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
  have houtIncident : Incident G available.outsideEndpoint available.edge := by
    unfold Incident
    rw [available.edgeEnds]
    exact Sym2.mem_mk_right _ _
  simp [TwoColorIncidenceGraph, houtIncident, hedgeSigmaActive]

theorem helper_holdDeltaAtNewVertex_1560.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ⟩ : Fin ett.rounds);
    ∀ (available : RevisitingExtensionCertificate ett.series.data q.castSucc) (originalPrefix :
        ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by
                    have := GoldbergSeymour.TreeSequence.positive T
                    omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (corr : CorrespondingExtendedTashkinovTree G k e0
        originalPrefix sigma (ett.series.data.tree (Fin.last ett.rounds).castSucc)) (oldi : Fin
        ett.rounds) (oldChoice : MaximumDefectiveChoice G e0 (ett.series.data.tree
        oldi.succ.castSucc) (TashkinovStoredColors ett.series.data oldi.castSucc)
        (ett.series.data.coloring oldi.castSucc)) (newi : Fin originalPrefix.rounds) (newChoice :
        MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree newi.succ.castSucc)
        (TashkinovStoredColors corr.replacementSeries.data newi.castSucc)
        (corr.replacementSeries.data.coloring newi.castSucc)), oldChoice.color ∈ MissingColors G
        (ett.series.data.coloring oldi.succ) oldChoice.vertex → oldChoice.color = available.delta
        → newChoice.vertex = oldChoice.vertex → ett.series.data.coloring q.castSucc =
        ett.series.data.coloring oldi.succ → available.delta ∈ MissingColors G
        (ett.series.data.coloring q.castSucc) newChoice.vertex := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma _ q available originalPrefix
    corr oldi oldChoice newi newChoice holdDeltaMissing holdDeltaAvailable hnewVertexOld
    holdColorConstant
  have hm := holdDeltaMissing
  rw [holdDeltaAvailable] at hm
  have hm' :
    available.delta ∈ MissingColors G (ett.series.data.coloring oldi.succ) newChoice.vertex := by
    simpa only [hnewVertexOld] using hm
  exact
    Eq.mpr
      (congrArg (fun phi => available.delta ∈ MissingColors G phi newChoice.vertex)
        holdColorConstant)
      hm'

theorem helper_hreplacementCurrentTree_1736.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (originalPrefix : ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last
        ett.rounds).castSucc) (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by
                  have := GoldbergSeymour.TreeSequence.positive T
                  omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (corr : CorrespondingExtendedTashkinovTree G k e0
        originalPrefix sigma (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
        corr.replacementSeries.data.tree (Fin.last (originalPrefix.rounds + (1 : ℕ))) =
        ett.series.data.tree (Fin.last ett.rounds).castSucc →
    let replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last originalPrefix.rounds;
        corr.replacementSeries.data.tree replacementLast.succ = ett.series.data.tree (Fin.last
        ett.rounds).castSucc := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma originalPrefix corr hcorrFinalTree
    replacementLast
  as_aux_lemma =>
    calc
      corr.replacementSeries.data.tree replacementLast.succ =
          corr.replacementSeries.data.tree (Fin.last (originalPrefix.rounds + 1)) :=
        by congr 1
      _ = ett.series.data.tree (Fin.last ett.rounds).castSucc := hcorrFinalTree

theorem helper_hreturnNotNext_1938.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ⟩ : Fin ett.rounds);
    ∀ (available : RevisitingExtensionCertificate ett.series.data q.castSucc) (replacementCycle :
        TwoColorCycle G sigma available.gamma available.delta),
    let currentTree : Finset V := TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc);
    ∀ (hreturnCycle : Sum.inl available.returnVertex ∈ replacementCycle.walk.support),
    let rootedCycle : (TwoColorIncidenceGraph G sigma available.gamma available.delta).Walk
        (Sum.inl available.returnVertex) (Sum.inl available.returnVertex) :=
        replacementCycle.walk.rotate (Sum.inl available.returnVertex) hreturnCycle;
    let outsideIndices : Finset (Fin (rootedCycle.length + (1 : ℕ))) := ({i : Fin
        (rootedCycle.length + (1 : ℕ)) |
    ∃ (v : V), rootedCycle.getVert (↑i : ℕ) = Sum.inl v ∧ v ∉ currentTree} : Finset (Fin
        (rootedCycle.length + (1 : ℕ))));
    ∀ (outsideIndicesNonempty : outsideIndices.Nonempty),
    let firstOutside : Fin (rootedCycle.length + (1 : ℕ)) := outsideIndices.min'
        outsideIndicesNonempty;
    ∀ (outsideOne : V), rootedCycle.getVert (↑(outsideIndices.min' outsideIndicesNonempty) : ℕ) =
        Sum.inl outsideOne → (↑firstOutside : ℕ) < rootedCycle.length →
    let laterInsideIndices : Finset (Fin (rootedCycle.length + (1 : ℕ))) := ({idx : Fin
        (rootedCycle.length + (1 : ℕ)) | (↑firstOutside : ℕ) < (↑idx : ℕ) ∧
    ∃ (v : V), rootedCycle.getVert (↑idx : ℕ) = Sum.inl v ∧ v ∈ currentTree} : Finset (Fin
        (rootedCycle.length + (1 : ℕ))));
    ∀ (laterInsideNonempty : laterInsideIndices.Nonempty),
    let firstReturn : Fin (rootedCycle.length + (1 : ℕ)) := laterInsideIndices.min'
        laterInsideNonempty;
    ∀ (insideTwo : V), rootedCycle.getVert (↑(laterInsideIndices.min' laterInsideNonempty) : ℕ) =
        Sum.inl insideTwo → (↑firstReturn : ℕ) ≠ (↑firstOutside : ℕ) + (1 : ℕ) := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hpositive sigma _ q available replacementCycle
    currentTree hreturnCycle rootedCycle outsideIndices outsideIndicesNonempty firstOutside
    outsideOne houtsideOneAt firstOutsideLt laterInsideIndices laterInsideNonempty firstReturn
    insideTwo hinsideTwoAt heq
  have hadj := rootedCycle.adj_getVert_succ (i := firstOutside.val) (by omega)
  rw [houtsideOneAt] at hadj
  have hnext : rootedCycle.getVert (firstOutside.val + 1) = Sum.inl insideTwo := by
    have heq' : (laterInsideIndices.min' laterInsideNonempty).val = firstOutside.val + 1 := heq
    rw [heq'] at hinsideTwoAt
    exact hinsideTwoAt
  rw [hnext] at hadj
  simp [TwoColorIncidenceGraph] at hadj

theorem helper_hfirstGamma_2063.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ⟩ : Fin ett.rounds);
    ∀ (available : RevisitingExtensionCertificate ett.series.data q.castSucc) (originalPrefix :
        ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by
                    have := GoldbergSeymour.TreeSequence.positive T
                    omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (corr : CorrespondingExtendedTashkinovTree G k e0
        originalPrefix sigma (ett.series.data.tree (Fin.last ett.rounds).castSucc)) (newi : Fin
        originalPrefix.rounds) (newChoice : MaximumDefectiveChoice G e0
        (corr.replacementSeries.data.tree newi.succ.castSucc) (TashkinovStoredColors
        corr.replacementSeries.data newi.castSucc) (corr.replacementSeries.data.coloring
        newi.castSucc)), available.delta ∈ MissingColors G sigma newChoice.vertex →
        ColoredVertexSetClosed G sigma (TreeSequenceVertexSet (ett.series.data.tree
        q.succ.castSucc)) →
    let currentTree : Finset V := TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc);
    ∀ (firstEdge : E), sigma firstEdge = some available.gamma ∨ sigma firstEdge = some
        available.delta → firstEdge ∈ BoundaryEdges G currentTree → newChoice.vertex ∈ currentTree
        → sigma firstEdge = some available.gamma := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma _ q available originalPrefix
    corr newi newChoice hnewDeltaSigma hclosedSigma currentTree firstEdge hfirstEdgeActive
    hfirstBoundary hnewVertexCurrent
  rcases hfirstEdgeActive with hgamma | hdelta
  · exact hgamma
  · exfalso
    exact (hclosedSigma hfirstBoundary hnewVertexCurrent hdelta) hnewDeltaSigma

theorem helper_hsecondGamma_2070.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ⟩ : Fin ett.rounds);
    ∀ (available : RevisitingExtensionCertificate ett.series.data q.castSucc) (originalPrefix :
        ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by
                    have := GoldbergSeymour.TreeSequence.positive T
                    omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (corr : CorrespondingExtendedTashkinovTree G k e0
        originalPrefix sigma (ett.series.data.tree (Fin.last ett.rounds).castSucc)) (newi : Fin
        originalPrefix.rounds) (newChoice : MaximumDefectiveChoice G e0
        (corr.replacementSeries.data.tree newi.succ.castSucc) (TashkinovStoredColors
        corr.replacementSeries.data newi.castSucc) (corr.replacementSeries.data.coloring
        newi.castSucc)), available.delta ∈ MissingColors G sigma newChoice.vertex →
        ColoredVertexSetClosed G sigma (TreeSequenceVertexSet (ett.series.data.tree
        q.succ.castSucc)) →
    let currentTree : Finset V := TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc);
    ∀ (secondEdge : E), sigma secondEdge = some available.gamma ∨ sigma secondEdge = some
        available.delta → secondEdge ∈ BoundaryEdges G currentTree → newChoice.vertex ∈
        currentTree → sigma secondEdge = some available.gamma := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma _ q available originalPrefix
    corr newi newChoice hnewDeltaSigma hclosedSigma currentTree secondEdge hsecondEdgeActive
    hsecondBoundary hnewVertexCurrent
  rcases hsecondEdgeActive with hgamma | hdelta
  · exact hgamma
  · exfalso
    exact (hclosedSigma hsecondBoundary hnewVertexCurrent hdelta) hnewDeltaSigma

theorem helper_hsigmaPathInQ_2135.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ⟩ : Fin ett.rounds);
    ∀ (available : RevisitingExtensionCertificate ett.series.data q.castSucc),
    let sigmaReturnGraph : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G sigma available.gamma
        available.delta;
    ∀ (returnEdgeTransfer :
    ∀ edge ∈ available.returnPath.edges, edge ∈ sigmaReturnGraph.edgeSet),
    let sigmaReturnPath : sigmaReturnGraph.Walk (Sum.inr available.edge) (Sum.inl
        available.returnVertex) := available.returnPath.transfer sigmaReturnGraph
        returnEdgeTransfer;
    ∀ z ∈ sigmaReturnPath.support, z ∈ TwoColorComponent G sigma available.gamma available.delta
        (Sum.inr available.edge) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma _ q available sigmaReturnGraph
    returnEdgeTransfer sigmaReturnPath z hz
  obtain ⟨m, hm, hmle⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hz
  change
    sigmaReturnGraph.connectedComponentMk z =
      sigmaReturnGraph.connectedComponentMk (Sum.inr available.edge)
  rw [← hm]
  exact (SimpleGraph.ConnectedComponent.sound (sigmaReturnPath.take m).reachable).symm

theorem helper_hfstar_2233.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (_ : TreeSequence G e0) (fstar :
        E), ett.series.data.connectingEdges (Fin.last ett.rounds) = ({ fstar } : Finset E) →
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    ⟩ : Fin ett.rounds); q.succ = Fin.last ett.rounds →
    ∀ (available : RevisitingExtensionCertificate ett.series.data q.castSucc),
        ett.series.data.connectingEdges q.succ = ({ available.edge } : Finset E) → fstar =
        available.edge := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ fstar hfinalEdges q hqSucc available
    currentEdges
  have hcurrentEdgesFinal :
    ett.series.data.connectingEdges (Fin.last ett.rounds) = { available.edge } := by
    rw [← hqSucc]
    exact currentEdges
  apply Finset.mem_singleton.mp
  rw [← hcurrentEdgesFinal, hfinalEdges]
  exact Finset.mem_singleton_self fstar

theorem helper_hfinalTree_2464.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [inst_2 : DecidableEq
        E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ closureTree : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ⟩ : Fin ett.rounds);
    ∀ (available : RevisitingExtensionCertificate ett.series.data q.castSucc) (originalPrefix :
        ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by
                    have := GoldbergSeymour.TreeSequence.positive T
                    omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (corr : CorrespondingExtendedTashkinovTree G k e0
        originalPrefix sigma (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
    let newStored : Finset (Fin k) := (insert available.delta ({ available.gamma } : Finset (Fin
        k)) : Finset (Fin k));
    let newEdges : Finset E := ({ available.edge } : Finset E);
    let newKind : Option TashkinovExtensionKind := some TashkinovExtensionKind.RE;
    let newVertex : Option V := some available.insideEndpoint;
    let newOutside : Option V := some available.outsideEndpoint;
    let newDelta : Option (Fin k) := some available.delta;
    let newGamma : Option (Fin k) := some available.gamma;
    let _ : TashkinovSeriesData G k (originalPrefix.rounds + (1 : ℕ)) e0 :=
        TashkinovSeriesDataAppend corr.replacementSeries.data closureTree sigma newStored newEdges
        newKind newVertex newOutside newDelta newGamma;
    ∀ (extendedSeries : TashkinovSeries G k (originalPrefix.rounds + (1 : ℕ)) e0
        corr.replacementInput), extendedSeries.data = TashkinovSeriesDataAppend
        corr.replacementSeries.data closureTree sigma newStored newEdges newKind newVertex
        newOutside newDelta newGamma →
    ∀ (hroundsEq : originalPrefix.rounds + (1 : ℕ) = ett.rounds),
    let castSeries : {a b : ℕ} → a = b → TashkinovSeries G k a e0 corr.replacementInput →
        TashkinovSeries G k b e0 corr.replacementInput := fun {a b : ℕ} (h : a = b) (S :
        TashkinovSeries G k a e0 corr.replacementInput) ↦ @Eq.ndrec Nat a (fun {b : Nat} ↦
        @TashkinovSeries V E inst inst_1 inst_2 G k b e0
        (@CorrespondingExtendedTashkinovTree.replacementInput V E inst inst_1 inst_2 G k e0 input
        (@TashkinovSeriesData.tree V E G k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G
        k e0 input T generating ett) e0 (@TashkinovSeries.data V E inst inst_1 inst_2 G k
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett) e0
        input (@ExtendedTashkinovTree.series V E inst inst_1 inst_2 G k e0 input T generating
        ett)) (@Fin.castSucc (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett)
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (Fin.last
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett))))
        (@TashkinovSeriesData.coloring V E G k (@ExtendedTashkinovTree.rounds V E inst inst_1
        inst_2 G k e0 input T generating ett) e0 (@TashkinovSeries.data V E inst inst_1 inst_2 G k
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett) e0
        input (@ExtendedTashkinovTree.series V E inst inst_1 inst_2 G k e0 input T generating
        ett)) (@Fin.mk (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett)
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (@HSub.hSub Nat Nat Nat
        (@instHSub Nat instSubNat) (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0
        input T generating ett) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (
    by
                                have := GoldbergSeymour.TreeSequence.positive T
                                omega
    ))) originalPrefix sigma (@TashkinovSeriesData.tree V E G k (@ExtendedTashkinovTree.rounds V E
        inst inst_1 inst_2 G k e0 input T generating ett) e0 (@TashkinovSeries.data V E inst
        inst_1 inst_2 G k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T
        generating ett) e0 input (@ExtendedTashkinovTree.series V E inst inst_1 inst_2 G k e0
        input T generating ett)) (@Fin.castSucc (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett)
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (Fin.last
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett))))
        corr)) S b h; (
    ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 corr.replacementInput) (i : Fin (b + (2
        : ℕ))), (castSeries h S).data.tree i = S.data.tree (Fin.cast (
    by omega
    ) i)) →
    let finalSeries : TashkinovSeries G k ett.rounds e0 corr.replacementInput := castSeries
        hroundsEq extendedSeries;
    let rawFinalTree : Fin (originalPrefix.rounds + (3 : ℕ)) := Fin.cast (
    by
                        have := GoldbergSeymour.TreeSequence.positive T
                        omega
    ) (Fin.last (ett.rounds + (1 : ℕ))); rawFinalTree = Fin.last (originalPrefix.rounds + (2 : ℕ))
        → finalSeries.data.tree (Fin.last (ett.rounds + (1 : ℕ))) = closureTree := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma _ closureTree q available
    originalPrefix corr newStored newEdges newKind newVertex newOutside newDelta newGamma
    appendedData extendedSeries hextendedData hroundsEq castSeries castSeriesTree finalSeries
    rawFinalTree hrawFinalTree
  calc
    finalSeries.data.tree (Fin.last (ett.rounds + 1)) = extendedSeries.data.tree rawFinalTree := by
      exact castSeriesTree hroundsEq extendedSeries _
    _ = appendedData.tree rawFinalTree := by rw [hextendedData]
    _ = closureTree := by
      rw [hrawFinalTree]
      simp [appendedData, TashkinovSeriesDataAppend]

theorem helper_hfinalColor_2482.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [inst_2 : DecidableEq
        E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ closureTree : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ⟩ : Fin ett.rounds);
    ∀ (available : RevisitingExtensionCertificate ett.series.data q.castSucc) (originalPrefix :
        ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by
                    have := GoldbergSeymour.TreeSequence.positive T
                    omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (corr : CorrespondingExtendedTashkinovTree G k e0
        originalPrefix sigma (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
    let newStored : Finset (Fin k) := (insert available.delta ({ available.gamma } : Finset (Fin
        k)) : Finset (Fin k));
    let newEdges : Finset E := ({ available.edge } : Finset E);
    let newKind : Option TashkinovExtensionKind := some TashkinovExtensionKind.RE;
    let newVertex : Option V := some available.insideEndpoint;
    let newOutside : Option V := some available.outsideEndpoint;
    let newDelta : Option (Fin k) := some available.delta;
    let newGamma : Option (Fin k) := some available.gamma;
    let _ : TashkinovSeriesData G k (originalPrefix.rounds + (1 : ℕ)) e0 :=
        TashkinovSeriesDataAppend corr.replacementSeries.data closureTree sigma newStored newEdges
        newKind newVertex newOutside newDelta newGamma;
    ∀ (extendedSeries : TashkinovSeries G k (originalPrefix.rounds + (1 : ℕ)) e0
        corr.replacementInput), extendedSeries.data = TashkinovSeriesDataAppend
        corr.replacementSeries.data closureTree sigma newStored newEdges newKind newVertex
        newOutside newDelta newGamma →
    ∀ (hroundsEq : originalPrefix.rounds + (1 : ℕ) = ett.rounds),
    let castSeries : {a b : ℕ} → a = b → TashkinovSeries G k a e0 corr.replacementInput →
        TashkinovSeries G k b e0 corr.replacementInput := fun {a b : ℕ} (h : a = b) (S :
        TashkinovSeries G k a e0 corr.replacementInput) ↦ @Eq.ndrec Nat a (fun {b : Nat} ↦
        @TashkinovSeries V E inst inst_1 inst_2 G k b e0
        (@CorrespondingExtendedTashkinovTree.replacementInput V E inst inst_1 inst_2 G k e0 input
        (@TashkinovSeriesData.tree V E G k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G
        k e0 input T generating ett) e0 (@TashkinovSeries.data V E inst inst_1 inst_2 G k
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett) e0
        input (@ExtendedTashkinovTree.series V E inst inst_1 inst_2 G k e0 input T generating
        ett)) (@Fin.castSucc (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett)
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (Fin.last
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett))))
        (@TashkinovSeriesData.coloring V E G k (@ExtendedTashkinovTree.rounds V E inst inst_1
        inst_2 G k e0 input T generating ett) e0 (@TashkinovSeries.data V E inst inst_1 inst_2 G k
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett) e0
        input (@ExtendedTashkinovTree.series V E inst inst_1 inst_2 G k e0 input T generating
        ett)) (@Fin.mk (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett)
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (@HSub.hSub Nat Nat Nat
        (@instHSub Nat instSubNat) (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0
        input T generating ett) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (
    by
                                have := GoldbergSeymour.TreeSequence.positive T
                                omega
    ))) originalPrefix sigma (@TashkinovSeriesData.tree V E G k (@ExtendedTashkinovTree.rounds V E
        inst inst_1 inst_2 G k e0 input T generating ett) e0 (@TashkinovSeries.data V E inst
        inst_1 inst_2 G k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T
        generating ett) e0 input (@ExtendedTashkinovTree.series V E inst inst_1 inst_2 G k e0
        input T generating ett)) (@Fin.castSucc (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett)
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (Fin.last
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett))))
        corr)) S b h; (
    ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 corr.replacementInput) (i : Fin (b + (1
        : ℕ))), (castSeries h S).data.coloring i = S.data.coloring (Fin.cast (
    by omega
    ) i)) →
    let finalSeries : TashkinovSeries G k ett.rounds e0 corr.replacementInput := castSeries
        hroundsEq extendedSeries;
    let rawFinalColor : Fin (originalPrefix.rounds + (2 : ℕ)) := Fin.cast (
    by
                        have := GoldbergSeymour.TreeSequence.positive T
                        omega
    ) (Fin.last ett.rounds); rawFinalColor = Fin.last (originalPrefix.rounds + (1 : ℕ)) →
        finalSeries.data.coloring (Fin.last ett.rounds) = sigma := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma _ closureTree q available
    originalPrefix corr newStored newEdges newKind newVertex newOutside newDelta newGamma
    appendedData extendedSeries hextendedData hroundsEq castSeries castSeriesColoring finalSeries
    rawFinalColor hrawFinalColor
  calc
    finalSeries.data.coloring (Fin.last ett.rounds) = extendedSeries.data.coloring rawFinalColor :=
      by exact castSeriesColoring hroundsEq extendedSeries _
    _ = appendedData.coloring rawFinalColor := by rw [hextendedData]
    _ = sigma := by
      rw [hrawFinalColor]
      simp [appendedData, TashkinovSeriesDataAppend]

theorem helper_pePostStatus_2097.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (X : TreeSequence G e0) (C : Finset (Fin k)) (phi : PartialEdgeColoring E k) (ch
        : MaximumDefectiveChoice G e0 X C phi) (g : Fin k) (second : PartialEdgeColoring E k),
        IsProperEdgeColoring G second → StableColoring X (insert ch.color C : Finset (Fin k))
        ch.selected second → g ∈ MissingColors G ch.selected ch.vertex →
    let post : PartialEdgeColoring E k := TwoColorComponentSwap G second g ch.color (Sum.inl
        ch.vertex); ch.color ∈ MissingColors G post ch.vertex ∧ g ∉ MissingColors G post ch.vertex
        ∧ g ≠ ch.color := by
  classical
  intro V E _ _ G k e0 X C phi ch g second hsecondProper hsecondStable hgSelected
  dsimp
  have hgSecond : g ∈ MissingColors G second ch.vertex := by
    rw [hsecondStable.2 ch.vertex ch.vertexDefective.1]
    exact hgSelected
  have hedgeSecond : second ch.edge = some ch.color := by
    exact
      (hsecondStable.1 ch.edge ⟨ch.vertex, ch.vertexDefective.1, ch.edgeIncident⟩
            ⟨ch.color, Finset.mem_union_right _ (Finset.mem_insert_self _ _), ch.edgeColor⟩).trans
        ch.edgeColor
  have hne : g ≠ ch.color := by
    exact
      @helper_hne_1035 (@V) (@E) inferInstance inferInstance (@G) (@k) (@e0) (@X) (@C) (@phi) (@ch)
        (@g) (@second) (@hgSecond) (@hedgeSecond)
  have hedgeComponent :
    Sum.inr ch.edge ∈ TwoColorComponent G second g ch.color (Sum.inl ch.vertex) := by
    apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    simp [TwoColorIncidenceGraph, ch.edgeIncident, hedgeSecond]
  have hmissingDelta :
    ch.color ∈
      MissingColors G (TwoColorComponentSwap G second g ch.color (Sum.inl ch.vertex)) ch.vertex :=
    by
    exact
      (TwoColorComponentSwapMissingBehavior G second g ch.color hne hsecondProper
              (Sum.inl ch.vertex)).2.1
        ch.vertex rfl hgSecond
  have hedgePost : TwoColorComponentSwap G second g ch.color (Sum.inl ch.vertex) ch.edge = some g :=
    by simp [TwoColorComponentSwap, hedgeComponent, hedgeSecond, hne.symm]
  have hgammaPresent :
    g ∈ PresentColors G (TwoColorComponentSwap G second g ch.color (Sum.inl ch.vertex)) ch.vertex :=
    by
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨ch.edge, ch.edgeIncident, hedgePost⟩
  exact ⟨hmissingDelta, by simpa [MissingColors] using hgammaPresent, hne⟩

theorem helper_reStepColoring_2269.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ⟩ : Fin ett.rounds);
    ∀ (adjoined : TreeSequence G e0) (available : RevisitingExtensionCertificate ett.series.data
        q.castSucc), TreeSequenceAdjoinEdge (ett.series.data.tree q.succ.castSucc) available.edge
        adjoined → (1 : ℕ) < ett.rounds →
    ∀ (originalPrefix : ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last
        ett.rounds).castSucc) (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by
                          have := GoldbergSeymour.TreeSequence.positive T
                          omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))), originalPrefix.rounds = ett.rounds - (1 : ℕ) →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigma (ett.series.data.tree
        (Fin.last ett.rounds).castSucc)) (oldi : Fin ett.rounds) (_ : MaximumDefectiveChoice G e0
        (ett.series.data.tree oldi.succ.castSucc) (TashkinovStoredColors ett.series.data
        oldi.castSucc) (ett.series.data.coloring oldi.castSucc)) (_ : Fin k) (newi : Fin
        originalPrefix.rounds) (_ : MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree
        newi.succ.castSucc) (TashkinovStoredColors corr.replacementSeries.data newi.castSucc)
        (corr.replacementSeries.data.coloring newi.castSucc)) (_ : Fin k),
        corr.replacementSeries.data.tree newi.succ.castSucc = ett.series.data.tree
        oldi.succ.castSucc →
    ∀ {rounds' : ℕ} {input' : PartialEdgeColoring E k} (series : TashkinovSeries G k rounds' e0
        input') (j : Fin rounds'), series.data.kind j.succ = some TashkinovExtensionKind.RE →
        series.data.coloring j.succ = series.data.coloring j.castSucc := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma Tstar q adjoined available
    adjoinedExactly hroundLarge originalPrefix hr corr oldi oldChoice oldGamma newi newChoice
    newGamma htree
  exact
    @helper_reStepColoring_588 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
      (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@Tstar) (@adjoined) (@available)
      (@adjoinedExactly) (@hroundLarge) (@originalPrefix) (@hr) (@corr) (@oldi) (@oldChoice)
      (@oldGamma) (@newi) (@newChoice) (@newGamma) (@htree)

theorem helper_reIntervalColoring_2281.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ⟩ : Fin ett.rounds);
    ∀ (_ : RevisitingExtensionCertificate ett.series.data q.castSucc), (1 : ℕ) < ett.rounds →
    ∀ (originalPrefix : ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last
        ett.rounds).castSucc) (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by
                        have := GoldbergSeymour.TreeSequence.positive T
                        omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))), originalPrefix.rounds = ett.rounds - (1 : ℕ) →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigma (ett.series.data.tree
        (Fin.last ett.rounds).castSucc)) (oldi : Fin ett.rounds) (_ : MaximumDefectiveChoice G e0
        (ett.series.data.tree oldi.succ.castSucc) (TashkinovStoredColors ett.series.data
        oldi.castSucc) (ett.series.data.coloring oldi.castSucc)) (_ : Fin k) (newi : Fin
        originalPrefix.rounds) (_ : MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree
        newi.succ.castSucc) (TashkinovStoredColors corr.replacementSeries.data newi.castSucc)
        (corr.replacementSeries.data.coloring newi.castSucc)) (_ : Fin k),
        corr.replacementSeries.data.tree newi.succ.castSucc = ett.series.data.tree
        oldi.succ.castSucc → (
    ∀ {rounds' : ℕ} {input' : PartialEdgeColoring E k} (series : TashkinovSeries G k rounds' e0
        input') (j : Fin rounds'), series.data.kind j.succ = some TashkinovExtensionKind.RE →
        series.data.coloring j.succ = series.data.coloring j.castSucc) →
    ∀ {rounds' : ℕ} {input' : PartialEdgeColoring E k} (series : TashkinovSeries G k rounds' e0
        input') (a b : Fin (rounds' + (1 : ℕ))), (↑a : ℕ) ≤ (↑b : ℕ) → (
    ∀ (j : Fin (rounds' + (1 : ℕ))), (↑a : ℕ) < (↑j : ℕ) → (↑j : ℕ) ≤ (↑b : ℕ) → series.data.kind
        j = some TashkinovExtensionKind.RE) → series.data.coloring b = series.data.coloring a := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma Tstar q available hroundLarge
    originalPrefix hr corr oldi oldChoice oldGamma newi newChoice newGamma htree reStepColoring
  exact
    @helper_reIntervalColoring_625 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
      (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@Tstar) (@available)
      (@hroundLarge) (@originalPrefix) (@hr) (@corr) (@oldi) (@oldChoice) (@oldGamma) (@newi)
      (@newChoice) (@newGamma) (@htree) (@reStepColoring)

theorem helper_holdColorConstant_2295.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ⟩ : Fin ett.rounds); q.castSucc = (⟨ett.rounds - (1 : ℕ),
    by
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))) →
    ∀ (available : RevisitingExtensionCertificate ett.series.data q.castSucc), (1 : ℕ) <
        ett.rounds →
    ∀ (originalPrefix : ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last
        ett.rounds).castSucc) (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by
                          have := GoldbergSeymour.TreeSequence.positive T
                          omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))), originalPrefix.rounds = ett.rounds - (1 : ℕ) →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigma (ett.series.data.tree
        (Fin.last ett.rounds).castSucc)) (oldi : Fin ett.rounds) (_ : MaximumDefectiveChoice G e0
        (ett.series.data.tree oldi.succ.castSucc) (TashkinovStoredColors ett.series.data
        oldi.castSucc) (ett.series.data.coloring oldi.castSucc)) (_ : Fin k), available.earlier =
        oldi.succ → oldi.succ = available.earlier →
    ∀ (newi : Fin originalPrefix.rounds) (_ : MaximumDefectiveChoice G e0
        (corr.replacementSeries.data.tree newi.succ.castSucc) (TashkinovStoredColors
        corr.replacementSeries.data newi.castSucc) (corr.replacementSeries.data.coloring
        newi.castSucc)) (_ : Fin k), corr.replacementSeries.data.tree newi.succ.castSucc =
        ett.series.data.tree oldi.succ.castSucc → (
    ∀ {rounds' : ℕ} {input' : PartialEdgeColoring E k} (series : TashkinovSeries G k rounds' e0
        input') (a b : Fin (rounds' + (1 : ℕ))), (↑a : ℕ) ≤ (↑b : ℕ) → (
    ∀ (j : Fin (rounds' + (1 : ℕ))), (↑a : ℕ) < (↑j : ℕ) → (↑j : ℕ) ≤ (↑b : ℕ) → series.data.kind
        j = some TashkinovExtensionKind.RE) → series.data.coloring b = series.data.coloring a) →
        ett.series.data.coloring q.castSucc = ett.series.data.coloring oldi.succ := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma Tstar q hqCast available hroundLarge
    originalPrefix hr corr oldi oldChoice oldGamma holdTarget holdIndex newi newChoice newGamma
    htree reIntervalColoring
  exact
    @helper_holdColorConstant_669 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
      (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@Tstar) (@hqCast) (@available)
      (@hroundLarge) (@originalPrefix) (@hr) (@corr) (@oldi) (@oldChoice) (@oldGamma) (@holdTarget)
      (@holdIndex) (@newi) (@newChoice) (@newGamma) (@htree) (@reIntervalColoring)

theorem helper_copyReturnEdge_2580.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ⟩ : Fin ett.rounds);
    ∀ (available : RevisitingExtensionCertificate ett.series.data q.castSucc), StableColoring
        (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors ett.series.data q.castSucc)
        (ett.series.data.coloring q.castSucc) sigma → available.gamma ∈ ett.series.data.stored
        available.earlier → available.delta ∈ ett.series.data.stored available.earlier → (
    ∀ c ∈ ett.series.data.stored available.earlier, c ∈ TreeMissingColors
        (ett.series.data.coloring q.castSucc) (ett.series.data.tree q.succ.castSucc) ∪
        TashkinovStoredColors ett.series.data q.castSucc) → (
    ∀ (f : E), Sum.inr f ∈ available.returnPath.support → TreeIncidentEdge (ett.series.data.tree
        q.succ.castSucc) f ∧ (ett.series.data.coloring q.castSucc f = some available.gamma ∨
        ett.series.data.coloring q.castSucc f = some available.delta)) →
    ∀ (f : E), Sum.inr f ∈ available.returnPath.support → sigma f = ett.series.data.coloring
        q.castSucc f := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma Tstar q available hsigmaPrevStableQ
    hgammaEarlierStored hdeltaEarlierStored colorControlAtQ oldReturnEdgeData f hf
  exact
    @helper_copyReturnEdge_1482 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
      (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@Tstar) (@available)
      (@hsigmaPrevStableQ) (@hgammaEarlierStored) (@hdeltaEarlierStored) (@colorControlAtQ)
      (@oldReturnEdgeData) (@f) (@hf)

theorem helper_holdDeltaAtNewVertex_2647.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ⟩ : Fin ett.rounds);
    ∀ (available : RevisitingExtensionCertificate ett.series.data q.castSucc) (originalPrefix :
        ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by
                    have := GoldbergSeymour.TreeSequence.positive T
                    omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (corr : CorrespondingExtendedTashkinovTree G k e0
        originalPrefix sigma (ett.series.data.tree (Fin.last ett.rounds).castSucc)) (oldi : Fin
        ett.rounds) (oldChoice : MaximumDefectiveChoice G e0 (ett.series.data.tree
        oldi.succ.castSucc) (TashkinovStoredColors ett.series.data oldi.castSucc)
        (ett.series.data.coloring oldi.castSucc)) (newi : Fin originalPrefix.rounds) (newChoice :
        MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree newi.succ.castSucc)
        (TashkinovStoredColors corr.replacementSeries.data newi.castSucc)
        (corr.replacementSeries.data.coloring newi.castSucc)), oldChoice.color ∈ MissingColors G
        (ett.series.data.coloring oldi.succ) oldChoice.vertex → oldChoice.color = available.delta
        → newChoice.vertex = oldChoice.vertex → ett.series.data.coloring q.castSucc =
        ett.series.data.coloring oldi.succ → available.delta ∈ MissingColors G
        (ett.series.data.coloring q.castSucc) newChoice.vertex := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma Tstar q available originalPrefix
    corr oldi oldChoice newi newChoice holdDeltaMissing holdDeltaAvailable hnewVertexOld
    holdColorConstant
  exact
    @helper_holdDeltaAtNewVertex_1560 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
      (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@Tstar) (@available)
      (@originalPrefix) (@corr) (@oldi) (@oldChoice) (@newi) (@newChoice) (@holdDeltaMissing)
      (@holdDeltaAvailable) (@hnewVertexOld) (@holdColorConstant)

theorem helper_hsigmaExitGraph_2697.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ⟩ : Fin ett.rounds);
    ∀ (available : RevisitingExtensionCertificate ett.series.data q.castSucc) (originalPrefix :
        ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by
                    have := GoldbergSeymour.TreeSequence.positive T
                    omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (corr : CorrespondingExtendedTashkinovTree G k e0
        originalPrefix sigma (ett.series.data.tree (Fin.last ett.rounds).castSucc)) (newi : Fin
        originalPrefix.rounds) (newChoice : MaximumDefectiveChoice G e0
        (corr.replacementSeries.data.tree newi.succ.castSucc) (TashkinovStoredColors
        corr.replacementSeries.data newi.castSucc) (corr.replacementSeries.data.coloring
        newi.castSucc)) (newGamma : Fin k) (newSecond : PartialEdgeColoring E k),
        corr.replacementSeries.data.coloring newi.succ = TwoColorComponentSwap G newSecond
        newGamma newChoice.color (Sum.inl newChoice.vertex) → newChoice.color = available.delta →
        newGamma = available.gamma → corr.replacementSeries.data.coloring newi.succ = sigma →
        TwoColorIncidenceGraph G (TwoColorComponentSwap G newSecond newGamma newChoice.color
        (Sum.inl newChoice.vertex)) newGamma newChoice.color = TwoColorIncidenceGraph G newSecond
        newGamma newChoice.color → TwoColorIncidenceGraph G sigma available.gamma available.delta
        = TwoColorIncidenceGraph G newSecond newGamma newChoice.color := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma Tstar q available originalPrefix
    corr newi newChoice newGamma newSecond newCurrentColoring hnewDeltaAvailable hnewGammaAvailable
    hnewPostSigma hswapGraph
  exact
    @helper_hsigmaExitGraph_1471 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
      (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@Tstar) (@available)
      (@originalPrefix) (@corr) (@newi) (@newChoice) (@newGamma) (@newSecond) (@newCurrentColoring)
      (@hnewDeltaAvailable) (@hnewGammaAvailable) (@hnewPostSigma) (@hswapGraph)

theorem helper_hreturnNotNext_3034.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ⟩ : Fin ett.rounds);
    ∀ (available : RevisitingExtensionCertificate ett.series.data q.castSucc) (replacementCycle :
        TwoColorCycle G sigma available.gamma available.delta),
    let currentTree : Finset V := TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc);
    ∀ (hreturnCycle : Sum.inl available.returnVertex ∈ replacementCycle.walk.support),
    let rootedCycle : (TwoColorIncidenceGraph G sigma available.gamma available.delta).Walk
        (Sum.inl available.returnVertex) (Sum.inl available.returnVertex) :=
        replacementCycle.walk.rotate (Sum.inl available.returnVertex) hreturnCycle;
    let outsideIndices : Finset (Fin (rootedCycle.length + (1 : ℕ))) := ({i : Fin
        (rootedCycle.length + (1 : ℕ)) |
    ∃ (v : V), rootedCycle.getVert (↑i : ℕ) = Sum.inl v ∧ v ∉ currentTree} : Finset (Fin
        (rootedCycle.length + (1 : ℕ))));
    ∀ (outsideIndicesNonempty : outsideIndices.Nonempty),
    let firstOutside : Fin (rootedCycle.length + (1 : ℕ)) := outsideIndices.min'
        outsideIndicesNonempty;
    ∀ (outsideOne : V), rootedCycle.getVert (↑(outsideIndices.min' outsideIndicesNonempty) : ℕ) =
        Sum.inl outsideOne → (↑firstOutside : ℕ) < rootedCycle.length →
    let laterInsideIndices : Finset (Fin (rootedCycle.length + (1 : ℕ))) := ({idx : Fin
        (rootedCycle.length + (1 : ℕ)) | (↑firstOutside : ℕ) < (↑idx : ℕ) ∧
    ∃ (v : V), rootedCycle.getVert (↑idx : ℕ) = Sum.inl v ∧ v ∈ currentTree} : Finset (Fin
        (rootedCycle.length + (1 : ℕ))));
    ∀ (laterInsideNonempty : laterInsideIndices.Nonempty),
    let firstReturn : Fin (rootedCycle.length + (1 : ℕ)) := laterInsideIndices.min'
        laterInsideNonempty;
    ∀ (insideTwo : V), rootedCycle.getVert (↑(laterInsideIndices.min' laterInsideNonempty) : ℕ) =
        Sum.inl insideTwo → (↑firstReturn : ℕ) ≠ (↑firstOutside : ℕ) + (1 : ℕ) := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hpositive sigma Tstar q available replacementCycle
    currentTree hreturnCycle rootedCycle outsideIndices outsideIndicesNonempty firstOutside
    outsideOne houtsideOneAt firstOutsideLt laterInsideIndices laterInsideNonempty firstReturn
    insideTwo hinsideTwoAt
  exact
    @helper_hreturnNotNext_1938 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@Tstar) (@available)
      (@replacementCycle) (@hreturnCycle) (@outsideIndicesNonempty) (@outsideOne) (@houtsideOneAt)
      (@firstOutsideLt) (@laterInsideNonempty) (@insideTwo) (@hinsideTwoAt)

theorem helper_stepSegment_2938.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), Nat.sub_lt (Nat.zero_lt_of_lt hpositive) (
    by omega
    )⟩ : Fin ett.rounds);
    ∀ (adjoined : TreeSequence G e0) (available : RevisitingExtensionCertificate ett.series.data
        q.castSucc) (_ : TreeSequenceAdjoinEdge (ett.series.data.tree q.succ.castSucc)
        available.edge adjoined) (hroundLarge : (1 : ℕ) < ett.rounds) (originalPrefix :
        ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (_ : originalPrefix.rounds = ett.rounds - (1 : ℕ)) (corr :
        CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigma (ett.series.data.tree
        (Fin.last ett.rounds).castSucc)) (_ : (↑available.earlier : ℕ) < originalPrefix.rounds +
        (1 : ℕ)) (oldi : Fin ett.rounds) (oldChoice : MaximumDefectiveChoice G e0
        (ett.series.data.tree oldi.succ.castSucc) (TashkinovStoredColors ett.series.data
        oldi.castSucc) (ett.series.data.coloring oldi.castSucc)) (oldGamma : Fin k) (newi : Fin
        originalPrefix.rounds) (newChoice : MaximumDefectiveChoice G e0
        (corr.replacementSeries.data.tree newi.succ.castSucc) (TashkinovStoredColors
        corr.replacementSeries.data newi.castSucc) (corr.replacementSeries.data.coloring
        newi.castSucc)) (newGamma : Fin k) (htree : corr.replacementSeries.data.tree
        newi.succ.castSucc = ett.series.data.tree oldi.succ.castSucc),
    let oldChoiceOnNew : MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree
        newi.succ.castSucc) (TashkinovStoredColors ett.series.data oldi.castSucc)
        (ett.series.data.coloring oldi.castSucc) := transportDefectiveChoice (Eq.symm htree)
        oldChoice;
    ∀ (_ : oldChoiceOnNew.color = oldChoice.color) (_ : oldGamma ≠ oldChoice.color) (_ : newGamma
        ≠ newChoice.color) (_ : newChoice.color = oldChoiceOnNew.color) (_ : newGamma = oldGamma)
        (_ : oldChoice.color = available.delta) (_ : oldGamma = available.gamma) (r : Fin
        originalPrefix.rounds), TreeSequenceInitialSegment (corr.replacementSeries.data.tree
        r.succ.castSucc) (corr.replacementSeries.data.tree r.succ.succ) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma _ q adjoined available
    adjoinedExactly hroundLarge originalPrefix hr corr earlierPrefixBound oldi oldChoice oldGamma
    newi newChoice newGamma htree oldChoiceOnNew holdColorCast holdColorNe hnewColorNe
    hidentifiedDelta hidentifiedGamma holdDeltaAvailable holdGammaAvailable r
  have hstep := corr.replacementSeries.certified r.succ
  generalize hslot : r.succ = slot at hstep
  cases hstep with
  | initial triple seedLength initialColoring initialStored initialEdges initialKind initialVertex
    initialOutside initialDelta initialGamma initialClosure => exact (Fin.succ_ne_zero r hslot).elim
  | SE i prevProper prevOne prevClosed prevNotStrong noRE choice alternative coloring stored edges
    kind vertex outside delta gamma adjoined adjoinedExactly closed ordered
    strict =>
    have hi : i = r := by
      apply Fin.ext
      have hv := congrArg Fin.val hslot
      simp only [Fin.val_succ] at hv
      omega
    subst i
    simpa [hslot] using ordered
  | PE i prevProper prevOne prevClosed prevNotStrong noRE choice alternativeFails gamma gammaRule
    second secondProper secondOne secondStable exit coloring coloringProper coloringOne stored edges
    kind vertex outside delta gammaValue closed ordered
    strict =>
    have hi : i = r := by
      apply Fin.ext
      have hv := congrArg Fin.val hslot
      simp only [Fin.val_succ] at hv
      omega
    subst i
    simpa [hslot] using ordered
  | RE i prevProper prevOne prevClosed prevNotStrong cert coloring stored edges kind vertex outside
    delta gamma adjoined adjoinedExactly closed ordered
    strict =>
    have hi : i = r := by
      apply Fin.ext
      have hv := congrArg Fin.val hslot
      simp only [Fin.val_succ] at hv
      omega
    subst i
    simpa [hslot] using ordered

theorem helper_treeToFinal_2987.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), Nat.sub_lt (Nat.zero_lt_of_lt hpositive) (
    by omega
    )⟩ : Fin ett.rounds);
    ∀ (available : RevisitingExtensionCertificate ett.series.data q.castSucc) (hroundLarge : (1 :
        ℕ) < ett.rounds) (originalPrefix : ExtendedTashkinovTree G k e0 input
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) (ett.series.data.coloring
        (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (_ : originalPrefix.rounds = ett.rounds - (1 : ℕ)) (corr :
        CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigma (ett.series.data.tree
        (Fin.last ett.rounds).castSucc)) (_ : (↑available.earlier : ℕ) < originalPrefix.rounds +
        (1 : ℕ)) (oldi : Fin ett.rounds) (oldChoice : MaximumDefectiveChoice G e0
        (ett.series.data.tree oldi.succ.castSucc) (TashkinovStoredColors ett.series.data
        oldi.castSucc) (ett.series.data.coloring oldi.castSucc)) (oldGamma : Fin k) (newi : Fin
        originalPrefix.rounds) (newChoice : MaximumDefectiveChoice G e0
        (corr.replacementSeries.data.tree newi.succ.castSucc) (TashkinovStoredColors
        corr.replacementSeries.data newi.castSucc) (corr.replacementSeries.data.coloring
        newi.castSucc)) (newGamma : Fin k) (htree : corr.replacementSeries.data.tree
        newi.succ.castSucc = ett.series.data.tree oldi.succ.castSucc),
    let oldChoiceOnNew : MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree
        newi.succ.castSucc) (TashkinovStoredColors ett.series.data oldi.castSucc)
        (ett.series.data.coloring oldi.castSucc) := transportDefectiveChoice (Eq.symm htree)
        oldChoice;
    ∀ (_ : oldChoiceOnNew.color = oldChoice.color) (_ : oldGamma ≠ oldChoice.color) (_ : newGamma
        ≠ newChoice.color) (_ : newChoice.color = oldChoiceOnNew.color) (_ : newGamma = oldGamma)
        (_ : oldChoice.color = available.delta) (_ : oldGamma = available.gamma) (_ :
    ∀ (r : Fin originalPrefix.rounds), TreeSequenceInitialSegment
        (corr.replacementSeries.data.tree r.succ.castSucc) (corr.replacementSeries.data.tree
        r.succ.succ)) (_ :
    ∀ (A B C : TreeSequence G e0), TreeSequenceInitialSegment A B → TreeSequenceInitialSegment B C
        → TreeSequenceInitialSegment A C) (d : ℕ) (idx : Fin (originalPrefix.rounds + (2 : ℕ))),
        (↑idx : ℕ) + d = originalPrefix.rounds + (1 : ℕ) → (1 : ℕ) ≤ (↑idx : ℕ) →
        TreeSequenceInitialSegment (corr.replacementSeries.data.tree idx)
        (corr.replacementSeries.data.tree (Fin.last (originalPrefix.rounds + (1 : ℕ)))) :=
  by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma _ q available hroundLarge
    originalPrefix hr corr earlierPrefixBound oldi oldChoice oldGamma newi newChoice newGamma htree
    oldChoiceOnNew holdColorCast holdColorNe hnewColorNe hidentifiedDelta hidentifiedGamma
    holdDeltaAvailable holdGammaAvailable stepSegment segmentTrans d
  induction d with
  | zero =>
    intro idx hidx hpos
    have hi : idx = Fin.last (originalPrefix.rounds + 1) := by
      apply Fin.ext
      simp
      omega
    rw [hi]
    exact ⟨le_rfl, (fun _ => rfl), (fun _ => rfl)⟩
  | succ d ih =>
    intro idx hidx hpos
    have hlt : idx.val < originalPrefix.rounds + 1 := by omega
    let r : Fin originalPrefix.rounds := ⟨idx.val - 1, by omega⟩
    have hleft : idx = r.succ.castSucc := by
      apply Fin.ext
      simp [r]
      omega
    let next : Fin (originalPrefix.rounds + 2) := ⟨idx.val + 1, by omega⟩
    have hright : next = r.succ.succ := by
      apply Fin.ext
      simp [next, r]
      omega
    have hfirst :
      TreeSequenceInitialSegment (corr.replacementSeries.data.tree idx)
        (corr.replacementSeries.data.tree next) := by
      rw [hleft, hright]
      exact stepSegment r
    exact segmentTrans _ _ _ hfirst (ih next (by simp [next]; omega) (by simp [next]))

theorem helper_hclosedSigma_3647.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ : IsProperEdgeColoring G sigma) (_ : IsOneEdgeUncolored sigma e0) (_ : TreeSequence
        G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (_ : IsProperEdgeColoring G (ett.series.data.coloring q.castSucc)) (_ : IsOneEdgeUncolored
        (ett.series.data.coloring q.castSucc) e0) (_ : ColoredVertexSetClosed G
        (ett.series.data.coloring q.castSucc) (TreeSequenceVertexSet (ett.series.data.tree
        q.succ.castSucc))) (hroundLarge : (1 : ℕ) < ett.rounds) (originalPrefix :
        ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (corr : CorrespondingExtendedTashkinovTree G k e0
        originalPrefix sigma (ett.series.data.tree (Fin.last ett.rounds).castSucc)) (oldi : Fin
        ett.rounds) (oldChoice : MaximumDefectiveChoice G e0 (ett.series.data.tree
        oldi.succ.castSucc) (TashkinovStoredColors ett.series.data oldi.castSucc)
        (ett.series.data.coloring oldi.castSucc)) (newi : Fin originalPrefix.rounds) (newChoice :
        MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree newi.succ.castSucc)
        (TashkinovStoredColors corr.replacementSeries.data newi.castSucc)
        (corr.replacementSeries.data.coloring newi.castSucc)) (htree :
        corr.replacementSeries.data.tree newi.succ.castSucc = ett.series.data.tree
        oldi.succ.castSucc),
    let oldChoiceOnNew : MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree
        newi.succ.castSucc) (TashkinovStoredColors ett.series.data oldi.castSucc)
        (ett.series.data.coloring oldi.castSucc) := transportDefectiveChoice (Eq.symm htree)
        oldChoice;
    ∀ (_ : s(oldChoiceOnNew.vertex, oldChoiceOnNew.otherEndpoint) = s(newChoice.vertex,
        newChoice.otherEndpoint)) (_ : StableColoring (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)
        sigma), ColoredVertexSetClosed G sigma (TreeSequenceVertexSet (ett.series.data.tree
        q.succ.castSucc)) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma hsigmaProper hsigmaOne _ q
      previousProper previousOneUncolored previousClosed hroundLarge originalPrefix corr oldi
      oldChoice newi newChoice htree oldChoiceOnNew hends hsigmaPrevStableQ f c v hf hv hsf hcm
  obtain ⟨x, hx, y, hy, hends⟩ := by simpa [BoundaryEdges] using hf
  have hxf : Incident G x f := by
    unfold Incident
    rw [hends]
    exact Sym2.mem_mk_left _ _
  have hmissingEq := hsigmaPrevStableQ.2 v hv
  have hcTree :
    c ∈
      TreeMissingColors (ett.series.data.coloring q.castSucc)
        (ett.series.data.tree q.succ.castSucc) := by
    simp only [TreeMissingColors, Finset.mem_biUnion]
    exact ⟨v, hv, hmissingEq ▸ hcm⟩
  have hcriterion :=
    (sc1 G e0 (ett.series.data.tree q.succ.castSucc)
          (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)
          sigma previousProper previousOneUncolored hsigmaProper hsigmaOne).mp
      hsigmaPrevStableQ
  have hcopy := hcriterion f ⟨x, hx, hxf⟩ (Or.inr ⟨c, Finset.mem_union_left _ hcTree, hsf⟩)
  have holdf : ett.series.data.coloring q.castSucc f = some c := hcopy.symm.trans hsf
  have hnotOld := previousClosed hf hv holdf
  exact hnotOld (hmissingEq ▸ hcm)

theorem helper_outsideIndicesNonempty_4016.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (available : RevisitingExtensionCertificate ett.series.data q.castSucc) (hroundLarge : (1 :
        ℕ) < ett.rounds) (originalPrefix : ExtendedTashkinovTree G k e0 input
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) (ett.series.data.coloring
        (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (_ : originalPrefix.rounds = ett.rounds - (1 : ℕ)) (corr :
        CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigma (ett.series.data.tree
        (Fin.last ett.rounds).castSucc)) (_ : (↑available.earlier : ℕ) < originalPrefix.rounds +
        (1 : ℕ)) (oldi : Fin ett.rounds) (oldChoice : MaximumDefectiveChoice G e0
        (ett.series.data.tree oldi.succ.castSucc) (TashkinovStoredColors ett.series.data
        oldi.castSucc) (ett.series.data.coloring oldi.castSucc)) (oldGamma : Fin k) (newi : Fin
        originalPrefix.rounds) (newChoice : MaximumDefectiveChoice G e0
        (corr.replacementSeries.data.tree newi.succ.castSucc) (TashkinovStoredColors
        corr.replacementSeries.data newi.castSucc) (corr.replacementSeries.data.coloring
        newi.castSucc)) (newGamma : Fin k) (htree : corr.replacementSeries.data.tree
        newi.succ.castSucc = ett.series.data.tree oldi.succ.castSucc),
    let oldChoiceOnNew : MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree
        newi.succ.castSucc) (TashkinovStoredColors ett.series.data oldi.castSucc)
        (ett.series.data.coloring oldi.castSucc) := transportDefectiveChoice (Eq.symm htree)
        oldChoice;
    ∀ (_ : oldChoiceOnNew.color = oldChoice.color) (_ : oldGamma ≠ oldChoice.color) (_ : newGamma
        ≠ newChoice.color) (_ : newChoice.color = oldChoiceOnNew.color) (_ : newGamma = oldGamma)
        (_ : oldChoice.color = available.delta) (_ : oldGamma = available.gamma) (replacementCycle
        : TwoColorCycle G sigma available.gamma available.delta),
    let currentTree : Finset V := TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc);
    ∀ (hreturnCycle : Sum.inl available.returnVertex ∈ replacementCycle.walk.support) (_ :
        available.outsideEndpoint ∉ currentTree),
    let rootedCycle : (TwoColorIncidenceGraph G sigma available.gamma available.delta).Walk
        (Sum.inl available.returnVertex) (Sum.inl available.returnVertex) :=
        replacementCycle.walk.rotate (Sum.inl available.returnVertex) hreturnCycle;
    ∀ (_ : Sum.inl available.outsideEndpoint ∈ rootedCycle.support),
    let outsideIndices : Finset (Fin (rootedCycle.length + (1 : ℕ))) := ({i : Fin
        (rootedCycle.length + (1 : ℕ)) |
    ∃ (v : V), rootedCycle.getVert (↑i : ℕ) = Sum.inl v ∧ v ∉ currentTree} : Finset (Fin
        (rootedCycle.length + (1 : ℕ)))); outsideIndices.Nonempty := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hpositive sigma _ q available hroundLarge
    originalPrefix hr corr earlierPrefixBound oldi oldChoice oldGamma newi newChoice newGamma htree
    oldChoiceOnNew holdColorCast holdColorNe hnewColorNe hidentifiedDelta hidentifiedGamma
    holdDeltaAvailable holdGammaAvailable replacementCycle currentTree hreturnCycle
    houtsideNotCurrent rootedCycle houtsideRooted outsideIndices
  obtain ⟨m, hm, hmle⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp houtsideRooted
  let idx : Fin (rootedCycle.length + 1) := ⟨m, by omega⟩
  refine ⟨idx, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  exact ⟨available.outsideEndpoint, by simpa [idx] using hm, houtsideNotCurrent⟩

theorem helper_beforeFirstOutside_4031.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (available : RevisitingExtensionCertificate ett.series.data q.castSucc) (hroundLarge : (1 :
        ℕ) < ett.rounds) (originalPrefix : ExtendedTashkinovTree G k e0 input
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) (ett.series.data.coloring
        (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (_ : originalPrefix.rounds = ett.rounds - (1 : ℕ)) (corr :
        CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigma (ett.series.data.tree
        (Fin.last ett.rounds).castSucc)) (_ : (↑available.earlier : ℕ) < originalPrefix.rounds +
        (1 : ℕ)) (oldi : Fin ett.rounds) (oldChoice : MaximumDefectiveChoice G e0
        (ett.series.data.tree oldi.succ.castSucc) (TashkinovStoredColors ett.series.data
        oldi.castSucc) (ett.series.data.coloring oldi.castSucc)) (oldGamma : Fin k) (newi : Fin
        originalPrefix.rounds) (newChoice : MaximumDefectiveChoice G e0
        (corr.replacementSeries.data.tree newi.succ.castSucc) (TashkinovStoredColors
        corr.replacementSeries.data newi.castSucc) (corr.replacementSeries.data.coloring
        newi.castSucc)) (newGamma : Fin k) (htree : corr.replacementSeries.data.tree
        newi.succ.castSucc = ett.series.data.tree oldi.succ.castSucc),
    let oldChoiceOnNew : MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree
        newi.succ.castSucc) (TashkinovStoredColors ett.series.data oldi.castSucc)
        (ett.series.data.coloring oldi.castSucc) := transportDefectiveChoice (Eq.symm htree)
        oldChoice;
    ∀ (_ : oldChoiceOnNew.color = oldChoice.color) (_ : oldGamma ≠ oldChoice.color) (_ : newGamma
        ≠ newChoice.color) (_ : newChoice.color = oldChoiceOnNew.color) (_ : newGamma = oldGamma)
        (_ : oldChoice.color = available.delta) (_ : oldGamma = available.gamma) (replacementCycle
        : TwoColorCycle G sigma available.gamma available.delta),
    let currentTree : Finset V := TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc);
    ∀ (hreturnCycle : Sum.inl available.returnVertex ∈ replacementCycle.walk.support),
    let rootedCycle : (TwoColorIncidenceGraph G sigma available.gamma available.delta).Walk
        (Sum.inl available.returnVertex) (Sum.inl available.returnVertex) :=
        replacementCycle.walk.rotate (Sum.inl available.returnVertex) hreturnCycle;
    let outsideIndices : Finset (Fin (rootedCycle.length + (1 : ℕ))) := ({i : Fin
        (rootedCycle.length + (1 : ℕ)) |
    ∃ (v : V), rootedCycle.getVert (↑i : ℕ) = Sum.inl v ∧ v ∉ currentTree} : Finset (Fin
        (rootedCycle.length + (1 : ℕ))));
    ∀ (outsideIndicesNonempty : outsideIndices.Nonempty),
    let firstOutside : Fin (rootedCycle.length + (1 : ℕ)) := outsideIndices.min'
        outsideIndicesNonempty;
    ∀ (idx : Fin (rootedCycle.length + (1 : ℕ))), (↑idx : ℕ) < (↑firstOutside : ℕ) →
    ∀ (v : V), rootedCycle.getVert (↑idx : ℕ) = Sum.inl v → v ∈ currentTree := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hpositive sigma _ q available hroundLarge
      originalPrefix hr corr earlierPrefixBound oldi oldChoice oldGamma newi newChoice newGamma
      htree oldChoiceOnNew holdColorCast holdColorNe hnewColorNe hidentifiedDelta hidentifiedGamma
      holdDeltaAvailable holdGammaAvailable replacementCycle currentTree hreturnCycle rootedCycle
      outsideIndices outsideIndicesNonempty firstOutside idx hidx v hv
  by_contra hvNot
  have hmem : idx ∈ outsideIndices := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨v, hv, hvNot⟩⟩
  have hmin := Finset.min'_le outsideIndices idx hmem
  omega

theorem helper_firstOutsidePositive_4043.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (available : RevisitingExtensionCertificate ett.series.data q.castSucc) (hroundLarge : (1 :
        ℕ) < ett.rounds) (originalPrefix : ExtendedTashkinovTree G k e0 input
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) (ett.series.data.coloring
        (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (_ : originalPrefix.rounds = ett.rounds - (1 : ℕ)) (corr :
        CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigma (ett.series.data.tree
        (Fin.last ett.rounds).castSucc)) (_ : (↑available.earlier : ℕ) < originalPrefix.rounds +
        (1 : ℕ)) (oldi : Fin ett.rounds) (oldChoice : MaximumDefectiveChoice G e0
        (ett.series.data.tree oldi.succ.castSucc) (TashkinovStoredColors ett.series.data
        oldi.castSucc) (ett.series.data.coloring oldi.castSucc)) (oldGamma : Fin k) (newi : Fin
        originalPrefix.rounds) (newChoice : MaximumDefectiveChoice G e0
        (corr.replacementSeries.data.tree newi.succ.castSucc) (TashkinovStoredColors
        corr.replacementSeries.data newi.castSucc) (corr.replacementSeries.data.coloring
        newi.castSucc)) (newGamma : Fin k) (htree : corr.replacementSeries.data.tree
        newi.succ.castSucc = ett.series.data.tree oldi.succ.castSucc),
    let oldChoiceOnNew : MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree
        newi.succ.castSucc) (TashkinovStoredColors ett.series.data oldi.castSucc)
        (ett.series.data.coloring oldi.castSucc) := transportDefectiveChoice (Eq.symm htree)
        oldChoice;
    ∀ (_ : oldChoiceOnNew.color = oldChoice.color) (_ : oldGamma ≠ oldChoice.color) (_ : newGamma
        ≠ newChoice.color) (_ : newChoice.color = oldChoiceOnNew.color) (_ : newGamma = oldGamma)
        (_ : oldChoice.color = available.delta) (_ : oldGamma = available.gamma) (replacementCycle
        : TwoColorCycle G sigma available.gamma available.delta),
    let currentTree : Finset V := TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc);
    ∀ (hreturnCycle : Sum.inl available.returnVertex ∈ replacementCycle.walk.support) (_ :
        available.returnVertex ∈ currentTree),
    let rootedCycle : (TwoColorIncidenceGraph G sigma available.gamma available.delta).Walk
        (Sum.inl available.returnVertex) (Sum.inl available.returnVertex) :=
        replacementCycle.walk.rotate (Sum.inl available.returnVertex) hreturnCycle;
    let outsideIndices : Finset (Fin (rootedCycle.length + (1 : ℕ))) := ({i : Fin
        (rootedCycle.length + (1 : ℕ)) |
    ∃ (v : V), rootedCycle.getVert (↑i : ℕ) = Sum.inl v ∧ v ∉ currentTree} : Finset (Fin
        (rootedCycle.length + (1 : ℕ))));
    ∀ (outsideIndicesNonempty : outsideIndices.Nonempty),
    let firstOutside : Fin (rootedCycle.length + (1 : ℕ)) := outsideIndices.min'
        outsideIndicesNonempty;
    ∀ (outsideOne : V) (_ : rootedCycle.getVert (↑(outsideIndices.min' outsideIndicesNonempty) :
        ℕ) = Sum.inl outsideOne) (_ : outsideOne ∉ currentTree), (0 : ℕ) < (↑firstOutside : ℕ) := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hpositive sigma _ q available hroundLarge
    originalPrefix hr corr earlierPrefixBound oldi oldChoice oldGamma newi newChoice newGamma htree
    oldChoiceOnNew holdColorCast holdColorNe hnewColorNe hidentifiedDelta hidentifiedGamma
    holdDeltaAvailable holdGammaAvailable replacementCycle currentTree hreturnCycle hreturnCurrent
    rootedCycle outsideIndices outsideIndicesNonempty firstOutside outsideOne houtsideOneAt
    houtsideOneNot
  by_contra hnot
  have hzero : firstOutside.val = 0 := by omega
  have heq : outsideOne = available.returnVertex := by
    apply Sum.inl.inj
    calc
      Sum.inl outsideOne = rootedCycle.getVert firstOutside.val := houtsideOneAt.symm
      _ = rootedCycle.getVert 0 := by rw [hzero]
      _ = Sum.inl available.returnVertex := rootedCycle.getVert_zero
  exact houtsideOneNot (heq.symm ▸ hreturnCurrent)

theorem helper_firstOutsideLt_4055.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (available : RevisitingExtensionCertificate ett.series.data q.castSucc) (hroundLarge : (1 :
        ℕ) < ett.rounds) (originalPrefix : ExtendedTashkinovTree G k e0 input
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) (ett.series.data.coloring
        (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (_ : originalPrefix.rounds = ett.rounds - (1 : ℕ)) (corr :
        CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigma (ett.series.data.tree
        (Fin.last ett.rounds).castSucc)) (_ : (↑available.earlier : ℕ) < originalPrefix.rounds +
        (1 : ℕ)) (oldi : Fin ett.rounds) (oldChoice : MaximumDefectiveChoice G e0
        (ett.series.data.tree oldi.succ.castSucc) (TashkinovStoredColors ett.series.data
        oldi.castSucc) (ett.series.data.coloring oldi.castSucc)) (oldGamma : Fin k) (newi : Fin
        originalPrefix.rounds) (newChoice : MaximumDefectiveChoice G e0
        (corr.replacementSeries.data.tree newi.succ.castSucc) (TashkinovStoredColors
        corr.replacementSeries.data newi.castSucc) (corr.replacementSeries.data.coloring
        newi.castSucc)) (newGamma : Fin k) (htree : corr.replacementSeries.data.tree
        newi.succ.castSucc = ett.series.data.tree oldi.succ.castSucc),
    let oldChoiceOnNew : MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree
        newi.succ.castSucc) (TashkinovStoredColors ett.series.data oldi.castSucc)
        (ett.series.data.coloring oldi.castSucc) := transportDefectiveChoice (Eq.symm htree)
        oldChoice;
    ∀ (_ : oldChoiceOnNew.color = oldChoice.color) (_ : oldGamma ≠ oldChoice.color) (_ : newGamma
        ≠ newChoice.color) (_ : newChoice.color = oldChoiceOnNew.color) (_ : newGamma = oldGamma)
        (_ : oldChoice.color = available.delta) (_ : oldGamma = available.gamma) (replacementCycle
        : TwoColorCycle G sigma available.gamma available.delta),
    let currentTree : Finset V := TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc);
    ∀ (hreturnCycle : Sum.inl available.returnVertex ∈ replacementCycle.walk.support) (_ :
        available.returnVertex ∈ currentTree),
    let rootedCycle : (TwoColorIncidenceGraph G sigma available.gamma available.delta).Walk
        (Sum.inl available.returnVertex) (Sum.inl available.returnVertex) :=
        replacementCycle.walk.rotate (Sum.inl available.returnVertex) hreturnCycle;
    let outsideIndices : Finset (Fin (rootedCycle.length + (1 : ℕ))) := ({i : Fin
        (rootedCycle.length + (1 : ℕ)) |
    ∃ (v : V), rootedCycle.getVert (↑i : ℕ) = Sum.inl v ∧ v ∉ currentTree} : Finset (Fin
        (rootedCycle.length + (1 : ℕ))));
    ∀ (outsideIndicesNonempty : outsideIndices.Nonempty),
    let firstOutside : Fin (rootedCycle.length + (1 : ℕ)) := outsideIndices.min'
        outsideIndicesNonempty;
    ∀ (outsideOne : V) (_ : rootedCycle.getVert (↑(outsideIndices.min' outsideIndicesNonempty) :
        ℕ) = Sum.inl outsideOne) (_ : outsideOne ∉ currentTree), (↑firstOutside : ℕ) <
        rootedCycle.length := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hpositive sigma _ q available hroundLarge
    originalPrefix hr corr earlierPrefixBound oldi oldChoice oldGamma newi newChoice newGamma htree
    oldChoiceOnNew holdColorCast holdColorNe hnewColorNe hidentifiedDelta hidentifiedGamma
    holdDeltaAvailable holdGammaAvailable replacementCycle currentTree hreturnCycle hreturnCurrent
    rootedCycle outsideIndices outsideIndicesNonempty firstOutside outsideOne houtsideOneAt
    houtsideOneNot
  by_contra hnot
  have hlast : firstOutside.val = rootedCycle.length := by
    have := firstOutside.isLt
    omega
  have heq : outsideOne = available.returnVertex := by
    apply Sum.inl.inj
    calc
      Sum.inl outsideOne = rootedCycle.getVert firstOutside.val := houtsideOneAt.symm
      _ = rootedCycle.getVert rootedCycle.length := by rw [hlast]
      _ = Sum.inl available.returnVertex := rootedCycle.getVert_length
  exact houtsideOneNot (heq.symm ▸ hreturnCurrent)

theorem helper_firstOutsideNotOne_4070.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (available : RevisitingExtensionCertificate ett.series.data q.castSucc) (hroundLarge : (1 :
        ℕ) < ett.rounds) (originalPrefix : ExtendedTashkinovTree G k e0 input
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) (ett.series.data.coloring
        (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (_ : originalPrefix.rounds = ett.rounds - (1 : ℕ)) (corr :
        CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigma (ett.series.data.tree
        (Fin.last ett.rounds).castSucc)) (_ : (↑available.earlier : ℕ) < originalPrefix.rounds +
        (1 : ℕ)) (oldi : Fin ett.rounds) (oldChoice : MaximumDefectiveChoice G e0
        (ett.series.data.tree oldi.succ.castSucc) (TashkinovStoredColors ett.series.data
        oldi.castSucc) (ett.series.data.coloring oldi.castSucc)) (oldGamma : Fin k) (newi : Fin
        originalPrefix.rounds) (newChoice : MaximumDefectiveChoice G e0
        (corr.replacementSeries.data.tree newi.succ.castSucc) (TashkinovStoredColors
        corr.replacementSeries.data newi.castSucc) (corr.replacementSeries.data.coloring
        newi.castSucc)) (newGamma : Fin k) (htree : corr.replacementSeries.data.tree
        newi.succ.castSucc = ett.series.data.tree oldi.succ.castSucc),
    let oldChoiceOnNew : MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree
        newi.succ.castSucc) (TashkinovStoredColors ett.series.data oldi.castSucc)
        (ett.series.data.coloring oldi.castSucc) := transportDefectiveChoice (Eq.symm htree)
        oldChoice;
    ∀ (_ : oldChoiceOnNew.color = oldChoice.color) (_ : oldGamma ≠ oldChoice.color) (_ : newGamma
        ≠ newChoice.color) (_ : newChoice.color = oldChoiceOnNew.color) (_ : newGamma = oldGamma)
        (_ : oldChoice.color = available.delta) (_ : oldGamma = available.gamma) (replacementCycle
        : TwoColorCycle G sigma available.gamma available.delta),
    let currentTree : Finset V := TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc);
    ∀ (hreturnCycle : Sum.inl available.returnVertex ∈ replacementCycle.walk.support),
    let rootedCycle : (TwoColorIncidenceGraph G sigma available.gamma available.delta).Walk
        (Sum.inl available.returnVertex) (Sum.inl available.returnVertex) :=
        replacementCycle.walk.rotate (Sum.inl available.returnVertex) hreturnCycle;
    let outsideIndices : Finset (Fin (rootedCycle.length + (1 : ℕ))) := ({i : Fin
        (rootedCycle.length + (1 : ℕ)) |
    ∃ (v : V), rootedCycle.getVert (↑i : ℕ) = Sum.inl v ∧ v ∉ currentTree} : Finset (Fin
        (rootedCycle.length + (1 : ℕ))));
    ∀ (outsideIndicesNonempty : outsideIndices.Nonempty),
    let firstOutside : Fin (rootedCycle.length + (1 : ℕ)) := outsideIndices.min'
        outsideIndicesNonempty;
    ∀ (outsideOne : V) (_ : rootedCycle.getVert (↑(outsideIndices.min' outsideIndicesNonempty) :
        ℕ) = Sum.inl outsideOne) (_ : (↑firstOutside : ℕ) < rootedCycle.length), (↑firstOutside :
        ℕ) ≠ (1 : ℕ) :=
  by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hpositive sigma _ q available hroundLarge
      originalPrefix hr corr earlierPrefixBound oldi oldChoice oldGamma newi newChoice newGamma
      htree oldChoiceOnNew holdColorCast holdColorNe hnewColorNe hidentifiedDelta hidentifiedGamma
      holdDeltaAvailable holdGammaAvailable replacementCycle currentTree hreturnCycle rootedCycle
      outsideIndices outsideIndicesNonempty firstOutside outsideOne houtsideOneAt firstOutsideLt
      hone
  have hadj := rootedCycle.adj_getVert_succ (i := 0) (by omega)
  have hy : rootedCycle.getVert 1 = Sum.inl outsideOne := by
    have hone' : (outsideIndices.min' outsideIndicesNonempty).val = 1 := hone
    rw [hone'] at houtsideOneAt
    exact houtsideOneAt
  rw [rootedCycle.getVert_zero, hy] at hadj
  simp [TwoColorIncidenceGraph] at hadj

theorem helper_hinsideOneCurrent_4119.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (available : RevisitingExtensionCertificate ett.series.data q.castSucc) (hroundLarge : (1 :
        ℕ) < ett.rounds) (originalPrefix : ExtendedTashkinovTree G k e0 input
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) (ett.series.data.coloring
        (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (_ : originalPrefix.rounds = ett.rounds - (1 : ℕ)) (corr :
        CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigma (ett.series.data.tree
        (Fin.last ett.rounds).castSucc)) (_ : (↑available.earlier : ℕ) < originalPrefix.rounds +
        (1 : ℕ)) (oldi : Fin ett.rounds) (oldChoice : MaximumDefectiveChoice G e0
        (ett.series.data.tree oldi.succ.castSucc) (TashkinovStoredColors ett.series.data
        oldi.castSucc) (ett.series.data.coloring oldi.castSucc)) (oldGamma : Fin k) (newi : Fin
        originalPrefix.rounds) (newChoice : MaximumDefectiveChoice G e0
        (corr.replacementSeries.data.tree newi.succ.castSucc) (TashkinovStoredColors
        corr.replacementSeries.data newi.castSucc) (corr.replacementSeries.data.coloring
        newi.castSucc)) (newGamma : Fin k) (htree : corr.replacementSeries.data.tree
        newi.succ.castSucc = ett.series.data.tree oldi.succ.castSucc),
    let oldChoiceOnNew : MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree
        newi.succ.castSucc) (TashkinovStoredColors ett.series.data oldi.castSucc)
        (ett.series.data.coloring oldi.castSucc) := transportDefectiveChoice (Eq.symm htree)
        oldChoice;
    ∀ (_ : oldChoiceOnNew.color = oldChoice.color) (_ : oldGamma ≠ oldChoice.color) (_ : newGamma
        ≠ newChoice.color) (_ : newChoice.color = oldChoiceOnNew.color) (_ : newGamma = oldGamma)
        (_ : oldChoice.color = available.delta) (_ : oldGamma = available.gamma) (replacementCycle
        : TwoColorCycle G sigma available.gamma available.delta),
    let currentTree : Finset V := TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc);
    ∀ (hreturnCycle : Sum.inl available.returnVertex ∈ replacementCycle.walk.support),
    let rootedCycle : (TwoColorIncidenceGraph G sigma available.gamma available.delta).Walk
        (Sum.inl available.returnVertex) (Sum.inl available.returnVertex) :=
        replacementCycle.walk.rotate (Sum.inl available.returnVertex) hreturnCycle;
    let outsideIndices : Finset (Fin (rootedCycle.length + (1 : ℕ))) := ({i : Fin
        (rootedCycle.length + (1 : ℕ)) |
    ∃ (v : V), rootedCycle.getVert (↑i : ℕ) = Sum.inl v ∧ v ∉ currentTree} : Finset (Fin
        (rootedCycle.length + (1 : ℕ))));
    ∀ (outsideIndicesNonempty : outsideIndices.Nonempty),
    let firstOutside : Fin (rootedCycle.length + (1 : ℕ)) := outsideIndices.min'
        outsideIndicesNonempty;
    ∀ (_ :
    ∀ (idx : Fin (rootedCycle.length + (1 : ℕ))), (↑idx : ℕ) < (↑firstOutside : ℕ) →
    ∀ (v : V), rootedCycle.getVert (↑idx : ℕ) = Sum.inl v → v ∈ currentTree) (_ : (↑firstOutside :
        ℕ) - (1 : ℕ) + (1 : ℕ) = (↑firstOutside : ℕ)) (_ : (↑firstOutside : ℕ) - (2 : ℕ) + (1 : ℕ)
        = (↑firstOutside : ℕ) - (1 : ℕ)) (insideOne : V) (_ : rootedCycle.getVert ((↑firstOutside
        : ℕ) - (2 : ℕ)) = Sum.inl insideOne), insideOne ∈ currentTree := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hpositive sigma _ q available hroundLarge
    originalPrefix hr corr earlierPrefixBound oldi oldChoice oldGamma newi newChoice newGamma htree
    oldChoiceOnNew holdColorCast holdColorNe hnewColorNe hidentifiedDelta hidentifiedGamma
    holdDeltaAvailable holdGammaAvailable replacementCycle currentTree hreturnCycle rootedCycle
    outsideIndices outsideIndicesNonempty firstOutside beforeFirstOutside firstCrossingIndex
    beforeFirstCrossingIndex insideOne hinsideOneAt
  let idx : Fin (rootedCycle.length + 1) :=
    ⟨firstOutside.val - 2, lt_of_le_of_lt (Nat.sub_le _ _) firstOutside.isLt⟩
  apply
    beforeFirstOutside idx
      (by
        change firstOutside.val - 2 < firstOutside.val
        omega)
      insideOne
  simpa [idx] using hinsideOneAt

theorem helper_laterInsideNonempty_4150.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (available : RevisitingExtensionCertificate ett.series.data q.castSucc) (hroundLarge : (1 :
        ℕ) < ett.rounds) (originalPrefix : ExtendedTashkinovTree G k e0 input
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) (ett.series.data.coloring
        (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (_ : originalPrefix.rounds = ett.rounds - (1 : ℕ)) (corr :
        CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigma (ett.series.data.tree
        (Fin.last ett.rounds).castSucc)) (_ : (↑available.earlier : ℕ) < originalPrefix.rounds +
        (1 : ℕ)) (oldi : Fin ett.rounds) (oldChoice : MaximumDefectiveChoice G e0
        (ett.series.data.tree oldi.succ.castSucc) (TashkinovStoredColors ett.series.data
        oldi.castSucc) (ett.series.data.coloring oldi.castSucc)) (oldGamma : Fin k) (newi : Fin
        originalPrefix.rounds) (newChoice : MaximumDefectiveChoice G e0
        (corr.replacementSeries.data.tree newi.succ.castSucc) (TashkinovStoredColors
        corr.replacementSeries.data newi.castSucc) (corr.replacementSeries.data.coloring
        newi.castSucc)) (newGamma : Fin k) (htree : corr.replacementSeries.data.tree
        newi.succ.castSucc = ett.series.data.tree oldi.succ.castSucc),
    let oldChoiceOnNew : MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree
        newi.succ.castSucc) (TashkinovStoredColors ett.series.data oldi.castSucc)
        (ett.series.data.coloring oldi.castSucc) := transportDefectiveChoice (Eq.symm htree)
        oldChoice;
    ∀ (_ : oldChoiceOnNew.color = oldChoice.color) (_ : oldGamma ≠ oldChoice.color) (_ : newGamma
        ≠ newChoice.color) (_ : newChoice.color = oldChoiceOnNew.color) (_ : newGamma = oldGamma)
        (_ : oldChoice.color = available.delta) (_ : oldGamma = available.gamma) (replacementCycle
        : TwoColorCycle G sigma available.gamma available.delta),
    let currentTree : Finset V := TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc);
    ∀ (hreturnCycle : Sum.inl available.returnVertex ∈ replacementCycle.walk.support) (_ :
        available.returnVertex ∈ currentTree),
    let rootedCycle : (TwoColorIncidenceGraph G sigma available.gamma available.delta).Walk
        (Sum.inl available.returnVertex) (Sum.inl available.returnVertex) :=
        replacementCycle.walk.rotate (Sum.inl available.returnVertex) hreturnCycle;
    let outsideIndices : Finset (Fin (rootedCycle.length + (1 : ℕ))) := ({i : Fin
        (rootedCycle.length + (1 : ℕ)) |
    ∃ (v : V), rootedCycle.getVert (↑i : ℕ) = Sum.inl v ∧ v ∉ currentTree} : Finset (Fin
        (rootedCycle.length + (1 : ℕ))));
    ∀ (outsideIndicesNonempty : outsideIndices.Nonempty),
    let firstOutside : Fin (rootedCycle.length + (1 : ℕ)) := outsideIndices.min'
        outsideIndicesNonempty;
    ∀ (_ : (↑firstOutside : ℕ) < rootedCycle.length),
    let laterInsideIndices : Finset (Fin (rootedCycle.length + (1 : ℕ))) := ({idx : Fin
        (rootedCycle.length + (1 : ℕ)) | (↑firstOutside : ℕ) < (↑idx : ℕ) ∧
    ∃ (v : V), rootedCycle.getVert (↑idx : ℕ) = Sum.inl v ∧ v ∈ currentTree} : Finset (Fin
        (rootedCycle.length + (1 : ℕ)))); laterInsideIndices.Nonempty := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hpositive sigma _ q available hroundLarge
    originalPrefix hr corr earlierPrefixBound oldi oldChoice oldGamma newi newChoice newGamma htree
    oldChoiceOnNew holdColorCast holdColorNe hnewColorNe hidentifiedDelta hidentifiedGamma
    holdDeltaAvailable holdGammaAvailable replacementCycle currentTree hreturnCycle hreturnCurrent
    rootedCycle outsideIndices outsideIndicesNonempty firstOutside firstOutsideLt laterInsideIndices
  let idx : Fin (rootedCycle.length + 1) := ⟨rootedCycle.length, by omega⟩
  refine ⟨idx, Finset.mem_filter.mpr ⟨Finset.mem_univ _, firstOutsideLt, ?_⟩⟩
  exact ⟨available.returnVertex, by simp [idx], hreturnCurrent⟩

theorem helper_houtsideTwoNot_4210.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (available : RevisitingExtensionCertificate ett.series.data q.castSucc) (hroundLarge : (1 :
        ℕ) < ett.rounds) (originalPrefix : ExtendedTashkinovTree G k e0 input
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) (ett.series.data.coloring
        (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (_ : originalPrefix.rounds = ett.rounds - (1 : ℕ)) (corr :
        CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigma (ett.series.data.tree
        (Fin.last ett.rounds).castSucc)) (_ : (↑available.earlier : ℕ) < originalPrefix.rounds +
        (1 : ℕ)) (oldi : Fin ett.rounds) (oldChoice : MaximumDefectiveChoice G e0
        (ett.series.data.tree oldi.succ.castSucc) (TashkinovStoredColors ett.series.data
        oldi.castSucc) (ett.series.data.coloring oldi.castSucc)) (oldGamma : Fin k) (newi : Fin
        originalPrefix.rounds) (newChoice : MaximumDefectiveChoice G e0
        (corr.replacementSeries.data.tree newi.succ.castSucc) (TashkinovStoredColors
        corr.replacementSeries.data newi.castSucc) (corr.replacementSeries.data.coloring
        newi.castSucc)) (newGamma : Fin k) (htree : corr.replacementSeries.data.tree
        newi.succ.castSucc = ett.series.data.tree oldi.succ.castSucc),
    let oldChoiceOnNew : MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree
        newi.succ.castSucc) (TashkinovStoredColors ett.series.data oldi.castSucc)
        (ett.series.data.coloring oldi.castSucc) := transportDefectiveChoice (Eq.symm htree)
        oldChoice;
    ∀ (_ : oldChoiceOnNew.color = oldChoice.color) (_ : oldGamma ≠ oldChoice.color) (_ : newGamma
        ≠ newChoice.color) (_ : newChoice.color = oldChoiceOnNew.color) (_ : newGamma = oldGamma)
        (_ : oldChoice.color = available.delta) (_ : oldGamma = available.gamma) (replacementCycle
        : TwoColorCycle G sigma available.gamma available.delta),
    let currentTree : Finset V := TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc);
    ∀ (hreturnCycle : Sum.inl available.returnVertex ∈ replacementCycle.walk.support),
    let rootedCycle : (TwoColorIncidenceGraph G sigma available.gamma available.delta).Walk
        (Sum.inl available.returnVertex) (Sum.inl available.returnVertex) :=
        replacementCycle.walk.rotate (Sum.inl available.returnVertex) hreturnCycle;
    let outsideIndices : Finset (Fin (rootedCycle.length + (1 : ℕ))) := ({i : Fin
        (rootedCycle.length + (1 : ℕ)) |
    ∃ (v : V), rootedCycle.getVert (↑i : ℕ) = Sum.inl v ∧ v ∉ currentTree} : Finset (Fin
        (rootedCycle.length + (1 : ℕ))));
    ∀ (outsideIndicesNonempty : outsideIndices.Nonempty),
    let firstOutside : Fin (rootedCycle.length + (1 : ℕ)) := outsideIndices.min'
        outsideIndicesNonempty;
    ∀ (outsideOne : V) (_ : rootedCycle.getVert (↑(outsideIndices.min' outsideIndicesNonempty) :
        ℕ) = Sum.inl outsideOne) (_ : outsideOne ∉ currentTree) (_ : (↑firstOutside : ℕ) - (1 : ℕ)
        + (1 : ℕ) = (↑firstOutside : ℕ)) (_ : (↑firstOutside : ℕ) - (2 : ℕ) + (1 : ℕ) =
        (↑firstOutside : ℕ) - (1 : ℕ)),
    let laterInsideIndices : Finset (Fin (rootedCycle.length + (1 : ℕ))) := ({idx : Fin
        (rootedCycle.length + (1 : ℕ)) | (↑firstOutside : ℕ) < (↑idx : ℕ) ∧
    ∃ (v : V), rootedCycle.getVert (↑idx : ℕ) = Sum.inl v ∧ v ∈ currentTree} : Finset (Fin
        (rootedCycle.length + (1 : ℕ))));
    ∀ (laterInsideNonempty : laterInsideIndices.Nonempty),
    let firstReturn : Fin (rootedCycle.length + (1 : ℕ)) := laterInsideIndices.min'
        laterInsideNonempty;
    ∀ (_ : (↑firstOutside : ℕ) + (2 : ℕ) ≤ (↑firstReturn : ℕ)) (_ : (↑firstReturn : ℕ) - (1 : ℕ) +
        (1 : ℕ) = (↑firstReturn : ℕ)) (_ : (↑firstReturn : ℕ) - (2 : ℕ) + (1 : ℕ) = (↑firstReturn
        : ℕ) - (1 : ℕ)) (outsideTwo : V) (_ : rootedCycle.getVert ((↑firstReturn : ℕ) - (2 : ℕ)) =
        Sum.inl outsideTwo), outsideTwo ∉ currentTree := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hpositive sigma _ q available hroundLarge
      originalPrefix hr corr earlierPrefixBound oldi oldChoice oldGamma newi newChoice newGamma
      htree oldChoiceOnNew holdColorCast holdColorNe hnewColorNe hidentifiedDelta hidentifiedGamma
      holdDeltaAvailable holdGammaAvailable replacementCycle currentTree hreturnCycle rootedCycle
      outsideIndices outsideIndicesNonempty firstOutside outsideOne houtsideOneAt houtsideOneNot
      firstCrossingIndex beforeFirstCrossingIndex laterInsideIndices laterInsideNonempty firstReturn
      hreturnGap returnCrossingIndex beforeReturnCrossingIndex outsideTwo houtsideTwoAt
      houtsideTwoCurrent
  by_cases heq : firstReturn.val - 2 = firstOutside.val
  · have hvertices : outsideTwo = outsideOne := by
      apply Sum.inl.inj
      calc
        Sum.inl outsideTwo = rootedCycle.getVert (firstReturn.val - 2) := houtsideTwoAt.symm
        _ = rootedCycle.getVert firstOutside.val := by rw [heq]
        _ = Sum.inl outsideOne := houtsideOneAt
    exact houtsideOneNot (hvertices.symm ▸ houtsideTwoCurrent)
  · have hbetween : firstOutside.val < firstReturn.val - 2 := by omega
    let idx : Fin (rootedCycle.length + 1) :=
      ⟨firstReturn.val - 2, lt_of_le_of_lt (Nat.sub_le _ _) firstReturn.isLt⟩
    have hmem : idx ∈ laterInsideIndices :=
      Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, by simpa [idx], outsideTwo, by simpa [idx] using houtsideTwoAt,
          houtsideTwoCurrent⟩
    have hmin := Finset.min'_le laterInsideIndices idx hmem
    have hmin' : firstReturn.val ≤ idx.val := by simpa [firstReturn] using hmin
    simp [idx] at hmin'
    omega

theorem helper_hcrossingEdgesNe_4255.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (available : RevisitingExtensionCertificate ett.series.data q.castSucc) (hroundLarge : (1 :
        ℕ) < ett.rounds) (originalPrefix : ExtendedTashkinovTree G k e0 input
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) (ett.series.data.coloring
        (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (_ : originalPrefix.rounds = ett.rounds - (1 : ℕ)) (corr :
        CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigma (ett.series.data.tree
        (Fin.last ett.rounds).castSucc)) (_ : (↑available.earlier : ℕ) < originalPrefix.rounds +
        (1 : ℕ)) (oldi : Fin ett.rounds) (oldChoice : MaximumDefectiveChoice G e0
        (ett.series.data.tree oldi.succ.castSucc) (TashkinovStoredColors ett.series.data
        oldi.castSucc) (ett.series.data.coloring oldi.castSucc)) (oldGamma : Fin k) (newi : Fin
        originalPrefix.rounds) (newChoice : MaximumDefectiveChoice G e0
        (corr.replacementSeries.data.tree newi.succ.castSucc) (TashkinovStoredColors
        corr.replacementSeries.data newi.castSucc) (corr.replacementSeries.data.coloring
        newi.castSucc)) (newGamma : Fin k) (htree : corr.replacementSeries.data.tree
        newi.succ.castSucc = ett.series.data.tree oldi.succ.castSucc),
    let oldChoiceOnNew : MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree
        newi.succ.castSucc) (TashkinovStoredColors ett.series.data oldi.castSucc)
        (ett.series.data.coloring oldi.castSucc) := transportDefectiveChoice (Eq.symm htree)
        oldChoice;
    ∀ (_ : oldChoiceOnNew.color = oldChoice.color) (_ : oldGamma ≠ oldChoice.color) (_ : newGamma
        ≠ newChoice.color) (_ : newChoice.color = oldChoiceOnNew.color) (_ : newGamma = oldGamma)
        (_ : oldChoice.color = available.delta) (_ : oldGamma = available.gamma) (replacementCycle
        : TwoColorCycle G sigma available.gamma available.delta),
    let currentTree : Finset V := TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc);
    ∀ (hreturnCycle : Sum.inl available.returnVertex ∈ replacementCycle.walk.support),
    let rootedCycle : (TwoColorIncidenceGraph G sigma available.gamma available.delta).Walk
        (Sum.inl available.returnVertex) (Sum.inl available.returnVertex) :=
        replacementCycle.walk.rotate (Sum.inl available.returnVertex) hreturnCycle;
    ∀ (_ : rootedCycle.IsCycle),
    let outsideIndices : Finset (Fin (rootedCycle.length + (1 : ℕ))) := ({i : Fin
        (rootedCycle.length + (1 : ℕ)) |
    ∃ (v : V), rootedCycle.getVert (↑i : ℕ) = Sum.inl v ∧ v ∉ currentTree} : Finset (Fin
        (rootedCycle.length + (1 : ℕ))));
    ∀ (outsideIndicesNonempty : outsideIndices.Nonempty),
    let firstOutside : Fin (rootedCycle.length + (1 : ℕ)) := outsideIndices.min'
        outsideIndicesNonempty;
    ∀ (_ : (↑firstOutside : ℕ) < rootedCycle.length) (_ : (2 : ℕ) ≤ (↑firstOutside : ℕ)) (_ :
        (↑firstOutside : ℕ) - (1 : ℕ) + (1 : ℕ) = (↑firstOutside : ℕ)) (firstEdge : E) (_ :
        rootedCycle.getVert ((↑firstOutside : ℕ) - (1 : ℕ)) = Sum.inr firstEdge) (_ :
        (↑firstOutside : ℕ) - (2 : ℕ) + (1 : ℕ) = (↑firstOutside : ℕ) - (1 : ℕ)),
    let laterInsideIndices : Finset (Fin (rootedCycle.length + (1 : ℕ))) := ({idx : Fin
        (rootedCycle.length + (1 : ℕ)) | (↑firstOutside : ℕ) < (↑idx : ℕ) ∧
    ∃ (v : V), rootedCycle.getVert (↑idx : ℕ) = Sum.inl v ∧ v ∈ currentTree} : Finset (Fin
        (rootedCycle.length + (1 : ℕ))));
    ∀ (laterInsideNonempty : laterInsideIndices.Nonempty),
    let firstReturn : Fin (rootedCycle.length + (1 : ℕ)) := laterInsideIndices.min'
        laterInsideNonempty;
    ∀ (_ : (↑firstOutside : ℕ) + (2 : ℕ) ≤ (↑firstReturn : ℕ)) (_ : (↑firstReturn : ℕ) - (1 : ℕ) +
        (1 : ℕ) = (↑firstReturn : ℕ)) (secondEdge : E) (_ : rootedCycle.getVert ((↑firstReturn :
        ℕ) - (1 : ℕ)) = Sum.inr secondEdge) (_ : (↑firstReturn : ℕ) - (2 : ℕ) + (1 : ℕ) =
        (↑firstReturn : ℕ) - (1 : ℕ)), firstEdge ≠ secondEdge := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hpositive sigma _ q available hroundLarge
      originalPrefix hr corr earlierPrefixBound oldi oldChoice oldGamma newi newChoice newGamma
      htree oldChoiceOnNew holdColorCast holdColorNe hnewColorNe hidentifiedDelta hidentifiedGamma
      holdDeltaAvailable holdGammaAvailable replacementCycle currentTree hreturnCycle rootedCycle
      rootedIsCycle outsideIndices outsideIndicesNonempty firstOutside firstOutsideLt
      firstOutsideAtLeastTwo firstCrossingIndex firstEdge hfirstEdgeAt beforeFirstCrossingIndex
      laterInsideIndices laterInsideNonempty firstReturn hreturnGap returnCrossingIndex secondEdge
      hsecondEdgeAt beforeReturnCrossingIndex heq
  have hp1Positive : 0 < firstOutside.val - 1 := by omega
  have hp1AtMost : firstOutside.val - 1 ≤ rootedCycle.length := by omega
  have hp2Positive : 0 < firstReturn.val - 1 := by omega
  have hreturnAtMost : firstReturn.val ≤ rootedCycle.length := by
    exact Nat.lt_succ_iff.mp firstReturn.isLt
  have hp2AtMost : firstReturn.val - 1 ≤ rootedCycle.length := (Nat.sub_le _ _).trans hreturnAtMost
  have hindices :=
    rootedIsCycle.getVert_injOn
      (by
        simp only [Set.mem_ofPred_eq]
        exact ⟨hp1Positive, hp1AtMost⟩)
      (by
        simp only [Set.mem_ofPred_eq]
        exact ⟨hp2Positive, hp2AtMost⟩)
  have hvertices :
    rootedCycle.getVert (firstOutside.val - 1) = rootedCycle.getVert (firstReturn.val - 1) := by
    rw [hfirstEdgeAt, hsecondEdgeAt, heq]
  have := hindices hvertices
  omega

theorem helper_interveningRevisiting_4368.{u_1, u_2} :
    helperInterveningRevisiting4368Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hpositive sigma _ q hqCast available
      hroundLarge originalPrefix hr hprefixData corr earlierPrefixBound earlierPrefix hearlierMap
      oldi oldChoice oldGamma newi newChoice newGamma htree oldChoiceOnNew holdColorCast holdColorNe
      hnewColorNe hidentifiedDelta hidentifiedGamma holdDeltaAvailable holdGammaAvailable
      replacementLast hreplacementLastMap hgammaDeltaNe replacementCycle currentTree hreturnCycle
      rootedCycle outsideIndices outsideIndicesNonempty firstOutside firstOutsideNotOne
      firstOutsideAtLeastTwo firstCrossingIndex beforeFirstCrossingIndex laterInsideIndices
      laterInsideNonempty firstReturn hreturnNotNext hreturnGap returnCrossingIndex
      beforeReturnCrossingIndex j hjPositive hjLower hjUpper
  rw [corr.extensionKindsAgree j, (hprefixData j).2.2.2.1]
  apply available.interveningRevisiting (Fin.castLE (by omega) j)
  · exact hjPositive
  · have hvals := congrArg Fin.val hearlierMap
    simp only [Fin.val_castLE] at hvals ⊢
    omega
  · simp only [Fin.val_castLE]
    have hupper := hjUpper
    simp [replacementLast] at hupper
    have hqval : q.castSucc.val = originalPrefix.rounds := by simp [q, hr]
    omega

theorem helper_leavesCurrent_4395.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [inst_3 : DecidableEq
        E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (available : RevisitingExtensionCertificate ett.series.data q.castSucc) (hroundLarge : (1 :
        ℕ) < ett.rounds) (originalPrefix : ExtendedTashkinovTree G k e0 input
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) (ett.series.data.coloring
        (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (corr : CorrespondingExtendedTashkinovTree G k e0
        originalPrefix sigma (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
    let replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last originalPrefix.rounds;
    ∀ (replacementCycle : TwoColorCycle G sigma available.gamma available.delta) (_ :
    have replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last
        originalPrefix.rounds; corr.replacementSeries.data.tree replacementLast.succ =
        ett.series.data.tree (Fin.last ett.rounds).castSucc) (_ : ett.series.data.tree
        q.castSucc.succ = ett.series.data.tree (Fin.last ett.rounds).castSucc) (_ : Sum.inl
        available.outsideEndpoint ∈ replacementCycle.walk.support) (hreplacementColor :
        corr.replacementSeries.data.coloring replacementLast = sigma),
    let castCycle : (phi psi : PartialEdgeColoring E k) → (hphi : phi = psi) → (C : TwoColorCycle
        G psi available.gamma available.delta) → TwoColorCycle G phi available.gamma
        available.delta := fun (phi psi : PartialEdgeColoring E k) (hphi : phi = psi) (C :
        TwoColorCycle G psi available.gamma available.delta) ↦ @Eq.ndrec (PartialEdgeColoring E k)
        phi (fun (psi : PartialEdgeColoring E k) ↦ (C : @TwoColorCycle V E G k psi
        (@RevisitingExtensionCertificate.gamma V E inst inst_1 G k (@ExtendedTashkinovTree.rounds
        V E inst inst_1 inst_3 G k e0 input T generating ett) e0 (@TashkinovSeries.data V E inst
        inst_1 inst_3 G k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
        generating ett) e0 input (@ExtendedTashkinovTree.series V E inst inst_1 inst_3 G k e0
        input T generating ett)) (@Fin.castSucc (@ExtendedTashkinovTree.rounds V E inst inst_1
        inst_3 G k e0 input T generating ett) q) available) (@RevisitingExtensionCertificate.delta
        V E inst inst_1 G k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
        generating ett) e0 (@TashkinovSeries.data V E inst inst_1 inst_3 G k
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T generating ett) e0
        input (@ExtendedTashkinovTree.series V E inst inst_1 inst_3 G k e0 input T generating
        ett)) (@Fin.castSucc (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
        generating ett) q) available)) → @TwoColorCycle V E G k phi
        (@RevisitingExtensionCertificate.gamma V E inst inst_1 G k (@ExtendedTashkinovTree.rounds
        V E inst inst_1 inst_3 G k e0 input T generating ett) e0 (@TashkinovSeries.data V E inst
        inst_1 inst_3 G k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
        generating ett) e0 input (@ExtendedTashkinovTree.series V E inst inst_1 inst_3 G k e0
        input T generating ett)) (@Fin.castSucc (@ExtendedTashkinovTree.rounds V E inst inst_1
        inst_3 G k e0 input T generating ett) q) available) (@RevisitingExtensionCertificate.delta
        V E inst inst_1 G k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
        generating ett) e0 (@TashkinovSeries.data V E inst inst_1 inst_3 G k
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T generating ett) e0
        input (@ExtendedTashkinovTree.series V E inst inst_1 inst_3 G k e0 input T generating
        ett)) (@Fin.castSucc (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
        generating ett) q) available)) (fun (C : @TwoColorCycle V E G k phi
        (@RevisitingExtensionCertificate.gamma V E inst inst_1 G k (@ExtendedTashkinovTree.rounds
        V E inst inst_1 inst_3 G k e0 input T generating ett) e0 (@TashkinovSeries.data V E inst
        inst_1 inst_3 G k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
        generating ett) e0 input (@ExtendedTashkinovTree.series V E inst inst_1 inst_3 G k e0
        input T generating ett)) (@Fin.castSucc (@ExtendedTashkinovTree.rounds V E inst inst_1
        inst_3 G k e0 input T generating ett) q) available) (@RevisitingExtensionCertificate.delta
        V E inst inst_1 G k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
        generating ett) e0 (@TashkinovSeries.data V E inst inst_1 inst_3 G k
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T generating ett) e0
        input (@ExtendedTashkinovTree.series V E inst inst_1 inst_3 G k e0 input T generating
        ett)) (@Fin.castSucc (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T
        generating ett) q) available)) ↦ C) psi hphi C;
    ∀ (_ :
    ∀ (phi psi : PartialEdgeColoring E k) (hphi : phi = psi) (C : TwoColorCycle G psi
        available.gamma available.delta) (z : V ⊕ E), z ∈ (castCycle phi psi hphi C).walk.support
        ↔ z ∈ C.walk.support),
    let replacementCycleForPrefix : TwoColorCycle G (corr.replacementSeries.data.coloring
        replacementLast) available.gamma available.delta := castCycle
        (corr.replacementSeries.data.coloring replacementLast) sigma hreplacementColor
        replacementCycle;
    ∃ u ∉ TreeSequenceVertexSet (corr.replacementSeries.data.tree replacementLast.succ), Sum.inl u
        ∈ replacementCycleForPrefix.walk.support := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma _ q available hroundLarge
    originalPrefix corr replacementLast replacementCycle hreplacementCurrentTree
    havailableCurrentTree houtsideCycle hreplacementColor castCycle castCycleSupport
    replacementCycleForPrefix
  refine ⟨available.outsideEndpoint, ?_, ?_⟩
  · rw [hreplacementCurrentTree, ← havailableCurrentTree]
    exact available.outsideNotCurrent
  · exact (castCycleSupport _ _ hreplacementColor replacementCycle _).2 houtsideCycle

theorem helper_returnPathOnCycle_4421.{u_1, u_2} :
    helperReturnPathOnCycle4421Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma _ q available hroundLarge
      originalPrefix corr replacementLast sigmaReturnGraph returnEdgeTransfer sigmaReturnPath
      replacementCycle hreplacementColor castReturnWalk castReturnWalkSupport castCycle
      castCycleSupport replacementCycleForPrefix replacementReturnPath hsigmaPathOnCycle z hz
  apply (castCycleSupport _ _ hreplacementColor replacementCycle _).2
  apply hsigmaPathOnCycle
  exact (castReturnWalkSupport _ _ hreplacementColor sigmaReturnPath z).1 hz

theorem helper_returnPathInternal_4428.{u_1, u_2} : returnPathInternalStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma _ q available hroundLarge
      originalPrefix corr replacementLast sigmaReturnGraph returnEdgeTransfer sigmaReturnPath
      hsigmaReturnSupport hreplacementCurrentTree havailableCurrentTree hreplacementColor
      castReturnWalk castReturnWalkSupport replacementReturnPath v hv
  have hvOld : Sum.inl v ∈ available.returnPath.support :=
    (hsigmaReturnSupport (Sum.inl v)).mp
      ((castReturnWalkSupport _ _ hreplacementColor sigmaReturnPath _).1 hv)
  rw [hreplacementCurrentTree, ← havailableCurrentTree]
  exact available.returnPathInternal v hvOld

end GoldbergSeymour.TerminalRebuild

end
