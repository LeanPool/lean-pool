/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/

module

public import LeanPool.GoldbergSeymour.TashkinovSeriesStability


public import LeanPool.GoldbergSeymour.RevisitingTerminalStatements
public import LeanPool.GoldbergSeymour.TashkinovSeriesAppend
public import LeanPool.GoldbergSeymour.TdReplacementPrefixExact
public import LeanPool.GoldbergSeymour.TdEarlierPEWitnessIdentification

/-!
# Rebuilding a revisiting terminal extension

Supporting material for the Goldberg–Seymour revisiting construction.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
-/

@[expose] public section

namespace GoldbergSeymour.TerminalRebuild

private abbrev revisitingFirstCrossingStatement.{u_1, u_2} : Prop :=
 open scoped Classical Sym2 in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T generating) (hpositive : 0 < ett.rounds),
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
  ∀ (fstar : E) (seed : TreeSequence G e0),
  ett.series.data.connectingEdges (Fin.last ett.rounds) = { fstar } →
  TreeSequenceAdjoinEdge (ett.series.data.tree (Fin.last ett.rounds).castSucc) fstar
    seed →
  ∀ (closureTree : TreeSequence G e0),
  TashkinovClosure sigma seed closureTree →
  TreeSequenceInitialSegment Tstar closureTree →
  TreeSequenceInitialSegment (ett.series.data.tree (Fin.last ett.rounds).castSucc)
    closureTree →
  let q : Fin ett.rounds := (⟨ett.rounds - 1, (by omega)⟩ : Fin ett.rounds);
  q.succ = Fin.last ett.rounds →
  q.castSucc = (⟨ett.rounds - 1, (by omega)⟩ : Fin (ett.rounds + 1)) →
  ∀ (adjoined : TreeSequence G e0),
  IsProperEdgeColoring G (ett.series.data.coloring q.castSucc) →
  IsOneEdgeUncolored (ett.series.data.coloring q.castSucc) e0 →
  ColoredVertexSetClosed G (ett.series.data.coloring q.castSucc)
    (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) →
  ∀ (available : RevisitingExtensionCertificate ett.series.data q.castSucc),
  ett.series.data.stored q.succ = { available.delta, available.gamma } →
  ett.series.data.connectingEdges q.succ = { available.edge } →
  ett.series.data.kind q.succ = some TashkinovExtensionKind.RE →
  ∀ (hroundLarge : 1 < ett.rounds)
   (originalPrefix :
    ExtendedTashkinovTree G k e0 input
     (ett.series.data.tree (Fin.last ett.rounds).castSucc)
     (ett.series.data.coloring
      (⟨ett.rounds - 1, (by omega)⟩ : Fin (ett.rounds + 1))))
   (hr : originalPrefix.rounds = ett.rounds - 1),
  (
  ∀ (i : Fin (originalPrefix.rounds + 2)),
  originalPrefix.series.data.tree i =
   ett.series.data.tree (Fin.castLE ((by omega)) i)) →
  (
  ∀ (i : Fin (originalPrefix.rounds + 1)),
  originalPrefix.series.data.coloring i =
    ett.series.data.coloring (Fin.castLE ((by omega)) i) ∧
   originalPrefix.series.data.stored i =
     ett.series.data.stored (Fin.castLE ((by omega)) i) ∧
    originalPrefix.series.data.connectingEdges i =
      ett.series.data.connectingEdges (Fin.castLE ((by omega)) i) ∧
     originalPrefix.series.data.kind i =
       ett.series.data.kind (Fin.castLE ((by omega)) i) ∧
      TashkinovStoredColors originalPrefix.series.data i =
       TashkinovStoredColors ett.series.data
        (Fin.castLE ((by omega)) i)) →
  ∀
   (corr :
    CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigma
     (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
  corr.replacementSeries.data.tree
     (Fin.last (originalPrefix.rounds + 1)) =
    ett.series.data.tree (Fin.last ett.rounds).castSucc →
  corr.replacementSeries.data.coloring
     (Fin.last originalPrefix.rounds) =
    sigma →
  MaximumProperty corr.replacementETT →
  ∀
   (earlierPrefixBound :
    (↑available.earlier : ℕ) < originalPrefix.rounds + 1),
  let earlierPrefix : Fin (originalPrefix.rounds + 1) :=
   (⟨(↑available.earlier : ℕ), earlierPrefixBound⟩ :
    Fin (originalPrefix.rounds + 1));
  Fin.castLE ((by omega)) earlierPrefix = available.earlier →
  0 < (↑earlierPrefix : ℕ) →
  corr.replacementSeries.data.kind earlierPrefix =
    some TashkinovExtensionKind.PE →
  ∀ (oldi : Fin ett.rounds)
   (oldChoice :
    MaximumDefectiveChoice G e0
     (ett.series.data.tree oldi.succ.castSucc)
     (TashkinovStoredColors ett.series.data oldi.castSucc)
     (ett.series.data.coloring oldi.castSucc))
   (oldGamma : Fin k),
  available.earlier = oldi.succ →
  ∀ (newi : Fin originalPrefix.rounds)
   (newChoice :
    MaximumDefectiveChoice G e0
     (corr.replacementSeries.data.tree newi.succ.castSucc)
     (TashkinovStoredColors corr.replacementSeries.data
      newi.castSucc)
     (corr.replacementSeries.data.coloring newi.castSucc))
   (newGamma : Fin k),
  corr.replacementSeries.data.delta newi.succ =
    some newChoice.color →
  corr.replacementSeries.data.gamma newi.succ =
    some newGamma →
  newi.succ = earlierPrefix →
  ∀
   (htree :
    corr.replacementSeries.data.tree newi.succ.castSucc =
     ett.series.data.tree oldi.succ.castSucc),
  let oldChoiceOnNew :
   MaximumDefectiveChoice G e0
    (corr.replacementSeries.data.tree
     newi.succ.castSucc)
    (TashkinovStoredColors ett.series.data
     oldi.castSucc)
    (ett.series.data.coloring oldi.castSucc) :=
   transportDefectiveChoice htree.symm oldChoice;
  ∀
   (holdColorCast :
    oldChoiceOnNew.color = oldChoice.color),
  s(oldChoiceOnNew.vertex,
     oldChoiceOnNew.otherEndpoint) =
    s(newChoice.vertex, newChoice.otherEndpoint) →
  ∀ (holdColorNe : oldGamma ≠ oldChoice.color)
   (hnewColorNe : newGamma ≠ newChoice.color)
   (hidentifiedDelta :
    newChoice.color = oldChoiceOnNew.color)
   (hidentifiedGamma : newGamma = oldGamma)
   (holdDeltaAvailable :
    oldChoice.color = available.delta)
   (holdGammaAvailable : oldGamma = available.gamma),
  newChoice.color = available.delta →
  newGamma = available.gamma →
  let replacementLast :
   Fin (originalPrefix.rounds + 1) :=
   Fin.last originalPrefix.rounds;
  Fin.castLE ((by omega)) replacementLast =
    q.castSucc →
  available.delta ∈
    MissingColors G sigma newChoice.vertex →
  available.gamma ≠ available.delta →
  newChoice.vertex ∈
    TreeSequenceVertexSet
     (ett.series.data.tree
      (Fin.last ett.rounds).castSucc) →
  TwoColorNontrivialPathComponent G sigma
    available.gamma available.delta
    (Sum.inl newChoice.vertex) →
  (∃
    v ∈
     TreeSequenceVertexSet
      (ett.series.data.tree
       (Fin.last ett.rounds).castSucc),
    Sum.inl v ∈
     TwoColorComponent G sigma available.gamma
      available.delta
      (Sum.inl newChoice.vertex)) →
  StableColoring
    (ett.series.data.tree q.succ.castSucc)
    (TashkinovStoredColors ett.series.data
     q.castSucc)
    (ett.series.data.coloring q.castSucc)
    sigma →
  let sigmaReturnGraph :
   SimpleGraph (V ⊕ E) :=
   TwoColorIncidenceGraph G sigma
    available.gamma available.delta;
  ∀
   (returnEdgeTransfer :
    ∀ edge ∈ available.returnPath.edges,
     edge ∈ sigmaReturnGraph.edgeSet),
  let sigmaReturnPath :
   sigmaReturnGraph.Walk
    (Sum.inr available.edge)
    (Sum.inl available.returnVertex) :=
   available.returnPath.transfer
    sigmaReturnGraph returnEdgeTransfer;
  sigmaReturnPath.IsPath →
  (
  ∀ (z : V ⊕ E),
  z ∈ sigmaReturnPath.support ↔
   z ∈ available.returnPath.support) →
  Sum.inl available.returnVertex ∈
    TwoColorComponent G sigma
     available.gamma available.delta
     (Sum.inr available.edge) →
  Sum.inl available.outsideEndpoint ∈
    TwoColorComponent G sigma
     available.gamma available.delta
     (Sum.inr available.edge) →
  available.returnVertex ∈
    TreeSequenceVertexSet
     (corr.replacementSeries.data.tree
      earlierPrefix.castSucc) →
  available.returnVertex ∈
    TreeSequenceVertexSet
     (ett.series.data.tree
      (Fin.last
        ett.rounds).castSucc) →
  TwoColorComponent G sigma
     available.gamma available.delta
     (Sum.inl newChoice.vertex) ≠
    TwoColorComponent G sigma
     available.gamma available.delta
     (Sum.inr available.edge) →
  (∃
    v ∈
     TreeSequenceVertexSet
      (ett.series.data.tree
       (Fin.last
         ett.rounds).castSucc),
    Sum.inl v ∈
     TwoColorComponent G sigma
      available.gamma
      available.delta
      (Sum.inr available.edge)) →
  0 < corr.replacementETT.rounds →
  corr.replacementETT.rounds <
    ett.rounds →
  (
  ∀
   (C :
    CorrespondingExtendedTashkinovTree
     G k e0 originalPrefix sigma
     (ett.series.data.tree
      (Fin.last
        ett.rounds).castSucc)),
  C.replacementETT.series.data.tree
    (Fin.last
     (C.replacementETT.rounds +
      1)) =
   C.replacementSeries.data.tree
    (Fin.last
     (originalPrefix.rounds +
      1))) →
  corr.replacementETT.series.data.tree
     (Fin.last
      (corr.replacementETT.rounds +
       1)) =
    corr.replacementSeries.data.tree
     (Fin.last
      (originalPrefix.rounds +
       1)) →
  corr.replacementETT.series.data.coloring
     (Fin.last
      corr.replacementETT.rounds) =
    sigma →
  StableColoring
    (corr.replacementETT.series.data.tree
     (Fin.last
      (corr.replacementETT.rounds +
       1)))
    (TashkinovStoredColors
     corr.replacementETT.series.data
     (Fin.last
      corr.replacementETT.rounds))
    (corr.replacementETT.series.data.coloring
     (Fin.last
      corr.replacementETT.rounds))
    sigma →
  corr.replacementETT.series.data.tree
     (Fin.last
      (corr.replacementETT.rounds +
       1)) =
    ett.series.data.tree
     (Fin.last
       ett.rounds).castSucc →
  available.delta ∈
    TreeMissingColors sigma
     (corr.replacementETT.series.data.tree
      (Fin.last
       (corr.replacementETT.rounds +
        1))) →
  LowerRoundProperties
    corr.replacementETT →
  TreeInterchangeable G
    (corr.replacementETT.series.data.tree
     (Fin.last
      (corr.replacementETT.rounds +
       1)))
    sigma available.gamma
    available.delta →
  TreeInterchangeable G
    (ett.series.data.tree
     (Fin.last
       ett.rounds).castSucc)
    sigma available.gamma
    available.delta →
  ∀
   (replacementCycle :
    TwoColorCycle G
     sigma
     available.gamma
     available.delta),
  (
  ∀ (x : V ⊕ E),
  x ∈
    replacementCycle.walk.support ↔
   x ∈
    TwoColorComponent
     G sigma
     available.gamma
     available.delta
     (Sum.inr
      available.edge)) →
  ColoredVertexSetClosed
    G sigma
    (TreeSequenceVertexSet
     (ett.series.data.tree
      q.succ.castSucc)) →
  ColoredVertexSetClosed
    G sigma
    (TreeSequenceVertexSet
     (ett.series.data.tree
      (Fin.last
        ett.rounds).castSucc)) →
  (
  have
   replacementLast :
   Fin
    (originalPrefix.rounds +
     1) :=
   Fin.last
    originalPrefix.rounds;
  corr.replacementSeries.data.tree
    replacementLast.succ =
   ett.series.data.tree
    (Fin.last
      ett.rounds).castSucc) →
  q.castSucc.succ =
    (Fin.last
      ett.rounds).castSucc →
  ett.series.data.tree
     q.castSucc.succ =
    ett.series.data.tree
     (Fin.last
       ett.rounds).castSucc →
  let
   currentTree :
   Finset V :=
   TreeSequenceVertexSet
    (ett.series.data.tree
     q.succ.castSucc);
  ∀
   (hreturnCycle :
    Sum.inl
      available.returnVertex ∈
     replacementCycle.walk.support),
  Sum.inl
     available.outsideEndpoint ∈
    replacementCycle.walk.support →
  available.returnVertex ∈
    currentTree →
  available.outsideEndpoint ∉
    currentTree →
  let
   rootedCycle :
   (TwoColorIncidenceGraph
      G sigma
      available.gamma
      available.delta).Walk
    (Sum.inl
     available.returnVertex)
    (Sum.inl
     available.returnVertex) :=
   replacementCycle.walk.rotate
    (Sum.inl
     available.returnVertex)
    hreturnCycle;
  rootedCycle.IsCycle →
  Sum.inl
     available.outsideEndpoint ∈
    rootedCycle.support →
  let
   outsideIndices :
   Finset
    (Fin
     (rootedCycle.length +
      1)) :=
   {i :
    Fin
     (rootedCycle.length +
      1) |
    ∃ (v :
     V),
     rootedCycle.getVert
        (↑i :
         ℕ) =
       Sum.inl
        v ∧
      v ∉
       currentTree};
  ∀
   (outsideIndicesNonempty :
    outsideIndices.Nonempty),
  let
   firstOutside :
   Fin
    (rootedCycle.length +
     1) :=
   outsideIndices.min'
    outsideIndicesNonempty;
  Nonempty
   (CorrespondingExtendedTashkinovTree
    G k e0
    ett
    sigma
    Tstar)

private abbrev revisitingReturnCrossingStatement.{u_1, u_2} : Prop :=
 open scoped Classical Sym2 in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T generating) (hpositive : 0 < ett.rounds),
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
  ∀ (fstar : E) (seed : TreeSequence G e0),
  ett.series.data.connectingEdges (Fin.last ett.rounds) = { fstar } →
  TreeSequenceAdjoinEdge (ett.series.data.tree (Fin.last ett.rounds).castSucc) fstar
    seed →
  ∀ (closureTree : TreeSequence G e0),
  TashkinovClosure sigma seed closureTree →
  TreeSequenceInitialSegment Tstar closureTree →
  TreeSequenceInitialSegment (ett.series.data.tree (Fin.last ett.rounds).castSucc)
    closureTree →
  let q : Fin ett.rounds := (⟨ett.rounds - 1, (by omega)⟩ : Fin ett.rounds);
  q.succ = Fin.last ett.rounds →
  q.castSucc = (⟨ett.rounds - 1, (by omega)⟩ : Fin (ett.rounds + 1)) →
  ∀ (adjoined : TreeSequence G e0),
  IsProperEdgeColoring G (ett.series.data.coloring q.castSucc) →
  IsOneEdgeUncolored (ett.series.data.coloring q.castSucc) e0 →
  ColoredVertexSetClosed G (ett.series.data.coloring q.castSucc)
    (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) →
  ∀ (available : RevisitingExtensionCertificate ett.series.data q.castSucc),
  ett.series.data.stored q.succ = { available.delta, available.gamma } →
  ett.series.data.connectingEdges q.succ = { available.edge } →
  ett.series.data.kind q.succ = some TashkinovExtensionKind.RE →
  ∀ (hroundLarge : 1 < ett.rounds)
   (originalPrefix :
    ExtendedTashkinovTree G k e0 input
     (ett.series.data.tree (Fin.last ett.rounds).castSucc)
     (ett.series.data.coloring
      (⟨ett.rounds - 1, (by omega)⟩ : Fin (ett.rounds + 1))))
   (hr : originalPrefix.rounds = ett.rounds - 1),
  (
  ∀ (i : Fin (originalPrefix.rounds + 2)),
  originalPrefix.series.data.tree i =
   ett.series.data.tree (Fin.castLE ((by omega)) i)) →
  (
  ∀ (i : Fin (originalPrefix.rounds + 1)),
  originalPrefix.series.data.coloring i =
    ett.series.data.coloring (Fin.castLE ((by omega)) i) ∧
   originalPrefix.series.data.stored i =
     ett.series.data.stored (Fin.castLE ((by omega)) i) ∧
    originalPrefix.series.data.connectingEdges i =
      ett.series.data.connectingEdges (Fin.castLE ((by omega)) i) ∧
     originalPrefix.series.data.kind i =
       ett.series.data.kind (Fin.castLE ((by omega)) i) ∧
      TashkinovStoredColors originalPrefix.series.data i =
       TashkinovStoredColors ett.series.data
        (Fin.castLE ((by omega)) i)) →
  ∀
   (corr :
    CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigma
     (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
  corr.replacementSeries.data.tree
     (Fin.last (originalPrefix.rounds + 1)) =
    ett.series.data.tree (Fin.last ett.rounds).castSucc →
  corr.replacementSeries.data.coloring
     (Fin.last originalPrefix.rounds) =
    sigma →
  MaximumProperty corr.replacementETT →
  ∀
   (earlierPrefixBound :
    (↑available.earlier : ℕ) < originalPrefix.rounds + 1),
  let earlierPrefix : Fin (originalPrefix.rounds + 1) :=
   (⟨(↑available.earlier : ℕ), earlierPrefixBound⟩ :
    Fin (originalPrefix.rounds + 1));
  Fin.castLE ((by omega)) earlierPrefix = available.earlier →
  0 < (↑earlierPrefix : ℕ) →
  corr.replacementSeries.data.kind earlierPrefix =
    some TashkinovExtensionKind.PE →
  ∀ (oldi : Fin ett.rounds)
   (oldChoice :
    MaximumDefectiveChoice G e0
     (ett.series.data.tree oldi.succ.castSucc)
     (TashkinovStoredColors ett.series.data oldi.castSucc)
     (ett.series.data.coloring oldi.castSucc))
   (oldGamma : Fin k),
  available.earlier = oldi.succ →
  ∀ (newi : Fin originalPrefix.rounds)
   (newChoice :
    MaximumDefectiveChoice G e0
     (corr.replacementSeries.data.tree newi.succ.castSucc)
     (TashkinovStoredColors corr.replacementSeries.data
      newi.castSucc)
     (corr.replacementSeries.data.coloring newi.castSucc))
   (newGamma : Fin k),
  corr.replacementSeries.data.delta newi.succ =
    some newChoice.color →
  corr.replacementSeries.data.gamma newi.succ =
    some newGamma →
  newi.succ = earlierPrefix →
  ∀
   (htree :
    corr.replacementSeries.data.tree newi.succ.castSucc =
     ett.series.data.tree oldi.succ.castSucc),
  let oldChoiceOnNew :
   MaximumDefectiveChoice G e0
    (corr.replacementSeries.data.tree
     newi.succ.castSucc)
    (TashkinovStoredColors ett.series.data
     oldi.castSucc)
    (ett.series.data.coloring oldi.castSucc) :=
   transportDefectiveChoice htree.symm oldChoice;
  ∀
   (holdColorCast :
    oldChoiceOnNew.color = oldChoice.color),
  s(oldChoiceOnNew.vertex,
     oldChoiceOnNew.otherEndpoint) =
    s(newChoice.vertex, newChoice.otherEndpoint) →
  ∀ (holdColorNe : oldGamma ≠ oldChoice.color)
   (hnewColorNe : newGamma ≠ newChoice.color)
   (hidentifiedDelta :
    newChoice.color = oldChoiceOnNew.color)
   (hidentifiedGamma : newGamma = oldGamma)
   (holdDeltaAvailable :
    oldChoice.color = available.delta)
   (holdGammaAvailable : oldGamma = available.gamma),
  newChoice.color = available.delta →
  newGamma = available.gamma →
  let replacementLast :
   Fin (originalPrefix.rounds + 1) :=
   Fin.last originalPrefix.rounds;
  Fin.castLE ((by omega)) replacementLast =
    q.castSucc →
  available.delta ∈
    MissingColors G sigma newChoice.vertex →
  available.gamma ≠ available.delta →
  newChoice.vertex ∈
    TreeSequenceVertexSet
     (ett.series.data.tree
      (Fin.last ett.rounds).castSucc) →
  TwoColorNontrivialPathComponent G sigma
    available.gamma available.delta
    (Sum.inl newChoice.vertex) →
  (∃
    v ∈
     TreeSequenceVertexSet
      (ett.series.data.tree
       (Fin.last ett.rounds).castSucc),
    Sum.inl v ∈
     TwoColorComponent G sigma available.gamma
      available.delta
      (Sum.inl newChoice.vertex)) →
  StableColoring
    (ett.series.data.tree q.succ.castSucc)
    (TashkinovStoredColors ett.series.data
     q.castSucc)
    (ett.series.data.coloring q.castSucc)
    sigma →
  let sigmaReturnGraph :
   SimpleGraph (V ⊕ E) :=
   TwoColorIncidenceGraph G sigma
    available.gamma available.delta;
  ∀
   (returnEdgeTransfer :
    ∀ edge ∈ available.returnPath.edges,
     edge ∈ sigmaReturnGraph.edgeSet),
  let sigmaReturnPath :
   sigmaReturnGraph.Walk
    (Sum.inr available.edge)
    (Sum.inl available.returnVertex) :=
   available.returnPath.transfer
    sigmaReturnGraph returnEdgeTransfer;
  sigmaReturnPath.IsPath →
  (
  ∀ (z : V ⊕ E),
  z ∈ sigmaReturnPath.support ↔
   z ∈ available.returnPath.support) →
  Sum.inl available.returnVertex ∈
    TwoColorComponent G sigma
     available.gamma available.delta
     (Sum.inr available.edge) →
  Sum.inl available.outsideEndpoint ∈
    TwoColorComponent G sigma
     available.gamma available.delta
     (Sum.inr available.edge) →
  available.returnVertex ∈
    TreeSequenceVertexSet
     (corr.replacementSeries.data.tree
      earlierPrefix.castSucc) →
  available.returnVertex ∈
    TreeSequenceVertexSet
     (ett.series.data.tree
      (Fin.last
        ett.rounds).castSucc) →
  TwoColorComponent G sigma
     available.gamma available.delta
     (Sum.inl newChoice.vertex) ≠
    TwoColorComponent G sigma
     available.gamma available.delta
     (Sum.inr available.edge) →
  (∃
    v ∈
     TreeSequenceVertexSet
      (ett.series.data.tree
       (Fin.last
         ett.rounds).castSucc),
    Sum.inl v ∈
     TwoColorComponent G sigma
      available.gamma
      available.delta
      (Sum.inr available.edge)) →
  0 < corr.replacementETT.rounds →
  corr.replacementETT.rounds <
    ett.rounds →
  (
  ∀
   (C :
    CorrespondingExtendedTashkinovTree
     G k e0 originalPrefix sigma
     (ett.series.data.tree
      (Fin.last
        ett.rounds).castSucc)),
  C.replacementETT.series.data.tree
    (Fin.last
     (C.replacementETT.rounds +
      1)) =
   C.replacementSeries.data.tree
    (Fin.last
     (originalPrefix.rounds +
      1))) →
  corr.replacementETT.series.data.tree
     (Fin.last
      (corr.replacementETT.rounds +
       1)) =
    corr.replacementSeries.data.tree
     (Fin.last
      (originalPrefix.rounds +
       1)) →
  corr.replacementETT.series.data.coloring
     (Fin.last
      corr.replacementETT.rounds) =
    sigma →
  StableColoring
    (corr.replacementETT.series.data.tree
     (Fin.last
      (corr.replacementETT.rounds +
       1)))
    (TashkinovStoredColors
     corr.replacementETT.series.data
     (Fin.last
      corr.replacementETT.rounds))
    (corr.replacementETT.series.data.coloring
     (Fin.last
      corr.replacementETT.rounds))
    sigma →
  corr.replacementETT.series.data.tree
     (Fin.last
      (corr.replacementETT.rounds +
       1)) =
    ett.series.data.tree
     (Fin.last
       ett.rounds).castSucc →
  available.delta ∈
    TreeMissingColors sigma
     (corr.replacementETT.series.data.tree
      (Fin.last
       (corr.replacementETT.rounds +
        1))) →
  LowerRoundProperties
    corr.replacementETT →
  TreeInterchangeable G
    (corr.replacementETT.series.data.tree
     (Fin.last
      (corr.replacementETT.rounds +
       1)))
    sigma available.gamma
    available.delta →
  TreeInterchangeable G
    (ett.series.data.tree
     (Fin.last
       ett.rounds).castSucc)
    sigma available.gamma
    available.delta →
  ∀
   (replacementCycle :
    TwoColorCycle G
     sigma
     available.gamma
     available.delta),
  (
  ∀ (x : V ⊕ E),
  x ∈
    replacementCycle.walk.support ↔
   x ∈
    TwoColorComponent
     G sigma
     available.gamma
     available.delta
     (Sum.inr
      available.edge)) →
  ColoredVertexSetClosed
    G sigma
    (TreeSequenceVertexSet
     (ett.series.data.tree
      q.succ.castSucc)) →
  ColoredVertexSetClosed
    G sigma
    (TreeSequenceVertexSet
     (ett.series.data.tree
      (Fin.last
        ett.rounds).castSucc)) →
  (
  have
   replacementLast :
   Fin
    (originalPrefix.rounds +
     1) :=
   Fin.last
    originalPrefix.rounds;
  corr.replacementSeries.data.tree
    replacementLast.succ =
   ett.series.data.tree
    (Fin.last
      ett.rounds).castSucc) →
  q.castSucc.succ =
    (Fin.last
      ett.rounds).castSucc →
  ett.series.data.tree
     q.castSucc.succ =
    ett.series.data.tree
     (Fin.last
       ett.rounds).castSucc →
  let
   currentTree :
   Finset V :=
   TreeSequenceVertexSet
    (ett.series.data.tree
     q.succ.castSucc);
  ∀
   (hreturnCycle :
    Sum.inl
      available.returnVertex ∈
     replacementCycle.walk.support),
  Sum.inl
     available.outsideEndpoint ∈
    replacementCycle.walk.support →
  available.returnVertex ∈
    currentTree →
  available.outsideEndpoint ∉
    currentTree →
  let
   rootedCycle :
   (TwoColorIncidenceGraph
      G sigma
      available.gamma
      available.delta).Walk
    (Sum.inl
     available.returnVertex)
    (Sum.inl
     available.returnVertex) :=
   replacementCycle.walk.rotate
    (Sum.inl
     available.returnVertex)
    hreturnCycle;
  rootedCycle.IsCycle →
  Sum.inl
     available.outsideEndpoint ∈
    rootedCycle.support →
  let
   outsideIndices :
   Finset
    (Fin
     (rootedCycle.length +
      1)) :=
   {i :
    Fin
     (rootedCycle.length +
      1) |
    ∃ (v :
     V),
     rootedCycle.getVert
        (↑i :
         ℕ) =
       Sum.inl
        v ∧
      v ∉
       currentTree};
  ∀
   (outsideIndicesNonempty :
    outsideIndices.Nonempty),
  let
   firstOutside :
   Fin
    (rootedCycle.length +
     1) :=
   outsideIndices.min'
    outsideIndicesNonempty;
  ∀
   (outsideOne :
    V),
  rootedCycle.getVert
     (↑(outsideIndices.min'
        outsideIndicesNonempty) :
      ℕ) =
    Sum.inl
     outsideOne →
  outsideOne ∉
    currentTree →
  (
  ∀
   (idx :
    Fin
     (rootedCycle.length +
      1)),
  (↑idx :
     ℕ) <
    (↑firstOutside :
     ℕ) →
  ∀
   (v :
    V),
  rootedCycle.getVert
     (↑idx :
      ℕ) =
    Sum.inl
     v →
  v ∈
   currentTree) →
  0 <
    (↑firstOutside :
     ℕ) →
  (↑firstOutside :
     ℕ) <
    rootedCycle.length →
  (↑firstOutside :
     ℕ) ≠
    1 →
  2 ≤
    (↑firstOutside :
     ℕ) →
  (TwoColorIncidenceGraph
      G
      sigma
      available.gamma
      available.delta).Adj
    (rootedCycle.getVert
     ((↑firstOutside :
       ℕ) -
      1))
    (rootedCycle.getVert
     ((↑firstOutside :
        ℕ) -
       1 +
      1)) →
  (↑firstOutside :
       ℕ) -
      1 +
     1 =
    (↑firstOutside :
     ℕ) →
  ∀
   (firstEdge :
    E),
  rootedCycle.getVert
     ((↑firstOutside :
       ℕ) -
      1) =
    Sum.inr
     firstEdge →
  Incident
    G
    outsideOne
    firstEdge →
  sigma
      firstEdge =
     some
      available.gamma ∨
    sigma
      firstEdge =
     some
      available.delta →
  (TwoColorIncidenceGraph
      G
      sigma
      available.gamma
      available.delta).Adj
    (rootedCycle.getVert
     ((↑firstOutside :
       ℕ) -
      2))
    (rootedCycle.getVert
     ((↑firstOutside :
        ℕ) -
       2 +
      1)) →
  (↑firstOutside :
       ℕ) -
      2 +
     1 =
    (↑firstOutside :
      ℕ) -
     1 →
  ∀
   (insideOne :
    V),
  rootedCycle.getVert
     ((↑firstOutside :
       ℕ) -
      2) =
    Sum.inl
     insideOne →
  insideOne ∈
    currentTree →
  Incident
    G
    insideOne
    firstEdge →
  (
  ∀
   {f :
    E}
   {a
    b :
    V},
  Incident
    G
    a
    f →
  Incident
    G
    b
    f →
  a ≠
    b →
  G.ends
    f =
   s(a,
    b)) →
  insideOne ≠
    outsideOne →
  G.ends
     firstEdge =
    s(insideOne,
     outsideOne) →
  firstEdge ∈
    BoundaryEdges
     G
     currentTree →
  let
   laterInsideIndices :
   Finset
    (Fin
     (rootedCycle.length +
      1)) :=
   {idx :
    Fin
     (rootedCycle.length +
      1) |
    (↑firstOutside :
       ℕ) <
      (↑idx :
       ℕ) ∧
     ∃
      (v
      :
      V),
      rootedCycle.getVert
         (↑idx :
          ℕ) =
        Sum.inl
         v ∧
       v ∈
        currentTree};
  ∀
   (laterInsideNonempty :
    laterInsideIndices.Nonempty),
  let
   firstReturn :
   Fin
    (rootedCycle.length +
     1) :=
   laterInsideIndices.min'
    laterInsideNonempty;
  laterInsideIndices.min'
     laterInsideNonempty ∈
    laterInsideIndices →
  (↑firstOutside :
     ℕ) <
    (↑firstReturn :
     ℕ) →
  ∀
   (insideTwo :
    V),
  rootedCycle.getVert
     (↑(laterInsideIndices.min'
        laterInsideNonempty) :
      ℕ) =
    Sum.inl
     insideTwo →
  insideTwo ∈
    currentTree →
  (↑firstReturn :
     ℕ) ≠
    (↑firstOutside :
      ℕ) +
     1 →
  Nonempty (CorrespondingExtendedTashkinovTree G k e0 ett sigma Tstar)

private abbrev revisitingCertificateTransportStatement.{u_1, u_2} : Prop :=
 open scoped Classical Sym2 in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T generating) (hpositive : 0 < ett.rounds),
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
  ∀ (fstar : E) (seed : TreeSequence G e0),
  ett.series.data.connectingEdges (Fin.last ett.rounds) = { fstar } →
  TreeSequenceAdjoinEdge (ett.series.data.tree (Fin.last ett.rounds).castSucc) fstar
    seed →
  ∀ (closureTree : TreeSequence G e0),
  TashkinovClosure sigma seed closureTree →
  TreeSequenceInitialSegment Tstar closureTree →
  TreeSequenceInitialSegment (ett.series.data.tree (Fin.last ett.rounds).castSucc)
    closureTree →
  let q : Fin ett.rounds := (⟨ett.rounds - 1, (by omega)⟩ : Fin ett.rounds);
  q.succ = Fin.last ett.rounds →
  q.castSucc = (⟨ett.rounds - 1, (by omega)⟩ : Fin (ett.rounds + 1)) →
  ∀ (adjoined : TreeSequence G e0),
  IsProperEdgeColoring G (ett.series.data.coloring q.castSucc) →
  IsOneEdgeUncolored (ett.series.data.coloring q.castSucc) e0 →
  ColoredVertexSetClosed G (ett.series.data.coloring q.castSucc)
    (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) →
  ∀ (available : RevisitingExtensionCertificate ett.series.data q.castSucc),
  ett.series.data.stored q.succ = { available.delta, available.gamma } →
  ett.series.data.connectingEdges q.succ = { available.edge } →
  ett.series.data.kind q.succ = some TashkinovExtensionKind.RE →
  ∀ (hroundLarge : 1 < ett.rounds)
   (originalPrefix :
    ExtendedTashkinovTree G k e0 input
     (ett.series.data.tree (Fin.last ett.rounds).castSucc)
     (ett.series.data.coloring
      (⟨ett.rounds - 1, (by omega)⟩ : Fin (ett.rounds + 1))))
   (hr : originalPrefix.rounds = ett.rounds - 1),
  (
  ∀ (i : Fin (originalPrefix.rounds + 2)),
  originalPrefix.series.data.tree i =
   ett.series.data.tree (Fin.castLE ((by omega)) i)) →
  (
  ∀ (i : Fin (originalPrefix.rounds + 1)),
  originalPrefix.series.data.coloring i =
    ett.series.data.coloring (Fin.castLE ((by omega)) i) ∧
   originalPrefix.series.data.stored i =
     ett.series.data.stored (Fin.castLE ((by omega)) i) ∧
    originalPrefix.series.data.connectingEdges i =
      ett.series.data.connectingEdges (Fin.castLE ((by omega)) i) ∧
     originalPrefix.series.data.kind i =
       ett.series.data.kind (Fin.castLE ((by omega)) i) ∧
      TashkinovStoredColors originalPrefix.series.data i =
       TashkinovStoredColors ett.series.data
        (Fin.castLE ((by omega)) i)) →
  ∀
   (corr :
    CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigma
     (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
  corr.replacementSeries.data.tree
     (Fin.last (originalPrefix.rounds + 1)) =
    ett.series.data.tree (Fin.last ett.rounds).castSucc →
  corr.replacementSeries.data.coloring
     (Fin.last originalPrefix.rounds) =
    sigma →
  MaximumProperty corr.replacementETT →
  ∀
   (earlierPrefixBound :
    (↑available.earlier : ℕ) < originalPrefix.rounds + 1),
  let earlierPrefix : Fin (originalPrefix.rounds + 1) :=
   (⟨(↑available.earlier : ℕ), earlierPrefixBound⟩ :
    Fin (originalPrefix.rounds + 1));
  Fin.castLE ((by omega)) earlierPrefix = available.earlier →
  0 < (↑earlierPrefix : ℕ) →
  corr.replacementSeries.data.kind earlierPrefix =
    some TashkinovExtensionKind.PE →
  ∀ (oldi : Fin ett.rounds)
   (oldChoice :
    MaximumDefectiveChoice G e0
     (ett.series.data.tree oldi.succ.castSucc)
     (TashkinovStoredColors ett.series.data oldi.castSucc)
     (ett.series.data.coloring oldi.castSucc))
   (oldGamma : Fin k),
  available.earlier = oldi.succ →
  ∀ (newi : Fin originalPrefix.rounds)
   (newChoice :
    MaximumDefectiveChoice G e0
     (corr.replacementSeries.data.tree newi.succ.castSucc)
     (TashkinovStoredColors corr.replacementSeries.data
      newi.castSucc)
     (corr.replacementSeries.data.coloring newi.castSucc))
   (newGamma : Fin k),
  corr.replacementSeries.data.delta newi.succ =
    some newChoice.color →
  corr.replacementSeries.data.gamma newi.succ =
    some newGamma →
  newi.succ = earlierPrefix →
  ∀
   (htree :
    corr.replacementSeries.data.tree newi.succ.castSucc =
     ett.series.data.tree oldi.succ.castSucc),
  let oldChoiceOnNew :
   MaximumDefectiveChoice G e0
    (corr.replacementSeries.data.tree
     newi.succ.castSucc)
    (TashkinovStoredColors ett.series.data
     oldi.castSucc)
    (ett.series.data.coloring oldi.castSucc) :=
   transportDefectiveChoice htree.symm oldChoice;
  ∀
   (holdColorCast :
    oldChoiceOnNew.color = oldChoice.color),
  s(oldChoiceOnNew.vertex,
     oldChoiceOnNew.otherEndpoint) =
    s(newChoice.vertex, newChoice.otherEndpoint) →
  ∀ (holdColorNe : oldGamma ≠ oldChoice.color)
   (hnewColorNe : newGamma ≠ newChoice.color)
   (hidentifiedDelta :
    newChoice.color = oldChoiceOnNew.color)
   (hidentifiedGamma : newGamma = oldGamma)
   (holdDeltaAvailable :
    oldChoice.color = available.delta)
   (holdGammaAvailable : oldGamma = available.gamma),
  newChoice.color = available.delta →
  newGamma = available.gamma →
  let replacementLast :
   Fin (originalPrefix.rounds + 1) :=
   Fin.last originalPrefix.rounds;
  Fin.castLE ((by omega)) replacementLast =
    q.castSucc →
  available.delta ∈
    MissingColors G sigma newChoice.vertex →
  available.gamma ≠ available.delta →
  newChoice.vertex ∈
    TreeSequenceVertexSet
     (ett.series.data.tree
      (Fin.last ett.rounds).castSucc) →
  TwoColorNontrivialPathComponent G sigma
    available.gamma available.delta
    (Sum.inl newChoice.vertex) →
  (∃
    v ∈
     TreeSequenceVertexSet
      (ett.series.data.tree
       (Fin.last ett.rounds).castSucc),
    Sum.inl v ∈
     TwoColorComponent G sigma available.gamma
      available.delta
      (Sum.inl newChoice.vertex)) →
  StableColoring
    (ett.series.data.tree q.succ.castSucc)
    (TashkinovStoredColors ett.series.data
     q.castSucc)
    (ett.series.data.coloring q.castSucc)
    sigma →
  let sigmaReturnGraph :
   SimpleGraph (V ⊕ E) :=
   TwoColorIncidenceGraph G sigma
    available.gamma available.delta;
  ∀
   (returnEdgeTransfer :
    ∀ edge ∈ available.returnPath.edges,
     edge ∈ sigmaReturnGraph.edgeSet),
  let sigmaReturnPath :
   sigmaReturnGraph.Walk
    (Sum.inr available.edge)
    (Sum.inl available.returnVertex) :=
   available.returnPath.transfer
    sigmaReturnGraph returnEdgeTransfer;
  sigmaReturnPath.IsPath →
  (
  ∀ (z : V ⊕ E),
  z ∈ sigmaReturnPath.support ↔
   z ∈ available.returnPath.support) →
  Sum.inl available.returnVertex ∈
    TwoColorComponent G sigma
     available.gamma available.delta
     (Sum.inr available.edge) →
  Sum.inl available.outsideEndpoint ∈
    TwoColorComponent G sigma
     available.gamma available.delta
     (Sum.inr available.edge) →
  available.returnVertex ∈
    TreeSequenceVertexSet
     (corr.replacementSeries.data.tree
      earlierPrefix.castSucc) →
  available.returnVertex ∈
    TreeSequenceVertexSet
     (ett.series.data.tree
      (Fin.last
        ett.rounds).castSucc) →
  TwoColorComponent G sigma
     available.gamma available.delta
     (Sum.inl newChoice.vertex) ≠
    TwoColorComponent G sigma
     available.gamma available.delta
     (Sum.inr available.edge) →
  (∃
    v ∈
     TreeSequenceVertexSet
      (ett.series.data.tree
       (Fin.last
         ett.rounds).castSucc),
    Sum.inl v ∈
     TwoColorComponent G sigma
      available.gamma
      available.delta
      (Sum.inr available.edge)) →
  0 < corr.replacementETT.rounds →
  corr.replacementETT.rounds <
    ett.rounds →
  (
  ∀
   (C :
    CorrespondingExtendedTashkinovTree
     G k e0 originalPrefix sigma
     (ett.series.data.tree
      (Fin.last
        ett.rounds).castSucc)),
  C.replacementETT.series.data.tree
    (Fin.last
     (C.replacementETT.rounds +
      1)) =
   C.replacementSeries.data.tree
    (Fin.last
     (originalPrefix.rounds +
      1))) →
  corr.replacementETT.series.data.tree
     (Fin.last
      (corr.replacementETT.rounds +
       1)) =
    corr.replacementSeries.data.tree
     (Fin.last
      (originalPrefix.rounds +
       1)) →
  corr.replacementETT.series.data.coloring
     (Fin.last
      corr.replacementETT.rounds) =
    sigma →
  StableColoring
    (corr.replacementETT.series.data.tree
     (Fin.last
      (corr.replacementETT.rounds +
       1)))
    (TashkinovStoredColors
     corr.replacementETT.series.data
     (Fin.last
      corr.replacementETT.rounds))
    (corr.replacementETT.series.data.coloring
     (Fin.last
      corr.replacementETT.rounds))
    sigma →
  corr.replacementETT.series.data.tree
     (Fin.last
      (corr.replacementETT.rounds +
       1)) =
    ett.series.data.tree
     (Fin.last
       ett.rounds).castSucc →
  available.delta ∈
    TreeMissingColors sigma
     (corr.replacementETT.series.data.tree
      (Fin.last
       (corr.replacementETT.rounds +
        1))) →
  LowerRoundProperties
    corr.replacementETT →
  TreeInterchangeable G
    (corr.replacementETT.series.data.tree
     (Fin.last
      (corr.replacementETT.rounds +
       1)))
    sigma available.gamma
    available.delta →
  TreeInterchangeable G
    (ett.series.data.tree
     (Fin.last
       ett.rounds).castSucc)
    sigma available.gamma
    available.delta →
  ∀
   (replacementCycle :
    TwoColorCycle G
     sigma
     available.gamma
     available.delta),
  (
  ∀ (x : V ⊕ E),
  x ∈
    replacementCycle.walk.support ↔
   x ∈
    TwoColorComponent
     G sigma
     available.gamma
     available.delta
     (Sum.inr
      available.edge)) →
  ColoredVertexSetClosed
    G sigma
    (TreeSequenceVertexSet
     (ett.series.data.tree
      q.succ.castSucc)) →
  ColoredVertexSetClosed
    G sigma
    (TreeSequenceVertexSet
     (ett.series.data.tree
      (Fin.last
        ett.rounds).castSucc)) →
  (
  have
   replacementLast :
   Fin
    (originalPrefix.rounds +
     1) :=
   Fin.last
    originalPrefix.rounds;
  corr.replacementSeries.data.tree
    replacementLast.succ =
   ett.series.data.tree
    (Fin.last
      ett.rounds).castSucc) →
  q.castSucc.succ =
    (Fin.last
      ett.rounds).castSucc →
  ett.series.data.tree
     q.castSucc.succ =
    ett.series.data.tree
     (Fin.last
       ett.rounds).castSucc →
  let
   currentTree :
   Finset V :=
   TreeSequenceVertexSet
    (ett.series.data.tree
     q.succ.castSucc);
  ∀
   (hreturnCycle :
    Sum.inl
      available.returnVertex ∈
     replacementCycle.walk.support),
  Sum.inl
     available.outsideEndpoint ∈
    replacementCycle.walk.support →
  available.returnVertex ∈
    currentTree →
  available.outsideEndpoint ∉
    currentTree →
  let
   rootedCycle :
   (TwoColorIncidenceGraph
      G sigma
      available.gamma
      available.delta).Walk
    (Sum.inl
     available.returnVertex)
    (Sum.inl
     available.returnVertex) :=
   replacementCycle.walk.rotate
    (Sum.inl
     available.returnVertex)
    hreturnCycle;
  rootedCycle.IsCycle →
  Sum.inl
     available.outsideEndpoint ∈
    rootedCycle.support →
  let
   outsideIndices :
   Finset
    (Fin
     (rootedCycle.length +
      1)) :=
   {i :
    Fin
     (rootedCycle.length +
      1) |
    ∃ (v :
     V),
     rootedCycle.getVert
        (↑i :
         ℕ) =
       Sum.inl
        v ∧
      v ∉
       currentTree};
  ∀
   (outsideIndicesNonempty :
    outsideIndices.Nonempty),
  let
   firstOutside :
   Fin
    (rootedCycle.length +
     1) :=
   outsideIndices.min'
    outsideIndicesNonempty;
  ∀
   (outsideOne :
    V),
  rootedCycle.getVert
     (↑(outsideIndices.min'
        outsideIndicesNonempty) :
      ℕ) =
    Sum.inl
     outsideOne →
  outsideOne ∉
    currentTree →
  (
  ∀
   (idx :
    Fin
     (rootedCycle.length +
      1)),
  (↑idx :
     ℕ) <
    (↑firstOutside :
     ℕ) →
  ∀
   (v :
    V),
  rootedCycle.getVert
     (↑idx :
      ℕ) =
    Sum.inl
     v →
  v ∈
   currentTree) →
  0 <
    (↑firstOutside :
     ℕ) →
  (↑firstOutside :
     ℕ) <
    rootedCycle.length →
  (↑firstOutside :
     ℕ) ≠
    1 →
  2 ≤
    (↑firstOutside :
     ℕ) →
  (TwoColorIncidenceGraph
      G
      sigma
      available.gamma
      available.delta).Adj
    (rootedCycle.getVert
     ((↑firstOutside :
       ℕ) -
      1))
    (rootedCycle.getVert
     ((↑firstOutside :
        ℕ) -
       1 +
      1)) →
  (↑firstOutside :
       ℕ) -
      1 +
     1 =
    (↑firstOutside :
     ℕ) →
  ∀
   (firstEdge :
    E),
  rootedCycle.getVert
     ((↑firstOutside :
       ℕ) -
      1) =
    Sum.inr
     firstEdge →
  Incident
    G
    outsideOne
    firstEdge →
  sigma
      firstEdge =
     some
      available.gamma ∨
    sigma
      firstEdge =
     some
      available.delta →
  (TwoColorIncidenceGraph
      G
      sigma
      available.gamma
      available.delta).Adj
    (rootedCycle.getVert
     ((↑firstOutside :
       ℕ) -
      2))
    (rootedCycle.getVert
     ((↑firstOutside :
        ℕ) -
       2 +
      1)) →
  (↑firstOutside :
       ℕ) -
      2 +
     1 =
    (↑firstOutside :
      ℕ) -
     1 →
  ∀
   (insideOne :
    V),
  rootedCycle.getVert
     ((↑firstOutside :
       ℕ) -
      2) =
    Sum.inl
     insideOne →
  insideOne ∈
    currentTree →
  Incident
    G
    insideOne
    firstEdge →
  (
  ∀
   {f :
    E}
   {a
    b :
    V},
  Incident
    G
    a
    f →
  Incident
    G
    b
    f →
  a ≠
    b →
  G.ends
    f =
   s(a,
    b)) →
  insideOne ≠
    outsideOne →
  G.ends
     firstEdge =
    s(insideOne,
     outsideOne) →
  firstEdge ∈
    BoundaryEdges
     G
     currentTree →
  let
   laterInsideIndices :
   Finset
    (Fin
     (rootedCycle.length +
      1)) :=
   {idx :
    Fin
     (rootedCycle.length +
      1) |
    (↑firstOutside :
       ℕ) <
      (↑idx :
       ℕ) ∧
     ∃
      (v
      :
      V),
      rootedCycle.getVert
         (↑idx :
          ℕ) =
        Sum.inl
         v ∧
       v ∈
        currentTree};
  ∀
   (laterInsideNonempty :
    laterInsideIndices.Nonempty),
  let
   firstReturn :
   Fin
    (rootedCycle.length +
     1) :=
   laterInsideIndices.min'
    laterInsideNonempty;
  laterInsideIndices.min'
     laterInsideNonempty ∈
    laterInsideIndices →
  (↑firstOutside :
     ℕ) <
    (↑firstReturn :
     ℕ) →
  ∀
   (insideTwo :
    V),
  rootedCycle.getVert
     (↑(laterInsideIndices.min'
        laterInsideNonempty) :
      ℕ) =
    Sum.inl
     insideTwo →
  insideTwo ∈
    currentTree →
  (↑firstReturn :
     ℕ) ≠
    (↑firstOutside :
      ℕ) +
     1 →
  (↑firstOutside :
      ℕ) +
     2 ≤
    (↑firstReturn :
     ℕ) →
  (TwoColorIncidenceGraph
      G
      sigma
      available.gamma
      available.delta).Adj
    (rootedCycle.getVert
     ((↑firstReturn :
       ℕ) -
      1))
    (rootedCycle.getVert
     ((↑firstReturn :
        ℕ) -
       1 +
      1)) →
  (↑firstReturn :
       ℕ) -
      1 +
     1 =
    (↑firstReturn :
     ℕ) →
  ∀
   (secondEdge :
    E),
  rootedCycle.getVert
     ((↑firstReturn :
       ℕ) -
      1) =
    Sum.inr
     secondEdge →
  Incident
    G
    insideTwo
    secondEdge →
  sigma
      secondEdge =
     some
      available.gamma ∨
    sigma
      secondEdge =
     some
      available.delta →
  (TwoColorIncidenceGraph
      G
      sigma
      available.gamma
      available.delta).Adj
    (rootedCycle.getVert
     ((↑firstReturn :
       ℕ) -
      2))
    (rootedCycle.getVert
     ((↑firstReturn :
        ℕ) -
       2 +
      1)) →
  (↑firstReturn :
       ℕ) -
      2 +
     1 =
    (↑firstReturn :
      ℕ) -
     1 →
  ∀
   (outsideTwo :
    V),
  rootedCycle.getVert
     ((↑firstReturn :
       ℕ) -
      2) =
    Sum.inl
     outsideTwo →
  outsideTwo ∉
    currentTree →
  Incident
    G
    outsideTwo
    secondEdge →
  outsideTwo ≠
    insideTwo →
  G.ends
     secondEdge =
    s(insideTwo,
     outsideTwo) →
  secondEdge ∈
    BoundaryEdges
     G
     currentTree →
  firstEdge ≠
    secondEdge →
  newChoice.vertex ∈
    currentTree →
  sigma
     firstEdge =
    some
     available.gamma →
  sigma
     secondEdge =
    some
     available.gamma →
  ¬ColoredVertexSetStronglyClosed
     G
     sigma
     currentTree →
  corr.replacementSeries.data.coloring
     replacementLast =
    sigma →
  let
   castReturnWalk :
  (phi
    psi :
    PartialEdgeColoring
     E
     k) →
  phi =
    psi →
  (TwoColorIncidenceGraph
      G
      psi
      available.gamma
      available.delta).Walk
    (Sum.inr
     available.edge)
    (Sum.inl
     available.returnVertex) →
  (TwoColorIncidenceGraph
     G
     phi
     available.gamma
     available.delta).Walk
   (Sum.inr
    available.edge)
   (Sum.inl
    available.returnVertex) :=
   fun
    (phi
      psi :
     PartialEdgeColoring
      E
      k)
    (hphi :
     phi =
      psi)
    (P :
     (TwoColorIncidenceGraph
        G
        psi
        available.gamma
        available.delta).Walk
      (Sum.inr
       available.edge)
      (Sum.inl
       available.returnVertex)) ↦
   Eq.ndrec
    (motive :=
    fun
     (psi :
      PartialEdgeColoring
       E
       k) ↦
  (TwoColorIncidenceGraph
      G
      psi
      available.gamma
      available.delta).Walk
    (Sum.inr
     available.edge)
    (Sum.inl
     available.returnVertex) →
  (TwoColorIncidenceGraph
     G
     phi
     available.gamma
     available.delta).Walk
   (Sum.inr
    available.edge)
   (Sum.inl
    available.returnVertex))
    (fun
      (P :
       (TwoColorIncidenceGraph
          G
          phi
          available.gamma
          available.delta).Walk
        (Sum.inr
         available.edge)
        (Sum.inl
         available.returnVertex)) ↦
     P)
    hphi
    P;
  (
  ∀
   (phi
    psi :
    PartialEdgeColoring
     E
     k)
   (hphi :
    phi =
     psi)
   (P :
    (TwoColorIncidenceGraph
       G
       psi
       available.gamma
       available.delta).Walk
     (Sum.inr
      available.edge)
     (Sum.inl
      available.returnVertex)),
  P.IsPath →
  (castReturnWalk
    phi
    psi
    hphi
    P).IsPath) →
  (
  ∀
   (phi
    psi :
    PartialEdgeColoring
     E
     k)
   (hphi :
    phi =
     psi)
   (P :
    (TwoColorIncidenceGraph
       G
       psi
       available.gamma
       available.delta).Walk
     (Sum.inr
      available.edge)
     (Sum.inl
      available.returnVertex))
   (z :
    V ⊕
     E),
  z ∈
    (castReturnWalk
      phi
      psi
      hphi
      P).support ↔
   z ∈
    P.support) →
  let
   castCycle :
  (phi
    psi :
    PartialEdgeColoring
     E
     k) →
  phi =
    psi →
  TwoColorCycle
    G
    psi
    available.gamma
    available.delta →
  TwoColorCycle
   G
   phi
   available.gamma
   available.delta :=
   fun
    (phi
      psi :
     PartialEdgeColoring
      E
      k)
    (hphi :
     phi =
      psi)
    (C :
     TwoColorCycle
      G
      psi
      available.gamma
      available.delta) ↦
   Eq.ndrec
    (motive :=
    fun
     (psi :
      PartialEdgeColoring
       E
       k) ↦
  TwoColorCycle
    G
    psi
    available.gamma
    available.delta →
  TwoColorCycle
   G
   phi
   available.gamma
   available.delta)
    (fun
      (C :
       TwoColorCycle
        G
        phi
        available.gamma
        available.delta) ↦
     C)
    hphi
    C;
  Nonempty (CorrespondingExtendedTashkinovTree G k e0 ett sigma Tstar)

private abbrev revisitingFinalSeriesStatement.{u_1, u_2} : Prop :=
 open scoped Classical Sym2 in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T generating) (hpositive : 0 < ett.rounds),
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
  ∀ (fstar : E) (seed : TreeSequence G e0),
  ett.series.data.connectingEdges (Fin.last ett.rounds) = { fstar } →
  TreeSequenceAdjoinEdge (ett.series.data.tree (Fin.last ett.rounds).castSucc) fstar
    seed →
  ∀ (closureTree : TreeSequence G e0),
  TashkinovClosure sigma seed closureTree →
  TreeSequenceInitialSegment Tstar closureTree →
  TreeSequenceInitialSegment (ett.series.data.tree (Fin.last ett.rounds).castSucc)
    closureTree →
  let q : Fin ett.rounds := (⟨ett.rounds - 1, (by omega)⟩ : Fin ett.rounds);
  q.succ = Fin.last ett.rounds →
  ∀ (hqCast : q.castSucc = (⟨ett.rounds - 1, (by omega)⟩ : Fin (ett.rounds + 1)))
   (adjoined : TreeSequence G e0),
  IsProperEdgeColoring G (ett.series.data.coloring q.castSucc) →
  IsOneEdgeUncolored (ett.series.data.coloring q.castSucc) e0 →
  ColoredVertexSetClosed G (ett.series.data.coloring q.castSucc)
    (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) →
  ∀ (available : RevisitingExtensionCertificate ett.series.data q.castSucc),
  ett.series.data.stored q.succ = { available.delta, available.gamma } →
  ett.series.data.connectingEdges q.succ = { available.edge } →
  ett.series.data.kind q.succ = some TashkinovExtensionKind.RE →
  ∀ (hroundLarge : 1 < ett.rounds)
   (originalPrefix :
    ExtendedTashkinovTree G k e0 input
     (ett.series.data.tree (Fin.last ett.rounds).castSucc)
     (ett.series.data.coloring
      (⟨ett.rounds - 1, (by omega)⟩ : Fin (ett.rounds + 1))))
   (hr : originalPrefix.rounds = ett.rounds - 1),
  (
  ∀ (i : Fin (originalPrefix.rounds + 2)),
  originalPrefix.series.data.tree i =
   ett.series.data.tree (Fin.castLE ((by omega)) i)) →
  ∀
   (hprefixData :
  ∀ (i : Fin (originalPrefix.rounds + 1)),
  originalPrefix.series.data.coloring i =
    ett.series.data.coloring (Fin.castLE ((by omega)) i) ∧
   originalPrefix.series.data.stored i =
     ett.series.data.stored (Fin.castLE ((by omega)) i) ∧
    originalPrefix.series.data.connectingEdges i =
      ett.series.data.connectingEdges (Fin.castLE ((by omega)) i) ∧
     originalPrefix.series.data.kind i =
       ett.series.data.kind (Fin.castLE ((by omega)) i) ∧
      TashkinovStoredColors originalPrefix.series.data i =
       TashkinovStoredColors ett.series.data
        (Fin.castLE ((by omega)) i))
   (corr :
    CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigma
     (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
  corr.replacementSeries.data.tree
     (Fin.last (originalPrefix.rounds + 1)) =
    ett.series.data.tree (Fin.last ett.rounds).castSucc →
  corr.replacementSeries.data.coloring
     (Fin.last originalPrefix.rounds) =
    sigma →
  MaximumProperty corr.replacementETT →
  ∀
   (earlierPrefixBound :
    (↑available.earlier : ℕ) < originalPrefix.rounds + 1),
  let earlierPrefix : Fin (originalPrefix.rounds + 1) :=
   (⟨(↑available.earlier : ℕ), earlierPrefixBound⟩ :
    Fin (originalPrefix.rounds + 1));
  ∀
   (hearlierMap :
    Fin.castLE ((by omega)) earlierPrefix = available.earlier)
   (hearlierPositive : 0 < (↑earlierPrefix : ℕ))
   (hreplacementEarlierKind :
    corr.replacementSeries.data.kind earlierPrefix =
     some TashkinovExtensionKind.PE)
   (oldi : Fin ett.rounds)
   (oldChoice :
    MaximumDefectiveChoice G e0
     (ett.series.data.tree oldi.succ.castSucc)
     (TashkinovStoredColors ett.series.data oldi.castSucc)
     (ett.series.data.coloring oldi.castSucc))
   (oldGamma : Fin k),
  available.earlier = oldi.succ →
  ∀ (newi : Fin originalPrefix.rounds)
   (newChoice :
    MaximumDefectiveChoice G e0
     (corr.replacementSeries.data.tree newi.succ.castSucc)
     (TashkinovStoredColors corr.replacementSeries.data
      newi.castSucc)
     (corr.replacementSeries.data.coloring newi.castSucc))
   (newGamma : Fin k)
   (newCurrentDelta :
    corr.replacementSeries.data.delta newi.succ =
     some newChoice.color)
   (newCurrentGamma :
    corr.replacementSeries.data.gamma newi.succ = some newGamma)
   (hnewIndex : newi.succ = earlierPrefix)
   (htree :
    corr.replacementSeries.data.tree newi.succ.castSucc =
     ett.series.data.tree oldi.succ.castSucc),
  let oldChoiceOnNew :
   MaximumDefectiveChoice G e0
    (corr.replacementSeries.data.tree newi.succ.castSucc)
    (TashkinovStoredColors ett.series.data oldi.castSucc)
    (ett.series.data.coloring oldi.castSucc) :=
   transportDefectiveChoice htree.symm oldChoice;
  ∀ (holdColorCast : oldChoiceOnNew.color = oldChoice.color),
  s(oldChoiceOnNew.vertex, oldChoiceOnNew.otherEndpoint) =
    s(newChoice.vertex, newChoice.otherEndpoint) →
  ∀ (holdColorNe : oldGamma ≠ oldChoice.color)
   (hnewColorNe : newGamma ≠ newChoice.color)
   (hidentifiedDelta : newChoice.color = oldChoiceOnNew.color)
   (hidentifiedGamma : newGamma = oldGamma)
   (holdDeltaAvailable : oldChoice.color = available.delta)
   (holdGammaAvailable : oldGamma = available.gamma)
   (hnewDeltaAvailable : newChoice.color = available.delta)
   (hnewGammaAvailable : newGamma = available.gamma),
  let replacementLast : Fin (originalPrefix.rounds + 1) :=
   Fin.last originalPrefix.rounds;
  ∀
   (hreplacementLastMap :
    Fin.castLE ((by omega)) replacementLast = q.castSucc),
  available.delta ∈ MissingColors G sigma newChoice.vertex →
  ∀ (hgammaDeltaNe : available.gamma ≠ available.delta),
  newChoice.vertex ∈
    TreeSequenceVertexSet
     (ett.series.data.tree
      (Fin.last ett.rounds).castSucc) →
  TwoColorNontrivialPathComponent G sigma available.gamma
    available.delta (Sum.inl newChoice.vertex) →
  (∃
    v ∈
     TreeSequenceVertexSet
      (ett.series.data.tree
       (Fin.last ett.rounds).castSucc),
    Sum.inl v ∈
     TwoColorComponent G sigma available.gamma
      available.delta (Sum.inl newChoice.vertex)) →
  StableColoring (ett.series.data.tree q.succ.castSucc)
    (TashkinovStoredColors ett.series.data q.castSucc)
    (ett.series.data.coloring q.castSucc) sigma →
  let sigmaReturnGraph : SimpleGraph (V ⊕ E) :=
   TwoColorIncidenceGraph G sigma available.gamma
    available.delta;
  ∀
   (returnEdgeTransfer :
    ∀ edge ∈ available.returnPath.edges,
     edge ∈ sigmaReturnGraph.edgeSet),
  let sigmaReturnPath :
   sigmaReturnGraph.Walk (Sum.inr available.edge)
    (Sum.inl available.returnVertex) :=
   available.returnPath.transfer sigmaReturnGraph
    returnEdgeTransfer;
  ∀ (hsigmaReturnIsPath : sigmaReturnPath.IsPath)
   (hsigmaReturnSupport :
  ∀ (z : V ⊕ E),
  z ∈ sigmaReturnPath.support ↔
   z ∈ available.returnPath.support),
  Sum.inl available.returnVertex ∈
    TwoColorComponent G sigma available.gamma
     available.delta (Sum.inr available.edge) →
  Sum.inl available.outsideEndpoint ∈
    TwoColorComponent G sigma available.gamma
     available.delta (Sum.inr available.edge) →
  ∀
   (hreturnInNewEarlier :
    available.returnVertex ∈
     TreeSequenceVertexSet
      (corr.replacementSeries.data.tree
       earlierPrefix.castSucc)),
  available.returnVertex ∈
    TreeSequenceVertexSet
     (ett.series.data.tree
      (Fin.last ett.rounds).castSucc) →
  TwoColorComponent G sigma available.gamma
     available.delta (Sum.inl newChoice.vertex) ≠
    TwoColorComponent G sigma available.gamma
     available.delta (Sum.inr available.edge) →
  (∃
    v ∈
     TreeSequenceVertexSet
      (ett.series.data.tree
       (Fin.last ett.rounds).castSucc),
    Sum.inl v ∈
     TwoColorComponent G sigma available.gamma
      available.delta
      (Sum.inr available.edge)) →
  0 < corr.replacementETT.rounds →
  corr.replacementETT.rounds < ett.rounds →
  (
  ∀
   (C :
    CorrespondingExtendedTashkinovTree G k
     e0 originalPrefix sigma
     (ett.series.data.tree
      (Fin.last ett.rounds).castSucc)),
  C.replacementETT.series.data.tree
    (Fin.last
     (C.replacementETT.rounds + 1)) =
   C.replacementSeries.data.tree
    (Fin.last
     (originalPrefix.rounds + 1))) →
  corr.replacementETT.series.data.tree
     (Fin.last
      (corr.replacementETT.rounds + 1)) =
    corr.replacementSeries.data.tree
     (Fin.last
      (originalPrefix.rounds + 1)) →
  corr.replacementETT.series.data.coloring
     (Fin.last
      corr.replacementETT.rounds) =
    sigma →
  StableColoring
    (corr.replacementETT.series.data.tree
     (Fin.last
      (corr.replacementETT.rounds + 1)))
    (TashkinovStoredColors
     corr.replacementETT.series.data
     (Fin.last
      corr.replacementETT.rounds))
    (corr.replacementETT.series.data.coloring
     (Fin.last
      corr.replacementETT.rounds))
    sigma →
  corr.replacementETT.series.data.tree
     (Fin.last
      (corr.replacementETT.rounds + 1)) =
    ett.series.data.tree
     (Fin.last ett.rounds).castSucc →
  available.delta ∈
    TreeMissingColors sigma
     (corr.replacementETT.series.data.tree
      (Fin.last
       (corr.replacementETT.rounds +
        1))) →
  LowerRoundProperties
    corr.replacementETT →
  TreeInterchangeable G
    (corr.replacementETT.series.data.tree
     (Fin.last
      (corr.replacementETT.rounds +
       1)))
    sigma available.gamma
    available.delta →
  TreeInterchangeable G
    (ett.series.data.tree
     (Fin.last ett.rounds).castSucc)
    sigma available.gamma
    available.delta →
  ∀
   (replacementCycle :
    TwoColorCycle G sigma
     available.gamma
     available.delta)
   (hcycleFull :
  ∀ (x : V ⊕ E),
  x ∈
    replacementCycle.walk.support ↔
   x ∈
    TwoColorComponent G sigma
     available.gamma
     available.delta
     (Sum.inr available.edge)),
  ColoredVertexSetClosed G sigma
    (TreeSequenceVertexSet
     (ett.series.data.tree
      q.succ.castSucc)) →
  ColoredVertexSetClosed G sigma
    (TreeSequenceVertexSet
     (ett.series.data.tree
      (Fin.last
        ett.rounds).castSucc)) →
  ∀
   (hreplacementCurrentTree :
  have replacementLast :
   Fin
    (originalPrefix.rounds +
     1) :=
   Fin.last
    originalPrefix.rounds;
  corr.replacementSeries.data.tree
    replacementLast.succ =
   ett.series.data.tree
    (Fin.last
      ett.rounds).castSucc),
  q.castSucc.succ =
    (Fin.last
      ett.rounds).castSucc →
  ∀
   (havailableCurrentTree :
    ett.series.data.tree
      q.castSucc.succ =
     ett.series.data.tree
      (Fin.last
        ett.rounds).castSucc),
  let currentTree :
   Finset V :=
   TreeSequenceVertexSet
    (ett.series.data.tree
     q.succ.castSucc);
  ∀
   (hreturnCycle :
    Sum.inl
      available.returnVertex ∈
     replacementCycle.walk.support)
   (houtsideCycle :
    Sum.inl
      available.outsideEndpoint ∈
     replacementCycle.walk.support),
  available.returnVertex ∈
    currentTree →
  available.outsideEndpoint ∉
    currentTree →
  let rootedCycle :
   (TwoColorIncidenceGraph
      G sigma
      available.gamma
      available.delta).Walk
    (Sum.inl
     available.returnVertex)
    (Sum.inl
     available.returnVertex) :=
   replacementCycle.walk.rotate
    (Sum.inl
     available.returnVertex)
    hreturnCycle;
  rootedCycle.IsCycle →
  Sum.inl
     available.outsideEndpoint ∈
    rootedCycle.support →
  let outsideIndices :
   Finset
    (Fin
     (rootedCycle.length +
      1)) :=
   {i :
    Fin
     (rootedCycle.length +
      1) |
    ∃ (v : V),
     rootedCycle.getVert
        (↑i : ℕ) =
       Sum.inl v ∧
      v ∉ currentTree};
  ∀
   (outsideIndicesNonempty :
    outsideIndices.Nonempty),
  let firstOutside :
   Fin
    (rootedCycle.length +
     1) :=
   outsideIndices.min'
    outsideIndicesNonempty;
  ∀ (outsideOne : V),
  rootedCycle.getVert
     (↑(outsideIndices.min'
        outsideIndicesNonempty) :
      ℕ) =
    Sum.inl
     outsideOne →
  outsideOne ∉
    currentTree →
  (
  ∀
   (idx :
    Fin
     (rootedCycle.length +
      1)),
  (↑idx : ℕ) <
    (↑firstOutside :
     ℕ) →
  ∀ (v : V),
  rootedCycle.getVert
     (↑idx : ℕ) =
    Sum.inl v →
  v ∈
   currentTree) →
  0 <
    (↑firstOutside :
     ℕ) →
  (↑firstOutside :
     ℕ) <
    rootedCycle.length →
  ∀
   (firstOutsideNotOne :
    (↑firstOutside :
      ℕ) ≠
     1)
   (firstOutsideAtLeastTwo :
    2 ≤
     (↑firstOutside :
      ℕ)),
  (TwoColorIncidenceGraph
      G sigma
      available.gamma
      available.delta).Adj
    (rootedCycle.getVert
     ((↑firstOutside :
       ℕ) -
      1))
    (rootedCycle.getVert
     ((↑firstOutside :
        ℕ) -
       1 +
      1)) →
  ∀
   (firstCrossingIndex :
    (↑firstOutside :
        ℕ) -
       1 +
      1 =
     (↑firstOutside :
      ℕ))
   (firstEdge :
    E),
  rootedCycle.getVert
     ((↑firstOutside :
       ℕ) -
      1) =
    Sum.inr
     firstEdge →
  Incident G
    outsideOne
    firstEdge →
  sigma
      firstEdge =
     some
      available.gamma ∨
    sigma
      firstEdge =
     some
      available.delta →
  (TwoColorIncidenceGraph
      G
      sigma
      available.gamma
      available.delta).Adj
    (rootedCycle.getVert
     ((↑firstOutside :
       ℕ) -
      2))
    (rootedCycle.getVert
     ((↑firstOutside :
        ℕ) -
       2 +
      1)) →
  ∀
   (beforeFirstCrossingIndex :
    (↑firstOutside :
        ℕ) -
       2 +
      1 =
     (↑firstOutside :
       ℕ) -
      1)
   (insideOne :
    V),
  rootedCycle.getVert
     ((↑firstOutside :
       ℕ) -
      2) =
    Sum.inl
     insideOne →
  insideOne ∈
    currentTree →
  Incident
    G
    insideOne
    firstEdge →
  (
  ∀
   {f :
    E}
   {a
    b :
    V},
  Incident
    G
    a
    f →
  Incident
    G
    b
    f →
  a ≠
    b →
  G.ends
    f =
   s(a,
    b)) →
  insideOne ≠
    outsideOne →
  G.ends
     firstEdge =
    s(insideOne,
     outsideOne) →
  firstEdge ∈
    BoundaryEdges
     G
     currentTree →
  let
   laterInsideIndices :
   Finset
    (Fin
     (rootedCycle.length +
      1)) :=
   {idx :
    Fin
     (rootedCycle.length +
      1) |
    (↑firstOutside :
       ℕ) <
      (↑idx :
       ℕ) ∧
     ∃
      (v
      :
      V),
      rootedCycle.getVert
         (↑idx :
          ℕ) =
        Sum.inl
         v ∧
       v ∈
        currentTree};
  ∀
   (laterInsideNonempty :
    laterInsideIndices.Nonempty),
  let
   firstReturn :
   Fin
    (rootedCycle.length +
     1) :=
   laterInsideIndices.min'
    laterInsideNonempty;
  laterInsideIndices.min'
     laterInsideNonempty ∈
    laterInsideIndices →
  (↑firstOutside :
     ℕ) <
    (↑firstReturn :
     ℕ) →
  ∀
   (insideTwo :
    V),
  rootedCycle.getVert
     (↑(laterInsideIndices.min'
        laterInsideNonempty) :
      ℕ) =
    Sum.inl
     insideTwo →
  insideTwo ∈
    currentTree →
  ∀
   (hreturnNotNext :
    (↑firstReturn :
      ℕ) ≠
     (↑firstOutside :
       ℕ) +
      1)
   (hreturnGap :
    (↑firstOutside :
       ℕ) +
      2 ≤
     (↑firstReturn :
      ℕ)),
  (TwoColorIncidenceGraph
      G
      sigma
      available.gamma
      available.delta).Adj
    (rootedCycle.getVert
     ((↑firstReturn :
       ℕ) -
      1))
    (rootedCycle.getVert
     ((↑firstReturn :
        ℕ) -
       1 +
      1)) →
  ∀
   (returnCrossingIndex :
    (↑firstReturn :
        ℕ) -
       1 +
      1 =
     (↑firstReturn :
      ℕ))
   (secondEdge :
    E),
  rootedCycle.getVert
     ((↑firstReturn :
       ℕ) -
      1) =
    Sum.inr
     secondEdge →
  Incident
    G
    insideTwo
    secondEdge →
  sigma
      secondEdge =
     some
      available.gamma ∨
    sigma
      secondEdge =
     some
      available.delta →
  (TwoColorIncidenceGraph
      G
      sigma
      available.gamma
      available.delta).Adj
    (rootedCycle.getVert
     ((↑firstReturn :
       ℕ) -
      2))
    (rootedCycle.getVert
     ((↑firstReturn :
        ℕ) -
       2 +
      1)) →
  ∀
   (beforeReturnCrossingIndex :
    (↑firstReturn :
        ℕ) -
       2 +
      1 =
     (↑firstReturn :
       ℕ) -
      1)
   (outsideTwo :
    V),
  rootedCycle.getVert
     ((↑firstReturn :
       ℕ) -
      2) =
    Sum.inl
     outsideTwo →
  outsideTwo ∉
    currentTree →
  Incident
    G
    outsideTwo
    secondEdge →
  outsideTwo ≠
    insideTwo →
  G.ends
     secondEdge =
    s(insideTwo,
     outsideTwo) →
  secondEdge ∈
    BoundaryEdges
     G
     currentTree →
  firstEdge ≠
    secondEdge →
  newChoice.vertex ∈
    currentTree →
  sigma
     firstEdge =
    some
     available.gamma →
  sigma
     secondEdge =
    some
     available.gamma →
  ¬ColoredVertexSetStronglyClosed
     G
     sigma
     currentTree →
  ∀
   (hreplacementColor :
    corr.replacementSeries.data.coloring
      replacementLast =
     sigma),
  let
   castReturnWalk :
  (phi
    psi :
    PartialEdgeColoring
     E
     k) →
  phi =
    psi →
  (TwoColorIncidenceGraph
      G
      psi
      available.gamma
      available.delta).Walk
    (Sum.inr
     available.edge)
    (Sum.inl
     available.returnVertex) →
  (TwoColorIncidenceGraph
     G
     phi
     available.gamma
     available.delta).Walk
   (Sum.inr
    available.edge)
   (Sum.inl
    available.returnVertex) :=
   fun
    (phi
      psi :
     PartialEdgeColoring
      E
      k)
    (hphi :
     phi =
      psi)
    (P :
     (TwoColorIncidenceGraph
        G
        psi
        available.gamma
        available.delta).Walk
      (Sum.inr
       available.edge)
      (Sum.inl
       available.returnVertex)) ↦
   Eq.ndrec
    (motive :=
    fun
     (psi :
      PartialEdgeColoring
       E
       k) ↦
  (TwoColorIncidenceGraph
      G
      psi
      available.gamma
      available.delta).Walk
    (Sum.inr
     available.edge)
    (Sum.inl
     available.returnVertex) →
  (TwoColorIncidenceGraph
     G
     phi
     available.gamma
     available.delta).Walk
   (Sum.inr
    available.edge)
   (Sum.inl
    available.returnVertex))
    (fun
      (P :
       (TwoColorIncidenceGraph
          G
          phi
          available.gamma
          available.delta).Walk
        (Sum.inr
         available.edge)
        (Sum.inl
         available.returnVertex)) ↦
     P)
    hphi
    P;
  ∀
   (castReturnWalkIsPath :
  ∀
   (phi
    psi :
    PartialEdgeColoring
     E
     k)
   (hphi :
    phi =
     psi)
   (P :
    (TwoColorIncidenceGraph
       G
       psi
       available.gamma
       available.delta).Walk
     (Sum.inr
      available.edge)
     (Sum.inl
      available.returnVertex)),
  P.IsPath →
  (castReturnWalk
    phi
    psi
    hphi
    P).IsPath)
   (castReturnWalkSupport :
  ∀
   (phi
    psi :
    PartialEdgeColoring
     E
     k)
   (hphi :
    phi =
     psi)
   (P :
    (TwoColorIncidenceGraph
       G
       psi
       available.gamma
       available.delta).Walk
     (Sum.inr
      available.edge)
     (Sum.inl
      available.returnVertex))
   (z :
    V ⊕
     E),
  z ∈
    (castReturnWalk
      phi
      psi
      hphi
      P).support ↔
   z ∈
    P.support),
  let
   castCycle :
  (phi
    psi :
    PartialEdgeColoring
     E
     k) →
  phi =
    psi →
  TwoColorCycle
    G
    psi
    available.gamma
    available.delta →
  TwoColorCycle
   G
   phi
   available.gamma
   available.delta :=
   fun
    (phi
      psi :
     PartialEdgeColoring
      E
      k)
    (hphi :
     phi =
      psi)
    (C :
     TwoColorCycle
      G
      psi
      available.gamma
      available.delta) ↦
   Eq.ndrec
    (motive :=
    fun
     (psi :
      PartialEdgeColoring
       E
       k) ↦
  TwoColorCycle
    G
    psi
    available.gamma
    available.delta →
  TwoColorCycle
   G
   phi
   available.gamma
   available.delta)
    (fun
      (C :
       TwoColorCycle
        G
        phi
        available.gamma
        available.delta) ↦
     C)
    hphi
    C;
  ∀
   (castCycleSupport :
  ∀
   (phi
    psi :
    PartialEdgeColoring
     E
     k)
   (hphi :
    phi =
     psi)
   (C :
    TwoColorCycle
     G
     psi
     available.gamma
     available.delta)
   (z :
    V ⊕
     E),
  z ∈
    (castCycle
      phi
      psi
      hphi
      C).walk.support ↔
   z ∈
    C.walk.support),
  let
   replacementCycleForPrefix :
   TwoColorCycle
    G
    (corr.replacementSeries.data.coloring
     replacementLast)
    available.gamma
    available.delta :=
   castCycle
    (corr.replacementSeries.data.coloring
     replacementLast)
    sigma
    hreplacementColor
    replacementCycle;
  let
   replacementReturnPath :
   (TwoColorIncidenceGraph
      G
      (corr.replacementSeries.data.coloring
       replacementLast)
      available.gamma
      available.delta).Walk
    (Sum.inr
     available.edge)
    (Sum.inl
     available.returnVertex) :=
   castReturnWalk
    (corr.replacementSeries.data.coloring
     replacementLast)
    sigma
    hreplacementColor
    sigmaReturnPath;
  (
  have
   sigmaReturnPath :
   (TwoColorIncidenceGraph
      G
      sigma
      available.gamma
      available.delta).Walk
    (Sum.inr
     available.edge)
    (Sum.inl
     available.returnVertex) :=
   available.returnPath.transfer
    (TwoColorIncidenceGraph
     G
     sigma
     available.gamma
     available.delta)
    returnEdgeTransfer;
  ∀
   z ∈
    sigmaReturnPath.support,
   z ∈
    TwoColorComponent
     G
     sigma
     available.gamma
     available.delta
     (Sum.inr
      available.edge)) →
  ∀
   (hsigmaPathOnCycle :
    ∀
     z ∈
      sigmaReturnPath.support,
     z ∈
      replacementCycle.walk.support),
  let
   replacementCertificate :
   RevisitingExtensionCertificate
    corr.replacementSeries.data
    replacementLast :=
   {
    earlier :=
     earlierPrefix,
    earlierPositive :=
     hearlierPositive,
    earlierAtMost :=
     Nat.le_of_lt_succ
      earlierPrefix.isLt,
    earlierPE :=
     hreplacementEarlierKind,
    interveningRevisiting :=
     helper_interveningRevisiting_4368
      G
      k
      e0
      input
      T
      generating
      ett
      hpositive
      sigma
      Tstar
      hqCast
      available
      hroundLarge
      originalPrefix
      hr
      hprefixData
      corr
      earlierPrefixBound
      hearlierMap
      oldi
      oldChoice
      oldGamma
      newi
      newChoice
      newGamma
      htree
      holdColorCast
      holdColorNe
      hnewColorNe
      hidentifiedDelta
      hidentifiedGamma
      holdDeltaAvailable
      holdGammaAvailable
      hreplacementLastMap
      hgammaDeltaNe
      replacementCycle
      hreturnCycle
      outsideIndicesNonempty
      firstOutsideNotOne
      firstOutsideAtLeastTwo
      firstCrossingIndex
      beforeFirstCrossingIndex
      laterInsideNonempty
      hreturnNotNext
      hreturnGap
      returnCrossingIndex
      beforeReturnCrossingIndex,
    gamma :=
     available.gamma,
    delta :=
     available.delta,
    earlierGamma :=
     Eq.mpr
      (id
       (congrArg
        (fun
          (_a :
           Fin
            (originalPrefix.rounds +
             1)) ↦
         corr.replacementSeries.data.gamma
           _a =
          some
           available.gamma)
        (Eq.symm
         hnewIndex)))
      (Eq.mpr
       (id
        (congrArg
         (fun
           (_a :
            Option
             (Fin
              k)) ↦
          _a =
           some
            available.gamma)
         newCurrentGamma))
       (Eq.mpr
        (id
         (congrArg
          (fun
            (_a :
             Fin
              k) ↦
           some
             _a =
            some
             available.gamma)
          hnewGammaAvailable))
        (Eq.refl
         (some
          available.gamma)))),
    earlierDelta :=
     Eq.mpr
      (id
       (congrArg
        (fun
          (_a :
           Fin
            (originalPrefix.rounds +
             1)) ↦
         corr.replacementSeries.data.delta
           _a =
          some
           available.delta)
        (Eq.symm
         hnewIndex)))
      (Eq.mpr
       (id
        (congrArg
         (fun
           (_a :
            Option
             (Fin
              k)) ↦
          _a =
           some
            available.delta)
         newCurrentDelta))
       (Eq.mpr
        (id
         (congrArg
          (fun
            (_a :
             Fin
              k) ↦
           some
             _a =
            some
             available.delta)
          hnewDeltaAvailable))
        (Eq.refl
         (some
          available.delta)))),
    cycle :=
     replacementCycleForPrefix,
    meetsEarlier :=
     Exists.intro
      available.returnVertex
      (⟨hreturnInNewEarlier,
        (castCycleSupport
           (corr.replacementSeries.data.coloring
            replacementLast)
           sigma
           hreplacementColor
           replacementCycle
           (Sum.inl
            available.returnVertex)).mpr
         hreturnCycle⟩ :
       available.returnVertex ∈
         TreeSequenceVertexSet
          (corr.replacementSeries.data.tree
           earlierPrefix.castSucc) ∧
        Sum.inl
          available.returnVertex ∈
         replacementCycleForPrefix.walk.support),
    leavesCurrent :=
     helper_leavesCurrent_4395
      G
      k
      e0
      input
      T
      generating
      ett
      hpositive
      sigma
      Tstar
      available
      hroundLarge
      originalPrefix
      corr
      replacementCycle
      hreplacementCurrentTree
      havailableCurrentTree
      houtsideCycle
      hreplacementColor
      castCycleSupport,
    edge :=
     available.edge,
    edgeOnCycle :=
     (castCycleSupport
        (corr.replacementSeries.data.coloring
         replacementLast)
        sigma
        hreplacementColor
        replacementCycle
        (Sum.inr
         available.edge)).mpr
      ((hcycleFull
         (Sum.inr
          available.edge)).mpr
       rfl),
    edgeBoundary :=
     Eq.mpr
      (id
       (congrArg
        (fun
          (_a :
           TreeSequence
            G
            e0) ↦
         available.edge ∈
          BoundaryEdges
           G
           (TreeSequenceVertexSet
            _a))
        hreplacementCurrentTree))
      (Eq.mpr
       (id
        (congrArg
         (fun
           (_a :
            TreeSequence
             G
             e0) ↦
          available.edge ∈
           BoundaryEdges
            G
            (TreeSequenceVertexSet
             _a))
         (Eq.symm
          havailableCurrentTree)))
       available.edgeBoundary),
    insideEndpoint :=
     available.insideEndpoint,
    outsideEndpoint :=
     available.outsideEndpoint,
    insideInCurrent :=
     Eq.mpr
      (id
       (congrArg
        (fun
          (_a :
           TreeSequence
            G
            e0) ↦
         available.insideEndpoint ∈
          TreeSequenceVertexSet
           _a)
        hreplacementCurrentTree))
      (Eq.mpr
       (id
        (congrArg
         (fun
           (_a :
            TreeSequence
             G
             e0) ↦
          available.insideEndpoint ∈
           TreeSequenceVertexSet
            _a)
         (Eq.symm
          havailableCurrentTree)))
       available.insideInCurrent),
    outsideNotCurrent :=
     Eq.mpr
      (id
       (congrArg
        (fun
          (_a :
           TreeSequence
            G
            e0) ↦
         available.outsideEndpoint ∉
          TreeSequenceVertexSet
           _a)
        hreplacementCurrentTree))
      (Eq.mpr
       (id
        (congrArg
         (fun
           (_a :
            TreeSequence
             G
             e0) ↦
          available.outsideEndpoint ∉
           TreeSequenceVertexSet
            _a)
         (Eq.symm
          havailableCurrentTree)))
       available.outsideNotCurrent),
    edgeEnds :=
     available.edgeEnds,
    returnVertex :=
     available.returnVertex,
    returnInEarlier :=
     hreturnInNewEarlier,
    returnPath :=
     replacementReturnPath,
    returnPathIsPath :=
     castReturnWalkIsPath
      (corr.replacementSeries.data.coloring
       replacementLast)
      sigma
      hreplacementColor
      sigmaReturnPath
      hsigmaReturnIsPath,
    returnPathOnCycle :=
     helper_returnPathOnCycle_4421
      G
      k
      e0
      input
      T
      generating
      ett
      hpositive
      sigma
      Tstar
      available
      hroundLarge
      originalPrefix
      corr
      returnEdgeTransfer
      replacementCycle
      hreplacementColor
      castReturnWalkSupport
      castCycleSupport
      hsigmaPathOnCycle,
    returnPathInternal :=
     helper_returnPathInternal_4428
      G
      k
      e0
      input
      T
      generating
      ett
      hpositive
      sigma
      Tstar
      available
      hroundLarge
      originalPrefix
      corr
      returnEdgeTransfer
      hsigmaReturnSupport
      hreplacementCurrentTree
      havailableCurrentTree
      hreplacementColor
      castReturnWalkSupport :
    RevisitingExtensionCertificate
     corr.replacementSeries.data
     replacementLast };
  fstar =
    available.edge →
  let
   newStored :
   Finset
    (Fin
     k) :=
   {
    available.delta,
    available.gamma };
  let
   newEdges :
   Finset
    E :=
   {
    available.edge };
  let
   newKind :
   Option
    TashkinovExtensionKind :=
   some
    TashkinovExtensionKind.RE;
  let
   newVertex :
   Option
    V :=
   some
    available.insideEndpoint;
  let
   newOutside :
   Option
    V :=
   some
    available.outsideEndpoint;
  let
   newDelta :
   Option
    (Fin
     k) :=
   some
    available.delta;
  let
   newGamma :
   Option
    (Fin
     k) :=
   some
    available.gamma;
  let
   appendedData :
   TashkinovSeriesData
    G
    k
    (originalPrefix.rounds +
     1)
    e0 :=
   TashkinovSeriesDataAppend
    corr.replacementSeries.data
    closureTree
    sigma
    newStored
    newEdges
    newKind
    newVertex
    newOutside
    newDelta
    newGamma;
  ∀
   (appendedCertificate :
    RevisitingExtensionCertificate
     (TashkinovSeriesDataAppend
      corr.replacementSeries.data
      closureTree
      sigma
      newStored
      newEdges
      newKind
      newVertex
      newOutside
      newDelta
      newGamma)
     replacementLast.castSucc),
  appendedCertificate.gamma =
    replacementCertificate.gamma →
  appendedCertificate.delta =
    replacementCertificate.delta →
  appendedCertificate.edge =
    replacementCertificate.edge →
  appendedCertificate.insideEndpoint =
    replacementCertificate.insideEndpoint →
  appendedCertificate.outsideEndpoint =
    replacementCertificate.outsideEndpoint →
  (ett.series.data.tree
      (Fin.last
        ett.rounds).castSucc).length <
    closureTree.length →
  TashkinovSeriesStep
    G
    k
    (originalPrefix.rounds +
     1)
    e0
    corr.replacementInput
    appendedData
    (Fin.last
     (originalPrefix.rounds +
      1)) →
  ∀
   (extendedSeries :
    TashkinovSeries
     G
     k
     (originalPrefix.rounds +
      1)
     e0
     corr.replacementInput),
  extendedSeries.data =
    TashkinovSeriesDataAppend
     corr.replacementSeries.data
     closureTree
     sigma
     newStored
     newEdges
     newKind
     newVertex
     newOutside
     newDelta
     newGamma →
  Nonempty
   (CorrespondingExtendedTashkinovTree
    G
    k
    e0
    ett
    sigma
    Tstar)

private abbrev revisitingSeriesAgreementStatement.{u_1, u_2} : Prop :=
 open scoped Classical Sym2 in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T generating) (hpositive : 0 < ett.rounds),
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
  ∀ (fstar : E) (seed : TreeSequence G e0),
  ett.series.data.connectingEdges (Fin.last ett.rounds) = { fstar } →
  TreeSequenceAdjoinEdge (ett.series.data.tree (Fin.last ett.rounds).castSucc) fstar
    seed →
  ∀ (closureTree : TreeSequence G e0),
  TashkinovClosure sigma seed closureTree →
  TreeSequenceInitialSegment Tstar closureTree →
  TreeSequenceInitialSegment (ett.series.data.tree (Fin.last ett.rounds).castSucc)
    closureTree →
  let q : Fin ett.rounds := (⟨ett.rounds - 1, (by omega)⟩ : Fin ett.rounds);
  q.succ = Fin.last ett.rounds →
  ∀ (hqCast : q.castSucc = (⟨ett.rounds - 1, (by omega)⟩ : Fin (ett.rounds + 1)))
   (adjoined : TreeSequence G e0),
  IsProperEdgeColoring G (ett.series.data.coloring q.castSucc) →
  IsOneEdgeUncolored (ett.series.data.coloring q.castSucc) e0 →
  ColoredVertexSetClosed G (ett.series.data.coloring q.castSucc)
    (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) →
  ∀ (available : RevisitingExtensionCertificate ett.series.data q.castSucc),
  ett.series.data.stored q.succ = { available.delta, available.gamma } →
  ett.series.data.connectingEdges q.succ = { available.edge } →
  ett.series.data.kind q.succ = some TashkinovExtensionKind.RE →
  ∀ (hroundLarge : 1 < ett.rounds)
   (originalPrefix :
    ExtendedTashkinovTree G k e0 input
     (ett.series.data.tree (Fin.last ett.rounds).castSucc)
     (ett.series.data.coloring
      (⟨ett.rounds - 1, (by omega)⟩ : Fin (ett.rounds + 1))))
   (hr : originalPrefix.rounds = ett.rounds - 1),
  (
  ∀ (i : Fin (originalPrefix.rounds + 2)),
  originalPrefix.series.data.tree i =
   ett.series.data.tree (Fin.castLE ((by omega)) i)) →
  ∀
   (hprefixData :
  ∀ (i : Fin (originalPrefix.rounds + 1)),
  originalPrefix.series.data.coloring i =
    ett.series.data.coloring (Fin.castLE ((by omega)) i) ∧
   originalPrefix.series.data.stored i =
     ett.series.data.stored (Fin.castLE ((by omega)) i) ∧
    originalPrefix.series.data.connectingEdges i =
      ett.series.data.connectingEdges (Fin.castLE ((by omega)) i) ∧
     originalPrefix.series.data.kind i =
       ett.series.data.kind (Fin.castLE ((by omega)) i) ∧
      TashkinovStoredColors originalPrefix.series.data i =
       TashkinovStoredColors ett.series.data
        (Fin.castLE ((by omega)) i))
   (corr :
    CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigma
     (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
  corr.replacementSeries.data.tree
     (Fin.last (originalPrefix.rounds + 1)) =
    ett.series.data.tree (Fin.last ett.rounds).castSucc →
  corr.replacementSeries.data.coloring
     (Fin.last originalPrefix.rounds) =
    sigma →
  MaximumProperty corr.replacementETT →
  ∀
   (earlierPrefixBound :
    (↑available.earlier : ℕ) < originalPrefix.rounds + 1),
  let earlierPrefix : Fin (originalPrefix.rounds + 1) :=
   (⟨(↑available.earlier : ℕ), earlierPrefixBound⟩ :
    Fin (originalPrefix.rounds + 1));
  ∀
   (hearlierMap :
    Fin.castLE ((by omega)) earlierPrefix = available.earlier)
   (hearlierPositive : 0 < (↑earlierPrefix : ℕ))
   (hreplacementEarlierKind :
    corr.replacementSeries.data.kind earlierPrefix =
     some TashkinovExtensionKind.PE)
   (oldi : Fin ett.rounds)
   (oldChoice :
    MaximumDefectiveChoice G e0
     (ett.series.data.tree oldi.succ.castSucc)
     (TashkinovStoredColors ett.series.data oldi.castSucc)
     (ett.series.data.coloring oldi.castSucc))
   (oldGamma : Fin k),
  available.earlier = oldi.succ →
  ∀ (newi : Fin originalPrefix.rounds)
   (newChoice :
    MaximumDefectiveChoice G e0
     (corr.replacementSeries.data.tree newi.succ.castSucc)
     (TashkinovStoredColors corr.replacementSeries.data
      newi.castSucc)
     (corr.replacementSeries.data.coloring newi.castSucc))
   (newGamma : Fin k)
   (newCurrentDelta :
    corr.replacementSeries.data.delta newi.succ =
     some newChoice.color)
   (newCurrentGamma :
    corr.replacementSeries.data.gamma newi.succ = some newGamma)
   (hnewIndex : newi.succ = earlierPrefix)
   (htree :
    corr.replacementSeries.data.tree newi.succ.castSucc =
     ett.series.data.tree oldi.succ.castSucc),
  let oldChoiceOnNew :
   MaximumDefectiveChoice G e0
    (corr.replacementSeries.data.tree newi.succ.castSucc)
    (TashkinovStoredColors ett.series.data oldi.castSucc)
    (ett.series.data.coloring oldi.castSucc) :=
   transportDefectiveChoice htree.symm oldChoice;
  ∀ (holdColorCast : oldChoiceOnNew.color = oldChoice.color),
  s(oldChoiceOnNew.vertex, oldChoiceOnNew.otherEndpoint) =
    s(newChoice.vertex, newChoice.otherEndpoint) →
  ∀ (holdColorNe : oldGamma ≠ oldChoice.color)
   (hnewColorNe : newGamma ≠ newChoice.color)
   (hidentifiedDelta : newChoice.color = oldChoiceOnNew.color)
   (hidentifiedGamma : newGamma = oldGamma)
   (holdDeltaAvailable : oldChoice.color = available.delta)
   (holdGammaAvailable : oldGamma = available.gamma)
   (hnewDeltaAvailable : newChoice.color = available.delta)
   (hnewGammaAvailable : newGamma = available.gamma),
  let replacementLast : Fin (originalPrefix.rounds + 1) :=
   Fin.last originalPrefix.rounds;
  ∀
   (hreplacementLastMap :
    Fin.castLE ((by omega)) replacementLast = q.castSucc),
  available.delta ∈ MissingColors G sigma newChoice.vertex →
  ∀ (hgammaDeltaNe : available.gamma ≠ available.delta),
  newChoice.vertex ∈
    TreeSequenceVertexSet
     (ett.series.data.tree
      (Fin.last ett.rounds).castSucc) →
  TwoColorNontrivialPathComponent G sigma available.gamma
    available.delta (Sum.inl newChoice.vertex) →
  (∃
    v ∈
     TreeSequenceVertexSet
      (ett.series.data.tree
       (Fin.last ett.rounds).castSucc),
    Sum.inl v ∈
     TwoColorComponent G sigma available.gamma
      available.delta (Sum.inl newChoice.vertex)) →
  StableColoring (ett.series.data.tree q.succ.castSucc)
    (TashkinovStoredColors ett.series.data q.castSucc)
    (ett.series.data.coloring q.castSucc) sigma →
  let sigmaReturnGraph : SimpleGraph (V ⊕ E) :=
   TwoColorIncidenceGraph G sigma available.gamma
    available.delta;
  ∀
   (returnEdgeTransfer :
    ∀ edge ∈ available.returnPath.edges,
     edge ∈ sigmaReturnGraph.edgeSet),
  let sigmaReturnPath :
   sigmaReturnGraph.Walk (Sum.inr available.edge)
    (Sum.inl available.returnVertex) :=
   available.returnPath.transfer sigmaReturnGraph
    returnEdgeTransfer;
  ∀ (hsigmaReturnIsPath : sigmaReturnPath.IsPath)
   (hsigmaReturnSupport :
  ∀ (z : V ⊕ E),
  z ∈ sigmaReturnPath.support ↔
   z ∈ available.returnPath.support),
  Sum.inl available.returnVertex ∈
    TwoColorComponent G sigma available.gamma
     available.delta (Sum.inr available.edge) →
  Sum.inl available.outsideEndpoint ∈
    TwoColorComponent G sigma available.gamma
     available.delta (Sum.inr available.edge) →
  ∀
   (hreturnInNewEarlier :
    available.returnVertex ∈
     TreeSequenceVertexSet
      (corr.replacementSeries.data.tree
       earlierPrefix.castSucc)),
  available.returnVertex ∈
    TreeSequenceVertexSet
     (ett.series.data.tree
      (Fin.last ett.rounds).castSucc) →
  TwoColorComponent G sigma available.gamma
     available.delta (Sum.inl newChoice.vertex) ≠
    TwoColorComponent G sigma available.gamma
     available.delta (Sum.inr available.edge) →
  (∃
    v ∈
     TreeSequenceVertexSet
      (ett.series.data.tree
       (Fin.last ett.rounds).castSucc),
    Sum.inl v ∈
     TwoColorComponent G sigma available.gamma
      available.delta
      (Sum.inr available.edge)) →
  0 < corr.replacementETT.rounds →
  corr.replacementETT.rounds < ett.rounds →
  (
  ∀
   (C :
    CorrespondingExtendedTashkinovTree G k
     e0 originalPrefix sigma
     (ett.series.data.tree
      (Fin.last ett.rounds).castSucc)),
  C.replacementETT.series.data.tree
    (Fin.last
     (C.replacementETT.rounds + 1)) =
   C.replacementSeries.data.tree
    (Fin.last
     (originalPrefix.rounds + 1))) →
  corr.replacementETT.series.data.tree
     (Fin.last
      (corr.replacementETT.rounds + 1)) =
    corr.replacementSeries.data.tree
     (Fin.last
      (originalPrefix.rounds + 1)) →
  corr.replacementETT.series.data.coloring
     (Fin.last
      corr.replacementETT.rounds) =
    sigma →
  StableColoring
    (corr.replacementETT.series.data.tree
     (Fin.last
      (corr.replacementETT.rounds + 1)))
    (TashkinovStoredColors
     corr.replacementETT.series.data
     (Fin.last
      corr.replacementETT.rounds))
    (corr.replacementETT.series.data.coloring
     (Fin.last
      corr.replacementETT.rounds))
    sigma →
  corr.replacementETT.series.data.tree
     (Fin.last
      (corr.replacementETT.rounds + 1)) =
    ett.series.data.tree
     (Fin.last ett.rounds).castSucc →
  available.delta ∈
    TreeMissingColors sigma
     (corr.replacementETT.series.data.tree
      (Fin.last
       (corr.replacementETT.rounds +
        1))) →
  LowerRoundProperties
    corr.replacementETT →
  TreeInterchangeable G
    (corr.replacementETT.series.data.tree
     (Fin.last
      (corr.replacementETT.rounds +
       1)))
    sigma available.gamma
    available.delta →
  TreeInterchangeable G
    (ett.series.data.tree
     (Fin.last ett.rounds).castSucc)
    sigma available.gamma
    available.delta →
  ∀
   (replacementCycle :
    TwoColorCycle G sigma
     available.gamma
     available.delta)
   (hcycleFull :
  ∀ (x : V ⊕ E),
  x ∈
    replacementCycle.walk.support ↔
   x ∈
    TwoColorComponent G sigma
     available.gamma
     available.delta
     (Sum.inr available.edge)),
  ColoredVertexSetClosed G sigma
    (TreeSequenceVertexSet
     (ett.series.data.tree
      q.succ.castSucc)) →
  ColoredVertexSetClosed G sigma
    (TreeSequenceVertexSet
     (ett.series.data.tree
      (Fin.last
        ett.rounds).castSucc)) →
  ∀
   (hreplacementCurrentTree :
  have replacementLast :
   Fin
    (originalPrefix.rounds +
     1) :=
   Fin.last
    originalPrefix.rounds;
  corr.replacementSeries.data.tree
    replacementLast.succ =
   ett.series.data.tree
    (Fin.last
      ett.rounds).castSucc),
  q.castSucc.succ =
    (Fin.last
      ett.rounds).castSucc →
  ∀
   (havailableCurrentTree :
    ett.series.data.tree
      q.castSucc.succ =
     ett.series.data.tree
      (Fin.last
        ett.rounds).castSucc),
  let currentTree :
   Finset V :=
   TreeSequenceVertexSet
    (ett.series.data.tree
     q.succ.castSucc);
  ∀
   (hreturnCycle :
    Sum.inl
      available.returnVertex ∈
     replacementCycle.walk.support)
   (houtsideCycle :
    Sum.inl
      available.outsideEndpoint ∈
     replacementCycle.walk.support),
  available.returnVertex ∈
    currentTree →
  available.outsideEndpoint ∉
    currentTree →
  let rootedCycle :
   (TwoColorIncidenceGraph
      G sigma
      available.gamma
      available.delta).Walk
    (Sum.inl
     available.returnVertex)
    (Sum.inl
     available.returnVertex) :=
   replacementCycle.walk.rotate
    (Sum.inl
     available.returnVertex)
    hreturnCycle;
  rootedCycle.IsCycle →
  Sum.inl
     available.outsideEndpoint ∈
    rootedCycle.support →
  let outsideIndices :
   Finset
    (Fin
     (rootedCycle.length +
      1)) :=
   {i :
    Fin
     (rootedCycle.length +
      1) |
    ∃ (v : V),
     rootedCycle.getVert
        (↑i : ℕ) =
       Sum.inl v ∧
      v ∉ currentTree};
  ∀
   (outsideIndicesNonempty :
    outsideIndices.Nonempty),
  let firstOutside :
   Fin
    (rootedCycle.length +
     1) :=
   outsideIndices.min'
    outsideIndicesNonempty;
  ∀ (outsideOne : V),
  rootedCycle.getVert
     (↑(outsideIndices.min'
        outsideIndicesNonempty) :
      ℕ) =
    Sum.inl
     outsideOne →
  outsideOne ∉
    currentTree →
  (
  ∀
   (idx :
    Fin
     (rootedCycle.length +
      1)),
  (↑idx : ℕ) <
    (↑firstOutside :
     ℕ) →
  ∀ (v : V),
  rootedCycle.getVert
     (↑idx : ℕ) =
    Sum.inl v →
  v ∈
   currentTree) →
  0 <
    (↑firstOutside :
     ℕ) →
  (↑firstOutside :
     ℕ) <
    rootedCycle.length →
  ∀
   (firstOutsideNotOne :
    (↑firstOutside :
      ℕ) ≠
     1)
   (firstOutsideAtLeastTwo :
    2 ≤
     (↑firstOutside :
      ℕ)),
  (TwoColorIncidenceGraph
      G sigma
      available.gamma
      available.delta).Adj
    (rootedCycle.getVert
     ((↑firstOutside :
       ℕ) -
      1))
    (rootedCycle.getVert
     ((↑firstOutside :
        ℕ) -
       1 +
      1)) →
  ∀
   (firstCrossingIndex :
    (↑firstOutside :
        ℕ) -
       1 +
      1 =
     (↑firstOutside :
      ℕ))
   (firstEdge :
    E),
  rootedCycle.getVert
     ((↑firstOutside :
       ℕ) -
      1) =
    Sum.inr
     firstEdge →
  Incident G
    outsideOne
    firstEdge →
  sigma
      firstEdge =
     some
      available.gamma ∨
    sigma
      firstEdge =
     some
      available.delta →
  (TwoColorIncidenceGraph
      G
      sigma
      available.gamma
      available.delta).Adj
    (rootedCycle.getVert
     ((↑firstOutside :
       ℕ) -
      2))
    (rootedCycle.getVert
     ((↑firstOutside :
        ℕ) -
       2 +
      1)) →
  ∀
   (beforeFirstCrossingIndex :
    (↑firstOutside :
        ℕ) -
       2 +
      1 =
     (↑firstOutside :
       ℕ) -
      1)
   (insideOne :
    V),
  rootedCycle.getVert
     ((↑firstOutside :
       ℕ) -
      2) =
    Sum.inl
     insideOne →
  insideOne ∈
    currentTree →
  Incident
    G
    insideOne
    firstEdge →
  (
  ∀
   {f :
    E}
   {a
    b :
    V},
  Incident
    G
    a
    f →
  Incident
    G
    b
    f →
  a ≠
    b →
  G.ends
    f =
   s(a,
    b)) →
  insideOne ≠
    outsideOne →
  G.ends
     firstEdge =
    s(insideOne,
     outsideOne) →
  firstEdge ∈
    BoundaryEdges
     G
     currentTree →
  let
   laterInsideIndices :
   Finset
    (Fin
     (rootedCycle.length +
      1)) :=
   {idx :
    Fin
     (rootedCycle.length +
      1) |
    (↑firstOutside :
       ℕ) <
      (↑idx :
       ℕ) ∧
     ∃
      (v
      :
      V),
      rootedCycle.getVert
         (↑idx :
          ℕ) =
        Sum.inl
         v ∧
       v ∈
        currentTree};
  ∀
   (laterInsideNonempty :
    laterInsideIndices.Nonempty),
  let
   firstReturn :
   Fin
    (rootedCycle.length +
     1) :=
   laterInsideIndices.min'
    laterInsideNonempty;
  laterInsideIndices.min'
     laterInsideNonempty ∈
    laterInsideIndices →
  (↑firstOutside :
     ℕ) <
    (↑firstReturn :
     ℕ) →
  ∀
   (insideTwo :
    V),
  rootedCycle.getVert
     (↑(laterInsideIndices.min'
        laterInsideNonempty) :
      ℕ) =
    Sum.inl
     insideTwo →
  insideTwo ∈
    currentTree →
  ∀
   (hreturnNotNext :
    (↑firstReturn :
      ℕ) ≠
     (↑firstOutside :
       ℕ) +
      1)
   (hreturnGap :
    (↑firstOutside :
       ℕ) +
      2 ≤
     (↑firstReturn :
      ℕ)),
  (TwoColorIncidenceGraph
      G
      sigma
      available.gamma
      available.delta).Adj
    (rootedCycle.getVert
     ((↑firstReturn :
       ℕ) -
      1))
    (rootedCycle.getVert
     ((↑firstReturn :
        ℕ) -
       1 +
      1)) →
  ∀
   (returnCrossingIndex :
    (↑firstReturn :
        ℕ) -
       1 +
      1 =
     (↑firstReturn :
      ℕ))
   (secondEdge :
    E),
  rootedCycle.getVert
     ((↑firstReturn :
       ℕ) -
      1) =
    Sum.inr
     secondEdge →
  Incident
    G
    insideTwo
    secondEdge →
  sigma
      secondEdge =
     some
      available.gamma ∨
    sigma
      secondEdge =
     some
      available.delta →
  (TwoColorIncidenceGraph
      G
      sigma
      available.gamma
      available.delta).Adj
    (rootedCycle.getVert
     ((↑firstReturn :
       ℕ) -
      2))
    (rootedCycle.getVert
     ((↑firstReturn :
        ℕ) -
       2 +
      1)) →
  ∀
   (beforeReturnCrossingIndex :
    (↑firstReturn :
        ℕ) -
       2 +
      1 =
     (↑firstReturn :
       ℕ) -
      1)
   (outsideTwo :
    V),
  rootedCycle.getVert
     ((↑firstReturn :
       ℕ) -
      2) =
    Sum.inl
     outsideTwo →
  outsideTwo ∉
    currentTree →
  Incident
    G
    outsideTwo
    secondEdge →
  outsideTwo ≠
    insideTwo →
  G.ends
     secondEdge =
    s(insideTwo,
     outsideTwo) →
  secondEdge ∈
    BoundaryEdges
     G
     currentTree →
  firstEdge ≠
    secondEdge →
  newChoice.vertex ∈
    currentTree →
  sigma
     firstEdge =
    some
     available.gamma →
  sigma
     secondEdge =
    some
     available.gamma →
  ¬ColoredVertexSetStronglyClosed
     G
     sigma
     currentTree →
  ∀
   (hreplacementColor :
    corr.replacementSeries.data.coloring
      replacementLast =
     sigma),
  let
   castReturnWalk :
  (phi
    psi :
    PartialEdgeColoring
     E
     k) →
  phi =
    psi →
  (TwoColorIncidenceGraph
      G
      psi
      available.gamma
      available.delta).Walk
    (Sum.inr
     available.edge)
    (Sum.inl
     available.returnVertex) →
  (TwoColorIncidenceGraph
     G
     phi
     available.gamma
     available.delta).Walk
   (Sum.inr
    available.edge)
   (Sum.inl
    available.returnVertex) :=
   fun
    (phi
      psi :
     PartialEdgeColoring
      E
      k)
    (hphi :
     phi =
      psi)
    (P :
     (TwoColorIncidenceGraph
        G
        psi
        available.gamma
        available.delta).Walk
      (Sum.inr
       available.edge)
      (Sum.inl
       available.returnVertex)) ↦
   Eq.ndrec
    (motive :=
    fun
     (psi :
      PartialEdgeColoring
       E
       k) ↦
  (TwoColorIncidenceGraph
      G
      psi
      available.gamma
      available.delta).Walk
    (Sum.inr
     available.edge)
    (Sum.inl
     available.returnVertex) →
  (TwoColorIncidenceGraph
     G
     phi
     available.gamma
     available.delta).Walk
   (Sum.inr
    available.edge)
   (Sum.inl
    available.returnVertex))
    (fun
      (P :
       (TwoColorIncidenceGraph
          G
          phi
          available.gamma
          available.delta).Walk
        (Sum.inr
         available.edge)
        (Sum.inl
         available.returnVertex)) ↦
     P)
    hphi
    P;
  ∀
   (castReturnWalkIsPath :
  ∀
   (phi
    psi :
    PartialEdgeColoring
     E
     k)
   (hphi :
    phi =
     psi)
   (P :
    (TwoColorIncidenceGraph
       G
       psi
       available.gamma
       available.delta).Walk
     (Sum.inr
      available.edge)
     (Sum.inl
      available.returnVertex)),
  P.IsPath →
  (castReturnWalk
    phi
    psi
    hphi
    P).IsPath)
   (castReturnWalkSupport :
  ∀
   (phi
    psi :
    PartialEdgeColoring
     E
     k)
   (hphi :
    phi =
     psi)
   (P :
    (TwoColorIncidenceGraph
       G
       psi
       available.gamma
       available.delta).Walk
     (Sum.inr
      available.edge)
     (Sum.inl
      available.returnVertex))
   (z :
    V ⊕
     E),
  z ∈
    (castReturnWalk
      phi
      psi
      hphi
      P).support ↔
   z ∈
    P.support),
  let
   castCycle :
  (phi
    psi :
    PartialEdgeColoring
     E
     k) →
  phi =
    psi →
  TwoColorCycle
    G
    psi
    available.gamma
    available.delta →
  TwoColorCycle
   G
   phi
   available.gamma
   available.delta :=
   fun
    (phi
      psi :
     PartialEdgeColoring
      E
      k)
    (hphi :
     phi =
      psi)
    (C :
     TwoColorCycle
      G
      psi
      available.gamma
      available.delta) ↦
   Eq.ndrec
    (motive :=
    fun
     (psi :
      PartialEdgeColoring
       E
       k) ↦
  TwoColorCycle
    G
    psi
    available.gamma
    available.delta →
  TwoColorCycle
   G
   phi
   available.gamma
   available.delta)
    (fun
      (C :
       TwoColorCycle
        G
        phi
        available.gamma
        available.delta) ↦
     C)
    hphi
    C;
  ∀
   (castCycleSupport :
  ∀
   (phi
    psi :
    PartialEdgeColoring
     E
     k)
   (hphi :
    phi =
     psi)
   (C :
    TwoColorCycle
     G
     psi
     available.gamma
     available.delta)
   (z :
    V ⊕
     E),
  z ∈
    (castCycle
      phi
      psi
      hphi
      C).walk.support ↔
   z ∈
    C.walk.support),
  let
   replacementCycleForPrefix :
   TwoColorCycle
    G
    (corr.replacementSeries.data.coloring
     replacementLast)
    available.gamma
    available.delta :=
   castCycle
    (corr.replacementSeries.data.coloring
     replacementLast)
    sigma
    hreplacementColor
    replacementCycle;
  let
   replacementReturnPath :
   (TwoColorIncidenceGraph
      G
      (corr.replacementSeries.data.coloring
       replacementLast)
      available.gamma
      available.delta).Walk
    (Sum.inr
     available.edge)
    (Sum.inl
     available.returnVertex) :=
   castReturnWalk
    (corr.replacementSeries.data.coloring
     replacementLast)
    sigma
    hreplacementColor
    sigmaReturnPath;
  (
  have
   sigmaReturnPath :
   (TwoColorIncidenceGraph
      G
      sigma
      available.gamma
      available.delta).Walk
    (Sum.inr
     available.edge)
    (Sum.inl
     available.returnVertex) :=
   available.returnPath.transfer
    (TwoColorIncidenceGraph
     G
     sigma
     available.gamma
     available.delta)
    returnEdgeTransfer;
  ∀
   z ∈
    sigmaReturnPath.support,
   z ∈
    TwoColorComponent
     G
     sigma
     available.gamma
     available.delta
     (Sum.inr
      available.edge)) →
  ∀
   (hsigmaPathOnCycle :
    ∀
     z ∈
      sigmaReturnPath.support,
     z ∈
      replacementCycle.walk.support),
  let
   replacementCertificate :
   RevisitingExtensionCertificate
    corr.replacementSeries.data
    replacementLast :=
   {
    earlier :=
     earlierPrefix,
    earlierPositive :=
     hearlierPositive,
    earlierAtMost :=
     Nat.le_of_lt_succ
      earlierPrefix.isLt,
    earlierPE :=
     hreplacementEarlierKind,
    interveningRevisiting :=
     helper_interveningRevisiting_4368
      G
      k
      e0
      input
      T
      generating
      ett
      hpositive
      sigma
      Tstar
      hqCast
      available
      hroundLarge
      originalPrefix
      hr
      hprefixData
      corr
      earlierPrefixBound
      hearlierMap
      oldi
      oldChoice
      oldGamma
      newi
      newChoice
      newGamma
      htree
      holdColorCast
      holdColorNe
      hnewColorNe
      hidentifiedDelta
      hidentifiedGamma
      holdDeltaAvailable
      holdGammaAvailable
      hreplacementLastMap
      hgammaDeltaNe
      replacementCycle
      hreturnCycle
      outsideIndicesNonempty
      firstOutsideNotOne
      firstOutsideAtLeastTwo
      firstCrossingIndex
      beforeFirstCrossingIndex
      laterInsideNonempty
      hreturnNotNext
      hreturnGap
      returnCrossingIndex
      beforeReturnCrossingIndex,
    gamma :=
     available.gamma,
    delta :=
     available.delta,
    earlierGamma :=
     Eq.mpr
      (id
       (congrArg
        (fun
          (_a :
           Fin
            (originalPrefix.rounds +
             1)) ↦
         corr.replacementSeries.data.gamma
           _a =
          some
           available.gamma)
        (Eq.symm
         hnewIndex)))
      (Eq.mpr
       (id
        (congrArg
         (fun
           (_a :
            Option
             (Fin
              k)) ↦
          _a =
           some
            available.gamma)
         newCurrentGamma))
       (Eq.mpr
        (id
         (congrArg
          (fun
            (_a :
             Fin
              k) ↦
           some
             _a =
            some
             available.gamma)
          hnewGammaAvailable))
        (Eq.refl
         (some
          available.gamma)))),
    earlierDelta :=
     Eq.mpr
      (id
       (congrArg
        (fun
          (_a :
           Fin
            (originalPrefix.rounds +
             1)) ↦
         corr.replacementSeries.data.delta
           _a =
          some
           available.delta)
        (Eq.symm
         hnewIndex)))
      (Eq.mpr
       (id
        (congrArg
         (fun
           (_a :
            Option
             (Fin
              k)) ↦
          _a =
           some
            available.delta)
         newCurrentDelta))
       (Eq.mpr
        (id
         (congrArg
          (fun
            (_a :
             Fin
              k) ↦
           some
             _a =
            some
             available.delta)
          hnewDeltaAvailable))
        (Eq.refl
         (some
          available.delta)))),
    cycle :=
     replacementCycleForPrefix,
    meetsEarlier :=
     Exists.intro
      available.returnVertex
      (⟨hreturnInNewEarlier,
        (castCycleSupport
           (corr.replacementSeries.data.coloring
            replacementLast)
           sigma
           hreplacementColor
           replacementCycle
           (Sum.inl
            available.returnVertex)).mpr
         hreturnCycle⟩ :
       available.returnVertex ∈
         TreeSequenceVertexSet
          (corr.replacementSeries.data.tree
           earlierPrefix.castSucc) ∧
        Sum.inl
          available.returnVertex ∈
         replacementCycleForPrefix.walk.support),
    leavesCurrent :=
     helper_leavesCurrent_4395
      G
      k
      e0
      input
      T
      generating
      ett
      hpositive
      sigma
      Tstar
      available
      hroundLarge
      originalPrefix
      corr
      replacementCycle
      hreplacementCurrentTree
      havailableCurrentTree
      houtsideCycle
      hreplacementColor
      castCycleSupport,
    edge :=
     available.edge,
    edgeOnCycle :=
     (castCycleSupport
        (corr.replacementSeries.data.coloring
         replacementLast)
        sigma
        hreplacementColor
        replacementCycle
        (Sum.inr
         available.edge)).mpr
      ((hcycleFull
         (Sum.inr
          available.edge)).mpr
       rfl),
    edgeBoundary :=
     Eq.mpr
      (id
       (congrArg
        (fun
          (_a :
           TreeSequence
            G
            e0) ↦
         available.edge ∈
          BoundaryEdges
           G
           (TreeSequenceVertexSet
            _a))
        hreplacementCurrentTree))
      (Eq.mpr
       (id
        (congrArg
         (fun
           (_a :
            TreeSequence
             G
             e0) ↦
          available.edge ∈
           BoundaryEdges
            G
            (TreeSequenceVertexSet
             _a))
         (Eq.symm
          havailableCurrentTree)))
       available.edgeBoundary),
    insideEndpoint :=
     available.insideEndpoint,
    outsideEndpoint :=
     available.outsideEndpoint,
    insideInCurrent :=
     Eq.mpr
      (id
       (congrArg
        (fun
          (_a :
           TreeSequence
            G
            e0) ↦
         available.insideEndpoint ∈
          TreeSequenceVertexSet
           _a)
        hreplacementCurrentTree))
      (Eq.mpr
       (id
        (congrArg
         (fun
           (_a :
            TreeSequence
             G
             e0) ↦
          available.insideEndpoint ∈
           TreeSequenceVertexSet
            _a)
         (Eq.symm
          havailableCurrentTree)))
       available.insideInCurrent),
    outsideNotCurrent :=
     Eq.mpr
      (id
       (congrArg
        (fun
          (_a :
           TreeSequence
            G
            e0) ↦
         available.outsideEndpoint ∉
          TreeSequenceVertexSet
           _a)
        hreplacementCurrentTree))
      (Eq.mpr
       (id
        (congrArg
         (fun
           (_a :
            TreeSequence
             G
             e0) ↦
          available.outsideEndpoint ∉
           TreeSequenceVertexSet
            _a)
         (Eq.symm
          havailableCurrentTree)))
       available.outsideNotCurrent),
    edgeEnds :=
     available.edgeEnds,
    returnVertex :=
     available.returnVertex,
    returnInEarlier :=
     hreturnInNewEarlier,
    returnPath :=
     replacementReturnPath,
    returnPathIsPath :=
     castReturnWalkIsPath
      (corr.replacementSeries.data.coloring
       replacementLast)
      sigma
      hreplacementColor
      sigmaReturnPath
      hsigmaReturnIsPath,
    returnPathOnCycle :=
     helper_returnPathOnCycle_4421
      G
      k
      e0
      input
      T
      generating
      ett
      hpositive
      sigma
      Tstar
      available
      hroundLarge
      originalPrefix
      corr
      returnEdgeTransfer
      replacementCycle
      hreplacementColor
      castReturnWalkSupport
      castCycleSupport
      hsigmaPathOnCycle,
    returnPathInternal :=
     helper_returnPathInternal_4428
      G
      k
      e0
      input
      T
      generating
      ett
      hpositive
      sigma
      Tstar
      available
      hroundLarge
      originalPrefix
      corr
      returnEdgeTransfer
      hsigmaReturnSupport
      hreplacementCurrentTree
      havailableCurrentTree
      hreplacementColor
      castReturnWalkSupport :
    RevisitingExtensionCertificate
     corr.replacementSeries.data
     replacementLast };
  fstar =
    available.edge →
  let
   newStored :
   Finset
    (Fin
     k) :=
   {
    available.delta,
    available.gamma };
  let
   newEdges :
   Finset
    E :=
   {
    available.edge };
  let
   newKind :
   Option
    TashkinovExtensionKind :=
   some
    TashkinovExtensionKind.RE;
  let
   newVertex :
   Option
    V :=
   some
    available.insideEndpoint;
  let
   newOutside :
   Option
    V :=
   some
    available.outsideEndpoint;
  let
   newDelta :
   Option
    (Fin
     k) :=
   some
    available.delta;
  let
   newGamma_1 :
   Option
    (Fin
     k) :=
   some
    available.gamma;
  let
   appendedData :
   TashkinovSeriesData
    G
    k
    (originalPrefix.rounds +
     1)
    e0 :=
   TashkinovSeriesDataAppend
    corr.replacementSeries.data
    closureTree
    sigma
    newStored
    newEdges
    newKind
    newVertex
    newOutside
    newDelta
    newGamma_1;
  ∀
   (appendedCertificate :
    RevisitingExtensionCertificate
     (TashkinovSeriesDataAppend
      corr.replacementSeries.data
      closureTree
      sigma
      newStored
      newEdges
      newKind
      newVertex
      newOutside
      newDelta
      newGamma_1)
     replacementLast.castSucc),
  appendedCertificate.gamma =
    replacementCertificate.gamma →
  appendedCertificate.delta =
    replacementCertificate.delta →
  appendedCertificate.edge =
    replacementCertificate.edge →
  appendedCertificate.insideEndpoint =
    replacementCertificate.insideEndpoint →
  appendedCertificate.outsideEndpoint =
    replacementCertificate.outsideEndpoint →
  (ett.series.data.tree
      (Fin.last
        ett.rounds).castSucc).length <
    closureTree.length →
  TashkinovSeriesStep
    G
    k
    (originalPrefix.rounds +
     1)
    e0
    corr.replacementInput
    appendedData
    (Fin.last
     (originalPrefix.rounds +
      1)) →
  ∀
   (extendedSeries :
    TashkinovSeries
     G
     k
     (originalPrefix.rounds +
      1)
     e0
     corr.replacementInput),
  extendedSeries.data =
    TashkinovSeriesDataAppend
     corr.replacementSeries.data
     closureTree
     sigma
     newStored
     newEdges
     newKind
     newVertex
     newOutside
     newDelta
     newGamma_1 →
  ∀
   (hroundsEq :
    originalPrefix.rounds +
      1 =
     ett.rounds),
  let
   castSeries :
  {a
    b :
    ℕ} →
  a =
    b →
  TashkinovSeries
    G
    k
    a
    e0
    corr.replacementInput →
  TashkinovSeries
   G
   k
   b
   e0
   corr.replacementInput :=
   fun
    {a
     b :
     ℕ}
    (h :
     a =
      b)
    (S :
     TashkinovSeries
      G
      k
      a
      e0
      corr.replacementInput) ↦
   h ▸
    S;
  (
  ∀
   {a
    b :
    ℕ}
   (h :
    a =
     b)
   (S :
    TashkinovSeries
     G
     k
     a
     e0
     corr.replacementInput)
   (i :
    Fin
     (b +
      2)),
  (castSeries
      h
      S).data.tree
    i =
   S.data.tree
    (Fin.cast
     (congrArg
      (fun
        (m :
         ℕ) ↦
       m +
        2)
      (Eq.symm
       h))
     i)) →
  (
  ∀
   {a
    b :
    ℕ}
   (h :
    a =
     b)
   (S :
    TashkinovSeries
     G
     k
     a
     e0
     corr.replacementInput)
   (i :
    Fin
     (b +
      1)),
  (castSeries
      h
      S).data.coloring
    i =
   S.data.coloring
    (Fin.cast
     (congrArg
      (fun
        (m :
         ℕ) ↦
       m +
        1)
      (Eq.symm
       h))
     i)) →
  (
  ∀
   {a
    b :
    ℕ}
   (h :
    a =
     b)
   (S :
    TashkinovSeries
     G
     k
     a
     e0
     corr.replacementInput)
   (i :
    Fin
     (b +
      1)),
  (castSeries
      h
      S).data.stored
    i =
   S.data.stored
    (Fin.cast
     (congrArg
      (fun
        (m :
         ℕ) ↦
       m +
        1)
      (Eq.symm
       h))
     i)) →
  (
  ∀
   {a
    b :
    ℕ}
   (h :
    a =
     b)
   (S :
    TashkinovSeries
     G
     k
     a
     e0
     corr.replacementInput)
   (i :
    Fin
     (b +
      1)),
  (castSeries
      h
      S).data.connectingEdges
    i =
   S.data.connectingEdges
    (Fin.cast
     (congrArg
      (fun
        (m :
         ℕ) ↦
       m +
        1)
      (Eq.symm
       h))
     i)) →
  (
  ∀
   {a
    b :
    ℕ}
   (h :
    a =
     b)
   (S :
    TashkinovSeries
     G
     k
     a
     e0
     corr.replacementInput)
   (i :
    Fin
     (b +
      1)),
  (castSeries
      h
      S).data.kind
    i =
   S.data.kind
    (Fin.cast
     (congrArg
      (fun
        (m :
         ℕ) ↦
       m +
        1)
      (Eq.symm
       h))
     i)) →
  let
   finalSeries :
   TashkinovSeries
    G
    k
    ett.rounds
    e0
    corr.replacementInput :=
   castSeries
    hroundsEq
    extendedSeries;
  let
   rawPenultimate :
   Fin
    (originalPrefix.rounds +
     3) :=
   Fin.cast
    (congrArg
     (fun
       (m :
        ℕ) ↦
      m +
       2)
     (Eq.symm
      hroundsEq))
    (⟨ett.rounds,
      Decidable.byContradiction
       fun
        (a :
         ¬ett.rounds <
           ett.rounds +
            2) ↦
       (by
        omega)⟩ :
     Fin
      (ett.rounds +
       2));
  rawPenultimate =
    replacementLast.succ.castSucc →
  finalSeries.data.tree
     (⟨ett.rounds,
       Decidable.byContradiction
        fun
         (a :
          ¬ett.rounds <
            ett.rounds +
             2) ↦
        (by
         omega)⟩ :
      Fin
       (ett.rounds +
        2)) =
    ett.series.data.tree
     (Fin.last
       ett.rounds).castSucc →
  let
   rawFinalTree :
   Fin
    (originalPrefix.rounds +
     3) :=
   Fin.cast
    (congrArg
     (fun
       (m :
        ℕ) ↦
      m +
       2)
     (Eq.symm
      hroundsEq))
    (Fin.last
     (ett.rounds +
      1));
  rawFinalTree =
    Fin.last
     (originalPrefix.rounds +
      2) →
  ((fun
         {a
          b :
          ℕ}
         (h :
          a =
           b)
         (S :
          TashkinovSeries
           G
           k
           a
           e0
           corr.replacementInput) ↦
        h ▸
         S)
       hroundsEq
       extendedSeries).data.tree
     (Fin.last
      (ett.rounds +
       1)) =
    closureTree →
  let
   rawFinalColor :
   Fin
    (originalPrefix.rounds +
     2) :=
   Fin.cast
    (congrArg
     (fun
       (m :
        ℕ) ↦
      m +
       1)
     (Eq.symm
      hroundsEq))
    (Fin.last
     ett.rounds);
  rawFinalColor =
    Fin.last
     (originalPrefix.rounds +
      1) →
  ((fun
         {a
          b :
          ℕ}
         (h :
          a =
           b)
         (S :
          TashkinovSeries
           G
           k
           a
           e0
           corr.replacementInput) ↦
        h ▸
         S)
       hroundsEq
       extendedSeries).data.coloring
     (Fin.last
      ett.rounds) =
    sigma →
  let
   rawDataIndex :
  Fin
    (ett.rounds +
     1) →
  Fin
   (originalPrefix.rounds +
    2) :=
   fun
    (i :
     Fin
      (ett.rounds +
       1)) ↦
   Fin.cast
    (congrArg
     (fun
       (m :
        ℕ) ↦
      m +
       1)
     (Eq.symm
      hroundsEq))
    i;
  (
  ∀
   (i :
    Fin
     (ett.rounds +
      1)),
  finalSeries.data.stored
     i =
    ett.series.data.stored
     i ∧
   finalSeries.data.connectingEdges
      i =
     ett.series.data.connectingEdges
      i ∧
    finalSeries.data.kind
      i =
     ett.series.data.kind
      i) →
  let
   rawTreeIndex :
  Fin
    (ett.rounds +
     2) →
  Fin
   (originalPrefix.rounds +
    3) :=
   fun
    (i :
     Fin
      (ett.rounds +
       2)) ↦
   Fin.cast
    (congrArg
     (fun
       (m :
        ℕ) ↦
      m +
       2)
     (Eq.symm
      hroundsEq))
    i;
  Nonempty
   (CorrespondingExtendedTashkinovTree
    G
    k
    e0
    ett
    sigma
    Tstar)

open scoped Sym2

theorem helper_lastStep_6001.{u_1, u_2} :
    terminalLastStepStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hpositive sigma hsigmaProper hsigmaOne _ fstar
      seed hadjoin closureTree hseedClosure hTnClosure q hqSucc hqCast adjoined previousProper
      previousOneUncolored previousClosed available hroundLarge originalPrefix hr hprefixData corr
      hcorrFinalTree earlierPrefixBound earlierPrefix hearlierMap hearlierPositive
      hreplacementEarlierKind oldi oldChoice oldGamma holdTarget newi newChoice _ newCurrentDelta
      newCurrentGamma hnewIndex htree oldChoiceOnNew holdColorCast hends holdColorNe hnewColorNe
      hidentifiedDelta hidentifiedGamma holdDeltaAvailable holdGammaAvailable hnewDeltaAvailable
      hnewGammaAvailable replacementLast hreplacementLastMap hgammaDeltaNe hsigmaPrevStableQ
      sigmaReturnGraph returnEdgeTransfer sigmaReturnPath hsigmaReturnIsPath hsigmaReturnSupport
      hreturnInNewEarlier replacementCycle hcycleFull hclosedFinal hreplacementCurrentTree
      havailableCurrentTree currentTree hreturnCycle houtsideCycle rootedCycle outsideIndices
      outsideIndicesNonempty firstOutside firstOutsideNotOne firstOutsideAtLeastTwo
      firstCrossingIndex beforeFirstCrossingIndex laterInsideIndices laterInsideNonempty firstReturn
      hreturnNotNext hreturnGap returnCrossingIndex beforeReturnCrossingIndex hnotStrongSigma
      hreplacementColor castReturnWalk castReturnWalkIsPath castReturnWalkSupport castCycle
      castCycleSupport replacementCycleForPrefix replacementReturnPath hsigmaPathOnCycle
      replacementCertificate hfstar newStored newEdges newKind newVertex newOutside newDelta
      newGamma appendedData appendedCertificate happGamma happDelta happEdge happInside happOutside
      hstrictClosure
  have hlast : replacementLast.succ =
      Fin.last (originalPrefix.rounds + 1) := by
    apply Fin.ext
    simp [replacementLast]
  have hclosedReplacement : ColoredVertexSetClosed G sigma
      (TreeSequenceVertexSet
        (corr.replacementSeries.data.tree
          (Fin.last (originalPrefix.rounds + 1)))) := by
    rw [hcorrFinalTree]
    exact hclosedFinal
  rw [← hlast]
  apply TashkinovSeriesStep.RE (i := replacementLast)
    (available := appendedCertificate) (adjoined := seed)
  · simpa [appendedData, TashkinovSeriesDataAppend,
      hlast, replacementLast, hreplacementColor] using hsigmaProper
  · simpa [appendedData, TashkinovSeriesDataAppend,
      hlast, replacementLast, hreplacementColor] using hsigmaOne
  · simp only [TashkinovSeriesDataAppend,
      Fin.lastCases_castSucc]
    rw [hreplacementColor, hlast]
    intro f c v hf hv hsf hcm
    obtain ⟨x, hx, y, hy, hends⟩ := by
      simpa [BoundaryEdges] using hf
    have htreeEq : TreeSequenceVertexSet
          (corr.replacementSeries.data.tree
            (Fin.last (originalPrefix.rounds + 1))) =
        TreeSequenceVertexSet
          (ett.series.data.tree q.succ.castSucc) := by
      rw [hcorrFinalTree, hqSucc]
    have hxOld : x ∈ TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc) := by
      rw [← htreeEq]
      exact hx
    have hyOld : y ∉ TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc) := by
      rw [← htreeEq]
      exact hy
    have hfOld : f ∈ BoundaryEdges G
        (TreeSequenceVertexSet
          (ett.series.data.tree q.succ.castSucc)) := by
      simp only [BoundaryEdges, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact ⟨x, hxOld, y, hyOld, hends⟩
    have hvOld : v ∈ TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc) := by
      rw [← htreeEq]
      exact hv
    have hxf : Incident G x f := by
      unfold Incident
      rw [hends]
      exact Sym2.mem_mk_left _ _
    have hmissingEq := hsigmaPrevStableQ.2 v hvOld
    have hcTree : c ∈ TreeMissingColors
        (ett.series.data.coloring q.castSucc)
        (ett.series.data.tree q.succ.castSucc) := by
      simp only [TreeMissingColors, Finset.mem_biUnion]
      exact ⟨v, hvOld, hmissingEq ▸ hcm⟩
    have hcriterion := (sc1 G e0
      (ett.series.data.tree q.succ.castSucc)
      (TashkinovStoredColors ett.series.data q.castSucc)
      (ett.series.data.coloring q.castSucc) sigma
      previousProper previousOneUncolored hsigmaProper
      hsigmaOne).mp hsigmaPrevStableQ
    have hcopy := hcriterion f ⟨x, hxOld, hxf⟩
      (Or.inr ⟨c, Finset.mem_union_left _ hcTree, hsf⟩)
    have holdf : ett.series.data.coloring q.castSucc f =
        some c := hcopy.symm.trans hsf
    have hnotOld := previousClosed hfOld hvOld holdf
    exact hnotOld (hmissingEq ▸ hcm)
  · simpa [appendedData, TashkinovSeriesDataAppend,
      hlast, replacementLast, hreplacementColor,
      hcorrFinalTree, currentTree, hqSucc] using
      hnotStrongSigma
  · simp [TashkinovSeriesDataAppend,
      hlast, replacementLast, hreplacementColor]
  · simp [TashkinovSeriesDataAppend, newStored,
      hlast, replacementCertificate, happDelta, happGamma]
  · simp [TashkinovSeriesDataAppend, newEdges,
      hlast, replacementCertificate, happEdge]
  · simp [TashkinovSeriesDataAppend, hlast, newKind]
  · simp [TashkinovSeriesDataAppend, newVertex,
      hlast, replacementCertificate, happInside]
  · simp [TashkinovSeriesDataAppend, newOutside,
      hlast, replacementCertificate, happOutside]
  · simp [TashkinovSeriesDataAppend, newDelta,
      hlast, replacementCertificate, happDelta]
  · simp [TashkinovSeriesDataAppend, newGamma,
      hlast, replacementCertificate, happGamma]
  · simpa [appendedData, TashkinovSeriesDataAppend,
      hlast, replacementLast, hcorrFinalTree, hfstar,
      replacementCertificate, happEdge] using hadjoin
  · simpa [appendedData, TashkinovSeriesDataAppend, hlast] using
      hseedClosure
  · simpa [appendedData, TashkinovSeriesDataAppend,
      hlast, replacementLast, hcorrFinalTree] using hTnClosure
  · simpa [appendedData, TashkinovSeriesDataAppend,
      hlast, replacementLast, hcorrFinalTree] using
      hstrictClosure

theorem helper_hfinalPenultimateTree_6172.{u_1, u_2} :
    penultimateTreeStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hpositive sigma _ closureTree q hqCast
      available hroundLarge originalPrefix hr hprefixData corr earlierPrefixBound earlierPrefix
      hearlierMap hearlierPositive hreplacementEarlierKind oldi oldChoice oldGamma holdTarget newi
      newChoice _ newCurrentDelta newCurrentGamma hnewIndex htree oldChoiceOnNew holdColorCast
      holdColorNe hnewColorNe hidentifiedDelta hidentifiedGamma holdDeltaAvailable
      holdGammaAvailable hnewDeltaAvailable hnewGammaAvailable replacementLast hreplacementLastMap
      hgammaDeltaNe sigmaReturnGraph returnEdgeTransfer sigmaReturnPath hsigmaReturnIsPath
      hsigmaReturnSupport hreturnInNewEarlier replacementCycle hcycleFull hreplacementCurrentTree
      havailableCurrentTree currentTree hreturnCycle houtsideCycle rootedCycle outsideIndices
      outsideIndicesNonempty firstOutside firstOutsideNotOne firstOutsideAtLeastTwo
      firstCrossingIndex beforeFirstCrossingIndex laterInsideIndices laterInsideNonempty firstReturn
      hreturnNotNext hreturnGap returnCrossingIndex beforeReturnCrossingIndex hreplacementColor
      castReturnWalk castReturnWalkIsPath castReturnWalkSupport castCycle castCycleSupport
      hsigmaPathOnCycle newStored newEdges newKind newVertex newOutside newDelta newGamma
      appendedData appendedCertificate extendedSeries hextendedData hroundsEq castSeries
      castSeriesTree finalSeries rawPenultimate hrawPenultimate
  calc
    finalSeries.data.tree
          (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2)) =
        extendedSeries.data.tree rawPenultimate := by
          exact castSeriesTree hroundsEq extendedSeries _
    _ = appendedData.tree rawPenultimate := by
          rw [hextendedData]
    _ = corr.replacementSeries.data.tree
          replacementLast.succ := by
          rw [hrawPenultimate]
          simp only [appendedData,
            TashkinovSeriesDataAppend]
          exact Fin.lastCases_castSucc replacementLast.succ
    _ = ett.series.data.tree
          (Fin.last ett.rounds).castSucc :=
      hreplacementCurrentTree

theorem helper_hseriesDataAgree_6220.{u_1, u_2} :
    storedDataAgreementStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hpositive sigma _ closureTree q hqSucc hqCast
      available currentStored currentEdges currentKind hroundLarge originalPrefix hr hprefixData
      corr earlierPrefixBound earlierPrefix hearlierMap hearlierPositive hreplacementEarlierKind
      oldi oldChoice oldGamma holdTarget newi newChoice _ newCurrentDelta newCurrentGamma hnewIndex
      htree oldChoiceOnNew holdColorCast holdColorNe hnewColorNe hidentifiedDelta hidentifiedGamma
      holdDeltaAvailable holdGammaAvailable hnewDeltaAvailable hnewGammaAvailable replacementLast
      hreplacementLastMap hgammaDeltaNe sigmaReturnGraph returnEdgeTransfer sigmaReturnPath
      hsigmaReturnIsPath hsigmaReturnSupport hreturnInNewEarlier replacementCycle hcycleFull
      hreplacementCurrentTree havailableCurrentTree currentTree hreturnCycle houtsideCycle
      rootedCycle outsideIndices outsideIndicesNonempty firstOutside firstOutsideNotOne
      firstOutsideAtLeastTwo firstCrossingIndex beforeFirstCrossingIndex laterInsideIndices
      laterInsideNonempty firstReturn hreturnNotNext hreturnGap returnCrossingIndex
      beforeReturnCrossingIndex hreplacementColor castReturnWalk castReturnWalkIsPath
      castReturnWalkSupport castCycle castCycleSupport hsigmaPathOnCycle newStored newEdges newKind
      newVertex newOutside newDelta newGamma appendedData appendedCertificate extendedSeries
      hextendedData hroundsEq castSeries castSeriesStored castSeriesEdges castSeriesKind finalSeries
      rawDataIndex i
  by_cases hi : i.val < ett.rounds
  · let j : Fin (originalPrefix.rounds + 1) :=
      ⟨i.val, by rw [hroundsEq]; exact hi⟩
    have hraw : rawDataIndex i = j.castSucc := by
      apply Fin.ext
      rfl
    have hmap : Fin.castLE (by omega) j = i := by
      apply Fin.ext
      rfl
    constructor
    · calc
        finalSeries.data.stored i =
            extendedSeries.data.stored (rawDataIndex i) := by
              exact castSeriesStored hroundsEq extendedSeries i
        _ = appendedData.stored (rawDataIndex i) := by
              rw [hextendedData]
        _ = corr.replacementSeries.data.stored j := by
              rw [hraw]
              simp [appendedData, TashkinovSeriesDataAppend]
        _ = originalPrefix.series.data.stored j :=
              corr.storedColorsAgree j
        _ = ett.series.data.stored (Fin.castLE (by omega) j) :=
              (hprefixData j).2.1
        _ = ett.series.data.stored i := by rw [hmap]
    · constructor
      · calc
          finalSeries.data.connectingEdges i =
              extendedSeries.data.connectingEdges
                (rawDataIndex i) := by
                  exact castSeriesEdges hroundsEq
                    extendedSeries i
          _ = appendedData.connectingEdges
                (rawDataIndex i) := by rw [hextendedData]
          _ = corr.replacementSeries.data.connectingEdges j := by
                rw [hraw]
                simp [appendedData,
                  TashkinovSeriesDataAppend]
          _ = originalPrefix.series.data.connectingEdges j :=
                corr.connectingEdgesAgree j
          _ = ett.series.data.connectingEdges
                (Fin.castLE (by omega) j) :=
                (hprefixData j).2.2.1
          _ = ett.series.data.connectingEdges i := by rw [hmap]
      · calc
          finalSeries.data.kind i =
              extendedSeries.data.kind (rawDataIndex i) := by
                exact castSeriesKind hroundsEq extendedSeries i
          _ = appendedData.kind (rawDataIndex i) := by
                rw [hextendedData]
          _ = corr.replacementSeries.data.kind j := by
                rw [hraw]
                simp [appendedData,
                  TashkinovSeriesDataAppend]
          _ = originalPrefix.series.data.kind j :=
                corr.extensionKindsAgree j
          _ = ett.series.data.kind
                (Fin.castLE (by omega) j) :=
                (hprefixData j).2.2.2.1
          _ = ett.series.data.kind i := by rw [hmap]
  · have hilast : i = Fin.last ett.rounds := by
      apply Fin.ext
      simp
      omega
    subst i
    have hraw : rawDataIndex (Fin.last ett.rounds) =
        Fin.last (originalPrefix.rounds + 1) := by
      apply Fin.ext
      simp [rawDataIndex]
    constructor
    · calc
        finalSeries.data.stored (Fin.last ett.rounds) =
            extendedSeries.data.stored
              (rawDataIndex (Fin.last ett.rounds)) := by
              exact castSeriesStored hroundsEq extendedSeries _
        _ = appendedData.stored
              (rawDataIndex (Fin.last ett.rounds)) := by
              rw [hextendedData]
        _ = newStored := by
              rw [hraw]
              simp [appendedData, TashkinovSeriesDataAppend]
        _ = {available.delta, available.gamma} := rfl
        _ = ett.series.data.stored (Fin.last ett.rounds) := by
              rw [← hqSucc]
              exact currentStored.symm
    · constructor
      · calc
          finalSeries.data.connectingEdges
                (Fin.last ett.rounds) =
              extendedSeries.data.connectingEdges
                (rawDataIndex (Fin.last ett.rounds)) := by
                  exact castSeriesEdges hroundsEq
                    extendedSeries _
          _ = appendedData.connectingEdges
                (rawDataIndex (Fin.last ett.rounds)) := by
                  rw [hextendedData]
          _ = newEdges := by
                  rw [hraw]
                  simp [appendedData,
                    TashkinovSeriesDataAppend]
          _ = {available.edge} := rfl
          _ = ett.series.data.connectingEdges
                (Fin.last ett.rounds) := by
                  rw [← hqSucc]
                  exact currentEdges.symm
      · calc
          finalSeries.data.kind (Fin.last ett.rounds) =
              extendedSeries.data.kind
                (rawDataIndex (Fin.last ett.rounds)) := by
                  exact castSeriesKind hroundsEq extendedSeries _
          _ = appendedData.kind
                (rawDataIndex (Fin.last ett.rounds)) := by
                  rw [hextendedData]
          _ = newKind := by
                  rw [hraw]
                  simp [appendedData,
                    TashkinovSeriesDataAppend]
          _ = some TashkinovExtensionKind.RE := rfl
          _ = ett.series.data.kind
                (Fin.last ett.rounds) := by
                  rw [← hqSucc]
                  exact currentKind.symm

theorem helper_hseriesTreeAgree_6351.{u_1, u_2} :
    treeAgreementStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hpositive sigma _ closureTree q hqCast
      available hroundLarge originalPrefix hr hprefixTrees hprefixData corr earlierPrefixBound
      earlierPrefix hearlierMap hearlierPositive hreplacementEarlierKind oldi oldChoice oldGamma
      holdTarget newi newChoice _ newCurrentDelta newCurrentGamma hnewIndex htree oldChoiceOnNew
      holdColorCast holdColorNe hnewColorNe hidentifiedDelta hidentifiedGamma holdDeltaAvailable
      holdGammaAvailable hnewDeltaAvailable hnewGammaAvailable replacementLast hreplacementLastMap
      hgammaDeltaNe sigmaReturnGraph returnEdgeTransfer sigmaReturnPath hsigmaReturnIsPath
      hsigmaReturnSupport hreturnInNewEarlier replacementCycle hcycleFull hreplacementCurrentTree
      havailableCurrentTree currentTree hreturnCycle houtsideCycle rootedCycle outsideIndices
      outsideIndicesNonempty firstOutside firstOutsideNotOne firstOutsideAtLeastTwo
      firstCrossingIndex beforeFirstCrossingIndex laterInsideIndices laterInsideNonempty firstReturn
      hreturnNotNext hreturnGap returnCrossingIndex beforeReturnCrossingIndex hreplacementColor
      castReturnWalk castReturnWalkIsPath castReturnWalkSupport castCycle castCycleSupport
      hsigmaPathOnCycle newStored newEdges newKind newVertex newOutside newDelta newGamma
      appendedData appendedCertificate extendedSeries hextendedData hroundsEq castSeries
      castSeriesTree finalSeries hfinalPenultimateTree rawTreeIndex i
  by_cases hi : i.val < originalPrefix.rounds
  · let j : Fin originalPrefix.rounds := ⟨i.val, hi⟩
    have hraw : rawTreeIndex i.succ.castSucc =
        j.succ.castSucc.castSucc := by
      apply Fin.ext
      rfl
    have hmap : Fin.castLE (by omega) j.succ.castSucc =
        i.succ.castSucc := by
      apply Fin.ext
      rfl
    calc
      finalSeries.data.tree i.succ.castSucc =
          extendedSeries.data.tree
            (rawTreeIndex i.succ.castSucc) := by
            exact castSeriesTree hroundsEq extendedSeries _
      _ = appendedData.tree
            (rawTreeIndex i.succ.castSucc) := by
            rw [hextendedData]
      _ = corr.replacementSeries.data.tree
            j.succ.castSucc := by
            rw [hraw]
            simp only [appendedData,
              TashkinovSeriesDataAppend]
            convert (Fin.lastCases_castSucc
              j.succ.castSucc) using 1;
      _ = originalPrefix.series.data.tree
            j.succ.castSucc := corr.ladderTreesAgree j
      _ = ett.series.data.tree
            (Fin.castLE (by omega) j.succ.castSucc) :=
            hprefixTrees j.succ.castSucc
      _ = ett.series.data.tree i.succ.castSucc := by rw [hmap]
  · let ilast : Fin ett.rounds :=
      ⟨ett.rounds - 1, by omega⟩
    have hilast : i = ilast := by
      apply Fin.ext
      have hiBound := i.isLt
      have hprefixRounds := hr
      simp [ilast]
      omega
    rw [hilast]
    have hindex :
        ilast.succ.castSucc =
          (Fin.last ett.rounds).castSucc := by
      apply Fin.ext
      simp [ilast]
      omega
    rw [hindex]
    exact hfinalPenultimateTree

private theorem revisitingSeriesAgreement.{u_1, u_2} : revisitingSeriesAgreementStatement.{u_1, u_2}
    := by
  classical
  intro «V» «E» «inst» «inst_1» «inst_2» «inst_3» «G» «k» «e0» «input» «T» «generating» «ett»
      «hpositive» «hlower» «sigma» «hsigmaProper» «hsigmaOne» «hsigmaStable» «Tstar» «hTnTstar»
      «hstrict» «fstar» «seed» «hfinalEdges» «hadjoin» «closureTree» «hseedClosure» «hTstarClosure»
      «hTnClosure» «q» «hqSucc» «hqCast» «adjoined» «previousProper» «previousOneUncolored»
      «previousClosed» «available» «currentStored» «currentEdges» «currentKind» «hroundLarge»
      «originalPrefix» «hr» «hprefixTrees» «hprefixData» «corr» «hcorrFinalTree» «hcorrFinalColor»
      «hcorrMP» «earlierPrefixBound» «earlierPrefix» «hearlierMap» «hearlierPositive»
      «hreplacementEarlierKind» «oldi» «oldChoice» «oldGamma» «holdTarget» «newi» «newChoice»
      «newGamma» «newCurrentDelta» «newCurrentGamma» «hnewIndex» «htree» «oldChoiceOnNew»
      «holdColorCast» «hends» «holdColorNe» «hnewColorNe» «hidentifiedDelta» «hidentifiedGamma»
      «holdDeltaAvailable» «holdGammaAvailable» «hnewDeltaAvailable» «hnewGammaAvailable»
      «replacementLast» «hreplacementLastMap» «hnewDeltaSigma» «hgammaDeltaNe» «hnewVertexTn»
      «hpathComponent» «hpathMeetsTn» «hsigmaPrevStableQ» «sigmaReturnGraph» «returnEdgeTransfer»
      «sigmaReturnPath» «hsigmaReturnIsPath» «hsigmaReturnSupport» «hreturnInQ» «houtsideInQ»
      «hreturnInNewEarlier» «hreturnInTn» «hcomponentDistinct» «hQMeetsTn» «hcorrRoundsPositive»
      «hcorrRoundsLess» «correspondingTerminalTree» «hseriesTree» «hlowerColor» «hstableLower»
      «hlowerTree» «hdeltaLower» «hlowerPackage» «hinterchangeLower» «hinterchangeTn»
      «replacementCycle» «hcycleFull» «hclosedSigma» «hclosedFinal» «hreplacementCurrentTree»
      «havailableCurrentIndex» «havailableCurrentTree» «currentTree» «hreturnCycle» «houtsideCycle»
      «hreturnCurrent» «houtsideNotCurrent» «rootedCycle» «rootedIsCycle» «houtsideRooted»
      «outsideIndices» «outsideIndicesNonempty» «firstOutside» «outsideOne» «houtsideOneAt»
      «houtsideOneNot» «beforeFirstOutside» «firstOutsidePositive» «firstOutsideLt»
      «firstOutsideNotOne» «firstOutsideAtLeastTwo» «firstCrossingAdj» «firstCrossingIndex»
      «firstEdge» «hfirstEdgeAt» «hfirstOutsideIncident» «hfirstEdgeActive» «beforeFirstCrossingAdj»
      «beforeFirstCrossingIndex» «insideOne» «hinsideOneAt» «hinsideOneCurrent» «hinsideOneIncident»
      «endpointIdentity» «hinsideOutsideOne» «hfirstEnds» «hfirstBoundary» «laterInsideIndices»
      «laterInsideNonempty» «firstReturn» «hfirstReturnMem» «hfirstReturnAfter» «insideTwo»
      «hinsideTwoAt» «hinsideTwoCurrent» «hreturnNotNext» «hreturnGap» «returnCrossingAdj»
      «returnCrossingIndex» «secondEdge» «hsecondEdgeAt» «hinsideTwoIncident» «hsecondEdgeActive»
      «beforeReturnCrossingAdj» «beforeReturnCrossingIndex» «outsideTwo» «houtsideTwoAt»
      «houtsideTwoNot» «houtsideTwoIncident» «houtsideInsideTwo» «hsecondEnds» «hsecondBoundary»
      «hcrossingEdgesNe» «hnewVertexCurrent» «hfirstGamma» «hsecondGamma» «hnotStrongSigma»
      «hreplacementColor» «castReturnWalk» «castReturnWalkIsPath» «castReturnWalkSupport»
      «castCycle» «castCycleSupport» «replacementCycleForPrefix» «replacementReturnPath»
      «hsigmaPathInQ» «hsigmaPathOnCycle» «replacementCertificate» «hfstar» «newStored» «newEdges»
      «newKind» «newVertex» «newOutside» «newDelta» «newGamma» «appendedData» «appendedCertificate»
      «happGamma» «happDelta» «happEdge» «happInside» «happOutside» «hstrictClosure» «lastStep»
      «extendedSeries» «hextendedData» «hroundsEq» «castSeries» «castSeriesTree»
      «castSeriesColoring» «castSeriesStored» «castSeriesEdges» «castSeriesKind» «finalSeries»
      «rawPenultimate» «hrawPenultimate» «hfinalPenultimateTree» «rawFinalTree» «hrawFinalTree»
      «hfinalTree» «rawFinalColor» «hrawFinalColor» «hfinalColor» «rawDataIndex» «hseriesDataAgree»
      «rawTreeIndex»
  let rawTreeIndex (i : Fin (ett.rounds + 2)) :
      Fin (originalPrefix.rounds + 3) :=
    Fin.cast
      (congrArg (fun m : ℕ => m + 2) hroundsEq.symm) i
  have hseriesTreeAgree : ∀ i : Fin ett.rounds,
      finalSeries.data.tree i.succ.castSucc =
        ett.series.data.tree i.succ.castSucc := by
    exact @helper_hseriesTreeAgree_6351 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma)
        (@Tstar) (@closureTree) (@hqCast) (@available) (@hroundLarge) (@originalPrefix) (@hr)
        (@hprefixTrees) (@hprefixData) (@corr) (@earlierPrefixBound) (@hearlierMap)
        (@hearlierPositive) (@hreplacementEarlierKind) (@oldi) (@oldChoice) (@oldGamma)
        (@holdTarget) (@newi) (@newChoice) _ (@newCurrentDelta) (@newCurrentGamma) (@hnewIndex)
        (@htree) (@holdColorCast) (@holdColorNe) (@hnewColorNe) (@hidentifiedDelta)
        (@hidentifiedGamma) (@holdDeltaAvailable) (@holdGammaAvailable) (@hnewDeltaAvailable)
        (@hnewGammaAvailable) (@hreplacementLastMap) (@hgammaDeltaNe) (@returnEdgeTransfer)
        (@hsigmaReturnIsPath) (@hsigmaReturnSupport) (@hreturnInNewEarlier) (@replacementCycle)
        (@hcycleFull) (@hreplacementCurrentTree) (@havailableCurrentTree) (@hreturnCycle)
        (@houtsideCycle) (@outsideIndicesNonempty) (@firstOutsideNotOne) (@firstOutsideAtLeastTwo)
        (@firstCrossingIndex) (@beforeFirstCrossingIndex) (@laterInsideNonempty) (@hreturnNotNext)
        (@hreturnGap) (@returnCrossingIndex) (@beforeReturnCrossingIndex) (@hreplacementColor)
        (@castReturnWalkIsPath) (@castReturnWalkSupport) (@castCycleSupport) (@hsigmaPathOnCycle)
        (@appendedCertificate) (@extendedSeries) (@hextendedData) (@hroundsEq) (@castSeriesTree)
        (@hfinalPenultimateTree)
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
      corr.replacementInput Tstar sigma := {
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

private theorem revisitingFinalSeries.{u_1, u_2} : revisitingFinalSeriesStatement.{u_1, u_2} := by
  classical
  intro V E inst inst_1 inst_2 inst_3 G k e0 input T generating ett hpositive hlower sigma
    hsigmaProper hsigmaOne hsigmaStable Tstar hTnTstar hstrict fstar seed hfinalEdges hadjoin
    closureTree hseedClosure hTstarClosure hTnClosure q hqSucc hqCast adjoined previousProper
    previousOneUncolored previousClosed available currentStored currentEdges currentKind hroundLarge
    originalPrefix hr hprefixTrees hprefixData corr hcorrFinalTree hcorrFinalColor hcorrMP
    earlierPrefixBound earlierPrefix hearlierMap hearlierPositive hreplacementEarlierKind oldi
    oldChoice oldGamma holdTarget newi newChoice newGamma newCurrentDelta newCurrentGamma hnewIndex
    htree oldChoiceOnNew holdColorCast hends holdColorNe hnewColorNe hidentifiedDelta
    hidentifiedGamma holdDeltaAvailable holdGammaAvailable hnewDeltaAvailable hnewGammaAvailable
    replacementLast hreplacementLastMap hnewDeltaSigma hgammaDeltaNe hnewVertexTn hpathComponent
    hpathMeetsTn hsigmaPrevStableQ sigmaReturnGraph returnEdgeTransfer sigmaReturnPath
    hsigmaReturnIsPath hsigmaReturnSupport hreturnInQ houtsideInQ hreturnInNewEarlier hreturnInTn
    hcomponentDistinct hQMeetsTn hcorrRoundsPositive hcorrRoundsLess correspondingTerminalTree
    hseriesTree hlowerColor hstableLower hlowerTree hdeltaLower hlowerPackage hinterchangeLower
    hinterchangeTn replacementCycle hcycleFull hclosedSigma hclosedFinal hreplacementCurrentTree
    havailableCurrentIndex havailableCurrentTree currentTree hreturnCycle houtsideCycle
    hreturnCurrent houtsideNotCurrent rootedCycle rootedIsCycle houtsideRooted outsideIndices
    outsideIndicesNonempty firstOutside outsideOne houtsideOneAt houtsideOneNot beforeFirstOutside
    firstOutsidePositive firstOutsideLt firstOutsideNotOne firstOutsideAtLeastTwo firstCrossingAdj
    firstCrossingIndex firstEdge hfirstEdgeAt hfirstOutsideIncident hfirstEdgeActive
    beforeFirstCrossingAdj beforeFirstCrossingIndex insideOne hinsideOneAt hinsideOneCurrent
    hinsideOneIncident endpointIdentity hinsideOutsideOne hfirstEnds hfirstBoundary
    laterInsideIndices laterInsideNonempty firstReturn hfirstReturnMem hfirstReturnAfter insideTwo
    hinsideTwoAt hinsideTwoCurrent hreturnNotNext hreturnGap returnCrossingAdj returnCrossingIndex
    secondEdge hsecondEdgeAt hinsideTwoIncident hsecondEdgeActive beforeReturnCrossingAdj
    beforeReturnCrossingIndex outsideTwo houtsideTwoAt houtsideTwoNot houtsideTwoIncident
    houtsideInsideTwo hsecondEnds hsecondBoundary hcrossingEdgesNe hnewVertexCurrent hfirstGamma
    hsecondGamma hnotStrongSigma hreplacementColor castReturnWalk castReturnWalkIsPath
    castReturnWalkSupport castCycle castCycleSupport replacementCycleForPrefix replacementReturnPath
    hsigmaPathInQ hsigmaPathOnCycle replacementCertificate hfstar newStored newEdges newKind
    newVertex newOutside newDelta newGamma appendedData appendedCertificate happGamma happDelta
    happEdge happInside happOutside hstrictClosure lastStep extendedSeries hextendedData
  have hroundsEq : originalPrefix.rounds + 1 = ett.rounds := by
    rw [hr]
    omega
  let castSeries {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 corr.replacementInput) :
    TashkinovSeries G k b e0 corr.replacementInput := by
    subst b
    exact S
  have castSeriesTree :
    ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 corr.replacementInput) (i : Fin (b + 2)),
      (castSeries h S).data.tree i =
        S.data.tree (Fin.cast (congrArg (fun m : ℕ => m + 2) h.symm) i) := by
    intro a b h S i
    subst b
    rfl
  have castSeriesColoring :
    ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 corr.replacementInput) (i : Fin (b + 1)),
      (castSeries h S).data.coloring i =
        S.data.coloring (Fin.cast (congrArg (fun m : ℕ => m + 1) h.symm) i) := by
    intro a b h S i
    subst b
    rfl
  have castSeriesStored :
    ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 corr.replacementInput) (i : Fin (b + 1)),
      (castSeries h S).data.stored i =
        S.data.stored (Fin.cast (congrArg (fun m : ℕ => m + 1) h.symm) i) := by
    intro a b h S i
    subst b
    rfl
  have castSeriesEdges :
    ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 corr.replacementInput) (i : Fin (b + 1)),
      (castSeries h S).data.connectingEdges i =
        S.data.connectingEdges (Fin.cast (congrArg (fun m : ℕ => m + 1) h.symm) i) := by
    intro a b h S i
    subst b
    rfl
  have castSeriesKind :
    ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 corr.replacementInput) (i : Fin (b + 1)),
      (castSeries h S).data.kind i =
        S.data.kind (Fin.cast (congrArg (fun m : ℕ => m + 1) h.symm) i) := by
    intro a b h S i
    subst b
    rfl
  let finalSeries : TashkinovSeries G k ett.rounds e0 corr.replacementInput :=
    castSeries hroundsEq extendedSeries
  let rawPenultimate : Fin (originalPrefix.rounds + 3) :=
    Fin.cast (congrArg (fun m : ℕ => m + 2) hroundsEq.symm)
      (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2))
  have hrawPenultimate : rawPenultimate = replacementLast.succ.castSucc := by
    apply Fin.ext
    simp [rawPenultimate, replacementLast]
    omega
  have hfinalPenultimateTree :
    finalSeries.data.tree (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2)) =
      ett.series.data.tree (Fin.last ett.rounds).castSucc := by
    exact
      @helper_hfinalPenultimateTree_6172 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma)
        (@Tstar) (@closureTree) (@hqCast) (@available) (@hroundLarge) (@originalPrefix) (@hr)
        (@hprefixData) (@corr) (@earlierPrefixBound) (@hearlierMap) (@hearlierPositive)
        (@hreplacementEarlierKind) (@oldi) (@oldChoice) (@oldGamma) (@holdTarget) (@newi)
        (@newChoice) _ (@newCurrentDelta) (@newCurrentGamma) (@hnewIndex) (@htree) (@holdColorCast)
        (@holdColorNe) (@hnewColorNe) (@hidentifiedDelta) (@hidentifiedGamma) (@holdDeltaAvailable)
        (@holdGammaAvailable) (@hnewDeltaAvailable) (@hnewGammaAvailable) (@hreplacementLastMap)
        (@hgammaDeltaNe) (@returnEdgeTransfer) (@hsigmaReturnIsPath) (@hsigmaReturnSupport)
        (@hreturnInNewEarlier) (@replacementCycle) (@hcycleFull) (@hreplacementCurrentTree)
        (@havailableCurrentTree) (@hreturnCycle) (@houtsideCycle) (@outsideIndicesNonempty)
        (@firstOutsideNotOne) (@firstOutsideAtLeastTwo) (@firstCrossingIndex)
        (@beforeFirstCrossingIndex) (@laterInsideNonempty) (@hreturnNotNext) (@hreturnGap)
        (@returnCrossingIndex) (@beforeReturnCrossingIndex) (@hreplacementColor)
        (@castReturnWalkIsPath) (@castReturnWalkSupport) (@castCycleSupport) (@hsigmaPathOnCycle)
        (@appendedCertificate) (@extendedSeries) (@hextendedData) (@hroundsEq) (@castSeriesTree)
        (@hrawPenultimate)
  let rawFinalTree : Fin (originalPrefix.rounds + 3) :=
    Fin.cast (congrArg (fun m : ℕ => m + 2) hroundsEq.symm) (Fin.last (ett.rounds + 1))
  have hrawFinalTree : rawFinalTree = Fin.last (originalPrefix.rounds + 2) := by
    apply Fin.ext
    simp [rawFinalTree]
  have hfinalTree :=
    helper_hfinalTree_2464 (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma)
      (@Tstar) (@closureTree) (@available) (@originalPrefix) (@corr) (@extendedSeries)
      (@hextendedData) (@hroundsEq) (@castSeriesTree) (@hrawFinalTree)
  let rawFinalColor : Fin (originalPrefix.rounds + 2) :=
    Fin.cast (congrArg (fun m : ℕ => m + 1) hroundsEq.symm) (Fin.last ett.rounds)
  have hrawFinalColor : rawFinalColor = Fin.last (originalPrefix.rounds + 1) := by
    apply Fin.ext
    simp [rawFinalColor]
  have hfinalColor :=
    helper_hfinalColor_2482 (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma)
      (@Tstar) (@closureTree) (@available) (@originalPrefix) (@corr) (@extendedSeries)
      (@hextendedData) (@hroundsEq) (@castSeriesColoring) (@hrawFinalColor)
  let rawDataIndex (i : Fin (ett.rounds + 1)) : Fin (originalPrefix.rounds + 2) :=
    Fin.cast (congrArg (fun m : ℕ => m + 1) hroundsEq.symm) i
  have hseriesDataAgree :
    ∀ i : Fin (ett.rounds + 1),
      finalSeries.data.stored i = ett.series.data.stored i ∧
        finalSeries.data.connectingEdges i = ett.series.data.connectingEdges i ∧
          finalSeries.data.kind i = ett.series.data.kind i := by
    exact
      @helper_hseriesDataAgree_6220 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma)
        (@Tstar) (@closureTree) (@hqSucc) (@hqCast) (@available) (@currentStored) (@currentEdges)
        (@currentKind) (@hroundLarge) (@originalPrefix) (@hr) (@hprefixData) (@corr)
        (@earlierPrefixBound) (@hearlierMap) (@hearlierPositive) (@hreplacementEarlierKind) (@oldi)
        (@oldChoice) (@oldGamma) (@holdTarget) (@newi) (@newChoice) _ (@newCurrentDelta)
        (@newCurrentGamma) (@hnewIndex) (@htree) (@holdColorCast) (@holdColorNe) (@hnewColorNe)
        (@hidentifiedDelta) (@hidentifiedGamma) (@holdDeltaAvailable) (@holdGammaAvailable)
        (@hnewDeltaAvailable) (@hnewGammaAvailable) (@hreplacementLastMap) (@hgammaDeltaNe)
        (@returnEdgeTransfer) (@hsigmaReturnIsPath) (@hsigmaReturnSupport) (@hreturnInNewEarlier)
        (@replacementCycle) (@hcycleFull) (@hreplacementCurrentTree) (@havailableCurrentTree)
        (@hreturnCycle) (@houtsideCycle) (@outsideIndicesNonempty) (@firstOutsideNotOne)
        (@firstOutsideAtLeastTwo) (@firstCrossingIndex) (@beforeFirstCrossingIndex)
        (@laterInsideNonempty) (@hreturnNotNext) (@hreturnGap) (@returnCrossingIndex)
        (@beforeReturnCrossingIndex) (@hreplacementColor) (@castReturnWalkIsPath)
        (@castReturnWalkSupport) (@castCycleSupport) (@hsigmaPathOnCycle) (@appendedCertificate)
        (@extendedSeries) (@hextendedData) (@hroundsEq) (@castSeriesStored) (@castSeriesEdges)
        (@castSeriesKind)
  exact
    @revisitingSeriesAgreement (@V) (@E) inferInstance inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@hlower) (@sigma)
      (@hsigmaProper) (@hsigmaOne) (@hsigmaStable) (@Tstar) (@hTnTstar) (@hstrict) (@fstar) (@seed)
      (@hfinalEdges) (@hadjoin) (@closureTree) (@hseedClosure) (@hTstarClosure) (@hTnClosure)
      (@hqSucc) (@hqCast) (@adjoined) (@previousProper) (@previousOneUncolored) (@previousClosed)
      (@available) (@currentStored) (@currentEdges) (@currentKind) (@hroundLarge) (@originalPrefix)
      (@hr) (@hprefixTrees) (@hprefixData) (@corr) (@hcorrFinalTree) (@hcorrFinalColor) (@hcorrMP)
      (@earlierPrefixBound) (@hearlierMap) (@hearlierPositive) (@hreplacementEarlierKind) (@oldi)
      (@oldChoice) (@oldGamma) (@holdTarget) (@newi) (@newChoice) (by assumption) (@newCurrentDelta)
      (@newCurrentGamma) (@hnewIndex) (@htree) (@holdColorCast) (@hends) (@holdColorNe)
      (@hnewColorNe) (@hidentifiedDelta) (@hidentifiedGamma) (@holdDeltaAvailable)
      (@holdGammaAvailable) (@hnewDeltaAvailable) (@hnewGammaAvailable) (@hreplacementLastMap)
      (@hnewDeltaSigma) (@hgammaDeltaNe) (@hnewVertexTn) (@hpathComponent) (@hpathMeetsTn)
      (@hsigmaPrevStableQ) (@returnEdgeTransfer) (@hsigmaReturnIsPath) (@hsigmaReturnSupport)
      (@hreturnInQ) (@houtsideInQ) (@hreturnInNewEarlier) (@hreturnInTn) (@hcomponentDistinct)
      (@hQMeetsTn) (@hcorrRoundsPositive) (@hcorrRoundsLess) (@correspondingTerminalTree)
      (@hseriesTree) (@hlowerColor) (@hstableLower) (@hlowerTree) (@hdeltaLower) (@hlowerPackage)
      (@hinterchangeLower) (@hinterchangeTn) (@replacementCycle) (@hcycleFull) (@hclosedSigma)
      (@hclosedFinal) (@hreplacementCurrentTree) (@havailableCurrentIndex) (@havailableCurrentTree)
      (@hreturnCycle) (@houtsideCycle) (@hreturnCurrent) (@houtsideNotCurrent) (@rootedIsCycle)
      (@houtsideRooted) (@outsideIndicesNonempty) (@outsideOne) (@houtsideOneAt) (@houtsideOneNot)
      (@beforeFirstOutside) (@firstOutsidePositive) (@firstOutsideLt) (@firstOutsideNotOne)
      (@firstOutsideAtLeastTwo) (@firstCrossingAdj) (@firstCrossingIndex) (@firstEdge)
      (@hfirstEdgeAt) (@hfirstOutsideIncident) (@hfirstEdgeActive) (@beforeFirstCrossingAdj)
      (@beforeFirstCrossingIndex) (@insideOne) (@hinsideOneAt) (@hinsideOneCurrent)
      (@hinsideOneIncident) (@endpointIdentity) (@hinsideOutsideOne) (@hfirstEnds) (@hfirstBoundary)
      (@laterInsideNonempty) (@hfirstReturnMem) (@hfirstReturnAfter) (@insideTwo) (@hinsideTwoAt)
      (@hinsideTwoCurrent) (@hreturnNotNext) (@hreturnGap) (@returnCrossingAdj)
      (@returnCrossingIndex) (@secondEdge) (@hsecondEdgeAt) (@hinsideTwoIncident)
      (@hsecondEdgeActive) (@beforeReturnCrossingAdj) (@beforeReturnCrossingIndex) (@outsideTwo)
      (@houtsideTwoAt) (@houtsideTwoNot) (@houtsideTwoIncident) (@houtsideInsideTwo) (@hsecondEnds)
      (@hsecondBoundary) (@hcrossingEdgesNe) (@hnewVertexCurrent) (@hfirstGamma) (@hsecondGamma)
      (@hnotStrongSigma) (@hreplacementColor) (@castReturnWalkIsPath) (@castReturnWalkSupport)
      (@castCycleSupport) (@hsigmaPathInQ) (@hsigmaPathOnCycle) (@hfstar) (@appendedCertificate)
      (@happGamma) (@happDelta) (@happEdge) (@happInside) (@happOutside) (@hstrictClosure)
      (@lastStep) (@extendedSeries) (@hextendedData) (@hroundsEq) (@castSeriesTree)
      (@castSeriesColoring) (@castSeriesStored) (@castSeriesEdges) (@castSeriesKind)
      (@hrawPenultimate) (@hfinalPenultimateTree) (@hrawFinalTree) (@hfinalTree) (@hrawFinalColor)
      (@hfinalColor) (@hseriesDataAgree)

private theorem revisitingCertificateTransport.{u_1, u_2} :
    revisitingCertificateTransportStatement.{u_1, u_2} := by
  classical
  intro V E inst inst_1 inst_2 inst_3 G k e0 input T generating ett hpositive hlower sigma
    hsigmaProper hsigmaOne hsigmaStable Tstar hTnTstar hstrict fstar seed hfinalEdges hadjoin
    closureTree hseedClosure hTstarClosure hTnClosure q hqSucc hqCast adjoined previousProper
    previousOneUncolored previousClosed available currentStored currentEdges currentKind hroundLarge
    originalPrefix hr hprefixTrees hprefixData corr hcorrFinalTree hcorrFinalColor hcorrMP
    earlierPrefixBound earlierPrefix hearlierMap hearlierPositive hreplacementEarlierKind oldi
    oldChoice oldGamma holdTarget newi newChoice newGamma newCurrentDelta newCurrentGamma hnewIndex
    htree oldChoiceOnNew holdColorCast hends holdColorNe hnewColorNe hidentifiedDelta
    hidentifiedGamma holdDeltaAvailable holdGammaAvailable hnewDeltaAvailable hnewGammaAvailable
    replacementLast hreplacementLastMap hnewDeltaSigma hgammaDeltaNe hnewVertexTn hpathComponent
    hpathMeetsTn hsigmaPrevStableQ sigmaReturnGraph returnEdgeTransfer sigmaReturnPath
    hsigmaReturnIsPath hsigmaReturnSupport hreturnInQ houtsideInQ hreturnInNewEarlier hreturnInTn
    hcomponentDistinct hQMeetsTn hcorrRoundsPositive hcorrRoundsLess correspondingTerminalTree
    hseriesTree hlowerColor hstableLower hlowerTree hdeltaLower hlowerPackage hinterchangeLower
    hinterchangeTn replacementCycle hcycleFull hclosedSigma hclosedFinal hreplacementCurrentTree
    havailableCurrentIndex havailableCurrentTree currentTree hreturnCycle houtsideCycle
    hreturnCurrent houtsideNotCurrent rootedCycle rootedIsCycle houtsideRooted outsideIndices
    outsideIndicesNonempty firstOutside outsideOne houtsideOneAt houtsideOneNot beforeFirstOutside
    firstOutsidePositive firstOutsideLt firstOutsideNotOne firstOutsideAtLeastTwo firstCrossingAdj
    firstCrossingIndex firstEdge hfirstEdgeAt hfirstOutsideIncident hfirstEdgeActive
    beforeFirstCrossingAdj beforeFirstCrossingIndex insideOne hinsideOneAt hinsideOneCurrent
    hinsideOneIncident endpointIdentity hinsideOutsideOne hfirstEnds hfirstBoundary
    laterInsideIndices laterInsideNonempty firstReturn hfirstReturnMem hfirstReturnAfter insideTwo
    hinsideTwoAt hinsideTwoCurrent hreturnNotNext hreturnGap returnCrossingAdj returnCrossingIndex
    secondEdge hsecondEdgeAt hinsideTwoIncident hsecondEdgeActive beforeReturnCrossingAdj
    beforeReturnCrossingIndex outsideTwo houtsideTwoAt houtsideTwoNot houtsideTwoIncident
    houtsideInsideTwo hsecondEnds hsecondBoundary hcrossingEdgesNe hnewVertexCurrent hfirstGamma
    hsecondGamma hnotStrongSigma hreplacementColor castReturnWalk castReturnWalkIsPath
    castReturnWalkSupport castCycle
  have castCycleSupport :
    ∀ (phi psi : PartialEdgeColoring E k) (hphi : phi = psi)
      (C : TwoColorCycle G psi available.gamma available.delta) z,
      z ∈ (castCycle phi psi hphi C).walk.support ↔ z ∈ C.walk.support := by
    intro phi psi hphi C z
    subst psi
    rfl
  let replacementCycleForPrefix :=
    castCycle (corr.replacementSeries.data.coloring replacementLast) sigma hreplacementColor
      replacementCycle
  let replacementReturnPath :=
    castReturnWalk (corr.replacementSeries.data.coloring replacementLast) sigma hreplacementColor
      sigmaReturnPath
  have hsigmaPathInQ :=
    helper_hsigmaPathInQ_2135 (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive)
      (@sigma) (@Tstar) (@available) (@returnEdgeTransfer)
  have hsigmaPathOnCycle : ∀ z, z ∈ sigmaReturnPath.support → z ∈ replacementCycle.walk.support :=
    by
    intro z hz
    exact (hcycleFull z).2 (hsigmaPathInQ z hz)
  let replacementCertificate :
    RevisitingExtensionCertificate corr.replacementSeries.data replacementLast :=
    { earlier := earlierPrefix
      earlierPositive := hearlierPositive
      earlierAtMost := Nat.le_of_lt_succ earlierPrefix.isLt, earlierPE := hreplacementEarlierKind
      interveningRevisiting := by
        exact
          @helper_interveningRevisiting_4368 (@V) (@E) inferInstance inferInstance inferInstance
            inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma)
            (@Tstar) (@hqCast) (@available) (@hroundLarge) (@originalPrefix) (@hr) (@hprefixData)
            (@corr) (@earlierPrefixBound) (@hearlierMap) (@oldi) (@oldChoice) (@oldGamma) (@newi)
            (@newChoice) (@newGamma) (@htree) (@holdColorCast) (@holdColorNe) (@hnewColorNe)
            (@hidentifiedDelta) (@hidentifiedGamma) (@holdDeltaAvailable) (@holdGammaAvailable)
            (@hreplacementLastMap) (@hgammaDeltaNe) (@replacementCycle) (@hreturnCycle)
            (@outsideIndicesNonempty) (@firstOutsideNotOne) (@firstOutsideAtLeastTwo)
            (@firstCrossingIndex) (@beforeFirstCrossingIndex) (@laterInsideNonempty)
            (@hreturnNotNext) (@hreturnGap) (@returnCrossingIndex) (@beforeReturnCrossingIndex)
      gamma := available.gamma
      delta := available.delta
      earlierGamma := by rw [← hnewIndex, newCurrentGamma, hnewGammaAvailable]
      earlierDelta := by rw [← hnewIndex, newCurrentDelta, hnewDeltaAvailable]
      cycle := replacementCycleForPrefix
      meetsEarlier := by
        refine ⟨available.returnVertex, hreturnInNewEarlier, ?_⟩
        exact (castCycleSupport _ _ hreplacementColor replacementCycle _).2 hreturnCycle
      leavesCurrent := by
        exact
          @helper_leavesCurrent_4395 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
            (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@Tstar) (@available)
            (@hroundLarge) (@originalPrefix) (@corr) (@replacementCycle) (@hreplacementCurrentTree)
            (@havailableCurrentTree) (@houtsideCycle) (@hreplacementColor) (@castCycleSupport)
      edge := available.edge
      edgeOnCycle :=
        (castCycleSupport _ _ hreplacementColor replacementCycle _).2 ((hcycleFull _).2 rfl)
      edgeBoundary := by
        rw [hreplacementCurrentTree, ← havailableCurrentTree]
        exact available.edgeBoundary
      insideEndpoint := available.insideEndpoint
      outsideEndpoint := available.outsideEndpoint
      insideInCurrent := by
        rw [hreplacementCurrentTree, ← havailableCurrentTree]
        exact available.insideInCurrent
      outsideNotCurrent := by
        rw [hreplacementCurrentTree, ← havailableCurrentTree]
        exact available.outsideNotCurrent
      edgeEnds := available.edgeEnds
      returnVertex := available.returnVertex
      returnInEarlier := hreturnInNewEarlier
      returnPath := replacementReturnPath
      returnPathIsPath :=
        castReturnWalkIsPath _ _ hreplacementColor sigmaReturnPath hsigmaReturnIsPath
      returnPathOnCycle := by
        exact
          @helper_returnPathOnCycle_4421 (@V) (@E) inferInstance inferInstance inferInstance (@G)
            (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@Tstar)
            (@available) (@hroundLarge) (@originalPrefix) (@corr) (@returnEdgeTransfer)
            (@replacementCycle) (@hreplacementColor) (@castReturnWalkSupport) (@castCycleSupport)
            (@hsigmaPathOnCycle)
      returnPathInternal := by
        exact
          @helper_returnPathInternal_4428 (@V) (@E) inferInstance inferInstance inferInstance (@G)
            (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@Tstar)
            (@available) (@hroundLarge) (@originalPrefix) (@corr) (@returnEdgeTransfer)
            (@hsigmaReturnSupport) (@hreplacementCurrentTree) (@havailableCurrentTree)
            (@hreplacementColor) (@castReturnWalkSupport) }
  have hfstar :=
    helper_hfstar_2233 (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@Tstar)
      (@fstar) (@hfinalEdges) (@hqSucc) (@available) (@currentEdges)
  let newStored : Finset (Fin k) := { available.delta, available.gamma }
  let newEdges : Finset E := { available.edge }
  let newKind : Option TashkinovExtensionKind := some TashkinovExtensionKind.RE
  let newVertex : Option V := some available.insideEndpoint
  let newOutside : Option V := some available.outsideEndpoint
  let newDelta : Option (Fin k) := some available.delta
  let newGamma : Option (Fin k) := some available.gamma
  let appendedData :=
    TashkinovSeriesDataAppend corr.replacementSeries.data closureTree sigma newStored newEdges
      newKind newVertex newOutside newDelta newGamma
  obtain ⟨appendedCertificate, happGamma, happDelta, happEdge, happInside, happOutside⟩ :=
    (RevisitingExtensionCertificateAppend corr.replacementSeries.data closureTree sigma newStored
          newEdges newKind newVertex newOutside newDelta newGamma replacementLast).2
      replacementCertificate
  have hstrictClosure :
    (ett.series.data.tree (Fin.last ett.rounds).castSucc).length < closureTree.length :=
    lt_of_lt_of_le hstrict hTstarClosure.1
  have lastStep :
    TashkinovSeriesStep G k (originalPrefix.rounds + 1) e0 corr.replacementInput appendedData
      (Fin.last (originalPrefix.rounds + 1)) := by
    exact
      @helper_lastStep_6001 (@V) (@E) inferInstance inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@hsigmaProper)
        (@hsigmaOne) (@Tstar) (@fstar) (@seed) (@hadjoin) (@closureTree) (@hseedClosure)
        (@hTnClosure) (@hqSucc) (@hqCast) (@adjoined) (@previousProper) (@previousOneUncolored)
        (@previousClosed) (@available) (@hroundLarge) (@originalPrefix) (@hr) (@hprefixData) (@corr)
        (@hcorrFinalTree) (@earlierPrefixBound) (@hearlierMap) (@hearlierPositive)
        (@hreplacementEarlierKind) (@oldi) (@oldChoice) (@oldGamma) (@holdTarget) (@newi)
        (@newChoice) _ (@newCurrentDelta) (@newCurrentGamma) (@hnewIndex) (@htree) (@holdColorCast)
        (@hends) (@holdColorNe) (@hnewColorNe) (@hidentifiedDelta) (@hidentifiedGamma)
        (@holdDeltaAvailable) (@holdGammaAvailable) (@hnewDeltaAvailable) (@hnewGammaAvailable)
        (@hreplacementLastMap) (@hgammaDeltaNe) (@hsigmaPrevStableQ) (@returnEdgeTransfer)
        (@hsigmaReturnIsPath) (@hsigmaReturnSupport) (@hreturnInNewEarlier) (@replacementCycle)
        (@hcycleFull) (@hclosedFinal) (@hreplacementCurrentTree) (@havailableCurrentTree)
        (@hreturnCycle) (@houtsideCycle) (@outsideIndicesNonempty) (@firstOutsideNotOne)
        (@firstOutsideAtLeastTwo) (@firstCrossingIndex) (@beforeFirstCrossingIndex)
        (@laterInsideNonempty) (@hreturnNotNext) (@hreturnGap) (@returnCrossingIndex)
        (@beforeReturnCrossingIndex) (@hnotStrongSigma) (@hreplacementColor) (@castReturnWalkIsPath)
        (@castReturnWalkSupport) (@castCycleSupport) (@hsigmaPathOnCycle) (@hfstar)
        (@appendedCertificate) (@happGamma) (@happDelta) (@happEdge) (@happInside) (@happOutside)
        (@hstrictClosure)
  obtain ⟨extendedSeries, hextendedData⟩ :=
    TashkinovSeriesAppend G k originalPrefix.rounds e0 corr.replacementInput corr.replacementSeries
      closureTree sigma newStored newEdges newKind newVertex newOutside newDelta newGamma lastStep
  exact
    @revisitingFinalSeries (@V) (@E) inferInstance inferInstance inferInstance inferInstance (@G)
      (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@hlower) (@sigma) (@hsigmaProper)
      (@hsigmaOne) (@hsigmaStable) (@Tstar) (@hTnTstar) (@hstrict) (@fstar) (@seed) (@hfinalEdges)
      (@hadjoin) (@closureTree) (@hseedClosure) (@hTstarClosure) (@hTnClosure) (@hqSucc) (@hqCast)
      (@adjoined) (@previousProper) (@previousOneUncolored) (@previousClosed) (@available)
      (@currentStored) (@currentEdges) (@currentKind) (@hroundLarge) (@originalPrefix) (@hr)
      (@hprefixTrees) (@hprefixData) (@corr) (@hcorrFinalTree) (@hcorrFinalColor) (@hcorrMP)
      (@earlierPrefixBound) (@hearlierMap) (@hearlierPositive) (@hreplacementEarlierKind) (@oldi)
      (@oldChoice) (@oldGamma) (@holdTarget) (@newi) (@newChoice) (by assumption) (@newCurrentDelta)
      (@newCurrentGamma) (@hnewIndex) (@htree) (@holdColorCast) (@hends) (@holdColorNe)
      (@hnewColorNe) (@hidentifiedDelta) (@hidentifiedGamma) (@holdDeltaAvailable)
      (@holdGammaAvailable) (@hnewDeltaAvailable) (@hnewGammaAvailable) (@hreplacementLastMap)
      (@hnewDeltaSigma) (@hgammaDeltaNe) (@hnewVertexTn) (@hpathComponent) (@hpathMeetsTn)
      (@hsigmaPrevStableQ) (@returnEdgeTransfer) (@hsigmaReturnIsPath) (@hsigmaReturnSupport)
      (@hreturnInQ) (@houtsideInQ) (@hreturnInNewEarlier) (@hreturnInTn) (@hcomponentDistinct)
      (@hQMeetsTn) (@hcorrRoundsPositive) (@hcorrRoundsLess) (@correspondingTerminalTree)
      (@hseriesTree) (@hlowerColor) (@hstableLower) (@hlowerTree) (@hdeltaLower) (@hlowerPackage)
      (@hinterchangeLower) (@hinterchangeTn) (@replacementCycle) (@hcycleFull) (@hclosedSigma)
      (@hclosedFinal) (@hreplacementCurrentTree) (@havailableCurrentIndex) (@havailableCurrentTree)
      (@hreturnCycle) (@houtsideCycle) (@hreturnCurrent) (@houtsideNotCurrent) (@rootedIsCycle)
      (@houtsideRooted) (@outsideIndicesNonempty) (@outsideOne) (@houtsideOneAt) (@houtsideOneNot)
      (@beforeFirstOutside) (@firstOutsidePositive) (@firstOutsideLt) (@firstOutsideNotOne)
      (@firstOutsideAtLeastTwo) (@firstCrossingAdj) (@firstCrossingIndex) (@firstEdge)
      (@hfirstEdgeAt) (@hfirstOutsideIncident) (@hfirstEdgeActive) (@beforeFirstCrossingAdj)
      (@beforeFirstCrossingIndex) (@insideOne) (@hinsideOneAt) (@hinsideOneCurrent)
      (@hinsideOneIncident) (@endpointIdentity) (@hinsideOutsideOne) (@hfirstEnds) (@hfirstBoundary)
      (@laterInsideNonempty) (@hfirstReturnMem) (@hfirstReturnAfter) (@insideTwo) (@hinsideTwoAt)
      (@hinsideTwoCurrent) (@hreturnNotNext) (@hreturnGap) (@returnCrossingAdj)
      (@returnCrossingIndex) (@secondEdge) (@hsecondEdgeAt) (@hinsideTwoIncident)
      (@hsecondEdgeActive) (@beforeReturnCrossingAdj) (@beforeReturnCrossingIndex) (@outsideTwo)
      (@houtsideTwoAt) (@houtsideTwoNot) (@houtsideTwoIncident) (@houtsideInsideTwo) (@hsecondEnds)
      (@hsecondBoundary) (@hcrossingEdgesNe) (@hnewVertexCurrent) (@hfirstGamma) (@hsecondGamma)
      (@hnotStrongSigma) (@hreplacementColor) (@castReturnWalkIsPath) (@castReturnWalkSupport)
      (@castCycleSupport) (@hsigmaPathInQ) (@hsigmaPathOnCycle) (@hfstar) (@appendedCertificate)
      (@happGamma) (@happDelta) (@happEdge) (@happInside) (@happOutside) (@hstrictClosure)
      (@lastStep) (@extendedSeries) (@hextendedData)

private theorem revisitingReturnCrossing.{u_1, u_2} :
    revisitingReturnCrossingStatement.{u_1, u_2} := by
  classical
  intro V E inst inst_1 inst_2 inst_3 G k e0 input T generating ett hpositive hlower sigma
    hsigmaProper hsigmaOne hsigmaStable Tstar hTnTstar hstrict fstar seed hfinalEdges hadjoin
    closureTree hseedClosure hTstarClosure hTnClosure q hqSucc hqCast adjoined previousProper
    previousOneUncolored previousClosed available currentStored currentEdges currentKind hroundLarge
    originalPrefix hr hprefixTrees hprefixData corr hcorrFinalTree hcorrFinalColor hcorrMP
    earlierPrefixBound earlierPrefix hearlierMap hearlierPositive hreplacementEarlierKind oldi
    oldChoice oldGamma holdTarget newi newChoice newGamma newCurrentDelta newCurrentGamma hnewIndex
    htree oldChoiceOnNew holdColorCast hends holdColorNe hnewColorNe hidentifiedDelta
    hidentifiedGamma holdDeltaAvailable holdGammaAvailable hnewDeltaAvailable hnewGammaAvailable
    replacementLast hreplacementLastMap hnewDeltaSigma hgammaDeltaNe hnewVertexTn hpathComponent
    hpathMeetsTn hsigmaPrevStableQ sigmaReturnGraph returnEdgeTransfer sigmaReturnPath
    hsigmaReturnIsPath hsigmaReturnSupport hreturnInQ houtsideInQ hreturnInNewEarlier hreturnInTn
    hcomponentDistinct hQMeetsTn hcorrRoundsPositive hcorrRoundsLess correspondingTerminalTree
    hseriesTree hlowerColor hstableLower hlowerTree hdeltaLower hlowerPackage hinterchangeLower
    hinterchangeTn replacementCycle hcycleFull hclosedSigma hclosedFinal hreplacementCurrentTree
    havailableCurrentIndex havailableCurrentTree currentTree hreturnCycle houtsideCycle
    hreturnCurrent houtsideNotCurrent rootedCycle rootedIsCycle houtsideRooted outsideIndices
    outsideIndicesNonempty firstOutside outsideOne houtsideOneAt houtsideOneNot beforeFirstOutside
    firstOutsidePositive firstOutsideLt firstOutsideNotOne firstOutsideAtLeastTwo firstCrossingAdj
    firstCrossingIndex firstEdge hfirstEdgeAt hfirstOutsideIncident hfirstEdgeActive
    beforeFirstCrossingAdj beforeFirstCrossingIndex insideOne hinsideOneAt hinsideOneCurrent
    hinsideOneIncident endpointIdentity hinsideOutsideOne hfirstEnds hfirstBoundary
    laterInsideIndices laterInsideNonempty firstReturn hfirstReturnMem hfirstReturnAfter insideTwo
    hinsideTwoAt hinsideTwoCurrent hreturnNotNext
  have hreturnGap : firstOutside.val + 2 ≤ firstReturn.val := by omega
  have returnCrossingAdj := rootedCycle.adj_getVert_succ (i := firstReturn.val - 1) (by omega)
  have returnCrossingIndex : firstReturn.val - 1 + 1 = firstReturn.val := by omega
  obtain ⟨secondEdge, hsecondEdgeAt⟩ :
    ∃ f : E, rootedCycle.getVert (firstReturn.val - 1) = Sum.inr f := by
    cases hnode : rootedCycle.getVert (firstReturn.val - 1) with
    | inl v =>
      exfalso
      rw [returnCrossingIndex, hinsideTwoAt, hnode] at returnCrossingAdj
      simp [TwoColorIncidenceGraph] at returnCrossingAdj
    | inr f => exact ⟨f, rfl⟩
  have hinsideTwoIncident : Incident G insideTwo secondEdge := by
    rw [returnCrossingIndex, hinsideTwoAt, hsecondEdgeAt] at returnCrossingAdj
    simpa [TwoColorIncidenceGraph] using returnCrossingAdj.1
  have hsecondEdgeActive :
    sigma secondEdge = some available.gamma ∨ sigma secondEdge = some available.delta := by
    rw [returnCrossingIndex, hinsideTwoAt, hsecondEdgeAt] at returnCrossingAdj
    simpa [TwoColorIncidenceGraph] using returnCrossingAdj.2
  have beforeReturnCrossingAdj := rootedCycle.adj_getVert_succ (i := firstReturn.val - 2) (by omega)
  have beforeReturnCrossingIndex : firstReturn.val - 2 + 1 = firstReturn.val - 1 := by omega
  obtain ⟨outsideTwo, houtsideTwoAt⟩ :
    ∃ y : V, rootedCycle.getVert (firstReturn.val - 2) = Sum.inl y := by
    cases hnode : rootedCycle.getVert (firstReturn.val - 2) with
    | inl y => exact ⟨y, rfl⟩
    | inr f =>
      exfalso
      rw [beforeReturnCrossingIndex, hsecondEdgeAt, hnode] at beforeReturnCrossingAdj
      simp [TwoColorIncidenceGraph] at beforeReturnCrossingAdj
  have houtsideTwoNot : outsideTwo ∉ currentTree := by
    exact
      @helper_houtsideTwoNot_4210 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@Tstar)
        (@available) (@hroundLarge) (@originalPrefix) (@hr) (@corr) (@earlierPrefixBound) (@oldi)
        (@oldChoice) (@oldGamma) (@newi) (@newChoice) (@newGamma) (@htree) (@holdColorCast)
        (@holdColorNe) (@hnewColorNe) (@hidentifiedDelta) (@hidentifiedGamma) (@holdDeltaAvailable)
        (@holdGammaAvailable) (@replacementCycle) (@hreturnCycle) (@outsideIndicesNonempty)
        (@outsideOne) (@houtsideOneAt) (@houtsideOneNot) (@firstCrossingIndex)
        (@beforeFirstCrossingIndex) (@laterInsideNonempty) (@hreturnGap) (@returnCrossingIndex)
        (@beforeReturnCrossingIndex) (@outsideTwo) (@houtsideTwoAt)
  have houtsideTwoIncident : Incident G outsideTwo secondEdge := by
    rw [beforeReturnCrossingIndex, hsecondEdgeAt, houtsideTwoAt] at beforeReturnCrossingAdj
    simpa [TwoColorIncidenceGraph] using beforeReturnCrossingAdj.1
  have houtsideInsideTwo : outsideTwo ≠ insideTwo := by
    intro heq
    exact houtsideTwoNot (heq ▸ hinsideTwoCurrent)
  have hsecondEnds : G.ends secondEdge = s(insideTwo, outsideTwo) := by
    rw [Sym2.eq_swap]
    exact endpointIdentity houtsideTwoIncident hinsideTwoIncident houtsideInsideTwo
  have hsecondBoundary : secondEdge ∈ BoundaryEdges G currentTree := by
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨insideTwo, hinsideTwoCurrent, outsideTwo, houtsideTwoNot, hsecondEnds⟩
  have hcrossingEdgesNe : firstEdge ≠ secondEdge := by
    exact
      @helper_hcrossingEdgesNe_4255 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma)
        (@Tstar) (@available) (@hroundLarge) (@originalPrefix) (@hr) (@corr) (@earlierPrefixBound)
        (@oldi) (@oldChoice) (@oldGamma) (@newi) (@newChoice) (@newGamma) (@htree) (@holdColorCast)
        (@holdColorNe) (@hnewColorNe) (@hidentifiedDelta) (@hidentifiedGamma) (@holdDeltaAvailable)
        (@holdGammaAvailable) (@replacementCycle) (@hreturnCycle) (@rootedIsCycle)
        (@outsideIndicesNonempty) (@firstOutsideLt) (@firstOutsideAtLeastTwo) (@firstCrossingIndex)
        (@firstEdge) (@hfirstEdgeAt) (@beforeFirstCrossingIndex) (@laterInsideNonempty)
        (@hreturnGap) (@returnCrossingIndex) (@secondEdge) (@hsecondEdgeAt)
        (@beforeReturnCrossingIndex)
  have hnewVertexCurrent : newChoice.vertex ∈ currentTree := by
    simpa [currentTree, hqSucc] using hnewVertexTn
  have hfirstGamma :=
    helper_hfirstGamma_2063 (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma)
      (@Tstar) (@available) (@originalPrefix) (@corr) (@newi) (@newChoice) (@hnewDeltaSigma)
      (@hclosedSigma) (@firstEdge) (@hfirstEdgeActive) (@hfirstBoundary) (@hnewVertexCurrent)
  have hsecondGamma :=
    helper_hsecondGamma_2070 (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive)
      (@sigma) (@Tstar) (@available) (@originalPrefix) (@corr) (@newi) (@newChoice)
      (@hnewDeltaSigma) (@hclosedSigma) (@secondEdge) (@hsecondEdgeActive) (@hsecondBoundary)
      (@hnewVertexCurrent)
  have hnotStrongSigma : ¬ColoredVertexSetStronglyClosed G sigma currentTree := by
    intro hstrong
    exact (hstrong.2 hfirstBoundary hsecondBoundary hcrossingEdgesNe hfirstGamma) hsecondGamma
  have hreplacementColor : corr.replacementSeries.data.coloring replacementLast = sigma := by
    simpa [replacementLast] using hcorrFinalColor
  let castReturnWalk (phi psi : PartialEdgeColoring E k) (hphi : phi = psi)
    (P :
      (TwoColorIncidenceGraph G psi available.gamma available.delta).Walk (Sum.inr available.edge)
        (Sum.inl available.returnVertex)) :
    (TwoColorIncidenceGraph G phi available.gamma available.delta).Walk (Sum.inr available.edge)
      (Sum.inl available.returnVertex) := by
    subst psi
    exact P
  have castReturnWalkIsPath :
    ∀ (phi psi : PartialEdgeColoring E k) (hphi : phi = psi)
      (P :
        (TwoColorIncidenceGraph G psi available.gamma available.delta).Walk (Sum.inr available.edge)
          (Sum.inl available.returnVertex)),
      P.IsPath → (castReturnWalk phi psi hphi P).IsPath := by
    intro phi psi hphi P hP
    subst psi
    exact hP
  have castReturnWalkSupport :
    ∀ (phi psi : PartialEdgeColoring E k) (hphi : phi = psi)
      (P :
        (TwoColorIncidenceGraph G psi available.gamma available.delta).Walk (Sum.inr available.edge)
          (Sum.inl available.returnVertex))
      z, z ∈ (castReturnWalk phi psi hphi P).support ↔ z ∈ P.support := by
    intro phi psi hphi P z
    subst psi
    rfl
  let castCycle (phi psi : PartialEdgeColoring E k) (hphi : phi = psi)
    (C : TwoColorCycle G psi available.gamma available.delta) :
    TwoColorCycle G phi available.gamma available.delta := by
    subst psi
    exact C
  exact
    @revisitingCertificateTransport (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@hlower)
      (@sigma) (@hsigmaProper) (@hsigmaOne) (@hsigmaStable) (@Tstar) (@hTnTstar) (@hstrict) (@fstar)
      (@seed) (@hfinalEdges) (@hadjoin) (@closureTree) (@hseedClosure) (@hTstarClosure)
      (@hTnClosure) (@hqSucc) (@hqCast) (@adjoined) (@previousProper) (@previousOneUncolored)
      (@previousClosed) (@available) (@currentStored) (@currentEdges) (@currentKind) (@hroundLarge)
      (@originalPrefix) (@hr) (@hprefixTrees) (@hprefixData) (@corr) (@hcorrFinalTree)
      (@hcorrFinalColor) (@hcorrMP) (@earlierPrefixBound) (@hearlierMap) (@hearlierPositive)
      (@hreplacementEarlierKind) (@oldi) (@oldChoice) (@oldGamma) (@holdTarget) (@newi) (@newChoice)
      (@newGamma) (@newCurrentDelta) (@newCurrentGamma) (@hnewIndex) (@htree) (@holdColorCast)
      (@hends) (@holdColorNe) (@hnewColorNe) (@hidentifiedDelta) (@hidentifiedGamma)
      (@holdDeltaAvailable) (@holdGammaAvailable) (@hnewDeltaAvailable) (@hnewGammaAvailable)
      (@hreplacementLastMap) (@hnewDeltaSigma) (@hgammaDeltaNe) (@hnewVertexTn) (@hpathComponent)
      (@hpathMeetsTn) (@hsigmaPrevStableQ) (@returnEdgeTransfer) (@hsigmaReturnIsPath)
      (@hsigmaReturnSupport) (@hreturnInQ) (@houtsideInQ) (@hreturnInNewEarlier) (@hreturnInTn)
      (@hcomponentDistinct) (@hQMeetsTn) (@hcorrRoundsPositive) (@hcorrRoundsLess)
      (@correspondingTerminalTree) (@hseriesTree) (@hlowerColor) (@hstableLower) (@hlowerTree)
      (@hdeltaLower) (@hlowerPackage) (@hinterchangeLower) (@hinterchangeTn) (@replacementCycle)
      (@hcycleFull) (@hclosedSigma) (@hclosedFinal) (@hreplacementCurrentTree)
      (@havailableCurrentIndex) (@havailableCurrentTree) (@hreturnCycle) (@houtsideCycle)
      (@hreturnCurrent) (@houtsideNotCurrent) (@rootedIsCycle) (@houtsideRooted)
      (@outsideIndicesNonempty) (@outsideOne) (@houtsideOneAt) (@houtsideOneNot)
      (@beforeFirstOutside) (@firstOutsidePositive) (@firstOutsideLt) (@firstOutsideNotOne)
      (@firstOutsideAtLeastTwo) (@firstCrossingAdj) (@firstCrossingIndex) (@firstEdge)
      (@hfirstEdgeAt) (@hfirstOutsideIncident) (@hfirstEdgeActive) (@beforeFirstCrossingAdj)
      (@beforeFirstCrossingIndex) (@insideOne) (@hinsideOneAt) (@hinsideOneCurrent)
      (@hinsideOneIncident) (@endpointIdentity) (@hinsideOutsideOne) (@hfirstEnds) (@hfirstBoundary)
      (@laterInsideNonempty) (@hfirstReturnMem) (@hfirstReturnAfter) (@insideTwo) (@hinsideTwoAt)
      (@hinsideTwoCurrent) (@hreturnNotNext) (@hreturnGap) (@returnCrossingAdj)
      (@returnCrossingIndex) (@secondEdge) (@hsecondEdgeAt) (@hinsideTwoIncident)
      (@hsecondEdgeActive) (@beforeReturnCrossingAdj) (@beforeReturnCrossingIndex) (@outsideTwo)
      (@houtsideTwoAt) (@houtsideTwoNot) (@houtsideTwoIncident) (@houtsideInsideTwo) (@hsecondEnds)
      (@hsecondBoundary) (@hcrossingEdgesNe) (@hnewVertexCurrent) (@hfirstGamma) (@hsecondGamma)
      (@hnotStrongSigma) (@hreplacementColor) (@castReturnWalkIsPath) (@castReturnWalkSupport)

private theorem revisitingFirstCrossing.{u_1, u_2} : revisitingFirstCrossingStatement.{u_1, u_2}
    := by
  classical
  intro «V» «E» «inst» «inst_1» «inst_2» «inst_3» «G» «k» «e0» «input» «T» «generating» «ett»
      «hpositive» «hlower» «sigma» «hsigmaProper» «hsigmaOne» «hsigmaStable» «Tstar» «hTnTstar»
      «hstrict» «fstar» «seed» «hfinalEdges» «hadjoin» «closureTree» «hseedClosure» «hTstarClosure»
      «hTnClosure» «q» «hqSucc» «hqCast» «adjoined» «previousProper» «previousOneUncolored»
      «previousClosed» «available» «currentStored» «currentEdges» «currentKind» «hroundLarge»
      «originalPrefix» «hr» «hprefixTrees» «hprefixData» «corr» «hcorrFinalTree» «hcorrFinalColor»
      «hcorrMP» «earlierPrefixBound» «earlierPrefix» «hearlierMap» «hearlierPositive»
      «hreplacementEarlierKind» «oldi» «oldChoice» «oldGamma» «holdTarget» «newi» «newChoice»
      «newGamma» «newCurrentDelta» «newCurrentGamma» «hnewIndex» «htree» «oldChoiceOnNew»
      «holdColorCast» «hends» «holdColorNe» «hnewColorNe» «hidentifiedDelta» «hidentifiedGamma»
      «holdDeltaAvailable» «holdGammaAvailable» «hnewDeltaAvailable» «hnewGammaAvailable»
      «replacementLast» «hreplacementLastMap» «hnewDeltaSigma» «hgammaDeltaNe» «hnewVertexTn»
      «hpathComponent» «hpathMeetsTn» «hsigmaPrevStableQ» «sigmaReturnGraph» «returnEdgeTransfer»
      «sigmaReturnPath» «hsigmaReturnIsPath» «hsigmaReturnSupport» «hreturnInQ» «houtsideInQ»
      «hreturnInNewEarlier» «hreturnInTn» «hcomponentDistinct» «hQMeetsTn» «hcorrRoundsPositive»
      «hcorrRoundsLess» «correspondingTerminalTree» «hseriesTree» «hlowerColor» «hstableLower»
      «hlowerTree» «hdeltaLower» «hlowerPackage» «hinterchangeLower» «hinterchangeTn»
      «replacementCycle» «hcycleFull» «hclosedSigma» «hclosedFinal» «hreplacementCurrentTree»
      «havailableCurrentIndex» «havailableCurrentTree» «currentTree» «hreturnCycle» «houtsideCycle»
      «hreturnCurrent» «houtsideNotCurrent» «rootedCycle» «rootedIsCycle» «houtsideRooted»
      «outsideIndices» «outsideIndicesNonempty» «firstOutside»
  let firstOutside : Fin (rootedCycle.length + 1) :=
    outsideIndices.min' outsideIndicesNonempty
  obtain ⟨outsideOne, houtsideOneAt, houtsideOneNot⟩ :=
    (Finset.mem_filter.mp
      (Finset.min'_mem outsideIndices
        outsideIndicesNonempty)).2
  have beforeFirstOutside : ∀
      (idx : Fin (rootedCycle.length + 1)),
      idx.val < firstOutside.val → ∀ v : V,
      rootedCycle.getVert idx.val = Sum.inl v →
        v ∈ currentTree := by
    exact @helper_beforeFirstOutside_4031 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma)
        (@Tstar) (@available) (@hroundLarge) (@originalPrefix) (@hr) (@corr) (@earlierPrefixBound)
        (@oldi) (@oldChoice) (@oldGamma) (@newi) (@newChoice) (@newGamma) (@htree) (@holdColorCast)
        (@holdColorNe) (@hnewColorNe) (@hidentifiedDelta) (@hidentifiedGamma) (@holdDeltaAvailable)
        (@holdGammaAvailable) (@replacementCycle) (@hreturnCycle) (@outsideIndicesNonempty)
  have firstOutsidePositive : 0 < firstOutside.val := by
    exact @helper_firstOutsidePositive_4043 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma)
        (@Tstar) (@available) (@hroundLarge) (@originalPrefix) (@hr) (@corr) (@earlierPrefixBound)
        (@oldi) (@oldChoice) (@oldGamma) (@newi) (@newChoice) (@newGamma) (@htree) (@holdColorCast)
        (@holdColorNe) (@hnewColorNe) (@hidentifiedDelta) (@hidentifiedGamma) (@holdDeltaAvailable)
        (@holdGammaAvailable) (@replacementCycle) (@hreturnCycle) (@hreturnCurrent)
        (@outsideIndicesNonempty) (@outsideOne) (@houtsideOneAt) (@houtsideOneNot)
  have firstOutsideLt : firstOutside.val <
      rootedCycle.length := by
    exact @helper_firstOutsideLt_4055 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma)
        (@Tstar) (@available) (@hroundLarge) (@originalPrefix) (@hr) (@corr) (@earlierPrefixBound)
        (@oldi) (@oldChoice) (@oldGamma) (@newi) (@newChoice) (@newGamma) (@htree) (@holdColorCast)
        (@holdColorNe) (@hnewColorNe) (@hidentifiedDelta) (@hidentifiedGamma) (@holdDeltaAvailable)
        (@holdGammaAvailable) (@replacementCycle) (@hreturnCycle) (@hreturnCurrent)
        (@outsideIndicesNonempty) (@outsideOne) (@houtsideOneAt) (@houtsideOneNot)
  have firstOutsideNotOne : firstOutside.val ≠ 1 := by
    exact @helper_firstOutsideNotOne_4070 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma)
        (@Tstar) (@available) (@hroundLarge) (@originalPrefix) (@hr) (@corr) (@earlierPrefixBound)
        (@oldi) (@oldChoice) (@oldGamma) (@newi) (@newChoice) (@newGamma) (@htree) (@holdColorCast)
        (@holdColorNe) (@hnewColorNe) (@hidentifiedDelta) (@hidentifiedGamma) (@holdDeltaAvailable)
        (@holdGammaAvailable) (@replacementCycle) (@hreturnCycle) (@outsideIndicesNonempty)
        (@outsideOne) (@houtsideOneAt) (@firstOutsideLt)
  have firstOutsideAtLeastTwo : 2 ≤ firstOutside.val := by omega
  have firstCrossingAdj := rootedCycle.adj_getVert_succ
    (i := firstOutside.val - 1) (by omega)
  have firstCrossingIndex : firstOutside.val - 1 + 1 =
      firstOutside.val := by omega
  obtain ⟨firstEdge, hfirstEdgeAt⟩ : ∃ f : E,
      rootedCycle.getVert (firstOutside.val - 1) =
        Sum.inr f := by
    cases hnode : rootedCycle.getVert
        (firstOutside.val - 1) with
    | inl v =>
        exfalso
        rw [firstCrossingIndex, houtsideOneAt, hnode] at firstCrossingAdj
        simp [TwoColorIncidenceGraph] at firstCrossingAdj
    | inr f => exact ⟨f, rfl⟩
  have hfirstOutsideIncident : Incident G outsideOne firstEdge := by
    rw [firstCrossingIndex, houtsideOneAt, hfirstEdgeAt] at firstCrossingAdj
    simpa [TwoColorIncidenceGraph] using firstCrossingAdj.1
  have hfirstEdgeActive : sigma firstEdge =
        some available.gamma ∨
      sigma firstEdge = some available.delta := by
    rw [firstCrossingIndex, houtsideOneAt, hfirstEdgeAt] at firstCrossingAdj
    simpa [TwoColorIncidenceGraph] using firstCrossingAdj.2
  have beforeFirstCrossingAdj := rootedCycle.adj_getVert_succ
    (i := firstOutside.val - 2) (by omega)
  have beforeFirstCrossingIndex : firstOutside.val - 2 + 1 =
      firstOutside.val - 1 := by omega
  obtain ⟨insideOne, hinsideOneAt⟩ : ∃ x : V,
      rootedCycle.getVert (firstOutside.val - 2) =
        Sum.inl x := by
    cases hnode : rootedCycle.getVert
        (firstOutside.val - 2) with
    | inl x => exact ⟨x, rfl⟩
    | inr f =>
        exfalso
        rw [beforeFirstCrossingIndex, hfirstEdgeAt, hnode] at beforeFirstCrossingAdj
        simp [TwoColorIncidenceGraph] at beforeFirstCrossingAdj
  have hinsideOneCurrent : insideOne ∈ currentTree := by
    exact @helper_hinsideOneCurrent_4119 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma)
        (@Tstar) (@available) (@hroundLarge) (@originalPrefix) (@hr) (@corr) (@earlierPrefixBound)
        (@oldi) (@oldChoice) (@oldGamma) (@newi) (@newChoice) (@newGamma) (@htree) (@holdColorCast)
        (@holdColorNe) (@hnewColorNe) (@hidentifiedDelta) (@hidentifiedGamma) (@holdDeltaAvailable)
        (@holdGammaAvailable) (@replacementCycle) (@hreturnCycle) (@outsideIndicesNonempty)
        (@beforeFirstOutside) (@firstCrossingIndex) (@beforeFirstCrossingIndex) (@insideOne)
        (@hinsideOneAt)
  have hinsideOneIncident : Incident G insideOne firstEdge := by
    rw [beforeFirstCrossingIndex, hfirstEdgeAt, hinsideOneAt] at beforeFirstCrossingAdj
    simpa [TwoColorIncidenceGraph] using
      beforeFirstCrossingAdj.1
  have endpointIdentity :=
    @helper_endpointIdentity_1568 (@V) (@E) (@G)
  have hinsideOutsideOne : insideOne ≠ outsideOne := by
    intro heq
    exact houtsideOneNot (heq ▸ hinsideOneCurrent)
  have hfirstEnds : G.ends firstEdge =
      s(insideOne, outsideOne) :=
    endpointIdentity hinsideOneIncident hfirstOutsideIncident
      hinsideOutsideOne
  have hfirstBoundary : firstEdge ∈ BoundaryEdges G currentTree := by
    simp only [BoundaryEdges, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨insideOne, hinsideOneCurrent, outsideOne,
      houtsideOneNot, hfirstEnds⟩
  let laterInsideIndices : Finset
      (Fin (rootedCycle.length + 1)) :=
    Finset.univ.filter fun idx => firstOutside.val < idx.val ∧
      ∃ v : V, rootedCycle.getVert idx.val = Sum.inl v ∧
        v ∈ currentTree
  have laterInsideNonempty : laterInsideIndices.Nonempty := by
    exact @helper_laterInsideNonempty_4150 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma)
        (@Tstar) (@available) (@hroundLarge) (@originalPrefix) (@hr) (@corr) (@earlierPrefixBound)
        (@oldi) (@oldChoice) (@oldGamma) (@newi) (@newChoice) (@newGamma) (@htree) (@holdColorCast)
        (@holdColorNe) (@hnewColorNe) (@hidentifiedDelta) (@hidentifiedGamma) (@holdDeltaAvailable)
        (@holdGammaAvailable) (@replacementCycle) (@hreturnCycle) (@hreturnCurrent)
        (@outsideIndicesNonempty) (@firstOutsideLt)
  let firstReturn : Fin (rootedCycle.length + 1) :=
    laterInsideIndices.min' laterInsideNonempty
  have hfirstReturnMem := Finset.min'_mem laterInsideIndices
    laterInsideNonempty
  have hfirstReturnAfter : firstOutside.val < firstReturn.val :=
    (Finset.mem_filter.mp hfirstReturnMem).2.1
  obtain ⟨insideTwo, hinsideTwoAt, hinsideTwoCurrent⟩ :=
    (Finset.mem_filter.mp hfirstReturnMem).2.2
  have hreturnNotNext : firstReturn.val ≠
      firstOutside.val + 1 := by
    exact helper_hreturnNotNext_3034 (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett)
        (@hpositive) (@sigma) (@Tstar) (@available) (@replacementCycle) (@hreturnCycle)
        (@outsideIndicesNonempty) (@outsideOne) (@houtsideOneAt) (@firstOutsideLt)
        (@laterInsideNonempty) (@insideTwo) (@hinsideTwoAt)
  exact @revisitingReturnCrossing (@«V») (@«E») inferInstance inferInstance inferInstance
      inferInstance (@«G») (@«k») (@«e0») (@«input») (@«T») (@«generating») (@«ett») (@«hpositive»)
      (@«hlower») (@«sigma») (@«hsigmaProper») (@«hsigmaOne») (@«hsigmaStable») (@«Tstar»)
      (@«hTnTstar») (@«hstrict») (@«fstar») (@«seed») (@«hfinalEdges») (@«hadjoin») (@«closureTree»)
      (@«hseedClosure») (@«hTstarClosure») (@«hTnClosure») (@«hqSucc») (@«hqCast») (@«adjoined»)
      (@«previousProper») (@«previousOneUncolored») (@«previousClosed») (@«available»)
      (@«currentStored») (@«currentEdges») (@«currentKind») (@«hroundLarge») (@«originalPrefix»)
      (@«hr») (@«hprefixTrees») (@«hprefixData») (@«corr») (@«hcorrFinalTree») (@«hcorrFinalColor»)
      (@«hcorrMP») (@«earlierPrefixBound») (@«hearlierMap») (@«hearlierPositive»)
      (@«hreplacementEarlierKind») (@«oldi») (@«oldChoice») (@«oldGamma») (@«holdTarget») (@«newi»)
      (@«newChoice») (@«newGamma») (@«newCurrentDelta») (@«newCurrentGamma») (@«hnewIndex»)
      (@«htree») (@«holdColorCast») (@«hends») (@«holdColorNe») (@«hnewColorNe»)
      (@«hidentifiedDelta») (@«hidentifiedGamma») (@«holdDeltaAvailable») (@«holdGammaAvailable»)
      (@«hnewDeltaAvailable») (@«hnewGammaAvailable») (@«hreplacementLastMap») (@«hnewDeltaSigma»)
      (@«hgammaDeltaNe») (@«hnewVertexTn») (@«hpathComponent») (@«hpathMeetsTn»)
      (@«hsigmaPrevStableQ») (@«returnEdgeTransfer») (@«hsigmaReturnIsPath»)
      (@«hsigmaReturnSupport») (@«hreturnInQ») (@«houtsideInQ») (@«hreturnInNewEarlier»)
      (@«hreturnInTn») (@«hcomponentDistinct») (@«hQMeetsTn») (@«hcorrRoundsPositive»)
      (@«hcorrRoundsLess») (@«correspondingTerminalTree») (@«hseriesTree») (@«hlowerColor»)
      (@«hstableLower») (@«hlowerTree») (@«hdeltaLower») (@«hlowerPackage») (@«hinterchangeLower»)
      (@«hinterchangeTn») (@«replacementCycle») (@«hcycleFull») (@«hclosedSigma») (@«hclosedFinal»)
      (@«hreplacementCurrentTree») (@«havailableCurrentIndex») (@«havailableCurrentTree»)
      (@«hreturnCycle») (@«houtsideCycle») (@«hreturnCurrent») (@«houtsideNotCurrent»)
      (@«rootedIsCycle») (@«houtsideRooted») (@«outsideIndicesNonempty») (@«outsideOne»)
      (@«houtsideOneAt») (@«houtsideOneNot») (@«beforeFirstOutside») (@«firstOutsidePositive»)
      (@«firstOutsideLt») (@«firstOutsideNotOne») (@«firstOutsideAtLeastTwo») (@«firstCrossingAdj»)
      (@«firstCrossingIndex») (@«firstEdge») (@«hfirstEdgeAt») (@«hfirstOutsideIncident»)
      (@«hfirstEdgeActive») (@«beforeFirstCrossingAdj») (@«beforeFirstCrossingIndex») (@«insideOne»)
      (@«hinsideOneAt») (@«hinsideOneCurrent») (@«hinsideOneIncident») (@«endpointIdentity»)
      (@«hinsideOutsideOne») (@«hfirstEnds») (@«hfirstBoundary») (@«laterInsideNonempty»)
      (@«hfirstReturnMem») (@«hfirstReturnAfter») (@«insideTwo») (@«hinsideTwoAt»)
      (@«hinsideTwoCurrent») (@«hreturnNotNext»)

theorem helper_continuation_3762.{u_1, u_2} :
    terminalContinuationStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hpositive hlower sigma hsigmaProper hsigmaOne
      hsigmaStable Tstar hTnTstar hstrict fstar seed hfinalEdges hadjoin closureTree hseedClosure
      hTstarClosure hTnClosure q hqSucc hqCast adjoined previousProper previousOneUncolored
      previousClosed available currentStored currentEdges currentKind hroundLarge originalPrefix
      hr hprefixTrees hprefixData corr hcorrFinalTree hcorrFinalColor hcorrMP earlierPrefixBound
      earlierPrefix hearlierMap hearlierPositive hreplacementEarlierKind oldi oldChoice oldGamma
      holdTarget newi newChoice newGamma newCurrentDelta newCurrentGamma hnewIndex htree
      oldChoiceOnNew holdColorCast hends holdColorNe hnewColorNe hidentifiedDelta
      hidentifiedGamma holdDeltaAvailable holdGammaAvailable hnewDeltaAvailable
      hnewGammaAvailable replacementLast hreplacementLastMap hnewDeltaSigma hgammaDeltaNe
      hnewVertexTn hpathComponent hpathMeetsTn hsigmaPrevStableQ sigmaReturnGraph
      returnEdgeTransfer sigmaReturnPath hsigmaReturnIsPath hsigmaReturnSupport hreturnInQ
      houtsideInQ hreturnInNewEarlier hreturnInTn hcomponentDistinct
  have hQMeetsTn : ∃ v ∈ TreeSequenceVertexSet
      (ett.series.data.tree (Fin.last ett.rounds).castSucc),
      Sum.inl v ∈ TwoColorComponent G sigma available.gamma
        available.delta (Sum.inr available.edge) :=
    ⟨available.returnVertex, hreturnInTn, hreturnInQ⟩
  have hcorrRoundsPositive : 0 < corr.replacementETT.rounds :=
    corr.replacementETT.roundsPositive
  have hcorrRoundsLess : corr.replacementETT.rounds <
      ett.rounds := by
    rw [corr.rungAgreement, hr]
    omega
  have correspondingTerminalTree :=
    helper_correspondingTerminalTree_1299 (@G) (@k) (@e0) (@input) (@T) (@generating)
        (@ett) (@hpositive) (@sigma) (@originalPrefix)
  have hseriesTree := correspondingTerminalTree corr
  have hlowerColor :
      corr.replacementETT.series.data.coloring
          (Fin.last corr.replacementETT.rounds) = sigma := by
    exact corr.replacementETT.generatingColoring.symm
  have hstableLower : StableColoring
      (corr.replacementETT.series.data.tree
        (Fin.last (corr.replacementETT.rounds + 1)))
      (TashkinovStoredColors corr.replacementETT.series.data
        (Fin.last corr.replacementETT.rounds))
      (corr.replacementETT.series.data.coloring
        (Fin.last corr.replacementETT.rounds)) sigma := by
    rw [hlowerColor]
    exact ⟨(by intros; rfl), (by intros; rfl)⟩
  have hlowerTree : corr.replacementETT.series.data.tree
        (Fin.last (corr.replacementETT.rounds + 1)) =
      ett.series.data.tree
        (Fin.last ett.rounds).castSucc :=
    hseriesTree.trans hcorrFinalTree
  have hdeltaLower : available.delta ∈ TreeMissingColors sigma
      (corr.replacementETT.series.data.tree
        (Fin.last (corr.replacementETT.rounds + 1))) := by
    simp only [TreeMissingColors, Finset.mem_biUnion]
    refine ⟨newChoice.vertex, ?_, hnewDeltaSigma⟩
    rw [hlowerTree]
    exact hnewVertexTn
  have hlowerPackage := hlower corr.replacementETT
    hcorrRoundsPositive hcorrRoundsLess hcorrMP
  have hinterchangeLower := hlowerPackage.2.1 sigma
    hsigmaProper hsigmaOne hstableLower available.gamma
    available.delta (Or.inr hdeltaLower)
  have hinterchangeTn : TreeInterchangeable G
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      sigma available.gamma available.delta := by
    rw [← hlowerTree]
    exact hinterchangeLower
  have hcycleComponent :=
    TwoColorInterchangeableDistinctComponentCycle G
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      sigma available.gamma available.delta hsigmaProper
      (Sum.inl newChoice.vertex) (Sum.inr available.edge)
      hpathComponent.1 hinterchangeTn hpathMeetsTn hQMeetsTn
      hcomponentDistinct
  obtain ⟨replacementCycle, hcycleFull⟩ := hcycleComponent
  have hclosedSigma : ColoredVertexSetClosed G sigma
      (TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc)) := by
    exact helper_hclosedSigma_3647 (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett)
        (@hpositive) (@sigma) (@hsigmaProper) (@hsigmaOne) (@Tstar) (@previousProper)
        (@previousOneUncolored) (@previousClosed) (@hroundLarge) (@originalPrefix) (@corr)
        (@oldi) (@oldChoice) (@newi) (@newChoice) (@htree) (@hends) (@hsigmaPrevStableQ)
  have hclosedFinal : ColoredVertexSetClosed G sigma
      (TreeSequenceVertexSet
        (ett.series.data.tree
          (Fin.last ett.rounds).castSucc)) := by
    rw [← hqSucc]
    exact hclosedSigma
  have hreplacementCurrentTree :=
    helper_hreplacementCurrentTree_1736 (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett)
        (@hpositive) (@sigma) (@originalPrefix) (@corr) (@hcorrFinalTree)
  have havailableCurrentIndex : q.castSucc.succ =
      (Fin.last ett.rounds).castSucc := by
    apply Fin.ext
    have hvals := congrArg Fin.val hqSucc
    simp only [Fin.val_succ, Fin.val_castSucc] at hvals ⊢
    exact hvals
  have havailableCurrentTree :
      ett.series.data.tree q.castSucc.succ =
        ett.series.data.tree
          (Fin.last ett.rounds).castSucc := by
    rw [havailableCurrentIndex]
  let currentTree := TreeSequenceVertexSet
    (ett.series.data.tree q.succ.castSucc)
  have hreturnCycle : Sum.inl available.returnVertex ∈
      replacementCycle.walk.support :=
    (hcycleFull _).2 hreturnInQ
  have houtsideCycle : Sum.inl available.outsideEndpoint ∈
      replacementCycle.walk.support :=
    (hcycleFull _).2 houtsideInQ
  have hreturnCurrent : available.returnVertex ∈ currentTree := by
    simpa [currentTree, hqSucc] using hreturnInTn
  have houtsideNotCurrent : available.outsideEndpoint ∉
      currentTree := by
    simpa [currentTree] using available.outsideNotCurrent
  let rootedCycle := replacementCycle.walk.rotate
    (Sum.inl available.returnVertex) hreturnCycle
  have rootedIsCycle : rootedCycle.IsCycle :=
    replacementCycle.isCycle.rotate hreturnCycle
  have houtsideRooted : Sum.inl available.outsideEndpoint ∈
      rootedCycle.support := by
    apply (replacementCycle.walk.mem_support_rotate_iff
      (Sum.inl available.returnVertex) hreturnCycle).mpr
    exact houtsideCycle
  let outsideIndices : Finset
      (Fin (rootedCycle.length + 1)) :=
    Finset.univ.filter fun i => ∃ v : V,
      rootedCycle.getVert i.val = Sum.inl v ∧
        v ∉ currentTree
  have outsideIndicesNonempty : outsideIndices.Nonempty := by
    exact @helper_outsideIndicesNonempty_4016 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma)
        (@Tstar) (@available) (@hroundLarge) (@originalPrefix) (@hr) (@corr) (@earlierPrefixBound)
        (@oldi) (@oldChoice) (@oldGamma) (@newi) (@newChoice) (@newGamma) (@htree) (@holdColorCast)
        (@holdColorNe) (@hnewColorNe) (@hidentifiedDelta) (@hidentifiedGamma) (@holdDeltaAvailable)
        (@holdGammaAvailable) (@replacementCycle) (@hreturnCycle) (@houtsideNotCurrent)
        (@houtsideRooted)
  exact @revisitingFirstCrossing (@«V») (@«E») inferInstance inferInstance inferInstance
      inferInstance (@«G») (@«k») (@«e0») (@«input») (@«T») (@«generating») (@«ett») (@«hpositive»)
      (@«hlower») (@«sigma») (@«hsigmaProper») (@«hsigmaOne») (@«hsigmaStable») (@«Tstar»)
      (@«hTnTstar») (@«hstrict») (@«fstar») (@«seed») (@«hfinalEdges») (@«hadjoin») (@«closureTree»)
      (@«hseedClosure») (@«hTstarClosure») (@«hTnClosure») (@«hqSucc») (@«hqCast») (@«adjoined»)
      (@«previousProper») (@«previousOneUncolored») (@«previousClosed») (@«available»)
      (@«currentStored») (@«currentEdges») (@«currentKind») (@«hroundLarge») (@«originalPrefix»)
      (@«hr») (@«hprefixTrees») (@«hprefixData») (@«corr») (@«hcorrFinalTree») (@«hcorrFinalColor»)
      (@«hcorrMP») (@«earlierPrefixBound») (@«hearlierMap») (@«hearlierPositive»)
      (@«hreplacementEarlierKind») (@«oldi») (@«oldChoice») (@«oldGamma») (@«holdTarget») (@«newi»)
      (@«newChoice») (@«newGamma») (@«newCurrentDelta») (@«newCurrentGamma») (@«hnewIndex»)
      (@«htree») (@«holdColorCast») (@«hends») (@«holdColorNe») (@«hnewColorNe»)
      (@«hidentifiedDelta») (@«hidentifiedGamma») (@«holdDeltaAvailable») (@«holdGammaAvailable»)
      (@«hnewDeltaAvailable») (@«hnewGammaAvailable») (@«hreplacementLastMap») (@«hnewDeltaSigma»)
      (@«hgammaDeltaNe») (@«hnewVertexTn») (@«hpathComponent») (@«hpathMeetsTn»)
      (@«hsigmaPrevStableQ») (@«returnEdgeTransfer») (@«hsigmaReturnIsPath»)
      (@«hsigmaReturnSupport») (@«hreturnInQ») (@«houtsideInQ») (@«hreturnInNewEarlier»)
      (@«hreturnInTn») (@«hcomponentDistinct») (@«hQMeetsTn») (@«hcorrRoundsPositive»)
      (@«hcorrRoundsLess») (@«correspondingTerminalTree») (@«hseriesTree») (@«hlowerColor»)
      (@«hstableLower») (@«hlowerTree») (@«hdeltaLower») (@«hlowerPackage») (@«hinterchangeLower»)
      (@«hinterchangeTn») (@«replacementCycle») (@«hcycleFull») (@«hclosedSigma») (@«hclosedFinal»)
      (@«hreplacementCurrentTree») (@«havailableCurrentIndex») (@«havailableCurrentTree»)
      (@«hreturnCycle») (@«houtsideCycle») (@«hreturnCurrent») (@«houtsideNotCurrent»)
      (@«rootedIsCycle») (@«houtsideRooted») (@«outsideIndicesNonempty»)

theorem helper_continuation_3509.{u_1, u_2} :
    helperContinuation3509Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hpositive hlower sigma hsigmaProper hsigmaOne
      hsigmaStable Tstar hTnTstar hstrict fstar seed hfinalEdges hadjoin closureTree hseedClosure
      hTstarClosure hTnClosure q hqSucc hqCast adjoined previousProper previousOneUncolored
      previousClosed available currentStored currentEdges currentKind hroundLarge originalPrefix
      hr hprefixTrees hprefixData corr hcorrFinalTree hcorrFinalColor hcorrMP earlierPrefixBound
      earlierPrefix hearlierMap hearlierPositive hreplacementEarlierKind oldi oldChoice oldGamma
      holdTarget holdIndex newi newChoice newGamma newGammaRule newSecond newSecondProper
      newSecondStable newExit newCurrentColoring newCurrentDelta newCurrentGamma hnewIndex htree
      oldChoiceOnNew holdColorCast hends holdDeltaMissing holdColorNe hnewColorNe
      hidentifiedDelta hidentifiedGamma holdDeltaAvailable holdGammaAvailable hnewDeltaAvailable
      hnewGammaAvailable hnewVertexOld holdColorConstant replacementLast hreplacementLastMap
      hnewPostSigma hnewDeltaSigma hgammaDeltaNe hnewTreeFinal hnewVertexTn hpathComponent
      hpathMeetsTn hsigmaPrevStableQ hgammaEarlierStored hdeltaEarlierStored colorControlAtQ
  have hreturnNotNil : ¬ available.returnPath.Nil := by
    intro hnil
    have hend := SimpleGraph.Walk.Nil.eq hnil
    simp at hend
  have oldReturnEdgeData (f : E)
      (hf : Sum.inr f ∈ available.returnPath.support) :
      TreeIncidentEdge
          (ett.series.data.tree q.succ.castSucc) f ∧
        (ett.series.data.coloring q.castSucc f =
            some available.gamma ∨
          ett.series.data.coloring q.castSucc f =
            some available.delta) := by
    exact @helper_oldReturnEdgeData_978 (@V) (@E) inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett)
        (@hpositive) (@Tstar) (@available) (@hreturnNotNil) (@f) (@hf)
  have copyReturnEdge (f : E)
      (hf : Sum.inr f ∈ available.returnPath.support) :
      sigma f = ett.series.data.coloring q.castSucc f := by
    exact @helper_copyReturnEdge_2580 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@Tstar) (@available)
        (@hsigmaPrevStableQ) (@hgammaEarlierStored) (@hdeltaEarlierStored) (@colorControlAtQ)
        (@oldReturnEdgeData) (@f) (@hf)
  let oldReturnGraph := TwoColorIncidenceGraph G
    (ett.series.data.coloring q.castSucc) available.gamma
    available.delta
  let sigmaReturnGraph := TwoColorIncidenceGraph G sigma
    available.gamma available.delta
  have returnEdgeTransfer : ∀ edge,
      edge ∈ available.returnPath.edges →
      edge ∈ sigmaReturnGraph.edgeSet := by
    exact @helper_returnEdgeTransfer_1018 (@V) (@E) inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett)
        (@hpositive) (@sigma) (@Tstar) (@available) (@copyReturnEdge)
  let sigmaReturnPath :=
    available.returnPath.transfer sigmaReturnGraph
      returnEdgeTransfer
  have hsigmaReturnIsPath : sigmaReturnPath.IsPath := by
    exact available.returnPathIsPath.transfer returnEdgeTransfer
  have hsigmaReturnSupport : ∀ z,
      z ∈ sigmaReturnPath.support ↔
        z ∈ available.returnPath.support := by
    intro z
    simp [sigmaReturnPath]
  have hreturnInQ : Sum.inl available.returnVertex ∈
      TwoColorComponent G sigma available.gamma available.delta
        (Sum.inr available.edge) := by
    exact @helper_hreturnInQ_1513 (@V) (@E) inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett)
        (@hpositive) (@sigma) (@Tstar) (@available) (@returnEdgeTransfer)
  have hedgeSigmaActive : sigma available.edge =
        some available.gamma ∨
      sigma available.edge = some available.delta := by
    exact @helper_hedgeSigmaActive_1522 (@V) (@E) inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett)
        (@hpositive) (@sigma) (@Tstar) (@available) (@oldReturnEdgeData)
        (@copyReturnEdge)
  have houtsideInQ : Sum.inl available.outsideEndpoint ∈
      TwoColorComponent G sigma available.gamma available.delta
        (Sum.inr available.edge) := by
    exact @helper_houtsideInQ_1530 (@V) (@E) inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett)
        (@hpositive) (@sigma) (@Tstar) (@available) (@hedgeSigmaActive)
  have hreturnInNewEarlier : available.returnVertex ∈
      TreeSequenceVertexSet
        (corr.replacementSeries.data.tree
          earlierPrefix.castSucc) := by
    rw [← hnewIndex, htree]
    simpa only [holdIndex] using available.returnInEarlier
  have hreturnInTn : available.returnVertex ∈
      TreeSequenceVertexSet
        (ett.series.data.tree
          (Fin.last ett.rounds).castSucc) := by
    have hvFinal : available.returnVertex ∈
        TreeSequenceVertexSet
          (corr.replacementSeries.data.tree
            (Fin.last (originalPrefix.rounds + 1))) :=
      TreeSequenceInitialSegmentVertexSetSubset hnewTreeFinal
        (by simpa only [hnewIndex] using hreturnInNewEarlier)
    exact Eq.mp
      (congrArg (fun X => available.returnVertex ∈
        TreeSequenceVertexSet X) hcorrFinalTree) hvFinal
  have holdDeltaAtNewVertex : available.delta ∈ MissingColors G
      (ett.series.data.coloring q.castSucc)
      newChoice.vertex := by
    exact @helper_holdDeltaAtNewVertex_2647 (@V) (@E) inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@Tstar)
        (@available) (@originalPrefix) (@corr) (@oldi) (@oldChoice) (@newi) (@newChoice)
        (@holdDeltaMissing) (@holdDeltaAvailable) (@hnewVertexOld) (@holdColorConstant)
  have holdLeafDegree : @SimpleGraph.degree _
      (TwoColorIncidenceGraph G
        (ett.series.data.coloring q.castSucc)
        available.gamma available.delta)
      (Sum.inl newChoice.vertex) (Fintype.ofFinite _) ≤ 1 := by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, Fintype.card_eq_nat_card]
        using
      (@helper_holdLeafDegree_1372 (@V) (@E) inferInstance inferInstance
           inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating)
          (@ett) (@hpositive) (@sigma) (@Tstar) (@previousProper) (@available)
          (@originalPrefix) (@corr) (@newi) (@newChoice) (@hgammaDeltaNe)
          (@holdDeltaAtNewVertex))
  have holdLeaf : Set.Subsingleton
      ((TwoColorIncidenceGraph G
        (ett.series.data.coloring q.castSucc)
        available.gamma available.delta).neighborSet
          (Sum.inl newChoice.vertex)) := by
    let : Fintype
        ((TwoColorIncidenceGraph G
          (ett.series.data.coloring q.castSucc)
          available.gamma available.delta).neighborSet
            (Sum.inl newChoice.vertex)) := Fintype.ofFinite _
    rw [← SimpleGraph.card_neighborSet_eq_degree] at holdLeafDegree
    have hsub := Fintype.card_le_one_iff.mp holdLeafDegree
    intro a ha b hb
    exact congrArg Subtype.val (hsub ⟨a, ha⟩ ⟨b, hb⟩)
  have hreturnNeNew : available.returnVertex ≠
      newChoice.vertex := by
    exact @helper_hreturnNeNew_1406 (@V) (@E) inferInstance inferInstance
         inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating)
        (@ett) (@hpositive) (@sigma) (@Tstar) (@available) (@originalPrefix)
        (@corr) (@newi) (@newChoice) (@holdLeaf)
  have hswapGraph : TwoColorIncidenceGraph G
        (TwoColorComponentSwap G newSecond newGamma
          newChoice.color (Sum.inl newChoice.vertex))
        newGamma newChoice.color =
      TwoColorIncidenceGraph G newSecond newGamma
        newChoice.color := by
    exact @helper_hswapGraph_1429 (@V) (@E) inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett)
        (@hpositive) (@sigma) (@originalPrefix) (@corr) (@newi) (@newChoice)
        (@newGamma) (@newSecond)
  have hsigmaExitGraph : TwoColorIncidenceGraph G sigma
        available.gamma available.delta =
      TwoColorIncidenceGraph G newSecond newGamma
        newChoice.color := by
    exact @helper_hsigmaExitGraph_2697 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@Tstar) (@available)
        (@originalPrefix) (@corr) (@newi) (@newChoice) (@newGamma) (@newSecond)
        (@newCurrentColoring) (@hnewDeltaAvailable) (@hnewGammaAvailable) (@hnewPostSigma)
        (@hswapGraph)
  have hnewGammaSecond : newGamma ∈ MissingColors G newSecond
      newChoice.vertex := by
    rw [newSecondStable.2 newChoice.vertex
      newChoice.vertexDefective.1]
    exact newGammaRule.1
  have hcomponentOnly := TreeExitComponentMeetsTreeOnlyAtExit
    (corr.replacementSeries.data.tree newi.succ.castSucc)
    newSecond newGamma newChoice.color newChoice.vertex
    newSecondProper hnewGammaSecond newExit
  have hcomponentDistinct :
      TwoColorComponent G sigma available.gamma available.delta
          (Sum.inl newChoice.vertex) ≠
        TwoColorComponent G sigma available.gamma available.delta
          (Sum.inr available.edge) := by
    intro heq
    have hreturnExitSigma : Sum.inl available.returnVertex ∈
        TwoColorComponent G sigma available.gamma
          available.delta (Sum.inl newChoice.vertex) := by
      rw [heq]
      exact hreturnInQ
    have hreturnExitSecond : Sum.inl available.returnVertex ∈
        TwoColorComponent G newSecond newGamma newChoice.color
          (Sum.inl newChoice.vertex) := by
      unfold TwoColorComponent at hreturnExitSigma ⊢
      rw [← hsigmaExitGraph]
      exact hreturnExitSigma
    exact hreturnNeNew
      ((hcomponentOnly available.returnVertex
        (by simpa only [hnewIndex] using hreturnInNewEarlier)).mp
          hreturnExitSecond)
  exact @helper_continuation_3762 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@hlower)
      (@sigma) (@hsigmaProper) (@hsigmaOne) (@hsigmaStable) (@Tstar) (@hTnTstar) (@hstrict)
      (@fstar) (@seed) (@hfinalEdges) (@hadjoin) (@closureTree) (@hseedClosure) (@hTstarClosure)
      (@hTnClosure) (@hqSucc) (@hqCast) (@adjoined) (@previousProper) (@previousOneUncolored)
      (@previousClosed) (@available) (@currentStored) (@currentEdges) (@currentKind)
      (@hroundLarge) (@originalPrefix) (@hr) (@hprefixTrees) (@hprefixData) (@corr)
      (@hcorrFinalTree) (@hcorrFinalColor) (@hcorrMP) (@earlierPrefixBound) (@hearlierMap)
      (@hearlierPositive) (@hreplacementEarlierKind) (@oldi) (@oldChoice) (@oldGamma)
      (@holdTarget) (@newi) (@newChoice) (@newGamma) (@newCurrentDelta) (@newCurrentGamma)
      (@hnewIndex) (@htree) (@holdColorCast) (@hends) (@holdColorNe) (@hnewColorNe)
      (@hidentifiedDelta) (@hidentifiedGamma) (@holdDeltaAvailable) (@holdGammaAvailable)
      (@hnewDeltaAvailable) (@hnewGammaAvailable) (@hreplacementLastMap) (@hnewDeltaSigma)
      (@hgammaDeltaNe) (@hnewVertexTn) (@hpathComponent) (@hpathMeetsTn) (@hsigmaPrevStableQ)
      (@returnEdgeTransfer) (@hsigmaReturnIsPath) (@hsigmaReturnSupport) (@hreturnInQ)
      (@houtsideInQ) (@hreturnInNewEarlier) (@hreturnInTn) (@hcomponentDistinct)
theorem helper_continuation_2808.{u_1, u_2} :
    helperContinuation2808Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hpositive hlower sigma hsigmaProper hsigmaOne
      hsigmaStable Tstar hTnTstar hstrict fstar seed hfinalEdges hadjoin closureTree hseedClosure
      hTstarClosure hTnClosure q hqSucc hqCast adjoined previousProper previousOneUncolored
      previousClosed available currentStored currentEdges currentKind adjoinedExactly
      hsigmaPrevStable hroundLarge originalPrefix hr hprefixTrees hprefixData corr hcorrFinalTree
      hcorrFinalColor hcorrMP earlierPrefixBound earlierPrefix hearlierMap hearlierPositive
      hreplacementEarlierKind oldi oldChoice oldGamma oldCurrentStored holdTarget holdIndex newi
      newChoice newGamma newGammaRule newSecond newSecondProper newSecondStable newExit
      newCurrentColoring newCurrentDelta newCurrentGamma hnewTarget hnewIndex htree
      oldChoiceOnNew holdColorCast hends holdDeltaMissing holdColorNe hnewDeltaMissing
      hnewGammaNotMissing hnewColorNe hidentifiedDelta hidentifiedGamma holdDeltaAvailable
      holdGammaAvailable hnewDeltaAvailable hnewGammaAvailable hnewVertexOld holdColorConstant
      replacementLast hreplacementLastMap hreplacementColorConstant
  have hnewPostSigma :
      corr.replacementSeries.data.coloring newi.succ = sigma := by
    exact hreplacementColorConstant.symm.trans
      (by simpa [replacementLast] using hcorrFinalColor)
  have hnewDeltaSigma : available.delta ∈
      MissingColors G sigma newChoice.vertex := by
    have hm := hnewDeltaMissing
    rw [hnewDeltaAvailable] at hm
    exact Eq.mp (congrArg (fun phi => available.delta ∈
      MissingColors G phi newChoice.vertex) hnewPostSigma) hm
  have hnewGammaSigmaNot : available.gamma ∉
      MissingColors G sigma newChoice.vertex := by
    have hm := hnewGammaNotMissing
    rw [hnewGammaAvailable] at hm
    exact Eq.mp (congrArg (fun phi => available.gamma ∉
      MissingColors G phi newChoice.vertex) hnewPostSigma) hm
  have hgammaDeltaNe : available.gamma ≠ available.delta := by
    intro heq
    apply hnewColorNe
    rw [hnewGammaAvailable, hnewDeltaAvailable, heq]
  have stepSegment :=
    helper_stepSegment_2938 (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive)
        (@sigma) (@Tstar) (@adjoined) (@available) (@adjoinedExactly) (@hroundLarge)
        (@originalPrefix) (@hr) (@corr) (@earlierPrefixBound) (@oldi) (@oldChoice) (@oldGamma)
        (@newi) (@newChoice) (@newGamma) (@htree) (@holdColorCast) (@holdColorNe) (@hnewColorNe)
        (@hidentifiedDelta) (@hidentifiedGamma) (@holdDeltaAvailable) (@holdGammaAvailable)
  have segmentTrans :=
    @helper_segmentTrans_778 (@V) (@E) (@G) (@e0)
  have treeToFinal :=
    helper_treeToFinal_2987 (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive)
        (@sigma) (@Tstar) (@available) (@hroundLarge) (@originalPrefix) (@hr) (@corr)
        (@earlierPrefixBound) (@oldi) (@oldChoice) (@oldGamma) (@newi) (@newChoice) (@newGamma)
        (@htree) (@holdColorCast) (@holdColorNe) (@hnewColorNe) (@hidentifiedDelta)
        (@hidentifiedGamma) (@holdDeltaAvailable) (@holdGammaAvailable) (@stepSegment)
        (@segmentTrans)
  have hnewTreeFinal : TreeSequenceInitialSegment
      (corr.replacementSeries.data.tree newi.succ.castSucc)
      (corr.replacementSeries.data.tree
        (Fin.last (originalPrefix.rounds + 1))) := by
    apply treeToFinal (originalPrefix.rounds - newi.val)
    · simp
      omega
    · simp
  have hnewVertexTn :=
    helper_hnewVertexTn_1347 (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett)
        (@hpositive) (@sigma) (@originalPrefix) (@corr) (@hcorrFinalTree) (@newi) (@newChoice)
        (@hnewTreeFinal)
  have hgammaPresentSigma : available.gamma ∈
      PresentColors G sigma newChoice.vertex := by
    simpa [MissingColors] using hnewGammaSigmaNot
  obtain ⟨pathEdge, hpathEdgeIncident, hpathEdgeColor⟩ := by
    simpa only [PresentColors, Finset.mem_filter,
      Finset.mem_univ, true_and] using hgammaPresentSigma
  have hpathEdgeComponent : Sum.inr pathEdge ∈
      TwoColorComponent G sigma available.gamma available.delta
        (Sum.inl newChoice.vertex) := by
    apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    simp [TwoColorIncidenceGraph,
      hpathEdgeIncident, hpathEdgeColor]
  have hleafDegree : @SimpleGraph.degree _
      (TwoColorIncidenceGraph G sigma available.gamma
        available.delta) (Sum.inl newChoice.vertex)
      (Fintype.ofFinite _) ≤ 1 := by
    have hgraphSwapOrder :
        TwoColorIncidenceGraph G sigma available.delta
            available.gamma =
          TwoColorIncidenceGraph G sigma available.gamma
            available.delta := by
      ext x y
      cases x <;> cases y <;>
        simp [TwoColorIncidenceGraph, or_comm]
    rw [← hgraphSwapOrder]
    exact MissingColorIncidenceEndpoint G sigma available.delta
      available.gamma hgammaDeltaNe.symm hsigmaProper
      newChoice.vertex hnewDeltaSigma
  have hleaf : Set.Subsingleton
      ((TwoColorIncidenceGraph G sigma available.gamma
        available.delta).neighborSet
          (Sum.inl newChoice.vertex)) := by
    let : Fintype
        ((TwoColorIncidenceGraph G sigma available.gamma
          available.delta).neighborSet
            (Sum.inl newChoice.vertex)) := Fintype.ofFinite _
    rw [← SimpleGraph.card_neighborSet_eq_degree] at hleafDegree
    have hsub := Fintype.card_le_one_iff.mp hleafDegree
    intro a ha b hb
    exact congrArg Subtype.val
      (hsub ⟨a, ha⟩ ⟨b, hb⟩)
  have hpathComponent : TwoColorNontrivialPathComponent G sigma
      available.gamma available.delta
      (Sum.inl newChoice.vertex) := by
    refine ⟨⟨hgammaDeltaNe, Sum.inl newChoice.vertex, rfl,
      hleaf⟩, pathEdge, hpathEdgeComponent⟩
  have hpathMeetsTn : ∃ v ∈ TreeSequenceVertexSet
      (ett.series.data.tree (Fin.last ett.rounds).castSucc),
      Sum.inl v ∈ TwoColorComponent G sigma available.gamma
        available.delta (Sum.inl newChoice.vertex) :=
    ⟨newChoice.vertex, hnewVertexTn, rfl⟩
  have hsigmaPrevStableQ : StableColoring
      (ett.series.data.tree q.succ.castSucc)
      (TashkinovStoredColors ett.series.data q.castSucc)
      (ett.series.data.coloring q.castSucc) sigma := by
    rw [hqSucc]
    simpa [q] using hsigmaPrevStable
  have hgammaEarlierStored : available.gamma ∈
      ett.series.data.stored available.earlier := by
    rw [← holdIndex, oldCurrentStored, ← holdGammaAvailable]
    simp
  have hdeltaEarlierStored : available.delta ∈
      ett.series.data.stored available.earlier := by
    rw [← holdIndex, oldCurrentStored, ← holdDeltaAvailable]
    simp
  let previousPrefixIndex : Fin (originalPrefix.rounds + 2) :=
    ⟨originalPrefix.rounds, by omega⟩
  have hpreviousPrefixMap : Fin.castLE (by omega)
      previousPrefixIndex = q.castSucc.castSucc := by
    apply Fin.ext
    simp [previousPrefixIndex, q, hr]
  have hpreviousToTn : TreeSequenceInitialSegment
      (ett.series.data.tree q.castSucc.castSucc)
      (ett.series.data.tree q.succ.castSucc) := by
    have hseg := originalPrefix.abovePenultimate
    rw [hprefixTrees previousPrefixIndex] at hseg
    rw [hpreviousPrefixMap] at hseg
    simpa [hqSucc] using hseg
  have missingPreviousToTn (c : Fin k)
      (hc : c ∈ TreeMissingColors
        (ett.series.data.coloring q.castSucc)
        (ett.series.data.tree q.castSucc.castSucc)) :=
    helper_missingPreviousToTn_1435 (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett)
        (@hpositive) (@Tstar) (@hpreviousToTn) (@c) (@hc)
  have colorControlAtQ (c : Fin k)
      (hc : c ∈ ett.series.data.stored available.earlier) :
      c ∈ TreeMissingColors (ett.series.data.coloring q.castSucc)
            (ett.series.data.tree q.succ.castSucc) ∪
          TashkinovStoredColors ett.series.data q.castSucc := by
    by_cases hm : c ∈ TreeMissingColors
        (ett.series.data.coloring q.castSucc)
        (ett.series.data.tree q.castSucc.castSucc)
    · exact Finset.mem_union_left _ (missingPreviousToTn c hm)
    · apply Finset.mem_union_right
      unfold TashkinovStoredColors
      have hqne : q.castSucc.val ≠ 0 := by
        change ett.rounds - 1 ≠ 0
        omega
      rw [ite_eq_right hqne]
      rw [Finset.mem_sdiff]
      refine ⟨?_, hm⟩
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
      refine ⟨available.earlier, ?_⟩
      rw [ite_eq_left]
      · exact hc
      · exact available.earlierAtMost
  exact helper_continuation_3509 (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive)
      (@hlower) (@sigma) (@hsigmaProper) (@hsigmaOne) (@hsigmaStable) (@Tstar) (@hTnTstar)
      (@hstrict) (@fstar) (@seed) (@hfinalEdges) (@hadjoin) (@closureTree) (@hseedClosure)
      (@hTstarClosure) (@hTnClosure) (@hqSucc) (@hqCast) (@adjoined) (@previousProper)
      (@previousOneUncolored) (@previousClosed) (@available) (@currentStored) (@currentEdges)
      (@currentKind) (@hroundLarge) (@originalPrefix) (@hr) (@hprefixTrees) (@hprefixData)
      (@corr) (@hcorrFinalTree) (@hcorrFinalColor) (@hcorrMP) (@earlierPrefixBound)
      (@hearlierMap) (@hearlierPositive) (@hreplacementEarlierKind) (@oldi) (@oldChoice)
      (@oldGamma) (@holdTarget) (@holdIndex) (@newi) (@newChoice) (@newGamma) (@newGammaRule)
      (@newSecond) (@newSecondProper) (@newSecondStable) (@newExit) (@newCurrentColoring)
      (@newCurrentDelta) (@newCurrentGamma) (@hnewIndex) (@htree) (@holdColorCast) (@hends)
      (@holdDeltaMissing) (@holdColorNe) (@hnewColorNe) (@hidentifiedDelta) (@hidentifiedGamma)
      (@holdDeltaAvailable) (@holdGammaAvailable) (@hnewDeltaAvailable) (@hnewGammaAvailable)
      (@hnewVertexOld) (@holdColorConstant) (@hreplacementLastMap) (@hnewPostSigma)
      (@hnewDeltaSigma) (@hgammaDeltaNe) (@hnewTreeFinal) (@hnewVertexTn) (@hpathComponent)
      (@hpathMeetsTn) (@hsigmaPrevStableQ) (@hgammaEarlierStored) (@hdeltaEarlierStored)
      (@colorControlAtQ)
theorem helper_caseContinuation_2517.{u_1, u_2} :
    helperCaseContinuation2517Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hpositive hlower sigma hsigmaProper hsigmaOne
      hsigmaStable Tstar hTnTstar hstrict fstar seed hfinalEdges hadjoin closureTree hseedClosure
      hTstarClosure hTnClosure q hqSucc hqCast adjoined previousProper previousOneUncolored
      previousClosed available currentStored currentEdges currentKind adjoinedExactly
      hsigmaPrevStable hroundLarge originalPrefix hr hprefixTrees hprefixData corr hcorrFinalTree
      hcorrFinalColor hcorrMP earlierPrefixBound earlierPrefix hearlierMap hearlierPositive
      hreplacementEarlierKind oldi oldChoice oldGamma oldSecond oldCurrentColoring
      oldCurrentStored oldCurrentDelta oldCurrentGamma holdTarget holdIndex newi newChoice
      newGamma newGammaRule newSecond newSecondProper newSecondStable newExit newCurrentColoring
      newCurrentDelta newCurrentGamma hnewTarget hnewIndex htree oldChoiceOnNew holdVertexCast
      holdOtherCast holdColorCast hedgePairs hcolorPairs hends hvertexIdentity pePostStatus
      holdDeltaMissing holdGammaNotMissing holdColorNe
  obtain ⟨hnewDeltaMissing, hnewGammaNotMissing, hnewColorNe⟩ :=
    pePostStatus
      (corr.replacementSeries.data.tree newi.succ.castSucc)
      (TashkinovStoredColors corr.replacementSeries.data
        newi.castSucc)
      (corr.replacementSeries.data.coloring newi.castSucc)
      newChoice newGamma newSecond newSecondProper
      newSecondStable newGammaRule.1
  rw [← oldCurrentColoring] at holdDeltaMissing holdGammaNotMissing
  rw [← newCurrentColoring] at hnewDeltaMissing hnewGammaNotMissing
  have hbaseTree : originalPrefix.series.data.tree
      newi.succ.castSucc =
        ett.series.data.tree oldi.succ.castSucc := by
    exact @helper_hbaseTree_1084 (@V) (@E) inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett)
        (@hpositive) (@sigma) (@originalPrefix) (@corr) (@oldi) (@newi) (@htree)
  have hbaseColor : originalPrefix.series.data.coloring
      newi.succ = ett.series.data.coloring oldi.succ := by
    calc
      originalPrefix.series.data.coloring newi.succ =
          ett.series.data.coloring
            (Fin.castLE (by omega) newi.succ) :=
        (hprefixData newi.succ).1
      _ = ett.series.data.coloring oldi.succ := by
        congr 1
        apply Fin.ext
        have hvalsOld := congrArg Fin.val holdIndex
        have hvalsNew := congrArg Fin.val hnewIndex
        have hvalsMap := congrArg Fin.val hearlierMap
        simp only [Fin.val_succ] at hvalsOld hvalsNew
        simp only [Fin.val_castLE] at hvalsMap ⊢
        omega
  have hmissingSameVertex : MissingColors G
      (ett.series.data.coloring oldi.succ) oldChoice.vertex =
        MissingColors G
          (corr.replacementSeries.data.coloring newi.succ)
          oldChoice.vertex := by
    exact @helper_hmissingSameVertex_1108 (@V) (@E) inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett)
        (@hpositive) (@sigma) (@originalPrefix) (@corr) (@oldi) (@oldChoice)
        (@newi) (@hbaseTree) (@hbaseColor)
  have hmissingForIdentification : MissingColors G
      (ett.series.data.coloring oldi.succ)
        oldChoiceOnNew.vertex =
      MissingColors G
        (corr.replacementSeries.data.coloring newi.succ)
        newChoice.vertex := by
    calc
      MissingColors G (ett.series.data.coloring oldi.succ)
          oldChoiceOnNew.vertex =
          MissingColors G (ett.series.data.coloring oldi.succ)
            oldChoice.vertex := congrArg _ holdVertexCast
      _ = MissingColors G
            (corr.replacementSeries.data.coloring newi.succ)
            oldChoice.vertex := hmissingSameVertex
      _ = MissingColors G
            (corr.replacementSeries.data.coloring newi.succ)
            newChoice.vertex := congrArg _
              (hvertexIdentity.trans holdVertexCast).symm
  have holdDeltaForIdentification : oldChoiceOnNew.color ∈
      MissingColors G (ett.series.data.coloring oldi.succ)
        oldChoiceOnNew.vertex := by
    simpa only [holdColorCast, holdVertexCast] using
      holdDeltaMissing
  have holdGammaForIdentification : oldGamma ∉
      MissingColors G (ett.series.data.coloring oldi.succ)
        oldChoiceOnNew.vertex := by
    simpa only [holdVertexCast] using holdGammaNotMissing
  have hidentified := TdEarlierPEWitnessIdentification G k e0
    (corr.replacementSeries.data.tree newi.succ.castSucc)
    (TashkinovStoredColors ett.series.data oldi.castSucc)
    (TashkinovStoredColors corr.replacementSeries.data
      newi.castSucc)
    (ett.series.data.coloring oldi.castSucc)
    (corr.replacementSeries.data.coloring newi.castSucc)
    oldChoiceOnNew newChoice oldGamma newGamma
    (ett.series.data.coloring oldi.succ)
    (corr.replacementSeries.data.coloring newi.succ)
    hedgePairs hcolorPairs hmissingForIdentification
    holdDeltaForIdentification holdGammaForIdentification
    hnewDeltaMissing hnewGammaNotMissing
  rcases hidentified with ⟨hidentifiedEdge, hidentifiedVertex,
    hidentifiedOther, hidentifiedDelta, hidentifiedGamma⟩
  have holdDeltaAvailable : oldChoice.color = available.delta := by
    exact Option.some.inj (oldCurrentDelta.symm.trans
      ((congrArg ett.series.data.delta holdIndex).trans
        available.earlierDelta))
  have holdGammaAvailable : oldGamma = available.gamma := by
    exact Option.some.inj (oldCurrentGamma.symm.trans
      ((congrArg ett.series.data.gamma holdIndex).trans
        available.earlierGamma))
  have hnewDeltaAvailable : newChoice.color = available.delta := by
    exact hidentifiedDelta.trans
      (holdColorCast.trans holdDeltaAvailable)
  have hnewGammaAvailable : newGamma = available.gamma := by
    exact hidentifiedGamma.trans holdGammaAvailable
  have hnewVertexOld : newChoice.vertex = oldChoice.vertex :=
    hidentifiedVertex.trans holdVertexCast
  have hnewOtherOld : newChoice.otherEndpoint =
      oldChoice.otherEndpoint :=
    hidentifiedOther.trans holdOtherCast
  have reStepColoring : ∀ {rounds' : ℕ}
      {input' : PartialEdgeColoring E k}
      (series : TashkinovSeries G k rounds' e0 input')
      (j : Fin rounds'),
      series.data.kind j.succ = some TashkinovExtensionKind.RE →
      series.data.coloring j.succ =
        series.data.coloring j.castSucc := by
    exact @helper_reStepColoring_2269 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@Tstar) (@adjoined)
        (@available) (@adjoinedExactly) (@hroundLarge) (@originalPrefix) (@hr) (@corr) (@oldi)
        (@oldChoice) (@oldGamma) (@newi) (@newChoice) (@newGamma) (@htree)
  have reIntervalColoring : ∀ {rounds' : ℕ}
      {input' : PartialEdgeColoring E k}
      (series : TashkinovSeries G k rounds' e0 input')
      (a b : Fin (rounds' + 1)),
      a.val ≤ b.val →
      (∀ j : Fin (rounds' + 1), a.val < j.val →
        j.val ≤ b.val →
        series.data.kind j = some TashkinovExtensionKind.RE) →
      series.data.coloring b = series.data.coloring a := by
    exact @helper_reIntervalColoring_2281 (@V) (@E) inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@Tstar)
        (@available) (@hroundLarge) (@originalPrefix) (@hr) (@corr) (@oldi) (@oldChoice)
        (@oldGamma) (@newi) (@newChoice) (@newGamma) (@htree) (@reStepColoring)
  have holdColorConstant : ett.series.data.coloring q.castSucc =
      ett.series.data.coloring oldi.succ := by
    exact @helper_holdColorConstant_2295 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@Tstar) (@hqCast)
        (@available) (@hroundLarge) (@originalPrefix) (@hr) (@corr) (@oldi) (@oldChoice)
        (@oldGamma) (@holdTarget) (@holdIndex) (@newi) (@newChoice) (@newGamma) (@htree)
        (@reIntervalColoring)
  let replacementLast : Fin (originalPrefix.rounds + 1) :=
    Fin.last originalPrefix.rounds
  have hreplacementLastMap : Fin.castLE (by omega)
      replacementLast = q.castSucc := by
    apply Fin.ext
    simp [replacementLast, q, hr]
  have hreplacementColorConstant :
      corr.replacementSeries.data.coloring replacementLast =
        corr.replacementSeries.data.coloring newi.succ := by
    apply reIntervalColoring corr.replacementSeries newi.succ
      replacementLast
    · have hvals := congrArg Fin.val hnewIndex
      simp [replacementLast] at hvals ⊢
    · intro j hjLower hjUpper
      rw [corr.extensionKindsAgree j,
        (hprefixData j).2.2.2.1]
      apply available.interveningRevisiting
        (Fin.castLE (by omega) j)
      · simp only [Fin.val_castLE]
        omega
      · have hvalsNew := congrArg Fin.val hnewIndex
        have hvalsMap := congrArg Fin.val hearlierMap
        simp only [Fin.val_succ] at hvalsNew
        simp only [Fin.val_castLE] at hvalsMap ⊢
        omega
      · have hvalsLast := congrArg Fin.val hreplacementLastMap
        simp only [Fin.val_castLE] at hvalsLast ⊢
        omega
  exact @helper_continuation_2808 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@hlower)
      (@sigma) (@hsigmaProper) (@hsigmaOne) (@hsigmaStable) (@Tstar) (@hTnTstar) (@hstrict)
      (@fstar) (@seed) (@hfinalEdges) (@hadjoin) (@closureTree) (@hseedClosure) (@hTstarClosure)
      (@hTnClosure) (@hqSucc) (@hqCast) (@adjoined) (@previousProper) (@previousOneUncolored)
      (@previousClosed) (@available) (@currentStored) (@currentEdges) (@currentKind)
      (@adjoinedExactly) (@hsigmaPrevStable) (@hroundLarge) (@originalPrefix) (@hr)
      (@hprefixTrees) (@hprefixData) (@corr) (@hcorrFinalTree) (@hcorrFinalColor) (@hcorrMP)
      (@earlierPrefixBound) (@hearlierMap) (@hearlierPositive) (@hreplacementEarlierKind) (@oldi)
      (@oldChoice) (@oldGamma) (@oldCurrentStored) (@holdTarget) (@holdIndex) (@newi)
      (@newChoice) (@newGamma) (@newGammaRule) (@newSecond) (@newSecondProper) (@newSecondStable)
      (@newExit) (@newCurrentColoring) (@newCurrentDelta) (@newCurrentGamma) (@hnewTarget)
      (@hnewIndex) (@htree) (@holdColorCast) (@hends) (@holdDeltaMissing) (@holdColorNe)
      (@hnewDeltaMissing) (@hnewGammaNotMissing) (@hnewColorNe) (@hidentifiedDelta)
      (@hidentifiedGamma) (@holdDeltaAvailable) (@holdGammaAvailable) (@hnewDeltaAvailable)
      (@hnewGammaAvailable) (@hnewVertexOld) (@holdColorConstant) (@hreplacementLastMap)
      (@hreplacementColorConstant)
theorem helper_branch_4795.{u_1, u_2} :
    helperBranch4795Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hpositive hlower sigma hsigmaProper hsigmaOne
      hsigmaStable Tstar hTnTstar hstrict fstar seed hfinalEdges hadjoin closureTree hseedClosure
      hTstarClosure hTnClosure q hqSucc hqCast adjoined previousProper previousOneUncolored
      previousClosed available currentStored currentEdges currentKind adjoinedExactly
      hsigmaPrevStable hroundLarge originalPrefix hr hprefixTrees hprefixData corr hcorrFinalTree
      hcorrFinalColor hcorrMP earlierPrefixBound earlierPrefix hearlierMap hearlierPositive
      hreplacementEarlierKind oldi oldChoice oldGamma oldGammaRule oldSecond oldSecondProper
      oldSecondStable oldCurrentColoring oldCurrentStored oldCurrentEdges oldCurrentDelta
      oldCurrentGamma holdTarget holdIndex newi newChoice newGamma newGammaRule newSecond
      newSecondProper newSecondStable newExit newCurrentColoring newCurrentStored newCurrentEdges
      newCurrentDelta newCurrentGamma hnewTarget
  have hnewIndex : newi.succ = earlierPrefix := by
    simpa using hnewTarget.symm
  have htree :
      corr.replacementSeries.data.tree newi.succ.castSucc =
        ett.series.data.tree oldi.succ.castSucc := by
    calc
      corr.replacementSeries.data.tree newi.succ.castSucc =
          originalPrefix.series.data.tree newi.succ.castSucc :=
        corr.ladderTreesAgree newi
      _ = ett.series.data.tree
            (Fin.castLE (by omega) newi.succ.castSucc) :=
        hprefixTrees newi.succ.castSucc
      _ = ett.series.data.tree oldi.succ.castSucc := by
        congr 1
        apply Fin.ext
        have hvalsOld := congrArg Fin.val holdIndex
        have hvalsNew := congrArg Fin.val hnewIndex
        have hvalsMap := congrArg Fin.val hearlierMap
        simp only [Fin.val_succ] at hvalsOld hvalsNew
        simp only [Fin.val_castLE] at hvalsMap
        simp only [Fin.val_castLE, Fin.val_castSucc]
        omega
  let oldChoiceOnNew : MaximumDefectiveChoice G e0
      (corr.replacementSeries.data.tree newi.succ.castSucc)
      (TashkinovStoredColors ett.series.data oldi.castSucc)
      (ett.series.data.coloring oldi.castSucc) :=
    transportDefectiveChoice htree.symm oldChoice
  have transportChoiceFields : ∀
      {A B : TreeSequence G e0} (hAB : A = B)
      (C : Finset (Fin k)) (phi : PartialEdgeColoring E k)
      (ch : MaximumDefectiveChoice G e0 A C phi),
      (hAB ▸ ch).edge = ch.edge ∧
        (hAB ▸ ch).vertex = ch.vertex ∧
        (hAB ▸ ch).otherEndpoint = ch.otherEndpoint ∧
        (hAB ▸ ch).color = ch.color := by
    intro A B hAB C phi ch
    subst B
    exact ⟨rfl, rfl, rfl, rfl⟩
  have htransport := transportChoiceFields htree.symm
    (TashkinovStoredColors ett.series.data oldi.castSucc)
    (ett.series.data.coloring oldi.castSucc) oldChoice
  have holdEdgeCast : oldChoiceOnNew.edge = oldChoice.edge := by
    exact htransport.1
  have holdVertexCast : oldChoiceOnNew.vertex = oldChoice.vertex := by
    exact htransport.2.1
  have holdOtherCast : oldChoiceOnNew.otherEndpoint =
      oldChoice.otherEndpoint := by
    exact htransport.2.2.1
  have holdColorCast : oldChoiceOnNew.color = oldChoice.color := by
    exact htransport.2.2.2
  have hdataEdges : corr.replacementSeries.data.connectingEdges
      earlierPrefix =
        ett.series.data.connectingEdges available.earlier := by
    calc
      corr.replacementSeries.data.connectingEdges earlierPrefix =
          originalPrefix.series.data.connectingEdges earlierPrefix :=
        corr.connectingEdgesAgree earlierPrefix
      _ = ett.series.data.connectingEdges
            (Fin.castLE (by omega) earlierPrefix) :=
        (hprefixData earlierPrefix).2.2.1
      _ = ett.series.data.connectingEdges available.earlier := by
        rw [hearlierMap]
  have hdataStored : corr.replacementSeries.data.stored
      earlierPrefix = ett.series.data.stored available.earlier := by
    calc
      corr.replacementSeries.data.stored earlierPrefix =
          originalPrefix.series.data.stored earlierPrefix :=
        corr.storedColorsAgree earlierPrefix
      _ = ett.series.data.stored
            (Fin.castLE (by omega) earlierPrefix) :=
        (hprefixData earlierPrefix).2.1
      _ = ett.series.data.stored available.earlier := by
        rw [hearlierMap]
  have hedgePairs : ({oldChoiceOnNew.edge} : Finset E) =
      {newChoice.edge} := by
    have holdEdges : ett.series.data.connectingEdges
        available.earlier = {oldChoice.edge} := by
      simpa only [holdIndex] using oldCurrentEdges
    have hnewEdges : corr.replacementSeries.data.connectingEdges
        earlierPrefix = {newChoice.edge} := by
      simpa only [hnewIndex] using newCurrentEdges
    simpa only [holdEdgeCast] using
      holdEdges.symm.trans (hdataEdges.symm.trans hnewEdges)
  have hcolorPairs :
      ({oldChoiceOnNew.color, oldGamma} : Finset (Fin k)) =
        {newChoice.color, newGamma} := by
    have holdStored : ett.series.data.stored available.earlier =
        {oldChoice.color, oldGamma} := by
      simpa only [holdIndex] using oldCurrentStored
    have hnewStored : corr.replacementSeries.data.stored
        earlierPrefix = {newChoice.color, newGamma} := by
      simpa only [hnewIndex] using newCurrentStored
    simpa only [holdColorCast] using
      holdStored.symm.trans (hdataStored.symm.trans hnewStored)
  have hedgeIdentity : newChoice.edge = oldChoiceOnNew.edge := by
    apply Finset.mem_singleton.mp
    rw [hedgePairs]
    exact Finset.mem_singleton_self _
  have hends : s(oldChoiceOnNew.vertex,
        oldChoiceOnNew.otherEndpoint) =
      s(newChoice.vertex, newChoice.otherEndpoint) := by
    calc
      s(oldChoiceOnNew.vertex, oldChoiceOnNew.otherEndpoint) =
          G.ends oldChoiceOnNew.edge := oldChoiceOnNew.edgeEnds.symm
      _ = G.ends newChoice.edge := congrArg G.ends hedgeIdentity.symm
      _ = s(newChoice.vertex, newChoice.otherEndpoint) :=
        newChoice.edgeEnds
  have hvertexIdentity : newChoice.vertex =
      oldChoiceOnNew.vertex := by
    rcases Sym2.eq_iff.mp hends with hstraight | hcross
    · exact hstraight.1.symm
    · exfalso
      exact newChoice.otherOutside
        (hcross.1 ▸ oldChoiceOnNew.vertexDefective.1)
  have hotherIdentity : newChoice.otherEndpoint =
      oldChoiceOnNew.otherEndpoint := by
    rcases Sym2.eq_iff.mp hends with hstraight | hcross
    · exact hstraight.2.symm
    · exfalso
      exact oldChoiceOnNew.otherOutside
        (hcross.2 ▸ newChoice.vertexDefective.1)
  have pePostStatus :=
    helper_pePostStatus_2097 (@G) (@k) (@e0)
  obtain ⟨holdDeltaMissing, holdGammaNotMissing, holdColorNe⟩ :=
    pePostStatus
      (ett.series.data.tree oldi.succ.castSucc)
      (TashkinovStoredColors ett.series.data oldi.castSucc)
      (ett.series.data.coloring oldi.castSucc) oldChoice oldGamma
      oldSecond oldSecondProper oldSecondStable oldGammaRule.1
  exact helper_caseContinuation_2517 (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett)
      (@hpositive) (@hlower) (@sigma) (@hsigmaProper) (@hsigmaOne) (@hsigmaStable) (@Tstar)
      (@hTnTstar) (@hstrict) (@fstar) (@seed) (@hfinalEdges) (@hadjoin) (@closureTree)
      (@hseedClosure) (@hTstarClosure) (@hTnClosure) (@hqSucc) (@hqCast) (@adjoined)
      (@previousProper) (@previousOneUncolored) (@previousClosed) (@available) (@currentStored)
      (@currentEdges) (@currentKind) (@adjoinedExactly) (@hsigmaPrevStable) (@hroundLarge)
      (@originalPrefix) (@hr) (@hprefixTrees) (@hprefixData) (@corr) (@hcorrFinalTree)
      (@hcorrFinalColor) (@hcorrMP) (@earlierPrefixBound) (@hearlierMap) (@hearlierPositive)
      (@hreplacementEarlierKind) (@oldi) (@oldChoice) (@oldGamma) (@oldSecond)
      (@oldCurrentColoring) (@oldCurrentStored) (@oldCurrentDelta) (@oldCurrentGamma)
      (@holdTarget) (@holdIndex) (@newi) (@newChoice) (@newGamma) (@newGammaRule) (@newSecond)
      (@newSecondProper) (@newSecondStable) (@newExit) (@newCurrentColoring) (@newCurrentDelta)
      (@newCurrentGamma) (@hnewTarget) (@hnewIndex) (@htree) (@holdVertexCast) (@holdOtherCast)
      (@holdColorCast) (@hedgePairs) (@hcolorPairs) (@hends) (@hvertexIdentity) (@pePostStatus)
      (@holdDeltaMissing) (@holdGammaNotMissing) (@holdColorNe)

theorem helper_branch_5611.{u_1, u_2} :
    helperBranch5611Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hpositive hlower sigma hsigmaProper hsigmaOne
      hsigmaStable Tstar hTnTstar hstrict fstar seed hfinalEdges hadjoin closureTree hseedClosure
      hTstarClosure hTnClosure q hqSucc hqCast adjoined previousProper previousOneUncolored
      previousClosed available currentStored currentEdges currentKind adjoinedExactly
      hsigmaPrevStable hpositivePrefix
  rcases hpositivePrefix with ⟨hroundLarge, originalPrefix, hr,
      hprefixMP, hprefixTrees, hprefixData, corr, hcorrFinalTree,
      hcorrFinalColor, hcorrMP⟩
  have earlierPrefixBound : available.earlier.val < originalPrefix.rounds + 1 := by
    rw [hr]
    have hle := available.earlierAtMost
    change available.earlier.val ≤ q.castSucc.val at hle
    simp [q] at hle ⊢
    omega
  let earlierPrefix : Fin (originalPrefix.rounds + 1) :=
    ⟨available.earlier.val, earlierPrefixBound⟩
  have hearlierMap : Fin.castLE (by omega) earlierPrefix =
      available.earlier := by
    apply Fin.ext
    rfl
  have hearlierPositive : 0 < earlierPrefix.val :=
    available.earlierPositive
  have hprefixEarlierKind : originalPrefix.series.data.kind
      earlierPrefix = some TashkinovExtensionKind.PE := by
    rw [(hprefixData earlierPrefix).2.2.2.1, hearlierMap]
    exact available.earlierPE
  have hreplacementEarlierKind : corr.replacementSeries.data.kind
      earlierPrefix = some TashkinovExtensionKind.PE := by
    rw [corr.extensionKindsAgree earlierPrefix]
    exact hprefixEarlierKind
  have holdStep := ett.series.certified available.earlier
  generalize holdTarget : available.earlier = oldTarget at holdStep
  cases holdStep with
  | initial tripleOld seedLengthOld initialColoringOld initialStoredOld
      initialEdgesOld initialKindOld initialVertexOld initialOutsideOld
      initialDeltaOld initialGammaOld initialClosureOld =>
      have hbad := initialKindOld.symm.trans
        (by simpa [holdTarget] using available.earlierPE)
      simp at hbad
  | SE oldi oldPreviousProper oldPreviousOne oldPreviousClosed
      oldPreviousNotStrong oldNoRE oldChoice oldAlternative
      oldCurrentColoring oldCurrentStored oldCurrentEdges oldCurrentKind
      oldCurrentVertex oldCurrentOutside oldCurrentDelta oldCurrentGamma
      oldAdjoined oldAdjoinedExactly oldClosedExtension
      oldOrderedExtension oldStrictExtension =>
      have hbad := oldCurrentKind.symm.trans
        (by simpa [holdTarget] using available.earlierPE)
      cases hbad
  | RE oldi oldPreviousProper oldPreviousOne oldPreviousClosed
      oldPreviousNotStrong oldAvailable oldCurrentColoring
      oldCurrentStored oldCurrentEdges oldCurrentKind oldCurrentVertex
      oldCurrentOutside oldCurrentDelta oldCurrentGamma oldAdjoined
      oldAdjoinedExactly oldClosedExtension oldOrderedExtension
      oldStrictExtension =>
      have hbad := oldCurrentKind.symm.trans
        (by simpa [holdTarget] using available.earlierPE)
      cases hbad
  | PE oldi oldPreviousProper oldPreviousOne oldPreviousClosed
      oldPreviousNotStrong oldNoRE oldChoice oldAlternativeFails oldGamma
      oldGammaRule oldSecond oldSecondProper oldSecondOne
      oldSecondStable oldExit oldCurrentColoring oldCurrentProper
      oldCurrentOne oldCurrentStored oldCurrentEdges oldCurrentKind
      oldCurrentVertex oldCurrentOutside oldCurrentDelta oldCurrentGamma
      oldClosedExtension oldOrderedExtension oldStrictExtension =>
      have holdIndex : oldi.succ = available.earlier := by
        simpa using holdTarget.symm
      have hnewStep := corr.replacementSeries.certified earlierPrefix
      generalize hnewTarget : earlierPrefix = newTarget at hnewStep
      cases hnewStep with
      | initial tripleNew seedLengthNew initialColoringNew initialStoredNew
          initialEdgesNew initialKindNew initialVertexNew initialOutsideNew
          initialDeltaNew initialGammaNew initialClosureNew =>
          have hbad := initialKindNew.symm.trans
            (by simpa [hnewTarget] using hreplacementEarlierKind)
          simp at hbad
      | SE newi newPreviousProper newPreviousOne newPreviousClosed
          newPreviousNotStrong newNoRE newChoice newAlternative
          newCurrentColoring newCurrentStored newCurrentEdges
          newCurrentKind newCurrentVertex newCurrentOutside
          newCurrentDelta newCurrentGamma newAdjoined
          newAdjoinedExactly newClosedExtension newOrderedExtension
          newStrictExtension =>
          have hbad := newCurrentKind.symm.trans
            (by simpa [hnewTarget] using hreplacementEarlierKind)
          cases hbad
      | RE newi newPreviousProper newPreviousOne newPreviousClosed
          newPreviousNotStrong newAvailable newCurrentColoring
          newCurrentStored newCurrentEdges newCurrentKind
          newCurrentVertex newCurrentOutside newCurrentDelta
          newCurrentGamma newAdjoined newAdjoinedExactly
          newClosedExtension newOrderedExtension newStrictExtension =>
          have hbad := newCurrentKind.symm.trans
            (by simpa [hnewTarget] using hreplacementEarlierKind)
          cases hbad
      | PE newi newPreviousProper newPreviousOne newPreviousClosed
          newPreviousNotStrong newNoRE newChoice newAlternativeFails
          newGamma newGammaRule newSecond newSecondProper newSecondOne
          newSecondStable newExit newCurrentColoring newCurrentProper
          newCurrentOne newCurrentStored newCurrentEdges newCurrentKind
          newCurrentVertex newCurrentOutside newCurrentDelta
          newCurrentGamma newClosedExtension newOrderedExtension
          newStrictExtension =>
              exact @helper_branch_4795 (@V) (@E) inferInstance inferInstance inferInstance
                  inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett)
                  (@hpositive) (@hlower) (@sigma) (@hsigmaProper) (@hsigmaOne)
                  (@hsigmaStable) (@Tstar) (@hTnTstar) (@hstrict) (@fstar) (@seed)
                  (@hfinalEdges) (@hadjoin) (@closureTree) (@hseedClosure) (@hTstarClosure)
                  (@hTnClosure) (@hqSucc) (@hqCast) (@adjoined) (@previousProper)
                  (@previousOneUncolored) (@previousClosed) (@available) (@currentStored)
                  (@currentEdges) (@currentKind) (@adjoinedExactly) (@hsigmaPrevStable)
                  (@hroundLarge) (@originalPrefix) (@hr) (@hprefixTrees) (@hprefixData)
                  (@corr) (@hcorrFinalTree) (@hcorrFinalColor) (@hcorrMP)
                  (@earlierPrefixBound) (@hearlierMap) (@hearlierPositive)
                  (@hreplacementEarlierKind) (@oldi) (@oldChoice) (@oldGamma)
                  (@oldGammaRule) (@oldSecond) (@oldSecondProper) (@oldSecondStable)
                  (@oldCurrentColoring) (@oldCurrentStored) (@oldCurrentEdges)
                  (@oldCurrentDelta) (@oldCurrentGamma) (@holdTarget) (@holdIndex) (@newi)
                  (@newChoice) (@newGamma) (@newGammaRule) (@newSecond) (@newSecondProper)
                  (@newSecondStable) (@newExit) (@newCurrentColoring) (@newCurrentStored)
                  (@newCurrentEdges) (@newCurrentDelta) (@newCurrentGamma) (@hnewTarget)

end GoldbergSeymour.TerminalRebuild

namespace GoldbergSeymour

open TerminalRebuild

theorem TdTerminalRERebuild {V E : Type*} [Fintype V] [Fintype E]
     [DecidableEq E] (G : LooplessMultigraph V E)
    (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
    (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hMP : MaximumProperty ett)
    (hpositive : 0 < ett.rounds)
    (hlower : LowerRoundInductionHypothesis G k e0 ett.rounds) :
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  ett.series.data.kind n = some TashkinovExtensionKind.RE →
  let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc
  ∀ sigma : PartialEdgeColoring E k,
  IsProperEdgeColoring G sigma →
  IsOneEdgeUncolored sigma e0 →
  StableColoring Tn
    (TashkinovStoredColors ett.series.data n)
    (ett.series.data.coloring n) sigma →
  ModColoring ett sigma := by
  classical
  dsimp
  intro hterminalRE sigma hsigmaProper hsigmaOne hsigmaStable
  refine ⟨hsigmaProper, hsigmaOne, ?_⟩
  intro Tstar hTnTstar hstrict heligible
  rcases heligible with hparallel | hre
  · rw [hterminalRE] at hparallel
    simp at hparallel
  rcases hre with ⟨hkind, fstar, seed, hfinalEdges, hadjoin, hroute⟩
  obtain ⟨closureTree, hclosure⟩ :=
    TashkinovClosureExists sigma Tstar
  have hrouteClosure : TashkinovAugmentationSequence sigma seed closureTree :=
    hroute.trans hclosure.1
  have hseedClosure : TashkinovClosure sigma seed closureTree :=
    ⟨hrouteClosure, hclosure.2⟩
  have hTstarClosure : TreeSequenceInitialSegment Tstar closureTree :=
    TashkinovAugmentationSequenceInitialSegment sigma Tstar closureTree hclosure.1
  have hTnClosure : TreeSequenceInitialSegment
      (ett.series.data.tree (Fin.last ett.rounds).castSucc) closureTree := by
    exact @helper_hTnClosure_110 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
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
  | SE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
      have hbad := currentKind.symm.trans (by simpa [htarget] using hterminalRE)
      cases hbad
  | PE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper secondStableOneUncolored
      secondStableRelation exitWitness currentColoring currentProper
      currentOneUncolored currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma closedExtension orderedExtension
      strictExtension =>
      have hbad := currentKind.symm.trans (by simpa [htarget] using hterminalRE)
      cases hbad
  | RE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
      have hi : i = q := by
        exact @helper_hi_768 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
            (@input) (@T) (@generating) (@ett) (@hpositive) (@Tstar) (@i) (@htarget)
      subst i
      have hreKind : ett.series.data.kind q.succ =
          some TashkinovExtensionKind.RE := by
        simpa [htarget] using currentKind
      have hprefix := TdReplacementPrefixExact G k e0 input T generating ett
        hMP hpositive hlower sigma hsigmaProper hsigmaOne
        (by simpa [hqSucc] using hsigmaStable)
      obtain ⟨sigmaPrev, hsigmaPrevProper, hsigmaPrevOne,
          hsigmaPrevStable, hsigmaPrevEq, hparallelPrev, hprefixCases⟩ := hprefix
      have hsigmaPrevSigma : sigmaPrev = sigma :=
        hsigmaPrevEq (Or.inr (by simpa [hqSucc] using hreKind))
      subst sigmaPrev
      rcases hprefixCases with hzero | hpositivePrefix
      · exact @helper_branch_787 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
          (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@Tstar) (@hqCast)
          (@available) (@hzero)
      · exact @helper_branch_5611 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
          (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@hlower) (@sigma)
          (@hsigmaProper) (@hsigmaOne) (@hsigmaStable) (@Tstar) (@hTnTstar) (@hstrict) (@fstar)
          (@seed) (@hfinalEdges) (@hadjoin) (@closureTree) (@hseedClosure) (@hTstarClosure)
          (@hTnClosure) (@hqSucc) (@hqCast) (@adjoined) (@previousProper) (@previousOneUncolored)
          (@previousClosed) (@available) (@currentStored) (@currentEdges) (@currentKind)
          (@adjoinedExactly) (@hsigmaPrevStable) (@hpositivePrefix)

end GoldbergSeymour

end
