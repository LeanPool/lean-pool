/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.Basic2
public import LeanPool.GoldbergSeymour.PositivePrefixNoRevisiting
public import LeanPool.GoldbergSeymour.TdEarlierPEWitnessIdentification
public import LeanPool.GoldbergSeymour.TdReplacementPrefixExact
public import LeanPool.GoldbergSeymour.AdjacentEdges
public import LeanPool.GoldbergSeymour.BoundaryColorEdges
public import LeanPool.GoldbergSeymour.BoundaryEdges
public import LeanPool.GoldbergSeymour.CertifiedETTRestriction
public import LeanPool.GoldbergSeymour.ColoredVertexSetClosed
public import LeanPool.GoldbergSeymour.ColoredVertexSetStronglyClosed
public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTree
public import LeanPool.GoldbergSeymour.DefectiveColor
public import LeanPool.GoldbergSeymour.DefectiveEdge
public import LeanPool.GoldbergSeymour.DefectiveVertex
public import LeanPool.GoldbergSeymour.ExtendedTashkinovTree
public import LeanPool.GoldbergSeymour.ExtensionBase
public import LeanPool.GoldbergSeymour.ExtensionRules
public import LeanPool.GoldbergSeymour.HkuMissingStoredMonotone
public import LeanPool.GoldbergSeymour.HkuTreeColorsControlled
public import LeanPool.GoldbergSeymour.IsOneEdgeUncolored
public import LeanPool.GoldbergSeymour.IsProperEdgeColoring
public import LeanPool.GoldbergSeymour.KTriple
public import LeanPool.GoldbergSeymour.LooplessMultigraph
public import LeanPool.GoldbergSeymour.MaximumDefectiveChoice
public import LeanPool.GoldbergSeymour.MaximumProperty
public import LeanPool.GoldbergSeymour.MaximumPropertyTransport
public import LeanPool.GoldbergSeymour.MissingColors
public import LeanPool.GoldbergSeymour.ModColoring
public import LeanPool.GoldbergSeymour.ParallelExtensionColor
public import LeanPool.GoldbergSeymour.ParallelExtensionUndoStable
public import LeanPool.GoldbergSeymour.PresentColors
public import LeanPool.GoldbergSeymour.RevisitingExtensionCertificate
public import LeanPool.GoldbergSeymour.StableColoring
public import LeanPool.GoldbergSeymour.TashkinovAugmentation
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequence
public import LeanPool.GoldbergSeymour.TashkinovClosure
public import LeanPool.GoldbergSeymour.TashkinovClosureExists
public import LeanPool.GoldbergSeymour.TashkinovSeries
public import LeanPool.GoldbergSeymour.TashkinovSeriesAppend
public import LeanPool.GoldbergSeymour.TashkinovSeriesFinalETTExists
public import LeanPool.GoldbergSeymour.TashkinovSeriesStep
public import LeanPool.GoldbergSeymour.TashkinovStoredColors
public import LeanPool.GoldbergSeymour.TashkinovStoredColorsAppend
public import LeanPool.GoldbergSeymour.TechnicalTheoremBase
public import LeanPool.GoldbergSeymour.TreeExit
public import LeanPool.GoldbergSeymour.TreeExitPath
public import LeanPool.GoldbergSeymour.TreeIncidentEdge
public import LeanPool.GoldbergSeymour.TreeInterchangeable
public import LeanPool.GoldbergSeymour.TreeMissingColors
public import LeanPool.GoldbergSeymour.TreeSequenceAdjoinEdge
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegment
public import LeanPool.GoldbergSeymour.TwoColorComponent
public import LeanPool.GoldbergSeymour.TwoColorIncidenceGraph
public import LeanPool.GoldbergSeymour.TwoColorComponentSpanningPath
public import LeanPool.GoldbergSeymour.TwoColorComponentSwap
public import LeanPool.GoldbergSeymour.TwoColorCycle
public import LeanPool.GoldbergSeymour.TwoColorIncidenceDegreeAtMostTwo
public import LeanPool.GoldbergSeymour.TwoColorPathComponent
public import LeanPool.GoldbergSeymour.TwoColorNontrivialPathComponent
public import LeanPool.GoldbergSeymour.RevisitingExtensionCertificateAppend
public import LeanPool.GoldbergSeymour.ParallelExtensionColorAppend
public import LeanPool.GoldbergSeymour.StableColoringIncidentEdgeCriterion
public import LeanPool.GoldbergSeymour.StableColoringEquivalence
public import LeanPool.GoldbergSeymour.LowerRoundInductionHypothesis

/-!
# Preparatory lemmas for terminal extension reconstruction

Part of Wesley Pegden’s Trellis formalization of the Goldberg–Seymour theorem,
commit 88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12. These lemmas support the
reconstruction of terminal series extensions.
-/

@[expose] public section

namespace GoldbergSeymour.TerminalSeriesRebuild

/-- Typed data construction shared by the terminal series reconstruction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
noncomputable abbrev helperNewChoice2409.{u_1, u_2} :
    open scoped Classical in
      {V : Type u_1} →
  {E : Type u_2} →
  [ Fintype V] →
  [ Fintype E] →
  [ DecidableEq E] →
  (G : LooplessMultigraph V E) →
  (k : ℕ) →
  (e0 : E) →
  (input : PartialEdgeColoring E k) →
  (T : TreeSequence G e0) →
  (generating : PartialEdgeColoring E k) →
  (ett : ExtendedTashkinovTree G k e0 input T generating) →
  (hpositive : (0 : ℕ) < ett.rounds) →
  let q : Fin ett.rounds :=
    (⟨ett.rounds - (1 : ℕ),
        by
        have := GoldbergSeymour.TreeSequence.positive T
        omega⟩ :
      Fin ett.rounds);
  IsProperEdgeColoring G (ett.series.data.coloring q.castSucc) →
  IsOneEdgeUncolored (ett.series.data.coloring q.castSucc) e0 →
  (choice :
      MaximumDefectiveChoice G e0
        (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc)
        (ett.series.data.coloring q.castSucc)) →
  (sigmaPrev : PartialEdgeColoring E k) →
  IsProperEdgeColoring G sigmaPrev →
  IsOneEdgeUncolored sigmaPrev e0 →
  StableColoring (ett.series.data.tree q.succ.castSucc)
      (TashkinovStoredColors ett.series.data q.castSucc)
      (ett.series.data.coloring q.castSucc) sigmaPrev →
  DefectiveColor G sigmaPrev
      (TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc))
      choice.color →
  choice.edge ∈
      BoundaryColorEdges G sigmaPrev
        (TreeSequenceVertexSet
          (ett.series.data.tree q.succ.castSucc))
        choice.color →
  StableColoring
      (ett.series.data.tree q.succ.castSucc)
      (TashkinovStoredColors ett.series.data
        q.castSucc)
      sigmaPrev sigmaPrev →
  MaximumDefectiveChoice G e0
    (ett.series.data.tree q.succ.castSucc)
    (TashkinovStoredColors ett.series.data
      q.castSucc)
    sigmaPrev := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive q previousProper previousOneUncolored
      choice sigmaPrev hsigmaPrevProper hsigmaPrevOne hsigmaPrevStableQ hchoiceDefective
      hchoiceEdgeNew hsigmaPrevSelf
  exact {
    selected := sigmaPrev
    selectedProper := hsigmaPrevProper
    selectedOneUncolored := hsigmaPrevOne
    selectedStable := hsigmaPrevSelf
    vertex := choice.vertex
    vertexDefective := ⟨choice.vertexDefective.1, choice.edge,
      ⟨choice.color, hchoiceDefective, hchoiceEdgeNew⟩,
      choice.edgeIncident⟩
    maximal := by
      intro pi w hpiProper hpiOne hpiStable hw
      have hpiOld : StableColoring
          (ett.series.data.tree q.succ.castSucc)
          (TashkinovStoredColors ett.series.data q.castSucc)
          (ett.series.data.coloring q.castSucc) pi := by
        exact (sc2 G e0 (ett.series.data.tree q.succ.castSucc)
          (TashkinovStoredColors ett.series.data q.castSucc)).trans
            (x := ⟨ett.series.data.coloring q.castSucc,
              ⟨previousProper, previousOneUncolored⟩⟩)
            (y := ⟨sigmaPrev, ⟨hsigmaPrevProper, hsigmaPrevOne⟩⟩)
            (z := ⟨pi, ⟨hpiProper, hpiOne⟩⟩)
            hsigmaPrevStableQ hpiStable
      exact choice.maximal pi w hpiProper hpiOne hpiOld hw
    edge := choice.edge
    edgeDefective := ⟨choice.color, hchoiceDefective, hchoiceEdgeNew⟩
    edgeIncident := choice.edgeIncident
    otherEndpoint := choice.otherEndpoint
    otherOutside := choice.otherOutside
    edgeEnds := choice.edgeEnds
    color := choice.color
    edgeColor := (Finset.mem_filter.mp hchoiceEdgeNew).2 }

/-- Typed data construction shared by the terminal series reconstruction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
noncomputable abbrev helperNewChoice4049.{u_1, u_2} :
    open scoped Classical in
      {V : Type u_1} →
  {E : Type u_2} →
  [ Fintype V] →
  [ Fintype E] →
  [ DecidableEq E] →
  (G : LooplessMultigraph V E) →
  (k : ℕ) →
  (e0 : E) →
  (input : PartialEdgeColoring E k) →
  (T : TreeSequence G e0) →
  (generating : PartialEdgeColoring E k) →
  (ett : ExtendedTashkinovTree G k e0 input T generating) →
  (hpositive : (0 : ℕ) < ett.rounds) →
  let q : Fin ett.rounds :=
    (⟨ett.rounds - (1 : ℕ),
        by
        have := GoldbergSeymour.TreeSequence.positive T
        omega⟩ :
      Fin ett.rounds);
  IsProperEdgeColoring G (ett.series.data.coloring q.castSucc) →
  IsOneEdgeUncolored (ett.series.data.coloring q.castSucc) e0 →
  (choice :
      MaximumDefectiveChoice G e0
        (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc)
        (ett.series.data.coloring q.castSucc)) →
  (sigmaPrev : PartialEdgeColoring E k) →
  IsProperEdgeColoring G sigmaPrev →
  IsOneEdgeUncolored sigmaPrev e0 →
  StableColoring (ett.series.data.tree q.succ.castSucc)
      (TashkinovStoredColors ett.series.data q.castSucc)
      (ett.series.data.coloring q.castSucc) sigmaPrev →
  DefectiveColor G sigmaPrev
      (TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc))
      choice.color →
  choice.edge ∈
      BoundaryColorEdges G sigmaPrev
        (TreeSequenceVertexSet
          (ett.series.data.tree q.succ.castSucc))
        choice.color →
  StableColoring
      (ett.series.data.tree q.succ.castSucc)
      (TashkinovStoredColors ett.series.data
        q.castSucc)
      sigmaPrev sigmaPrev →
  MaximumDefectiveChoice G e0
    (ett.series.data.tree q.succ.castSucc)
    (TashkinovStoredColors ett.series.data
      q.castSucc)
    sigmaPrev := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive q previousProper previousOneUncolored
      choice sigmaPrev hsigmaPrevProper hsigmaPrevOne hsigmaPrevStableQ hchoiceDefective
      hchoiceEdgeNew hsigmaPrevSelf
  exact {
    selected := sigmaPrev
    selectedProper := hsigmaPrevProper
    selectedOneUncolored := hsigmaPrevOne
    selectedStable := hsigmaPrevSelf
    vertex := choice.vertex
    vertexDefective := ⟨choice.vertexDefective.1, choice.edge,
      ⟨choice.color, hchoiceDefective, hchoiceEdgeNew⟩,
      choice.edgeIncident⟩
    maximal := by
      intro pi w hpiProper hpiOne hpiStable hw
      have hpiOld : StableColoring
          (ett.series.data.tree q.succ.castSucc)
          (TashkinovStoredColors ett.series.data q.castSucc)
          (ett.series.data.coloring q.castSucc) pi := by
        exact (sc2 G e0 (ett.series.data.tree q.succ.castSucc)
          (TashkinovStoredColors ett.series.data q.castSucc)).trans
            (x := ⟨ett.series.data.coloring q.castSucc,
              ⟨previousProper, previousOneUncolored⟩⟩)
            (y := ⟨sigmaPrev, ⟨hsigmaPrevProper, hsigmaPrevOne⟩⟩)
            (z := ⟨pi, ⟨hpiProper, hpiOne⟩⟩)
            hsigmaPrevStableQ hpiStable
      exact choice.maximal pi w hpiProper hpiOne hpiOld hw
    edge := choice.edge
    edgeDefective := ⟨choice.color, hchoiceDefective, hchoiceEdgeNew⟩
    edgeIncident := choice.edgeIncident
    otherEndpoint := choice.otherEndpoint
    otherOutside := choice.otherOutside
    edgeEnds := choice.edgeEnds
    color := choice.color
    edgeColor := (Finset.mem_filter.mp hchoiceEdgeNew).2 }

/-- Typed data construction shared by the terminal series reconstruction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
noncomputable abbrev helperAppendedChoice2713.{u_1, u_2} :
    open scoped Classical in
      {V : Type u_1} →
  {E : Type u_2} →
  [ Fintype V] →
  [ Fintype E] →
  [ DecidableEq E] →
  (G : LooplessMultigraph V E) →
  (k : ℕ) →
  (e0 : E) →
  (input : PartialEdgeColoring E k) →
  (T : TreeSequence G e0) →
  (generating : PartialEdgeColoring E k) →
  (ett : ExtendedTashkinovTree G k e0 input T generating) →
  (hpositive : (0 : ℕ) < ett.rounds) →
  (sigma : PartialEdgeColoring E k) →
  (closureTree : TreeSequence G e0) →
  let q : Fin ett.rounds :=
    (⟨ett.rounds - (1 : ℕ),
        by
        have := GoldbergSeymour.TreeSequence.positive T
        omega⟩ :
      Fin ett.rounds);
  (previousProper :
      IsProperEdgeColoring G
        (ett.series.data.coloring q.castSucc)) →
  (previousOneUncolored :
      IsOneEdgeUncolored (ett.series.data.coloring q.castSucc)
        e0) →
  (choice :
      MaximumDefectiveChoice G e0
        (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc)
        (ett.series.data.coloring q.castSucc)) →
  (sigmaPrev : PartialEdgeColoring E k) →
  (hsigmaPrevProper : IsProperEdgeColoring G sigmaPrev) →
  (hsigmaPrevOne : IsOneEdgeUncolored sigmaPrev e0) →
  (hsigmaPrevStableQ :
      StableColoring
        (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data
          q.castSucc)
        (ett.series.data.coloring q.castSucc)
        sigmaPrev) →
  (hchoiceDefective :
      DefectiveColor G sigmaPrev
        (TreeSequenceVertexSet
          (ett.series.data.tree q.succ.castSucc))
        choice.color) →
  (hchoiceEdgeNew :
      choice.edge ∈
        BoundaryColorEdges G sigmaPrev
          (TreeSequenceVertexSet
            (ett.series.data.tree
              q.succ.castSucc))
          choice.color) →
  (hsigmaPrevSelf :
      StableColoring
        (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data
          q.castSucc)
        sigmaPrev sigmaPrev) →
  let _ :
    MaximumDefectiveChoice G e0
      (ett.series.data.tree q.succ.castSucc)
      (TashkinovStoredColors ett.series.data
        q.castSucc)
      sigmaPrev :=
    helperNewChoice2409 G k e0 input T
      generating ett hpositive previousProper
      previousOneUncolored choice sigmaPrev
      hsigmaPrevProper hsigmaPrevOne
      hsigmaPrevStableQ hchoiceDefective
      hchoiceEdgeNew hsigmaPrevSelf;
  (prefixInput : PartialEdgeColoring E k) →
  (zeroPrefix :
      TashkinovSeries G k (0 : ℕ) e0
        prefixInput) →
  let zeroLast :
    Fin ((0 : ℕ) + (1 : ℕ)) :=
    Fin.last (0 : ℕ);
  let newStored : Finset (Fin k) :=
    ({ choice.color } : Finset (Fin k));
  let newEdges : Finset E :=
    ({ choice.edge } : Finset E);
  let newKind :
    Option TashkinovExtensionKind :=
    some TashkinovExtensionKind.SE;
  let newVertex : Option V :=
    some choice.vertex;
  let newOutside : Option V :=
    some choice.otherEndpoint;
  let newDelta : Option (Fin k) :=
    some choice.color;
  let newGamma : Option (Fin k) := none;
  let appendedData :
    TashkinovSeriesData G k
      ((0 : ℕ) + (1 : ℕ)) e0 :=
    TashkinovSeriesDataAppend
      zeroPrefix.data closureTree sigma
      newStored newEdges newKind newVertex
      newOutside newDelta newGamma;
  appendedData.tree
        zeroLast.succ.castSucc =
      ett.series.data.tree
        q.succ.castSucc →
  appendedData.coloring
        zeroLast.castSucc =
      sigmaPrev →
  TashkinovStoredColors appendedData
        zeroLast.castSucc =
      TashkinovStoredColors
        ett.series.data q.castSucc →
  MaximumDefectiveChoice G e0
    (appendedData.tree
      zeroLast.succ.castSucc)
    (TashkinovStoredColors
      appendedData
      zeroLast.castSucc)
    (appendedData.coloring
      zeroLast.castSucc) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma closureTree q previousProper
      previousOneUncolored choice sigmaPrev hsigmaPrevProper hsigmaPrevOne hsigmaPrevStableQ
      hchoiceDefective hchoiceEdgeNew hsigmaPrevSelf newChoice prefixInput zeroPrefix zeroLast
      newStored newEdges newKind newVertex newOutside newDelta newGamma appendedData happendTree
      happendColor happendStored
  exact {
    selected := sigmaPrev
    selectedProper := hsigmaPrevProper
    selectedOneUncolored := hsigmaPrevOne
    selectedStable := by
      rw [happendTree, happendStored, happendColor]
      exact newChoice.selectedStable
    vertex := choice.vertex
    vertexDefective := by
      rw [happendTree]
      exact newChoice.vertexDefective
    maximal := by
      intro pi w hpiProper hpiOne hpiStable hw
      rw [happendTree, happendStored, happendColor] at hpiStable
      rw [happendTree] at hw ⊢
      exact newChoice.maximal pi w hpiProper hpiOne hpiStable hw
    edge := choice.edge
    edgeDefective := by
      rw [happendTree]
      exact newChoice.edgeDefective
    edgeIncident := choice.edgeIncident
    otherEndpoint := choice.otherEndpoint
    otherOutside := by
      rw [happendTree]
      exact newChoice.otherOutside
    edgeEnds := choice.edgeEnds
    color := choice.color
    edgeColor := newChoice.edgeColor }

/-- Typed data construction shared by the terminal series reconstruction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
noncomputable abbrev helperAppendedChoice4500.{u_1, u_2} :
    open scoped Classical in
      {V : Type u_1} →
  {E : Type u_2} →
  [ Fintype V] →
  [ Fintype E] →
  [ DecidableEq E] →
  (G : LooplessMultigraph V E) →
  (k : ℕ) →
  (e0 : E) →
  (input : PartialEdgeColoring E k) →
  (T : TreeSequence G e0) →
  (generating : PartialEdgeColoring E k) →
  (ett : ExtendedTashkinovTree G k e0 input T generating) →
  (hpositive : (0 : ℕ) < ett.rounds) →
  (sigma : PartialEdgeColoring E k) →
  (closureTree : TreeSequence G e0) →
  let q : Fin ett.rounds :=
    (⟨ett.rounds - (1 : ℕ),
        by
        have := GoldbergSeymour.TreeSequence.positive T
        omega⟩ :
      Fin ett.rounds);
  (gamma : Fin k) →
  (previousProper :
      IsProperEdgeColoring G
        (ett.series.data.coloring q.castSucc)) →
  (previousOneUncolored :
      IsOneEdgeUncolored (ett.series.data.coloring q.castSucc)
        e0) →
  (choice :
      MaximumDefectiveChoice G e0
        (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc)
        (ett.series.data.coloring q.castSucc)) →
  (sigmaPrev : PartialEdgeColoring E k) →
  (hsigmaPrevProper :
      IsProperEdgeColoring G sigmaPrev) →
  (hsigmaPrevOne : IsOneEdgeUncolored sigmaPrev e0) →
  (hsigmaPrevStableQ :
      StableColoring
        (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data
          q.castSucc)
        (ett.series.data.coloring q.castSucc)
        sigmaPrev) →
  (hchoiceDefective :
      DefectiveColor G sigmaPrev
        (TreeSequenceVertexSet
          (ett.series.data.tree q.succ.castSucc))
        choice.color) →
  (hchoiceEdgeNew :
      choice.edge ∈
        BoundaryColorEdges G sigmaPrev
          (TreeSequenceVertexSet
            (ett.series.data.tree
              q.succ.castSucc))
          choice.color) →
  (hsigmaPrevSelf :
      StableColoring
        (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data
          q.castSucc)
        sigmaPrev sigmaPrev) →
  let _ :
    MaximumDefectiveChoice G e0
      (ett.series.data.tree q.succ.castSucc)
      (TashkinovStoredColors ett.series.data
        q.castSucc)
      sigmaPrev :=
    helperNewChoice4049 G k e0 input T
      generating ett hpositive
      previousProper previousOneUncolored
      choice sigmaPrev hsigmaPrevProper
      hsigmaPrevOne hsigmaPrevStableQ
      hchoiceDefective hchoiceEdgeNew
      hsigmaPrevSelf;
  (prefixInput : PartialEdgeColoring E k) →
  (zeroPrefix :
      TashkinovSeries G k (0 : ℕ) e0
        prefixInput) →
  let zeroLast :
    Fin ((0 : ℕ) + (1 : ℕ)) :=
    Fin.last (0 : ℕ);
  let newStored : Finset (Fin k) :=
    (insert choice.color
        ({ gamma } : Finset (Fin k)) :
      Finset (Fin k));
  let newEdges : Finset E :=
    ({ choice.edge } : Finset E);
  let newKind :
    Option TashkinovExtensionKind :=
    some TashkinovExtensionKind.PE;
  let newVertex : Option V :=
    some choice.vertex;
  let newOutside : Option V :=
    some choice.otherEndpoint;
  let newDelta : Option (Fin k) :=
    some choice.color;
  let newGamma : Option (Fin k) :=
    some gamma;
  let appendedData :
    TashkinovSeriesData G k
      ((0 : ℕ) + (1 : ℕ)) e0 :=
    TashkinovSeriesDataAppend
      zeroPrefix.data closureTree sigma
      newStored newEdges newKind
      newVertex newOutside newDelta
      newGamma;
  appendedData.tree
        zeroLast.succ.castSucc =
      ett.series.data.tree
        q.succ.castSucc →
  appendedData.coloring
        zeroLast.castSucc =
      sigmaPrev →
  TashkinovStoredColors appendedData
        zeroLast.castSucc =
      TashkinovStoredColors
        ett.series.data q.castSucc →
  MaximumDefectiveChoice G e0
    (appendedData.tree
      zeroLast.succ.castSucc)
    (TashkinovStoredColors
      appendedData
      zeroLast.castSucc)
    (appendedData.coloring
      zeroLast.castSucc) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma closureTree q gamma previousProper
      previousOneUncolored choice sigmaPrev hsigmaPrevProper hsigmaPrevOne hsigmaPrevStableQ
      hchoiceDefective hchoiceEdgeNew hsigmaPrevSelf newChoice prefixInput zeroPrefix zeroLast
      newStored newEdges newKind newVertex newOutside newDelta newGamma appendedData happendTree
      happendColor happendStored
  exact {
    selected := sigmaPrev
    selectedProper := hsigmaPrevProper
    selectedOneUncolored := hsigmaPrevOne
    selectedStable := by
      rw [happendTree, happendStored, happendColor]
      exact newChoice.selectedStable
    vertex := choice.vertex
    vertexDefective := by
      rw [happendTree]
      exact newChoice.vertexDefective
    maximal := by
      intro pi w hpiProper hpiOne hpiStable hw
      rw [happendTree, happendStored, happendColor] at hpiStable
      rw [happendTree] at hw ⊢
      exact newChoice.maximal pi w hpiProper hpiOne hpiStable hw
    edge := choice.edge
    edgeDefective := by
      rw [happendTree]
      exact newChoice.edgeDefective
    edgeIncident := choice.edgeIncident
    otherEndpoint := choice.otherEndpoint
    otherOutside := by
      rw [happendTree]
      exact newChoice.otherOutside
    edgeEnds := choice.edgeEnds
    color := choice.color
    edgeColor := newChoice.edgeColor }

/-- Typed data construction shared by the terminal series reconstruction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
noncomputable abbrev helperReplacementETT3160.{u_1, u_2} :
    open scoped Classical in
      {V : Type u_1} →
  {E : Type u_2} →
  [inst : Fintype V] →
  [inst_1 : Fintype E] →
  [inst_2 : DecidableEq E] →
  (G : LooplessMultigraph V E) →
  (k : ℕ) →
  (e0 : E) →
  (input : PartialEdgeColoring E k) →
  (T : TreeSequence G e0) →
  (generating : PartialEdgeColoring E k) →
  (ett : ExtendedTashkinovTree G k e0 input T generating) →
  (sigma : PartialEdgeColoring E k) →
  (Tstar : TreeSequence G e0) →
  TreeSequenceInitialSegment
      (ett.series.data.tree (Fin.last ett.rounds).castSucc) Tstar →
  (ett.series.data.tree (Fin.last ett.rounds).castSucc).length <
      Tstar.length →
  (closureTree : TreeSequence G e0) →
  TreeSequenceInitialSegment Tstar closureTree →
  (prefixInput : PartialEdgeColoring E k) →
  (extendedSeries :
      TashkinovSeries G k ((0 : ℕ) + (1 : ℕ)) e0
        prefixInput) →
  (hroundsEq : (0 : ℕ) + (1 : ℕ) = ett.rounds) →
  let castSeries :
    {a b : ℕ} →
      a = b →
        TashkinovSeries G k a e0 prefixInput →
          TashkinovSeries G k b e0 prefixInput :=
    fun {a b : ℕ} (h : a = b)
      (S : TashkinovSeries G k a e0 prefixInput) ↦
    @Eq.ndrec Nat a
      (fun {b : Nat} ↦
        @TashkinovSeries V E inst inst_1 inst_2 G k b
          e0 prefixInput)
      S b h;
  let finalSeries :
    TashkinovSeries G k ett.rounds e0 prefixInput :=
    castSeries hroundsEq extendedSeries;
  finalSeries.data.tree
        (Fin.last (ett.rounds + (1 : ℕ))) =
      closureTree →
  finalSeries.data.tree
        (⟨ett.rounds,
            by
            have :=
              GoldbergSeymour.TreeSequence.positive
                T
            omega⟩ :
          Fin (ett.rounds + (2 : ℕ))) =
      ett.series.data.tree
        (Fin.last ett.rounds).castSucc →
  finalSeries.data.coloring
        (Fin.last ett.rounds) =
      sigma →
  ExtendedTashkinovTree G k e0 prefixInput Tstar
    sigma := by
  classical
  intro V E _ _ _ G k e0 input T generating ett sigma Tstar hTnTstar hstrict closureTree
      hTstarClosure prefixInput extendedSeries hroundsEq castSeries finalSeries hfinalTree
      hpenultimateTree hfinalColor
  exact {
    rounds := ett.rounds
    roundsPositive := ett.roundsPositive
    series := finalSeries
    abovePenultimate := by rw [hpenultimateTree]; exact hTnTstar
    strictAbovePenultimate := by rw [hpenultimateTree]; exact hstrict
    belowFinal := by rw [hfinalTree]; exact hTstarClosure
    generatingColoring := hfinalColor.symm }

/-- Typed data construction shared by the terminal series reconstruction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
noncomputable abbrev helperReplacementETT4947.{u_1, u_2} :
    open scoped Classical in
      {V : Type u_1} →
  {E : Type u_2} →
  [inst : Fintype V] →
  [inst_1 : Fintype E] →
  [inst_2 : DecidableEq E] →
  (G : LooplessMultigraph V E) →
  (k : ℕ) →
  (e0 : E) →
  (input : PartialEdgeColoring E k) →
  (T : TreeSequence G e0) →
  (generating : PartialEdgeColoring E k) →
  (ett : ExtendedTashkinovTree G k e0 input T generating) →
  (hpositive : (0 : ℕ) < ett.rounds) →
  (sigma : PartialEdgeColoring E k) →
  (Tstar : TreeSequence G e0) →
  TreeSequenceInitialSegment
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      Tstar →
  (ett.series.data.tree (Fin.last ett.rounds).castSucc).length <
      Tstar.length →
  (closureTree : TreeSequence G e0) →
  TreeSequenceInitialSegment Tstar closureTree →
  let q : Fin ett.rounds :=
    (⟨ett.rounds - (1 : ℕ),
        by
        have := GoldbergSeymour.TreeSequence.positive T
        omega⟩ :
      Fin ett.rounds);
  (gamma : Fin k) →
  (choice :
      MaximumDefectiveChoice G e0
        (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data
          q.castSucc)
        (ett.series.data.coloring q.castSucc)) →
  (sigmaPrev : PartialEdgeColoring E k) →
  let H : SimpleGraph (V ⊕ E) :=
    TwoColorIncidenceGraph G sigmaPrev gamma
      choice.color;
  (u : V) →
  (p :
      H.Walk (Sum.inl choice.vertex)
        (Sum.inl u)) →
  (prefixInput : PartialEdgeColoring E k) →
  (extendedSeries :
      TashkinovSeries G k ((0 : ℕ) + (1 : ℕ))
        e0 prefixInput) →
  (hroundsEq :
      (0 : ℕ) + (1 : ℕ) = ett.rounds) →
  let castSeries :
    {a b : ℕ} →
      a = b →
        TashkinovSeries G k a e0
            prefixInput →
          TashkinovSeries G k b e0
            prefixInput :=
    fun {a b : ℕ} (h : a = b)
      (S :
        TashkinovSeries G k a e0
          prefixInput) ↦
    @Eq.ndrec Nat a
      (fun {b : Nat} ↦
        @TashkinovSeries V E inst inst_1
          inst_2 G k b e0 prefixInput)
      S b h;
  let finalSeries :
    TashkinovSeries G k ett.rounds e0
      prefixInput :=
    castSeries hroundsEq extendedSeries;
  finalSeries.data.tree
        (Fin.last
          (ett.rounds + (1 : ℕ))) =
      closureTree →
  finalSeries.data.tree
        (⟨ett.rounds,
            by
            have :=
              GoldbergSeymour.TreeSequence.positive
                T
            omega⟩ :
          Fin (ett.rounds + (2 : ℕ))) =
      ett.series.data.tree
        (Fin.last ett.rounds).castSucc →
  finalSeries.data.coloring
        (Fin.last ett.rounds) =
      sigma →
  ExtendedTashkinovTree G k e0
    prefixInput Tstar sigma := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma Tstar hTnTstar hstrict
      closureTree hTstarClosure q gamma choice sigmaPrev H u p prefixInput extendedSeries
      hroundsEq castSeries finalSeries hfinalTree hpenultimateTree hfinalColor
  exact {
    rounds := ett.rounds
    roundsPositive := ett.roundsPositive
    series := finalSeries
    abovePenultimate := by rw [hpenultimateTree]; exact hTnTstar
    strictAbovePenultimate := by rw [hpenultimateTree]; exact hstrict
    belowFinal := by rw [hfinalTree]; exact hTstarClosure
    generatingColoring := hfinalColor.symm }

/-- Typed data construction shared by the terminal series reconstruction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
noncomputable abbrev helperReplacementChoice3411.{u_1, u_2} :
    open scoped Classical in
      {V : Type u_1} →
  {E : Type u_2} →
  [ Fintype V] →
  [ Fintype E] →
  [ DecidableEq E] →
  (G : LooplessMultigraph V E) →
  (k : ℕ) →
  (e0 : E) →
  (input : PartialEdgeColoring E k) →
  (T : TreeSequence G e0) →
  (generating : PartialEdgeColoring E k) →
  (ett : ExtendedTashkinovTree G k e0 input T generating) →
  (hpositive : (0 : ℕ) < ett.rounds) →

  let q : Fin ett.rounds :=
    (⟨ett.rounds - (1 : ℕ),
        by
        have := GoldbergSeymour.TreeSequence.positive T
        omega⟩ :
      Fin ett.rounds);
  (previousProper :
      IsProperEdgeColoring G
        (ett.series.data.coloring q.castSucc)) →
  (previousOneUncolored :
      IsOneEdgeUncolored (ett.series.data.coloring q.castSucc)
        e0) →
  (choice :
      MaximumDefectiveChoice G e0
        (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc)
        (ett.series.data.coloring q.castSucc)) →
  (sigmaPrev : PartialEdgeColoring E k) →
  (hsigmaPrevProper : IsProperEdgeColoring G sigmaPrev) →
  (hsigmaPrevOne : IsOneEdgeUncolored sigmaPrev e0) →
  (hsigmaPrevStableQ :
      StableColoring
        (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data
          q.castSucc)
        (ett.series.data.coloring q.castSucc)
        sigmaPrev) →
  (hchoiceDefective :
      DefectiveColor G sigmaPrev
        (TreeSequenceVertexSet
          (ett.series.data.tree q.succ.castSucc))
        choice.color) →
  (hchoiceEdgeNew :
      choice.edge ∈
        BoundaryColorEdges G sigmaPrev
          (TreeSequenceVertexSet
            (ett.series.data.tree q.succ.castSucc))
          choice.color) →
  (hsigmaPrevSelf :
      StableColoring
        (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data
          q.castSucc)
        sigmaPrev sigmaPrev) →
  let _ :
    MaximumDefectiveChoice G e0
      (ett.series.data.tree q.succ.castSucc)
      (TashkinovStoredColors ett.series.data
        q.castSucc)
      sigmaPrev :=
    helperNewChoice2409 G k e0 input T
      generating ett hpositive previousProper
      previousOneUncolored choice sigmaPrev
      hsigmaPrevProper hsigmaPrevOne
      hsigmaPrevStableQ hchoiceDefective
      hchoiceEdgeNew hsigmaPrevSelf;
  (originalPrefix :
      ExtendedTashkinovTree G k e0 input
        (ett.series.data.tree
          (Fin.last ett.rounds).castSucc)
        (ett.series.data.coloring
          (⟨ett.rounds - (1 : ℕ),
              by
              have :=
                GoldbergSeymour.TreeSequence.positive
                  T
              omega⟩ :
            Fin (ett.rounds + (1 : ℕ))))) →
  (corr :
      CorrespondingExtendedTashkinovTree G k
        e0 originalPrefix sigmaPrev
        (ett.series.data.tree
          (Fin.last ett.rounds).castSucc)) →
  corr.replacementSeries.data.coloring
        (Fin.last originalPrefix.rounds) =
      sigmaPrev →
  let replacementLast :
    Fin
      (originalPrefix.rounds + (1 : ℕ)) :=
    Fin.last originalPrefix.rounds;
  corr.replacementSeries.data.tree
        replacementLast.succ =
      ett.series.data.tree
        q.succ.castSucc →
  TashkinovStoredColors
        corr.replacementSeries.data
        replacementLast =
      TashkinovStoredColors
        ett.series.data q.castSucc →
  MaximumDefectiveChoice G e0
    (corr.replacementSeries.data.tree
      replacementLast.succ)
    (TashkinovStoredColors
      corr.replacementSeries.data
      replacementLast)
    (corr.replacementSeries.data.coloring
      replacementLast) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive q previousProper previousOneUncolored
      choice sigmaPrev hsigmaPrevProper hsigmaPrevOne hsigmaPrevStableQ hchoiceDefective
      hchoiceEdgeNew hsigmaPrevSelf newChoice originalPrefix corr hcorrFinalColor replacementLast
      hreplacementCurrentTree hreplacementStored
  exact {
    selected := sigmaPrev
    selectedProper := hsigmaPrevProper
    selectedOneUncolored := hsigmaPrevOne
    selectedStable := by
      rw [hreplacementCurrentTree, hreplacementStored, hcorrFinalColor]
      exact newChoice.selectedStable
    vertex := choice.vertex
    vertexDefective := by
      rw [hreplacementCurrentTree]
      exact newChoice.vertexDefective
    maximal := by
      intro pi w hpiProper hpiOne hpiStable hw
      rw [hreplacementCurrentTree, hreplacementStored, hcorrFinalColor]
        at hpiStable
      rw [hreplacementCurrentTree] at hw ⊢
      exact newChoice.maximal pi w hpiProper hpiOne hpiStable hw
    edge := choice.edge
    edgeDefective := by
      rw [hreplacementCurrentTree]
      exact newChoice.edgeDefective
    edgeIncident := choice.edgeIncident
    otherEndpoint := choice.otherEndpoint
    otherOutside := by
      rw [hreplacementCurrentTree]
      exact newChoice.otherOutside
    edgeEnds := choice.edgeEnds
    color := choice.color
    edgeColor := newChoice.edgeColor }

/-- Typed data construction shared by the terminal series reconstruction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
noncomputable abbrev helperReplacementChoice5196.{u_1, u_2} :
    open scoped Classical in
      {V : Type u_1} →
  {E : Type u_2} →
  [ Fintype V] →
  [ Fintype E] →
  [ DecidableEq E] →
  (G : LooplessMultigraph V E) →
  (k : ℕ) →
  (e0 : E) →
  (input : PartialEdgeColoring E k) →
  (T : TreeSequence G e0) →
  (generating : PartialEdgeColoring E k) →
  (ett : ExtendedTashkinovTree G k e0 input T generating) →
  (hpositive : (0 : ℕ) < ett.rounds) →

  let q : Fin ett.rounds :=
    (⟨ett.rounds - (1 : ℕ),
        by
        have := GoldbergSeymour.TreeSequence.positive T
        omega⟩ :
      Fin ett.rounds);
  (previousProper :
      IsProperEdgeColoring G
        (ett.series.data.coloring q.castSucc)) →
  (previousOneUncolored :
      IsOneEdgeUncolored (ett.series.data.coloring q.castSucc)
        e0) →
  (choice :
      MaximumDefectiveChoice G e0
        (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc)
        (ett.series.data.coloring q.castSucc)) →
  (sigmaPrev : PartialEdgeColoring E k) →
  (hsigmaPrevProper : IsProperEdgeColoring G sigmaPrev) →
  (hsigmaPrevOne : IsOneEdgeUncolored sigmaPrev e0) →
  (hsigmaPrevStableQ :
      StableColoring
        (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data
          q.castSucc)
        (ett.series.data.coloring q.castSucc)
        sigmaPrev) →
  (hchoiceDefective :
      DefectiveColor G sigmaPrev
        (TreeSequenceVertexSet
          (ett.series.data.tree q.succ.castSucc))
        choice.color) →
  (hchoiceEdgeNew :
      choice.edge ∈
        BoundaryColorEdges G sigmaPrev
          (TreeSequenceVertexSet
            (ett.series.data.tree q.succ.castSucc))
          choice.color) →
  (hsigmaPrevSelf :
      StableColoring
        (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data
          q.castSucc)
        sigmaPrev sigmaPrev) →
  let _ :
    MaximumDefectiveChoice G e0
      (ett.series.data.tree q.succ.castSucc)
      (TashkinovStoredColors ett.series.data
        q.castSucc)
      sigmaPrev :=
    helperNewChoice4049 G k e0 input T
      generating ett hpositive previousProper
      previousOneUncolored choice sigmaPrev
      hsigmaPrevProper hsigmaPrevOne
      hsigmaPrevStableQ hchoiceDefective
      hchoiceEdgeNew hsigmaPrevSelf;
  (originalPrefix :
      ExtendedTashkinovTree G k e0 input
        (ett.series.data.tree
          (Fin.last ett.rounds).castSucc)
        (ett.series.data.coloring
          (⟨ett.rounds - (1 : ℕ),
              by
              have :=
                GoldbergSeymour.TreeSequence.positive
                  T
              omega⟩ :
            Fin (ett.rounds + (1 : ℕ))))) →
  (corr :
      CorrespondingExtendedTashkinovTree G k
        e0 originalPrefix sigmaPrev
        (ett.series.data.tree
          (Fin.last ett.rounds).castSucc)) →
  corr.replacementSeries.data.coloring
        (Fin.last originalPrefix.rounds) =
      sigmaPrev →
  let replacementLast :
    Fin
      (originalPrefix.rounds + (1 : ℕ)) :=
    Fin.last originalPrefix.rounds;
  corr.replacementSeries.data.tree
        replacementLast.succ =
      ett.series.data.tree
        q.succ.castSucc →
  TashkinovStoredColors
        corr.replacementSeries.data
        replacementLast =
      TashkinovStoredColors
        ett.series.data q.castSucc →
  MaximumDefectiveChoice G e0
    (corr.replacementSeries.data.tree
      replacementLast.succ)
    (TashkinovStoredColors
      corr.replacementSeries.data
      replacementLast)
    (corr.replacementSeries.data.coloring
      replacementLast) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive q previousProper previousOneUncolored
      choice sigmaPrev hsigmaPrevProper hsigmaPrevOne hsigmaPrevStableQ hchoiceDefective
      hchoiceEdgeNew hsigmaPrevSelf newChoice originalPrefix corr hcorrFinalColor replacementLast
      hreplacementCurrentTree hreplacementStored
  exact {
    selected := sigmaPrev
    selectedProper := hsigmaPrevProper
    selectedOneUncolored := hsigmaPrevOne
    selectedStable := by
      rw [hreplacementCurrentTree, hreplacementStored, hcorrFinalColor]
      exact newChoice.selectedStable
    vertex := choice.vertex
    vertexDefective := by
      rw [hreplacementCurrentTree]
      exact newChoice.vertexDefective
    maximal := by
      intro pi w hpiProper hpiOne hpiStable hw
      rw [hreplacementCurrentTree, hreplacementStored, hcorrFinalColor]
        at hpiStable
      rw [hreplacementCurrentTree] at hw ⊢
      exact newChoice.maximal pi w hpiProper hpiOne hpiStable hw
    edge := choice.edge
    edgeDefective := by
      rw [hreplacementCurrentTree]
      exact newChoice.edgeDefective
    edgeIncident := choice.edgeIncident
    otherEndpoint := choice.otherEndpoint
    otherOutside := by
      rw [hreplacementCurrentTree]
      exact newChoice.otherOutside
    edgeEnds := choice.edgeEnds
    color := choice.color
    edgeColor := newChoice.edgeColor }

/-- Dependent contract shared by the terminal series reconstruction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperHseriesColorProperties3585Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [inst_2 : DecidableEq
        E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
    ∀ (_ closureTree : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (sigmaPrev : PartialEdgeColoring E k), IsProperEdgeColoring G sigmaPrev →
        IsOneEdgeUncolored sigmaPrev e0 →
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G sigmaPrev gamma choice.color;
    ∀ (u : V) (_ : H.Walk (Sum.inl choice.vertex) (Sum.inl u)), ett.rounds = (1 : ℕ) →
    ∀ (prefixInput : PartialEdgeColoring E k) (zeroPrefix : TashkinovSeries G k (0 : ℕ) e0
        prefixInput),
    let zeroLast : Fin ((0 : ℕ) + (1 : ℕ)) := Fin.last (0 : ℕ);
    let newStored : Finset (Fin k) := (insert choice.color ({ gamma } : Finset (Fin k)) : Finset
        (Fin k));
    let newEdges : Finset E := ({ choice.edge } : Finset E);
    let newKind : Option TashkinovExtensionKind := some TashkinovExtensionKind.PE;
    let newVertex : Option V := some choice.vertex;
    let newOutside : Option V := some choice.otherEndpoint;
    let newDelta : Option (Fin k) := some choice.color;
    let newGamma : Option (Fin k) := some gamma;
    let appendedData : TashkinovSeriesData G k ((0 : ℕ) + (1 : ℕ)) e0 := TashkinovSeriesDataAppend
        zeroPrefix.data closureTree sigma newStored newEdges newKind newVertex newOutside newDelta
        newGamma; appendedData.coloring zeroLast.castSucc = sigmaPrev →
    ∀ (extendedSeries : TashkinovSeries G k ((0 : ℕ) + (1 : ℕ)) e0 prefixInput),
        extendedSeries.data = TashkinovSeriesDataAppend zeroPrefix.data closureTree sigma
        newStored newEdges newKind newVertex newOutside newDelta newGamma →
    ∀ (hroundsEq : (0 : ℕ) + (1 : ℕ) = ett.rounds),
    let castSeries : {a b : ℕ} → a = b → TashkinovSeries G k a e0 prefixInput → TashkinovSeries G
        k b e0 prefixInput := fun {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 prefixInput)
        ↦ @Eq.ndrec Nat a (fun {b : Nat} ↦ @TashkinovSeries V E inst inst_1 inst_2 G k b e0
        prefixInput) S b h; (
    ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 prefixInput) (i : Fin (b + (1 : ℕ))),
        (castSeries h S).data.coloring i = S.data.coloring (Fin.cast (
    by omega
    ) i)) →
    let finalSeries : TashkinovSeries G k ett.rounds e0 prefixInput := castSeries hroundsEq
        extendedSeries;
    let _ : Fin (ett.rounds + (1 : ℕ)) → Fin (2 : ℕ) := fun (i : Fin (ett.rounds + (1 : ℕ))) ↦
        Fin.cast (
    by omega
    ) i; finalSeries.data.coloring (Fin.last ett.rounds) = sigma →
    ∀ (i : Fin (ett.rounds + (1 : ℕ))), IsProperEdgeColoring G (finalSeries.data.coloring i) ∧
        IsOneEdgeUncolored (finalSeries.data.coloring i) e0

/-- Dependent contract shared by the terminal series reconstruction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperBranch4454Conditions.{u_1, u_2} : Prop :=
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
    ∀ (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (sigmaPrev : PartialEdgeColoring E k), (1 : ℕ) < ett.rounds →
    ∀ (originalPrefix : ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last
        ett.rounds).castSucc) (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by
        have := GoldbergSeymour.TreeSequence.positive T
        omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ)), (
    ∀ (i : Fin (originalPrefix.rounds + (1 : ℕ))), originalPrefix.series.data.coloring i =
        ett.series.data.coloring (Fin.castLE (
    by
         have := GoldbergSeymour.TreeSequence.positive T
         omega
    ) i) ∧ originalPrefix.series.data.stored i = ett.series.data.stored (Fin.castLE (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ) i) ∧ originalPrefix.series.data.connectingEdges i = ett.series.data.connectingEdges
        (Fin.castLE (
    by
           have := GoldbergSeymour.TreeSequence.positive T
           omega
    ) i) ∧ originalPrefix.series.data.kind i = ett.series.data.kind (Fin.castLE (
    by
            have := GoldbergSeymour.TreeSequence.positive T
            omega
    ) i) ∧ TashkinovStoredColors originalPrefix.series.data i = TashkinovStoredColors
        ett.series.data (Fin.castLE (
    by
            have := GoldbergSeymour.TreeSequence.positive T
            omega
    ) i)) →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)), (0 : ℕ) < originalPrefix.rounds →
    let newStored : Finset (Fin k) := ({ choice.color } : Finset (Fin k));
    let newEdges : Finset E := ({ choice.edge } : Finset E);
    let newKind : Option TashkinovExtensionKind := some TashkinovExtensionKind.SE;
    let newVertex : Option V := some choice.vertex;
    let newOutside : Option V := some choice.otherEndpoint;
    let newDelta : Option (Fin k) := some choice.color;
    let newGamma : Option (Fin k) := none;
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
    ))) originalPrefix sigmaPrev (@TashkinovSeriesData.tree V E G k (@ExtendedTashkinovTree.rounds
        V E inst inst_1 inst_2 G k e0 input T generating ett) e0 (@TashkinovSeries.data V E inst
        inst_1 inst_2 G k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T
        generating ett) e0 input (@ExtendedTashkinovTree.series V E inst inst_1 inst_2 G k e0
        input T generating ett)) (@Fin.castSucc (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett)
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (Fin.last
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett))))
        corr)) S b h; (
    ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 corr.replacementInput) (i : Fin (b + (1
        : ℕ))), (castSeries h S).data.stored i = S.data.stored (Fin.cast (
    by omega
    ) i)) → (
    ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 corr.replacementInput) (i : Fin (b + (1
        : ℕ))), (castSeries h S).data.connectingEdges i = S.data.connectingEdges (Fin.cast (
    by omega
    ) i)) → (
    ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 corr.replacementInput) (i : Fin (b + (1
        : ℕ))), (castSeries h S).data.kind i = S.data.kind (Fin.cast (
    by omega
    ) i)) →
    let finalSeries : TashkinovSeries G k ett.rounds e0 corr.replacementInput := castSeries
        hroundsEq extendedSeries;
    let _ : Fin (ett.rounds + (1 : ℕ)) → Fin (originalPrefix.rounds + (2 : ℕ)) := fun (i : Fin
        (ett.rounds + (1 : ℕ))) ↦ Fin.cast (
    by
     have := GoldbergSeymour.TreeSequence.positive T
     omega
    ) i;
    ∀ (i : Fin (ett.rounds + (1 : ℕ))), (↑i : ℕ) < ett.rounds → finalSeries.data.stored i =
        ett.series.data.stored i ∧ finalSeries.data.connectingEdges i =
        ett.series.data.connectingEdges i ∧ finalSeries.data.kind i = ett.series.data.kind i

/-- Dependent contract shared by the terminal series reconstruction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperBranch4512Conditions.{u_1, u_2} : Prop :=
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
    ⟩ : Fin ett.rounds); q.succ = Fin.last ett.rounds →
    ∀ (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)),
        ett.series.data.stored q.succ = ({ choice.color } : Finset (Fin k)) →
        ett.series.data.connectingEdges q.succ = ({ choice.edge } : Finset E) →
        ett.series.data.kind q.succ = some TashkinovExtensionKind.SE →
    ∀ (sigmaPrev : PartialEdgeColoring E k), (1 : ℕ) < ett.rounds →
    ∀ (originalPrefix : ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last
        ett.rounds).castSucc) (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by
        have := GoldbergSeymour.TreeSequence.positive T
        omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))), originalPrefix.rounds = ett.rounds - (1 : ℕ) →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)), (0 : ℕ) < originalPrefix.rounds →
    let newStored : Finset (Fin k) := ({ choice.color } : Finset (Fin k));
    let newEdges : Finset E := ({ choice.edge } : Finset E);
    let newKind : Option TashkinovExtensionKind := some TashkinovExtensionKind.SE;
    let newVertex : Option V := some choice.vertex;
    let newOutside : Option V := some choice.otherEndpoint;
    let newDelta : Option (Fin k) := some choice.color;
    let newGamma : Option (Fin k) := none;
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
    ))) originalPrefix sigmaPrev (@TashkinovSeriesData.tree V E G k (@ExtendedTashkinovTree.rounds
        V E inst inst_1 inst_2 G k e0 input T generating ett) e0 (@TashkinovSeries.data V E inst
        inst_1 inst_2 G k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T
        generating ett) e0 input (@ExtendedTashkinovTree.series V E inst inst_1 inst_2 G k e0
        input T generating ett)) (@Fin.castSucc (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett)
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (Fin.last
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett))))
        corr)) S b h; (
    ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 corr.replacementInput) (i : Fin (b + (1
        : ℕ))), (castSeries h S).data.stored i = S.data.stored (Fin.cast (
    by omega
    ) i)) → (
    ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 corr.replacementInput) (i : Fin (b + (1
        : ℕ))), (castSeries h S).data.connectingEdges i = S.data.connectingEdges (Fin.cast (
    by omega
    ) i)) → (
    ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 corr.replacementInput) (i : Fin (b + (1
        : ℕ))), (castSeries h S).data.kind i = S.data.kind (Fin.cast (
    by omega
    ) i)) →
    let finalSeries : TashkinovSeries G k ett.rounds e0 corr.replacementInput := castSeries
        hroundsEq extendedSeries;
    let _ : Fin (ett.rounds + (1 : ℕ)) → Fin (originalPrefix.rounds + (2 : ℕ)) := fun (i : Fin
        (ett.rounds + (1 : ℕ))) ↦ Fin.cast (
    by
     have := GoldbergSeymour.TreeSequence.positive T
     omega
    ) i;
    ∀ (i : Fin (ett.rounds + (1 : ℕ))), ¬(↑i : ℕ) < ett.rounds → finalSeries.data.stored i =
        ett.series.data.stored i ∧ finalSeries.data.connectingEdges i =
        ett.series.data.connectingEdges i ∧ finalSeries.data.kind i = ett.series.data.kind i

/-- Dependent contract shared by the terminal series reconstruction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperHseriesStable4663Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [inst_2 : DecidableEq
        E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k), StableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) (ett.series.data.coloring
        (Fin.last ett.rounds)) sigma →
    ∀ (_ closureTree : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
     have := GoldbergSeymour.TreeSequence.positive T
     omega
    ⟩ : Fin ett.rounds);
    ∀ (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (sigmaPrev : PartialEdgeColoring E k), (1 : ℕ) < ett.rounds →
    ∀ (originalPrefix : ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last
        ett.rounds).castSucc) (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by
        have := GoldbergSeymour.TreeSequence.positive T
        omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ)), (
    ∀ (i : Fin (originalPrefix.rounds + (2 : ℕ))), originalPrefix.series.data.tree i =
        ett.series.data.tree (Fin.castLE (
    by
        have := GoldbergSeymour.TreeSequence.positive T
        omega
    ) i)) → (
    ∀ (i : Fin (originalPrefix.rounds + (1 : ℕ))), originalPrefix.series.data.coloring i =
        ett.series.data.coloring (Fin.castLE (
    by
         have := GoldbergSeymour.TreeSequence.positive T
         omega
    ) i) ∧ originalPrefix.series.data.stored i = ett.series.data.stored (Fin.castLE (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ) i) ∧ originalPrefix.series.data.connectingEdges i = ett.series.data.connectingEdges
        (Fin.castLE (
    by
           have := GoldbergSeymour.TreeSequence.positive T
           omega
    ) i) ∧ originalPrefix.series.data.kind i = ett.series.data.kind (Fin.castLE (
    by
            have := GoldbergSeymour.TreeSequence.positive T
            omega
    ) i) ∧ TashkinovStoredColors originalPrefix.series.data i = TashkinovStoredColors
        ett.series.data (Fin.castLE (
    by
            have := GoldbergSeymour.TreeSequence.positive T
            omega
    ) i)) →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)), (0 : ℕ) < originalPrefix.rounds →
    let newStored : Finset (Fin k) := ({ choice.color } : Finset (Fin k));
    let newEdges : Finset E := ({ choice.edge } : Finset E);
    let newKind : Option TashkinovExtensionKind := some TashkinovExtensionKind.SE;
    let newVertex : Option V := some choice.vertex;
    let newOutside : Option V := some choice.otherEndpoint;
    let newDelta : Option (Fin k) := some choice.color;
    let newGamma : Option (Fin k) := none;
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
    ))) originalPrefix sigmaPrev (@TashkinovSeriesData.tree V E G k (@ExtendedTashkinovTree.rounds
        V E inst inst_1 inst_2 G k e0 input T generating ett) e0 (@TashkinovSeries.data V E inst
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
        hroundsEq extendedSeries; finalSeries.data.coloring (Fin.last ett.rounds) = sigma →
    let _ : Fin (ett.rounds + (1 : ℕ)) → Fin (originalPrefix.rounds + (2 : ℕ)) := fun (i : Fin
        (ett.rounds + (1 : ℕ))) ↦ Fin.cast (
    by
     have := GoldbergSeymour.TreeSequence.positive T
     omega
    ) i;
    ∀ (i : Fin ett.rounds), StableColoring (ett.series.data.tree i.succ.castSucc)
        (TashkinovStoredColors ett.series.data i.succ) (ett.series.data.coloring i.succ)
        (finalSeries.data.coloring i.succ)

/-- Dependent contract shared by the terminal series reconstruction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperBranch5026Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [inst_2 : DecidableEq
        E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
     have := GoldbergSeymour.TreeSequence.positive T
     omega
    ⟩ : Fin ett.rounds); StableColoring (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.succ) (ett.series.data.coloring q.succ) sigma →
    ∀ (gamma : Fin k) (secondStable : PartialEdgeColoring E k), IsProperEdgeColoring G
        secondStable → IsOneEdgeUncolored secondStable e0 →
    ∀ (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)),
        StableColoring (ett.series.data.tree q.succ.castSucc) (insert choice.color
        (TashkinovStoredColors ett.series.data q.castSucc) : Finset (Fin k)) choice.selected
        secondStable → ett.series.data.coloring q.succ = TwoColorComponentSwap G secondStable
        gamma choice.color (Sum.inl choice.vertex) → (
    ∀ (w : V), gamma ∈ MissingColors G secondStable w ∨ choice.color ∈ MissingColors G
        secondStable w → @SimpleGraph.degree (Sum V E) (@TwoColorIncidenceGraph V E G k
        secondStable gamma (@MaximumDefectiveChoice.color V E inst inst_1 G k e0
        (@TashkinovSeriesData.tree V E G k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G
        k e0 input T generating ett) e0 (@TashkinovSeries.data V E inst inst_1 inst_2 G k
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett) e0
        input (@ExtendedTashkinovTree.series V E inst inst_1 inst_2 G k e0 input T generating
        ett)) (@Fin.castSucc (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett)
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (@Fin.succ
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett) q)))
        (@TashkinovStoredColors V E inst_1 G k (@ExtendedTashkinovTree.rounds V E inst inst_1
        inst_2 G k e0 input T generating ett) e0 (@TashkinovSeries.data V E inst inst_1 inst_2 G k
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett) e0
        input (@ExtendedTashkinovTree.series V E inst inst_1 inst_2 G k e0 input T generating
        ett)) (@Fin.castSucc (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T
        generating ett) q)) (@TashkinovSeriesData.coloring V E G k (@ExtendedTashkinovTree.rounds
        V E inst inst_1 inst_2 G k e0 input T generating ett) e0 (@TashkinovSeries.data V E inst
        inst_1 inst_2 G k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T
        generating ett) e0 input (@ExtendedTashkinovTree.series V E inst inst_1 inst_2 G k e0
        input T generating ett)) (@Fin.castSucc (@ExtendedTashkinovTree.rounds V E inst inst_1
        inst_2 G k e0 input T generating ett) q)) choice)) (@Sum.inl V E w) (@Subtype.fintype (Sum
        V E) (@Membership.mem (Sum V E) (Set (Sum V E)) (@Set.instMembership (Sum V E))
        (@SimpleGraph.neighborSet (Sum V E) (@TwoColorIncidenceGraph V E G k secondStable gamma
        (@MaximumDefectiveChoice.color V E inst inst_1 G k e0 (@TashkinovSeriesData.tree V E G k
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett) e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k (@ExtendedTashkinovTree.rounds V E inst
        inst_1 inst_2 G k e0 input T generating ett) e0 input (@ExtendedTashkinovTree.series V E
        inst inst_1 inst_2 G k e0 input T generating ett)) (@Fin.castSucc (@HAdd.hAdd Nat Nat Nat
        (@instHAdd Nat instAddNat) (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0
        input T generating ett) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Fin.succ (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating
        ett) q))) (@TashkinovStoredColors V E inst_1 G k (@ExtendedTashkinovTree.rounds V E inst
        inst_1 inst_2 G k e0 input T generating ett) e0 (@TashkinovSeries.data V E inst inst_1
        inst_2 G k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating
        ett) e0 input (@ExtendedTashkinovTree.series V E inst inst_1 inst_2 G k e0 input T
        generating ett)) (@Fin.castSucc (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k
        e0 input T generating ett) q)) (@TashkinovSeriesData.coloring V E G k
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett) e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k (@ExtendedTashkinovTree.rounds V E inst
        inst_1 inst_2 G k e0 input T generating ett) e0 input (@ExtendedTashkinovTree.series V E
        inst inst_1 inst_2 G k e0 input T generating ett)) (@Fin.castSucc
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett) q))
        choice)) (@Sum.inl V E w))) (fun (a : Sum V E) ↦ @SimpleGraph.neighborSet.memDecidable
        (Sum V E) (@TwoColorIncidenceGraph V E G k secondStable gamma
        (@MaximumDefectiveChoice.color V E inst inst_1 G k e0 (@TashkinovSeriesData.tree V E G k
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett) e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k (@ExtendedTashkinovTree.rounds V E inst
        inst_1 inst_2 G k e0 input T generating ett) e0 input (@ExtendedTashkinovTree.series V E
        inst inst_1 inst_2 G k e0 input T generating ett)) (@Fin.castSucc (@HAdd.hAdd Nat Nat Nat
        (@instHAdd Nat instAddNat) (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0
        input T generating ett) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Fin.succ (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating
        ett) q))) (@TashkinovStoredColors V E inst_1 G k (@ExtendedTashkinovTree.rounds V E inst
        inst_1 inst_2 G k e0 input T generating ett) e0 (@TashkinovSeries.data V E inst inst_1
        inst_2 G k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating
        ett) e0 input (@ExtendedTashkinovTree.series V E inst inst_1 inst_2 G k e0 input T
        generating ett)) (@Fin.castSucc (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k
        e0 input T generating ett) q)) (@TashkinovSeriesData.coloring V E G k
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett) e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k (@ExtendedTashkinovTree.rounds V E inst
        inst_1 inst_2 G k e0 input T generating ett) e0 input (@ExtendedTashkinovTree.series V E
        inst inst_1 inst_2 G k e0 input T generating ett)) (@Fin.castSucc
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett) q))
        choice)) (@Sum.inl V E w) (fun (a b : Sum V E) ↦ Classical.propDecidable (@SimpleGraph.Adj
        (Sum V E) (@TwoColorIncidenceGraph V E G k secondStable gamma
        (@MaximumDefectiveChoice.color V E inst inst_1 G k e0 (@TashkinovSeriesData.tree V E G k
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett) e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k (@ExtendedTashkinovTree.rounds V E inst
        inst_1 inst_2 G k e0 input T generating ett) e0 input (@ExtendedTashkinovTree.series V E
        inst inst_1 inst_2 G k e0 input T generating ett)) (@Fin.castSucc (@HAdd.hAdd Nat Nat Nat
        (@instHAdd Nat instAddNat) (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0
        input T generating ett) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Fin.succ (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating
        ett) q))) (@TashkinovStoredColors V E inst_1 G k (@ExtendedTashkinovTree.rounds V E inst
        inst_1 inst_2 G k e0 input T generating ett) e0 (@TashkinovSeries.data V E inst inst_1
        inst_2 G k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating
        ett) e0 input (@ExtendedTashkinovTree.series V E inst inst_1 inst_2 G k e0 input T
        generating ett)) (@Fin.castSucc (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k
        e0 input T generating ett) q)) (@TashkinovSeriesData.coloring V E G k
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett) e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k (@ExtendedTashkinovTree.rounds V E inst
        inst_1 inst_2 G k e0 input T generating ett) e0 input (@ExtendedTashkinovTree.series V E
        inst inst_1 inst_2 G k e0 input T generating ett)) (@Fin.castSucc
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett) q))
        choice)) a b)) a) (@instFintypeSum V E inst inst_1)) ≤ (1 : ℕ)) →
    ∀ (u : V) (path : (TwoColorIncidenceGraph G secondStable gamma choice.color).Walk (Sum.inl u)
        (Sum.inl choice.vertex)), (
    ∀ (x : V ⊕ E), @SimpleGraph.degree (Sum V E) (@TwoColorIncidenceGraph V E G k secondStable
        gamma (@MaximumDefectiveChoice.color V E inst inst_1 G k e0 (@TashkinovSeriesData.tree V E
        G k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett)
        e0 (@TashkinovSeries.data V E inst inst_1 inst_2 G k (@ExtendedTashkinovTree.rounds V E
        inst inst_1 inst_2 G k e0 input T generating ett) e0 input (@ExtendedTashkinovTree.series
        V E inst inst_1 inst_2 G k e0 input T generating ett)) (@Fin.castSucc (@HAdd.hAdd Nat Nat
        Nat (@instHAdd Nat instAddNat) (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k
        e0 input T generating ett) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Fin.succ (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating
        ett) q))) (@TashkinovStoredColors V E inst_1 G k (@ExtendedTashkinovTree.rounds V E inst
        inst_1 inst_2 G k e0 input T generating ett) e0 (@TashkinovSeries.data V E inst inst_1
        inst_2 G k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating
        ett) e0 input (@ExtendedTashkinovTree.series V E inst inst_1 inst_2 G k e0 input T
        generating ett)) (@Fin.castSucc (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k
        e0 input T generating ett) q)) (@TashkinovSeriesData.coloring V E G k
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett) e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k (@ExtendedTashkinovTree.rounds V E inst
        inst_1 inst_2 G k e0 input T generating ett) e0 input (@ExtendedTashkinovTree.series V E
        inst inst_1 inst_2 G k e0 input T generating ett)) (@Fin.castSucc
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett) q))
        choice)) x (@Fintype.ofFinite (@Set.Elem (Sum V E) (@SimpleGraph.neighborSet (Sum V E)
        (@TwoColorIncidenceGraph V E G k secondStable gamma (@MaximumDefectiveChoice.color V E
        inst inst_1 G k e0 (@TashkinovSeriesData.tree V E G k (@ExtendedTashkinovTree.rounds V E
        inst inst_1 inst_2 G k e0 input T generating ett) e0 (@TashkinovSeries.data V E inst
        inst_1 inst_2 G k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T
        generating ett) e0 input (@ExtendedTashkinovTree.series V E inst inst_1 inst_2 G k e0
        input T generating ett)) (@Fin.castSucc (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett)
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (@Fin.succ
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett) q)))
        (@TashkinovStoredColors V E inst_1 G k (@ExtendedTashkinovTree.rounds V E inst inst_1
        inst_2 G k e0 input T generating ett) e0 (@TashkinovSeries.data V E inst inst_1 inst_2 G k
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett) e0
        input (@ExtendedTashkinovTree.series V E inst inst_1 inst_2 G k e0 input T generating
        ett)) (@Fin.castSucc (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T
        generating ett) q)) (@TashkinovSeriesData.coloring V E G k (@ExtendedTashkinovTree.rounds
        V E inst inst_1 inst_2 G k e0 input T generating ett) e0 (@TashkinovSeries.data V E inst
        inst_1 inst_2 G k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T
        generating ett) e0 input (@ExtendedTashkinovTree.series V E inst inst_1 inst_2 G k e0
        input T generating ett)) (@Fin.castSucc (@ExtendedTashkinovTree.rounds V E inst inst_1
        inst_2 G k e0 input T generating ett) q)) choice)) x)) (@Subtype.finite (Sum V E)
        (@Finite.instSum V E (@Finite.of_fintype V inst) (@Finite.of_fintype E inst_1))
        (@Membership.mem (Sum V E) (Set (Sum V E)) (@Set.instMembership (Sum V E))
        (@SimpleGraph.neighborSet (Sum V E) (@TwoColorIncidenceGraph V E G k secondStable gamma
        (@MaximumDefectiveChoice.color V E inst inst_1 G k e0 (@TashkinovSeriesData.tree V E G k
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett) e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k (@ExtendedTashkinovTree.rounds V E inst
        inst_1 inst_2 G k e0 input T generating ett) e0 input (@ExtendedTashkinovTree.series V E
        inst inst_1 inst_2 G k e0 input T generating ett)) (@Fin.castSucc (@HAdd.hAdd Nat Nat Nat
        (@instHAdd Nat instAddNat) (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0
        input T generating ett) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Fin.succ (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating
        ett) q))) (@TashkinovStoredColors V E inst_1 G k (@ExtendedTashkinovTree.rounds V E inst
        inst_1 inst_2 G k e0 input T generating ett) e0 (@TashkinovSeries.data V E inst inst_1
        inst_2 G k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating
        ett) e0 input (@ExtendedTashkinovTree.series V E inst inst_1 inst_2 G k e0 input T
        generating ett)) (@Fin.castSucc (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k
        e0 input T generating ett) q)) (@TashkinovSeriesData.coloring V E G k
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett) e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k (@ExtendedTashkinovTree.rounds V E inst
        inst_1 inst_2 G k e0 input T generating ett) e0 input (@ExtendedTashkinovTree.series V E
        inst inst_1 inst_2 G k e0 input T generating ett)) (@Fin.castSucc
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett) q))
        choice)) x)))) ≤ (2 : ℕ)) → (
    ∀ x ∈ path.support,
    ∀ (y : V ⊕ E), (TwoColorIncidenceGraph G secondStable gamma choice.color).Adj x y → y ∈
        path.support) → (
    ∀ y ∈ TwoColorComponent G secondStable gamma choice.color (Sum.inl choice.vertex), y ∈
        path.support) → (
    ∀ (e : E), Sum.inr e ∈ TwoColorComponent G secondStable gamma choice.color (Sum.inl
        choice.vertex) → secondStable e = some gamma ∨ secondStable e = some choice.color) →
        secondStable choice.edge = some choice.color → (
    ∀ (e : E), TreeIncidentEdge (ett.series.data.tree q.succ.castSucc) e → Sum.inr e ∈
        TwoColorComponent G secondStable gamma choice.color (Sum.inl choice.vertex) → e =
        choice.edge) → (
    ∀ (e : E), TreeIncidentEdge (ett.series.data.tree q.succ.castSucc) e → Sum.inr e ∈
        TwoColorComponent G sigma gamma choice.color (Sum.inl choice.vertex) → e = choice.edge) →
    let undone : PartialEdgeColoring E k := TwoColorComponentSwap G sigma gamma choice.color
        (Sum.inl choice.vertex); TreeMissingColors secondStable (ett.series.data.tree
        q.succ.castSucc) = TreeMissingColors choice.selected (ett.series.data.tree
        q.succ.castSucc) → (
    ∀ (e : E), Sum.inr e ∈ TwoColorComponent G sigma gamma choice.color (Sum.inl choice.vertex) →
        sigma e = some gamma ∨ sigma e = some choice.color) → choice.color ∈ MissingColors G sigma
        choice.vertex → (
    ∀ c ∈ TreeMissingColors choice.selected (ett.series.data.tree q.succ.castSucc) ∪ (insert
        choice.color (TashkinovStoredColors ett.series.data q.castSucc) : Finset (Fin k)), c ∈
        TreeMissingColors (ett.series.data.coloring q.succ) (ett.series.data.tree q.succ.castSucc)
        ∪ TashkinovStoredColors ett.series.data q.succ) → gamma ∈ TreeMissingColors
        choice.selected (ett.series.data.tree q.succ.castSucc) ∪ (insert choice.color
        (TashkinovStoredColors ett.series.data q.castSucc) : Finset (Fin k)) →
    ∀ (f : E), TreeIncidentEdge (ett.series.data.tree q.succ.castSucc) f → (
    ∃ c ∈ TreeMissingColors secondStable (ett.series.data.tree q.succ.castSucc) ∪ (insert
        choice.color (TashkinovStoredColors ett.series.data q.castSucc) : Finset (Fin k)),
        secondStable f = some c) → undone f = secondStable f

/-- Dependent contract shared by the terminal series reconstruction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperBranch5085Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [inst_2 : DecidableEq
        E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
    ∀ (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
     have := GoldbergSeymour.TreeSequence.positive T
     omega
    ⟩ : Fin ett.rounds); StableColoring (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.succ) (ett.series.data.coloring q.succ) sigma →
    ∀ (gamma : Fin k) (secondStable : PartialEdgeColoring E k) (choice : MaximumDefectiveChoice G
        e0 (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors ett.series.data
        q.castSucc) (ett.series.data.coloring q.castSucc)), ett.series.data.coloring q.succ =
        TwoColorComponentSwap G secondStable gamma choice.color (Sum.inl choice.vertex) →
        IsProperEdgeColoring G (ett.series.data.coloring q.succ) → IsOneEdgeUncolored
        (ett.series.data.coloring q.succ) e0 → (
    ∀ (w : V), gamma ∈ MissingColors G secondStable w ∨ choice.color ∈ MissingColors G
        secondStable w → @SimpleGraph.degree (Sum V E) (@TwoColorIncidenceGraph V E G k
        secondStable gamma (@MaximumDefectiveChoice.color V E inst inst_1 G k e0
        (@TashkinovSeriesData.tree V E G k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G
        k e0 input T generating ett) e0 (@TashkinovSeries.data V E inst inst_1 inst_2 G k
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett) e0
        input (@ExtendedTashkinovTree.series V E inst inst_1 inst_2 G k e0 input T generating
        ett)) (@Fin.castSucc (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett)
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (@Fin.succ
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett) q)))
        (@TashkinovStoredColors V E inst_1 G k (@ExtendedTashkinovTree.rounds V E inst inst_1
        inst_2 G k e0 input T generating ett) e0 (@TashkinovSeries.data V E inst inst_1 inst_2 G k
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett) e0
        input (@ExtendedTashkinovTree.series V E inst inst_1 inst_2 G k e0 input T generating
        ett)) (@Fin.castSucc (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T
        generating ett) q)) (@TashkinovSeriesData.coloring V E G k (@ExtendedTashkinovTree.rounds
        V E inst inst_1 inst_2 G k e0 input T generating ett) e0 (@TashkinovSeries.data V E inst
        inst_1 inst_2 G k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T
        generating ett) e0 input (@ExtendedTashkinovTree.series V E inst inst_1 inst_2 G k e0
        input T generating ett)) (@Fin.castSucc (@ExtendedTashkinovTree.rounds V E inst inst_1
        inst_2 G k e0 input T generating ett) q)) choice)) (@Sum.inl V E w) (@Subtype.fintype (Sum
        V E) (@Membership.mem (Sum V E) (Set (Sum V E)) (@Set.instMembership (Sum V E))
        (@SimpleGraph.neighborSet (Sum V E) (@TwoColorIncidenceGraph V E G k secondStable gamma
        (@MaximumDefectiveChoice.color V E inst inst_1 G k e0 (@TashkinovSeriesData.tree V E G k
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett) e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k (@ExtendedTashkinovTree.rounds V E inst
        inst_1 inst_2 G k e0 input T generating ett) e0 input (@ExtendedTashkinovTree.series V E
        inst inst_1 inst_2 G k e0 input T generating ett)) (@Fin.castSucc (@HAdd.hAdd Nat Nat Nat
        (@instHAdd Nat instAddNat) (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0
        input T generating ett) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Fin.succ (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating
        ett) q))) (@TashkinovStoredColors V E inst_1 G k (@ExtendedTashkinovTree.rounds V E inst
        inst_1 inst_2 G k e0 input T generating ett) e0 (@TashkinovSeries.data V E inst inst_1
        inst_2 G k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating
        ett) e0 input (@ExtendedTashkinovTree.series V E inst inst_1 inst_2 G k e0 input T
        generating ett)) (@Fin.castSucc (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k
        e0 input T generating ett) q)) (@TashkinovSeriesData.coloring V E G k
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett) e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k (@ExtendedTashkinovTree.rounds V E inst
        inst_1 inst_2 G k e0 input T generating ett) e0 input (@ExtendedTashkinovTree.series V E
        inst inst_1 inst_2 G k e0 input T generating ett)) (@Fin.castSucc
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett) q))
        choice)) (@Sum.inl V E w))) (fun (a : Sum V E) ↦ @SimpleGraph.neighborSet.memDecidable
        (Sum V E) (@TwoColorIncidenceGraph V E G k secondStable gamma
        (@MaximumDefectiveChoice.color V E inst inst_1 G k e0 (@TashkinovSeriesData.tree V E G k
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett) e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k (@ExtendedTashkinovTree.rounds V E inst
        inst_1 inst_2 G k e0 input T generating ett) e0 input (@ExtendedTashkinovTree.series V E
        inst inst_1 inst_2 G k e0 input T generating ett)) (@Fin.castSucc (@HAdd.hAdd Nat Nat Nat
        (@instHAdd Nat instAddNat) (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0
        input T generating ett) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Fin.succ (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating
        ett) q))) (@TashkinovStoredColors V E inst_1 G k (@ExtendedTashkinovTree.rounds V E inst
        inst_1 inst_2 G k e0 input T generating ett) e0 (@TashkinovSeries.data V E inst inst_1
        inst_2 G k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating
        ett) e0 input (@ExtendedTashkinovTree.series V E inst inst_1 inst_2 G k e0 input T
        generating ett)) (@Fin.castSucc (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k
        e0 input T generating ett) q)) (@TashkinovSeriesData.coloring V E G k
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett) e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k (@ExtendedTashkinovTree.rounds V E inst
        inst_1 inst_2 G k e0 input T generating ett) e0 input (@ExtendedTashkinovTree.series V E
        inst inst_1 inst_2 G k e0 input T generating ett)) (@Fin.castSucc
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett) q))
        choice)) (@Sum.inl V E w) (fun (a b : Sum V E) ↦ Classical.propDecidable (@SimpleGraph.Adj
        (Sum V E) (@TwoColorIncidenceGraph V E G k secondStable gamma
        (@MaximumDefectiveChoice.color V E inst inst_1 G k e0 (@TashkinovSeriesData.tree V E G k
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett) e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k (@ExtendedTashkinovTree.rounds V E inst
        inst_1 inst_2 G k e0 input T generating ett) e0 input (@ExtendedTashkinovTree.series V E
        inst inst_1 inst_2 G k e0 input T generating ett)) (@Fin.castSucc (@HAdd.hAdd Nat Nat Nat
        (@instHAdd Nat instAddNat) (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0
        input T generating ett) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Fin.succ (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating
        ett) q))) (@TashkinovStoredColors V E inst_1 G k (@ExtendedTashkinovTree.rounds V E inst
        inst_1 inst_2 G k e0 input T generating ett) e0 (@TashkinovSeries.data V E inst inst_1
        inst_2 G k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating
        ett) e0 input (@ExtendedTashkinovTree.series V E inst inst_1 inst_2 G k e0 input T
        generating ett)) (@Fin.castSucc (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k
        e0 input T generating ett) q)) (@TashkinovSeriesData.coloring V E G k
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett) e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k (@ExtendedTashkinovTree.rounds V E inst
        inst_1 inst_2 G k e0 input T generating ett) e0 input (@ExtendedTashkinovTree.series V E
        inst inst_1 inst_2 G k e0 input T generating ett)) (@Fin.castSucc
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett) q))
        choice)) a b)) a) (@instFintypeSum V E inst inst_1)) ≤ (1 : ℕ)) →
    ∀ (u : V) (path : (TwoColorIncidenceGraph G secondStable gamma choice.color).Walk (Sum.inl u)
        (Sum.inl choice.vertex)), (
    ∀ (x : V ⊕ E), @SimpleGraph.degree (Sum V E) (@TwoColorIncidenceGraph V E G k secondStable
        gamma (@MaximumDefectiveChoice.color V E inst inst_1 G k e0 (@TashkinovSeriesData.tree V E
        G k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett)
        e0 (@TashkinovSeries.data V E inst inst_1 inst_2 G k (@ExtendedTashkinovTree.rounds V E
        inst inst_1 inst_2 G k e0 input T generating ett) e0 input (@ExtendedTashkinovTree.series
        V E inst inst_1 inst_2 G k e0 input T generating ett)) (@Fin.castSucc (@HAdd.hAdd Nat Nat
        Nat (@instHAdd Nat instAddNat) (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k
        e0 input T generating ett) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Fin.succ (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating
        ett) q))) (@TashkinovStoredColors V E inst_1 G k (@ExtendedTashkinovTree.rounds V E inst
        inst_1 inst_2 G k e0 input T generating ett) e0 (@TashkinovSeries.data V E inst inst_1
        inst_2 G k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating
        ett) e0 input (@ExtendedTashkinovTree.series V E inst inst_1 inst_2 G k e0 input T
        generating ett)) (@Fin.castSucc (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k
        e0 input T generating ett) q)) (@TashkinovSeriesData.coloring V E G k
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett) e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k (@ExtendedTashkinovTree.rounds V E inst
        inst_1 inst_2 G k e0 input T generating ett) e0 input (@ExtendedTashkinovTree.series V E
        inst inst_1 inst_2 G k e0 input T generating ett)) (@Fin.castSucc
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett) q))
        choice)) x (@Fintype.ofFinite (@Set.Elem (Sum V E) (@SimpleGraph.neighborSet (Sum V E)
        (@TwoColorIncidenceGraph V E G k secondStable gamma (@MaximumDefectiveChoice.color V E
        inst inst_1 G k e0 (@TashkinovSeriesData.tree V E G k (@ExtendedTashkinovTree.rounds V E
        inst inst_1 inst_2 G k e0 input T generating ett) e0 (@TashkinovSeries.data V E inst
        inst_1 inst_2 G k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T
        generating ett) e0 input (@ExtendedTashkinovTree.series V E inst inst_1 inst_2 G k e0
        input T generating ett)) (@Fin.castSucc (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett)
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (@Fin.succ
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett) q)))
        (@TashkinovStoredColors V E inst_1 G k (@ExtendedTashkinovTree.rounds V E inst inst_1
        inst_2 G k e0 input T generating ett) e0 (@TashkinovSeries.data V E inst inst_1 inst_2 G k
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett) e0
        input (@ExtendedTashkinovTree.series V E inst inst_1 inst_2 G k e0 input T generating
        ett)) (@Fin.castSucc (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T
        generating ett) q)) (@TashkinovSeriesData.coloring V E G k (@ExtendedTashkinovTree.rounds
        V E inst inst_1 inst_2 G k e0 input T generating ett) e0 (@TashkinovSeries.data V E inst
        inst_1 inst_2 G k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T
        generating ett) e0 input (@ExtendedTashkinovTree.series V E inst inst_1 inst_2 G k e0
        input T generating ett)) (@Fin.castSucc (@ExtendedTashkinovTree.rounds V E inst inst_1
        inst_2 G k e0 input T generating ett) q)) choice)) x)) (@Subtype.finite (Sum V E)
        (@Finite.instSum V E (@Finite.of_fintype V inst) (@Finite.of_fintype E inst_1))
        (@Membership.mem (Sum V E) (Set (Sum V E)) (@Set.instMembership (Sum V E))
        (@SimpleGraph.neighborSet (Sum V E) (@TwoColorIncidenceGraph V E G k secondStable gamma
        (@MaximumDefectiveChoice.color V E inst inst_1 G k e0 (@TashkinovSeriesData.tree V E G k
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett) e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k (@ExtendedTashkinovTree.rounds V E inst
        inst_1 inst_2 G k e0 input T generating ett) e0 input (@ExtendedTashkinovTree.series V E
        inst inst_1 inst_2 G k e0 input T generating ett)) (@Fin.castSucc (@HAdd.hAdd Nat Nat Nat
        (@instHAdd Nat instAddNat) (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0
        input T generating ett) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Fin.succ (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating
        ett) q))) (@TashkinovStoredColors V E inst_1 G k (@ExtendedTashkinovTree.rounds V E inst
        inst_1 inst_2 G k e0 input T generating ett) e0 (@TashkinovSeries.data V E inst inst_1
        inst_2 G k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating
        ett) e0 input (@ExtendedTashkinovTree.series V E inst inst_1 inst_2 G k e0 input T
        generating ett)) (@Fin.castSucc (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k
        e0 input T generating ett) q)) (@TashkinovSeriesData.coloring V E G k
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett) e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k (@ExtendedTashkinovTree.rounds V E inst
        inst_1 inst_2 G k e0 input T generating ett) e0 input (@ExtendedTashkinovTree.series V E
        inst inst_1 inst_2 G k e0 input T generating ett)) (@Fin.castSucc
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett) q))
        choice)) x)))) ≤ (2 : ℕ)) → (
    ∀ x ∈ path.support,
    ∀ (y : V ⊕ E), (TwoColorIncidenceGraph G secondStable gamma choice.color).Adj x y → y ∈
        path.support) → (
    ∀ y ∈ TwoColorComponent G secondStable gamma choice.color (Sum.inl choice.vertex), y ∈
        path.support) → (
    ∀ (e : E), Sum.inr e ∈ TwoColorComponent G secondStable gamma choice.color (Sum.inl
        choice.vertex) → secondStable e = some gamma ∨ secondStable e = some choice.color) →
        secondStable choice.edge = some choice.color → (
    ∀ (e : E), TreeIncidentEdge (ett.series.data.tree q.succ.castSucc) e → Sum.inr e ∈
        TwoColorComponent G secondStable gamma choice.color (Sum.inl choice.vertex) → e =
        choice.edge) → (
    ∀ (e : E), TreeIncidentEdge (ett.series.data.tree q.succ.castSucc) e → Sum.inr e ∈
        TwoColorComponent G sigma gamma choice.color (Sum.inl choice.vertex) → e = choice.edge) →
    let undone : PartialEdgeColoring E k := TwoColorComponentSwap G sigma gamma choice.color
        (Sum.inl choice.vertex); TreeMissingColors secondStable (ett.series.data.tree
        q.succ.castSucc) = TreeMissingColors choice.selected (ett.series.data.tree
        q.succ.castSucc) → (
    ∀ (e : E), Sum.inr e ∈ TwoColorComponent G sigma gamma choice.color (Sum.inl choice.vertex) →
        sigma e = some gamma ∨ sigma e = some choice.color) → choice.color ∈ MissingColors G sigma
        choice.vertex → (
    ∀ c ∈ TreeMissingColors choice.selected (ett.series.data.tree q.succ.castSucc) ∪ (insert
        choice.color (TashkinovStoredColors ett.series.data q.castSucc) : Finset (Fin k)), c ∈
        TreeMissingColors (ett.series.data.coloring q.succ) (ett.series.data.tree q.succ.castSucc)
        ∪ TashkinovStoredColors ett.series.data q.succ) → gamma ∈ TreeMissingColors
        choice.selected (ett.series.data.tree q.succ.castSucc) ∪ (insert choice.color
        (TashkinovStoredColors ett.series.data q.castSucc) : Finset (Fin k)) →
    ∀ (f : E), TreeIncidentEdge (ett.series.data.tree q.succ.castSucc) f → (
    ∃ c ∈ TreeMissingColors secondStable (ett.series.data.tree q.succ.castSucc) ∪ (insert
        choice.color (TashkinovStoredColors ett.series.data q.castSucc) : Finset (Fin k)), undone
        f = some c) → undone f = secondStable f

/-- Dependent contract shared by the terminal series reconstruction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperBranch6743Conditions.{u_1, u_2} : Prop :=
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
    ∀ (gamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (sigmaPrev : PartialEdgeColoring E k),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G sigmaPrev gamma choice.color;
    ∀ (u : V) (_ : H.Walk (Sum.inl choice.vertex) (Sum.inl u)), (1 : ℕ) < ett.rounds →
    ∀ (originalPrefix : ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last
        ett.rounds).castSucc) (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by
        have := GoldbergSeymour.TreeSequence.positive T
        omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ)), (
    ∀ (i : Fin (originalPrefix.rounds + (1 : ℕ))), originalPrefix.series.data.coloring i =
        ett.series.data.coloring (Fin.castLE (
    by
         have := GoldbergSeymour.TreeSequence.positive T
         omega
    ) i) ∧ originalPrefix.series.data.stored i = ett.series.data.stored (Fin.castLE (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ) i) ∧ originalPrefix.series.data.connectingEdges i = ett.series.data.connectingEdges
        (Fin.castLE (
    by
           have := GoldbergSeymour.TreeSequence.positive T
           omega
    ) i) ∧ originalPrefix.series.data.kind i = ett.series.data.kind (Fin.castLE (
    by
            have := GoldbergSeymour.TreeSequence.positive T
            omega
    ) i) ∧ TashkinovStoredColors originalPrefix.series.data i = TashkinovStoredColors
        ett.series.data (Fin.castLE (
    by
            have := GoldbergSeymour.TreeSequence.positive T
            omega
    ) i)) →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)), (0 : ℕ) < originalPrefix.rounds →
    let newStored : Finset (Fin k) := (insert choice.color ({ gamma } : Finset (Fin k)) : Finset
        (Fin k));
    let newEdges : Finset E := ({ choice.edge } : Finset E);
    let newKind : Option TashkinovExtensionKind := some TashkinovExtensionKind.PE;
    let newVertex : Option V := some choice.vertex;
    let newOutside : Option V := some choice.otherEndpoint;
    let newDelta : Option (Fin k) := some choice.color;
    let newGamma : Option (Fin k) := some gamma;
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
    ))) originalPrefix sigmaPrev (@TashkinovSeriesData.tree V E G k (@ExtendedTashkinovTree.rounds
        V E inst inst_1 inst_2 G k e0 input T generating ett) e0 (@TashkinovSeries.data V E inst
        inst_1 inst_2 G k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T
        generating ett) e0 input (@ExtendedTashkinovTree.series V E inst inst_1 inst_2 G k e0
        input T generating ett)) (@Fin.castSucc (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett)
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (Fin.last
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett))))
        corr)) S b h; (
    ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 corr.replacementInput) (i : Fin (b + (1
        : ℕ))), (castSeries h S).data.stored i = S.data.stored (Fin.cast (
    by omega
    ) i)) → (
    ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 corr.replacementInput) (i : Fin (b + (1
        : ℕ))), (castSeries h S).data.connectingEdges i = S.data.connectingEdges (Fin.cast (
    by omega
    ) i)) → (
    ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 corr.replacementInput) (i : Fin (b + (1
        : ℕ))), (castSeries h S).data.kind i = S.data.kind (Fin.cast (
    by omega
    ) i)) →
    let finalSeries : TashkinovSeries G k ett.rounds e0 corr.replacementInput := castSeries
        hroundsEq extendedSeries;
    let _ : Fin (ett.rounds + (1 : ℕ)) → Fin (originalPrefix.rounds + (2 : ℕ)) := fun (i : Fin
        (ett.rounds + (1 : ℕ))) ↦ Fin.cast (
    by
     have := GoldbergSeymour.TreeSequence.positive T
     omega
    ) i;
    ∀ (i : Fin (ett.rounds + (1 : ℕ))), (↑i : ℕ) < ett.rounds → finalSeries.data.stored i =
        ett.series.data.stored i ∧ finalSeries.data.connectingEdges i =
        ett.series.data.connectingEdges i ∧ finalSeries.data.kind i = ett.series.data.kind i

/-- Dependent contract shared by the terminal series reconstruction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperBranch6801Conditions.{u_1, u_2} : Prop :=
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
    ⟩ : Fin ett.rounds); q.succ = Fin.last ett.rounds →
    ∀ (gamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)),
        ett.series.data.stored q.succ = (insert choice.color ({ gamma } : Finset (Fin k)) : Finset
        (Fin k)) → ett.series.data.connectingEdges q.succ = ({ choice.edge } : Finset E) →
        ett.series.data.kind q.succ = some TashkinovExtensionKind.PE →
    ∀ (sigmaPrev : PartialEdgeColoring E k),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G sigmaPrev gamma choice.color;
    ∀ (u : V) (_ : H.Walk (Sum.inl choice.vertex) (Sum.inl u)), (1 : ℕ) < ett.rounds →
    ∀ (originalPrefix : ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last
        ett.rounds).castSucc) (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by
        have := GoldbergSeymour.TreeSequence.positive T
        omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))), originalPrefix.rounds = ett.rounds - (1 : ℕ) →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)), (0 : ℕ) < originalPrefix.rounds →
    let newStored : Finset (Fin k) := (insert choice.color ({ gamma } : Finset (Fin k)) : Finset
        (Fin k));
    let newEdges : Finset E := ({ choice.edge } : Finset E);
    let newKind : Option TashkinovExtensionKind := some TashkinovExtensionKind.PE;
    let newVertex : Option V := some choice.vertex;
    let newOutside : Option V := some choice.otherEndpoint;
    let newDelta : Option (Fin k) := some choice.color;
    let newGamma : Option (Fin k) := some gamma;
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
    ))) originalPrefix sigmaPrev (@TashkinovSeriesData.tree V E G k (@ExtendedTashkinovTree.rounds
        V E inst inst_1 inst_2 G k e0 input T generating ett) e0 (@TashkinovSeries.data V E inst
        inst_1 inst_2 G k (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T
        generating ett) e0 input (@ExtendedTashkinovTree.series V E inst inst_1 inst_2 G k e0
        input T generating ett)) (@Fin.castSucc (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett)
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (Fin.last
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_2 G k e0 input T generating ett))))
        corr)) S b h; (
    ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 corr.replacementInput) (i : Fin (b + (1
        : ℕ))), (castSeries h S).data.stored i = S.data.stored (Fin.cast (
    by omega
    ) i)) → (
    ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 corr.replacementInput) (i : Fin (b + (1
        : ℕ))), (castSeries h S).data.connectingEdges i = S.data.connectingEdges (Fin.cast (
    by omega
    ) i)) → (
    ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 corr.replacementInput) (i : Fin (b + (1
        : ℕ))), (castSeries h S).data.kind i = S.data.kind (Fin.cast (
    by omega
    ) i)) →
    let finalSeries : TashkinovSeries G k ett.rounds e0 corr.replacementInput := castSeries
        hroundsEq extendedSeries;
    let _ : Fin (ett.rounds + (1 : ℕ)) → Fin (originalPrefix.rounds + (2 : ℕ)) := fun (i : Fin
        (ett.rounds + (1 : ℕ))) ↦ Fin.cast (
    by
     have := GoldbergSeymour.TreeSequence.positive T
     omega
    ) i;
    ∀ (i : Fin (ett.rounds + (1 : ℕ))), ¬(↑i : ℕ) < ett.rounds → finalSeries.data.stored i =
        ett.series.data.stored i ∧ finalSeries.data.connectingEdges i =
        ett.series.data.connectingEdges i ∧ finalSeries.data.kind i = ett.series.data.kind i

/-- Dependent contract shared by the terminal series reconstruction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperHseriesStable6952Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [inst_2 : DecidableEq
        E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k), StableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) (ett.series.data.coloring
        (Fin.last ett.rounds)) sigma →
    ∀ (_ closureTree : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
     have := GoldbergSeymour.TreeSequence.positive T
     omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (sigmaPrev : PartialEdgeColoring E k),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G sigmaPrev gamma choice.color;
    ∀ (u : V) (_ : H.Walk (Sum.inl choice.vertex) (Sum.inl u)), (1 : ℕ) < ett.rounds →
    ∀ (originalPrefix : ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last
        ett.rounds).castSucc) (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by
        have := GoldbergSeymour.TreeSequence.positive T
        omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ)), (
    ∀ (i : Fin (originalPrefix.rounds + (2 : ℕ))), originalPrefix.series.data.tree i =
        ett.series.data.tree (Fin.castLE (
    by
        have := GoldbergSeymour.TreeSequence.positive T
        omega
    ) i)) → (
    ∀ (i : Fin (originalPrefix.rounds + (1 : ℕ))), originalPrefix.series.data.coloring i =
        ett.series.data.coloring (Fin.castLE (
    by
         have := GoldbergSeymour.TreeSequence.positive T
         omega
    ) i) ∧ originalPrefix.series.data.stored i = ett.series.data.stored (Fin.castLE (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ) i) ∧ originalPrefix.series.data.connectingEdges i = ett.series.data.connectingEdges
        (Fin.castLE (
    by
           have := GoldbergSeymour.TreeSequence.positive T
           omega
    ) i) ∧ originalPrefix.series.data.kind i = ett.series.data.kind (Fin.castLE (
    by
            have := GoldbergSeymour.TreeSequence.positive T
            omega
    ) i) ∧ TashkinovStoredColors originalPrefix.series.data i = TashkinovStoredColors
        ett.series.data (Fin.castLE (
    by
            have := GoldbergSeymour.TreeSequence.positive T
            omega
    ) i)) →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)), (0 : ℕ) < originalPrefix.rounds →
    let newStored : Finset (Fin k) := (insert choice.color ({ gamma } : Finset (Fin k)) : Finset
        (Fin k));
    let newEdges : Finset E := ({ choice.edge } : Finset E);
    let newKind : Option TashkinovExtensionKind := some TashkinovExtensionKind.PE;
    let newVertex : Option V := some choice.vertex;
    let newOutside : Option V := some choice.otherEndpoint;
    let newDelta : Option (Fin k) := some choice.color;
    let newGamma : Option (Fin k) := some gamma;
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
    ))) originalPrefix sigmaPrev (@TashkinovSeriesData.tree V E G k (@ExtendedTashkinovTree.rounds
        V E inst inst_1 inst_2 G k e0 input T generating ett) e0 (@TashkinovSeries.data V E inst
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
        hroundsEq extendedSeries; finalSeries.data.coloring (Fin.last ett.rounds) = sigma →
    let _ : Fin (ett.rounds + (1 : ℕ)) → Fin (originalPrefix.rounds + (2 : ℕ)) := fun (i : Fin
        (ett.rounds + (1 : ℕ))) ↦ Fin.cast (
    by
     have := GoldbergSeymour.TreeSequence.positive T
     omega
    ) i;
    ∀ (i : Fin ett.rounds), StableColoring (ett.series.data.tree i.succ.castSucc)
        (TashkinovStoredColors ett.series.data i.succ) (ett.series.data.coloring i.succ)
        (finalSeries.data.coloring i.succ)

theorem helper_hTnClosure_112.{u_1, u_2} :
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
      closureTree.vertex
            (Fin.castLE (Nat.succ_le_succ (Nat.le_trans hlenAB hlenBC)) j) =
          closureTree.vertex
            (Fin.castLE (Nat.succ_le_succ hlenBC)
              (Fin.castLE (Nat.succ_le_succ hlenAB) j)) := by congr 1
      _ = Tstar.vertex (Fin.castLE (Nat.succ_le_succ hlenAB) j) :=
        hvertexBC _
      _ = (ett.series.data.tree (Fin.last ett.rounds).castSucc).vertex j :=
        hvertexAB j
  · intro j
    calc
      closureTree.edge (Fin.castLE (Nat.le_trans hlenAB hlenBC) j) =
          closureTree.edge (Fin.castLE hlenBC (Fin.castLE hlenAB j)) := by
        congr 1
      _ = Tstar.edge (Fin.castLE hlenAB j) := hedgeBC _
      _ = (ett.series.data.tree (Fin.last ett.rounds).castSucc).edge j :=
        hedgeAB j

theorem helper_hdeltaBoundary_254.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (sigmaPrev : PartialEdgeColoring E k), IsProperEdgeColoring G sigmaPrev →
        IsOneEdgeUncolored sigmaPrev e0 → StableColoring (ett.series.data.tree q.succ.castSucc)
        (insert choice.color (TashkinovStoredColors ett.series.data q.castSucc) : Finset (Fin k))
        choice.selected sigmaPrev → BoundaryColorEdges G choice.selected (TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc)) choice.color = BoundaryColorEdges G sigmaPrev
        (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) choice.color := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ q choice sigmaPrev hsigmaPrevProper
      hsigmaPrevOne hsigmaPrevEnlarged
  ext f
  simp only [BoundaryColorEdges, Finset.mem_filter]
  constructor
  · rintro ⟨hf, hfc⟩
    refine ⟨hf, ?_⟩
    obtain ⟨x, hx, y, hy, hends⟩ := by
      simpa [BoundaryEdges] using hf
    have hinc : TreeIncidentEdge
        (ett.series.data.tree q.succ.castSucc) f := by
      refine ⟨x, hx, ?_⟩
      unfold Incident
      rw [hends]
      exact Sym2.mem_mk_left _ _
    exact (hsigmaPrevEnlarged.1 f hinc
      ⟨choice.color, Finset.mem_union_right _
        (Finset.mem_insert_self _ _), hfc⟩).trans hfc
  · rintro ⟨hf, hfc⟩
    refine ⟨hf, ?_⟩
    obtain ⟨x, hx, y, hy, hends⟩ := by
      simpa [BoundaryEdges] using hf
    have hinc : TreeIncidentEdge
        (ett.series.data.tree q.succ.castSucc) f := by
      refine ⟨x, hx, ?_⟩
      unfold Incident
      rw [hends]
      exact Sym2.mem_mk_left _ _
    have hcriterion := (sc1 G e0
      (ett.series.data.tree q.succ.castSucc)
      (insert choice.color
        (TashkinovStoredColors ett.series.data q.castSucc))
      choice.selected sigmaPrev choice.selectedProper
      choice.selectedOneUncolored hsigmaPrevProper hsigmaPrevOne).mp
        hsigmaPrevEnlarged
    exact (hcriterion f hinc (Or.inr
      ⟨choice.color, Finset.mem_union_right _
        (Finset.mem_insert_self _ _), hfc⟩)).symm.trans hfc

theorem helper_hclosedPrev_356.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds); IsProperEdgeColoring G (ett.series.data.coloring q.castSucc) →
        IsOneEdgeUncolored (ett.series.data.coloring q.castSucc) e0 → ColoredVertexSetClosed G
        (ett.series.data.coloring q.castSucc) (TreeSequenceVertexSet (ett.series.data.tree
        q.succ.castSucc)) →
    ∀ (sigmaPrev : PartialEdgeColoring E k), IsProperEdgeColoring G sigmaPrev → IsOneEdgeUncolored
        sigmaPrev e0 → StableColoring (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)
        sigmaPrev → ColoredVertexSetClosed G sigmaPrev (TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc)) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ q previousProper
      previousOneUncolored previousClosed sigmaPrev hsigmaPrevProper hsigmaPrevOne hsigmaPrevStableQ
      f c v hf hv hsf hcm
  obtain ⟨x, hx, y, hy, hends⟩ := by
    simpa [BoundaryEdges] using hf
  have hinc : TreeIncidentEdge
      (ett.series.data.tree q.succ.castSucc) f := by
    refine ⟨x, hx, ?_⟩
    unfold Incident
    rw [hends]
    exact Sym2.mem_mk_left _ _
  have hmissingEq := hsigmaPrevStableQ.2 v hv
  have hcTree : c ∈ TreeMissingColors
      (ett.series.data.coloring q.castSucc)
      (ett.series.data.tree q.succ.castSucc) := by
    simp only [TreeMissingColors, Finset.mem_biUnion]
    exact ⟨v, hv, hmissingEq ▸ hcm⟩
  have hcriterion := (sc1 G e0
    (ett.series.data.tree q.succ.castSucc)
    (TashkinovStoredColors ett.series.data q.castSucc)
    (ett.series.data.coloring q.castSucc) sigmaPrev previousProper
    previousOneUncolored hsigmaPrevProper hsigmaPrevOne).mp
      hsigmaPrevStableQ
  have hcopy := hcriterion f hinc
    (Or.inr ⟨c, Finset.mem_union_left _ hcTree, hsf⟩)
  have holdf : ett.series.data.coloring q.castSucc f = some c :=
    hcopy.symm.trans hsf
  exact previousClosed hf hv holdf (hmissingEq ▸ hcm)

theorem helper_hpenultimateTree_713.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [inst_2 : DecidableEq
        E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ closureTree : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds); q.succ = Fin.last ett.rounds →
    ∀ (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (prefixInput : PartialEdgeColoring E k) (zeroPrefix : TashkinovSeries G k (0 : ℕ) e0
        prefixInput),
    let zeroLast : Fin ((0 : ℕ) + (1 : ℕ)) := Fin.last (0 : ℕ);
    let newStored : Finset (Fin k) := ({ choice.color } : Finset (Fin k));
    let newEdges : Finset E := ({ choice.edge } : Finset E);
    let newKind : Option TashkinovExtensionKind := some TashkinovExtensionKind.SE;
    let newVertex : Option V := some choice.vertex;
    let newOutside : Option V := some choice.otherEndpoint;
    let newDelta : Option (Fin k) := some choice.color;
    let newGamma : Option (Fin k) := none;
    let appendedData : TashkinovSeriesData G k ((0 : ℕ) + (1 : ℕ)) e0 := TashkinovSeriesDataAppend
        zeroPrefix.data closureTree sigma newStored newEdges newKind newVertex newOutside newDelta
        newGamma; appendedData.tree zeroLast.succ.castSucc = ett.series.data.tree q.succ.castSucc
        →
    ∀ (extendedSeries : TashkinovSeries G k ((0 : ℕ) + (1 : ℕ)) e0 prefixInput),
        extendedSeries.data = TashkinovSeriesDataAppend zeroPrefix.data closureTree sigma
        newStored newEdges newKind newVertex newOutside newDelta newGamma →
    ∀ (hroundsEq : (0 : ℕ) + (1 : ℕ) = ett.rounds),
    let castSeries : {a b : ℕ} → a = b → TashkinovSeries G k a e0 prefixInput → TashkinovSeries G
        k b e0 prefixInput := fun {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 prefixInput)
        ↦ @Eq.ndrec Nat a (fun {b : Nat} ↦ @TashkinovSeries V E inst inst_1 inst_2 G k b e0
        prefixInput) S b h; (
    ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 prefixInput) (i : Fin (b + (2 : ℕ))),
        (castSeries h S).data.tree i = S.data.tree (Fin.cast (
    by omega
    ) i)) →
    let finalSeries : TashkinovSeries G k ett.rounds e0 prefixInput := castSeries hroundsEq
        extendedSeries;
    let rawTreeIndex : Fin (ett.rounds + (2 : ℕ)) → Fin (3 : ℕ) := fun (i : Fin (ett.rounds + (2 :
        ℕ))) ↦ Fin.cast (
    by omega
    ) i; rawTreeIndex (⟨ett.rounds,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))) = zeroLast.succ.castSucc → finalSeries.data.tree (⟨ett.rounds,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))) = ett.series.data.tree (Fin.last ett.rounds).castSucc := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma _ closureTree q hqSucc choice
      prefixInput zeroPrefix zeroLast newStored newEdges newKind newVertex newOutside newDelta
      newGamma appendedData happendTree extendedSeries hextendedData hroundsEq castSeries
      castSeriesTree finalSeries rawTreeIndex hrawPenultimate
  calc
    finalSeries.data.tree
          (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2)) =
        extendedSeries.data.tree
          (rawTreeIndex
            (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2))) := by
          exact castSeriesTree hroundsEq extendedSeries _
    _ = appendedData.tree
          (rawTreeIndex
            (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2))) := by
          rw [hextendedData]
    _ = appendedData.tree zeroLast.succ.castSucc := by
          rw [hrawPenultimate]
    _ = ett.series.data.tree q.succ.castSucc := happendTree
    _ = ett.series.data.tree (Fin.last ett.rounds).castSucc := by
          rw [hqSucc]

theorem helper_hprefixFields_744.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating), (0 : ℕ) < ett.rounds →
    ∀ (_ _ : TreeSequence G e0), ett.rounds = (1 : ℕ) →
    ∀ (prefixInput : PartialEdgeColoring E k) (zeroPrefix : TashkinovSeries G k (0 : ℕ) e0
        prefixInput),
    let zeroLast : Fin ((0 : ℕ) + (1 : ℕ)) := Fin.last (0 : ℕ); (0 : ℕ) + (1 : ℕ) = ett.rounds →
    ∀ (i : Fin (ett.rounds + (1 : ℕ))), (↑i : ℕ) < ett.rounds → zeroPrefix.data.stored zeroLast =
        ett.series.data.stored i ∧ zeroPrefix.data.connectingEdges zeroLast =
        ett.series.data.connectingEdges i ∧ zeroPrefix.data.kind zeroLast = ett.series.data.kind i
  := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ closureTree hroundOne prefixInput
      zeroPrefix zeroLast hroundsEq i hi
  have hiZero : i.val = 0 := by
    have hr := hroundOne
    omega
  have hiEq : i = 0 := Fin.ext hiZero
  subst i
  have hold := zeroPrefix.certified 0
  have hnew := ett.series.certified 0
  cases hold with
  | initial triple0 seedLength0 initialColoring0 initialStored0
      initialEdges0 initialKind0 initialVertex0 initialOutside0
      initialDelta0 initialGamma0 initialClosure0 =>
    cases hnew with
    | initial triple1 seedLength1 initialColoring1 initialStored1
        initialEdges1 initialKind1 initialVertex1 initialOutside1
        initialDelta1 initialGamma1 initialClosure1 =>
      exact ⟨by simpa [zeroLast] using
          initialStored0.trans initialStored1.symm,
        by simpa [zeroLast] using
          initialEdges0.trans initialEdges1.symm,
        by simpa [zeroLast] using
          initialKind0.trans initialKind1.symm⟩

theorem helper_hseriesDataAgree_772.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [inst_2 : DecidableEq
        E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ closureTree : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds); q.succ = Fin.last ett.rounds →
    ∀ (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)),
        ett.series.data.stored q.succ = ({ choice.color } : Finset (Fin k)) →
        ett.series.data.connectingEdges q.succ = ({ choice.edge } : Finset E) →
        ett.series.data.kind q.succ = some TashkinovExtensionKind.SE → ett.rounds = (1 : ℕ) →
    ∀ (prefixInput : PartialEdgeColoring E k) (zeroPrefix : TashkinovSeries G k (0 : ℕ) e0
        prefixInput),
    let zeroLast : Fin ((0 : ℕ) + (1 : ℕ)) := Fin.last (0 : ℕ);
    let newStored : Finset (Fin k) := ({ choice.color } : Finset (Fin k));
    let newEdges : Finset E := ({ choice.edge } : Finset E);
    let newKind : Option TashkinovExtensionKind := some TashkinovExtensionKind.SE;
    let newVertex : Option V := some choice.vertex;
    let newOutside : Option V := some choice.otherEndpoint;
    let newDelta : Option (Fin k) := some choice.color;
    let newGamma : Option (Fin k) := none;
    let appendedData : TashkinovSeriesData G k ((0 : ℕ) + (1 : ℕ)) e0 := TashkinovSeriesDataAppend
        zeroPrefix.data closureTree sigma newStored newEdges newKind newVertex newOutside newDelta
        newGamma; appendedData.stored (Fin.last (1 : ℕ)) = newStored →
        appendedData.connectingEdges (Fin.last (1 : ℕ)) = newEdges → appendedData.kind (Fin.last
        (1 : ℕ)) = newKind →
    ∀ (extendedSeries : TashkinovSeries G k ((0 : ℕ) + (1 : ℕ)) e0 prefixInput),
        extendedSeries.data = TashkinovSeriesDataAppend zeroPrefix.data closureTree sigma
        newStored newEdges newKind newVertex newOutside newDelta newGamma →
    ∀ (hroundsEq : (0 : ℕ) + (1 : ℕ) = ett.rounds),
    let castSeries : {a b : ℕ} → a = b → TashkinovSeries G k a e0 prefixInput → TashkinovSeries G
        k b e0 prefixInput := fun {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 prefixInput)
        ↦ @Eq.ndrec Nat a (fun {b : Nat} ↦ @TashkinovSeries V E inst inst_1 inst_2 G k b e0
        prefixInput) S b h; (
    ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 prefixInput) (i : Fin (b + (1 : ℕ))),
        (castSeries h S).data.stored i = S.data.stored (Fin.cast (
    by omega
    ) i)) → (
    ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 prefixInput) (i : Fin (b + (1 : ℕ))),
        (castSeries h S).data.connectingEdges i = S.data.connectingEdges (Fin.cast (
    by omega
    ) i)) → (
    ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 prefixInput) (i : Fin (b + (1 : ℕ))),
        (castSeries h S).data.kind i = S.data.kind (Fin.cast (
    by omega
    ) i)) →
    let finalSeries : TashkinovSeries G k ett.rounds e0 prefixInput := castSeries hroundsEq
        extendedSeries;
    let rawDataIndex : Fin (ett.rounds + (1 : ℕ)) → Fin (2 : ℕ) := fun (i : Fin (ett.rounds + (1 :
        ℕ))) ↦ Fin.cast (
    by omega
    ) i; rawDataIndex (Fin.last ett.rounds) = Fin.last (1 : ℕ) → (
    ∀ (i : Fin (ett.rounds + (1 : ℕ))), (↑i : ℕ) < ett.rounds → zeroPrefix.data.stored zeroLast =
        ett.series.data.stored i ∧ zeroPrefix.data.connectingEdges zeroLast =
        ett.series.data.connectingEdges i ∧ zeroPrefix.data.kind zeroLast = ett.series.data.kind
        i) →
    ∀ (i : Fin (ett.rounds + (1 : ℕ))), finalSeries.data.stored i = ett.series.data.stored i ∧
        finalSeries.data.connectingEdges i = ett.series.data.connectingEdges i ∧
        finalSeries.data.kind i = ett.series.data.kind i := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma _ closureTree q hqSucc choice
      currentStored currentEdges currentKind hroundOne prefixInput zeroPrefix zeroLast newStored
      newEdges newKind newVertex newOutside newDelta newGamma appendedData happendLastStored
      happendLastEdges happendLastKind extendedSeries hextendedData hroundsEq castSeries
      castSeriesStored castSeriesEdges castSeriesKind finalSeries rawDataIndex hrawFinalData
      hprefixFields i
  by_cases hi : i.val < ett.rounds
  · have hraw : rawDataIndex i = zeroLast.castSucc := by
      apply Fin.ext
      have hiZero : i.val = 0 := by
        have hr := hroundOne
        omega
      exact hiZero
    have hp := hprefixFields i hi
    constructor
    · calc
        finalSeries.data.stored i =
            extendedSeries.data.stored (rawDataIndex i) := by
              exact castSeriesStored hroundsEq extendedSeries i
        _ = appendedData.stored (rawDataIndex i) := by
              rw [hextendedData]
        _ = zeroPrefix.data.stored zeroLast := by
              rw [hraw]
              simp only [appendedData, TashkinovSeriesDataAppend,
                Fin.lastCases_castSucc]
        _ = ett.series.data.stored i := hp.1
    · constructor
      · calc
          finalSeries.data.connectingEdges i =
              extendedSeries.data.connectingEdges
                (rawDataIndex i) := by
                exact castSeriesEdges hroundsEq extendedSeries i
          _ = appendedData.connectingEdges (rawDataIndex i) := by
                rw [hextendedData]
          _ = zeroPrefix.data.connectingEdges zeroLast := by
                rw [hraw]
                simp only [appendedData, TashkinovSeriesDataAppend,
                  Fin.lastCases_castSucc]
          _ = ett.series.data.connectingEdges i := hp.2.1
      · calc
          finalSeries.data.kind i =
              extendedSeries.data.kind (rawDataIndex i) := by
                exact castSeriesKind hroundsEq extendedSeries i
          _ = appendedData.kind (rawDataIndex i) := by
                rw [hextendedData]
          _ = zeroPrefix.data.kind zeroLast := by
                rw [hraw]
                simp only [appendedData, TashkinovSeriesDataAppend,
                  Fin.lastCases_castSucc]
          _ = ett.series.data.kind i := hp.2.2
  · have hilast : i = Fin.last ett.rounds := by
      apply Fin.ext
      have hibound := i.isLt
      simp
      omega
    subst i
    constructor
    · calc
        finalSeries.data.stored (Fin.last ett.rounds) =
            extendedSeries.data.stored
              (rawDataIndex (Fin.last ett.rounds)) := by
              exact castSeriesStored hroundsEq extendedSeries _
        _ = appendedData.stored
              (rawDataIndex (Fin.last ett.rounds)) := by
              rw [hextendedData]
        _ = appendedData.stored (Fin.last 1) := by rw [hrawFinalData]
        _ = newStored := happendLastStored
        _ = {choice.color} := rfl
        _ = ett.series.data.stored (Fin.last ett.rounds) := by
              rw [← hqSucc]
              exact currentStored.symm
    · constructor
      · calc
          finalSeries.data.connectingEdges (Fin.last ett.rounds) =
              extendedSeries.data.connectingEdges
                (rawDataIndex (Fin.last ett.rounds)) := by
                exact castSeriesEdges hroundsEq extendedSeries _
          _ = appendedData.connectingEdges
                (rawDataIndex (Fin.last ett.rounds)) := by
                rw [hextendedData]
          _ = appendedData.connectingEdges (Fin.last 1) := by
                rw [hrawFinalData]
          _ = newEdges := happendLastEdges
          _ = {choice.edge} := rfl
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
          _ = appendedData.kind (Fin.last 1) := by rw [hrawFinalData]
          _ = newKind := happendLastKind
          _ = some TashkinovExtensionKind.SE := rfl
          _ = ett.series.data.kind (Fin.last ett.rounds) := by
                rw [← hqSucc]
                exact currentKind.symm

theorem helper_hseriesTreeAgree_874.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [inst_2 : DecidableEq
        E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ closureTree : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds); q.succ = Fin.last ett.rounds →
    ∀ (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)),
        ett.rounds = (1 : ℕ) →
    ∀ (prefixInput : PartialEdgeColoring E k) (zeroPrefix : TashkinovSeries G k (0 : ℕ) e0
        prefixInput),
    let zeroLast : Fin ((0 : ℕ) + (1 : ℕ)) := Fin.last (0 : ℕ);
    let newStored : Finset (Fin k) := ({ choice.color } : Finset (Fin k));
    let newEdges : Finset E := ({ choice.edge } : Finset E);
    let newKind : Option TashkinovExtensionKind := some TashkinovExtensionKind.SE;
    let newVertex : Option V := some choice.vertex;
    let newOutside : Option V := some choice.otherEndpoint;
    let newDelta : Option (Fin k) := some choice.color;
    let newGamma : Option (Fin k) := none;
    let appendedData : TashkinovSeriesData G k ((0 : ℕ) + (1 : ℕ)) e0 := TashkinovSeriesDataAppend
        zeroPrefix.data closureTree sigma newStored newEdges newKind newVertex newOutside newDelta
        newGamma; appendedData.tree zeroLast.succ.castSucc = ett.series.data.tree q.succ.castSucc
        →
    ∀ (extendedSeries : TashkinovSeries G k ((0 : ℕ) + (1 : ℕ)) e0 prefixInput),
        extendedSeries.data = TashkinovSeriesDataAppend zeroPrefix.data closureTree sigma
        newStored newEdges newKind newVertex newOutside newDelta newGamma →
    ∀ (hroundsEq : (0 : ℕ) + (1 : ℕ) = ett.rounds),
    let castSeries : {a b : ℕ} → a = b → TashkinovSeries G k a e0 prefixInput → TashkinovSeries G
        k b e0 prefixInput := fun {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 prefixInput)
        ↦ @Eq.ndrec Nat a (fun {b : Nat} ↦ @TashkinovSeries V E inst inst_1 inst_2 G k b e0
        prefixInput) S b h; (
    ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 prefixInput) (i : Fin (b + (2 : ℕ))),
        (castSeries h S).data.tree i = S.data.tree (Fin.cast (
    by omega
    ) i)) →
    let finalSeries : TashkinovSeries G k ett.rounds e0 prefixInput := castSeries hroundsEq
        extendedSeries;
    let _ : Fin (ett.rounds + (2 : ℕ)) → Fin (3 : ℕ) := fun (i : Fin (ett.rounds + (2 : ℕ))) ↦
        Fin.cast (
    by omega
    ) i;
    ∀ (j : Fin ett.rounds), finalSeries.data.tree j.succ.castSucc = ett.series.data.tree
        j.succ.castSucc := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma _ closureTree q hqSucc choice
      hroundOne prefixInput zeroPrefix zeroLast newStored newEdges newKind newVertex newOutside
      newDelta newGamma appendedData happendTree extendedSeries hextendedData hroundsEq
      castSeries castSeriesTree finalSeries rawTreeIndex j
  have hj : j.succ = Fin.last ett.rounds := by
    apply Fin.ext
    have hjbound := j.isLt
    simp
    have hr := hroundOne
    omega
  have htreeIndex : rawTreeIndex j.succ.castSucc =
      zeroLast.succ.castSucc := by
    apply Fin.ext
    simp [rawTreeIndex, zeroLast]
  calc
    finalSeries.data.tree j.succ.castSucc =
        extendedSeries.data.tree (rawTreeIndex j.succ.castSucc) := by
          exact castSeriesTree hroundsEq extendedSeries _
    _ = appendedData.tree (rawTreeIndex j.succ.castSucc) := by
          rw [hextendedData]
    _ = appendedData.tree zeroLast.succ.castSucc := by rw [htreeIndex]
    _ = ett.series.data.tree q.succ.castSucc := happendTree
    _ = ett.series.data.tree j.succ.castSucc := by
          rw [hj, hqSucc]

theorem helper_hseriesColorProperties_898.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [inst_2 : DecidableEq
        E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
    ∀ (_ closureTree : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (sigmaPrev : PartialEdgeColoring E k), IsProperEdgeColoring G sigmaPrev →
        IsOneEdgeUncolored sigmaPrev e0 → ett.rounds = (1 : ℕ) →
    ∀ (prefixInput : PartialEdgeColoring E k) (zeroPrefix : TashkinovSeries G k (0 : ℕ) e0
        prefixInput),
    let zeroLast : Fin ((0 : ℕ) + (1 : ℕ)) := Fin.last (0 : ℕ);
    let newStored : Finset (Fin k) := ({ choice.color } : Finset (Fin k));
    let newEdges : Finset E := ({ choice.edge } : Finset E);
    let newKind : Option TashkinovExtensionKind := some TashkinovExtensionKind.SE;
    let newVertex : Option V := some choice.vertex;
    let newOutside : Option V := some choice.otherEndpoint;
    let newDelta : Option (Fin k) := some choice.color;
    let newGamma : Option (Fin k) := none;
    let appendedData : TashkinovSeriesData G k ((0 : ℕ) + (1 : ℕ)) e0 := TashkinovSeriesDataAppend
        zeroPrefix.data closureTree sigma newStored newEdges newKind newVertex newOutside newDelta
        newGamma; appendedData.coloring zeroLast.castSucc = sigmaPrev →
    ∀ (extendedSeries : TashkinovSeries G k ((0 : ℕ) + (1 : ℕ)) e0 prefixInput),
        extendedSeries.data = TashkinovSeriesDataAppend zeroPrefix.data closureTree sigma
        newStored newEdges newKind newVertex newOutside newDelta newGamma →
    ∀ (hroundsEq : (0 : ℕ) + (1 : ℕ) = ett.rounds),
    let castSeries : {a b : ℕ} → a = b → TashkinovSeries G k a e0 prefixInput → TashkinovSeries G
        k b e0 prefixInput := fun {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 prefixInput)
        ↦ @Eq.ndrec Nat a (fun {b : Nat} ↦ @TashkinovSeries V E inst inst_1 inst_2 G k b e0
        prefixInput) S b h; (
    ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 prefixInput) (i : Fin (b + (1 : ℕ))),
        (castSeries h S).data.coloring i = S.data.coloring (Fin.cast (
    by omega
    ) i)) →
    let finalSeries : TashkinovSeries G k ett.rounds e0 prefixInput := castSeries hroundsEq
        extendedSeries;
    let _ : Fin (ett.rounds + (1 : ℕ)) → Fin (2 : ℕ) := fun (i : Fin (ett.rounds + (1 : ℕ))) ↦
        Fin.cast (
    by omega
    ) i; finalSeries.data.coloring (Fin.last ett.rounds) = sigma →
    ∀ (i : Fin (ett.rounds + (1 : ℕ))), IsProperEdgeColoring G (finalSeries.data.coloring i) ∧
        IsOneEdgeUncolored (finalSeries.data.coloring i) e0 := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma hsigmaProper hsigmaOne _
      closureTree q choice sigmaPrev hsigmaPrevProper hsigmaPrevOne hroundOne prefixInput
      zeroPrefix zeroLast newStored newEdges newKind newVertex newOutside newDelta newGamma
      appendedData happendColor extendedSeries hextendedData hroundsEq castSeries
      castSeriesColoring finalSeries rawDataIndex hfinalColor i
  by_cases hi : i.val < ett.rounds
  · have hraw : rawDataIndex i = zeroLast.castSucc := by
      apply Fin.ext
      have hiZero : i.val = 0 := by
        have hr := hroundOne
        omega
      exact hiZero
    have hcolor : finalSeries.data.coloring i = sigmaPrev := by
      calc
        finalSeries.data.coloring i =
            extendedSeries.data.coloring (rawDataIndex i) := by
              exact castSeriesColoring hroundsEq extendedSeries i
        _ = appendedData.coloring (rawDataIndex i) := by
              rw [hextendedData]
        _ = appendedData.coloring zeroLast.castSucc := by rw [hraw]
        _ = sigmaPrev := happendColor
    rw [hcolor]
    exact ⟨hsigmaPrevProper, hsigmaPrevOne⟩
  · have hilast : i = Fin.last ett.rounds := by
      apply Fin.ext
      have hibound := i.isLt
      simp
      omega
    subst i
    rw [hfinalColor]
    exact ⟨hsigmaProper, hsigmaOne⟩

theorem helper_hdegree_1837.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (secondStable : PartialEdgeColoring E k), IsProperEdgeColoring G
        secondStable →
    ∀ (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (w : V), gamma ∈ MissingColors G secondStable w ∨ choice.color ∈ MissingColors G
        secondStable w → (TwoColorIncidenceGraph G secondStable gamma choice.color).degree
        (Sum.inl w) ≤ (1 : ℕ) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ q gamma secondStable
      secondStableProper choice w hw
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_le_one.mpr
  intro y hy z hz
  simp only [SimpleGraph.mem_neighborFinset] at hy hz
  cases y with
  | inl y => simp [TwoColorIncidenceGraph] at hy
  | inr e =>
    cases z with
    | inl z => simp [TwoColorIncidenceGraph] at hz
    | inr f =>
      simp only [TwoColorIncidenceGraph] at hy hz
      rcases hw with hw | hw
      · have he : secondStable e = some choice.color :=
          hy.2.resolve_left (by
            intro he
            apply (by simpa [MissingColors] using hw)
            simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨e, hy.1, he⟩)
        have hf : secondStable f = some choice.color :=
          hz.2.resolve_left (by
            intro hf
            apply (by simpa [MissingColors] using hw)
            simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨f, hz.1, hf⟩)
        by_cases h : e = f
        · exact congrArg Sum.inr h
        · exact (secondStableProper h ⟨w, hy.1, hz.1⟩ he hf).elim
      · have he : secondStable e = some gamma :=
          hy.2.resolve_right (by
            intro he
            apply (by simpa [MissingColors] using hw)
            simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨e, hy.1, he⟩)
        have hf : secondStable f = some gamma :=
          hz.2.resolve_right (by
            intro hf
            apply (by simpa [MissingColors] using hw)
            simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨f, hz.1, hf⟩)
        by_cases h : e = f
        · exact congrArg Sum.inr h
        · exact (secondStableProper h ⟨w, hy.1, hz.1⟩ he hf).elim

theorem helper_hclosed_1893.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (secondStable : PartialEdgeColoring E k) (choice : MaximumDefectiveChoice G
        e0 (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors ett.series.data
        q.castSucc) (ett.series.data.coloring q.castSucc)), gamma ∈ MissingColors G secondStable
        choice.vertex → (
    ∀ (w : V), gamma ∈ MissingColors G secondStable w ∨ choice.color ∈ MissingColors G
        secondStable w → (TwoColorIncidenceGraph G secondStable gamma choice.color).degree
        (Sum.inl w) ≤ (1 : ℕ)) →
    ∀ (u : V) (path : (TwoColorIncidenceGraph G secondStable gamma choice.color).Walk (Sum.inl u)
        (Sum.inl choice.vertex)), path.IsPath → (2 : ℕ) ≤ path.length → (
    ∀ (x : V ⊕ E), (TwoColorIncidenceGraph G secondStable gamma choice.color).degree x ≤ (2 : ℕ))
        → (TwoColorIncidenceGraph G secondStable gamma choice.color).degree (Sum.inl u) ≤ (1 : ℕ)
        →
    ∀ x ∈ path.support,
    ∀ (y : V ⊕ E), (TwoColorIncidenceGraph G secondStable gamma choice.color).Adj x y → y ∈
        path.support := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ q gamma secondStable choice hmissing
      hdegree u path pathIs pathLen hdegreeBound huDegree x hx y hxy
  obtain ⟨n, hn, hnle⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx
  by_cases hn0 : n = 0
  · subst n
    have hx0 : x = Sum.inl u := by simpa using hn.symm
    let graph := TwoColorIncidenceGraph G secondStable gamma choice.color
    let : Fintype (graph.neighborSet x) := Fintype.ofFinite _
    have card : Fintype.card (graph.neighborSet x) ≤ 1 := by
      rw [SimpleGraph.card_neighborSet_eq_degree]
      convert huDegree using 1
      cases hx0
      exact congrArg (fun z => @SimpleGraph.degree _ graph (Sum.inl u) z)
        (Subsingleton.elim _ _)
    have hy' : y ∈ graph.neighborSet x := by simpa [graph, SimpleGraph.mem_neighborSet] using hxy
    have hn' : path.getVert 1 ∈ graph.neighborSet x := by
      simpa [graph, hx0, SimpleGraph.mem_neighborSet] using
        path.adj_getVert_succ (show 0 < path.length by omega)
    have heq := Fintype.card_le_one_iff.mp card ⟨y, hy'⟩ ⟨path.getVert 1, hn'⟩
    have hey : y = path.getVert 1 := congrArg Subtype.val heq
    rw [hey]
    exact path.getVert_mem_support 1
  by_cases hlast : n = path.length
  · have hx1 : x = Sum.inl choice.vertex := by
      rw [← hn, pathIs.getVert_eq_end_iff hnle]
      exact hlast
    let graph := TwoColorIncidenceGraph G secondStable gamma choice.color
    let : Fintype (graph.neighborSet x) := Fintype.ofFinite _
    have card : Fintype.card (graph.neighborSet x) ≤ 1 := by
      rw [SimpleGraph.card_neighborSet_eq_degree]
      convert hdegree choice.vertex (Or.inl hmissing) using 1
      cases hx1
      exact congrArg (fun z => @SimpleGraph.degree _ graph (Sum.inl choice.vertex) z)
        (Subsingleton.elim _ _)
    have hy' : y ∈ graph.neighborSet x := by simpa [graph, SimpleGraph.mem_neighborSet] using hxy
    have hp : path.getVert (path.length - 1) ∈ graph.neighborSet x := by
      have ha : graph.Adj (Sum.inl choice.vertex) (path.getVert (path.length - 1)) := by
        simpa [graph, show path.length - 1 + 1 = path.length by omega] using
          (path.adj_getVert_succ (show path.length - 1 < path.length by omega)).symm
      simpa [hx1, SimpleGraph.mem_neighborSet] using ha
    have heq := Fintype.card_le_one_iff.mp card ⟨y, hy'⟩ ⟨path.getVert (path.length - 1), hp⟩
    have hey : y = path.getVert (path.length - 1) := congrArg Subtype.val heq
    rw [hey]
    exact path.getVert_mem_support _
  have hl : (TwoColorIncidenceGraph G secondStable gamma choice.color).Adj
      (path.getVert n) (path.getVert (n - 1)) := by
    rw [← show n - 1 + 1 = n by omega]
    exact (path.adj_getVert_succ (by omega)).symm
  have hnlt : n < path.length := lt_of_le_of_ne hnle hlast
  have hr := path.adj_getVert_succ hnlt
  by_contra hyout
  rw [← hn] at hxy
  have hnl : path.getVert (n - 1) ≠ y := by
    intro h; apply hyout; rw [← h]; exact path.getVert_mem_support _
  have hnr : path.getVert (n + 1) ≠ y := by
    intro h; apply hyout; rw [← h]; exact path.getVert_mem_support _
  have hnp : path.getVert (n - 1) ≠ path.getVert (n + 1) := by
    intro h
    have hi := pathIs.getVert_injOn (show n - 1 ≤ path.length by omega)
      (show n + 1 ≤ path.length by omega) h
    omega
  let graph := TwoColorIncidenceGraph G secondStable gamma choice.color
  let : Fintype (graph.neighborSet (path.getVert n)) := Fintype.ofFinite _
  have three : 3 ≤ graph.degree (path.getVert n) := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    let s : Finset _ := {y, path.getVert (n - 1), path.getVert (n + 1)}
    have hs : s ⊆ graph.neighborFinset (path.getVert n) := by
      intro t ht
      simp only [s, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · simpa [graph, SimpleGraph.mem_neighborFinset] using hxy
      · simpa [graph, SimpleGraph.mem_neighborFinset] using hl
      · simpa [graph, SimpleGraph.mem_neighborFinset] using hr
    have hc : 3 ≤ s.card := by simp [s, hnp, hnl.symm, hnr.symm]
    exact hc.trans (Finset.card_le_card hs)
  have upper : graph.degree (path.getVert n) ≤ 2 := by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, Fintype.card_eq_nat_card] using
      hdegreeBound (path.getVert n)
  omega

theorem helper_htreeEdge_2018.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (secondStable : PartialEdgeColoring E k), IsProperEdgeColoring G
        secondStable →
    ∀ (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)),
        gamma ∈ MissingColors G secondStable choice.vertex →
    ∀ (u : V) (path : (TwoColorIncidenceGraph G secondStable gamma choice.color).Walk (Sum.inl u)
        (Sum.inl choice.vertex)), ((gamma ∈ MissingColors G secondStable u ∨ choice.color ∈
        MissingColors G secondStable u) ∧
    ∀ w ∈ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc), Sum.inl w ∈ path.support ↔
        w = choice.vertex) → (
    ∀ y ∈ TwoColorComponent G secondStable gamma choice.color (Sum.inl choice.vertex), y ∈
        path.support) → (
    ∀ (e : E), Sum.inr e ∈ TwoColorComponent G secondStable gamma choice.color (Sum.inl
        choice.vertex) → secondStable e = some gamma ∨ secondStable e = some choice.color) →
        secondStable choice.edge = some choice.color →
    ∀ (e : E), TreeIncidentEdge (ett.series.data.tree q.succ.castSucc) e → Sum.inr e ∈
        TwoColorComponent G secondStable gamma choice.color (Sum.inl choice.vertex) → e =
        choice.edge := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ q gamma secondStable
      secondStableProper choice hmissing u path endOnly hpathComponent hcompEdge hchoiceSecond e
      heT heC
  rcases heT with ⟨w, hw, hwe⟩
  have hwC : Sum.inl w ∈ TwoColorComponent G secondStable gamma choice.color
      (Sum.inl choice.vertex) := by
    have hadj : (TwoColorIncidenceGraph G secondStable gamma choice.color).Adj
        (Sum.inl w) (Sum.inr e) := by
      simp [TwoColorIncidenceGraph, hwe, hcompEdge e heC]
    change (TwoColorIncidenceGraph G secondStable gamma choice.color).connectedComponentMk
        (Sum.inl w) = _
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans heC
  have hwv : w = choice.vertex := (endOnly.2 w hw).mp (hpathComponent _ hwC)
  subst w
  rcases hcompEdge e heC with hec | hec
  · have hnot : secondStable e ≠ some gamma := by
      intro heq
      have hp : gamma ∈ PresentColors G secondStable choice.vertex := by
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨e, hwe, heq⟩
      have hm : gamma ∉ PresentColors G secondStable choice.vertex := by
        simpa [MissingColors] using hmissing
      exact hm hp
    exact (hnot hec).elim
  · by_contra hne
    exact (secondStableProper hne ⟨choice.vertex, hwe, choice.edgeIncident⟩ hec
      hchoiceSecond).elim

theorem helper_hsigmaEdge_2047.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k), IsProperEdgeColoring G sigma →
    ∀ (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds); StableColoring (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.succ) (ett.series.data.coloring q.succ) sigma →
    ∀ (gamma : Fin k) (secondStable : PartialEdgeColoring E k), IsProperEdgeColoring G
        secondStable →
    ∀ (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)),
        ett.series.data.coloring q.succ = TwoColorComponentSwap G secondStable gamma choice.color
        (Sum.inl choice.vertex) → ett.series.data.stored q.succ = (insert choice.color ({ gamma }
        : Finset (Fin k)) : Finset (Fin k)) → choice.vertex ∈ TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc) → (
    ∀ w ∈ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc), Sum.inl w ∈
        TwoColorComponent G sigma gamma choice.color (Sum.inl choice.vertex) ↔ w = choice.vertex)
        → gamma ∈ MissingColors G secondStable choice.vertex →
    ∀ (_ : V), (
    ∀ (e : E), Sum.inr e ∈ TwoColorComponent G secondStable gamma choice.color (Sum.inl
        choice.vertex) → secondStable e = some gamma ∨ secondStable e = some choice.color) →
        secondStable choice.edge = some choice.color → gamma ≠ choice.color → Sum.inr choice.edge
        ∈ TwoColorComponent G secondStable gamma choice.color (Sum.inl choice.vertex) →
    ∀ (e : E), TreeIncidentEdge (ett.series.data.tree q.succ.castSucc) e → Sum.inr e ∈
        TwoColorComponent G sigma gamma choice.color (Sum.inl choice.vertex) → e = choice.edge := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma hsigmaProper _ q
      hsigmaStableQ gamma secondStable secondStableProper choice currentColoring currentStored
      hchoiceVertex hcomponent hmissing u hcompEdge hchoiceSecond hneq hfcomponent e heT heC
  rcases heT with ⟨w, hw, hwe⟩
  have hgamma : sigma choice.edge = some gamma := by
    have hsc := hsigmaStableQ.1 choice.edge
      ⟨choice.vertex, choice.vertexDefective.1, choice.edgeIncident⟩
    have hctrl : ∃ c ∈ TreeMissingColors (ett.series.data.coloring q.succ)
        (ett.series.data.tree q.succ.castSucc) ∪ TashkinovStoredColors ett.series.data q.succ,
        ett.series.data.coloring q.succ choice.edge = some c := by
      refine ⟨gamma, ?_, ?_⟩
      · by_cases hm : gamma ∈ TreeMissingColors (ett.series.data.coloring q.succ)
            (ett.series.data.tree q.succ.castSucc)
        · exact Finset.mem_union.mpr (Or.inl hm)
        · apply Finset.mem_union.mpr
          right
          unfold TashkinovStoredColors
          rw [ite_eq_right (by simp)]
          simp only [Finset.mem_sdiff, Finset.mem_biUnion]
          constructor
          · refine ⟨q.succ, ?_, ?_⟩
            · simp
            · simp [currentStored]
          · simpa using hm
      · rw [currentColoring]
        simp [TwoColorComponentSwap, hfcomponent, hchoiceSecond]
    exact (hsc hctrl).trans (by
      rw [currentColoring]
      simp [TwoColorComponentSwap, hfcomponent, hchoiceSecond])
  have hecol : sigma e = some gamma ∨ sigma e = some choice.color := by
    have hs : Sum.inr e ∈
        (TwoColorIncidenceGraph G sigma gamma choice.color).support := by
      apply SimpleGraph.mem_support_of_reachable
        (G := TwoColorIncidenceGraph G sigma gamma choice.color)
        (u := Sum.inr e) (v := Sum.inl choice.vertex) (by simp)
      exact SimpleGraph.ConnectedComponent.eq.mp heC
    obtain ⟨r, hr⟩ :=
      (TwoColorIncidenceGraph G sigma gamma choice.color).mem_support.mp hs
    cases r with
    | inl x => exact hr.2
    | inr x => simp [TwoColorIncidenceGraph] at hr
  have hwC : Sum.inl w ∈ TwoColorComponent G sigma gamma choice.color
      (Sum.inl choice.vertex) := by
    have hadj : (TwoColorIncidenceGraph G sigma gamma choice.color).Adj
        (Sum.inl w) (Sum.inr e) := by
      simp [TwoColorIncidenceGraph, hwe, hecol]
    change (TwoColorIncidenceGraph G sigma gamma choice.color).connectedComponentMk
        (Sum.inl w) = _
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans heC
  have hwv := (hcomponent w hw).mp hwC
  subst w
  rcases hecol with hec | hec
  · have hp : gamma ∈ PresentColors G sigma choice.vertex := by
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨e, hwe, hec⟩
    by_contra hne
    exact (hsigmaProper hne ⟨choice.vertex, hwe, choice.edgeIncident⟩ hec hgamma).elim
  · by_contra hne
    have hcolor : sigma e = some choice.color := hec
    have hmissColor : choice.color ∈ MissingColors G sigma choice.vertex := by
      rw [hsigmaStableQ.2 choice.vertex hchoiceVertex]
      rw [MissingColors]
      simp only [Finset.mem_sdiff]
      refine ⟨?_, ?_⟩
      · exact Finset.mem_univ _
      · intro hp
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and] at hp
        rcases hp with ⟨a, hae, hac⟩
        by_cases ha : Sum.inr a ∈
            TwoColorComponent G secondStable gamma choice.color
              (Sum.inl choice.vertex)
        · rcases hcompEdge a ha with hag | hacs
          · have hn : gamma ∉ PresentColors G secondStable choice.vertex := by
              simpa [MissingColors] using hmissing
            exact hn (by
              simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨a, hae, hag⟩)
          · rw [currentColoring] at hac
            simp [TwoColorComponentSwap, ha, hacs, hneq, hneq.symm] at hac
        · rw [currentColoring] at hac
          have hac' : secondStable a = some choice.color := by
            simpa [TwoColorComponentSwap, ha] using hac
          have hne : a ≠ choice.edge := by
            intro heq
            apply ha
            exact heq ▸ hfcomponent
          exact (secondStableProper hne ⟨choice.vertex, hae, choice.edgeIncident⟩
            hac' hchoiceSecond).elim
    have hnot : choice.color ∉ PresentColors G sigma choice.vertex := by
      change choice.color ∈ Finset.univ \ PresentColors G sigma choice.vertex at hmissColor
      exact (Finset.mem_sdiff.mp hmissColor).2
    exact (hnot (by
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨e, hwe, hcolor⟩)).elim

theorem helper_undoneOne_2148.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k), IsOneEdgeUncolored sigma e0 →
    ∀ (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)),
        gamma ≠ choice.color →
    let undone : PartialEdgeColoring E k := TwoColorComponentSwap G sigma gamma choice.color
        (Sum.inl choice.vertex); IsOneEdgeUncolored undone e0 := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma hsigmaOne _ q gamma choice
      hneq undone
  unfold IsOneEdgeUncolored
  constructor
  · by_cases he : Sum.inr e0 ∈
      TwoColorComponent G sigma gamma choice.color (Sum.inl choice.vertex)
    · simp [undone, TwoColorComponentSwap, he, hsigmaOne.1]
    · simp [undone, TwoColorComponentSwap, he, hsigmaOne.1]
  · intro e he
    obtain ⟨c, hc⟩ := hsigmaOne.2 e he
    by_cases hec : Sum.inr e ∈
        TwoColorComponent G sigma gamma choice.color (Sum.inl choice.vertex)
    · by_cases hcg : c = gamma
      · exact ⟨choice.color, by simp [undone, TwoColorComponentSwap, hec, hc, hcg]⟩
      · by_cases hcd : c = choice.color
        · exact ⟨gamma, by simp [undone, TwoColorComponentSwap, hec, hc, hcd,
            hneq.symm]⟩
        · exact ⟨c, by simp [undone, TwoColorComponentSwap, hec, hc, hcg, hcd]⟩
    · exact ⟨c, by simp [undone, TwoColorComponentSwap, hec, hc]⟩

theorem helper_currentColorMissing_2202.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (secondStable : PartialEdgeColoring E k), IsProperEdgeColoring G
        secondStable →
    ∀ (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)),
        ett.series.data.coloring q.succ = TwoColorComponentSwap G secondStable gamma choice.color
        (Sum.inl choice.vertex) → gamma ∈ MissingColors G secondStable choice.vertex → (
    ∀ (e : E), Sum.inr e ∈ TwoColorComponent G secondStable gamma choice.color (Sum.inl
        choice.vertex) → secondStable e = some gamma ∨ secondStable e = some choice.color) →
        secondStable choice.edge = some choice.color → gamma ≠ choice.color → Sum.inr choice.edge
        ∈ TwoColorComponent G secondStable gamma choice.color (Sum.inl choice.vertex) →
        choice.color ∈ MissingColors G (ett.series.data.coloring q.succ) choice.vertex := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ q gamma secondStable
      secondStableProper choice currentColoring hmissing hcompEdge hchoiceSecond hneq hfcomponent
  rw [MissingColors]
  simp only [Finset.mem_sdiff]
  refine ⟨Finset.mem_univ _, ?_⟩
  intro hp
  simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and] at hp
  rcases hp with ⟨e, he, hec⟩
  rw [currentColoring] at hec
  by_cases hecomp : Sum.inr e ∈
      TwoColorComponent G secondStable gamma choice.color (Sum.inl choice.vertex)
  · rcases hcompEdge e hecomp with hegamma | hecolor
    · have hm : gamma ∉ PresentColors G secondStable choice.vertex := by
        simpa [MissingColors] using hmissing
      apply hm
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨e, he, hegamma⟩
    · simp [TwoColorComponentSwap, hecomp, hecolor, hneq, hneq.symm] at hec
  · have hecolor : secondStable e = some choice.color := by
      simpa [TwoColorComponentSwap, hecomp] using hec
    by_cases heq : e = choice.edge
    · subst e
      exact (hecomp hfcomponent).elim
    · exact (secondStableProper heq ⟨choice.vertex, he, choice.edgeIncident⟩
        hecolor hchoiceSecond).elim

theorem helper_currentControl_2238.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)),
        ett.series.data.stored q.succ = (insert choice.color ({ gamma } : Finset (Fin k)) : Finset
        (Fin k)) → TreeMissingColors choice.selected (ett.series.data.tree q.succ.castSucc) =
        TreeMissingColors (ett.series.data.coloring q.castSucc) (ett.series.data.tree
        q.succ.castSucc) →
    ∀ c ∈ TreeMissingColors choice.selected (ett.series.data.tree q.succ.castSucc) ∪ (insert
        choice.color (TashkinovStoredColors ett.series.data q.castSucc) : Finset (Fin k)), c ∈
        TreeMissingColors (ett.series.data.coloring q.succ) (ett.series.data.tree q.succ.castSucc)
        ∪ TashkinovStoredColors ett.series.data q.succ := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ q gamma choice currentStored
      treeSelectedPrevious c hc
  rcases Finset.mem_union.mp hc with hc | hc
  · apply (HkuMissingStoredMonotone G k ett.rounds e0 input ett.series q).1
    rw [treeSelectedPrevious] at hc
    exact Finset.mem_union.mpr (Or.inl hc)
  · rcases Finset.mem_insert.mp hc with rfl | hc
    · by_cases hm : choice.color ∈ TreeMissingColors
          (ett.series.data.coloring q.succ) (ett.series.data.tree q.succ.castSucc)
      · exact Finset.mem_union.mpr (Or.inl hm)
      · apply Finset.mem_union.mpr
        right
        unfold TashkinovStoredColors
        rw [ite_eq_right (by simp)]
        simp only [Finset.mem_sdiff, Finset.mem_biUnion]
        exact ⟨⟨q.succ, by simp, by simp [currentStored]⟩, hm⟩
    · exact (HkuMissingStoredMonotone G k ett.rounds e0 input ett.series q).1
        (Finset.mem_union.mpr (Or.inr hc))

theorem helper_stableSelected_2405.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (secondStable : PartialEdgeColoring E k), IsProperEdgeColoring G
        secondStable → IsOneEdgeUncolored secondStable e0 →
    ∀ (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)),
        StableColoring (ett.series.data.tree q.succ.castSucc) (insert choice.color
        (TashkinovStoredColors ett.series.data q.castSucc) : Finset (Fin k)) choice.selected
        secondStable →
    let undone : PartialEdgeColoring E k := TwoColorComponentSwap G sigma gamma choice.color
        (Sum.inl choice.vertex); IsProperEdgeColoring G undone → IsOneEdgeUncolored undone e0 →
        TreeMissingColors secondStable (ett.series.data.tree q.succ.castSucc) = TreeMissingColors
        choice.selected (ett.series.data.tree q.succ.castSucc) → StableColoring
        (ett.series.data.tree q.succ.castSucc) (insert choice.color (TashkinovStoredColors
        ett.series.data q.castSucc) : Finset (Fin k)) secondStable undone → StableColoring
        (ett.series.data.tree q.succ.castSucc) (insert choice.color (TashkinovStoredColors
        ett.series.data q.castSucc) : Finset (Fin k)) choice.selected undone := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma _ q gamma secondStable
      secondStableProper secondStableOneUncolored choice secondStableRelation undone undoneProper
      undoneOne treeSecondSelected stableSecond
  apply (sc1 G e0 (ett.series.data.tree q.succ.castSucc)
    (insert choice.color (TashkinovStoredColors ett.series.data q.castSucc))
    choice.selected undone choice.selectedProper choice.selectedOneUncolored
    undoneProper undoneOne).2
  have stableSecondCriterion :=
    ((sc1 G e0 (ett.series.data.tree q.succ.castSucc)
      (insert choice.color (TashkinovStoredColors ett.series.data q.castSucc))
      secondStable undone secondStableProper secondStableOneUncolored
      undoneProper undoneOne).mp stableSecond)
  intro f hf h
  rcases h with h | h
  · rcases h with ⟨c, hc, hcf⟩
    have hrel := secondStableRelation.1 f hf
      ⟨c, hc, hcf⟩
    have hc2 := hc
    rw [← treeSecondSelected] at hc2
    have hstable := stableSecondCriterion f hf
      (Or.inl ⟨c, hc2, hrel.trans hcf⟩)
    exact hstable.trans hrel
  · rcases h with ⟨c, hc, hcf⟩
    have hc2 := hc
    rw [← treeSecondSelected] at hc2
    have hstable := stableSecondCriterion f hf
      (Or.inr ⟨c, hc2, hcf⟩)
    have hsecond : secondStable f = some c := hstable.symm.trans hcf
    have relationCriterion :=
      ((sc1 G e0 (ett.series.data.tree q.succ.castSucc)
        (insert choice.color (TashkinovStoredColors ett.series.data q.castSucc))
        choice.selected secondStable choice.selectedProper choice.selectedOneUncolored
        secondStableProper secondStableOneUncolored).mp secondStableRelation)
    have hrel := relationCriterion f hf (Or.inr ⟨c, hc, hsecond⟩)
    exact hstable.trans hrel

theorem helper_hdeltaBoundary_2443.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (sigmaPrev : PartialEdgeColoring E k), IsProperEdgeColoring G sigmaPrev →
        IsOneEdgeUncolored sigmaPrev e0 → StableColoring (ett.series.data.tree q.succ.castSucc)
        (insert choice.color (TashkinovStoredColors ett.series.data q.castSucc) : Finset (Fin k))
        choice.selected sigmaPrev → BoundaryColorEdges G choice.selected (TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc)) choice.color = BoundaryColorEdges G sigmaPrev
        (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) choice.color := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ q choice sigmaPrev hsigmaPrevProper
      hsigmaPrevOne hsigmaPrevEnlarged
  ext f
  simp only [BoundaryColorEdges, Finset.mem_filter]
  constructor
  · rintro ⟨hf, hfc⟩
    refine ⟨hf, ?_⟩
    obtain ⟨x, hx, y, hy, hends⟩ := by
      simpa [BoundaryEdges] using hf
    have hinc : TreeIncidentEdge
        (ett.series.data.tree q.succ.castSucc) f := by
      refine ⟨x, hx, ?_⟩
      unfold Incident
      rw [hends]
      exact Sym2.mem_mk_left _ _
    exact (hsigmaPrevEnlarged.1 f hinc
      ⟨choice.color, Finset.mem_union_right _
        (Finset.mem_insert_self _ _), hfc⟩).trans hfc
  · rintro ⟨hf, hfc⟩
    refine ⟨hf, ?_⟩
    obtain ⟨x, hx, y, hy, hends⟩ := by
      simpa [BoundaryEdges] using hf
    have hinc : TreeIncidentEdge
        (ett.series.data.tree q.succ.castSucc) f := by
      refine ⟨x, hx, ?_⟩
      unfold Incident
      rw [hends]
      exact Sym2.mem_mk_left _ _
    have hcriterion := (sc1 G e0
      (ett.series.data.tree q.succ.castSucc)
      (insert choice.color
        (TashkinovStoredColors ett.series.data q.castSucc))
      choice.selected sigmaPrev choice.selectedProper
      choice.selectedOneUncolored hsigmaPrevProper hsigmaPrevOne).mp
        hsigmaPrevEnlarged
    exact (hcriterion f hinc (Or.inr
      ⟨choice.color, Finset.mem_union_right _
        (Finset.mem_insert_self _ _), hfc⟩)).symm.trans hfc

theorem helper_hclosedPrev_2545.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds); IsProperEdgeColoring G (ett.series.data.coloring q.castSucc) →
        IsOneEdgeUncolored (ett.series.data.coloring q.castSucc) e0 → ColoredVertexSetClosed G
        (ett.series.data.coloring q.castSucc) (TreeSequenceVertexSet (ett.series.data.tree
        q.succ.castSucc)) →
    ∀ (sigmaPrev : PartialEdgeColoring E k), IsProperEdgeColoring G sigmaPrev → IsOneEdgeUncolored
        sigmaPrev e0 → StableColoring (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)
        sigmaPrev → ColoredVertexSetClosed G sigmaPrev (TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc)) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ q previousProper
      previousOneUncolored previousClosed sigmaPrev hsigmaPrevProper hsigmaPrevOne hsigmaPrevStableQ
      f c v hf hv hsf hcm
  obtain ⟨x, hx, y, hy, hends⟩ := by
    simpa [BoundaryEdges] using hf
  have hinc : TreeIncidentEdge
      (ett.series.data.tree q.succ.castSucc) f := by
    refine ⟨x, hx, ?_⟩
    unfold Incident
    rw [hends]
    exact Sym2.mem_mk_left _ _
  have hmissingEq := hsigmaPrevStableQ.2 v hv
  have hcTree : c ∈ TreeMissingColors
      (ett.series.data.coloring q.castSucc)
      (ett.series.data.tree q.succ.castSucc) := by
    simp only [TreeMissingColors, Finset.mem_biUnion]
    exact ⟨v, hv, hmissingEq ▸ hcm⟩
  have hcriterion := (sc1 G e0
    (ett.series.data.tree q.succ.castSucc)
    (TashkinovStoredColors ett.series.data q.castSucc)
    (ett.series.data.coloring q.castSucc) sigmaPrev previousProper
    previousOneUncolored hsigmaPrevProper hsigmaPrevOne).mp
      hsigmaPrevStableQ
  have hcopy := hcriterion f hinc
    (Or.inr ⟨c, Finset.mem_union_left _ hcTree, hsf⟩)
  have holdf : ett.series.data.coloring q.castSucc f = some c :=
    hcopy.symm.trans hsf
  exact previousClosed hf hv holdf (hmissingEq ▸ hcm)

theorem helper_hdeltaCurrentMissing_2652.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (secondStable : PartialEdgeColoring E k), IsProperEdgeColoring G
        secondStable →
    ∀ (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)),
        ett.series.data.coloring q.succ = TwoColorComponentSwap G secondStable gamma choice.color
        (Sum.inl choice.vertex) → gamma ∈ MissingColors G secondStable choice.vertex →
        secondStable choice.edge = some choice.color → gamma ≠ choice.color → Sum.inr choice.edge
        ∈ TwoColorComponent G secondStable gamma choice.color (Sum.inl choice.vertex) →
        choice.color ∈ MissingColors G (ett.series.data.coloring q.succ) choice.vertex := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ q gamma secondStable
      secondStableProper choice currentColoring hgammaSecond hchoiceSecond hgammaDeltaNe
      hchoiceSecondComponent
  rw [MissingColors]
  simp only [Finset.mem_sdiff]
  refine ⟨Finset.mem_univ _, ?_⟩
  intro hpresent
  simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
    true_and] at hpresent
  rcases hpresent with ⟨f, hfIncident, hfCurrent⟩
  rw [currentColoring] at hfCurrent
  by_cases hfComponent : Sum.inr f ∈
      TwoColorComponent G secondStable gamma choice.color
        (Sum.inl choice.vertex)
  · by_cases hfg : secondStable f = some gamma
    · have hp : gamma ∈ PresentColors G secondStable choice.vertex := by
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
          true_and]
        exact ⟨f, hfIncident, hfg⟩
      have hnot : gamma ∉ PresentColors G secondStable choice.vertex := by
        simpa [MissingColors] using hgammaSecond
      exact hnot hp
    · by_cases hfd : secondStable f = some choice.color
      · have heq : choice.color = gamma := by
          simpa [TwoColorComponentSwap, hfComponent, hfg, hfd,
            hgammaDeltaNe] using hfCurrent
        exact hgammaDeltaNe heq.symm
      · simp [TwoColorComponentSwap, hfComponent, hfg, hfd] at hfCurrent
  · have hfd : secondStable f = some choice.color := by
      simpa [TwoColorComponentSwap, hfComponent] using hfCurrent
    by_cases hfeq : f = choice.edge
    · subst f
      exact hfComponent hchoiceSecondComponent
    · exact (secondStableProper hfeq
        ⟨choice.vertex, hfIncident, choice.edgeIncident⟩
        hfd hchoiceSecond).elim

theorem helper_hgammaPrevMissing_2707.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (sigmaPrev : PartialEdgeColoring E k), sigmaPrev = TwoColorComponentSwap G sigma gamma
        choice.color (Sum.inl choice.vertex) → gamma ≠ choice.color → choice.color ∈ MissingColors
        G sigma choice.vertex → (
    ∀ (f : E), Sum.inr f ∈ TwoColorComponent G sigma gamma choice.color (Sum.inl choice.vertex) →
        sigma f = some gamma ∨ sigma f = some choice.color) → gamma ∈ MissingColors G sigmaPrev
        choice.vertex := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma _ q gamma choice sigmaPrev
      hsigmaPrevFormula hgammaDeltaNe hdeltaSigmaMissing hsigmaComponentColor
  rw [MissingColors]
  simp only [Finset.mem_sdiff]
  refine ⟨Finset.mem_univ _, ?_⟩
  intro hpresent
  simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
    true_and] at hpresent
  rcases hpresent with ⟨f, hfIncident, hfPrev⟩
  rw [hsigmaPrevFormula] at hfPrev
  by_cases hfComponent : Sum.inr f ∈
      TwoColorComponent G sigma gamma choice.color
        (Sum.inl choice.vertex)
  · rcases hsigmaComponentColor f hfComponent with hfg | hfd
    · have heq : choice.color = gamma := by
        simpa [TwoColorComponentSwap, hfComponent, hfg,
          hgammaDeltaNe] using hfPrev
      exact hgammaDeltaNe heq.symm
    · have hp : choice.color ∈ PresentColors G sigma choice.vertex := by
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
          true_and]
        exact ⟨f, hfIncident, hfd⟩
      have hnot : choice.color ∉ PresentColors G sigma choice.vertex := by
        simpa [MissingColors] using hdeltaSigmaMissing
      exact hnot hp
  · have hfg : sigma f = some gamma := by
      simpa [TwoColorComponentSwap, hfComponent] using hfPrev
    apply hfComponent
    apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    simp [TwoColorIncidenceGraph, hfIncident, hfg]

theorem helper_hswapGraph_2737.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (sigmaPrev : PartialEdgeColoring E k), sigmaPrev = TwoColorComponentSwap G sigma gamma
        choice.color (Sum.inl choice.vertex) → gamma ≠ choice.color → (
    ∀ (f : E), Sum.inr f ∈ TwoColorComponent G sigma gamma choice.color (Sum.inl choice.vertex) →
        sigma f = some gamma ∨ sigma f = some choice.color) → TwoColorIncidenceGraph G sigmaPrev
        gamma choice.color = TwoColorIncidenceGraph G sigma gamma choice.color := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma _ q gamma choice sigmaPrev
      hsigmaPrevFormula hgammaDeltaNe hsigmaComponentColor
  rw [hsigmaPrevFormula]
  ext x y
  cases x with
  | inl v =>
      cases y with
      | inl w => simp [TwoColorIncidenceGraph]
      | inr f =>
          by_cases hf : Sum.inr f ∈ TwoColorComponent G sigma gamma
              choice.color (Sum.inl choice.vertex)
          · rcases hsigmaComponentColor f hf with hfg | hfd
            · simp [TwoColorIncidenceGraph, TwoColorComponentSwap, hf,
                hfg, hgammaDeltaNe]
            · simp [TwoColorIncidenceGraph, TwoColorComponentSwap, hf,
                hfd, hgammaDeltaNe]
          · simp [TwoColorIncidenceGraph, TwoColorComponentSwap, hf]
  | inr f =>
      cases y with
      | inl v =>
          by_cases hf : Sum.inr f ∈ TwoColorComponent G sigma gamma
              choice.color (Sum.inl choice.vertex)
          · rcases hsigmaComponentColor f hf with hfg | hfd
            · simp [TwoColorIncidenceGraph, TwoColorComponentSwap, hf,
                hfg, hgammaDeltaNe]
            · simp [TwoColorIncidenceGraph, TwoColorComponentSwap, hf,
                hfd, hgammaDeltaNe]
          · simp [TwoColorIncidenceGraph, TwoColorComponentSwap, hf]
      | inr g => simp [TwoColorIncidenceGraph]

theorem helper_hsigmaRecovered_2774.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (sigmaPrev : PartialEdgeColoring E k), sigmaPrev = TwoColorComponentSwap G sigma gamma
        choice.color (Sum.inl choice.vertex) → gamma ≠ choice.color → (
    ∀ (f : E), Sum.inr f ∈ TwoColorComponent G sigma gamma choice.color (Sum.inl choice.vertex) →
        sigma f = some gamma ∨ sigma f = some choice.color) → TwoColorIncidenceGraph G sigmaPrev
        gamma choice.color = TwoColorIncidenceGraph G sigma gamma choice.color → sigma =
        TwoColorComponentSwap G sigmaPrev gamma choice.color (Sum.inl choice.vertex) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma _ q gamma choice sigmaPrev
      hsigmaPrevFormula hgammaDeltaNe hsigmaComponentColor hswapGraph
  funext f
  have hcomponentEq :
      (Sum.inr f ∈ TwoColorComponent G sigmaPrev gamma choice.color
          (Sum.inl choice.vertex)) ↔
        Sum.inr f ∈ TwoColorComponent G sigma gamma choice.color
          (Sum.inl choice.vertex) := by
    unfold TwoColorComponent
    rw [hswapGraph]
  by_cases hf : Sum.inr f ∈ TwoColorComponent G sigma gamma
      choice.color (Sum.inl choice.vertex)
  · have hfPrev := hcomponentEq.mpr hf
    rcases hsigmaComponentColor f hf with hfg | hfd
    · have hprevValue : sigmaPrev f = some choice.color := by
        rw [hsigmaPrevFormula, TwoColorComponentSwap, ite_eq_left hf]
        simp [hfg]
      rw [TwoColorComponentSwap, ite_eq_left hfPrev, hprevValue]
      simpa [hgammaDeltaNe, hgammaDeltaNe.symm] using hfg
    · have hprevValue : sigmaPrev f = some gamma := by
        rw [hsigmaPrevFormula, TwoColorComponentSwap, ite_eq_left hf]
        simp [hfd]
      rw [TwoColorComponentSwap, ite_eq_left hfPrev, hprevValue]
      simpa [hgammaDeltaNe, hgammaDeltaNe.symm] using hfd
  · have hfPrev : Sum.inr f ∉ TwoColorComponent G sigmaPrev gamma
        choice.color (Sum.inl choice.vertex) := by
      simpa [hcomponentEq] using hf
    rw [TwoColorComponentSwap, ite_eq_right hfPrev, hsigmaPrevFormula,
      TwoColorComponentSwap, ite_eq_right hf]

theorem helper_hendNeighbor_2869.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (sigmaPrev : PartialEdgeColoring E k), IsProperEdgeColoring G sigmaPrev →
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G sigmaPrev gamma choice.color;
        (H.neighborSet (Sum.inl choice.vertex)).Subsingleton →
    ∀ (a b_1 : V ⊕ E) (p_1 : (TwoColorIncidenceGraph G sigmaPrev gamma choice.color).Walk a b_1),
        p_1.IsPath → {x : V ⊕ E | x ∈ p_1.support} = TwoColorComponent G sigmaPrev gamma
        choice.color (Sum.inl choice.vertex) →
    ∀ (b : V ⊕ E) (p : H.Walk (Sum.inl choice.vertex) b), p.IsPath → {z : V ⊕ E | z ∈ p.support} =
        TwoColorComponent G sigmaPrev gamma choice.color (Sum.inl choice.vertex) → ¬p.Nil →
    ∀ (y : V ⊕ E), H.Adj b y → y = p.getVert (p.length - (1 : ℕ)) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ q gamma choice sigmaPrev
      hsigmaPrevProper H hrootLeaf a _ _ _ _ b p hp hps hpNotNil y hby
  have hyComponent : y ∈ TwoColorComponent G sigmaPrev gamma
      choice.color (Sum.inl choice.vertex) := by
    have hbComponent : b ∈ TwoColorComponent G sigmaPrev gamma
        choice.color (Sum.inl choice.vertex) := by
      rw [← hps]
      change b ∈ p.support
      simpa only [p.getVert_length] using
        p.getVert_mem_support p.length
    change H.connectedComponentMk y =
      H.connectedComponentMk (Sum.inl choice.vertex)
    change H.connectedComponentMk b =
      H.connectedComponentMk (Sum.inl choice.vertex) at hbComponent
    exact
      (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        hby).symm.trans hbComponent
  have hySupport : y ∈ p.support := by
    change y ∈ {z | z ∈ p.support}
    rw [hps]
    exact hyComponent
  obtain ⟨n, hn, hnle⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hySupport
  have hnlt : n < p.length := by
    have hnne : n ≠ p.length := by
      intro heq
      have hyb : y = b := by
        rw [← hn, heq, p.getVert_length]
      exact hby.ne hyb.symm
    omega
  by_cases hpen : n + 1 = p.length
  · rw [← hn]
    congr 1
    omega
  by_cases hn0 : n = 0
  · have hnext : H.Adj (Sum.inl choice.vertex) (p.getVert 1) := by
      simpa [hn0, p.getVert_zero] using
        p.adj_getVert_succ hnlt
    have hbstart : H.Adj (Sum.inl choice.vertex) b := by
      rw [← hn, hn0, p.getVert_zero] at hby
      exact hby.symm
    have hneNext : p.getVert 1 ≠ b := by
      intro heq
      have hindices := hp.getVert_injOn
        (show 1 ≤ p.length by omega)
        (show p.length ≤ p.length by rfl)
        (heq.trans p.getVert_length.symm)
      omega
    exact False.elim (hneNext (hrootLeaf hnext hbstart))
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hleft : H.Adj y (p.getVert (n - 1)) := by
      rw [← hn]
      have hadj := p.adj_getVert_succ (i := n - 1) (by omega)
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using
        hadj.symm
    have hright : H.Adj y (p.getVert (n + 1)) := by
      rw [← hn]
      exact p.adj_getVert_succ hnlt
    have hbneLeft : b ≠ p.getVert (n - 1) := by
      intro heq
      have hindices := hp.getVert_injOn
        (show p.length ≤ p.length by rfl)
        (show n - 1 ≤ p.length by omega)
        (p.getVert_length.trans heq)
      omega
    have hbneRight : b ≠ p.getVert (n + 1) := by
      intro heq
      have hindices := hp.getVert_injOn
        (show p.length ≤ p.length by rfl)
        (show n + 1 ≤ p.length by omega)
        (p.getVert_length.trans heq)
      omega
    have hlrne : p.getVert (n - 1) ≠ p.getVert (n + 1) := by
      intro heq
      have hindices := hp.getVert_injOn
        (show n - 1 ≤ p.length by omega)
        (show n + 1 ≤ p.length by omega) heq
      omega
    let : Fintype (H.neighborSet y) := Fintype.ofFinite _
    have hthree : 3 ≤ @SimpleGraph.degree _ H y
        (Fintype.ofFinite _) := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      let ss : Finset (Sum V E) :=
        {b, p.getVert (n - 1), p.getVert (n + 1)}
      have hss : ss ⊆ H.neighborFinset y := by
        intro z hz
        simp only [ss, Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        · simpa [SimpleGraph.mem_neighborFinset] using hby.symm
        · simpa [SimpleGraph.mem_neighborFinset] using hleft
        · simpa [SimpleGraph.mem_neighborFinset] using hright
      have hc3 : 3 ≤ ss.card := by
        simp [ss, hbneLeft, hbneRight, hlrne]
      exact hc3.trans (Finset.card_le_card hss)
    have htwo : @SimpleGraph.degree _ H y
        (Fintype.ofFinite _) ≤ 2 := by
      simpa [H] using TwoColorIncidenceDegreeAtMostTwo G sigmaPrev
        gamma choice.color hsigmaPrevProper y
    omega

theorem helper_hendVertex_2974.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (sigmaPrev : PartialEdgeColoring E k),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G sigmaPrev gamma choice.color;
    ∀ (a b_1 : V ⊕ E) (_ : (TwoColorIncidenceGraph G sigmaPrev gamma choice.color).Walk a b_1) (b
        : V ⊕ E) (p : H.Walk (Sum.inl choice.vertex) b), (H.neighborSet b).Subsingleton → (0 : ℕ)
        < p.length →
    ∃ (u : V), b = Sum.inl u := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ q gamma choice sigmaPrev H a _ _
      b p hendLeaf hpPos
  cases hb : b with
  | inl u => exact ⟨u, rfl⟩
  | inr e =>
      have hlastAdj : H.Adj (p.getVert (p.length - 1)) b := by
        simpa only [Nat.sub_add_cancel (by omega : 1 ≤ p.length),
          p.getVert_length] using
          p.adj_getVert_succ (i := p.length - 1) (by omega)
      have hecolor : sigmaPrev e = some gamma ∨
          sigmaPrev e = some choice.color := by
        cases hprev : p.getVert (p.length - 1) with
        | inl w =>
            rw [hprev, hb] at hlastAdj
            have hdata : Incident G w e ∧
                (sigmaPrev e = some gamma ∨
                  sigmaPrev e = some choice.color) := by
              simpa [H, TwoColorIncidenceGraph] using hlastAdj
            exact hdata.2
        | inr f =>
            rw [hprev, hb] at hlastAdj
            have : False := by
              simp [H, TwoColorIncidenceGraph] at hlastAdj
            exact this.elim
      induction hends : G.ends e using Sym2.inductionOn with
      | _ u v =>
          have huv : u ≠ v := by
            intro huv
            subst v
            exact G.loopless e u hends
          have huAdj : H.Adj b (Sum.inl u) := by
            rw [hb]
            simpa [H, TwoColorIncidenceGraph, Incident, hends] using
              (show Incident G u e ∧
                  (sigmaPrev e = some gamma ∨
                    sigmaPrev e = some choice.color) from
                ⟨by simp [Incident, hends], hecolor⟩)
          have hvAdj : H.Adj b (Sum.inl v) := by
            rw [hb]
            simpa [H, TwoColorIncidenceGraph, Incident, hends] using
              (show Incident G v e ∧
                  (sigmaPrev e = some gamma ∨
                    sigmaPrev e = some choice.color) from
                ⟨by simp [Incident, hends], hecolor⟩)
          exact False.elim
            (huv (Sum.inl.inj (hendLeaf huAdj hvAdj)))

theorem helper_hendMissing_3025.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (sigmaPrev : PartialEdgeColoring E k), gamma ≠ choice.color →
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G sigmaPrev gamma choice.color;
    ∀ (u : V), (H.neighborSet (Sum.inl u)).Subsingleton → gamma ∈ MissingColors G sigmaPrev u ∨
        choice.color ∈ MissingColors G sigmaPrev u := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ q gamma choice sigmaPrev
      hgammaDeltaNe H u hendLeaf
  by_cases hg : gamma ∈ MissingColors G sigmaPrev u
  · exact Or.inl hg
  · right
    have hgp : gamma ∈ PresentColors G sigmaPrev u := by
      simpa [MissingColors] using hg
    by_contra hd
    have hdp : choice.color ∈ PresentColors G sigmaPrev u := by
      simpa [MissingColors] using hd
    obtain ⟨eg, heg, hcg⟩ := by simpa [PresentColors] using hgp
    obtain ⟨ed, hed, hcd⟩ := by simpa [PresentColors] using hdp
    have hag : H.Adj (Sum.inl u) (Sum.inr eg) := by
      simpa [H, TwoColorIncidenceGraph] using
        (show Incident G u eg ∧
            (sigmaPrev eg = some gamma ∨
              sigmaPrev eg = some choice.color) from
          ⟨heg, Or.inl hcg⟩)
    have had : H.Adj (Sum.inl u) (Sum.inr ed) := by
      simpa [H, TwoColorIncidenceGraph] using
        (show Incident G u ed ∧
            (sigmaPrev ed = some gamma ∨
              sigmaPrev ed = some choice.color) from
          ⟨hed, Or.inr hcd⟩)
    have heq : eg = ed := Sum.inr.inj (hendLeaf hag had)
    subst ed
    exact hgammaDeltaNe (Option.some.inj (hcg.symm.trans hcd))

theorem helper_hnewExit_3069.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (sigmaPrev : PartialEdgeColoring E k), choice.vertex ∈ TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc) → (
    ∀ w ∈ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc), Sum.inl w ∈
        TwoColorComponent G sigmaPrev gamma choice.color (Sum.inl choice.vertex) ↔ w =
        choice.vertex) →
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G sigmaPrev gamma choice.color;
    ∀ (a b : V ⊕ E) (p_1 : (TwoColorIncidenceGraph G sigmaPrev gamma choice.color).Walk a b),
        p_1.IsPath → {x : V ⊕ E | x ∈ p_1.support} = TwoColorComponent G sigmaPrev gamma
        choice.color (Sum.inl choice.vertex) →
    ∀ (u : V) (p : H.Walk (Sum.inl choice.vertex) (Sum.inl u)), p.IsPath →
        {z : V ⊕ E | z ∈ p.support} = TwoColorComponent G sigmaPrev gamma choice.color (Sum.inl
        choice.vertex) → (0 : ℕ) < p.length → gamma ∈ MissingColors G sigmaPrev u ∨ choice.color ∈
        MissingColors G sigmaPrev u → u ∉ TreeSequenceVertexSet (ett.series.data.tree
        q.succ.castSucc) → p.length ≠ (1 : ℕ) → TreeExit (ett.series.data.tree q.succ.castSucc)
        sigmaPrev gamma choice.color choice.vertex := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ q gamma choice sigmaPrev
      hchoiceVertex hcomponentPrev H a b _ _ _ u p hp hps hpPos hendMissing huOutside hpNotOne
  refine ⟨u, p.reverse, ?_⟩
  unfold TreeExitPath
  refine ⟨hp.reverse, ?_, huOutside, hchoiceVertex,
    hendMissing, ?_⟩
  · simpa using (show 2 ≤ p.length by omega)
  · intro w hw
    constructor
    · intro hmem
      have hmem' : Sum.inl w ∈ p.support := by
        simpa [SimpleGraph.Walk.support_reverse] using hmem
      have hmemComponent : Sum.inl w ∈
          TwoColorComponent G sigmaPrev gamma choice.color
            (Sum.inl choice.vertex) := by
        rw [← hps]
        exact hmem'
      exact (hcomponentPrev w hw).mp hmemComponent
    · intro hwv
      subst w
      simp [SimpleGraph.Walk.support_reverse]

theorem helper_hpenultimateTree_3400.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [inst_2 : DecidableEq
        E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ closureTree : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds); q.succ = Fin.last ett.rounds →
    ∀ (gamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (sigmaPrev : PartialEdgeColoring E k),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G sigmaPrev gamma choice.color;
    ∀ (u : V) (_ : H.Walk (Sum.inl choice.vertex) (Sum.inl u)) (prefixInput : PartialEdgeColoring
        E k) (zeroPrefix : TashkinovSeries G k (0 : ℕ) e0 prefixInput),
    let zeroLast : Fin ((0 : ℕ) + (1 : ℕ)) := Fin.last (0 : ℕ);
    let newStored : Finset (Fin k) := (insert choice.color ({ gamma } : Finset (Fin k)) : Finset
        (Fin k));
    let newEdges : Finset E := ({ choice.edge } : Finset E);
    let newKind : Option TashkinovExtensionKind := some TashkinovExtensionKind.PE;
    let newVertex : Option V := some choice.vertex;
    let newOutside : Option V := some choice.otherEndpoint;
    let newDelta : Option (Fin k) := some choice.color;
    let newGamma : Option (Fin k) := some gamma;
    let appendedData : TashkinovSeriesData G k ((0 : ℕ) + (1 : ℕ)) e0 := TashkinovSeriesDataAppend
        zeroPrefix.data closureTree sigma newStored newEdges newKind newVertex newOutside newDelta
        newGamma; appendedData.tree zeroLast.succ.castSucc = ett.series.data.tree q.succ.castSucc
        →
    ∀ (extendedSeries : TashkinovSeries G k ((0 : ℕ) + (1 : ℕ)) e0 prefixInput),
        extendedSeries.data = TashkinovSeriesDataAppend zeroPrefix.data closureTree sigma
        newStored newEdges newKind newVertex newOutside newDelta newGamma →
    ∀ (hroundsEq : (0 : ℕ) + (1 : ℕ) = ett.rounds),
    let castSeries : {a b : ℕ} → a = b → TashkinovSeries G k a e0 prefixInput → TashkinovSeries G
        k b e0 prefixInput := fun {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 prefixInput)
        ↦ @Eq.ndrec Nat a (fun {b : Nat} ↦ @TashkinovSeries V E inst inst_1 inst_2 G k b e0
        prefixInput) S b h; (
    ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 prefixInput) (i : Fin (b + (2 : ℕ))),
        (castSeries h S).data.tree i = S.data.tree (Fin.cast (
    by omega
    ) i)) →
    let finalSeries : TashkinovSeries G k ett.rounds e0 prefixInput := castSeries hroundsEq
        extendedSeries;
    let rawTreeIndex : Fin (ett.rounds + (2 : ℕ)) → Fin (3 : ℕ) := fun (i : Fin (ett.rounds + (2 :
        ℕ))) ↦ Fin.cast (
    by omega
    ) i; rawTreeIndex (⟨ett.rounds,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))) = zeroLast.succ.castSucc → finalSeries.data.tree (⟨ett.rounds,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))) = ett.series.data.tree (Fin.last ett.rounds).castSucc := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma _ closureTree q hqSucc gamma
      choice sigmaPrev H u p prefixInput zeroPrefix zeroLast newStored newEdges newKind newVertex
      newOutside newDelta newGamma appendedData happendTree extendedSeries hextendedData
      hroundsEq castSeries castSeriesTree finalSeries rawTreeIndex hrawPenultimate
  calc
    finalSeries.data.tree
          (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2)) =
        extendedSeries.data.tree
          (rawTreeIndex
            (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2))) := by
          exact castSeriesTree hroundsEq extendedSeries _
    _ = appendedData.tree
          (rawTreeIndex
            (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2))) := by
          rw [hextendedData]
    _ = appendedData.tree zeroLast.succ.castSucc := by
          rw [hrawPenultimate]
    _ = ett.series.data.tree q.succ.castSucc := happendTree
    _ = ett.series.data.tree (Fin.last ett.rounds).castSucc := by
          rw [hqSucc]

theorem helper_hprefixFields_3431.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (_ _ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (sigmaPrev : PartialEdgeColoring E k),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G sigmaPrev gamma choice.color;
    ∀ (u : V) (_ : H.Walk (Sum.inl choice.vertex) (Sum.inl u)), ett.rounds = (1 : ℕ) →
    ∀ (prefixInput : PartialEdgeColoring E k) (zeroPrefix : TashkinovSeries G k (0 : ℕ) e0
        prefixInput),
    let zeroLast : Fin ((0 : ℕ) + (1 : ℕ)) := Fin.last (0 : ℕ); (0 : ℕ) + (1 : ℕ) = ett.rounds →
    ∀ (i : Fin (ett.rounds + (1 : ℕ))), (↑i : ℕ) < ett.rounds → zeroPrefix.data.stored zeroLast =
        ett.series.data.stored i ∧ zeroPrefix.data.connectingEdges zeroLast =
        ett.series.data.connectingEdges i ∧ zeroPrefix.data.kind zeroLast = ett.series.data.kind i
  := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ closureTree q gamma choice
      sigmaPrev H u p hroundOne prefixInput zeroPrefix zeroLast hroundsEq i hi
  have hiZero : i.val = 0 := by
    have hr := hroundOne
    omega
  have hiEq : i = 0 := Fin.ext hiZero
  subst i
  have hold := zeroPrefix.certified 0
  have hnew := ett.series.certified 0
  cases hold with
  | initial triple0 seedLength0 initialColoring0 initialStored0
      initialEdges0 initialKind0 initialVertex0 initialOutside0
      initialDelta0 initialGamma0 initialClosure0 =>
    cases hnew with
    | initial triple1 seedLength1 initialColoring1 initialStored1
        initialEdges1 initialKind1 initialVertex1 initialOutside1
        initialDelta1 initialGamma1 initialClosure1 =>
      exact ⟨by simpa [zeroLast] using
          initialStored0.trans initialStored1.symm,
        by simpa [zeroLast] using
          initialEdges0.trans initialEdges1.symm,
        by simpa [zeroLast] using
          initialKind0.trans initialKind1.symm⟩

theorem helper_hseriesDataAgree_3459.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [inst_2 : DecidableEq
        E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ closureTree : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds); q.succ = Fin.last ett.rounds →
    ∀ (gamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)),
        ett.series.data.stored q.succ = (insert choice.color ({ gamma } : Finset (Fin k)) : Finset
        (Fin k)) → ett.series.data.connectingEdges q.succ = ({ choice.edge } : Finset E) →
        ett.series.data.kind q.succ = some TashkinovExtensionKind.PE →
    ∀ (sigmaPrev : PartialEdgeColoring E k),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G sigmaPrev gamma choice.color;
    ∀ (a b : V ⊕ E) (p_1 : (TwoColorIncidenceGraph G sigmaPrev gamma choice.color).Walk a b),
        p_1.IsPath →
    ∀ (u : V) (p : H.Walk (Sum.inl choice.vertex) (Sum.inl u)), p.IsPath → ett.rounds = (1 : ℕ) →
    ∀ (prefixInput : PartialEdgeColoring E k) (zeroPrefix : TashkinovSeries G k (0 : ℕ) e0
        prefixInput),
    let zeroLast : Fin ((0 : ℕ) + (1 : ℕ)) := Fin.last (0 : ℕ);
    let newStored : Finset (Fin k) := (insert choice.color ({ gamma } : Finset (Fin k)) : Finset
        (Fin k));
    let newEdges : Finset E := ({ choice.edge } : Finset E);
    let newKind : Option TashkinovExtensionKind := some TashkinovExtensionKind.PE;
    let newVertex : Option V := some choice.vertex;
    let newOutside : Option V := some choice.otherEndpoint;
    let newDelta : Option (Fin k) := some choice.color;
    let newGamma : Option (Fin k) := some gamma;
    let appendedData : TashkinovSeriesData G k ((0 : ℕ) + (1 : ℕ)) e0 := TashkinovSeriesDataAppend
        zeroPrefix.data closureTree sigma newStored newEdges newKind newVertex newOutside newDelta
        newGamma; appendedData.stored (Fin.last (1 : ℕ)) = newStored →
        appendedData.connectingEdges (Fin.last (1 : ℕ)) = newEdges → appendedData.kind (Fin.last
        (1 : ℕ)) = newKind →
    ∀ (extendedSeries : TashkinovSeries G k ((0 : ℕ) + (1 : ℕ)) e0 prefixInput),
        extendedSeries.data = TashkinovSeriesDataAppend zeroPrefix.data closureTree sigma
        newStored newEdges newKind newVertex newOutside newDelta newGamma →
    ∀ (hroundsEq : (0 : ℕ) + (1 : ℕ) = ett.rounds),
    let castSeries : {a b : ℕ} → a = b → TashkinovSeries G k a e0 prefixInput → TashkinovSeries G
        k b e0 prefixInput := fun {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 prefixInput)
        ↦ @Eq.ndrec Nat a (fun {b : Nat} ↦ @TashkinovSeries V E inst inst_1 inst_2 G k b e0
        prefixInput) S b h; (
    ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 prefixInput) (i : Fin (b + (1 : ℕ))),
        (castSeries h S).data.stored i = S.data.stored (Fin.cast (
    by omega
    ) i)) → (
    ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 prefixInput) (i : Fin (b + (1 : ℕ))),
        (castSeries h S).data.connectingEdges i = S.data.connectingEdges (Fin.cast (
    by omega
    ) i)) → (
    ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 prefixInput) (i : Fin (b + (1 : ℕ))),
        (castSeries h S).data.kind i = S.data.kind (Fin.cast (
    by omega
    ) i)) →
    let finalSeries : TashkinovSeries G k ett.rounds e0 prefixInput := castSeries hroundsEq
        extendedSeries;
    let rawDataIndex : Fin (ett.rounds + (1 : ℕ)) → Fin (2 : ℕ) := fun (i : Fin (ett.rounds + (1 :
        ℕ))) ↦ Fin.cast (
    by omega
    ) i; rawDataIndex (Fin.last ett.rounds) = Fin.last (1 : ℕ) → (
    ∀ (i : Fin (ett.rounds + (1 : ℕ))), (↑i : ℕ) < ett.rounds → zeroPrefix.data.stored zeroLast =
        ett.series.data.stored i ∧ zeroPrefix.data.connectingEdges zeroLast =
        ett.series.data.connectingEdges i ∧ zeroPrefix.data.kind zeroLast = ett.series.data.kind
        i) →
    ∀ (i : Fin (ett.rounds + (1 : ℕ))), finalSeries.data.stored i = ett.series.data.stored i ∧
        finalSeries.data.connectingEdges i = ett.series.data.connectingEdges i ∧
        finalSeries.data.kind i = ett.series.data.kind i := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma _ closureTree q hqSucc gamma
      choice currentStored currentEdges currentKind sigmaPrev H a b _ _ u p hp hroundOne
      prefixInput zeroPrefix zeroLast newStored newEdges newKind newVertex newOutside newDelta
      newGamma appendedData happendLastStored happendLastEdges happendLastKind extendedSeries
      hextendedData hroundsEq castSeries castSeriesStored castSeriesEdges castSeriesKind
      finalSeries rawDataIndex hrawFinalData hprefixFields i
  by_cases hi : i.val < ett.rounds
  · have hraw : rawDataIndex i = zeroLast.castSucc := by
      apply Fin.ext
      have hiZero : i.val = 0 := by
        have hr := hroundOne
        omega
      exact hiZero
    have hp := hprefixFields i hi
    constructor
    · calc
        finalSeries.data.stored i =
            extendedSeries.data.stored (rawDataIndex i) := by
              exact castSeriesStored hroundsEq extendedSeries i
        _ = appendedData.stored (rawDataIndex i) := by
              rw [hextendedData]
        _ = zeroPrefix.data.stored zeroLast := by
              rw [hraw]
              simp only [appendedData, TashkinovSeriesDataAppend,
                Fin.lastCases_castSucc]
        _ = ett.series.data.stored i := hp.1
    · constructor
      · calc
          finalSeries.data.connectingEdges i =
              extendedSeries.data.connectingEdges
                (rawDataIndex i) := by
                exact castSeriesEdges hroundsEq extendedSeries i
          _ = appendedData.connectingEdges (rawDataIndex i) := by
                rw [hextendedData]
          _ = zeroPrefix.data.connectingEdges zeroLast := by
                rw [hraw]
                simp only [appendedData, TashkinovSeriesDataAppend,
                  Fin.lastCases_castSucc]
          _ = ett.series.data.connectingEdges i := hp.2.1
      · calc
          finalSeries.data.kind i =
              extendedSeries.data.kind (rawDataIndex i) := by
                exact castSeriesKind hroundsEq extendedSeries i
          _ = appendedData.kind (rawDataIndex i) := by
                rw [hextendedData]
          _ = zeroPrefix.data.kind zeroLast := by
                rw [hraw]
                simp only [appendedData, TashkinovSeriesDataAppend,
                  Fin.lastCases_castSucc]
          _ = ett.series.data.kind i := hp.2.2
  · have hilast : i = Fin.last ett.rounds := by
      apply Fin.ext
      have hibound := i.isLt
      simp
      omega
    subst i
    constructor
    · calc
        finalSeries.data.stored (Fin.last ett.rounds) =
            extendedSeries.data.stored
              (rawDataIndex (Fin.last ett.rounds)) := by
              exact castSeriesStored hroundsEq extendedSeries _
        _ = appendedData.stored
              (rawDataIndex (Fin.last ett.rounds)) := by
              rw [hextendedData]
        _ = appendedData.stored (Fin.last 1) := by rw [hrawFinalData]
        _ = newStored := happendLastStored
        _ = {choice.color, gamma} := rfl
        _ = ett.series.data.stored (Fin.last ett.rounds) := by
              rw [← hqSucc]
              exact currentStored.symm
    · constructor
      · calc
          finalSeries.data.connectingEdges (Fin.last ett.rounds) =
              extendedSeries.data.connectingEdges
                (rawDataIndex (Fin.last ett.rounds)) := by
                exact castSeriesEdges hroundsEq extendedSeries _
          _ = appendedData.connectingEdges
                (rawDataIndex (Fin.last ett.rounds)) := by
                rw [hextendedData]
          _ = appendedData.connectingEdges (Fin.last 1) := by
                rw [hrawFinalData]
          _ = newEdges := happendLastEdges
          _ = {choice.edge} := rfl
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
          _ = appendedData.kind (Fin.last 1) := by rw [hrawFinalData]
          _ = newKind := happendLastKind
          _ = some TashkinovExtensionKind.PE := rfl
          _ = ett.series.data.kind (Fin.last ett.rounds) := by
                rw [← hqSucc]
                exact currentKind.symm

theorem helper_hseriesTreeAgree_3561.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [inst_2 : DecidableEq
        E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ closureTree : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds); q.succ = Fin.last ett.rounds →
    ∀ (gamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (sigmaPrev : PartialEdgeColoring E k),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G sigmaPrev gamma choice.color;
    ∀ (u : V) (_ : H.Walk (Sum.inl choice.vertex) (Sum.inl u)), ett.rounds = (1 : ℕ) →
    ∀ (prefixInput : PartialEdgeColoring E k) (zeroPrefix : TashkinovSeries G k (0 : ℕ) e0
        prefixInput),
    let zeroLast : Fin ((0 : ℕ) + (1 : ℕ)) := Fin.last (0 : ℕ);
    let newStored : Finset (Fin k) := (insert choice.color ({ gamma } : Finset (Fin k)) : Finset
        (Fin k));
    let newEdges : Finset E := ({ choice.edge } : Finset E);
    let newKind : Option TashkinovExtensionKind := some TashkinovExtensionKind.PE;
    let newVertex : Option V := some choice.vertex;
    let newOutside : Option V := some choice.otherEndpoint;
    let newDelta : Option (Fin k) := some choice.color;
    let newGamma : Option (Fin k) := some gamma;
    let appendedData : TashkinovSeriesData G k ((0 : ℕ) + (1 : ℕ)) e0 := TashkinovSeriesDataAppend
        zeroPrefix.data closureTree sigma newStored newEdges newKind newVertex newOutside newDelta
        newGamma; appendedData.tree zeroLast.succ.castSucc = ett.series.data.tree q.succ.castSucc
        →
    ∀ (extendedSeries : TashkinovSeries G k ((0 : ℕ) + (1 : ℕ)) e0 prefixInput),
        extendedSeries.data = TashkinovSeriesDataAppend zeroPrefix.data closureTree sigma
        newStored newEdges newKind newVertex newOutside newDelta newGamma →
    ∀ (hroundsEq : (0 : ℕ) + (1 : ℕ) = ett.rounds),
    let castSeries : {a b : ℕ} → a = b → TashkinovSeries G k a e0 prefixInput → TashkinovSeries G
        k b e0 prefixInput := fun {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 prefixInput)
        ↦ @Eq.ndrec Nat a (fun {b : Nat} ↦ @TashkinovSeries V E inst inst_1 inst_2 G k b e0
        prefixInput) S b h; (
    ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 prefixInput) (i : Fin (b + (2 : ℕ))),
        (castSeries h S).data.tree i = S.data.tree (Fin.cast (
    by omega
    ) i)) →
    let finalSeries : TashkinovSeries G k ett.rounds e0 prefixInput := castSeries hroundsEq
        extendedSeries;
    let _ : Fin (ett.rounds + (2 : ℕ)) → Fin (3 : ℕ) := fun (i : Fin (ett.rounds + (2 : ℕ))) ↦
        Fin.cast (
    by omega
    ) i;
    ∀ (j : Fin ett.rounds), finalSeries.data.tree j.succ.castSucc = ett.series.data.tree
        j.succ.castSucc := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma _ closureTree q hqSucc gamma
      choice sigmaPrev H u p hroundOne prefixInput zeroPrefix zeroLast newStored newEdges newKind
      newVertex newOutside newDelta newGamma appendedData happendTree extendedSeries
      hextendedData hroundsEq castSeries castSeriesTree finalSeries rawTreeIndex j
  have hj : j.succ = Fin.last ett.rounds := by
    apply Fin.ext
    have hjbound := j.isLt
    simp
    have hr := hroundOne
    omega
  have htreeIndex : rawTreeIndex j.succ.castSucc =
      zeroLast.succ.castSucc := by
    apply Fin.ext
    simp [rawTreeIndex, zeroLast]
  calc
    finalSeries.data.tree j.succ.castSucc =
        extendedSeries.data.tree (rawTreeIndex j.succ.castSucc) := by
          exact castSeriesTree hroundsEq extendedSeries _
    _ = appendedData.tree (rawTreeIndex j.succ.castSucc) := by
          rw [hextendedData]
    _ = appendedData.tree zeroLast.succ.castSucc := by rw [htreeIndex]
    _ = ett.series.data.tree q.succ.castSucc := happendTree
    _ = ett.series.data.tree j.succ.castSucc := by
          rw [hj, hqSucc]

theorem helper_hseriesColorProperties_3585.{u_1, u_2} :
    helperHseriesColorProperties3585Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma hsigmaProper hsigmaOne _
      closureTree q gamma choice sigmaPrev hsigmaPrevProper hsigmaPrevOne H u p hroundOne
      prefixInput zeroPrefix zeroLast newStored newEdges newKind newVertex newOutside newDelta
      newGamma appendedData happendColor extendedSeries hextendedData hroundsEq castSeries
      castSeriesColoring finalSeries rawDataIndex hfinalColor i
  by_cases hi : i.val < ett.rounds
  · have hraw : rawDataIndex i = zeroLast.castSucc := by
      apply Fin.ext
      have hiZero : i.val = 0 := by
        have hr := hroundOne
        omega
      exact hiZero
    have hcolor : finalSeries.data.coloring i = sigmaPrev := by
      calc
        finalSeries.data.coloring i =
            extendedSeries.data.coloring (rawDataIndex i) := by
              exact castSeriesColoring hroundsEq extendedSeries i
        _ = appendedData.coloring (rawDataIndex i) := by
              rw [hextendedData]
        _ = appendedData.coloring zeroLast.castSucc := by rw [hraw]
        _ = sigmaPrev := happendColor
    rw [hcolor]
    exact ⟨hsigmaPrevProper, hsigmaPrevOne⟩
  · have hilast : i = Fin.last ett.rounds := by
      apply Fin.ext
      have hibound := i.isLt
      simp
      omega
    subst i
    rw [hfinalColor]
    exact ⟨hsigmaProper, hsigmaOne⟩

theorem helper_branch_3453.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
    (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating),
  ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.SE ∨
      ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE →
  ∀ (sigma : PartialEdgeColoring E k) (Tstar : TreeSequence G e0) (i : Fin ett.rounds),
  ett.series.data.kind i.succ = some TashkinovExtensionKind.RE →
  Fin.last ett.rounds = i.succ →
  Nonempty (CorrespondingExtendedTashkinovTree G k e0 ett sigma Tstar) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hterminal sigma _ i currentKind htarget
  have hbad : some TashkinovExtensionKind.RE =
      some TashkinovExtensionKind.SE ∨
      some TashkinovExtensionKind.RE =
        some TashkinovExtensionKind.PE := by
    simp [htarget, currentKind] at hterminal
  rcases hbad with hbad | hbad <;> cases hbad

theorem helper_hi_3469.{u_1, u_2} :
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
  have hv : ett.rounds = i.val + 1 := by
    simpa using congrArg Fin.val htarget
  change i.val = ett.rounds - 1
  omega

theorem helper_hdeltaCurrentControl_3499.{u_1, u_2} :
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
    ∀ (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)),
        ett.series.data.stored q.succ = ({ choice.color } : Finset (Fin k)) → choice.color ∈
        TreeMissingColors (ett.series.data.coloring q.succ) (ett.series.data.tree q.succ.castSucc)
        ∪ TashkinovStoredColors ett.series.data q.succ := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ q choice currentStored
  by_cases hm : choice.color ∈
      TreeMissingColors (ett.series.data.coloring q.succ)
        (ett.series.data.tree q.succ.castSucc)
  · exact Finset.mem_union_left _ hm
  · apply Finset.mem_union_right
    unfold TashkinovStoredColors
    have hqpos : q.succ.val ≠ 0 := by simp
    rw [ite_eq_right hqpos, Finset.mem_sdiff]
    refine ⟨?_, hm⟩
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    refine ⟨q.succ, ?_⟩
    rw [ite_eq_left le_rfl]
    simp [currentStored]

theorem helper_henlargedControl_3516.{u_1, u_2} :
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
    ∀ (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)),
        ett.series.data.coloring q.succ = choice.selected → TreeMissingColors
        (ett.series.data.coloring q.castSucc) (ett.series.data.tree q.succ.castSucc) ∪
        TashkinovStoredColors ett.series.data q.castSucc ⊆ TreeMissingColors
        (ett.series.data.coloring q.succ) (ett.series.data.tree q.succ.castSucc) ∪
        TashkinovStoredColors ett.series.data q.succ → choice.color ∈ TreeMissingColors
        (ett.series.data.coloring q.succ) (ett.series.data.tree q.succ.castSucc) ∪
        TashkinovStoredColors ett.series.data q.succ → TreeMissingColors choice.selected
        (ett.series.data.tree q.succ.castSucc) ∪ (insert choice.color (TashkinovStoredColors
        ett.series.data q.castSucc) : Finset (Fin k)) ⊆ TreeMissingColors
        (ett.series.data.coloring q.succ) (ett.series.data.tree q.succ.castSucc) ∪
        TashkinovStoredColors ett.series.data q.succ := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ q choice currentColoring
      hpreviousControl hdeltaCurrentControl c hc
  rcases Finset.mem_union.mp hc with hc | hc
  · apply Finset.mem_union_left
    simpa [currentColoring] using hc
  · rw [Finset.mem_insert] at hc
    rcases hc with rfl | hc
    · exact hdeltaCurrentControl
    · exact hpreviousControl (Finset.mem_union_right _ hc)

theorem helper_hsigmaPrevEnlarged_3532.{u_1, u_2} :
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
    ⟩ : Fin ett.rounds); StableColoring (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.succ) (ett.series.data.coloring q.succ) sigma →
    ∀ (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)),
        ett.series.data.coloring q.succ = choice.selected →
    ∀ (sigmaPrev : PartialEdgeColoring E k), sigmaPrev = sigma → TreeMissingColors choice.selected
        (ett.series.data.tree q.succ.castSucc) ∪ (insert choice.color (TashkinovStoredColors
        ett.series.data q.castSucc) : Finset (Fin k)) ⊆ TreeMissingColors
        (ett.series.data.coloring q.succ) (ett.series.data.tree q.succ.castSucc) ∪
        TashkinovStoredColors ett.series.data q.succ → StableColoring (ett.series.data.tree
        q.succ.castSucc) (insert choice.color (TashkinovStoredColors ett.series.data q.castSucc) :
        Finset (Fin k)) choice.selected sigmaPrev := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma _ q hsigmaStableQ choice
      currentColoring sigmaPrev hsigmaPrevSigma henlargedControl
  constructor
  · intro f hf hcolor
    rcases hcolor with ⟨c, hc, hfc⟩
    have hcopy := hsigmaStableQ.1 f hf
      ⟨c, henlargedControl hc, by simpa [currentColoring] using hfc⟩
    simpa [currentColoring, hsigmaPrevSigma] using hcopy
  · intro v hv
    simpa [currentColoring, hsigmaPrevSigma] using hsigmaStableQ.2 v hv

theorem helper_hchoiceDefective_3555.{u_1, u_2} :
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
    ∀ (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (sigmaPrev : PartialEdgeColoring E k), BoundaryColorEdges G choice.selected
        (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) choice.color =
        BoundaryColorEdges G sigmaPrev (TreeSequenceVertexSet (ett.series.data.tree
        q.succ.castSucc)) choice.color → DefectiveColor G sigmaPrev (TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc)) choice.color := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ q choice sigmaPrev hdeltaBoundary
  obtain ⟨oldColor, holdDefective, holdEdge⟩ := choice.edgeDefective
  have holdColor : oldColor = choice.color := by
    have holdEdgeColor := (Finset.mem_filter.mp holdEdge).2
    exact Option.some.inj (holdEdgeColor.symm.trans choice.edgeColor)
  subst oldColor
  unfold DefectiveColor
  rw [← hdeltaBoundary]
  exact holdDefective

theorem helper_hchoiceEdgeNew_3566.{u_1, u_2} :
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
    ∀ (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (sigmaPrev : PartialEdgeColoring E k), BoundaryColorEdges G choice.selected
        (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) choice.color =
        BoundaryColorEdges G sigmaPrev (TreeSequenceVertexSet (ett.series.data.tree
        q.succ.castSucc)) choice.color → choice.edge ∈ BoundaryColorEdges G sigmaPrev
        (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) choice.color := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ q choice sigmaPrev hdeltaBoundary
  rw [← hdeltaBoundary]
  obtain ⟨oldColor, holdDefective, holdEdge⟩ := choice.edgeDefective
  have holdColor : oldColor = choice.color := by
    have holdEdgeColor := (Finset.mem_filter.mp holdEdge).2
    exact Option.some.inj (holdEdgeColor.symm.trans choice.edgeColor)
  simpa [holdColor] using holdEdge

theorem helper_hnotStrongPrev_3595.{u_1, u_2} :
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
    ∀ (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (sigmaPrev : PartialEdgeColoring E k), DefectiveColor G sigmaPrev (TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc)) choice.color → ¬ColoredVertexSetStronglyClosed G
        sigmaPrev (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ q choice sigmaPrev
      hchoiceDefective hstrong
  have hone : 1 < (BoundaryColorEdges G sigmaPrev
      (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc))
      choice.color).card := by
    have htwo : 2 ≤ (BoundaryColorEdges G sigmaPrev
        (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc))
        choice.color).card := hchoiceDefective
    omega
  obtain ⟨f, hf, g, hg, hfg⟩ := Finset.one_lt_card.mp hone
  have hfBoundary := (Finset.mem_filter.mp hf).1
  have hgBoundary := (Finset.mem_filter.mp hg).1
  have hfColor := (Finset.mem_filter.mp hf).2
  have hgColor := (Finset.mem_filter.mp hg).2
  exact (hstrong.2 hfBoundary hgBoundary hfg hfColor) hgColor

theorem helper_hnewAlternative_3611.{u_1, u_2} :
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
    ∀ (previousProper : IsProperEdgeColoring G (ett.series.data.coloring q.castSucc))
        (previousOneUncolored : IsOneEdgeUncolored (ett.series.data.coloring q.castSucc) e0)
        (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)),
        (
    ∀ (pi : PartialEdgeColoring E k), IsProperEdgeColoring G pi → IsOneEdgeUncolored pi e0 →
        StableColoring (ett.series.data.tree q.succ.castSucc) (insert choice.color
        (TashkinovStoredColors ett.series.data q.castSucc) : Finset (Fin k)) choice.selected pi →
        Disjoint (MissingColors G pi choice.otherEndpoint) (TreeMissingColors pi
        (ett.series.data.tree q.succ.castSucc))) →
    ∀ (sigmaPrev : PartialEdgeColoring E k) (hsigmaPrevProper : IsProperEdgeColoring G sigmaPrev)
        (hsigmaPrevOne : IsOneEdgeUncolored sigmaPrev e0) (hsigmaPrevStableQ : StableColoring
        (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors ett.series.data q.castSucc)
        (ett.series.data.coloring q.castSucc) sigmaPrev), StableColoring (ett.series.data.tree
        q.succ.castSucc) (insert choice.color (TashkinovStoredColors ett.series.data q.castSucc) :
        Finset (Fin k)) choice.selected sigmaPrev →
    ∀ (hchoiceDefective : DefectiveColor G sigmaPrev (TreeSequenceVertexSet (ett.series.data.tree
        q.succ.castSucc)) choice.color) (hchoiceEdgeNew : choice.edge ∈ BoundaryColorEdges G
        sigmaPrev (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) choice.color)
        (hsigmaPrevSelf : StableColoring (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) sigmaPrev sigmaPrev),
    let newChoice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) sigmaPrev := helperNewChoice2409 G k e0
        input T generating ett hpositive previousProper previousOneUncolored choice sigmaPrev
        hsigmaPrevProper hsigmaPrevOne hsigmaPrevStableQ hchoiceDefective hchoiceEdgeNew
        hsigmaPrevSelf;
    ∀ (pi : PartialEdgeColoring E k), IsProperEdgeColoring G pi → IsOneEdgeUncolored pi e0 →
        StableColoring (ett.series.data.tree q.succ.castSucc) (insert newChoice.color
        (TashkinovStoredColors ett.series.data q.castSucc) : Finset (Fin k)) newChoice.selected pi
        → Disjoint (MissingColors G pi newChoice.otherEndpoint) (TreeMissingColors pi
        (ett.series.data.tree q.succ.castSucc)) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ q previousProper
      previousOneUncolored choice seriesAlternative sigmaPrev hsigmaPrevProper hsigmaPrevOne
      hsigmaPrevStableQ hsigmaPrevEnlarged hchoiceDefective hchoiceEdgeNew hsigmaPrevSelf
      newChoice pi hpiProper hpiOne hpiStable
  have hpiOld : StableColoring
      (ett.series.data.tree q.succ.castSucc)
      (insert choice.color
        (TashkinovStoredColors ett.series.data q.castSucc))
      choice.selected pi := by
    exact (sc2 G e0 (ett.series.data.tree q.succ.castSucc)
      (insert choice.color
        (TashkinovStoredColors ett.series.data q.castSucc))).trans
        (x := ⟨choice.selected,
          ⟨choice.selectedProper, choice.selectedOneUncolored⟩⟩)
        (y := ⟨sigmaPrev, ⟨hsigmaPrevProper, hsigmaPrevOne⟩⟩)
        (z := ⟨pi, ⟨hpiProper, hpiOne⟩⟩)
        hsigmaPrevEnlarged (by simpa [newChoice] using hpiStable)
  simpa [newChoice] using
    seriesAlternative pi hpiProper hpiOne hpiOld

theorem helper_happendTree_3707.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ closureTree : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
        have := GoldbergSeymour.TreeSequence.positive T
        omega
    ⟩ : Fin ett.rounds); q.succ = Fin.last ett.rounds →
    ∀ (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (prefixInput : PartialEdgeColoring E k) (zeroPrefix : TashkinovSeries G k (0 : ℕ) e0
        prefixInput), zeroPrefix.data.tree (Fin.last (1 : ℕ)) = ett.series.data.tree (Fin.last
        ett.rounds).castSucc →
    let zeroLast : Fin ((0 : ℕ) + (1 : ℕ)) := Fin.last (0 : ℕ);
    let newStored : Finset (Fin k) := ({ choice.color } : Finset (Fin k));
    let newEdges : Finset E := ({ choice.edge } : Finset E);
    let newKind : Option TashkinovExtensionKind := some TashkinovExtensionKind.SE;
    let newVertex : Option V := some choice.vertex;
    let newOutside : Option V := some choice.otherEndpoint;
    let newDelta : Option (Fin k) := some choice.color;
    let newGamma : Option (Fin k) := none;
    let appendedData : TashkinovSeriesData G k ((0 : ℕ) + (1 : ℕ)) e0 := TashkinovSeriesDataAppend
        zeroPrefix.data closureTree sigma newStored newEdges newKind newVertex newOutside newDelta
        newGamma; appendedData.tree zeroLast.succ.castSucc = ett.series.data.tree q.succ.castSucc
  := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma _ closureTree q hqSucc choice
      prefixInput zeroPrefix hzeroTree zeroLast newStored newEdges newKind newVertex newOutside
      newDelta newGamma appendedData
  calc
    appendedData.tree zeroLast.succ.castSucc =
        zeroPrefix.data.tree (Fin.last 1) := by
          simp only [appendedData, TashkinovSeriesDataAppend,
            Fin.lastCases_castSucc]
          congr 1
    _ = ett.series.data.tree (Fin.last ett.rounds).castSucc := hzeroTree
    _ = ett.series.data.tree q.succ.castSucc := by rw [hqSucc]

theorem helper_happendColor_3717.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ closureTree : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
        have := GoldbergSeymour.TreeSequence.positive T
        omega
    ⟩ : Fin ett.rounds);
    ∀ (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (sigmaPrev prefixInput : PartialEdgeColoring E k) (zeroPrefix : TashkinovSeries G k (0 :
        ℕ) e0 prefixInput), zeroPrefix.data.coloring (Fin.last (0 : ℕ)) = sigmaPrev →
    let zeroLast : Fin ((0 : ℕ) + (1 : ℕ)) := Fin.last (0 : ℕ);
    let newStored : Finset (Fin k) := ({ choice.color } : Finset (Fin k));
    let newEdges : Finset E := ({ choice.edge } : Finset E);
    let newKind : Option TashkinovExtensionKind := some TashkinovExtensionKind.SE;
    let newVertex : Option V := some choice.vertex;
    let newOutside : Option V := some choice.otherEndpoint;
    let newDelta : Option (Fin k) := some choice.color;
    let newGamma : Option (Fin k) := none;
    let appendedData : TashkinovSeriesData G k ((0 : ℕ) + (1 : ℕ)) e0 := TashkinovSeriesDataAppend
        zeroPrefix.data closureTree sigma newStored newEdges newKind newVertex newOutside newDelta
        newGamma; appendedData.coloring zeroLast.castSucc = sigmaPrev := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma _ closureTree q choice
      sigmaPrev prefixInput zeroPrefix hzeroColor zeroLast newStored newEdges newKind newVertex
      newOutside newDelta newGamma appendedData
  calc
    appendedData.coloring zeroLast.castSucc =
        zeroPrefix.data.coloring (Fin.last 0) := by
          simp only [appendedData, TashkinovSeriesDataAppend,
            Fin.lastCases_castSucc]
          congr 1
    _ = sigmaPrev := hzeroColor

theorem helper_hnoRevisitingZero_3741.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ closureTree : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
        have := GoldbergSeymour.TreeSequence.positive T
        omega
    ⟩ : Fin ett.rounds);
    ∀ (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (prefixInput : PartialEdgeColoring E k) (zeroPrefix : TashkinovSeries G k (0 : ℕ) e0
        prefixInput),
    let zeroLast : Fin ((0 : ℕ) + (1 : ℕ)) := Fin.last (0 : ℕ);
    let newStored : Finset (Fin k) := ({ choice.color } : Finset (Fin k));
    let newEdges : Finset E := ({ choice.edge } : Finset E);
    let newKind : Option TashkinovExtensionKind := some TashkinovExtensionKind.SE;
    let newVertex : Option V := some choice.vertex;
    let newOutside : Option V := some choice.otherEndpoint;
    let newDelta : Option (Fin k) := some choice.color;
    let newGamma : Option (Fin k) := none;
    let appendedData : TashkinovSeriesData G k ((0 : ℕ) + (1 : ℕ)) e0 := TashkinovSeriesDataAppend
        zeroPrefix.data closureTree sigma newStored newEdges newKind newVertex newOutside newDelta
        newGamma; ¬Nonempty (RevisitingExtensionCertificate appendedData zeroLast.castSucc) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma _ closureTree q choice
      prefixInput zeroPrefix zeroLast newStored newEdges newKind newVertex newOutside newDelta
      newGamma appendedData
  rintro ⟨cert⟩
  obtain ⟨oldCert, -, -, -, -, -⟩ :=
    (RevisitingExtensionCertificateAppend zeroPrefix.data
      closureTree sigma newStored newEdges newKind newVertex
      newOutside newDelta newGamma zeroLast).1 cert
  have hle := oldCert.earlierAtMost
  have hpos := oldCert.earlierPositive
  simp [zeroLast] at hle
  omega

theorem helper_hnewAlternativeZero_3753.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (Tstar closureTree : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
        have := GoldbergSeymour.TreeSequence.positive T
        omega
    ⟩ : Fin ett.rounds);
    ∀ (previousProper : IsProperEdgeColoring G (ett.series.data.coloring q.castSucc))
        (previousOneUncolored : IsOneEdgeUncolored (ett.series.data.coloring q.castSucc) e0)
        (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (sigmaPrev : PartialEdgeColoring E k) (hsigmaPrevProper : IsProperEdgeColoring G
        sigmaPrev) (hsigmaPrevOne : IsOneEdgeUncolored sigmaPrev e0) (hsigmaPrevStableQ :
        StableColoring (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors
        ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc) sigmaPrev)
        (hchoiceDefective : DefectiveColor G sigmaPrev (TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc)) choice.color) (hchoiceEdgeNew : choice.edge ∈
        BoundaryColorEdges G sigmaPrev (TreeSequenceVertexSet (ett.series.data.tree
        q.succ.castSucc)) choice.color) (hsigmaPrevSelf : StableColoring (ett.series.data.tree
        q.succ.castSucc) (TashkinovStoredColors ett.series.data q.castSucc) sigmaPrev sigmaPrev),
    let newChoice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) sigmaPrev := helperNewChoice2409 G k e0
        input T generating ett hpositive previousProper previousOneUncolored choice sigmaPrev
        hsigmaPrevProper hsigmaPrevOne hsigmaPrevStableQ hchoiceDefective hchoiceEdgeNew
        hsigmaPrevSelf; (
    ∀ (pi : PartialEdgeColoring E k), IsProperEdgeColoring G pi → IsOneEdgeUncolored pi e0 →
        StableColoring (ett.series.data.tree q.succ.castSucc) (insert newChoice.color
        (TashkinovStoredColors ett.series.data q.castSucc) : Finset (Fin k)) newChoice.selected pi
        → Disjoint (MissingColors G pi newChoice.otherEndpoint) (TreeMissingColors pi
        (ett.series.data.tree q.succ.castSucc))) →
    ∀ (prefixInput : PartialEdgeColoring E k) (zeroPrefix : TashkinovSeries G k (0 : ℕ) e0
        prefixInput),
    let zeroLast : Fin ((0 : ℕ) + (1 : ℕ)) := Fin.last (0 : ℕ);
    let newStored : Finset (Fin k) := ({ choice.color } : Finset (Fin k));
    let newEdges : Finset E := ({ choice.edge } : Finset E);
    let newKind : Option TashkinovExtensionKind := some TashkinovExtensionKind.SE;
    let newVertex : Option V := some choice.vertex;
    let newOutside : Option V := some choice.otherEndpoint;
    let newDelta : Option (Fin k) := some choice.color;
    let newGamma : Option (Fin k) := none;
    let appendedData : TashkinovSeriesData G k ((0 : ℕ) + (1 : ℕ)) e0 := TashkinovSeriesDataAppend
        zeroPrefix.data closureTree sigma newStored newEdges newKind newVertex newOutside newDelta
        newGamma;
    ∀ (happendTree : appendedData.tree zeroLast.succ.castSucc = ett.series.data.tree
        q.succ.castSucc) (happendColor : appendedData.coloring zeroLast.castSucc = sigmaPrev)
        (happendStored : TashkinovStoredColors appendedData zeroLast.castSucc =
        TashkinovStoredColors ett.series.data q.castSucc),
    let appendedChoice : MaximumDefectiveChoice G e0 (appendedData.tree zeroLast.succ.castSucc)
        (TashkinovStoredColors appendedData zeroLast.castSucc) (appendedData.coloring
        zeroLast.castSucc) := helperAppendedChoice2713 G k e0 input T generating ett hpositive
        sigma closureTree previousProper previousOneUncolored choice sigmaPrev hsigmaPrevProper
        hsigmaPrevOne hsigmaPrevStableQ hchoiceDefective hchoiceEdgeNew hsigmaPrevSelf prefixInput
        zeroPrefix happendTree happendColor happendStored;
    ∀ (pi : PartialEdgeColoring E k), IsProperEdgeColoring G pi → IsOneEdgeUncolored pi e0 →
        StableColoring (appendedData.tree zeroLast.succ.castSucc) (insert appendedChoice.color
        (TashkinovStoredColors appendedData zeroLast.castSucc) : Finset (Fin k))
        appendedChoice.selected pi → Disjoint (MissingColors G pi appendedChoice.otherEndpoint)
        (TreeMissingColors pi (appendedData.tree zeroLast.succ.castSucc)) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma _ closureTree q
      previousProper previousOneUncolored choice sigmaPrev hsigmaPrevProper hsigmaPrevOne
      hsigmaPrevStableQ hchoiceDefective hchoiceEdgeNew hsigmaPrevSelf newChoice hnewAlternative
      prefixInput zeroPrefix zeroLast newStored newEdges newKind newVertex newOutside newDelta
      newGamma appendedData happendTree happendColor happendStored appendedChoice pi hpiProper
      hpiOne hpiStable
  have hpiStable' := hpiStable
  change StableColoring (appendedData.tree zeroLast.succ.castSucc)
    (insert choice.color
      (TashkinovStoredColors appendedData zeroLast.castSucc))
    sigmaPrev pi at hpiStable'
  rw [happendTree, happendStored] at hpiStable'
  have hresult := hnewAlternative pi hpiProper hpiOne
    (by simpa [appendedChoice, newChoice] using hpiStable')
  change Disjoint (MissingColors G pi choice.otherEndpoint)
    (TreeMissingColors pi
      (appendedData.tree zeroLast.succ.castSucc))
  rw [happendTree]
  simpa [appendedChoice, newChoice] using hresult

theorem helper_lastStep_3779.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (Tstar closureTree : TreeSequence G e0), TreeSequenceInitialSegment
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) closureTree →
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
        have := GoldbergSeymour.TreeSequence.positive T
        omega
    ⟩ : Fin ett.rounds); q.succ = Fin.last ett.rounds →
    ∀ (_ : TreeSequence G e0) (previousProper : IsProperEdgeColoring G (ett.series.data.coloring
        q.castSucc)) (previousOneUncolored : IsOneEdgeUncolored (ett.series.data.coloring
        q.castSucc) e0) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree
        q.succ.castSucc) (TashkinovStoredColors ett.series.data q.castSucc)
        (ett.series.data.coloring q.castSucc)) (sigmaPrev : PartialEdgeColoring E k)
        (hsigmaPrevProper : IsProperEdgeColoring G sigmaPrev) (hsigmaPrevOne : IsOneEdgeUncolored
        sigmaPrev e0) (hsigmaPrevStableQ : StableColoring (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)
        sigmaPrev), sigmaPrev = sigma →
    ∀ (hchoiceDefective : DefectiveColor G sigmaPrev (TreeSequenceVertexSet (ett.series.data.tree
        q.succ.castSucc)) choice.color) (hchoiceEdgeNew : choice.edge ∈ BoundaryColorEdges G
        sigmaPrev (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) choice.color)
        (hsigmaPrevSelf : StableColoring (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) sigmaPrev sigmaPrev),
        ColoredVertexSetClosed G sigmaPrev (TreeSequenceVertexSet (ett.series.data.tree
        q.succ.castSucc)) → ¬ColoredVertexSetStronglyClosed G sigmaPrev (TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc)) →
    ∀ (prefixInput : PartialEdgeColoring E k) (zeroPrefix : TashkinovSeries G k (0 : ℕ) e0
        prefixInput) (fstar : E) (seed : TreeSequence G e0), TreeSequenceAdjoinEdge
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) fstar seed → fstar = choice.edge →
        TashkinovClosure sigma seed closureTree →
    let zeroLast : Fin ((0 : ℕ) + (1 : ℕ)) := Fin.last (0 : ℕ);
    let newStored : Finset (Fin k) := ({ choice.color } : Finset (Fin k));
    let newEdges : Finset E := ({ choice.edge } : Finset E);
    let newKind : Option TashkinovExtensionKind := some TashkinovExtensionKind.SE;
    let newVertex : Option V := some choice.vertex;
    let newOutside : Option V := some choice.otherEndpoint;
    let newDelta : Option (Fin k) := some choice.color;
    let newGamma : Option (Fin k) := none;
    let appendedData : TashkinovSeriesData G k ((0 : ℕ) + (1 : ℕ)) e0 := TashkinovSeriesDataAppend
        zeroPrefix.data closureTree sigma newStored newEdges newKind newVertex newOutside newDelta
        newGamma; appendedData.tree (Fin.last (2 : ℕ)) = closureTree → appendedData.coloring
        (Fin.last (1 : ℕ)) = sigma → appendedData.stored (Fin.last (1 : ℕ)) = newStored →
        appendedData.connectingEdges (Fin.last (1 : ℕ)) = newEdges → appendedData.kind (Fin.last
        (1 : ℕ)) = newKind → appendedData.chosenVertex (Fin.last (1 : ℕ)) = newVertex →
        appendedData.outsideVertex (Fin.last (1 : ℕ)) = newOutside → appendedData.delta (Fin.last
        (1 : ℕ)) = newDelta → appendedData.gamma (Fin.last (1 : ℕ)) = newGamma →
    ∀ (happendTree : appendedData.tree zeroLast.succ.castSucc = ett.series.data.tree
        q.succ.castSucc) (happendColor : appendedData.coloring zeroLast.castSucc = sigmaPrev)
        (happendStored : TashkinovStoredColors appendedData zeroLast.castSucc =
        TashkinovStoredColors ett.series.data q.castSucc),
    let appendedChoice : MaximumDefectiveChoice G e0 (appendedData.tree zeroLast.succ.castSucc)
        (TashkinovStoredColors appendedData zeroLast.castSucc) (appendedData.coloring
        zeroLast.castSucc) := helperAppendedChoice2713 G k e0 input T generating ett hpositive
        sigma closureTree previousProper previousOneUncolored choice sigmaPrev hsigmaPrevProper
        hsigmaPrevOne hsigmaPrevStableQ hchoiceDefective hchoiceEdgeNew hsigmaPrevSelf prefixInput
        zeroPrefix happendTree happendColor happendStored; ¬Nonempty
        (RevisitingExtensionCertificate appendedData zeroLast.castSucc) → (
    ∀ (pi : PartialEdgeColoring E k), IsProperEdgeColoring G pi → IsOneEdgeUncolored pi e0 →
        StableColoring (appendedData.tree zeroLast.succ.castSucc) (insert appendedChoice.color
        (TashkinovStoredColors appendedData zeroLast.castSucc) : Finset (Fin k))
        appendedChoice.selected pi → Disjoint (MissingColors G pi appendedChoice.otherEndpoint)
        (TreeMissingColors pi (appendedData.tree zeroLast.succ.castSucc))) → (ett.series.data.tree
        (Fin.last ett.rounds).castSucc).length < closureTree.length → TashkinovSeriesStep G k (1 :
        ℕ) e0 prefixInput appendedData (Fin.last (1 : ℕ)) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma _ closureTree hTnClosure q
      hqSucc adjoined previousProper previousOneUncolored choice sigmaPrev hsigmaPrevProper
      hsigmaPrevOne hsigmaPrevStableQ hsigmaPrevSigma hchoiceDefective hchoiceEdgeNew
      hsigmaPrevSelf hclosedPrev hnotStrongPrev prefixInput zeroPrefix fstar seed hadjoin hfstar
      hseedClosure zeroLast newStored newEdges newKind newVertex newOutside newDelta newGamma
      appendedData happendLastTree happendLastColor happendLastStored happendLastEdges
      happendLastKind happendLastVertex happendLastOutside happendLastDelta happendLastGamma
      happendTree happendColor happendStored appendedChoice hnoRevisitingZero hnewAlternativeZero
      hstrictClosure
  have hlast : zeroLast.succ = Fin.last 1 := by
    apply Fin.ext
    rfl
  rw [← hlast]
  apply TashkinovSeriesStep.SE (i := zeroLast)
    (choice := appendedChoice) (adjoined := seed)
  · rw [happendColor]; exact hsigmaPrevProper
  · rw [happendColor]; exact hsigmaPrevOne
  · rw [happendColor, happendTree]; exact hclosedPrev
  · rw [happendColor, happendTree]; exact hnotStrongPrev
  · exact hnoRevisitingZero
  · exact hnewAlternativeZero
  · exact happendLastColor.trans hsigmaPrevSigma.symm
  · exact happendLastStored.trans (by rfl)
  · exact happendLastEdges.trans (by rfl)
  · exact happendLastKind.trans (by rfl)
  · exact happendLastVertex.trans (by rfl)
  · exact happendLastOutside.trans (by rfl)
  · exact happendLastDelta.trans (by rfl)
  · exact happendLastGamma.trans (by rfl)
  · change TreeSequenceAdjoinEdge
      (appendedData.tree zeroLast.succ.castSucc) choice.edge seed
    rw [happendTree]
    simpa [hqSucc, hfstar] using hadjoin
  · change TashkinovClosure (appendedData.coloring (Fin.last 1))
      seed (appendedData.tree (Fin.last 2))
    rw [happendLastColor, happendLastTree]
    exact hseedClosure
  · change TreeSequenceInitialSegment
      (appendedData.tree zeroLast.succ.castSucc)
      (appendedData.tree (Fin.last 2))
    rw [happendTree]
    rw [happendLastTree]
    simpa [hqSucc] using hTnClosure
  · change (appendedData.tree zeroLast.succ.castSucc).length <
      (appendedData.tree (Fin.last 2)).length
    rw [happendTree]
    rw [happendLastTree]
    simpa [hqSucc] using hstrictClosure

theorem helper_hfinalTree_3891.{u_1, u_2} :
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
    ∀ (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (prefixInput : PartialEdgeColoring E k) (zeroPrefix : TashkinovSeries G k (0 : ℕ) e0
        prefixInput),
    let newStored : Finset (Fin k) := ({ choice.color } : Finset (Fin k));
    let newEdges : Finset E := ({ choice.edge } : Finset E);
    let newKind : Option TashkinovExtensionKind := some TashkinovExtensionKind.SE;
    let newVertex : Option V := some choice.vertex;
    let newOutside : Option V := some choice.otherEndpoint;
    let newDelta : Option (Fin k) := some choice.color;
    let newGamma : Option (Fin k) := none;
    let appendedData : TashkinovSeriesData G k ((0 : ℕ) + (1 : ℕ)) e0 := TashkinovSeriesDataAppend
        zeroPrefix.data closureTree sigma newStored newEdges newKind newVertex newOutside newDelta
        newGamma; appendedData.tree (Fin.last (2 : ℕ)) = closureTree →
    ∀ (extendedSeries : TashkinovSeries G k ((0 : ℕ) + (1 : ℕ)) e0 prefixInput),
        extendedSeries.data = TashkinovSeriesDataAppend zeroPrefix.data closureTree sigma
        newStored newEdges newKind newVertex newOutside newDelta newGamma →
    ∀ (hroundsEq : (0 : ℕ) + (1 : ℕ) = ett.rounds),
    let castSeries : {a b : ℕ} → a = b → TashkinovSeries G k a e0 prefixInput → TashkinovSeries G
        k b e0 prefixInput := fun {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 prefixInput)
        ↦ @Eq.ndrec Nat a (fun {b : Nat} ↦ @TashkinovSeries V E inst inst_1 inst_2 G k b e0
        prefixInput) S b h; (
    ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 prefixInput) (i : Fin (b + (2 : ℕ))),
        (castSeries h S).data.tree i = S.data.tree (Fin.cast (
    by omega
    ) i)) →
    let finalSeries : TashkinovSeries G k ett.rounds e0 prefixInput := castSeries hroundsEq
        extendedSeries;
    let rawTreeIndex : Fin (ett.rounds + (2 : ℕ)) → Fin (3 : ℕ) := fun (i : Fin (ett.rounds + (2 :
        ℕ))) ↦ Fin.cast (
    by
        have := GoldbergSeymour.TreeSequence.positive T
        omega
    ) i; rawTreeIndex (Fin.last (ett.rounds + (1 : ℕ))) = Fin.last (2 : ℕ) → finalSeries.data.tree
        (Fin.last (ett.rounds + (1 : ℕ))) = closureTree := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma _ closureTree q choice
      prefixInput zeroPrefix newStored newEdges newKind newVertex newOutside newDelta newGamma
      appendedData happendLastTree extendedSeries hextendedData hroundsEq castSeries
      castSeriesTree finalSeries rawTreeIndex hrawFinalTree
  calc
    finalSeries.data.tree (Fin.last (ett.rounds + 1)) =
        extendedSeries.data.tree
          (rawTreeIndex (Fin.last (ett.rounds + 1))) := by
          exact castSeriesTree hroundsEq extendedSeries _
    _ = appendedData.tree
          (rawTreeIndex (Fin.last (ett.rounds + 1))) := by
          rw [hextendedData]
    _ = appendedData.tree (Fin.last 2) := by rw [hrawFinalTree]
    _ = closureTree := happendLastTree

theorem helper_hpenultimateTree_3903.{u_1, u_2} :
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
    ⟩ : Fin ett.rounds); q.succ = Fin.last ett.rounds →
    ∀ (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (prefixInput : PartialEdgeColoring E k) (zeroPrefix : TashkinovSeries G k (0 : ℕ) e0
        prefixInput),
    let zeroLast : Fin ((0 : ℕ) + (1 : ℕ)) := Fin.last (0 : ℕ);
    let newStored : Finset (Fin k) := ({ choice.color } : Finset (Fin k));
    let newEdges : Finset E := ({ choice.edge } : Finset E);
    let newKind : Option TashkinovExtensionKind := some TashkinovExtensionKind.SE;
    let newVertex : Option V := some choice.vertex;
    let newOutside : Option V := some choice.otherEndpoint;
    let newDelta : Option (Fin k) := some choice.color;
    let newGamma : Option (Fin k) := none;
    let appendedData : TashkinovSeriesData G k ((0 : ℕ) + (1 : ℕ)) e0 := TashkinovSeriesDataAppend
        zeroPrefix.data closureTree sigma newStored newEdges newKind newVertex newOutside newDelta
        newGamma; appendedData.tree zeroLast.succ.castSucc = ett.series.data.tree q.succ.castSucc
        →
    ∀ (extendedSeries : TashkinovSeries G k ((0 : ℕ) + (1 : ℕ)) e0 prefixInput),
        extendedSeries.data = TashkinovSeriesDataAppend zeroPrefix.data closureTree sigma
        newStored newEdges newKind newVertex newOutside newDelta newGamma →
    ∀ (hroundsEq : (0 : ℕ) + (1 : ℕ) = ett.rounds),
    let castSeries : {a b : ℕ} → a = b → TashkinovSeries G k a e0 prefixInput → TashkinovSeries G
        k b e0 prefixInput := fun {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 prefixInput)
        ↦ @Eq.ndrec Nat a (fun {b : Nat} ↦ @TashkinovSeries V E inst inst_1 inst_2 G k b e0
        prefixInput) S b h; (
    ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 prefixInput) (i : Fin (b + (2 : ℕ))),
        (castSeries h S).data.tree i = S.data.tree (Fin.cast (
    by omega
    ) i)) →
    let finalSeries : TashkinovSeries G k ett.rounds e0 prefixInput := castSeries hroundsEq
        extendedSeries;
    let rawTreeIndex : Fin (ett.rounds + (2 : ℕ)) → Fin (3 : ℕ) := fun (i : Fin (ett.rounds + (2 :
        ℕ))) ↦ Fin.cast (
    by
        have := GoldbergSeymour.TreeSequence.positive T
        omega
    ) i; rawTreeIndex (⟨ett.rounds,
    by
            have := GoldbergSeymour.TreeSequence.positive T
            omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))) = zeroLast.succ.castSucc → finalSeries.data.tree (⟨ett.rounds,
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))) = ett.series.data.tree (Fin.last ett.rounds).castSucc := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma Tstar closureTree q hqSucc choice
      prefixInput zeroPrefix zeroLast newStored newEdges newKind newVertex newOutside newDelta
      newGamma appendedData happendTree extendedSeries hextendedData hroundsEq castSeries
      castSeriesTree finalSeries rawTreeIndex hrawPenultimate
  exact @helper_hpenultimateTree_713 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive)
      (@sigma) (@Tstar) (@closureTree) (@hqSucc) (@choice) (@prefixInput) (@zeroPrefix)
      (@happendTree) (@extendedSeries) (@hextendedData) (@hroundsEq) (@castSeriesTree)
      (@hrawPenultimate)

theorem helper_hfinalColor_3911.{u_1, u_2} :
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
    ∀ (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (prefixInput : PartialEdgeColoring E k) (zeroPrefix : TashkinovSeries G k (0 : ℕ) e0
        prefixInput),
    let newStored : Finset (Fin k) := ({ choice.color } : Finset (Fin k));
    let newEdges : Finset E := ({ choice.edge } : Finset E);
    let newKind : Option TashkinovExtensionKind := some TashkinovExtensionKind.SE;
    let newVertex : Option V := some choice.vertex;
    let newOutside : Option V := some choice.otherEndpoint;
    let newDelta : Option (Fin k) := some choice.color;
    let newGamma : Option (Fin k) := none;
    let appendedData : TashkinovSeriesData G k ((0 : ℕ) + (1 : ℕ)) e0 := TashkinovSeriesDataAppend
        zeroPrefix.data closureTree sigma newStored newEdges newKind newVertex newOutside newDelta
        newGamma; appendedData.coloring (Fin.last (1 : ℕ)) = sigma →
    ∀ (extendedSeries : TashkinovSeries G k ((0 : ℕ) + (1 : ℕ)) e0 prefixInput),
        extendedSeries.data = TashkinovSeriesDataAppend zeroPrefix.data closureTree sigma
        newStored newEdges newKind newVertex newOutside newDelta newGamma →
    ∀ (hroundsEq : (0 : ℕ) + (1 : ℕ) = ett.rounds),
    let castSeries : {a b : ℕ} → a = b → TashkinovSeries G k a e0 prefixInput → TashkinovSeries G
        k b e0 prefixInput := fun {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 prefixInput)
        ↦ @Eq.ndrec Nat a (fun {b : Nat} ↦ @TashkinovSeries V E inst inst_1 inst_2 G k b e0
        prefixInput) S b h; (
    ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 prefixInput) (i : Fin (b + (1 : ℕ))),
        (castSeries h S).data.coloring i = S.data.coloring (Fin.cast (
    by omega
    ) i)) →
    let finalSeries : TashkinovSeries G k ett.rounds e0 prefixInput := castSeries hroundsEq
        extendedSeries;
    let rawDataIndex : Fin (ett.rounds + (1 : ℕ)) → Fin (2 : ℕ) := fun (i : Fin (ett.rounds + (1 :
        ℕ))) ↦ Fin.cast (
    by
        have := GoldbergSeymour.TreeSequence.positive T
        omega
    ) i; rawDataIndex (Fin.last ett.rounds) = Fin.last (1 : ℕ) → finalSeries.data.coloring
        (Fin.last ett.rounds) = sigma := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma _ closureTree q choice
      prefixInput zeroPrefix newStored newEdges newKind newVertex newOutside newDelta newGamma
      appendedData happendLastColor extendedSeries hextendedData hroundsEq castSeries
      castSeriesColoring finalSeries rawDataIndex hrawFinalData
  calc
    finalSeries.data.coloring (Fin.last ett.rounds) =
        extendedSeries.data.coloring
          (rawDataIndex (Fin.last ett.rounds)) := by
          exact castSeriesColoring hroundsEq extendedSeries _
    _ = appendedData.coloring
          (rawDataIndex (Fin.last ett.rounds)) := by
          rw [hextendedData]
    _ = appendedData.coloring (Fin.last 1) := by rw [hrawFinalData]
    _ = sigma := happendLastColor

theorem helper_hseriesDataAgree_3932.{u_1, u_2} :
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
    ⟩ : Fin ett.rounds); q.succ = Fin.last ett.rounds →
    ∀ (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)),
        ett.series.data.stored q.succ = ({ choice.color } : Finset (Fin k)) →
        ett.series.data.connectingEdges q.succ = ({ choice.edge } : Finset E) →
        ett.series.data.kind q.succ = some TashkinovExtensionKind.SE → ett.rounds = (1 : ℕ) →
    ∀ (prefixInput : PartialEdgeColoring E k) (zeroPrefix : TashkinovSeries G k (0 : ℕ) e0
        prefixInput),
    let zeroLast : Fin ((0 : ℕ) + (1 : ℕ)) := Fin.last (0 : ℕ);
    let newStored : Finset (Fin k) := ({ choice.color } : Finset (Fin k));
    let newEdges : Finset E := ({ choice.edge } : Finset E);
    let newKind : Option TashkinovExtensionKind := some TashkinovExtensionKind.SE;
    let newVertex : Option V := some choice.vertex;
    let newOutside : Option V := some choice.otherEndpoint;
    let newDelta : Option (Fin k) := some choice.color;
    let newGamma : Option (Fin k) := none;
    let appendedData : TashkinovSeriesData G k ((0 : ℕ) + (1 : ℕ)) e0 := TashkinovSeriesDataAppend
        zeroPrefix.data closureTree sigma newStored newEdges newKind newVertex newOutside newDelta
        newGamma; appendedData.stored (Fin.last (1 : ℕ)) = newStored →
        appendedData.connectingEdges (Fin.last (1 : ℕ)) = newEdges → appendedData.kind (Fin.last
        (1 : ℕ)) = newKind →
    ∀ (extendedSeries : TashkinovSeries G k ((0 : ℕ) + (1 : ℕ)) e0 prefixInput),
        extendedSeries.data = TashkinovSeriesDataAppend zeroPrefix.data closureTree sigma
        newStored newEdges newKind newVertex newOutside newDelta newGamma →
    ∀ (hroundsEq : (0 : ℕ) + (1 : ℕ) = ett.rounds),
    let castSeries : {a b : ℕ} → a = b → TashkinovSeries G k a e0 prefixInput → TashkinovSeries G
        k b e0 prefixInput := fun {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 prefixInput)
        ↦ @Eq.ndrec Nat a (fun {b : Nat} ↦ @TashkinovSeries V E inst inst_1 inst_2 G k b e0
        prefixInput) S b h; (
    ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 prefixInput) (i : Fin (b + (1 : ℕ))),
        (castSeries h S).data.stored i = S.data.stored (Fin.cast (
    by omega
    ) i)) → (
    ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 prefixInput) (i : Fin (b + (1 : ℕ))),
        (castSeries h S).data.connectingEdges i = S.data.connectingEdges (Fin.cast (
    by omega
    ) i)) → (
    ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 prefixInput) (i : Fin (b + (1 : ℕ))),
        (castSeries h S).data.kind i = S.data.kind (Fin.cast (
    by omega
    ) i)) →
    let finalSeries : TashkinovSeries G k ett.rounds e0 prefixInput := castSeries hroundsEq
        extendedSeries;
    let rawDataIndex : Fin (ett.rounds + (1 : ℕ)) → Fin (2 : ℕ) := fun (i : Fin (ett.rounds + (1 :
        ℕ))) ↦ Fin.cast (
    by
        have := GoldbergSeymour.TreeSequence.positive T
        omega
    ) i; rawDataIndex (Fin.last ett.rounds) = Fin.last (1 : ℕ) → (
    ∀ (i : Fin (ett.rounds + (1 : ℕ))), (↑i : ℕ) < ett.rounds → zeroPrefix.data.stored zeroLast =
        ett.series.data.stored i ∧ zeroPrefix.data.connectingEdges zeroLast =
        ett.series.data.connectingEdges i ∧ zeroPrefix.data.kind zeroLast = ett.series.data.kind
        i) →
    ∀ (i : Fin (ett.rounds + (1 : ℕ))), finalSeries.data.stored i = ett.series.data.stored i ∧
        finalSeries.data.connectingEdges i = ett.series.data.connectingEdges i ∧
        finalSeries.data.kind i = ett.series.data.kind i := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma Tstar closureTree q hqSucc choice
      currentStored currentEdges currentKind hroundOne prefixInput zeroPrefix zeroLast newStored
      newEdges newKind newVertex newOutside newDelta newGamma appendedData happendLastStored
      happendLastEdges happendLastKind extendedSeries hextendedData hroundsEq castSeries
      castSeriesStored castSeriesEdges castSeriesKind finalSeries rawDataIndex hrawFinalData
      hprefixFields
  exact @helper_hseriesDataAgree_772 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive)
      (@sigma) (@Tstar) (@closureTree) (@hqSucc) (@choice) (@currentStored)
      (@currentEdges) (@currentKind) (@hroundOne) (@prefixInput) (@zeroPrefix)
      (@happendLastStored) (@happendLastEdges) (@happendLastKind) (@extendedSeries)
      (@hextendedData) (@hroundsEq) (@castSeriesStored) (@castSeriesEdges)
      (@castSeriesKind) (@hrawFinalData) (@hprefixFields)

theorem helper_hseriesTreeAgree_3944.{u_1, u_2} :
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
    ⟩ : Fin ett.rounds); q.succ = Fin.last ett.rounds →
    ∀ (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)),
        ett.rounds = (1 : ℕ) →
    ∀ (prefixInput : PartialEdgeColoring E k) (zeroPrefix : TashkinovSeries G k (0 : ℕ) e0
        prefixInput),
    let zeroLast : Fin ((0 : ℕ) + (1 : ℕ)) := Fin.last (0 : ℕ);
    let newStored : Finset (Fin k) := ({ choice.color } : Finset (Fin k));
    let newEdges : Finset E := ({ choice.edge } : Finset E);
    let newKind : Option TashkinovExtensionKind := some TashkinovExtensionKind.SE;
    let newVertex : Option V := some choice.vertex;
    let newOutside : Option V := some choice.otherEndpoint;
    let newDelta : Option (Fin k) := some choice.color;
    let newGamma : Option (Fin k) := none;
    let appendedData : TashkinovSeriesData G k ((0 : ℕ) + (1 : ℕ)) e0 := TashkinovSeriesDataAppend
        zeroPrefix.data closureTree sigma newStored newEdges newKind newVertex newOutside newDelta
        newGamma; appendedData.tree zeroLast.succ.castSucc = ett.series.data.tree q.succ.castSucc
        →
    ∀ (extendedSeries : TashkinovSeries G k ((0 : ℕ) + (1 : ℕ)) e0 prefixInput),
        extendedSeries.data = TashkinovSeriesDataAppend zeroPrefix.data closureTree sigma
        newStored newEdges newKind newVertex newOutside newDelta newGamma →
    ∀ (hroundsEq : (0 : ℕ) + (1 : ℕ) = ett.rounds),
    let castSeries : {a b : ℕ} → a = b → TashkinovSeries G k a e0 prefixInput → TashkinovSeries G
        k b e0 prefixInput := fun {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 prefixInput)
        ↦ @Eq.ndrec Nat a (fun {b : Nat} ↦ @TashkinovSeries V E inst inst_1 inst_2 G k b e0
        prefixInput) S b h; (
    ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 prefixInput) (i : Fin (b + (2 : ℕ))),
        (castSeries h S).data.tree i = S.data.tree (Fin.cast (
    by omega
    ) i)) →
    let finalSeries : TashkinovSeries G k ett.rounds e0 prefixInput := castSeries hroundsEq
        extendedSeries;
    ∀ (j : Fin ett.rounds), finalSeries.data.tree j.succ.castSucc = ett.series.data.tree
        j.succ.castSucc := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma Tstar closureTree q hqSucc choice
      hroundOne prefixInput zeroPrefix zeroLast newStored newEdges newKind newVertex newOutside
      newDelta newGamma appendedData happendTree extendedSeries hextendedData hroundsEq
      castSeries castSeriesTree finalSeries
  exact @helper_hseriesTreeAgree_874 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive)
      (@sigma) (@Tstar) (@closureTree) (@hqSucc) (@choice) (@hroundOne) (@prefixInput)
      (@zeroPrefix) (@happendTree) (@extendedSeries) (@hextendedData) (@hroundsEq)
      (@castSeriesTree)

theorem helper_hseriesColorProperties_3952.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [inst_2 : DecidableEq
        E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
    ∀ (_ closureTree : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
        have := GoldbergSeymour.TreeSequence.positive T
        omega
    ⟩ : Fin ett.rounds);
    ∀ (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (sigmaPrev : PartialEdgeColoring E k), IsProperEdgeColoring G sigmaPrev →
        IsOneEdgeUncolored sigmaPrev e0 → ett.rounds = (1 : ℕ) →
    ∀ (prefixInput : PartialEdgeColoring E k) (zeroPrefix : TashkinovSeries G k (0 : ℕ) e0
        prefixInput),
    let zeroLast : Fin ((0 : ℕ) + (1 : ℕ)) := Fin.last (0 : ℕ);
    let newStored : Finset (Fin k) := ({ choice.color } : Finset (Fin k));
    let newEdges : Finset E := ({ choice.edge } : Finset E);
    let newKind : Option TashkinovExtensionKind := some TashkinovExtensionKind.SE;
    let newVertex : Option V := some choice.vertex;
    let newOutside : Option V := some choice.otherEndpoint;
    let newDelta : Option (Fin k) := some choice.color;
    let newGamma : Option (Fin k) := none;
    let appendedData : TashkinovSeriesData G k ((0 : ℕ) + (1 : ℕ)) e0 := TashkinovSeriesDataAppend
        zeroPrefix.data closureTree sigma newStored newEdges newKind newVertex newOutside newDelta
        newGamma; appendedData.coloring zeroLast.castSucc = sigmaPrev →
    ∀ (extendedSeries : TashkinovSeries G k ((0 : ℕ) + (1 : ℕ)) e0 prefixInput),
        extendedSeries.data = TashkinovSeriesDataAppend zeroPrefix.data closureTree sigma
        newStored newEdges newKind newVertex newOutside newDelta newGamma →
    ∀ (hroundsEq : (0 : ℕ) + (1 : ℕ) = ett.rounds),
    let castSeries : {a b : ℕ} → a = b → TashkinovSeries G k a e0 prefixInput → TashkinovSeries G
        k b e0 prefixInput := fun {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 prefixInput)
        ↦ @Eq.ndrec Nat a (fun {b : Nat} ↦ @TashkinovSeries V E inst inst_1 inst_2 G k b e0
        prefixInput) S b h; (
    ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 prefixInput) (i : Fin (b + (1 : ℕ))),
        (castSeries h S).data.coloring i = S.data.coloring (Fin.cast (
    by omega
    ) i)) →
    let finalSeries : TashkinovSeries G k ett.rounds e0 prefixInput := castSeries hroundsEq
        extendedSeries; finalSeries.data.coloring (Fin.last ett.rounds) = sigma →
    ∀ (i : Fin (ett.rounds + (1 : ℕ))), IsProperEdgeColoring G (finalSeries.data.coloring i) ∧
        IsOneEdgeUncolored (finalSeries.data.coloring i) e0 := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma hsigmaProper hsigmaOne Tstar
      closureTree q choice sigmaPrev hsigmaPrevProper hsigmaPrevOne hroundOne prefixInput
      zeroPrefix zeroLast newStored newEdges newKind newVertex newOutside newDelta newGamma
      appendedData happendColor extendedSeries hextendedData hroundsEq castSeries
      castSeriesColoring finalSeries hfinalColor
  exact @helper_hseriesColorProperties_898 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive)
      (@sigma) (@hsigmaProper) (@hsigmaOne) (@Tstar) (@closureTree) (@choice)
      (@sigmaPrev) (@hsigmaPrevProper) (@hsigmaPrevOne) (@hroundOne) (@prefixInput)
      (@zeroPrefix) (@happendColor) (@extendedSeries) (@hextendedData) (@hroundsEq)
      (@castSeriesColoring) (@hfinalColor)

theorem helper_hseriesStable_3961.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [inst_2 : DecidableEq
        E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating), (0 : ℕ) < ett.rounds →
    ∀ (sigma : PartialEdgeColoring E k), StableColoring (ett.series.data.tree (Fin.last
        ett.rounds).castSucc) (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
        (ett.series.data.coloring (Fin.last ett.rounds)) sigma →
    ∀ (_ _ : TreeSequence G e0), ett.rounds = (1 : ℕ) →
    ∀ (prefixInput : PartialEdgeColoring E k) (extendedSeries : TashkinovSeries G k ((0 : ℕ) + (1
        : ℕ)) e0 prefixInput) (hroundsEq : (0 : ℕ) + (1 : ℕ) = ett.rounds),
    let castSeries : {a b : ℕ} → a = b → TashkinovSeries G k a e0 prefixInput → TashkinovSeries G
        k b e0 prefixInput := fun {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 prefixInput)
        ↦ @Eq.ndrec Nat a (fun {b : Nat} ↦ @TashkinovSeries V E inst inst_1 inst_2 G k b e0
        prefixInput) S b h;
    let finalSeries : TashkinovSeries G k ett.rounds e0 prefixInput := castSeries hroundsEq
        extendedSeries; finalSeries.data.coloring (Fin.last ett.rounds) = sigma →
    ∀ (j : Fin ett.rounds), StableColoring (ett.series.data.tree j.succ.castSucc)
        (TashkinovStoredColors ett.series.data j.succ) (ett.series.data.coloring j.succ)
        (finalSeries.data.coloring j.succ) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma hsigmaStable _ closureTree
      hroundOne prefixInput extendedSeries hroundsEq castSeries finalSeries hfinalColor j
  have hj : j.succ = Fin.last ett.rounds := by
    apply Fin.ext
    have hjbound := j.isLt
    simp
    have hr := hroundOne
    omega
  rw [hj, hfinalColor]
  exact hsigmaStable

theorem helper_hreplacementCurrentTree_4014.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
        have := GoldbergSeymour.TreeSequence.positive T
        omega
    ⟩ : Fin ett.rounds); q.succ = Fin.last ett.rounds →
    ∀ (sigmaPrev : PartialEdgeColoring E k) (originalPrefix : ExtendedTashkinovTree G k e0 input
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) (ett.series.data.coloring
        (⟨ett.rounds - (1 : ℕ),
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (corr : CorrespondingExtendedTashkinovTree G k e0
        originalPrefix sigmaPrev (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
        corr.replacementSeries.data.tree (Fin.last (originalPrefix.rounds + (1 : ℕ))) =
        ett.series.data.tree (Fin.last ett.rounds).castSucc →
    let replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last originalPrefix.rounds;
        corr.replacementSeries.data.tree replacementLast.succ = ett.series.data.tree
        q.succ.castSucc := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ q hqSucc sigmaPrev originalPrefix
      corr hcorrFinalTree replacementLast
  have hlastTree : replacementLast.succ =
      Fin.last (originalPrefix.rounds + 1) := by
    apply Fin.ext
    simp [replacementLast]
  rw [hlastTree, hcorrFinalTree, hqSucc]

theorem helper_horiginalCurrentTree_4022.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
        have := GoldbergSeymour.TreeSequence.positive T
        omega
    ⟩ : Fin ett.rounds); (1 : ℕ) < ett.rounds →
    ∀ (originalPrefix : ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last
        ett.rounds).castSucc) (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ)), (
    ∀ (i : Fin (originalPrefix.rounds + (2 : ℕ))), originalPrefix.series.data.tree i =
        ett.series.data.tree (Fin.castLE (
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ) i)) →
    let replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last originalPrefix.rounds;
        (0 : ℕ) < originalPrefix.rounds → originalPrefix.series.data.tree replacementLast.castSucc
        = ett.series.data.tree q.castSucc.castSucc := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ q hroundLarge originalPrefix hr
      hprefixTrees replacementLast horiginalPositive
  calc
    originalPrefix.series.data.tree replacementLast.castSucc =
        ett.series.data.tree
          (Fin.castLE (by omega) replacementLast.castSucc) :=
      hprefixTrees replacementLast.castSucc
    _ = ett.series.data.tree q.castSucc.castSucc := by
      congr 1
      apply Fin.ext
      simp [replacementLast, q, hr]

theorem helper_htreeMissingEq_4034.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (_ : TreeSequence G e0)
        (sigmaPrev : PartialEdgeColoring E k) (originalPrefix : ExtendedTashkinovTree G k e0 input
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) (ett.series.data.coloring
        (⟨ett.rounds - (1 : ℕ),
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (corr : CorrespondingExtendedTashkinovTree G k e0
        originalPrefix sigmaPrev (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
    let replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last originalPrefix.rounds;
    ∀ (horiginalPositive : (0 : ℕ) < originalPrefix.rounds),
    let previousReplacement : Fin originalPrefix.rounds := (⟨originalPrefix.rounds - (1 : ℕ),
    by
        have := GoldbergSeymour.TreeSequence.positive T
        omega
    ⟩ : Fin originalPrefix.rounds); previousReplacement.succ = replacementLast → TreeMissingColors
        (corr.replacementSeries.data.coloring replacementLast) (corr.replacementSeries.data.tree
        replacementLast.castSucc) = TreeMissingColors (originalPrefix.series.data.coloring
        replacementLast) (originalPrefix.series.data.tree replacementLast.castSucc) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ sigmaPrev originalPrefix corr
      replacementLast horiginalPositive previousReplacement hpreviousSucc
  have hstable := corr.replacementStable previousReplacement
  rw [hpreviousSucc] at hstable
  have htree := corr.ladderTreesAgree previousReplacement
  rw [hpreviousSucc] at htree
  rw [htree]
  ext c
  simp only [TreeMissingColors, Finset.mem_biUnion]
  constructor
  · rintro ⟨v, hv, hc⟩
    exact ⟨v, hv, (hstable.2 v hv).symm ▸ hc⟩
  · rintro ⟨v, hv, hc⟩
    exact ⟨v, hv, hstable.2 v hv ▸ hc⟩

theorem helper_hreplacementStored_4052.{u_1, u_2} :
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
    ∀ (sigmaPrev : PartialEdgeColoring E k) (hroundLarge : (1 : ℕ) < ett.rounds) (originalPrefix :
        ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ)), (
    ∀ (i : Fin (originalPrefix.rounds + (1 : ℕ))), originalPrefix.series.data.coloring i =
        ett.series.data.coloring (Fin.castLE (
    by
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    ) i) ∧ originalPrefix.series.data.stored i = ett.series.data.stored (Fin.castLE (
    by
                  have := GoldbergSeymour.TreeSequence.positive T
                  omega
    ) i) ∧ originalPrefix.series.data.connectingEdges i = ett.series.data.connectingEdges
        (Fin.castLE (
    by
                    have := GoldbergSeymour.TreeSequence.positive T
                    omega
    ) i) ∧ originalPrefix.series.data.kind i = ett.series.data.kind (Fin.castLE (
    by
                      have := GoldbergSeymour.TreeSequence.positive T
                      omega
    ) i) ∧ TashkinovStoredColors originalPrefix.series.data i = TashkinovStoredColors
        ett.series.data (Fin.castLE (
    by
                      have := GoldbergSeymour.TreeSequence.positive T
                      omega
    ) i)) →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
    let replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last originalPrefix.rounds;
    ∀ (_ : (0 : ℕ) < originalPrefix.rounds), Fin.castLE (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ) replacementLast = q.castSucc → TreeMissingColors (corr.replacementSeries.data.coloring
        replacementLast) (corr.replacementSeries.data.tree replacementLast.castSucc) =
        TreeMissingColors (originalPrefix.series.data.coloring replacementLast)
        (originalPrefix.series.data.tree replacementLast.castSucc) → TashkinovStoredColors
        corr.replacementSeries.data replacementLast = TashkinovStoredColors ett.series.data
        q.castSucc := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ q sigmaPrev hroundLarge
      originalPrefix hr hprefixData corr replacementLast horiginalPositive hlastMap htreeMissingEq
  have hcorrStored : TashkinovStoredColors
        corr.replacementSeries.data replacementLast =
      TashkinovStoredColors originalPrefix.series.data
        replacementLast := by
    unfold TashkinovStoredColors
    have hnonzero : replacementLast.val ≠ 0 := by
      simp only [Fin.val_last, ne_eq, replacementLast]
      exact Nat.ne_of_gt horiginalPositive
    rw [ite_eq_right hnonzero, ite_eq_right hnonzero]
    ext c
    simp only [Finset.mem_sdiff, Finset.mem_biUnion]
    constructor
    · rintro ⟨⟨j, hj, hc⟩, hn⟩
      refine ⟨⟨j, hj, ?_⟩, ?_⟩
      · by_cases hle : j.val ≤ replacementLast.val
        · simp only [ite_eq_left hle] at hc ⊢
          simpa [corr.storedColorsAgree j] using hc
        · simp only [ite_eq_right hle] at hc ⊢
          exact hc
      · rw [htreeMissingEq] at hn
        exact hn
    · rintro ⟨⟨j, hj, hc⟩, hn⟩
      refine ⟨⟨j, hj, ?_⟩, ?_⟩
      · by_cases hle : j.val ≤ replacementLast.val
        · simp only [ite_eq_left hle] at hc ⊢
          simpa [corr.storedColorsAgree j] using hc
        · simp only [ite_eq_right hle] at hc ⊢
          exact hc
      · rw [← htreeMissingEq] at hn
        exact hn
  calc
    TashkinovStoredColors corr.replacementSeries.data replacementLast =
        TashkinovStoredColors originalPrefix.series.data
          replacementLast := hcorrStored
    _ = TashkinovStoredColors ett.series.data
          (Fin.castLE (by omega) replacementLast) :=
      (hprefixData replacementLast).2.2.2.2
    _ = TashkinovStoredColors ett.series.data q.castSucc := by
      rw [hlastMap]

theorem helper_hnoRevisitingReplacement_4104.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating), MaximumProperty ett →
    ∀ (hpositive : (0 : ℕ) < ett.rounds), LowerRoundInductionHypothesis G k e0 ett.rounds →
    ∀ (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
        have := GoldbergSeymour.TreeSequence.positive T
        omega
    ⟩ : Fin ett.rounds); IsProperEdgeColoring G (ett.series.data.coloring q.castSucc) →
        IsOneEdgeUncolored (ett.series.data.coloring q.castSucc) e0 → ¬Nonempty
        (RevisitingExtensionCertificate ett.series.data q.castSucc) →
    ∀ (sigmaPrev : PartialEdgeColoring E k), IsProperEdgeColoring G sigmaPrev → IsOneEdgeUncolored
        sigmaPrev e0 → StableColoring (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)
        sigmaPrev → (1 : ℕ) < ett.rounds →
    ∀ (originalPrefix : ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last
        ett.rounds).castSucc) (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ)),
        MaximumProperty originalPrefix → (
    ∀ (i : Fin (originalPrefix.rounds + (2 : ℕ))), originalPrefix.series.data.tree i =
        ett.series.data.tree (Fin.castLE (
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ) i)) → (
    ∀ (i : Fin (originalPrefix.rounds + (1 : ℕ))), originalPrefix.series.data.coloring i =
        ett.series.data.coloring (Fin.castLE (
    by
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    ) i) ∧ originalPrefix.series.data.stored i = ett.series.data.stored (Fin.castLE (
    by
                  have := GoldbergSeymour.TreeSequence.positive T
                  omega
    ) i) ∧ originalPrefix.series.data.connectingEdges i = ett.series.data.connectingEdges
        (Fin.castLE (
    by
                    have := GoldbergSeymour.TreeSequence.positive T
                    omega
    ) i) ∧ originalPrefix.series.data.kind i = ett.series.data.kind (Fin.castLE (
    by
                      have := GoldbergSeymour.TreeSequence.positive T
                      omega
    ) i) ∧ TashkinovStoredColors originalPrefix.series.data i = TashkinovStoredColors
        ett.series.data (Fin.castLE (
    by
                      have := GoldbergSeymour.TreeSequence.positive T
                      omega
    ) i)) →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)), corr.replacementSeries.data.tree
        (Fin.last (originalPrefix.rounds + (1 : ℕ))) = ett.series.data.tree (Fin.last
        ett.rounds).castSucc → corr.replacementSeries.data.coloring (Fin.last
        originalPrefix.rounds) = sigmaPrev → MaximumProperty corr.replacementETT →
    let replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last originalPrefix.rounds;
        ¬Nonempty (RevisitingExtensionCertificate corr.replacementSeries.data replacementLast) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hMP hpositive hlower _ q previousProper
      previousOneUncolored noRevisiting sigmaPrev hsigmaPrevProper hsigmaPrevOne hsigmaPrevStableQ
      hroundLarge originalPrefix hr hprefixMP hprefixTrees hprefixData corr hcorrFinalTree
      hcorrFinalColor hcorrMP replacementLast
  exact P2971_T1_PositivePrefixNoRevisiting G k e0 input T generating
    ett hMP hroundLarge
    (fun lower hp hl hm =>
      ⟨(hlower lower hp hl hm).2.1,
        (hlower lower hp hl hm).2.2.2.1⟩)
    sigmaPrev hsigmaPrevProper hsigmaPrevOne previousProper
    previousOneUncolored hsigmaPrevStableQ originalPrefix hr
    hprefixMP hprefixTrees hprefixData corr hcorrFinalTree
    hcorrFinalColor hcorrMP noRevisiting

theorem helper_hnewAlternativeReplacement_4116.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (Tstar : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
        have := GoldbergSeymour.TreeSequence.positive T
        omega
    ⟩ : Fin ett.rounds);
    ∀ (previousProper : IsProperEdgeColoring G (ett.series.data.coloring q.castSucc))
        (previousOneUncolored : IsOneEdgeUncolored (ett.series.data.coloring q.castSucc) e0)
        (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (sigmaPrev : PartialEdgeColoring E k) (hsigmaPrevProper : IsProperEdgeColoring G
        sigmaPrev) (hsigmaPrevOne : IsOneEdgeUncolored sigmaPrev e0) (hsigmaPrevStableQ :
        StableColoring (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors
        ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc) sigmaPrev)
        (hchoiceDefective : DefectiveColor G sigmaPrev (TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc)) choice.color) (hchoiceEdgeNew : choice.edge ∈
        BoundaryColorEdges G sigmaPrev (TreeSequenceVertexSet (ett.series.data.tree
        q.succ.castSucc)) choice.color) (hsigmaPrevSelf : StableColoring (ett.series.data.tree
        q.succ.castSucc) (TashkinovStoredColors ett.series.data q.castSucc) sigmaPrev sigmaPrev),
    let newChoice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) sigmaPrev := helperNewChoice2409 G k e0
        input T generating ett hpositive previousProper previousOneUncolored choice sigmaPrev
        hsigmaPrevProper hsigmaPrevOne hsigmaPrevStableQ hchoiceDefective hchoiceEdgeNew
        hsigmaPrevSelf; (
    ∀ (pi : PartialEdgeColoring E k), IsProperEdgeColoring G pi → IsOneEdgeUncolored pi e0 →
        StableColoring (ett.series.data.tree q.succ.castSucc) (insert newChoice.color
        (TashkinovStoredColors ett.series.data q.castSucc) : Finset (Fin k)) newChoice.selected pi
        → Disjoint (MissingColors G pi newChoice.otherEndpoint) (TreeMissingColors pi
        (ett.series.data.tree q.succ.castSucc))) →
    ∀ (originalPrefix : ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last
        ett.rounds).castSucc) (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (corr : CorrespondingExtendedTashkinovTree G k e0
        originalPrefix sigmaPrev (ett.series.data.tree (Fin.last ett.rounds).castSucc))
        (hcorrFinalColor : corr.replacementSeries.data.coloring (Fin.last originalPrefix.rounds) =
        sigmaPrev),
    let replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last originalPrefix.rounds;
    ∀ (hreplacementCurrentTree : corr.replacementSeries.data.tree replacementLast.succ =
        ett.series.data.tree q.succ.castSucc) (hreplacementStored : TashkinovStoredColors
        corr.replacementSeries.data replacementLast = TashkinovStoredColors ett.series.data
        q.castSucc),
    let replacementChoice : MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree
        replacementLast.succ) (TashkinovStoredColors corr.replacementSeries.data replacementLast)
        (corr.replacementSeries.data.coloring replacementLast) := helperReplacementChoice3411 G k
        e0 input T generating ett hpositive previousProper previousOneUncolored choice sigmaPrev
        hsigmaPrevProper hsigmaPrevOne hsigmaPrevStableQ hchoiceDefective hchoiceEdgeNew
        hsigmaPrevSelf originalPrefix corr hcorrFinalColor hreplacementCurrentTree
        hreplacementStored;
    ∀ (pi : PartialEdgeColoring E k), IsProperEdgeColoring G pi → IsOneEdgeUncolored pi e0 →
        StableColoring (corr.replacementSeries.data.tree replacementLast.succ) (insert
        replacementChoice.color (TashkinovStoredColors corr.replacementSeries.data
        replacementLast) : Finset (Fin k)) replacementChoice.selected pi → Disjoint (MissingColors
        G pi replacementChoice.otherEndpoint) (TreeMissingColors pi
        (corr.replacementSeries.data.tree replacementLast.succ)) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ q previousProper
      previousOneUncolored choice sigmaPrev hsigmaPrevProper hsigmaPrevOne hsigmaPrevStableQ
      hchoiceDefective hchoiceEdgeNew hsigmaPrevSelf newChoice hnewAlternative originalPrefix
      corr hcorrFinalColor replacementLast hreplacementCurrentTree hreplacementStored
      replacementChoice pi hpiProper hpiOne hpiStable
  have hpiStable' := hpiStable
  change StableColoring
    (corr.replacementSeries.data.tree replacementLast.succ)
    (insert choice.color
      (TashkinovStoredColors corr.replacementSeries.data
        replacementLast)) sigmaPrev pi at hpiStable'
  rw [hreplacementCurrentTree, hreplacementStored] at hpiStable'
  have hresult := hnewAlternative pi hpiProper hpiOne
    (by simpa [replacementChoice, newChoice] using hpiStable')
  change Disjoint (MissingColors G pi choice.otherEndpoint)
    (TreeMissingColors pi
      (corr.replacementSeries.data.tree replacementLast.succ))
  rw [hreplacementCurrentTree]
  simpa [replacementChoice, newChoice] using hresult

end GoldbergSeymour.TerminalSeriesRebuild

end
