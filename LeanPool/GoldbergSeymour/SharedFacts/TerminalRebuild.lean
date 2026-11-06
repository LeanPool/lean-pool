/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.StableColoringEquivalence
public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTree

/-!
# Shared facts for TerminalSeriesRebuildPreparation

These interfaces and proofs are shared across the imported proof branches.
Extracted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12 during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour.SharedFacts.TerminalRebuild

/-- Shared dependent data used by more than one proof branch. -/
noncomputable abbrev newChoice2409.{u_1, u_2} :
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

/-- Shared dependent data used by more than one proof branch. -/
noncomputable abbrev replacementChoice3411.{u_1, u_2} :
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
    SharedFacts.TerminalRebuild.newChoice2409 G k e0 input T
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

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev hdeltaBoundaryStatement.{u_1, u_2} : Prop :=
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
          (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) choice.color

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev hclosedPrevStatement.{u_1, u_2} : Prop :=
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
          (ett.series.data.tree q.succ.castSucc))

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev hchoiceDefectiveStatement.{u_1, u_2} : Prop :=
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
          (ett.series.data.tree q.succ.castSucc)) choice.color

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev hchoiceEdgeNewStatement.{u_1, u_2} : Prop :=
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
          (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) choice.color

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev hnotStrongPrevStatement.{u_1, u_2} : Prop :=
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
          sigmaPrev (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc))

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev hreplacementCurrentTreeStatement.{u_1, u_2} : Prop :=
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
          q.succ.castSucc

/-- A common proof used by the branches of this transport or construction argument. -/
theorem hdeltaBoundary.{u_1, u_2} : hdeltaBoundaryStatement.{u_1, u_2} := by
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

/-- A common proof used by the branches of this transport or construction argument. -/
theorem hclosedPrev.{u_1, u_2} : hclosedPrevStatement.{u_1, u_2} := by
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

/-- A common proof used by the branches of this transport or construction argument. -/
theorem hchoiceDefective.{u_1, u_2} : hchoiceDefectiveStatement.{u_1, u_2} := by
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

/-- A common proof used by the branches of this transport or construction argument. -/
theorem hchoiceEdgeNew.{u_1, u_2} : hchoiceEdgeNewStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ q choice sigmaPrev hdeltaBoundary
  rw [← hdeltaBoundary]
  obtain ⟨oldColor, holdDefective, holdEdge⟩ := choice.edgeDefective
  have holdColor : oldColor = choice.color := by
    have holdEdgeColor := (Finset.mem_filter.mp holdEdge).2
    exact Option.some.inj (holdEdgeColor.symm.trans choice.edgeColor)
  simpa [holdColor] using holdEdge

/-- A common proof used by the branches of this transport or construction argument. -/
theorem hnotStrongPrev.{u_1, u_2} : hnotStrongPrevStatement.{u_1, u_2} := by
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

/-- A common proof used by the branches of this transport or construction argument. -/
theorem hreplacementCurrentTree.{u_1, u_2} : hreplacementCurrentTreeStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ q hqSucc sigmaPrev originalPrefix
      corr hcorrFinalTree replacementLast
  have hlastTree : replacementLast.succ =
      Fin.last (originalPrefix.rounds + 1) := by
    apply Fin.ext
    simp [replacementLast]
  rw [hlastTree, hcorrFinalTree, hqSucc]

end GoldbergSeymour.SharedFacts.TerminalRebuild

end
