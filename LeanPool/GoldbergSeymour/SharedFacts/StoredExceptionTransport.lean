/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyTreeFacts

public import LeanPool.GoldbergSeymour.HierarchyReplacementPresentation

/-!
# Shared facts for HierarchySituationTwoSubcaseOneOneStoredException

These interfaces and proofs are shared across the imported proof branches.
Extracted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12 during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour.SharedFacts.StoredExceptionTransport

/-- Shared dependent data used by more than one proof branch. -/
noncomputable abbrev selfCorr425.{u_1, u_2} :
    open scoped Classical in
  {V : Type u_1} →
  {E : Type u_2} →
  [Fintype V] →
  [Fintype E] →
  [DecidableEq E] →
  (G : LooplessMultigraph V E) →
  (k : ℕ) →
  (e0 : E) →
  (input : PartialEdgeColoring E k) →
  (T : TreeSequence G e0) →
  (phi : PartialEdgeColoring E k) →
  (ett : ExtendedTashkinovTree G k e0 input T phi) →
  (
  ∀ (j : Fin (ett.rounds + (1 : ℕ))),
  IsProperEdgeColoring G (ett.series.data.coloring j)) →
  (
  ∀ (j : Fin (ett.rounds + (1 : ℕ))),
  IsOneEdgeUncolored (ett.series.data.coloring j) e0) →
  CorrespondingExtendedTashkinovTree G k e0 ett phi T := by
  classical
  intro V E _ _ _ G k e0 input T phi ett seriesProper seriesOne
  exact {
    replacementInput := input
    replacementSeries := ett.series
    replacementETT := ett
    rungAgreement := rfl
    seriesPresentation := HEq.rfl
    finalGeneratingColoring := ett.generatingColoring
    ladderTreesAgree := fun _ => rfl
    storedColorsAgree := fun _ => rfl
    connectingEdgesAgree := fun _ => rfl
    extensionKindsAgree := fun _ => rfl
    replacementProper := seriesProper
    replacementOneUncolored := seriesOne
    replacementStable := fun _ => ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩ }

/-- Shared dependent data used by more than one proof branch. -/
noncomputable abbrev p0462.{u_1, u_2} :
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
  (seriesProper :
  ∀ (j : Fin (ett.rounds + (1 : ℕ))),
  IsProperEdgeColoring G (ett.series.data.coloring j)) →
  (seriesOne :
  ∀ (j : Fin (ett.rounds + (1 : ℕ))),
  IsOneEdgeUncolored (ett.series.data.coloring j) e0) →
  let _ :
    CorrespondingExtendedTashkinovTree G k e0 ett phi T :=
    SharedFacts.StoredExceptionTransport.selfCorr425 G k e0 input T phi ett seriesProper
      seriesOne;
  HierarchyReplacementPresentation G k e0 input T phi ett
    base C ctx := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx seriesProper seriesOne selfCorr
  exact {
    coloring := phi
    corresponding := selfCorr
    maximum := C.maximum
    replacementBase := base
    counterexample := C
    sameGood := ⟨⟨rfl, rfl, HEq.rfl, HEq.rfl, Iff.rfl, fun _ => rfl⟩,
      rfl, fun _ => ⟨rfl, fun _ _ => rfl⟩⟩
    minimumContext := ctx }

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev segmentTransStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
          {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Y → TreeSequenceInitialSegment Y
          Z → TreeSequenceInitialSegment X Z

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev hierarchyGeometryStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
          LooplessMultigraph V E) (k : ℕ) (e0 : E) (T : TreeSequence G e0), (
      ∀ {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Y → TreeSequenceInitialSegment Y Z
          → TreeSequenceInitialSegment X Z) →
      ∀ {inp col : PartialEdgeColoring E k} {J : ExtendedTashkinovTree G k e0 inp T col}
          {b : HierarchyBase J col} (H : TashkinovHierarchy J b), TreeSequenceInitialSegment
          (HierarchyStarredStage H (Fin.last H.dividerCount)) T ∧ TreeSequenceInitialSegment
          (J.series.data.tree (Fin.last J.rounds).castSucc) (HierarchyStarredStage H (Fin.last
          H.dividerCount))

/-- A common proof used by the branches of this transport or construction argument. -/
theorem segmentTrans.{u_1, u_2} : segmentTransStatement.{u_1, u_2} := by
  intro V E G e0 X Y Z hXY hYZ
  exact hXY.trans hYZ


/-- A common proof used by the branches of this transport or construction argument. -/
theorem hierarchyGeometry.{u_1, u_2} : hierarchyGeometryStatement.{u_1, u_2} := by
  intro V E _ _ _ _ G k e0 T segmentTrans inp col J b H
  exact ⟨H.lastStarredInitialSegment,
    b.lastRoundInitialSegmentCore.trans
      (H.coreInitialSegmentOfStarredStage (Fin.last H.dividerCount))⟩

end GoldbergSeymour.SharedFacts.StoredExceptionTransport

end
