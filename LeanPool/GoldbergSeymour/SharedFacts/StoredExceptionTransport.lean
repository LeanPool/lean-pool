/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

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
  classical
  intro V E G e0 X Y Z hXY hYZ
  refine ⟨le_trans hXY.1 hYZ.1, ?_, ?_⟩
  · intro i
    exact (hYZ.2.1 (Fin.castLE (Nat.succ_le_succ hXY.1) i)).trans (hXY.2.1 i)
  · intro i
    exact (hYZ.2.2 (Fin.castLE hXY.1 i)).trans (hXY.2.2 i)

/-- A common proof used by the branches of this transport or construction argument. -/
theorem hierarchyGeometry.{u_1, u_2} : hierarchyGeometryStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 T segmentTrans inp col J b H
  have forward : ∀ (a d : ℕ), (hbound : a + d ≤ H.dividerCount + 1) →
      TreeSequenceInitialSegment (H.stage ⟨a, by omega⟩)
        (H.stage ⟨a + d, by omega⟩) := by
    intro a d
    induction d with
    | zero => intro h; exact ⟨le_rfl, (by intro i; rfl), (by intro i; rfl)⟩
    | succ d ih =>
      intro h
      exact segmentTrans (ih (by omega)) (H.nested ⟨a + d, by omega⟩)
  let A := HierarchyStarredStage H (Fin.last H.dividerCount)
  let Tn := J.series.data.tree (Fin.last J.rounds).castSucc
  change TreeSequenceInitialSegment A T ∧ TreeSequenceInitialSegment Tn A
  have hTnCore : TreeSequenceInitialSegment Tn b.core := by
    by_cases hp : J.series.data.kind (Fin.last J.rounds) =
        some TashkinovExtensionKind.PE
    · exact (b.parallel hp).2.2.some.leftSegment
    · rw [b.nonparallel hp]
      exact ⟨le_rfl, (by intro i; rfl), (by intro i; rfl)⟩
  by_cases hq : H.dividerCount = 0
  · have hA : A = b.core := by
      simp [A, HierarchyStarredStage, Fin.last, hq]
    have hlast : H.stage ⟨1, by omega⟩ = T := by
      convert H.terminalStage using 1
      apply congrArg H.stage
      apply Fin.ext
      simp [hq]
    constructor
    · rw [hA]
      exact Eq.mp (congrArg (fun W : TreeSequence G e0 =>
        TreeSequenceInitialSegment b.core W) hlast) H.coreInsideFirst
    · rw [hA]
      exact hTnCore
  · have hpos : 0 < H.dividerCount := Nat.pos_of_ne_zero hq
    have hindex : (Fin.last H.dividerCount : Fin (H.dividerCount + 1)) =
        (⟨H.dividerCount - 1, by omega⟩ : Fin H.dividerCount).succ := by
      apply Fin.ext
      simp
      omega
    have hA : A = H.stage ⟨H.dividerCount, by omega⟩ := by
      dsimp [A, HierarchyStarredStage]
      rw [hindex]
      dsimp
      apply congrArg H.stage
      apply Fin.ext
      simp
      omega
    have hlast : H.stage ⟨H.dividerCount + 1, by omega⟩ = T := H.terminalStage
    have hTnStage : H.stage (0 : Fin (H.dividerCount + 2)) = Tn := H.baseStage
    refine ⟨?_, ?_⟩
    · simpa [hA, hlast] using forward H.dividerCount 1 (by omega)
    · simpa [hA, hTnStage] using forward 0 H.dividerCount (by omega)

end GoldbergSeymour.SharedFacts.StoredExceptionTransport

end
