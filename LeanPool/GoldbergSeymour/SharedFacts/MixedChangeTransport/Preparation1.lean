/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTree
public import LeanPool.GoldbergSeymour.HierarchyCounterexample
public import LeanPool.GoldbergSeymour.TwoColorPathComponent

/-!
# Shared facts for ChangeLemmaMixedClosedFinal

These interfaces and proofs are shared across the imported proof branches.
Extracted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12 during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour.SharedFacts.MixedChangeTransport

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev initialSegmentTransitiveStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
        {S U W : TreeSequence G e0},
      TreeSequenceInitialSegment S U →
      TreeSequenceInitialSegment U W →
      TreeSequenceInitialSegment S W

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev comparableInitialSegmentsStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
        {S U W : TreeSequence G e0},
      TreeSequenceInitialSegment S W →
      TreeSequenceInitialSegment U W →
      S.length ≤ U.length →
      TreeSequenceInitialSegment S U

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev stageInitialSegmentStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
        [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
        (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
        (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
      let H : TashkinovHierarchy ett base := C.hierarchy;
      (∀ (S : TreeSequence G e0), TreeSequenceInitialSegment S S) →
      (∀ {S U W : TreeSequence G e0},
          TreeSequenceInitialSegment S U →
            TreeSequenceInitialSegment U W → TreeSequenceInitialSegment S W) →
      ∀ (a d : ℕ) (hbound : a + d ≤ H.dividerCount + (1 : ℕ)),
      TreeSequenceInitialSegment (H.stage (⟨a, by omega⟩ : Fin (H.dividerCount + (2 : ℕ))))
        (H.stage (⟨a + d, by omega⟩ : Fin (H.dividerCount + (2 : ℕ))))

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev stageInitialSegmentOfFinalTreeStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
        [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
        (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
        (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
      let H : TashkinovHierarchy ett base := C.hierarchy;
      (∀ (a d : ℕ) (hbound : a + d ≤ H.dividerCount + (1 : ℕ)),
          TreeSequenceInitialSegment
            (H.stage (⟨a, by omega⟩ : Fin (H.dividerCount + (2 : ℕ))))
            (H.stage (⟨a + d, by omega⟩ : Fin (H.dividerCount + (2 : ℕ))))) →
      ∀ (j : Fin (H.dividerCount + (2 : ℕ))),
      TreeSequenceInitialSegment (H.stage j) T

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev lastStagePositiveStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
        [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
        (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
        (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
      let H : TashkinovHierarchy ett base := C.hierarchy;
      let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
      let A : TreeSequence G e0 := HierarchyStarredStage H q;
      H.dividerCount ≠ (0 : ℕ) →
      A = H.stage (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + (2 : ℕ)))

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev coreInitialSegmentOfStarredStageStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
        [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
        (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
        (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
      let H : TashkinovHierarchy ett base := C.hierarchy;
      let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
      let A : TreeSequence G e0 := HierarchyStarredStage H q;
      (∀ (S : TreeSequence G e0), TreeSequenceInitialSegment S S) →
      (∀ {S U W : TreeSequence G e0},
          TreeSequenceInitialSegment S U →
            TreeSequenceInitialSegment U W → TreeSequenceInitialSegment S W) →
      (∀ (a d : ℕ) (hbound : a + d ≤ H.dividerCount + (1 : ℕ)),
          TreeSequenceInitialSegment
            (H.stage (⟨a, by omega⟩ : Fin (H.dividerCount + (2 : ℕ))))
            (H.stage (⟨a + d, by omega⟩ : Fin (H.dividerCount + (2 : ℕ))))) →
      (H.dividerCount = (0 : ℕ) → A = base.core) →
      (H.dividerCount ≠ (0 : ℕ) →
          A = H.stage (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + (2 : ℕ)))) →
      TreeSequenceInitialSegment base.core A

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev terminalStageInitialSegmentOfCoreStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
        (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
        (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
        (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi),
      let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
      let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
      (∀ (S : TreeSequence G e0), TreeSequenceInitialSegment S S) →
      TreeSequenceInitialSegment Tn base.core

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev starredStageInitialSegmentOfFinalTreeStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
        [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
        (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
        (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
      let H : TashkinovHierarchy ett base := C.hierarchy;
      let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
      let A : TreeSequence G e0 := HierarchyStarredStage H q;
      (∀ {S U W : TreeSequence G e0},
          TreeSequenceInitialSegment S U →
            TreeSequenceInitialSegment U W → TreeSequenceInitialSegment S W) →
      (∀ (j : Fin (H.dividerCount + (2 : ℕ))), TreeSequenceInitialSegment (H.stage j) T) →
      (H.dividerCount = (0 : ℕ) → A = base.core) →
      (H.dividerCount ≠ (0 : ℕ) →
          A = H.stage (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + (2 : ℕ)))) →
      TreeSequenceInitialSegment A T

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev ordinaryStageInitialSegmentOfStarredStageStatement.{u_1, u_2} : Prop :=
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
      (H.dividerCount = (0 : ℕ) → A = base.core) →
      (H.dividerCount ≠ (0 : ℕ) →
          A = H.stage (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + (2 : ℕ)))) →
      TreeSequenceInitialSegment Tn A →
      ∀ (j : Fin (H.dividerCount + (1 : ℕ))),
      TreeSequenceInitialSegment (H.stage j.castSucc) A

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev firstMissingPositionWitnessStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
        [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
        (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
        (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
      let H : TashkinovHierarchy ett base := C.hierarchy;
      let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
      let A : TreeSequence G e0 := HierarchyStarredStage H q;
      let ell : ℕ := T.length - A.length;
      let yLength : ℕ := min (A.length + (ell - (1 : ℕ))) T.length;
      let Y : TreeSequence G e0 :=
        TreeSequencePrefix T yLength
          (have hA : (1 : ℕ) ≤ A.length := A.positive;
          have hT : (1 : ℕ) ≤ T.length := T.positive;
          Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ yLength) ↦ by omega)
          (by omega);
      TreeSequenceInitialSegment Y T →
      ∀ c ∈ TreeMissingColors phi Y,
      c ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T c)) ∧
        (↑(HierarchyFirstMissingPosition phi T c) : ℕ) ≤ Y.length

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev missingPositionOutsidePrefixStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
        (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
        (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
        (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
        (C : HierarchyCounterexample base),
      let H : TashkinovHierarchy ett base := C.hierarchy;
      let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
      let A : TreeSequence G e0 := HierarchyStarredStage H q;
      TreeSequenceInitialSegment A T →
      ∀ (i : Fin (T.length + (1 : ℕ))),
      T.vertex i ∉ TreeSequenceVertexSet A →
      A.length < (↑i : ℕ)

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev colorNotMissingOnStarredStageStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
        [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
        (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
        (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
        (alpha beta : Fin k),
      alpha ≠ beta →
      let H : TashkinovHierarchy ett base := C.hierarchy;
      let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
      let A : TreeSequence G e0 := HierarchyStarredStage H q;
      let ell : ℕ := T.length - A.length;
      let yLength : ℕ := min (A.length + (ell - (1 : ℕ))) T.length;
      let Y : TreeSequence G e0 :=
        TreeSequencePrefix T yLength
          (have hA : (1 : ℕ) ≤ A.length := A.positive;
          have hT : (1 : ℕ) ≤ T.length := T.positive;
          Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ yLength) ↦ by omega)
          (by omega);
      ColoredVertexSetElementary G phi (TreeSequenceVertexSet Y) →
      TreeSequenceInitialSegment A Y →
      ∀ (c : Fin k) (i : Fin (T.length + (1 : ℕ))),
      c ∈ MissingColors G phi (T.vertex i) →
      T.vertex i ∈ TreeSequenceVertexSet Y →
      T.vertex i ∉ TreeSequenceVertexSet A →
      c ∉ TreeMissingColors phi A

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev distinctMissingPositionIndicesStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
        (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
        (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
        (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
        (C : HierarchyCounterexample base) (alpha beta : Fin k),
      let ia : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T alpha;
      let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
      TreeVertexOrder T (T.vertex (HierarchyFirstMissingPosition phi T alpha))
            (T.vertex (HierarchyFirstMissingPosition phi T beta)) ∧
          alpha ∉
            ({c : Fin k |
                ∃ (t : Fin T.length),
                  (HierarchyStarredStage C.hierarchy
                          (Fin.last C.hierarchy.dividerCount)).length ≤
                      (↑t : ℕ) ∧
                    (↑t : ℕ) < (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ∧
                      phi (T.edge t) = some c} :
              Finset (Fin k)) →
      (↑ia : ℕ) < (↑ib : ℕ)

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev prefixStrictlyShorterThanFinalTreeStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
        [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
        (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
        (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (_ beta : Fin k),
      let H : TashkinovHierarchy ett base := C.hierarchy;
      let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
      let A : TreeSequence G e0 := HierarchyStarredStage H q;
      let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
      let ell : ℕ := T.length - A.length;
      let yLength : ℕ := min (A.length + (ell - (1 : ℕ))) T.length;
      let Y : TreeSequence G e0 :=
        TreeSequencePrefix T yLength
          (have hA : (1 : ℕ) ≤ A.length := A.positive;
          have hT : (1 : ℕ) ≤ T.length := T.positive;
          Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ yLength) ↦ by omega)
          (by omega);
      TreeSequenceInitialSegment A T →
      ∀ (hAib : A.length < (↑ib : ℕ)),
      let B : TreeSequence G e0 :=
        TreeSequencePrefix T (↑ib : ℕ)
          (have this : (1 : ℕ) ≤ A.length := A.positive;
          Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
          (by omega);
      A.length < B.length →
      TreeSequenceInitialSegment B Y →
      B.length < T.length

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev pathMissingStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E)
        (k : ℕ) (phi : PartialEdgeColoring E k),
      IsProperEdgeColoring G phi →
      ∀ (v : V) (c d : Fin k),
      c ≠ d →
      c ∈ MissingColors G phi v →
      TwoColorPathComponent G phi c d (Sum.inl v)

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev otherColorsUnaffectedStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
        [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input :
            PartialEdgeColoring E k)
        (T : TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
            input T phi)
        (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (alpha beta : Fin k),
        alpha ≠ beta →
          let H : TashkinovHierarchy ett base := C.hierarchy;
          let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
          let A : TreeSequence G e0 := HierarchyStarredStage H q;
          let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
          let vb : V := T.vertex ib;
          let ell : ℕ := T.length - A.length;
          let yLength : ℕ := min (A.length + (ell - (1 : ℕ))) T.length;
          let Y : TreeSequence G e0 :=
            TreeSequencePrefix T yLength
              (have hA : (1 : ℕ) ≤ A.length := A.positive;
              have hT : (1 : ℕ) ≤ T.length := T.positive;
              Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ yLength) ↦ by omega)
              (by omega);
          alpha ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T alpha)) ∧
              (↑(HierarchyFirstMissingPosition phi T alpha) : ℕ) ≤ Y.length →
            beta ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T beta)) ∧
                (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ Y.length →
              let _ : Set (V ⊕ E) := TwoColorComponent G phi alpha beta (Sum.inl vb);
              let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G phi alpha beta
                  (Sum.inl vb);
              ∀ (f : E) (c : Fin k), c ≠ alpha → c ≠ beta → (sigma f = some c ↔ phi f = some c)

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev swappedColoringOneUncoloredStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
        [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
        (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
        (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
      IsOneEdgeUncolored phi e0 →
      ∀ (alpha beta : Fin k),
      alpha ≠ beta →
      let H : TashkinovHierarchy ett base := C.hierarchy;
      let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
      let A : TreeSequence G e0 := HierarchyStarredStage H q;
      let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
      let vb : V := T.vertex ib;
      let ell : ℕ := T.length - A.length;
      let yLength : ℕ := min (A.length + (ell - (1 : ℕ))) T.length;
      let Y : TreeSequence G e0 :=
        TreeSequencePrefix T yLength
          (have hA : (1 : ℕ) ≤ A.length := A.positive;
          have hT : (1 : ℕ) ≤ T.length := T.positive;
          Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ yLength) ↦ by omega)
          (by omega);
      alpha ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T alpha)) ∧
          (↑(HierarchyFirstMissingPosition phi T alpha) : ℕ) ≤ Y.length →
      beta ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T beta)) ∧
          (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ Y.length →
      let _ : Set (V ⊕ E) := TwoColorComponent G phi alpha beta (Sum.inl vb);
      let sigma : PartialEdgeColoring E k :=
        TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
      (∀ (f : E) (c : Fin k), c ≠ alpha → c ≠ beta → (sigma f = some c ↔ phi f = some c)) →
      IsOneEdgeUncolored sigma e0

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev notMissingBeforeFirstPositionStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
        [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
        (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
        (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
        (alpha beta : Fin k),
      alpha ≠ beta →
      let H : TashkinovHierarchy ett base := C.hierarchy;
      let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
      let A : TreeSequence G e0 := HierarchyStarredStage H q;
      let ia : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T alpha;
      let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
      let va : V := T.vertex ia;
      let vb : V := T.vertex ib;
      let ell : ℕ := T.length - A.length;
      let yLength : ℕ := min (A.length + (ell - (1 : ℕ))) T.length;
      let Y : TreeSequence G e0 :=
        TreeSequencePrefix T yLength
          (have hA : (1 : ℕ) ≤ A.length := A.positive;
          have hT : (1 : ℕ) ≤ T.length := T.positive;
          Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ yLength) ↦ by omega)
          (by omega);
      ColoredVertexSetElementary G phi (TreeSequenceVertexSet Y) →
      alpha ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T alpha)) ∧
          (↑(HierarchyFirstMissingPosition phi T alpha) : ℕ) ≤ Y.length →
      beta ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T beta)) ∧
          (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ Y.length →
      va ∈ TreeSequenceVertexSet Y →
      vb ∈ TreeSequenceVertexSet Y →
      ∀ (hAib : A.length < (↑ib : ℕ)),
      let B : TreeSequence G e0 :=
        TreeSequencePrefix T (↑ib : ℕ)
          (have this : (1 : ℕ) ≤ A.length := A.positive;
          Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
          (by omega);
      TreeSequenceInitialSegment B Y →
      let K : Set (V ⊕ E) := TwoColorComponent G phi alpha beta (Sum.inl vb);
      let sigma : PartialEdgeColoring E k :=
        TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
      Sum.inl va ∉ K →
      (have C : Set (V ⊕ E) := TwoColorComponent G phi alpha beta (Sum.inl vb);
        have phi' : PartialEdgeColoring E k :=
          TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
        (∀ (v : V), Sum.inl v ∉ C → MissingColors G phi' v = MissingColors G phi v) ∧
          (∀ (v : V),
              Sum.inl v ∈ C → alpha ∈ MissingColors G phi v → beta ∈ MissingColors G phi' v) ∧
            (∀ (v : V),
                Sum.inl v ∈ C →
                  beta ∈ MissingColors G phi v → alpha ∈ MissingColors G phi' v) ∧
              ∀ (v : V) (c : Fin k),
                c ≠ alpha →
                  c ≠ beta → (c ∈ MissingColors G phi' v ↔ c ∈ MissingColors G phi v)) →
      (∀ {v : V} {f : E},
          Sum.inl v ∈ K →
            Incident G v f → phi f = some alpha ∨ phi f = some beta → Sum.inr f ∈ K) →
      ∀ v ∈ TreeSequenceVertexSet B,
      v ≠ vb →
      MissingColors G sigma v = MissingColors G phi v

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev routeTransportStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
        [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
        (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
        (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
        (alpha beta : Fin k),
      let H : TashkinovHierarchy ett base := C.hierarchy;
      let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
      let A : TreeSequence G e0 := HierarchyStarredStage H q;
      let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
      let vb : V := T.vertex ib;
      (∀ {S U W : TreeSequence G e0},
          TreeSequenceInitialSegment S U →
            TreeSequenceInitialSegment U W → TreeSequenceInitialSegment S W) →
      ∀ (hAib : A.length < (↑ib : ℕ)),
      let B : TreeSequence G e0 :=
        TreeSequencePrefix T (↑ib : ℕ)
          (have this : (1 : ℕ) ≤ A.length := A.positive;
          Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
          (by omega);
      TreeSequenceInitialSegment B T →
      let sigma : PartialEdgeColoring E k :=
        TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
      (∀ v ∈ TreeSequenceVertexSet B,
          v ≠ vb → MissingColors G sigma v = MissingColors G phi v) →
      (∀ (t : Fin B.length), sigma (B.edge t) = phi (B.edge t)) →
      ∀ (S : TreeSequence G e0),
      TashkinovAugmentationSequence phi S B →
      TashkinovAugmentationSequence sigma S B

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev storedColorsAtReplacementStageStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
        [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
        (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
        (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
        (alpha beta : Fin k),
      let H : TashkinovHierarchy ett base := C.hierarchy;
      let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
      let A : TreeSequence G e0 := HierarchyStarredStage H q;
      let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
      let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
      let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
      let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
      let vb : V := T.vertex ib;
      TreeSequenceInitialSegment Tn A →
      ∀ (hAib : A.length < (↑ib : ℕ)),
      let B : TreeSequence G e0 :=
        TreeSequencePrefix T (↑ib : ℕ)
          (have this : (1 : ℕ) ≤ A.length := A.positive;
          Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
          (by omega);
      ∀ (rpB : (1 : ℕ) ≤ ett.1)
        (aboveB :
          TreeSequenceInitialSegment
            (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
        (strictB :
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
            B.length)
        (belowB :
          TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
        (genB : phi = ett.series.data.coloring (Fin.last ett.1)),
      let ettB : ExtendedTashkinovTree G k e0 input B phi :=
        { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
          abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
          generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi };
      let sigma : PartialEdgeColoring E k :=
        TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
      (∀ (S : TreeSequence G e0),
          TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A →
            TreeMissingColors sigma S = TreeMissingColors phi S) →
      ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B),
      TashkinovStoredColors corr.replacementETT.series.data
          (Fin.last corr.replacementETT.rounds) =
        Dn

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev replacementStageInitialSegmentOfPrefixStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
        [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
        (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
        (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (_ beta : Fin k),
      let H : TashkinovHierarchy ett base := C.hierarchy;
      let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
      let A : TreeSequence G e0 := HierarchyStarredStage H q;
      let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
      (∀ (S : TreeSequence G e0), TreeSequenceInitialSegment S S) →
      (∀ {S U W : TreeSequence G e0},
          TreeSequenceInitialSegment S U →
            TreeSequenceInitialSegment U W → TreeSequenceInitialSegment S W) →
      ∀ (hAib : A.length < (↑ib : ℕ)),
      let B : TreeSequence G e0 :=
        TreeSequencePrefix T (↑ib : ℕ)
          (have this : (1 : ℕ) ≤ A.length := A.positive;
          Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
          (by omega);
      ∀ (rpB : (1 : ℕ) ≤ ett.1)
        (aboveB :
          TreeSequenceInitialSegment
            (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
        (strictB :
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
            B.length)
        (belowB :
          TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
        (genB : phi = ett.series.data.coloring (Fin.last ett.1))
        (baseB :
          HierarchyBase
            { rounds := ett.1, roundsPositive := rpB, series := ett.series,
              abovePenultimate := aboveB, strictAbovePenultimate := strictB,
              belowFinal := belowB, generatingColoring := genB :
              ExtendedTashkinovTree G k e0 input B phi }
            phi)
        (HB :
          TashkinovHierarchy
            { rounds := ett.1, roundsPositive := rpB, series := ett.series,
              abovePenultimate := aboveB, strictAbovePenultimate := strictB,
              belowFinal := belowB, generatingColoring := genB :
              ExtendedTashkinovTree G k e0 input B phi }
            baseB)
        (j : Fin (HB.dividerCount + (2 : ℕ))),
      TreeSequenceInitialSegment (HB.stage j) B

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev closureInitialSegmentOfStarredStageStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
        [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
        (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
        (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (_ beta : Fin k),
      let H : TashkinovHierarchy ett base := C.hierarchy;
      let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
      let A : TreeSequence G e0 := HierarchyStarredStage H q;
      let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
      let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
      TreeSequenceInitialSegment base.core A →
      ∀ (hAib : A.length < (↑ib : ℕ)),
      let B : TreeSequence G e0 :=
        TreeSequencePrefix T (↑ib : ℕ)
          (have this : (1 : ℕ) ≤ A.length := A.positive;
          Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
          (by omega);
      ∀ (rpB : (1 : ℕ) ≤ ett.1)
        (aboveB :
          TreeSequenceInitialSegment
            (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
        (strictB :
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
            B.length)
        (belowB :
          TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
        (genB : phi = ett.series.data.coloring (Fin.last ett.1))
        (baseB :
          HierarchyBase
            { rounds := ett.1, roundsPositive := rpB, series := ett.series,
              abovePenultimate := aboveB, strictAbovePenultimate := strictB,
              belowFinal := belowB, generatingColoring := genB :
              ExtendedTashkinovTree G k e0 input B phi }
            phi),
      baseB.core = base.core →
      ett.series.data.kind n = some TashkinovExtensionKind.PE →
      TreeSequenceVertexSet baseB.closure ⊆ TreeSequenceVertexSet A

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev storedColorsEqualityStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
        [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
        (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
        (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
        (alpha beta : Fin k),
      let H : TashkinovHierarchy ett base := C.hierarchy;
      let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
      let A : TreeSequence G e0 := HierarchyStarredStage H q;
      let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
      let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
      let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
      let vb : V := T.vertex ib;
      ∀ (hAib : A.length < (↑ib : ℕ)),
      let B : TreeSequence G e0 :=
        TreeSequencePrefix T (↑ib : ℕ)
          (have this : (1 : ℕ) ≤ A.length := A.positive;
          Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
          (by omega);
      ∀ (rpB : (1 : ℕ) ≤ ett.1)
        (aboveB :
          TreeSequenceInitialSegment
            (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
        (strictB :
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
            B.length)
        (belowB :
          TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
        (genB : phi = ett.series.data.coloring (Fin.last ett.1))
        (baseB :
          HierarchyBase
            { rounds := ett.1, roundsPositive := rpB, series := ett.series,
              abovePenultimate := aboveB, strictAbovePenultimate := strictB,
              belowFinal := belowB, generatingColoring := genB :
              ExtendedTashkinovTree G k e0 input B phi }
            phi),
      let ettB : ExtendedTashkinovTree G k e0 input B phi :=
        { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
          abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
          generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi };
      let sigma : PartialEdgeColoring E k :=
        TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
      (∀ (S : TreeSequence G e0),
          TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A →
            TreeMissingColors sigma S = TreeMissingColors phi S) →
      ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B)
        (baseS : HierarchyBase corr.replacementETT sigma),
      TashkinovStoredColors corr.replacementETT.series.data
            (Fin.last corr.replacementETT.rounds) =
          Dn →
      ∀ (count : ℕ) (stages : Fin (count + (2 : ℕ)) → TreeSequence G e0)
        (hbbase :
          stages (0 : Fin (count + (2 : ℕ))) =
            { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                  abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                  belowFinal := belowB, generatingColoring := genB :
                  ExtendedTashkinovTree G k e0 input B phi }.series.data.tree
              (Fin.last
                  { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                      abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                      belowFinal := belowB, generatingColoring := genB :
                      ExtendedTashkinovTree G k e0 input B phi }.rounds).castSucc)
        (hbterminal : stages (Fin.last (count + (1 : ℕ))) = B)
        (hbnested :
          ∀ (j : Fin (count + (1 : ℕ))),
            TreeSequenceInitialSegment (stages j.castSucc) (stages j.succ))
        (hbstrict :
          ∀ (j : Fin (count + (1 : ℕ))), (stages j.castSucc).length < (stages j.succ).length)
        (positions : Fin count → Fin (B.length + (1 : ℕ)))
        (hbpositive : ∀ (i : Fin count), (1 : ℕ) ≤ (↑(positions i) : ℕ))
        (hbincreasing :
          ∀ (i j : Fin count),
            (↑i : ℕ) < (↑j : ℕ) → (↑(positions i) : ℕ) < (↑(positions j) : ℕ))
        (hbdivider :
          ∀ (i : Fin count),
            stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
              TreeSequencePrefix B (↑(positions i) : ℕ) (hbpositive i) (by omega))
        (hbcore :
          TreeSequenceInitialSegment baseB.core
            (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
      (∀
          (j :
            Fin
              ({ dividerCount := count, stage := stages, baseStage := hbbase,
                    terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
                    dividerPosition := positions, dividerPositive := hbpositive,
                    dividerIncreasing := hbincreasing, dividerStage := hbdivider,
                    coreInsideFirst := hbcore :
                    TashkinovHierarchy
                      { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                        abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                        belowFinal := belowB, generatingColoring := genB :
                        ExtendedTashkinovTree G k e0 input B phi }
                      baseB }.dividerCount +
                (1 : ℕ))),
          TreeSequenceInitialSegment
            (HierarchyStarredStage
              { dividerCount := count, stage := stages, baseStage := hbbase,
                terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
                dividerPosition := positions, dividerPositive := hbpositive,
                dividerIncreasing := hbincreasing, dividerStage := hbdivider,
                coreInsideFirst := hbcore :
                TashkinovHierarchy
                  { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                    abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                    belowFinal := belowB, generatingColoring := genB :
                    ExtendedTashkinovTree G k e0 input B phi }
                  baseB }
              j)
            A) →
      ∀ (positionsS : Fin count → Fin (B.length + (1 : ℕ)))
        (hspositive : ∀ (i : Fin count), (1 : ℕ) ≤ (↑(positionsS i) : ℕ))
        (hsincreasing :
          ∀ (i j : Fin count),
            (↑i : ℕ) < (↑j : ℕ) → (↑(positionsS i) : ℕ) < (↑(positionsS j) : ℕ))
        (hsbase :
          stages (0 : Fin (count + (2 : ℕ))) =
            corr.replacementETT.series.data.tree
              (Fin.last corr.replacementETT.rounds).castSucc)
        (hsterminal : stages (Fin.last (count + (1 : ℕ))) = B)
        (hsnested :
          ∀ (j : Fin (count + (1 : ℕ))),
            TreeSequenceInitialSegment (stages j.castSucc) (stages j.succ))
        (hsstrict :
          ∀ (j : Fin (count + (1 : ℕ))), (stages j.castSucc).length < (stages j.succ).length)
        (hsdivider :
          ∀ (i : Fin count),
            stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
              TreeSequencePrefix B (↑(positionsS i) : ℕ) (hspositive i) (by omega))
        (hscore :
          TreeSequenceInitialSegment baseS.core
            (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
      let HB : TashkinovHierarchy ettB baseB :=
        { dividerCount := count, stage := stages, baseStage := hbbase,
          terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
          dividerPosition := positions, dividerPositive := hbpositive,
          dividerIncreasing := hbincreasing, dividerStage := hbdivider,
          coreInsideFirst := hbcore : TashkinovHierarchy ettB baseB };
      let HS : TashkinovHierarchy corr.replacementETT baseS :=
        { dividerCount := count, stage := stages, baseStage := hsbase,
          terminalStage := hsterminal, nested := hsnested, strict := hsstrict,
          dividerPosition := positionsS, dividerPositive := hspositive,
          dividerIncreasing := hsincreasing, dividerStage := hsdivider,
          coreInsideFirst := hscore : TashkinovHierarchy corr.replacementETT baseS };
      (∀ (j : Fin (count + (1 : ℕ))),
          HierarchyStarredStage HS j = HierarchyStarredStage HB j) →
      ∀ (j : Fin (count + (1 : ℕ))),
      HierarchyStoredColorsAt HS j = HierarchyStoredColorsAt HB j

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev missingColorsEqualityStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
        [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
        (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
        (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
        (alpha beta : Fin k),
      let H : TashkinovHierarchy ett base := C.hierarchy;
      let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
      let A : TreeSequence G e0 := HierarchyStarredStage H q;
      let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
      let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
      let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
      let vb : V := T.vertex ib;
      TreeSequenceInitialSegment Tn A →
      ∀ (hAib : A.length < (↑ib : ℕ)),
      let B : TreeSequence G e0 :=
        TreeSequencePrefix T (↑ib : ℕ)
          (have this : (1 : ℕ) ≤ A.length := A.positive;
          Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
          (by omega);
      ∀ (rpB : (1 : ℕ) ≤ ett.1)
        (aboveB :
          TreeSequenceInitialSegment
            (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
        (strictB :
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
            B.length)
        (belowB :
          TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
        (genB : phi = ett.series.data.coloring (Fin.last ett.1))
        (baseB :
          HierarchyBase
            { rounds := ett.1, roundsPositive := rpB, series := ett.series,
              abovePenultimate := aboveB, strictAbovePenultimate := strictB,
              belowFinal := belowB, generatingColoring := genB :
              ExtendedTashkinovTree G k e0 input B phi }
            phi),
      let ettB : ExtendedTashkinovTree G k e0 input B phi :=
        { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
          abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
          generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi };
      let sigma : PartialEdgeColoring E k :=
        TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
      (∀ (S : TreeSequence G e0),
          TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A →
            TreeMissingColors sigma S = TreeMissingColors phi S) →
      ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B)
        (baseS : HierarchyBase corr.replacementETT sigma) (count : ℕ)
        (stages : Fin (count + (2 : ℕ)) → TreeSequence G e0)
        (hbbase :
          stages (0 : Fin (count + (2 : ℕ))) =
            { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                  abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                  belowFinal := belowB, generatingColoring := genB :
                  ExtendedTashkinovTree G k e0 input B phi }.series.data.tree
              (Fin.last
                  { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                      abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                      belowFinal := belowB, generatingColoring := genB :
                      ExtendedTashkinovTree G k e0 input B phi }.rounds).castSucc)
        (hbterminal : stages (Fin.last (count + (1 : ℕ))) = B)
        (hbnested :
          ∀ (j : Fin (count + (1 : ℕ))),
            TreeSequenceInitialSegment (stages j.castSucc) (stages j.succ))
        (hbstrict :
          ∀ (j : Fin (count + (1 : ℕ))), (stages j.castSucc).length < (stages j.succ).length)
        (positions : Fin count → Fin (B.length + (1 : ℕ)))
        (hbpositive : ∀ (i : Fin count), (1 : ℕ) ≤ (↑(positions i) : ℕ))
        (hbincreasing :
          ∀ (i j : Fin count),
            (↑i : ℕ) < (↑j : ℕ) → (↑(positions i) : ℕ) < (↑(positions j) : ℕ))
        (hbdivider :
          ∀ (i : Fin count),
            stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
              TreeSequencePrefix B (↑(positions i) : ℕ) (hbpositive i) (by omega))
        (hbcore :
          TreeSequenceInitialSegment baseB.core
            (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
      (∀
          (j :
            Fin
              ({ dividerCount := count, stage := stages, baseStage := hbbase,
                    terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
                    dividerPosition := positions, dividerPositive := hbpositive,
                    dividerIncreasing := hbincreasing, dividerStage := hbdivider,
                    coreInsideFirst := hbcore :
                    TashkinovHierarchy
                      { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                        abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                        belowFinal := belowB, generatingColoring := genB :
                        ExtendedTashkinovTree G k e0 input B phi }
                      baseB }.dividerCount +
                (1 : ℕ))),
          TreeSequenceInitialSegment
            ({ dividerCount := count, stage := stages, baseStage := hbbase,
                  terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
                  dividerPosition := positions, dividerPositive := hbpositive,
                  dividerIncreasing := hbincreasing, dividerStage := hbdivider,
                  coreInsideFirst := hbcore :
                  TashkinovHierarchy
                    { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                      abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                      belowFinal := belowB, generatingColoring := genB :
                      ExtendedTashkinovTree G k e0 input B phi }
                    baseB }.stage
              j.castSucc)
            A) →
      ∀ (positionsS : Fin count → Fin (B.length + (1 : ℕ)))
        (hspositive : ∀ (i : Fin count), (1 : ℕ) ≤ (↑(positionsS i) : ℕ))
        (hsincreasing :
          ∀ (i j : Fin count),
            (↑i : ℕ) < (↑j : ℕ) → (↑(positionsS i) : ℕ) < (↑(positionsS j) : ℕ))
        (hsbase :
          stages (0 : Fin (count + (2 : ℕ))) =
            corr.replacementETT.series.data.tree
              (Fin.last corr.replacementETT.rounds).castSucc)
        (hsterminal : stages (Fin.last (count + (1 : ℕ))) = B)
        (hsnested :
          ∀ (j : Fin (count + (1 : ℕ))),
            TreeSequenceInitialSegment (stages j.castSucc) (stages j.succ))
        (hsstrict :
          ∀ (j : Fin (count + (1 : ℕ))), (stages j.castSucc).length < (stages j.succ).length)
        (hsdivider :
          ∀ (i : Fin count),
            stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
              TreeSequencePrefix B (↑(positionsS i) : ℕ) (hspositive i) (by omega))
        (hscore :
          TreeSequenceInitialSegment baseS.core
            (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
      let HB : TashkinovHierarchy ettB baseB :=
        { dividerCount := count, stage := stages, baseStage := hbbase,
          terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
          dividerPosition := positions, dividerPositive := hbpositive,
          dividerIncreasing := hbincreasing, dividerStage := hbdivider,
          coreInsideFirst := hbcore : TashkinovHierarchy ettB baseB };
      let HS : TashkinovHierarchy corr.replacementETT baseS :=
        { dividerCount := count, stage := stages, baseStage := hsbase,
          terminalStage := hsterminal, nested := hsnested, strict := hsstrict,
          dividerPosition := positionsS, dividerPositive := hspositive,
          dividerIncreasing := hsincreasing, dividerStage := hsdivider,
          coreInsideFirst := hscore : TashkinovHierarchy corr.replacementETT baseS };
      ∀ (j : Fin (count + (1 : ℕ))),
      HierarchyStageMissingColors HS j = HierarchyStageMissingColors HB j

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev firstMissingPositionUpperBoundStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
        [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
        (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
        (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (_ beta : Fin k),
      let H : TashkinovHierarchy ett base := C.hierarchy;
      let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
      let A : TreeSequence G e0 := HierarchyStarredStage H q;
      let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
      ∀ (hAib : A.length < (↑ib : ℕ)),
      let B : TreeSequence G e0 :=
        TreeSequencePrefix T (↑ib : ℕ)
          (have this : (1 : ℕ) ≤ A.length := A.positive;
          Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
          (by omega);
      ∀ (psi : PartialEdgeColoring E k) (eta : Fin k) (i : Fin (B.length + (1 : ℕ))),
      eta ∈ MissingColors G psi (B.vertex i) →
      (↑(HierarchyFirstMissingPosition psi B eta) : ℕ) ≤ (↑i : ℕ)

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev beforeFirstMissingPositionStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
        [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
        (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
        (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (_ beta : Fin k),
      let H : TashkinovHierarchy ett base := C.hierarchy;
      let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
      let A : TreeSequence G e0 := HierarchyStarredStage H q;
      let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
      ∀ (hAib : A.length < (↑ib : ℕ)),
      let B : TreeSequence G e0 :=
        TreeSequencePrefix T (↑ib : ℕ)
          (have this : (1 : ℕ) ≤ A.length := A.positive;
          Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
          (by omega);
      ∀ (psi : PartialEdgeColoring E k) (eta : Fin k),
      (↑(HierarchyFirstMissingPosition psi B eta) : ℕ) < B.length →
      eta ∈ MissingColors G psi (B.vertex (HierarchyFirstMissingPosition psi B eta))

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev firstMissingPositionEqualityStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
        [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
        (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
        (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
        (alpha beta : Fin k),
      let H : TashkinovHierarchy ett base := C.hierarchy;
      let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
      let A : TreeSequence G e0 := HierarchyStarredStage H q;
      let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
      let vb : V := T.vertex ib;
      ∀ (hAib : A.length < (↑ib : ℕ)),
      let B : TreeSequence G e0 :=
        TreeSequencePrefix T (↑ib : ℕ)
          (have this : (1 : ℕ) ≤ A.length := A.positive;
          Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
          (by omega);
      TreeSequenceInitialSegment B T →
      let sigma : PartialEdgeColoring E k :=
        TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
      (∀ v ∈ TreeSequenceVertexSet B,
          v ≠ vb → MissingColors G sigma v = MissingColors G phi v) →
      (∀ (psi : PartialEdgeColoring E k) (eta : Fin k) (i : Fin (B.length + (1 : ℕ))),
          eta ∈ MissingColors G psi (B.vertex i) →
            (↑(HierarchyFirstMissingPosition psi B eta) : ℕ) ≤ (↑i : ℕ)) →
      (∀ (psi : PartialEdgeColoring E k) (eta : Fin k),
          (↑(HierarchyFirstMissingPosition psi B eta) : ℕ) < B.length →
            eta ∈ MissingColors G psi (B.vertex (HierarchyFirstMissingPosition psi B eta))) →
      ∀ (eta : Fin k),
      HierarchyFirstMissingPosition sigma B eta = HierarchyFirstMissingPosition phi B eta

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev initialSegmentEqualityStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
        [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
        (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
        (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
        (alpha beta : Fin k),
      let H : TashkinovHierarchy ett base := C.hierarchy;
      let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
      let A : TreeSequence G e0 := HierarchyStarredStage H q;
      let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
      let vb : V := T.vertex ib;
      ∀ (hAib : A.length < (↑ib : ℕ)),
      let B : TreeSequence G e0 :=
        TreeSequencePrefix T (↑ib : ℕ)
          (have this : (1 : ℕ) ≤ A.length := A.positive;
          Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
          (by omega);
      ∀ (rpB : (1 : ℕ) ≤ ett.1)
        (aboveB :
          TreeSequenceInitialSegment
            (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
        (strictB :
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
            B.length)
        (belowB :
          TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
        (genB : phi = ett.series.data.coloring (Fin.last ett.1))
        (baseB :
          HierarchyBase
            { rounds := ett.1, roundsPositive := rpB, series := ett.series,
              abovePenultimate := aboveB, strictAbovePenultimate := strictB,
              belowFinal := belowB, generatingColoring := genB :
              ExtendedTashkinovTree G k e0 input B phi }
            phi),
      let ettB : ExtendedTashkinovTree G k e0 input B phi :=
        { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
          abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
          generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi };
      let sigma : PartialEdgeColoring E k :=
        TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
      (∀ (t : Fin B.length), sigma (B.edge t) = phi (B.edge t)) →
      ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B)
        (baseS : HierarchyBase corr.replacementETT sigma) (count : ℕ)
        (stages : Fin (count + (2 : ℕ)) → TreeSequence G e0)
        (hbbase :
          stages (0 : Fin (count + (2 : ℕ))) =
            { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                  abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                  belowFinal := belowB, generatingColoring := genB :
                  ExtendedTashkinovTree G k e0 input B phi }.series.data.tree
              (Fin.last
                  { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                      abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                      belowFinal := belowB, generatingColoring := genB :
                      ExtendedTashkinovTree G k e0 input B phi }.rounds).castSucc)
        (hbterminal : stages (Fin.last (count + (1 : ℕ))) = B)
        (hbnested :
          ∀ (j : Fin (count + (1 : ℕ))),
            TreeSequenceInitialSegment (stages j.castSucc) (stages j.succ))
        (hbstrict :
          ∀ (j : Fin (count + (1 : ℕ))), (stages j.castSucc).length < (stages j.succ).length)
        (positions : Fin count → Fin (B.length + (1 : ℕ)))
        (hbpositive : ∀ (i : Fin count), (1 : ℕ) ≤ (↑(positions i) : ℕ))
        (hbincreasing :
          ∀ (i j : Fin count),
            (↑i : ℕ) < (↑j : ℕ) → (↑(positions i) : ℕ) < (↑(positions j) : ℕ))
        (hbdivider :
          ∀ (i : Fin count),
            stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
              TreeSequencePrefix B (↑(positions i) : ℕ) (hbpositive i) (by omega))
        (hbcore :
          TreeSequenceInitialSegment baseB.core
            (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
      (∀
          (j :
            Fin
              ({ dividerCount := count, stage := stages, baseStage := hbbase,
                    terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
                    dividerPosition := positions, dividerPositive := hbpositive,
                    dividerIncreasing := hbincreasing, dividerStage := hbdivider,
                    coreInsideFirst := hbcore :
                    TashkinovHierarchy
                      { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                        abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                        belowFinal := belowB, generatingColoring := genB :
                        ExtendedTashkinovTree G k e0 input B phi }
                      baseB }.dividerCount +
                (2 : ℕ))),
          TreeSequenceInitialSegment
            ({ dividerCount := count, stage := stages, baseStage := hbbase,
                  terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
                  dividerPosition := positions, dividerPositive := hbpositive,
                  dividerIncreasing := hbincreasing, dividerStage := hbdivider,
                  coreInsideFirst := hbcore :
                  TashkinovHierarchy
                    { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                      abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                      belowFinal := belowB, generatingColoring := genB :
                      ExtendedTashkinovTree G k e0 input B phi }
                    baseB }.stage
              j)
            B) →
      ∀ (positionsS : Fin count → Fin (B.length + (1 : ℕ)))
        (hspositive : ∀ (i : Fin count), (1 : ℕ) ≤ (↑(positionsS i) : ℕ))
        (hsincreasing :
          ∀ (i j : Fin count),
            (↑i : ℕ) < (↑j : ℕ) → (↑(positionsS i) : ℕ) < (↑(positionsS j) : ℕ))
        (hsbase :
          stages (0 : Fin (count + (2 : ℕ))) =
            corr.replacementETT.series.data.tree
              (Fin.last corr.replacementETT.rounds).castSucc)
        (hsterminal : stages (Fin.last (count + (1 : ℕ))) = B)
        (hsnested :
          ∀ (j : Fin (count + (1 : ℕ))),
            TreeSequenceInitialSegment (stages j.castSucc) (stages j.succ))
        (hsstrict :
          ∀ (j : Fin (count + (1 : ℕ))), (stages j.castSucc).length < (stages j.succ).length)
        (hsdivider :
          ∀ (i : Fin count),
            stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
              TreeSequencePrefix B (↑(positionsS i) : ℕ) (hspositive i) (by omega))
        (hscore :
          TreeSequenceInitialSegment baseS.core
            (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
      let HB : TashkinovHierarchy ettB baseB :=
        { dividerCount := count, stage := stages, baseStage := hbbase,
          terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
          dividerPosition := positions, dividerPositive := hbpositive,
          dividerIncreasing := hbincreasing, dividerStage := hbdivider,
          coreInsideFirst := hbcore : TashkinovHierarchy ettB baseB };
      let HS : TashkinovHierarchy corr.replacementETT baseS :=
        { dividerCount := count, stage := stages, baseStage := hsbase,
          terminalStage := hsterminal, nested := hsnested, strict := hsstrict,
          dividerPosition := positionsS, dividerPositive := hspositive,
          dividerIncreasing := hsincreasing, dividerStage := hsdivider,
          coreInsideFirst := hscore : TashkinovHierarchy corr.replacementETT baseS };
      (∀ (j : Fin (count + (1 : ℕ))),
          HierarchyStarredStage HS j = HierarchyStarredStage HB j) →
      (∀ (eta : Fin k),
          HierarchyFirstMissingPosition sigma B eta =
            HierarchyFirstMissingPosition phi B eta) →
      ∀ (j : Fin (count + (1 : ℕ))) (eta : Fin k),
      HierarchySegmentColors HS j eta = HierarchySegmentColors HB j eta

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev refreshedHierarchyEqualityStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
        [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
        (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
        (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
        (alpha beta : Fin k),
      let H : TashkinovHierarchy ett base := C.hierarchy;
      let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
      let A : TreeSequence G e0 := HierarchyStarredStage H q;
      let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
      let vb : V := T.vertex ib;
      ∀ (hAib : A.length < (↑ib : ℕ)),
      let B : TreeSequence G e0 :=
        TreeSequencePrefix T (↑ib : ℕ)
          (have this : (1 : ℕ) ≤ A.length := A.positive;
          Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
          (by omega);
      ∀ (rpB : (1 : ℕ) ≤ ett.1)
        (aboveB :
          TreeSequenceInitialSegment
            (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
        (strictB :
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
            B.length)
        (belowB :
          TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
        (genB : phi = ett.series.data.coloring (Fin.last ett.1))
        (baseB :
          HierarchyBase
            { rounds := ett.1, roundsPositive := rpB, series := ett.series,
              abovePenultimate := aboveB, strictAbovePenultimate := strictB,
              belowFinal := belowB, generatingColoring := genB :
              ExtendedTashkinovTree G k e0 input B phi }
            phi),
      let ettB : ExtendedTashkinovTree G k e0 input B phi :=
        { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
          abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
          generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi };
      let sigma : PartialEdgeColoring E k :=
        TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
      (∀ v ∈ TreeSequenceVertexSet A, MissingColors G sigma v = MissingColors G phi v) →
      ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B)
        (baseS : HierarchyBase corr.replacementETT sigma) (count : ℕ)
        (stages : Fin (count + (2 : ℕ)) → TreeSequence G e0)
        (hbbase :
          stages (0 : Fin (count + (2 : ℕ))) =
            { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                  abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                  belowFinal := belowB, generatingColoring := genB :
                  ExtendedTashkinovTree G k e0 input B phi }.series.data.tree
              (Fin.last
                  { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                      abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                      belowFinal := belowB, generatingColoring := genB :
                      ExtendedTashkinovTree G k e0 input B phi }.rounds).castSucc)
        (hbterminal : stages (Fin.last (count + (1 : ℕ))) = B)
        (hbnested :
          ∀ (j : Fin (count + (1 : ℕ))),
            TreeSequenceInitialSegment (stages j.castSucc) (stages j.succ))
        (hbstrict :
          ∀ (j : Fin (count + (1 : ℕ))), (stages j.castSucc).length < (stages j.succ).length)
        (positions : Fin count → Fin (B.length + (1 : ℕ)))
        (hbpositive : ∀ (i : Fin count), (1 : ℕ) ≤ (↑(positions i) : ℕ))
        (hbincreasing :
          ∀ (i j : Fin count),
            (↑i : ℕ) < (↑j : ℕ) → (↑(positions i) : ℕ) < (↑(positions j) : ℕ))
        (hbdivider :
          ∀ (i : Fin count),
            stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
              TreeSequencePrefix B (↑(positions i) : ℕ) (hbpositive i) (by omega))
        (hbcore :
          TreeSequenceInitialSegment baseB.core
            (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
      (∀
          (j :
            Fin
              ({ dividerCount := count, stage := stages, baseStage := hbbase,
                    terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
                    dividerPosition := positions, dividerPositive := hbpositive,
                    dividerIncreasing := hbincreasing, dividerStage := hbdivider,
                    coreInsideFirst := hbcore :
                    TashkinovHierarchy
                      { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                        abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                        belowFinal := belowB, generatingColoring := genB :
                        ExtendedTashkinovTree G k e0 input B phi }
                      baseB }.dividerCount +
                (1 : ℕ))),
          TreeSequenceInitialSegment
            ({ dividerCount := count, stage := stages, baseStage := hbbase,
                  terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
                  dividerPosition := positions, dividerPositive := hbpositive,
                  dividerIncreasing := hbincreasing, dividerStage := hbdivider,
                  coreInsideFirst := hbcore :
                  TashkinovHierarchy
                    { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                      abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                      belowFinal := belowB, generatingColoring := genB :
                      ExtendedTashkinovTree G k e0 input B phi }
                    baseB }.stage
              j.castSucc)
            A) →
      ∀ (positionsS : Fin count → Fin (B.length + (1 : ℕ)))
        (hspositive : ∀ (i : Fin count), (1 : ℕ) ≤ (↑(positionsS i) : ℕ))
        (hsincreasing :
          ∀ (i j : Fin count),
            (↑i : ℕ) < (↑j : ℕ) → (↑(positionsS i) : ℕ) < (↑(positionsS j) : ℕ))
        (hsbase :
          stages (0 : Fin (count + (2 : ℕ))) =
            corr.replacementETT.series.data.tree
              (Fin.last corr.replacementETT.rounds).castSucc)
        (hsterminal : stages (Fin.last (count + (1 : ℕ))) = B)
        (hsnested :
          ∀ (j : Fin (count + (1 : ℕ))),
            TreeSequenceInitialSegment (stages j.castSucc) (stages j.succ))
        (hsstrict :
          ∀ (j : Fin (count + (1 : ℕ))), (stages j.castSucc).length < (stages j.succ).length)
        (hsdivider :
          ∀ (i : Fin count),
            stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
              TreeSequencePrefix B (↑(positionsS i) : ℕ) (hspositive i) (by omega))
        (hscore :
          TreeSequenceInitialSegment baseS.core
            (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
      let HB : TashkinovHierarchy ettB baseB :=
        { dividerCount := count, stage := stages, baseStage := hbbase,
          terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
          dividerPosition := positions, dividerPositive := hbpositive,
          dividerIncreasing := hbincreasing, dividerStage := hbdivider,
          coreInsideFirst := hbcore : TashkinovHierarchy ettB baseB };
      let HS : TashkinovHierarchy corr.replacementETT baseS :=
        { dividerCount := count, stage := stages, baseStage := hsbase,
          terminalStage := hsterminal, nested := hsnested, strict := hsstrict,
          dividerPosition := positionsS, dividerPositive := hspositive,
          dividerIncreasing := hsincreasing, dividerStage := hsdivider,
          coreInsideFirst := hscore : TashkinovHierarchy corr.replacementETT baseS };
      (∀ (j : Fin (count + (1 : ℕ))),
          HierarchyStarredStage HS j = HierarchyStarredStage HB j) →
      ∀ (i : Fin count),
      ((TreeSequenceVertexSet (HS.stage i.succ.castSucc) \
              TreeSequenceVertexSet (HierarchyStarredStage HS i.castSucc)).biUnion
          fun (v : V) ↦ MissingColors G sigma v) =
        (TreeSequenceVertexSet (HB.stage i.succ.castSucc) \
              TreeSequenceVertexSet (HierarchyStarredStage HB i.castSucc)).biUnion
          fun (v : V) ↦ MissingColors G phi v

end GoldbergSeymour.SharedFacts.MixedChangeTransport

end
