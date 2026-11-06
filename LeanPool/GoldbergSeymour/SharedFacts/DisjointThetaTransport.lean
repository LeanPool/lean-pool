/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchySituationThreeDisjointData
public import LeanPool.GoldbergSeymour.HierarchyCounterexamplePenultimateElementary
public import LeanPool.GoldbergSeymour.HierarchyEligibleCommonMissingIndices
public import LeanPool.GoldbergSeymour.StableChangeCasesOneTwo

/-!
# Shared facts for HierarchySituationThreeDisjointThetaStoredImpossible

These interfaces and proofs are shared across the imported proof branches.
Extracted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12 during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour.SharedFacts.DisjointThetaTransport

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev hthetaFirstIndexStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
          LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
          TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
          input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
          HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
          HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k)
          (d : HierarchySituationThreeDisjointData G k e0 input T phi ett base C ctx P alpha beta)
          (j : ℕ),
      let R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx := d.switched;
      let sigma : PartialEdgeColoring E k := R.coloring;
      let ell : ℕ := HierarchyFullTailLength C;
      let Y : TreeSequence G e0 := HierarchyFullTailPrefix C j;
      let Z : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ)); d.theta ∈
          MissingColors G sigma (Y.vertex (Fin.last Y.length)) → TreeSequenceInitialSegment Y T →
          TreeSequenceInitialSegment Y Z → TreeSequenceInitialSegment Z T →
          ColoredVertexSetElementary G sigma (TreeSequenceVertexSet Z) → (
      ∀ (W : TreeSequence G e0), TreeSequenceInitialSegment W T →
      ∀ (i : Fin (T.length + (1 : ℕ))), (↑i : ℕ) ≤ W.length → T.vertex i ∈ TreeSequenceVertexSet W)
          → d.theta ∈ MissingColors G sigma (T.vertex (HierarchyFirstMissingPosition sigma T
          d.theta)) ∧ (↑(HierarchyFirstMissingPosition sigma T d.theta) : ℕ) ≤ Y.length →
          (↑(HierarchyFirstMissingPosition sigma T d.theta) : ℕ) = Y.length

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev firstWitnessStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (T : TreeSequence G e0)
    (rho : PartialEdgeColoring E k) (W : TreeSequence G e0),
    TreeSequenceInitialSegment W T →
    ∀ c ∈ TreeMissingColors rho W,
    c ∈ MissingColors G rho (T.vertex (HierarchyFirstMissingPosition rho T c)) ∧
      (↑(HierarchyFirstMissingPosition rho T c) : ℕ) ≤ W.length

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev hthetaMissingYStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
          LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
          TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
          input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
          HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
          HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k)
          (d : HierarchySituationThreeDisjointData G k e0 input T phi ett base C ctx P alpha beta)
          (j : ℕ), HierarchyPathNumber C.hierarchy = j →
      let R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx := d.switched;
      let sigma : PartialEdgeColoring E k := R.coloring;
      let Y : TreeSequence G e0 := HierarchyFullTailPrefix C j; d.theta ∈ MissingColors G sigma
          (Y.vertex (Fin.last Y.length))

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev sameStarStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
          LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
          TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
          input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
          HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
          HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k)
          (d : HierarchySituationThreeDisjointData G k e0 input T phi ett base C ctx P alpha beta)
          (j : ℕ),
      let R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx := d.switched;
      let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
          R.counterexample.hierarchy;
      let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
      let A : TreeSequence G e0 := HierarchyStarredStage H q;
      let _ : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ));
      let _ : TreeSequence G e0 := HierarchyFullTailPrefix C j; HierarchyStarredStage C.hierarchy
          (Fin.last C.hierarchy.dividerCount) = A

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev hcutJstrictStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
          LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
          TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
          input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
          HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
          HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k)
          (d : HierarchySituationThreeDisjointData G k e0 input T phi ett base C ctx P alpha beta)
          (j : ℕ), HierarchyPathNumber C.hierarchy = j →
      let R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx := d.switched;
      let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
          R.counterexample.hierarchy;
      let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
      let A : TreeSequence G e0 := HierarchyStarredStage H q;
      let ell : ℕ := HierarchyFullTailLength C; HierarchyStarredStage C.hierarchy (Fin.last
          C.hierarchy.dividerCount) = A → TreeSequenceInitialSegment A T → j < ell → A.length + j <
          T.length

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev prefixToTreeStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
    (T : TreeSequence G e0) (m : ℕ) (hm : (1 : ℕ) ≤ m) (hmT : m ≤ T.length),
    TreeSequenceInitialSegment (TreeSequencePrefix T m hm hmT) T

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev comparableInitialSegmentsStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E) (T : TreeSequence G e0)
          {U W : TreeSequence G e0}, TreeSequenceInitialSegment U T → TreeSequenceInitialSegment W T
          → U.length ≤ W.length → TreeSequenceInitialSegment U W

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev elemZStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
          LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
          TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
          input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
          HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
          HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k)
          (d : HierarchySituationThreeDisjointData G k e0 input T phi ett base C ctx P alpha beta),
      let R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx := d.switched;
      let sigma : PartialEdgeColoring E k := R.coloring;
      let ell : ℕ := HierarchyFullTailLength C;
      let Z : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
          HierarchyFullTailPrefix R.counterexample (HierarchyFullTailLength R.counterexample - (1 :
          ℕ)) = Z → ColoredVertexSetElementary G sigma (TreeSequenceVertexSet Z)

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev vertexMemTStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E) (T W : TreeSequence G
          e0), TreeSequenceInitialSegment W T →
      ∀ (i : Fin (T.length + (1 : ℕ))), (↑i : ℕ) ≤ W.length → T.vertex i ∈ TreeSequenceVertexSet W

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev hthetaYStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
          LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
          TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
          input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
          HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
          HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k)
          (d : HierarchySituationThreeDisjointData G k e0 input T phi ett base C ctx P alpha beta)
          (j : ℕ),
      let R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx := d.switched;
      let sigma : PartialEdgeColoring E k := R.coloring;
      let Y : TreeSequence G e0 := HierarchyFullTailPrefix C j; d.theta ∈ MissingColors G sigma
          (Y.vertex (Fin.last Y.length)) → (
      ∀ (W : TreeSequence G e0) (i : Fin (W.length + (1 : ℕ))), W.vertex i ∈ TreeSequenceVertexSet
          W) → (
      ∀ (rho : PartialEdgeColoring E k) (W : TreeSequence G e0) (v : V) (c : Fin k), v ∈
          TreeSequenceVertexSet W → c ∈ MissingColors G rho v → c ∈ TreeMissingColors rho W) →
          d.theta ∈ TreeMissingColors sigma Y


/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev apositiveStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
          : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
          TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
          input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
          HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
          HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k)
          (d : HierarchySituationThreeDisjointData G k e0 input T phi ett base C ctx P alpha beta),
      let R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx := d.switched;
      let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
          R.counterexample.hierarchy;
      let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
      let A : TreeSequence G e0 := HierarchyStarredStage H q; (0 : ℕ) < H.dividerCount → A = H.stage
          (⟨H.dividerCount,
      by
            have := GoldbergSeymour.TreeSequence.positive T
            omega
      ⟩ : Fin (H.dividerCount + (2 : ℕ)))

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev sameGammaBetaStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
          : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
          TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
          input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
          HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
          HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k)
          (d : HierarchySituationThreeDisjointData G k e0 input T phi ett base C ctx P alpha beta),
      let R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx := d.switched;
      let sigma : PartialEdgeColoring E k := R.coloring;
      let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
          R.counterexample.hierarchy;
      let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
      let A : TreeSequence G e0 := HierarchyStarredStage H q;
      ∀ gamma ∈ TreeMissingColors sigma A, (
      let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
          R.counterexample.hierarchy;
      have q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
      have n : Fin (R.corresponding.replacementETT.rounds + (1 : ℕ)) := Fin.last
          R.corresponding.replacementETT.rounds;
      have A : TreeSequence G e0 := HierarchyStarredStage H q;
      have Tnq : TreeSequence G e0 := H.stage (⟨H.dividerCount,
      by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
      ⟩ : Fin (H.dividerCount + (2 : ℕ)));
      have Tn : TreeSequence G e0 := R.corresponding.replacementETT.series.data.tree n.castSucc;
      have Dn : Finset (Fin k) := TashkinovStoredColors R.corresponding.replacementETT.series.data
          n;
      have Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q;
      have va : V := T.vertex (HierarchyFirstMissingPosition sigma T gamma);
      have vb : V := T.vertex (HierarchyFirstMissingPosition sigma T beta);
      have sameComponent : Prop := TwoColorComponent G sigma gamma beta (Sum.inl va) =
          TwoColorComponent G sigma gamma beta (Sum.inl vb); ( (0 : ℕ) < H.dividerCount ∧ (gamma ∈
          TreeMissingColors sigma Tnq ∨ Disjoint (insert gamma ({ beta } : Finset (Fin k)) : Finset
          (Fin k)) Dnq) → sameComponent) ∧ ( H.dividerCount = (0 : ℕ) ∧ (gamma ∈ TreeMissingColors
          sigma Tn ∨ Disjoint (insert gamma ({ beta } : Finset (Fin k)) : Finset (Fin k)) Dn) →
          sameComponent) ∧ ( gamma ∈ TreeMissingColors sigma A ∧ TreeColorSetClosed G sigma A
          ({ gamma } : Finset (Fin k)) → sameComponent ∧ TreeInterchangeable G A sigma gamma beta))
          → gamma ∈ HierarchyStageMissingColors H q → ( (0 : ℕ) < H.dividerCount → A = H.stage
          (⟨H.dividerCount,
      by
            have := GoldbergSeymour.TreeSequence.positive T
            omega
      ⟩ : Fin (H.dividerCount + (2 : ℕ)))) → TwoColorComponent G sigma gamma beta (Sum.inl (T.vertex
          (HierarchyFirstMissingPosition sigma T gamma))) = TwoColorComponent G sigma gamma beta
          (Sum.inl (T.vertex (HierarchyFirstMissingPosition sigma T beta)))

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev hmu2OneStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
          LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
          TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
          input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
          HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
          HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k)
          (d : HierarchySituationThreeDisjointData G k e0 input T phi ett base C ctx P alpha beta),
      let R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx := d.switched;
      let sigma : PartialEdgeColoring E k := R.coloring;
      ∀ (gamma : Fin k),
      let z : V ⊕ E := Sum.inl (T.vertex (Fin.last T.length));
      let mu2 : PartialEdgeColoring E k := TwoColorComponentSwap G sigma gamma beta z;
          IsOneEdgeUncolored mu2 e0

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev hfirstBetaOutsideStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
          LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
          TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
          input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
          HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
          HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k)
          (d : HierarchySituationThreeDisjointData G k e0 input T phi ett base C ctx P alpha beta),
      let R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx := d.switched;
      let sigma : PartialEdgeColoring E k := R.coloring;
      ∀ (gamma : Fin k), TwoColorComponent G sigma gamma beta (Sum.inl (T.vertex
          (HierarchyFirstMissingPosition sigma T gamma))) = TwoColorComponent G sigma gamma beta
          (Sum.inl (T.vertex (HierarchyFirstMissingPosition sigma T beta))) → (
      ∀ (rho : PartialEdgeColoring E k) (a b : Fin k) (v : V), Sum.inl v ∈ TwoColorComponent G rho a
          b (Sum.inl v)) → Disjoint (TwoColorComponent G sigma gamma beta (Sum.inl (T.vertex
          (Fin.last T.length)))) (TwoColorComponent G sigma gamma beta (Sum.inl (T.vertex
          (HierarchyFirstMissingPosition sigma T gamma)))) →
      let z : V ⊕ E := Sum.inl (T.vertex (Fin.last T.length)); Sum.inl (T.vertex
          (HierarchyFirstMissingPosition sigma T beta)) ∉ TwoColorComponent G sigma gamma beta z

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev firstPreservedStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
          (e0 : E) (T : TreeSequence G e0) (_ : ℕ), (
      ∀ (rho : PartialEdgeColoring E k) (W : TreeSequence G e0), TreeSequenceInitialSegment W T →
      ∀ c ∈ TreeMissingColors rho W, c ∈ MissingColors G rho (T.vertex
          (HierarchyFirstMissingPosition rho T c)) ∧ (↑(HierarchyFirstMissingPosition rho T c) : ℕ)
          ≤ W.length) →
      ∀ (W : TreeSequence G e0), TreeSequenceInitialSegment W T →
      ∀ (rho sigma : PartialEdgeColoring E k) (c : Fin k), ColoredVertexSetElementary G rho
          (TreeSequenceVertexSet W) → (
      ∀ v ∈ TreeSequenceVertexSet W, MissingColors G sigma v = MissingColors G rho v) → c ∈
          TreeMissingColors rho W → HierarchyFirstMissingPosition sigma T c =
          HierarchyFirstMissingPosition rho T c

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev missingTransportStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
          LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
          TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
          input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
      let ell : ℕ := HierarchyFullTailLength C;
      let Z : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
      ∀ (old new : PartialEdgeColoring E k), (
      ∀ v ∈ TreeSequenceVertexSet Z, MissingColors G new v = MissingColors G old v) →
      ∀ (W : TreeSequence G e0), TreeSequenceInitialSegment W Z → TreeMissingColors new W =
          TreeMissingColors old W

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev hstoredMu2Statement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
          LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
          TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
          input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
          HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
          HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k)
          (d : HierarchySituationThreeDisjointData G k e0 input T phi ett base C ctx P alpha beta),
      let R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx := d.switched;
      let sigma : PartialEdgeColoring E k := R.coloring;
      let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
          R.counterexample.hierarchy;
      let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
      let A : TreeSequence G e0 := HierarchyStarredStage H q;
      let ell : ℕ := HierarchyFullTailLength C;
      let Z : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
      let D : Finset (Fin k) := HierarchyStoredColorsAt H q;
      ∀ gamma ∈ TreeMissingColors sigma A, gamma ≠ beta → TreeSequenceInitialSegment Z T →
          ColoredVertexSetElementary G sigma (TreeSequenceVertexSet Z) → beta ∈ TreeMissingColors
          sigma Z →
      let z : V ⊕ E := Sum.inl (T.vertex (Fin.last T.length));
      let mu2 : PartialEdgeColoring E k := TwoColorComponentSwap G sigma gamma beta z; (
      ∀ (W : TreeSequence G e0), TreeSequenceInitialSegment W T →
      ∀ (rho sigma : PartialEdgeColoring E k) (c : Fin k), ColoredVertexSetElementary G rho
          (TreeSequenceVertexSet W) → (
      ∀ v ∈ TreeSequenceVertexSet W, MissingColors G sigma v = MissingColors G rho v) → c ∈
          TreeMissingColors rho W → HierarchyFirstMissingPosition sigma T c =
          HierarchyFirstMissingPosition rho T c) → (
      ∀ (z : V ⊕ E) (rho : PartialEdgeColoring E k) (a b c : Fin k), a ≠ b → IsProperEdgeColoring G
          rho → c ≠ a → c ≠ b → HierarchyFirstMissingPosition (TwoColorComponentSwap G rho a b z) T
          c = HierarchyFirstMissingPosition rho T c) → (
      ∀ v ∈ TreeSequenceVertexSet Z, MissingColors G mu2 v = MissingColors G sigma v) →
      ∀ eta ∈ D, HierarchyFirstMissingPosition mu2 T eta = HierarchyFirstMissingPosition sigma T eta

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev originalStarStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
          LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
          TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
          input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
          HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (S :
          HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), HierarchyStarredStage
          C.hierarchy (Fin.last C.hierarchy.dividerCount) = HierarchyStarredStage
          S.counterexample.hierarchy (Fin.last S.counterexample.hierarchy.dividerCount)

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev lastDataStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount) =
        HierarchyStoredColorsAt S.counterexample.hierarchy
          (Fin.last S.counterexample.hierarchy.dividerCount) ∧
      ∀ eta ∈ HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount),
        C.good.gamma (Fin.last C.hierarchy.dividerCount) eta =
          S.counterexample.good.gamma (Fin.last S.counterexample.hierarchy.dividerCount) eta

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev sameLastStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
          LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
          TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
          input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
          HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
          HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k)
          (d : HierarchySituationThreeDisjointData G k e0 input T phi ett base C ctx P alpha beta),
      let R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx := d.switched;
      let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
          R.counterexample.hierarchy;
      let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
      let D : Finset (Fin k) := HierarchyStoredColorsAt H q; (
      ∀ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
          HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount) =
          HierarchyStoredColorsAt S.counterexample.hierarchy (Fin.last
          S.counterexample.hierarchy.dividerCount) ∧
      ∀ eta ∈ HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount), C.good.gamma
          (Fin.last C.hierarchy.dividerCount) eta = S.counterexample.good.gamma (Fin.last
          S.counterexample.hierarchy.dividerCount) eta) →
      ∀ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), D =
          HierarchyStoredColorsAt S.counterexample.hierarchy (Fin.last
          S.counterexample.hierarchy.dividerCount) ∧
      ∀ eta ∈ D, R.counterexample.good.gamma q eta = S.counterexample.good.gamma (Fin.last
          S.counterexample.hierarchy.dividerCount) eta

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev weakEdgesStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
          LooplessMultigraph V E) (k : ℕ) (e0 : E) (T : TreeSequence G e0)
          {input' : PartialEdgeColoring E k} (old new : PartialEdgeColoring E k) (et :
          ExtendedTashkinovTree G k e0 input' T old) (bs : HierarchyBase et old) (K :
          TashkinovHierarchy et bs), HierarchyWeaklyStable K (Fin.last K.dividerCount) new →
          IsOneEdgeUncolored old e0 → IsOneEdgeUncolored new e0 →
      ∀ (t : Fin (HierarchyStarredStage K (Fin.last K.dividerCount)).length), new
          ((HierarchyStarredStage K (Fin.last K.dividerCount)).edge t) = old ((HierarchyStarredStage
          K (Fin.last K.dividerCount)).edge t)

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev xYlenStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
          : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
          TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
          input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
          HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
          HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k)
          (d : HierarchySituationThreeDisjointData G k e0 input T phi ett base C ctx P alpha beta)
          (j : ℕ), HierarchyPathNumber C.hierarchy = j → (2 : ℕ) ≤ j →
      let R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx := d.switched;
      let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
          R.counterexample.hierarchy;
      let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
      let A : TreeSequence G e0 := HierarchyStarredStage H q;
      let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ));
      let Y : TreeSequence G e0 := HierarchyFullTailPrefix C j; TreeSequenceInitialSegment A T → j ≤
          T.length - A.length → (
      ∀ (m : ℕ), HierarchyFullTailPrefix C m = TreeSequencePrefix T (min (A.length + m) T.length) (
      by
          have := GoldbergSeymour.TreeSequence.positive T
          have := GoldbergSeymour.TreeSequence.positive A
          omega
      ) (
      by
          have := GoldbergSeymour.TreeSequence.positive T
          have := GoldbergSeymour.TreeSequence.positive A
          omega
      )) → Y.length = X.length + (1 : ℕ)

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev hweak1Statement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
          : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
          TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
          input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
          HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
          HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k)
          (d : HierarchySituationThreeDisjointData G k e0 input T phi ett base C ctx P alpha beta),
      let R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx := d.switched;
      let sigma : PartialEdgeColoring E k := R.coloring;
      let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
          R.counterexample.hierarchy;
      let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
      let A : TreeSequence G e0 := HierarchyStarredStage H q;
      ∀ (gamma : Fin k), gamma ≠ beta → ColoredVertexSetElementary G sigma (TreeSequenceVertexSet
          (HierarchyFullTailPrefix R.counterexample (HierarchyFullTailLength R.counterexample - (1 :
          ℕ)))) → gamma ∈ TreeMissingColors sigma (HierarchyFullTailPrefix R.counterexample
          (HierarchyFullTailLength R.counterexample - (1 : ℕ))) ∧ beta ∈ TreeMissingColors sigma
          (HierarchyFullTailPrefix R.counterexample (HierarchyFullTailLength R.counterexample - (1 :
          ℕ))) → Disjoint (TwoColorComponent G sigma gamma beta (Sum.inl (T.vertex (Fin.last
          T.length)))) (TwoColorComponent G sigma gamma beta (Sum.inl (T.vertex
          (HierarchyFirstMissingPosition sigma T gamma)))) →
      let z : V ⊕ E := Sum.inl (T.vertex (Fin.last T.length));
      let mu2 : PartialEdgeColoring E k := TwoColorComponentSwap G sigma gamma beta z; (0 : ℕ) <
          H.dividerCount ∧ gamma ∈ TreeMissingColors sigma (H.stage (⟨H.dividerCount,
      by
                    have := GoldbergSeymour.TreeSequence.positive T
                    omega
      ⟩ : Fin (H.dividerCount + (2 : ℕ)))) ∨ H.dividerCount = (0 : ℕ) ∧ (gamma ∈ TreeMissingColors
          sigma (R.corresponding.replacementETT.series.data.tree (Fin.last
          R.corresponding.replacementETT.rounds).castSucc) ∨ gamma ∈ TreeMissingColors sigma A ∧
          gamma ∉ TashkinovStoredColors R.corresponding.replacementETT.series.data (Fin.last
          R.corresponding.replacementETT.rounds) ∧ beta ∉ TashkinovStoredColors
          R.corresponding.replacementETT.series.data (Fin.last
          R.corresponding.replacementETT.rounds)) → TwoColorPathComponent G sigma gamma beta z →
          HierarchyWeaklyStable H q mu2

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev swapOneStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (T : TreeSequence G e0),
    let z : V ⊕ E := Sum.inl (T.vertex (Fin.last T.length));
    ∀ (old : PartialEdgeColoring E k) (a b : Fin k),
    IsOneEdgeUncolored old e0 →
    IsOneEdgeUncolored (TwoColorComponentSwap G old a b z) e0

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev hweak3Statement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
          : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
          TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
          input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
          HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
          HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k)
          (d : HierarchySituationThreeDisjointData G k e0 input T phi ett base C ctx P alpha beta),
      let ell : ℕ := HierarchyFullTailLength C;
      let Z : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
      ∀ (gamma : Fin k), gamma ≠ d.theta →
      let z : V ⊕ E := Sum.inl (T.vertex (Fin.last T.length)); (
      ∀ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
          HierarchyFullTailPrefix S.counterexample (HierarchyFullTailLength S.counterexample - (1 :
          ℕ)) = Z) →
      ∀ (R1 : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
      let rho : PartialEdgeColoring E k := R1.coloring; ColoredVertexSetElementary G rho
          (TreeSequenceVertexSet Z) →
      let mu3 : PartialEdgeColoring E k := TwoColorComponentSwap G rho gamma d.theta z;
          TwoColorPathComponent G rho gamma d.theta z → (
      let K : TashkinovHierarchy R1.corresponding.replacementETT R1.replacementBase :=
          R1.counterexample.hierarchy; (0 : ℕ) < K.dividerCount ∧ gamma ∈ TreeMissingColors rho
          (K.stage (⟨K.dividerCount,
      by
                  have := GoldbergSeymour.TreeSequence.positive T
                  omega
      ⟩ : Fin (K.dividerCount + (2 : ℕ)))) ∨ K.dividerCount = (0 : ℕ) ∧ (gamma ∈ TreeMissingColors
          rho (R1.corresponding.replacementETT.series.data.tree (Fin.last
          R1.corresponding.replacementETT.rounds).castSucc) ∨ gamma ∈ TreeMissingColors rho
          (HierarchyStarredStage K (Fin.last K.dividerCount)) ∧ gamma ∉ TashkinovStoredColors
          R1.corresponding.replacementETT.series.data (Fin.last
          R1.corresponding.replacementETT.rounds) ∧ d.theta ∉ TashkinovStoredColors
          R1.corresponding.replacementETT.series.data (Fin.last
          R1.corresponding.replacementETT.rounds))) → Disjoint (TwoColorComponent G rho gamma
          d.theta z) (TwoColorComponent G rho gamma d.theta (Sum.inl (T.vertex
          (HierarchyFirstMissingPosition rho T gamma)))) → gamma ∈ TreeMissingColors rho
          (HierarchyFullTailPrefix R1.counterexample (HierarchyFullTailLength R1.counterexample - (1
          : ℕ))) ∧ d.theta ∈ TreeMissingColors rho (HierarchyFullTailPrefix R1.counterexample
          (HierarchyFullTailLength R1.counterexample - (1 : ℕ))) → HierarchyWeaklyStable
          R1.counterexample.hierarchy (Fin.last R1.counterexample.hierarchy.dividerCount) mu3

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev yTerminalDistinctStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
          LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
          TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
          input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
          HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
          HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k)
          (d : HierarchySituationThreeDisjointData G k e0 input T phi ett base C ctx P alpha beta)
          (j : ℕ),
      let R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx := d.switched;
      let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
          R.counterexample.hierarchy;
      let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
      let A : TreeSequence G e0 := HierarchyStarredStage H q;
      let Y : TreeSequence G e0 := HierarchyFullTailPrefix C j; A.length + j < T.length → Y.length =
          A.length + j → TreeSequenceInitialSegment Y T → Y.vertex (Fin.last Y.length) ≠ T.vertex
          (Fin.last T.length)

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev hjEligibleStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
          LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
          TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
          input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
          HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
          HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k)
          (d : HierarchySituationThreeDisjointData G k e0 input T phi ett base C ctx P alpha beta)
          (j : ℕ), (2 : ℕ) ≤ j → j < HierarchyFullTailLength C →
      let Y : TreeSequence G e0 := HierarchyFullTailPrefix C j;
      ∀ (gamma : Fin k),
      let z : V ⊕ E := Sum.inl (T.vertex (Fin.last T.length));
      ∀ (R1 : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
      let rho : PartialEdgeColoring E k := R1.coloring;
      let mu3 : PartialEdgeColoring E k := TwoColorComponentSwap G rho gamma d.theta z; d.theta ∈
          MissingColors G mu3 (T.vertex (Fin.last T.length)) → d.theta ∈ MissingColors G mu3
          (Y.vertex (Fin.last Y.length)) →
      ∀ (R2 : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), R2.coloring = mu3
          → j ∈ HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx

/-- A common proof used by the branches of this transport or construction argument. -/
theorem hthetaFirstIndex.{u_1, u_2} : hthetaFirstIndexStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d j R sigma ell Y Z
      hthetaMissingY hYtoT hYtoZ hZtoT hElemZ vertexMemT hthetaFirst
  as_aux_lemma =>
    clear_value Y Z
    apply Nat.le_antisymm hthetaFirst.2
    by_contra hne
    have hlt : (HierarchyFirstMissingPosition sigma T d.theta).val < Y.length :=
      Nat.lt_of_not_ge hne
    have iZ : T.vertex (HierarchyFirstMissingPosition sigma T d.theta) ∈
        TreeSequenceVertexSet Z := vertexMemT Z hZtoT
          (HierarchyFirstMissingPosition sigma T d.theta)
          (Nat.le_trans (Nat.le_of_lt hlt) hYtoZ.1)
    have yZ : Y.vertex (Fin.last Y.length) ∈ TreeSequenceVertexSet Z :=
      TreeSequenceInitialSegmentVertexSetSubset hYtoZ
        (by simp [TreeSequenceVertexSet])
    have hvne : T.vertex (HierarchyFirstMissingPosition sigma T d.theta) ≠
        Y.vertex (Fin.last Y.length) := by
      intro heq
      let jY : Fin (Y.length + 1) :=
        ⟨(HierarchyFirstMissingPosition sigma T d.theta).val,
          Nat.lt_succ_of_le (Nat.le_of_lt hlt)⟩
      have hcast : Fin.castLE (Nat.succ_le_succ hYtoT.1) jY =
          HierarchyFirstMissingPosition sigma T d.theta := Fin.ext rfl
      have heqY : Y.vertex jY = Y.vertex (Fin.last Y.length) := by
        have htree := hYtoT.2.1 jY
        have hcastV := congrArg T.vertex hcast
        exact htree.symm.trans (hcastV.trans heq)
      have hidx := Y.vertex_injective heqY
      have hval := congrArg Fin.val hidx
      dsimp [jY] at hval
      exact (Nat.ne_of_lt hlt) hval
    exact Finset.disjoint_left.mp (hElemZ iZ yZ hvne)
      hthetaFirst.1 hthetaMissingY

/-- A common proof used by the branches of this transport or construction argument. -/
theorem firstWitness.{u_1, u_2} : firstWitnessStatement.{u_1, u_2} := by
  classical
  intro V E _ _ G k e0 T rho W hWT c hc
  let _ := Fintype.ofFinite V
  as_aux_lemma =>
    rcases Finset.mem_biUnion.mp hc with ⟨v, hv, hcv⟩
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and] at hv
    rcases hv with ⟨i, rfl⟩
    let candidates := Finset.univ.filter fun a : Fin (T.length + 1) =>
      c ∈ MissingColors G rho (T.vertex a)
    have hi : Fin.castLE (Nat.succ_le_succ hWT.1) i ∈ candidates := by
      simp [candidates, hWT.2.1 i, hcv]
    have hn : candidates.Nonempty := ⟨_, hi⟩
    have hmin := Finset.min'_le candidates _ hi
    have hmiss : c ∈ MissingColors G rho (T.vertex (candidates.min' hn)) :=
      (Finset.mem_filter.mp (Finset.min'_mem candidates hn)).2
    have hpos : HierarchyFirstMissingPosition rho T c = candidates.min' hn := by
      simp [HierarchyFirstMissingPosition, candidates, hn]
    constructor
    · simpa [HierarchyFirstMissingPosition, candidates, hn] using hmiss
    · rw [hpos]
      have hle : (candidates.min' hn).val ≤ i.val := by
        change (candidates.min' hn).val ≤ (Fin.castLE (Nat.succ_le_succ hWT.1) i).val at hmin
        simpa using hmin
      exact le_trans hle (Nat.le_of_lt_succ i.isLt)

/-- A common proof used by the branches of this transport or construction argument. -/
theorem hthetaMissingY.{u_1, u_2} : hthetaMissingYStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d j hj R sigma Y
  have ht := d.thetaMissingAtJ
  change d.theta ∈ MissingColors G d.switched.coloring
    ((HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy)).vertex
      (Fin.last (HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy)).length)) at ht
  rw [hj] at ht
  exact ht

/-- A common proof used by the branches of this transport or construction argument. -/
theorem sameStar.{u_1, u_2} : sameStarStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d j R H q A X Y
  as_aux_lemma =>
    clear * - G e0 base C R H q A
    have helper :
    ∀ (n m : ℕ) (X Y : TreeSequence G e0) (s : Fin (n + 2) → TreeSequence G e0) (t : Fin (m + 2) →
        TreeSequence G e0), n = m → X = Y → HEq s t → Fin.cases (motive := fun _ => TreeSequence G
        e0) X (fun i : Fin n => s i.succ.castSucc) (Fin.last n) = Fin.cases (motive := fun _ =>
        TreeSequence G e0) Y (fun i : Fin m => t i.succ.castSucc) (Fin.last m) := by
      intro n m X Y s t hnm hXY hst
      subst m
      have hs : s = t := eq_of_heq hst
      simp [hXY, hs]
    simpa [A, q, HierarchyStarredStage] using (helper _ _ base.core R.replacementBase.core
        C.hierarchy.stage
      H.stage R.sameGood.1.2.1 R.sameGood.1.1
      R.sameGood.1.2.2.1)

/-- A common proof used by the branches of this transport or construction argument. -/
theorem hcutJstrict.{u_1, u_2} : hcutJstrictStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d j hj R H q A ell sameStar
      hAtoT hjUpper
  have hj : j < T.length - A.length := by
    simpa only [ell, HierarchyFullTailLength, sameStar] using hjUpper
  have hAT := hAtoT.1
  clear * - hj hAT
  clear_value A
  omega

/-- A common proof used by the branches of this transport or construction argument. -/
theorem prefixToTree.{u_1, u_2} : prefixToTreeStatement.{u_1, u_2} := by
  classical
  intro V E G e0 T m hm hmT
  as_aux_lemma =>
    refine ⟨hmT, ?_, ?_⟩
    · intro i
      simp [TreeSequencePrefix]
    · intro i
      simp [TreeSequencePrefix]

/-- A common proof used by the branches of this transport or construction argument. -/
theorem comparableInitialSegments.{u_1, u_2} : comparableInitialSegmentsStatement.{u_1, u_2} := by
  classical
  intro V E G e0 T U W hUT hWT hUW
  as_aux_lemma =>
    rcases hUT with ⟨hu, huv, hue⟩
    rcases hWT with ⟨hw, hwv, hwe⟩
    refine ⟨hUW, ?_, ?_⟩
    · intro i
      calc
        W.vertex (Fin.castLE (Nat.succ_le_succ hUW) i) =
            T.vertex (Fin.castLE (Nat.succ_le_succ hw)
              (Fin.castLE (Nat.succ_le_succ hUW) i)) := (hwv _).symm
        _ = T.vertex (Fin.castLE (Nat.succ_le_succ hu) i) := by congr 1
        _ = U.vertex i := huv i
    · intro i
      calc
        W.edge (Fin.castLE hUW i) = T.edge (Fin.castLE hw (Fin.castLE hUW i)) :=
          (hwe _).symm
        _ = T.edge (Fin.castLE hu i) := by congr 1
        _ = U.edge i := hue i

/-- A common proof used by the branches of this transport or construction argument. -/
theorem elemZ.{u_1, u_2} : elemZStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d R sigma ell Z
      penultimatePrefixEq
  as_aux_lemma =>
    have hp : ColoredVertexSetElementary G sigma
        (TreeSequenceVertexSet (HierarchyFullTailPrefix R.counterexample
          (HierarchyFullTailLength R.counterexample - 1))) :=
      HierarchyCounterexamplePenultimateElementary G k e0
        R.corresponding.replacementInput T sigma R.corresponding.replacementETT
        R.replacementBase R.counterexample R.minimumContext.proper
        R.minimumContext.oneEdgeUncolored R.minimumContext.lowerRung
        R.minimumContext.fewerDividers R.minimumContext.lexicographicMinimality
        R.minimumContext.largeMissingSet
    intro u hu v hv huv
    apply hp
    · rw [penultimatePrefixEq]; exact hu
    · rw [penultimatePrefixEq]; exact hv
    · exact huv

/-- A common proof used by the branches of this transport or construction argument. -/
theorem vertexMemT.{u_1, u_2} : vertexMemTStatement.{u_1, u_2} := by
  classical
  intro V E G e0 T W hWT i hi
  as_aux_lemma =>
    let jW : Fin (W.length + 1) := ⟨i.val, Nat.lt_succ_of_le hi⟩
    have hcast : Fin.castLE (Nat.succ_le_succ hWT.1) jW = i := Fin.ext rfl
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨jW, ?_⟩
    rw [← hWT.2.1 jW, hcast]

/-- A common proof used by the branches of this transport or construction argument. -/
theorem hthetaY.{u_1, u_2} : hthetaYStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d j R sigma Y hthetaMissingY
      vertexMemSelf treeMissingIntro
  as_aux_lemma =>
    clear_value Y
    exact treeMissingIntro sigma Y (Y.vertex (Fin.last Y.length)) d.theta
      (vertexMemSelf Y (Fin.last Y.length)) hthetaMissingY


/-- A common proof used by the branches of this transport or construction argument. -/
theorem apositive.{u_1, u_2} : apositiveStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d R H q A hq
  as_aux_lemma =>
    have hlast : q =
        (⟨H.dividerCount - 1, Nat.sub_lt hq (by decide)⟩ : Fin H.dividerCount).succ := by
      apply Fin.ext
      change H.dividerCount = H.dividerCount - 1 + 1
      exact (Nat.sub_add_cancel hq).symm
    change HierarchyStarredStage H q = _
    rw [hlast]
    change H.stage _ = H.stage _
    congr 1
    apply Fin.ext
    change H.dividerCount - 1 + 1 = H.dividerCount
    exact Nat.sub_add_cancel hq

/-- A common proof used by the branches of this transport or construction argument. -/
theorem sameGammaBeta.{u_1, u_2} : sameGammaBetaStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d R sigma H q A gamma hgammaA
      firstChange hgammaStageMissing hApositive
  by_cases hzero : H.dividerCount = 0
  · have hgammaRaw : gamma ∈ TreeMissingColors sigma
      (R.corresponding.replacementETT.series.data.tree
        (Fin.last R.corresponding.replacementETT.rounds).castSucc) := by
      have hq0 : q = 0 := by
        apply Fin.ext
        simp [q, hzero]
      rw [hq0] at hgammaStageMissing
      simpa [HierarchyStageMissingColors] using hgammaStageMissing
    exact firstChange.2.1 ⟨hzero, Or.inl hgammaRaw⟩
  · have hgammaLast : gamma ∈ TreeMissingColors sigma
      (H.stage ⟨H.dividerCount, Nat.lt_add_of_pos_right (by decide)⟩) := by
      have hstar : A = H.stage ⟨H.dividerCount, Nat.lt_add_of_pos_right (by decide)⟩ :=
        hApositive (Nat.pos_of_ne_zero hzero)
      rw [← hstar]
      exact hgammaA
    exact firstChange.1 ⟨Nat.pos_of_ne_zero hzero, Or.inl hgammaLast⟩

/-- A common proof used by the branches of this transport or construction argument. -/
theorem hmu2One.{u_1, u_2} : hmu2OneStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d R sigma gamma z mu2
  as_aux_lemma =>
    constructor
    · have he0 : sigma e0 = none := R.minimumContext.oneEdgeUncolored.1
      simp [mu2, TwoColorComponentSwap, he0]
    · intro e he0
      obtain ⟨c, hc⟩ := R.minimumContext.oneEdgeUncolored.2 e he0
      by_cases heK : Sum.inr e ∈ TwoColorComponent G sigma gamma beta z
      · by_cases heGamma : sigma e = some gamma
        · exact ⟨beta, by simp [mu2, TwoColorComponentSwap, heK, heGamma]
          ⟩
        · by_cases heBeta : sigma e = some beta
          · exact ⟨gamma, by
              simp [mu2, TwoColorComponentSwap, heK, heBeta]
            ⟩
          · exact ⟨c, by
              simpa [mu2, TwoColorComponentSwap, heK, heGamma, heBeta] using hc⟩
      · exact ⟨c, by simpa [mu2, TwoColorComponentSwap, heK] using hc⟩

/-- A common proof used by the branches of this transport or construction argument. -/
theorem hfirstBetaOutside.{u_1, u_2} : hfirstBetaOutsideStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d R sigma gamma sameGammaBeta
      componentSelf hterminalDisjoint z hv
  have hv' : Sum.inl (T.vertex (HierarchyFirstMissingPosition sigma T beta)) ∈
    TwoColorComponent G sigma gamma beta
        (Sum.inl (T.vertex (HierarchyFirstMissingPosition sigma T gamma))) := by
    rw [sameGammaBeta]
    exact componentSelf sigma gamma beta
      (T.vertex (HierarchyFirstMissingPosition sigma T beta))
  exact (Set.disjoint_left.mp hterminalDisjoint) hv hv'

/-- A common proof used by the branches of this transport or construction argument. -/
theorem firstPreserved.{u_1, u_2} : firstPreservedStatement.{u_1, u_2} := by
  classical
  intro V E _ _ G k e0 T j firstWitness W hWT rho sigma c helem hmiss hc
  let _ := Fintype.ofFinite V
  as_aux_lemma =>
    clear * - G T W rho sigma c helem hmiss hc firstWitness hWT
    have hr := firstWitness rho W hWT c hc
    have hc' : c ∈ TreeMissingColors sigma W := by
      obtain ⟨v, hv, hm⟩ := Finset.mem_biUnion.mp hc
      exact Finset.mem_biUnion.mpr ⟨v, hv, (hmiss v hv).symm ▸ hm⟩
    have hs := firstWitness sigma W hWT c hc'
    have pref (i : Fin (T.length + 1)) (hi : i.val ≤ W.length) :
        T.vertex i ∈ TreeSequenceVertexSet W := by
      let j : Fin (W.length + 1) := ⟨i.val, Nat.lt_succ_of_le hi⟩
      have he : Fin.castLE (Nat.succ_le_succ hWT.1) j = i := Fin.ext rfl
      exact (@Finset.mem_image _ _ (Classical.decEq V)).mpr
        ⟨j, Finset.mem_univ _, (hWT.2.1 j).symm.trans (congrArg T.vertex he)⟩
    by_contra hne
    have hvne : T.vertex (HierarchyFirstMissingPosition sigma T c) ≠
        T.vertex (HierarchyFirstMissingPosition rho T c) :=
      fun he => hne (T.vertex_injective he)
    have hsOld := (hmiss _ (pref _ hs.2)) ▸ hs.1
    exact Finset.disjoint_left.mp (helem (pref _ hs.2) (pref _ hr.2) hvne) hsOld hr.1

/-- A common proof used by the branches of this transport or construction argument. -/
theorem missingTransport.{u_1, u_2} : missingTransportStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ell Z old new hm W hWZ
  as_aux_lemma =>
    clear_value Z
    clear * - old new hm W hWZ Z
    unfold TreeMissingColors
    exact Finset.biUnion_congr rfl (fun v hv =>
      hm v (TreeSequenceInitialSegmentVertexSetSubset hWZ hv))

/-- A common proof used by the branches of this transport or construction argument. -/
theorem hstoredMu2.{u_1, u_2} : hstoredMu2Statement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d R sigma H q A ell Z D gamma
      hgammaA hgammaNeBeta hZtoT hElemZ hbetaMissingZ z mu2 firstPreserved firstUnaffected
      hmissingMu2 eta heta
  have hneGamma : eta ≠ gamma := by
    intro he
    exact (Finset.mem_sdiff.mp heta).2 (he.symm ▸ hgammaA)
  by_cases he : eta = beta
  · subst eta
    exact firstPreserved Z hZtoT sigma mu2 beta hElemZ hmissingMu2 hbetaMissingZ
  · exact firstUnaffected z sigma gamma beta eta hgammaNeBeta
      R.minimumContext.proper hneGamma he

/-- A common proof used by the branches of this transport or construction argument. -/
theorem originalStar.{u_1, u_2} : originalStarStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx S
  as_aux_lemma =>
    have helper :
    ∀ (n m : ℕ) (U W : TreeSequence G e0) (s : Fin (n + 2) → TreeSequence G e0) (t : Fin (m + 2) →
        TreeSequence G e0), n = m → U = W → HEq s t → Fin.cases (motive := fun _ => TreeSequence G
        e0) U (fun i : Fin n => s i.succ.castSucc) (Fin.last n) = Fin.cases (motive := fun _ =>
        TreeSequence G e0) W (fun i : Fin m => t i.succ.castSucc) (Fin.last m) := by
      intro n m U W s t hnm hUW hst
      subst m
      have he : s = t := eq_of_heq hst
      simp only [hUW, he]
    exact helper _ _ _ _ _ _ S.sameGood.1.2.1 S.sameGood.1.1 S.sameGood.1.2.2.1

/-- A common proof used by the branches of this transport or construction argument. -/
theorem lastData.{u_1, u_2} : lastDataStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx S
  as_aux_lemma =>
    obtain ⟨hc, hd⟩ := S.sameGood.2
    have hi : Fin.cast (congrArg (fun n => n + 1) hc)
        (Fin.last C.hierarchy.dividerCount) =
          Fin.last S.counterexample.hierarchy.dividerCount := Fin.ext hc
    simpa only [hi] using hd (Fin.last C.hierarchy.dividerCount)

/-- A common proof used by the branches of this transport or construction argument. -/
theorem sameLast.{u_1, u_2} : sameLastStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d R H q D lastData S
  refine ⟨(lastData R).1.symm.trans (lastData S).1, ?_⟩
  intro eta heta
  have hc : eta ∈ HierarchyStoredColorsAt C.hierarchy
      (Fin.last C.hierarchy.dividerCount) := (lastData R).1.symm ▸ heta
  exact ((lastData R).2 eta hc).symm.trans ((lastData S).2 eta hc)

/-- A common proof used by the branches of this transport or construction argument. -/
theorem weakEdges.{u_1, u_2} : weakEdgesStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 T input' old new et bs K hw ho hn
  as_aux_lemma =>
    by_cases hz : K.dividerCount = 0
    · have hi : (Fin.last K.dividerCount : Fin (K.dividerCount + 1)) = 0 := Fin.ext hz
      rw [hi] at hw ⊢
      exact P2813_T1_BaseDisplayedEdges G k e0 input' T old et bs new ho hn hw
    · have hi : (Fin.last K.dividerCount : Fin (K.dividerCount + 1)) =
          (⟨K.dividerCount - 1, by omega⟩ : Fin K.dividerCount).succ :=
        Fin.ext (by simp only [Fin.val_last, Fin.val_succ]; omega)
      rw [hi] at hw ⊢
      intro t
      by_cases ht : 1 ≤ t.val
      · exact hw.2.1 t ht
      · let W := HierarchyStarredStage K
          (⟨K.dividerCount - 1, by omega⟩ : Fin K.dividerCount).succ
        have he : t = ⟨0, W.positive⟩ := Fin.ext (by change t.val = 0; omega)
        rw [he, W.first_edge, hn.1, ho.1]

/-- A common proof used by the branches of this transport or construction argument. -/
theorem xYlen.{u_1, u_2} : xYlenStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d j hj hpathLower R H q A X Y
      hAtoT htail fullPrefixEq
  change (HierarchyFullTailPrefix C j).length =
    (HierarchyFullTailPrefix C (j - 1)).length + 1
  rw [fullPrefixEq j, fullPrefixEq (j - 1)]
  simp only [TreeSequencePrefix]
  have hj : 2 ≤ j := hpathLower
  have hl : A.length + j ≤ T.length := by
    have hAT := hAtoT.1
    clear * - htail hAT
    omega
  clear * - hj hl
  omega

/-- A common proof used by the branches of this transport or construction argument. -/
theorem hweak1.{u_1, u_2} : hweak1Statement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d R sigma H q A gamma
      hgammaNeBeta hchangeElementary hchangeMissing hterminalDisjoint z mu2 hcase1 hpath1
  as_aux_lemma =>
    exact (StableChangeCasesOneTwo G k e0 R.corresponding.replacementInput T sigma
      R.corresponding.replacementETT R.replacementBase R.counterexample
      R.minimumContext.proper R.minimumContext.oneEdgeUncolored R.minimumContext.lowerRung
      R.minimumContext.fewerDividers R.minimumContext.lexicographicMinimality
      hchangeElementary R.minimumContext.largeMissingSet gamma beta hgammaNeBeta
      hchangeMissing z hpath1 mu2 rfl hcase1 hterminalDisjoint).1

/-- A common proof used by the branches of this transport or construction argument. -/
theorem swapOne.{u_1, u_2} : swapOneStatement.{u_1, u_2} := by
  classical
  intro V E G k e0 T z old a b ho
  as_aux_lemma =>
    constructor
    · simp only [TwoColorComponentSwap, ho.1, reduceCtorEq, ite_false, ite_self]
    · intro e he
      obtain ⟨c, hc⟩ := ho.2 e he
      by_cases hm : Sum.inr e ∈ TwoColorComponent G old a b z
      · by_cases ha : old e = some a
        · exact ⟨b, by simp only [TwoColorComponentSwap, hm, ha, ite_true]⟩
        · by_cases hb : old e = some b
          · refine ⟨a, ?_⟩
            unfold TwoColorComponentSwap
            rw [ite_eq_left hm, ite_eq_right ha, ite_eq_left hb]
          · exact ⟨c, by simpa only [TwoColorComponentSwap, hm, ha, hb, ite_true, ite_false]
              using hc⟩
      · exact ⟨c, by simpa only [TwoColorComponentSwap, hm, ite_false] using hc⟩

/-- A common proof used by the branches of this transport or construction argument. -/
theorem hweak3.{u_1, u_2} : hweak3Statement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d ell Z gamma hgammaNeTheta z
      samePenultimate R1 rho hElemRho mu3 hpath3 hcase3 hdisjoint3First hmissingPairCurrent
  as_aux_lemma =>
    exact (StableChangeCasesOneTwo G k e0 R1.corresponding.replacementInput T rho
      R1.corresponding.replacementETT R1.replacementBase R1.counterexample
      R1.minimumContext.proper R1.minimumContext.oneEdgeUncolored R1.minimumContext.lowerRung
      R1.minimumContext.fewerDividers R1.minimumContext.lexicographicMinimality
      (by
        change ColoredVertexSetElementary G rho
          (TreeSequenceVertexSet (HierarchyFullTailPrefix R1.counterexample
            (HierarchyFullTailLength R1.counterexample - 1)))
        rw [samePenultimate R1]
        exact hElemRho) R1.minimumContext.largeMissingSet
      gamma d.theta hgammaNeTheta hmissingPairCurrent z hpath3 mu3 rfl hcase3 hdisjoint3First).1

/-- A common proof used by the branches of this transport or construction argument. -/
theorem yTerminalDistinct.{u_1, u_2} : yTerminalDistinctStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d j R H q A Y hcutJstrict
      hYlen hYtoT he
  have hi := T.vertex_injective ((hYtoT.2.1 (Fin.last Y.length)).trans he)
  have hv := congrArg Fin.val hi
  simp only [Fin.val_castLE, Fin.val_last] at hv
  exact Nat.ne_of_lt (hYlen.symm ▸ hcutJstrict) hv

/-- A common proof used by the branches of this transport or construction argument. -/
theorem hjEligible.{u_1, u_2} : hjEligibleStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d j hpathLower hpathUpper Y
      gamma z R1 rho mu3 hthetaTerminalMu3 hthetaYMu3 R2 hR2
  refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, R2, d.theta, ?_, ?_⟩
  · exact (by decide : 1 ≤ 2).trans hpathLower
  · exact Nat.le_sub_one_of_lt hpathUpper
  · rw [hR2]
    exact hthetaYMu3
  · rw [hR2]
    exact hthetaTerminalMu3

end GoldbergSeymour.SharedFacts.DisjointThetaTransport

end
