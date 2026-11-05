/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TwoColorComponentColoringFacts

public import LeanPool.GoldbergSeymour.HierarchyFullTailLength
public import LeanPool.GoldbergSeymour.HierarchySituationThreeDisjointData
public import LeanPool.GoldbergSeymour.HierarchySituationThreeEligibleIndexBound

/-!
# Hierarchy Situation Three Disjoint Theta Unstored Beta Stored Impossible

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev helperRouteToY1012Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
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
    let ell : ℕ := HierarchyFullTailLength C;
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ));
    let Y : TreeSequence G e0 := HierarchyFullTailPrefix C j;
    let Z : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
        TreeSequenceInitialSegment A T → (
    ∀ {U W : TreeSequence G e0}, TreeSequenceInitialSegment U T → TreeSequenceInitialSegment W T →
        U.length ≤ W.length → TreeSequenceInitialSegment U W) → Y.length = A.length + j →
        TreeSequenceInitialSegment Y T → TreeSequenceInitialSegment X Y →
        TreeSequenceInitialSegment Y Z → TreeSequenceInitialSegment A Y → (
    ∀ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage S.counterexample.hierarchy (Fin.last
        S.counterexample.hierarchy.dividerCount) = A) → (
    ∀ {input' : PartialEdgeColoring E k} (old new : PartialEdgeColoring E k) (et :
        ExtendedTashkinovTree G k e0 input' T old) (bs : HierarchyBase et old) (K :
        TashkinovHierarchy et bs), HierarchyWeaklyStable K (Fin.last K.dividerCount) new →
        IsOneEdgeUncolored old e0 → IsOneEdgeUncolored new e0 →
    ∀ (t : Fin (HierarchyStarredStage K (Fin.last K.dividerCount)).length), new
        ((HierarchyStarredStage K (Fin.last K.dividerCount)).edge t) = old ((HierarchyStarredStage
        K (Fin.last K.dividerCount)).edge t)) → Y.length = X.length + (1 : ℕ) →
    ∀ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (nu :
        PartialEdgeColoring E k), IsOneEdgeUncolored nu e0 → HierarchyWeaklyStable
        S.counterexample.hierarchy (Fin.last S.counterexample.hierarchy.dividerCount) nu → (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < Y.length → nu (T.edge t) = S.coloring
        (T.edge t)) → (
    ∀ v ∈ TreeSequenceVertexSet Z, MissingColors G nu v = MissingColors G S.coloring v) →
    let et : ExtendedTashkinovTree G k e0 S.corresponding.replacementInput T S.coloring :=
        S.corresponding.replacementETT;
    let n : Fin (et.rounds + (1 : ℕ)) := Fin.last et.rounds;
    let Tn : TreeSequence G e0 := et.series.data.tree n.castSucc; et.series.data.kind n = some
        TashkinovExtensionKind.PE ∧ TashkinovAugmentationSequence nu Tn Y ∨ (et.series.data.kind n
        = some TashkinovExtensionKind.SE ∨ et.series.data.kind n = some TashkinovExtensionKind.RE)
        ∧
    ∃ (f : E) (seed : TreeSequence G e0), et.series.data.connectingEdges n = { f } ∧
        TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence nu seed Y

private abbrev helperContinuation2578Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k),
        (
    ∀ (mu : PartialEdgeColoring E k), IsProperEdgeColoring G mu → IsOneEdgeUncolored mu e0 →
    ∀ (v : V), (MissingColors G mu v).Nonempty) →
    ∀ (d : HierarchySituationThreeDisjointData G k e0 input T phi ett base C ctx P alpha beta) (j
        : ℕ), HierarchyPathNumber C.hierarchy = j → (2 : ℕ) ≤ j → j < HierarchyFullTailLength C →
    let R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx := d.switched;
    let sigma : PartialEdgeColoring E k := R.coloring;
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength C;
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ));
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ));
    let Y : TreeSequence G e0 := HierarchyFullTailPrefix C j;
    let Z : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q; beta ∈ D → beta ∈ TreeMissingColors
        sigma B → Disjoint (R.counterexample.good.gamma q beta ∪ ({ beta } : Finset (Fin k))) ({c
        : Fin k |
    ∃ (r : Fin T.length), A.length ≤ (↑r : ℕ) ∧ (↑r : ℕ) < A.length + j ∧ sigma (T.edge r) = some
        c} : Finset (Fin k)) → d.theta ∈ MissingColors G sigma (Y.vertex (Fin.last Y.length)) →
    ∀ gamma ∈ R.counterexample.good.gamma q beta, gamma ∈ TreeMissingColors sigma A → gamma ≠ beta
        → d.theta ∉ D → HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) = A
        → TreeSequenceInitialSegment A T → j ≤ T.length - A.length → A.length + j < T.length → (
    ∀ (m : ℕ), HierarchyFullTailPrefix C m = TreeSequencePrefix T (min (A.length + m) T.length) (
    by
       have := GoldbergSeymour.TreeSequence.positive T
       have := GoldbergSeymour.TreeSequence.positive A
       have :=
        GoldbergSeymour.CorrespondingExtendedTashkinovTree.rungAgreement
         (GoldbergSeymour.HierarchyReplacementPresentation.corresponding P)
       have := Fin.isLt alpha
       have := Fin.isLt beta
       have :=
        GoldbergSeymour.CorrespondingExtendedTashkinovTree.rungAgreement
         (GoldbergSeymour.HierarchyReplacementPresentation.corresponding R)
       have := Fin.isLt q
       have := GoldbergSeymour.TreeSequence.positive A
       have := GoldbergSeymour.TreeSequence.positive T
       omega
    ) (
    by
       have := GoldbergSeymour.TreeSequence.positive T
       have := GoldbergSeymour.TreeSequence.positive A
       have :=
        GoldbergSeymour.CorrespondingExtendedTashkinovTree.rungAgreement
         (GoldbergSeymour.HierarchyReplacementPresentation.corresponding P)
       have := Fin.isLt alpha
       have := Fin.isLt beta
       have :=
        GoldbergSeymour.CorrespondingExtendedTashkinovTree.rungAgreement
         (GoldbergSeymour.HierarchyReplacementPresentation.corresponding R)
       have := Fin.isLt q
       have := GoldbergSeymour.TreeSequence.positive A
       have := GoldbergSeymour.TreeSequence.positive T
       omega
    )) → (
    ∀ {U W : TreeSequence G e0}, TreeSequenceInitialSegment U T → TreeSequenceInitialSegment W T →
        U.length ≤ W.length → TreeSequenceInitialSegment U W) → Y.length = A.length + j →
        TreeSequenceInitialSegment B T → TreeSequenceInitialSegment Y T →
        TreeSequenceInitialSegment B X → TreeSequenceInitialSegment X Y →
        TreeSequenceInitialSegment Y Z → TreeSequenceInitialSegment Z T →
        TreeSequenceInitialSegment A Y → HierarchyFullTailPrefix R.counterexample
        (HierarchyFullTailLength R.counterexample - (1 : ℕ)) = Z → ColoredVertexSetElementary G
        sigma (TreeSequenceVertexSet Z) → (
    ∀ (rho : PartialEdgeColoring E k) (W : TreeSequence G e0), TreeSequenceInitialSegment W T →
    ∀ c ∈ TreeMissingColors rho W, c ∈ MissingColors G rho (T.vertex
        (HierarchyFirstMissingPosition rho T c)) ∧ (↑(HierarchyFirstMissingPosition rho T c) : ℕ)
        ≤ W.length) → gamma ∈ MissingColors G sigma (T.vertex (HierarchyFirstMissingPosition sigma
        T gamma)) ∧ (↑(HierarchyFirstMissingPosition sigma T gamma) : ℕ) ≤ A.length → beta ∈
        MissingColors G sigma (T.vertex (HierarchyFirstMissingPosition sigma T beta)) ∧
        (↑(HierarchyFirstMissingPosition sigma T beta) : ℕ) ≤ B.length →
        (↑(HierarchyFirstMissingPosition sigma T gamma) : ℕ) ≤ A.length →
        (↑(HierarchyFirstMissingPosition sigma T beta) : ℕ) ≤ B.length → (
    ∀ (W : TreeSequence G e0), TreeSequenceInitialSegment W T →
    ∀ (i : Fin (T.length + (1 : ℕ))), (↑i : ℕ) ≤ W.length → T.vertex i ∈ TreeSequenceVertexSet W)
        → False

private abbrev helperContinuation2662Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k),
        (
    ∀ (mu : PartialEdgeColoring E k), IsProperEdgeColoring G mu → IsOneEdgeUncolored mu e0 →
    ∀ (v : V), (MissingColors G mu v).Nonempty) →
    ∀ (d : HierarchySituationThreeDisjointData G k e0 input T phi ett base C ctx P alpha beta) (j
        : ℕ), HierarchyPathNumber C.hierarchy = j → (2 : ℕ) ≤ j → j < HierarchyFullTailLength C →
    let R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx := d.switched;
    let sigma : PartialEdgeColoring E k := R.coloring;
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength C;
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ));
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ));
    let Y : TreeSequence G e0 := HierarchyFullTailPrefix C j;
    let Z : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q; beta ∈ D → beta ∈ TreeMissingColors
        sigma B → Disjoint (R.counterexample.good.gamma q beta ∪ ({ beta } : Finset (Fin k))) ({c
        : Fin k |
    ∃ (r : Fin T.length), A.length ≤ (↑r : ℕ) ∧ (↑r : ℕ) < A.length + j ∧ sigma (T.edge r) = some
        c} : Finset (Fin k)) → d.theta ∈ MissingColors G sigma (Y.vertex (Fin.last Y.length)) →
    ∀ gamma ∈ R.counterexample.good.gamma q beta, gamma ∈ TreeMissingColors sigma A → gamma ≠ beta
        → d.theta ∉ D → HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) = A
        → TreeSequenceInitialSegment A T → j ≤ T.length - A.length → A.length + j < T.length → (
    ∀ (m : ℕ), HierarchyFullTailPrefix C m = TreeSequencePrefix T (min (A.length + m) T.length) (
    have this : (1 : ℕ) ≤ T.length := T.positive;
    have this_1 : (1 : ℕ) ≤ A.length := A.positive;
    have this_2 : P.corresponding.replacementETT.rounds = ett.rounds :=
    by
     have := GoldbergSeymour.TreeSequence.positive T
     have :=
      GoldbergSeymour.CorrespondingExtendedTashkinovTree.rungAgreement
       (GoldbergSeymour.HierarchyReplacementPresentation.corresponding P)
     omega;
    have this_3 : (↑alpha : ℕ) < k := alpha.isLt;
    have this_4 : (↑beta : ℕ) < k := beta.isLt;
    have this_5 : R.corresponding.replacementETT.rounds = ett.rounds :=
    by
     have := GoldbergSeymour.TreeSequence.positive T
     have :=
      GoldbergSeymour.CorrespondingExtendedTashkinovTree.rungAgreement
       (GoldbergSeymour.HierarchyReplacementPresentation.corresponding P)
     have := Fin.isLt alpha
     have := Fin.isLt beta
     have :=
      GoldbergSeymour.CorrespondingExtendedTashkinovTree.rungAgreement
       (GoldbergSeymour.HierarchyReplacementPresentation.corresponding R)
     omega;
    have this_6 : (↑q : ℕ) < H.dividerCount + (1 : ℕ) :=
    by
     have := GoldbergSeymour.TreeSequence.positive T
     have :=
      GoldbergSeymour.CorrespondingExtendedTashkinovTree.rungAgreement
       (GoldbergSeymour.HierarchyReplacementPresentation.corresponding P)
     have := Fin.isLt alpha
     have := Fin.isLt beta
     have :=
      GoldbergSeymour.CorrespondingExtendedTashkinovTree.rungAgreement
       (GoldbergSeymour.HierarchyReplacementPresentation.corresponding R)
     have := Fin.isLt q
     omega;
    have this_7 : (1 : ℕ) ≤ A.length := A.positive;
    have this_8 : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤
        min (A.length + m) T.length) ↦
    by omega
    ) (
    have this : (1 : ℕ) ≤ T.length := T.positive;
    have this : (1 : ℕ) ≤ A.length := A.positive;
    have this : P.corresponding.replacementETT.rounds = ett.rounds :=
    by
     have := GoldbergSeymour.TreeSequence.positive T
     have :=
      GoldbergSeymour.CorrespondingExtendedTashkinovTree.rungAgreement
       (GoldbergSeymour.HierarchyReplacementPresentation.corresponding P)
     omega;
    have this : (↑alpha : ℕ) < k := alpha.isLt;
    have this : (↑beta : ℕ) < k := beta.isLt;
    have this : R.corresponding.replacementETT.rounds = ett.rounds :=
    by
     have := GoldbergSeymour.TreeSequence.positive T
     have :=
      GoldbergSeymour.CorrespondingExtendedTashkinovTree.rungAgreement
       (GoldbergSeymour.HierarchyReplacementPresentation.corresponding P)
     have := Fin.isLt alpha
     have := Fin.isLt beta
     have :=
      GoldbergSeymour.CorrespondingExtendedTashkinovTree.rungAgreement
       (GoldbergSeymour.HierarchyReplacementPresentation.corresponding R)
     omega;
    have this : (↑q : ℕ) < H.dividerCount + (1 : ℕ) :=
    by
     have := GoldbergSeymour.TreeSequence.positive T
     have :=
      GoldbergSeymour.CorrespondingExtendedTashkinovTree.rungAgreement
       (GoldbergSeymour.HierarchyReplacementPresentation.corresponding P)
     have := Fin.isLt alpha
     have := Fin.isLt beta
     have :=
      GoldbergSeymour.CorrespondingExtendedTashkinovTree.rungAgreement
       (GoldbergSeymour.HierarchyReplacementPresentation.corresponding R)
     have := Fin.isLt q
     omega;
    have this : (1 : ℕ) ≤ A.length := A.positive;
    have this : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a : ¬min
        (A.length + m) T.length ≤ T.length) ↦
    by omega
    )) → (
    ∀ {U W : TreeSequence G e0}, TreeSequenceInitialSegment U T → TreeSequenceInitialSegment W T →
        U.length ≤ W.length → TreeSequenceInitialSegment U W) → Y.length = A.length + j →
        TreeSequenceInitialSegment B T → TreeSequenceInitialSegment Y T →
        TreeSequenceInitialSegment B X → TreeSequenceInitialSegment X Y →
        TreeSequenceInitialSegment Y Z → TreeSequenceInitialSegment Z T →
        TreeSequenceInitialSegment A Y → HierarchyFullTailPrefix R.counterexample
        (HierarchyFullTailLength R.counterexample - (1 : ℕ)) = Z → ColoredVertexSetElementary G
        sigma (TreeSequenceVertexSet Z) → (
    ∀ (rho : PartialEdgeColoring E k) (W : TreeSequence G e0), TreeSequenceInitialSegment W T →
    ∀ c ∈ TreeMissingColors rho W, c ∈ MissingColors G rho (T.vertex
        (HierarchyFirstMissingPosition rho T c)) ∧ (↑(HierarchyFirstMissingPosition rho T c) : ℕ)
        ≤ W.length) → gamma ∈ MissingColors G sigma (T.vertex (HierarchyFirstMissingPosition sigma
        T gamma)) ∧ (↑(HierarchyFirstMissingPosition sigma T gamma) : ℕ) ≤ A.length → beta ∈
        MissingColors G sigma (T.vertex (HierarchyFirstMissingPosition sigma T beta)) ∧
        (↑(HierarchyFirstMissingPosition sigma T beta) : ℕ) ≤ B.length →
        (↑(HierarchyFirstMissingPosition sigma T gamma) : ℕ) ≤ A.length →
        (↑(HierarchyFirstMissingPosition sigma T beta) : ℕ) ≤ B.length → (
    ∀ (W : TreeSequence G e0), TreeSequenceInitialSegment W T →
    ∀ (i : Fin (T.length + (1 : ℕ))), (↑i : ℕ) ≤ W.length → T.vertex i ∈ TreeSequenceVertexSet W)
        → (
    ∀ (W : TreeSequence G e0) (i : Fin (W.length + (1 : ℕ))), W.vertex i ∈ TreeSequenceVertexSet
        W) → d.theta ∈ TreeMissingColors sigma Y → d.theta ∈ MissingColors G sigma (T.vertex
        (HierarchyFirstMissingPosition sigma T d.theta)) ∧ (↑(HierarchyFirstMissingPosition sigma
        T d.theta) : ℕ) ≤ Y.length → (↑(HierarchyFirstMissingPosition d.switched.coloring T
        d.theta) : ℕ) = (HierarchyFullTailPrefix C j).length → d.theta ∉ D.biUnion
        (R.counterexample.good.gamma q) → gamma ≠ d.theta → TreeSequenceInitialSegment A Z →
        TreeSequenceInitialSegment B Z → (
    ∀ {U W : TreeSequence G e0}, TreeSequenceInitialSegment U W → TreeMissingColors sigma U ⊆
        TreeMissingColors sigma W) → gamma ∈ TreeMissingColors sigma Z → beta ∈ TreeMissingColors
        sigma Z → ColoredVertexSetElementary G sigma (TreeSequenceVertexSet
        (HierarchyFullTailPrefix R.counterexample (HierarchyFullTailLength R.counterexample - (1 :
        ℕ)))) → gamma ∈ TreeMissingColors sigma (HierarchyFullTailPrefix R.counterexample
        (HierarchyFullTailLength R.counterexample - (1 : ℕ))) ∧ beta ∈ TreeMissingColors sigma
        (HierarchyFullTailPrefix R.counterexample (HierarchyFullTailLength R.counterexample - (1 :
        ℕ))) → TwoColorComponent G sigma gamma beta (Sum.inl (T.vertex
        (HierarchyFirstMissingPosition sigma T gamma))) = TwoColorComponent G sigma gamma beta
        (Sum.inl (T.vertex (HierarchyFirstMissingPosition sigma T beta))) → (
    ∀ (rho : PartialEdgeColoring E k) (a b : Fin k) (v : V), Sum.inl v ∈ TwoColorComponent G rho a
        b (Sum.inl v)) → (
    ∀ (rho : PartialEdgeColoring E k) (a b : Fin k), a ≠ b → IsProperEdgeColoring G rho →
    ∀ (v : V), a ∈ MissingColors G rho v ∨ b ∈ MissingColors G rho v → ((TwoColorIncidenceGraph G
        rho a b).neighborSet (Sum.inl v)).Subsingleton) → (
    ∀ (rho : PartialEdgeColoring E k) (a b : Fin k), a ≠ b → IsProperEdgeColoring G rho →
    ∀ (u v w : V), u ≠ v → u ≠ w → v ≠ w → a ∈ MissingColors G rho u → b ∈ MissingColors G rho v →
        a ∈ MissingColors G rho w ∨ b ∈ MissingColors G rho w → TwoColorComponent G rho a b
        (Sum.inl u) = TwoColorComponent G rho a b (Sum.inl v) → Disjoint (TwoColorComponent G rho
        a b (Sum.inl w)) (TwoColorComponent G rho a b (Sum.inl u))) → B.length < T.length →
        T.vertex (HierarchyFirstMissingPosition sigma T gamma) ≠ T.vertex
        (HierarchyFirstMissingPosition sigma T beta) → T.vertex (HierarchyFirstMissingPosition
        sigma T gamma) ≠ T.vertex (Fin.last T.length) → False

private abbrev helperContinuation3731Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k),
        (
    ∀ (mu : PartialEdgeColoring E k), IsProperEdgeColoring G mu → IsOneEdgeUncolored mu e0 →
    ∀ (v : V), (MissingColors G mu v).Nonempty) →
    ∀ (d : HierarchySituationThreeDisjointData G k e0 input T phi ett base C ctx P alpha beta) (j
        : ℕ), HierarchyPathNumber C.hierarchy = j → (2 : ℕ) ≤ j → j < HierarchyFullTailLength C →
    let R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx := d.switched;
    let sigma : PartialEdgeColoring E k := R.coloring;
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength C;
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ));
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ));
    let Y : TreeSequence G e0 := HierarchyFullTailPrefix C j;
    let Z : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q; beta ∈ D →
    ∀ gamma ∈ R.counterexample.good.gamma q beta, gamma ∈ TreeMissingColors sigma A → gamma ≠ beta
        → d.theta ∉ D → A.length + j < T.length → Y.length = A.length + j →
        TreeSequenceInitialSegment Y T → TreeSequenceInitialSegment B X →
        TreeSequenceInitialSegment X Y → TreeSequenceInitialSegment Y Z →
        TreeSequenceInitialSegment Z T → TreeSequenceInitialSegment A Y →
        (↑(HierarchyFirstMissingPosition sigma T gamma) : ℕ) ≤ A.length →
        (↑(HierarchyFirstMissingPosition sigma T beta) : ℕ) ≤ B.length → (
    ∀ (W : TreeSequence G e0), TreeSequenceInitialSegment W T →
    ∀ (i : Fin (T.length + (1 : ℕ))), (↑i : ℕ) ≤ W.length → T.vertex i ∈ TreeSequenceVertexSet W)
        → (
    ∀ (W : TreeSequence G e0) (i : Fin (W.length + (1 : ℕ))), W.vertex i ∈ TreeSequenceVertexSet
        W) → d.theta ∈ TreeMissingColors sigma Y → d.theta ∈ MissingColors G sigma (T.vertex
        (HierarchyFirstMissingPosition sigma T d.theta)) ∧ (↑(HierarchyFirstMissingPosition sigma
        T d.theta) : ℕ) ≤ Y.length → d.theta ∉ D.biUnion (R.counterexample.good.gamma q) → gamma ≠
        d.theta → TreeSequenceInitialSegment A Z → (
    ∀ {U W : TreeSequence G e0}, TreeSequenceInitialSegment U W → TreeMissingColors sigma U ⊆
        TreeMissingColors sigma W) → (
    ∀ (rho : PartialEdgeColoring E k) (a b : Fin k) (v : V), Sum.inl v ∈ TwoColorComponent G rho a
        b (Sum.inl v)) → (
    ∀ (rho : PartialEdgeColoring E k) (a b : Fin k), a ≠ b → IsProperEdgeColoring G rho →
    ∀ (v : V), a ∈ MissingColors G rho v ∨ b ∈ MissingColors G rho v → ((TwoColorIncidenceGraph G
        rho a b).neighborSet (Sum.inl v)).Subsingleton) → (
    ∀ (rho : PartialEdgeColoring E k) (a b : Fin k), a ≠ b → IsProperEdgeColoring G rho →
    ∀ (u v w : V), u ≠ v → u ≠ w → v ≠ w → a ∈ MissingColors G rho u → b ∈ MissingColors G rho v →
        a ∈ MissingColors G rho w ∨ b ∈ MissingColors G rho w → TwoColorComponent G rho a b
        (Sum.inl u) = TwoColorComponent G rho a b (Sum.inl v) → Disjoint (TwoColorComponent G rho
        a b (Sum.inl w)) (TwoColorComponent G rho a b (Sum.inl u))) → T.vertex
        (HierarchyFirstMissingPosition sigma T gamma) ≠ T.vertex (Fin.last T.length) →
    let z : V ⊕ E := Sum.inl (T.vertex (Fin.last T.length));
    let mu2 : PartialEdgeColoring E k := TwoColorComponentSwap G sigma gamma beta z; (
    ∀ (W : TreeSequence G e0) (z : V ⊕ E) (rho : PartialEdgeColoring E k) (a b : Fin k), a ≠ b →
        IsProperEdgeColoring G rho → ColoredVertexSetElementary G rho (TreeSequenceVertexSet W) →
    ∀ (u v : V), u ∈ TreeSequenceVertexSet W → v ∈ TreeSequenceVertexSet W → a ∈ MissingColors G
        rho u → b ∈ MissingColors G rho v → Sum.inl u ∉ TwoColorComponent G rho a b z → Sum.inl v
        ∉ TwoColorComponent G rho a b z →
    ∀ w ∈ TreeSequenceVertexSet W, MissingColors G (TwoColorComponentSwap G rho a b z) w =
        MissingColors G rho w) → (
    ∀ (z : V ⊕ E) (rho : PartialEdgeColoring E k) (a b c : Fin k), a ≠ b → IsProperEdgeColoring G
        rho → c ≠ a → c ≠ b → HierarchyFirstMissingPosition (TwoColorComponentSwap G rho a b z) T
        c = HierarchyFirstMissingPosition rho T c) → (
    ∀ (old new : PartialEdgeColoring E k), (
    ∀ v ∈ TreeSequenceVertexSet Z, MissingColors G new v = MissingColors G old v) →
    ∀ (W : TreeSequence G e0), TreeSequenceInitialSegment W Z → TreeMissingColors new W =
        TreeMissingColors old W) → (
    ∀ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage S.counterexample.hierarchy (Fin.last
        S.counterexample.hierarchy.dividerCount) = A) → (
    ∀ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyFullTailPrefix S.counterexample (HierarchyFullTailLength S.counterexample - (1 :
        ℕ)) = Z) → (
    ∀ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), D =
        HierarchyStoredColorsAt S.counterexample.hierarchy (Fin.last
        S.counterexample.hierarchy.dividerCount) ∧
    ∀ eta ∈ D, R.counterexample.good.gamma q eta = S.counterexample.good.gamma (Fin.last
        S.counterexample.hierarchy.dividerCount) eta) → (
    ∀ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (nu :
        PartialEdgeColoring E k), IsOneEdgeUncolored nu e0 → HierarchyWeaklyStable
        S.counterexample.hierarchy (Fin.last S.counterexample.hierarchy.dividerCount) nu → (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < Y.length → nu (T.edge t) = S.coloring
        (T.edge t)) → (
    ∀ v ∈ TreeSequenceVertexSet Z, MissingColors G nu v = MissingColors G S.coloring v) →
    let et : ExtendedTashkinovTree G k e0 S.corresponding.replacementInput T S.coloring :=
        S.corresponding.replacementETT;
    let n : Fin (et.rounds + (1 : ℕ)) := Fin.last et.rounds;
    let Tn : TreeSequence G e0 := et.series.data.tree n.castSucc; et.series.data.kind n = some
        TashkinovExtensionKind.PE ∧ TashkinovAugmentationSequence nu Tn Y ∨ (et.series.data.kind n
        = some TashkinovExtensionKind.SE ∨ et.series.data.kind n = some TashkinovExtensionKind.RE)
        ∧
    ∃ (f : E) (seed : TreeSequence G e0), et.series.data.connectingEdges n = ({ f } : Finset E) ∧
        TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence nu seed Y) → (
    ∀ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), (0 : ℕ) <
        S.counterexample.hierarchy.dividerCount ∧ gamma ∈ TreeMissingColors S.coloring
        (S.counterexample.hierarchy.stage (⟨S.counterexample.hierarchy.dividerCount,
    by
         have := GoldbergSeymour.TreeSequence.positive T
         have :=
          GoldbergSeymour.CorrespondingExtendedTashkinovTree.rungAgreement
           (GoldbergSeymour.HierarchyReplacementPresentation.corresponding
            S)
         omega
    ⟩ : Fin (S.counterexample.hierarchy.dividerCount + (2 : ℕ)))) ∨
        S.counterexample.hierarchy.dividerCount = (0 : ℕ) ∧ gamma ∈ TreeMissingColors S.coloring
        (S.corresponding.replacementETT.series.data.tree (Fin.last
        S.corresponding.replacementETT.rounds).castSucc)) → TashkinovAugmentationSequence sigma Y
        T → gamma ∈ TreeMissingColors mu2 Y ∧ beta ∈ TreeMissingColors mu2 Y → A.length < Y.length
        →
    ∀ (R1 : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), R1.coloring = mu2
        →
    let rho : PartialEdgeColoring E k := R1.coloring; (
    ∀ v ∈ TreeSequenceVertexSet Z, MissingColors G rho v = MissingColors G sigma v) →
        ColoredVertexSetElementary G rho (TreeSequenceVertexSet Z) → HierarchyFirstMissingPosition
        rho T gamma = HierarchyFirstMissingPosition sigma T gamma → HierarchyFirstMissingPosition
        rho T beta = HierarchyFirstMissingPosition sigma T beta → gamma ∈ MissingColors G rho
        (T.vertex (HierarchyFirstMissingPosition sigma T gamma)) → d.theta ∈ MissingColors G rho
        (T.vertex (HierarchyFirstMissingPosition sigma T d.theta)) → d.theta ∈ MissingColors G rho
        (Y.vertex (Fin.last Y.length)) → gamma ∈ MissingColors G rho (T.vertex (Fin.last
        T.length)) → (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < Y.length → rho (T.edge t) ≠ some gamma)
        → (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < Y.length → rho (T.edge t) ≠ some
        d.theta) → gamma ∈ TreeMissingColors rho Z ∧ d.theta ∈ TreeMissingColors rho Z →
        TwoColorComponent G rho gamma d.theta (Sum.inl (T.vertex (HierarchyFirstMissingPosition
        sigma T gamma))) = TwoColorComponent G rho gamma d.theta (Sum.inl (T.vertex
        (HierarchyFirstMissingPosition sigma T d.theta))) → T.vertex
        (HierarchyFirstMissingPosition sigma T gamma) ≠ T.vertex (HierarchyFirstMissingPosition
        sigma T d.theta) → T.vertex (HierarchyFirstMissingPosition sigma T d.theta) ≠ T.vertex
        (Fin.last T.length) → False

private abbrev helperContinuation3042Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k),
        (
    ∀ (mu : PartialEdgeColoring E k), IsProperEdgeColoring G mu → IsOneEdgeUncolored mu e0 →
    ∀ (v : V), (MissingColors G mu v).Nonempty) →
    ∀ (d : HierarchySituationThreeDisjointData G k e0 input T phi ett base C ctx P alpha beta) (j
        : ℕ), HierarchyPathNumber C.hierarchy = j → (2 : ℕ) ≤ j → j < HierarchyFullTailLength C →
    let R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx := d.switched;
    let sigma : PartialEdgeColoring E k := R.coloring;
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength C;
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ));
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ));
    let Y : TreeSequence G e0 := HierarchyFullTailPrefix C j;
    let Z : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q; beta ∈ D → beta ∈ TreeMissingColors
        sigma B → Disjoint (R.counterexample.good.gamma q beta ∪ ({ beta } : Finset (Fin k))) ({c
        : Fin k |
    ∃ (r : Fin T.length), A.length ≤ (↑r : ℕ) ∧ (↑r : ℕ) < A.length + j ∧ sigma (T.edge r) = some
        c} : Finset (Fin k)) → d.theta ∈ MissingColors G sigma (Y.vertex (Fin.last Y.length)) →
    ∀ gamma ∈ R.counterexample.good.gamma q beta, gamma ∈ TreeMissingColors sigma A → gamma ≠ beta
        → d.theta ∉ D → HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) = A
        → TreeSequenceInitialSegment A T → A.length + j < T.length → (
    ∀ {U W : TreeSequence G e0}, TreeSequenceInitialSegment U T → TreeSequenceInitialSegment W T →
        U.length ≤ W.length → TreeSequenceInitialSegment U W) → Y.length = A.length + j →
        TreeSequenceInitialSegment B T → TreeSequenceInitialSegment Y T →
        TreeSequenceInitialSegment B X → TreeSequenceInitialSegment X Y →
        TreeSequenceInitialSegment Y Z → TreeSequenceInitialSegment Z T →
        TreeSequenceInitialSegment A Y → HierarchyFullTailPrefix R.counterexample
        (HierarchyFullTailLength R.counterexample - (1 : ℕ)) = Z → ColoredVertexSetElementary G
        sigma (TreeSequenceVertexSet Z) → (
    ∀ (rho : PartialEdgeColoring E k) (W : TreeSequence G e0), TreeSequenceInitialSegment W T →
    ∀ c ∈ TreeMissingColors rho W, c ∈ MissingColors G rho (T.vertex
        (HierarchyFirstMissingPosition rho T c)) ∧ (↑(HierarchyFirstMissingPosition rho T c) : ℕ)
        ≤ W.length) → gamma ∈ MissingColors G sigma (T.vertex (HierarchyFirstMissingPosition sigma
        T gamma)) ∧ (↑(HierarchyFirstMissingPosition sigma T gamma) : ℕ) ≤ A.length →
        (↑(HierarchyFirstMissingPosition sigma T gamma) : ℕ) ≤ A.length →
        (↑(HierarchyFirstMissingPosition sigma T beta) : ℕ) ≤ B.length → (
    ∀ (W : TreeSequence G e0), TreeSequenceInitialSegment W T →
    ∀ (i : Fin (T.length + (1 : ℕ))), (↑i : ℕ) ≤ W.length → T.vertex i ∈ TreeSequenceVertexSet W)
        → (
    ∀ (W : TreeSequence G e0) (i : Fin (W.length + (1 : ℕ))), W.vertex i ∈ TreeSequenceVertexSet
        W) → d.theta ∈ TreeMissingColors sigma Y → d.theta ∈ MissingColors G sigma (T.vertex
        (HierarchyFirstMissingPosition sigma T d.theta)) ∧ (↑(HierarchyFirstMissingPosition sigma
        T d.theta) : ℕ) ≤ Y.length → (↑(HierarchyFirstMissingPosition d.switched.coloring T
        d.theta) : ℕ) = (HierarchyFullTailPrefix C j).length → d.theta ∉ D.biUnion
        (R.counterexample.good.gamma q) → gamma ≠ d.theta → TreeSequenceInitialSegment A Z → (
    ∀ {U W : TreeSequence G e0}, TreeSequenceInitialSegment U W → TreeMissingColors sigma U ⊆
        TreeMissingColors sigma W) → gamma ∈ TreeMissingColors sigma Z → beta ∈ TreeMissingColors
        sigma Z → ColoredVertexSetElementary G sigma (TreeSequenceVertexSet
        (HierarchyFullTailPrefix R.counterexample (HierarchyFullTailLength R.counterexample - (1 :
        ℕ)))) → gamma ∈ TreeMissingColors sigma (HierarchyFullTailPrefix R.counterexample
        (HierarchyFullTailLength R.counterexample - (1 : ℕ))) ∧ beta ∈ TreeMissingColors sigma
        (HierarchyFullTailPrefix R.counterexample (HierarchyFullTailLength R.counterexample - (1 :
        ℕ))) → (
    ∀ (rho : PartialEdgeColoring E k) (a b : Fin k) (v : V), Sum.inl v ∈ TwoColorComponent G rho a
        b (Sum.inl v)) → (
    ∀ (rho : PartialEdgeColoring E k) (a b : Fin k), a ≠ b → IsProperEdgeColoring G rho →
    ∀ (v : V), a ∈ MissingColors G rho v ∨ b ∈ MissingColors G rho v → ((TwoColorIncidenceGraph G
        rho a b).neighborSet (Sum.inl v)).Subsingleton) → (
    ∀ (rho : PartialEdgeColoring E k) (a b : Fin k), a ≠ b → IsProperEdgeColoring G rho →
    ∀ (u v w : V), u ≠ v → u ≠ w → v ≠ w → a ∈ MissingColors G rho u → b ∈ MissingColors G rho v →
        a ∈ MissingColors G rho w ∨ b ∈ MissingColors G rho w → TwoColorComponent G rho a b
        (Sum.inl u) = TwoColorComponent G rho a b (Sum.inl v) → Disjoint (TwoColorComponent G rho
        a b (Sum.inl w)) (TwoColorComponent G rho a b (Sum.inl u))) → T.vertex
        (HierarchyFirstMissingPosition sigma T gamma) ≠ T.vertex (Fin.last T.length) → Disjoint
        (TwoColorComponent G sigma gamma beta (Sum.inl (T.vertex (Fin.last T.length))))
        (TwoColorComponent G sigma gamma beta (Sum.inl (T.vertex (HierarchyFirstMissingPosition
        sigma T gamma)))) →
    let z : V ⊕ E := Sum.inl (T.vertex (Fin.last T.length));
    let mu2 : PartialEdgeColoring E k := TwoColorComponentSwap G sigma gamma beta z;
        IsOneEdgeUncolored mu2 e0 → gamma ∈ MissingColors G mu2 (T.vertex
        (HierarchyFirstMissingPosition sigma T gamma)) → gamma ∈ MissingColors G mu2 (T.vertex
        (Fin.last T.length)) → (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < A.length + j → mu2 (T.edge t) = sigma
        (T.edge t)) → (
    ∀ (W : TreeSequence G e0) (z : V ⊕ E) (rho : PartialEdgeColoring E k) (a b : Fin k), a ≠ b →
        IsProperEdgeColoring G rho → ColoredVertexSetElementary G rho (TreeSequenceVertexSet W) →
    ∀ (u v : V), u ∈ TreeSequenceVertexSet W → v ∈ TreeSequenceVertexSet W → a ∈ MissingColors G
        rho u → b ∈ MissingColors G rho v → Sum.inl u ∉ TwoColorComponent G rho a b z → Sum.inl v
        ∉ TwoColorComponent G rho a b z →
    ∀ w ∈ TreeSequenceVertexSet W, MissingColors G (TwoColorComponentSwap G rho a b z) w =
        MissingColors G rho w) → (
    ∀ (W : TreeSequence G e0), TreeSequenceInitialSegment W T →
    ∀ (rho sigma : PartialEdgeColoring E k) (c : Fin k), ColoredVertexSetElementary G rho
        (TreeSequenceVertexSet W) → (
    ∀ v ∈ TreeSequenceVertexSet W, MissingColors G sigma v = MissingColors G rho v) → c ∈
        TreeMissingColors rho W → HierarchyFirstMissingPosition sigma T c =
        HierarchyFirstMissingPosition rho T c) → (
    ∀ (z : V ⊕ E) (rho : PartialEdgeColoring E k) (a b c : Fin k), a ≠ b → IsProperEdgeColoring G
        rho → c ≠ a → c ≠ b → HierarchyFirstMissingPosition (TwoColorComponentSwap G rho a b z) T
        c = HierarchyFirstMissingPosition rho T c) → (
    ∀ v ∈ TreeSequenceVertexSet Z, MissingColors G mu2 v = MissingColors G sigma v) → (
    ∀ (old new : PartialEdgeColoring E k), (
    ∀ v ∈ TreeSequenceVertexSet Z, MissingColors G new v = MissingColors G old v) →
    ∀ (W : TreeSequence G e0), TreeSequenceInitialSegment W Z → TreeMissingColors new W =
        TreeMissingColors old W) → (
    ∀ eta ∈ D, HierarchyFirstMissingPosition mu2 T eta = HierarchyFirstMissingPosition sigma T
        eta) → (
    ∀ eta ∈ D, gamma ∈ R.counterexample.good.gamma q eta ∨ beta ∈ R.counterexample.good.gamma q
        eta → (↑(HierarchyFirstMissingPosition sigma T eta) : ℕ) ≤ Y.length) → (
    ∀ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage S.counterexample.hierarchy (Fin.last
        S.counterexample.hierarchy.dividerCount) = A) → (
    ∀ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyFullTailPrefix S.counterexample (HierarchyFullTailLength S.counterexample - (1 :
        ℕ)) = Z) → (
    ∀ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), D =
        HierarchyStoredColorsAt S.counterexample.hierarchy (Fin.last
        S.counterexample.hierarchy.dividerCount) ∧
    ∀ eta ∈ D, R.counterexample.good.gamma q eta = S.counterexample.good.gamma (Fin.last
        S.counterexample.hierarchy.dividerCount) eta) → (
    ∀ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (nu :
        PartialEdgeColoring E k), IsOneEdgeUncolored nu e0 → HierarchyWeaklyStable
        S.counterexample.hierarchy (Fin.last S.counterexample.hierarchy.dividerCount) nu → (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < Y.length → nu (T.edge t) = S.coloring
        (T.edge t)) → (
    ∀ v ∈ TreeSequenceVertexSet Z, MissingColors G nu v = MissingColors G S.coloring v) →
    let et : ExtendedTashkinovTree G k e0 S.corresponding.replacementInput T S.coloring :=
        S.corresponding.replacementETT;
    let n : Fin (et.rounds + (1 : ℕ)) := Fin.last et.rounds;
    let Tn : TreeSequence G e0 := et.series.data.tree n.castSucc; et.series.data.kind n = some
        TashkinovExtensionKind.PE ∧ TashkinovAugmentationSequence nu Tn Y ∨ (et.series.data.kind n
        = some TashkinovExtensionKind.SE ∨ et.series.data.kind n = some TashkinovExtensionKind.RE)
        ∧
    ∃ (f : E) (seed : TreeSequence G e0), et.series.data.connectingEdges n = ({ f } : Finset E) ∧
        TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence nu seed Y) → False

private noncomputable abbrev helperC11319.{u_1, u_2} :
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
  (P :
      HierarchyReplacementPresentation G k e0 input T phi ett
        base C ctx) →
  (alpha beta : Fin k) →
  (d :
      HierarchySituationThreeDisjointData G k e0 input T phi
        ett base C ctx P alpha beta) →
  let R :
    HierarchyReplacementPresentation G k e0 input T phi
      ett base C ctx :=
    d.switched;
  let sigma : PartialEdgeColoring E k := R.coloring;
  (gamma : Fin k) →
  (
  ∀ (W : TreeSequence G e0)
     (i : Fin (W.length + (1 : ℕ))),
  W.vertex i ∈ TreeSequenceVertexSet W) →
  T.vertex
        (HierarchyFirstMissingPosition sigma T
          gamma) ≠
      T.vertex (Fin.last T.length) →
  let z : V ⊕ E :=
    Sum.inl (T.vertex (Fin.last T.length));
  let mu2 : PartialEdgeColoring E k :=
    TwoColorComponentSwap G sigma gamma beta z;
  gamma ∈
      MissingColors G mu2
        (T.vertex
          (HierarchyFirstMissingPosition sigma T
            gamma)) →
  gamma ∈
      MissingColors G mu2
        (T.vertex (Fin.last T.length)) →
  (corr1 :
      CorrespondingExtendedTashkinovTree G k e0
        R.corresponding.replacementETT mu2 T) →
  MaximumProperty corr1.replacementETT →
  (bs1 :
      HierarchyBase corr1.replacementETT
        mu2) →
  (K1 :
      TashkinovHierarchy
        corr1.replacementETT bs1) →
  GoodHierarchy K1 →
  HierarchyCounterexample bs1 := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d R sigma gamma vertexMemSelf
      hgammaTerminalDistinct z mu2 hgammaFirstMu2 hgammaTerminalMu2 corr1 hmax1 bs1 K1 good1
  exact {
    positive := Nat.lt_of_lt_of_le (by decide) corr1.replacementETT.roundsPositive
    hierarchy := K1
    good := good1
    maximum := hmax1
    notElementary := by
      intro he
      exact Finset.disjoint_left.mp (he
        (vertexMemSelf T (HierarchyFirstMissingPosition sigma T gamma))
        (vertexMemSelf T (Fin.last T.length)) hgammaTerminalDistinct)
        hgammaFirstMu2 hgammaTerminalMu2 }

private noncomputable abbrev helperC21693.{u_1, u_2} :
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
  (P :
      HierarchyReplacementPresentation G k e0 input T phi ett
        base C ctx) →
  (alpha beta : Fin k) →
  (d :
      HierarchySituationThreeDisjointData G k e0 input T phi
        ett base C ctx P alpha beta) →
  (j : ℕ) →
  let Y : TreeSequence G e0 :=
    HierarchyFullTailPrefix C j;
  (gamma : Fin k) →
  TreeSequenceInitialSegment Y T →
  (
  ∀ (W : TreeSequence G e0)
     (i : Fin (W.length + (1 : ℕ))),
  W.vertex i ∈ TreeSequenceVertexSet W) →
  let z : V ⊕ E :=
    Sum.inl (T.vertex (Fin.last T.length));
  (R1 :
      HierarchyReplacementPresentation G k e0
        input T phi ett base C ctx) →
  let rho : PartialEdgeColoring E k :=
    R1.coloring;
  let mu3 : PartialEdgeColoring E k :=
    TwoColorComponentSwap G rho gamma d.theta z;
  (corr2 :
      CorrespondingExtendedTashkinovTree G k e0
        R1.corresponding.replacementETT mu3 T) →
  MaximumProperty corr2.replacementETT →
  (bs2 :
      HierarchyBase corr2.replacementETT
        mu3) →
  (K2 :
      TashkinovHierarchy
        corr2.replacementETT bs2) →
  GoodHierarchy K2 →
  d.theta ∈
      MissingColors G mu3
        (T.vertex
          (Fin.last T.length)) →
  d.theta ∈
      MissingColors G mu3
        (Y.vertex
          (Fin.last Y.length)) →
  Y.vertex (Fin.last Y.length) ≠
      T.vertex
        (Fin.last T.length) →
  HierarchyCounterexample bs2 := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d j Y gamma hYtoT
      vertexMemSelf z R1 rho mu3 corr2 hmax2 bs2 K2 good2 hthetaTerminalMu3 hthetaYMu3
      hYTerminalDistinct
  exact {
    positive := Nat.lt_of_lt_of_le (by decide) corr2.replacementETT.roundsPositive
    hierarchy := K2
    good := good2
    maximum := hmax2
    notElementary := by
      intro he
      exact Finset.disjoint_left.mp (he
        (TreeSequenceInitialSegmentVertexSetSubset hYtoT (vertexMemSelf Y (Fin.last Y.length)))
        (vertexMemSelf T (Fin.last T.length)) hYTerminalDistinct)
        hthetaYMu3 hthetaTerminalMu3 }

private abbrev helperContinuation3727Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k)
        (hvertexMissing :
    ∀ (mu : PartialEdgeColoring E k), IsProperEdgeColoring G mu → IsOneEdgeUncolored mu e0 →
    ∀ (v : V), (MissingColors G mu v).Nonempty) (d : HierarchySituationThreeDisjointData G k e0
        input T phi ett base C ctx P alpha beta) (j : ℕ) (hj : HierarchyPathNumber C.hierarchy =
        j) (hpathLower : (2 : ℕ) ≤ j) (hpathUpper : j < HierarchyFullTailLength C),
    let R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx := d.switched;
    let sigma : PartialEdgeColoring E k := R.coloring;
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength C;
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ));
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ));
    let Y : TreeSequence G e0 := HierarchyFullTailPrefix C j;
    let Z : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q;
    ∀ (hbetaStored : beta ∈ D) (hbetaTail : Disjoint (R.counterexample.good.gamma q beta ∪
        ({ beta } : Finset (Fin k))) ({c : Fin k |
    ∃ (r : Fin T.length), A.length ≤ (↑r : ℕ) ∧ (↑r : ℕ) < A.length + j ∧ sigma (T.edge r) = some
        c} : Finset (Fin k))) (hthetaMissingY : d.theta ∈ MissingColors G sigma (Y.vertex
        (Fin.last Y.length))) (gamma : Fin k) (hgammaBeta : gamma ∈ R.counterexample.good.gamma q
        beta) (hgammaA : gamma ∈ TreeMissingColors sigma A) (hgammaNeBeta : gamma ≠ beta)
        (hthetaUnstored' : d.theta ∉ D) (sameStar : HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount) = A) (hcutJstrict : A.length + j < T.length) (hYlen : Y.length =
        A.length + j) (hYtoT : TreeSequenceInitialSegment Y T) (hBtoX : TreeSequenceInitialSegment
        B X) (hXtoY : TreeSequenceInitialSegment X Y) (hYtoZ : TreeSequenceInitialSegment Y Z)
        (hZtoT : TreeSequenceInitialSegment Z T) (hAtoY : TreeSequenceInitialSegment A Y) (hElemZ
        : ColoredVertexSetElementary G sigma (TreeSequenceVertexSet Z)) (hgammaFirst : gamma ∈
        MissingColors G sigma (T.vertex (HierarchyFirstMissingPosition sigma T gamma)) ∧
        (↑(HierarchyFirstMissingPosition sigma T gamma) : ℕ) ≤ A.length) (hgammaFirstLe :
        (↑(HierarchyFirstMissingPosition sigma T gamma) : ℕ) ≤ A.length) (hbetaFirstLe :
        (↑(HierarchyFirstMissingPosition sigma T beta) : ℕ) ≤ B.length) (vertexMemT :
    ∀ (W : TreeSequence G e0), TreeSequenceInitialSegment W T →
    ∀ (i : Fin (T.length + (1 : ℕ))), (↑i : ℕ) ≤ W.length → T.vertex i ∈ TreeSequenceVertexSet W)
        (vertexMemSelf :
    ∀ (W : TreeSequence G e0) (i : Fin (W.length + (1 : ℕ))), W.vertex i ∈ TreeSequenceVertexSet
        W) (hthetaY : d.theta ∈ TreeMissingColors sigma Y) (hthetaFirst : d.theta ∈ MissingColors
        G sigma (T.vertex (HierarchyFirstMissingPosition sigma T d.theta)) ∧
        (↑(HierarchyFirstMissingPosition sigma T d.theta) : ℕ) ≤ Y.length) (hthetaFirstIndex :
        (↑(HierarchyFirstMissingPosition d.switched.coloring T d.theta) : ℕ) =
        (HierarchyFullTailPrefix C j).length) (hthetaOutsideGamma : d.theta ∉ D.biUnion
        (R.counterexample.good.gamma q)) (hgammaNeTheta : gamma ≠ d.theta) (hAtoZ :
        TreeSequenceInitialSegment A Z) (treeMissingSubset :
    ∀ {U W : TreeSequence G e0}, TreeSequenceInitialSegment U W → TreeMissingColors sigma U ⊆
        TreeMissingColors sigma W) (hgammaMissingZ : gamma ∈ TreeMissingColors sigma Z)
        (hbetaMissingZ : beta ∈ TreeMissingColors sigma Z) (hchangeElementary :
        ColoredVertexSetElementary G sigma (TreeSequenceVertexSet (HierarchyFullTailPrefix
        R.counterexample (HierarchyFullTailLength R.counterexample - (1 : ℕ))))) (componentSelf :
    ∀ (rho : PartialEdgeColoring E k) (a b : Fin k) (v : V), Sum.inl v ∈ TwoColorComponent G rho a
        b (Sum.inl v)) (componentLeaf :
    ∀ (rho : PartialEdgeColoring E k) (a b : Fin k), a ≠ b → IsProperEdgeColoring G rho →
    ∀ (v : V), a ∈ MissingColors G rho v ∨ b ∈ MissingColors G rho v → ((TwoColorIncidenceGraph G
        rho a b).neighborSet (Sum.inl v)).Subsingleton) (separateComponents :
    ∀ (rho : PartialEdgeColoring E k) (a b : Fin k), a ≠ b → IsProperEdgeColoring G rho →
    ∀ (u v w : V), u ≠ v → u ≠ w → v ≠ w → a ∈ MissingColors G rho u → b ∈ MissingColors G rho v →
        a ∈ MissingColors G rho w ∨ b ∈ MissingColors G rho w → TwoColorComponent G rho a b
        (Sum.inl u) = TwoColorComponent G rho a b (Sum.inl v) → Disjoint (TwoColorComponent G rho
        a b (Sum.inl w)) (TwoColorComponent G rho a b (Sum.inl u))) (hgammaTerminalDistinct :
        T.vertex (HierarchyFirstMissingPosition sigma T gamma) ≠ T.vertex (Fin.last T.length)),
    let z : V ⊕ E := Sum.inl (T.vertex (Fin.last T.length));
    let mu2 : PartialEdgeColoring E k := TwoColorComponentSwap G sigma gamma beta z;
    ∀ (hgammaTerminalMu2 : gamma ∈ MissingColors G mu2 (T.vertex (Fin.last T.length)))
        (hfixedThroughY :
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < A.length + j → mu2 (T.edge t) = sigma
        (T.edge t)) (prefixMissing :
    ∀ (W : TreeSequence G e0) (z : V ⊕ E) (rho : PartialEdgeColoring E k) (a b : Fin k), a ≠ b →
        IsProperEdgeColoring G rho → ColoredVertexSetElementary G rho (TreeSequenceVertexSet W) →
    ∀ (u v : V), u ∈ TreeSequenceVertexSet W → v ∈ TreeSequenceVertexSet W → a ∈ MissingColors G
        rho u → b ∈ MissingColors G rho v → Sum.inl u ∉ TwoColorComponent G rho a b z → Sum.inl v
        ∉ TwoColorComponent G rho a b z →
    ∀ w ∈ TreeSequenceVertexSet W, MissingColors G (TwoColorComponentSwap G rho a b z) w =
        MissingColors G rho w) (firstPreserved :
    ∀ (W : TreeSequence G e0), TreeSequenceInitialSegment W T →
    ∀ (rho sigma : PartialEdgeColoring E k) (c : Fin k), ColoredVertexSetElementary G rho
        (TreeSequenceVertexSet W) → (
    ∀ v ∈ TreeSequenceVertexSet W, MissingColors G sigma v = MissingColors G rho v) → c ∈
        TreeMissingColors rho W → HierarchyFirstMissingPosition sigma T c =
        HierarchyFirstMissingPosition rho T c) (firstUnaffected :
    ∀ (z : V ⊕ E) (rho : PartialEdgeColoring E k) (a b c : Fin k), a ≠ b → IsProperEdgeColoring G
        rho → c ≠ a → c ≠ b → HierarchyFirstMissingPosition (TwoColorComponentSwap G rho a b z) T
        c = HierarchyFirstMissingPosition rho T c) (hmissingMu2 :
    ∀ v ∈ TreeSequenceVertexSet Z, MissingColors G mu2 v = MissingColors G sigma v)
        (missingTransport :
    ∀ (old new : PartialEdgeColoring E k), (
    ∀ v ∈ TreeSequenceVertexSet Z, MissingColors G new v = MissingColors G old v) →
    ∀ (W : TreeSequence G e0), TreeSequenceInitialSegment W Z → TreeMissingColors new W =
        TreeMissingColors old W) (sameStarAll :
    ∀ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage S.counterexample.hierarchy (Fin.last
        S.counterexample.hierarchy.dividerCount) = A) (samePenultimate :
    ∀ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyFullTailPrefix S.counterexample (HierarchyFullTailLength S.counterexample - (1 :
        ℕ)) = Z) (sameLast :
    ∀ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), D =
        HierarchyStoredColorsAt S.counterexample.hierarchy (Fin.last
        S.counterexample.hierarchy.dividerCount) ∧
    ∀ eta ∈ D, R.counterexample.good.gamma q eta = S.counterexample.good.gamma (Fin.last
        S.counterexample.hierarchy.dividerCount) eta) (routeToY :
    ∀ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (nu :
        PartialEdgeColoring E k), IsOneEdgeUncolored nu e0 → HierarchyWeaklyStable
        S.counterexample.hierarchy (Fin.last S.counterexample.hierarchy.dividerCount) nu → (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < Y.length → nu (T.edge t) = S.coloring
        (T.edge t)) → (
    ∀ v ∈ TreeSequenceVertexSet Z, MissingColors G nu v = MissingColors G S.coloring v) →
    have et : ExtendedTashkinovTree G k e0 S.corresponding.replacementInput T S.coloring :=
        S.corresponding.replacementETT;
    have n : Fin (et.rounds + (1 : ℕ)) := Fin.last et.rounds;
    have Tn : TreeSequence G e0 := et.series.data.tree n.castSucc; et.series.data.kind n = some
        TashkinovExtensionKind.PE ∧ TashkinovAugmentationSequence nu Tn Y ∨ (et.series.data.kind n
        = some TashkinovExtensionKind.SE ∨ et.series.data.kind n = some TashkinovExtensionKind.RE)
        ∧
    ∃ (f : E) (seed : TreeSequence G e0), et.series.data.connectingEdges n = ({ f } : Finset E) ∧
        TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence nu seed Y) (caseGamma :
    ∀ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), (0 : ℕ) <
        S.counterexample.hierarchy.dividerCount ∧ gamma ∈ TreeMissingColors S.coloring
        (S.counterexample.hierarchy.stage (⟨S.counterexample.hierarchy.dividerCount,
        Nat.lt_add_of_pos_right (
    by omega
    )⟩ : Fin (S.counterexample.hierarchy.dividerCount + (2 : ℕ)))) ∨
        S.counterexample.hierarchy.dividerCount = (0 : ℕ) ∧ gamma ∈ TreeMissingColors S.coloring
        (S.corresponding.replacementETT.series.data.tree (Fin.last
        S.corresponding.replacementETT.rounds).castSucc)) (hsuffixY :
        TashkinovAugmentationSequence sigma Y T) (hsplitMissing2 : gamma ∈ TreeMissingColors mu2 Y
        ∧ beta ∈ TreeMissingColors mu2 Y) (hAYstrict : A.length < Y.length) (R1 :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (hR1 : R1.coloring =
        mu2) (sameFullPrefix :
    ∀ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (m : ℕ),
        HierarchyFullTailPrefix S.counterexample m = HierarchyFullTailPrefix C m) (hthetaNotRaw :
        d.theta ∉ TashkinovStoredColors R.corresponding.replacementETT.series.data (Fin.last
        R.corresponding.replacementETT.rounds)), False

private abbrev helperContinuation3933Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k)
        (hvertexMissing :
    ∀ (mu : PartialEdgeColoring E k), IsProperEdgeColoring G mu → IsOneEdgeUncolored mu e0 →
    ∀ (v : V), (MissingColors G mu v).Nonempty) (d : HierarchySituationThreeDisjointData G k e0
        input T phi ett base C ctx P alpha beta) (j : ℕ) (hj : HierarchyPathNumber C.hierarchy =
        j) (hpathLower : (2 : ℕ) ≤ j) (hpathUpper : j < HierarchyFullTailLength C),
    let R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx := d.switched;
    let sigma : PartialEdgeColoring E k := R.coloring;
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength C;
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ));
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ));
    let Y : TreeSequence G e0 := HierarchyFullTailPrefix C j;
    let Z : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q;
    ∀ (hbetaStored : beta ∈ D) (hbetaB : beta ∈ TreeMissingColors sigma B) (hbetaTail : Disjoint
        (R.counterexample.good.gamma q beta ∪ ({ beta } : Finset (Fin k))) ({c : Fin k |
    ∃ (r : Fin T.length), A.length ≤ (↑r : ℕ) ∧ (↑r : ℕ) < A.length + j ∧ sigma (T.edge r) = some
        c} : Finset (Fin k))) (hthetaMissingY : d.theta ∈ MissingColors G sigma (Y.vertex
        (Fin.last Y.length))) (gamma : Fin k) (hgammaBeta : gamma ∈ R.counterexample.good.gamma q
        beta) (hgammaA : gamma ∈ TreeMissingColors sigma A) (hgammaNeBeta : gamma ≠ beta)
        (hthetaUnstored' : d.theta ∉ D) (sameStar : HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount) = A) (hAtoT : TreeSequenceInitialSegment A T) (htail : j ≤
        T.length - A.length) (hcutJstrict : A.length + j < T.length) (fullPrefixEq :
    ∀ (m : ℕ), HierarchyFullTailPrefix C m = TreeSequencePrefix T (min (A.length + m) T.length)
        (le_min (le_trans A.positive (Nat.le_add_right _ _)) T.positive) (
    by omega
    )) (commonPrefix :
    ∀ {U W : TreeSequence G e0}, TreeSequenceInitialSegment U T → TreeSequenceInitialSegment W T →
        U.length ≤ W.length → TreeSequenceInitialSegment U W) (hYlen : Y.length = A.length + j)
        (hBtoT : TreeSequenceInitialSegment B T) (hYtoT : TreeSequenceInitialSegment Y T) (hBtoX :
        TreeSequenceInitialSegment B X) (hXtoY : TreeSequenceInitialSegment X Y) (hYtoZ :
        TreeSequenceInitialSegment Y Z) (hZtoT : TreeSequenceInitialSegment Z T) (hAtoY :
        TreeSequenceInitialSegment A Y) (penultimatePrefixEq : HierarchyFullTailPrefix
        R.counterexample (HierarchyFullTailLength R.counterexample - (1 : ℕ)) = Z) (hElemZ :
        ColoredVertexSetElementary G sigma (TreeSequenceVertexSet Z)) (firstWitness :
    ∀ (rho : PartialEdgeColoring E k) (W : TreeSequence G e0), TreeSequenceInitialSegment W T →
    ∀ c ∈ TreeMissingColors rho W, c ∈ MissingColors G rho (T.vertex
        (HierarchyFirstMissingPosition rho T c)) ∧ (↑(HierarchyFirstMissingPosition rho T c) : ℕ)
        ≤ W.length) (hgammaFirst : gamma ∈ MissingColors G sigma (T.vertex
        (HierarchyFirstMissingPosition sigma T gamma)) ∧ (↑(HierarchyFirstMissingPosition sigma T
        gamma) : ℕ) ≤ A.length) (hgammaFirstLe : (↑(HierarchyFirstMissingPosition sigma T gamma) :
        ℕ) ≤ A.length) (hbetaFirstLe : (↑(HierarchyFirstMissingPosition sigma T beta) : ℕ) ≤
        B.length) (vertexMemT :
    ∀ (W : TreeSequence G e0), TreeSequenceInitialSegment W T →
    ∀ (i : Fin (T.length + (1 : ℕ))), (↑i : ℕ) ≤ W.length → T.vertex i ∈ TreeSequenceVertexSet W)
        (vertexMemSelf :
    ∀ (W : TreeSequence G e0) (i : Fin (W.length + (1 : ℕ))), W.vertex i ∈ TreeSequenceVertexSet
        W) (hthetaY : d.theta ∈ TreeMissingColors sigma Y) (hthetaFirst : d.theta ∈ MissingColors
        G sigma (T.vertex (HierarchyFirstMissingPosition sigma T d.theta)) ∧
        (↑(HierarchyFirstMissingPosition sigma T d.theta) : ℕ) ≤ Y.length) (hthetaFirstIndex :
        (↑(HierarchyFirstMissingPosition d.switched.coloring T d.theta) : ℕ) =
        (HierarchyFullTailPrefix C j).length) (hthetaOutsideGamma : d.theta ∉ D.biUnion
        (R.counterexample.good.gamma q)) (hgammaNeTheta : gamma ≠ d.theta) (hAtoZ :
        TreeSequenceInitialSegment A Z) (treeMissingSubset :
    ∀ {U W : TreeSequence G e0}, TreeSequenceInitialSegment U W → TreeMissingColors sigma U ⊆
        TreeMissingColors sigma W) (hgammaMissingZ : gamma ∈ TreeMissingColors sigma Z)
        (hbetaMissingZ : beta ∈ TreeMissingColors sigma Z) (hchangeElementary :
        ColoredVertexSetElementary G sigma (TreeSequenceVertexSet (HierarchyFullTailPrefix
        R.counterexample (HierarchyFullTailLength R.counterexample - (1 : ℕ))))) (hchangeMissing :
        gamma ∈ TreeMissingColors sigma (HierarchyFullTailPrefix R.counterexample
        (HierarchyFullTailLength R.counterexample - (1 : ℕ))) ∧ beta ∈ TreeMissingColors sigma
        (HierarchyFullTailPrefix R.counterexample (HierarchyFullTailLength R.counterexample - (1 :
        ℕ)))) (componentSelf :
    ∀ (rho : PartialEdgeColoring E k) (a b : Fin k) (v : V), Sum.inl v ∈ TwoColorComponent G rho a
        b (Sum.inl v)) (componentLeaf :
    ∀ (rho : PartialEdgeColoring E k) (a b : Fin k), a ≠ b → IsProperEdgeColoring G rho →
    ∀ (v : V), a ∈ MissingColors G rho v ∨ b ∈ MissingColors G rho v → ((TwoColorIncidenceGraph G
        rho a b).neighborSet (Sum.inl v)).Subsingleton) (separateComponents :
    ∀ (rho : PartialEdgeColoring E k) (a b : Fin k), a ≠ b → IsProperEdgeColoring G rho →
    ∀ (u v w : V), u ≠ v → u ≠ w → v ≠ w → a ∈ MissingColors G rho u → b ∈ MissingColors G rho v →
        a ∈ MissingColors G rho w ∨ b ∈ MissingColors G rho w → TwoColorComponent G rho a b
        (Sum.inl u) = TwoColorComponent G rho a b (Sum.inl v) → Disjoint (TwoColorComponent G rho
        a b (Sum.inl w)) (TwoColorComponent G rho a b (Sum.inl u))) (hgammaTerminalDistinct :
        T.vertex (HierarchyFirstMissingPosition sigma T gamma) ≠ T.vertex (Fin.last T.length))
        (hterminalDisjoint : Disjoint (TwoColorComponent G sigma gamma beta (Sum.inl (T.vertex
        (Fin.last T.length)))) (TwoColorComponent G sigma gamma beta (Sum.inl (T.vertex
        (HierarchyFirstMissingPosition sigma T gamma))))),
    let z : V ⊕ E := Sum.inl (T.vertex (Fin.last T.length));
    let mu2 : PartialEdgeColoring E k := TwoColorComponentSwap G sigma gamma beta z;
    ∀ (hmu2One : IsOneEdgeUncolored mu2 e0) (hgammaFirstMu2 : gamma ∈ MissingColors G mu2
        (T.vertex (HierarchyFirstMissingPosition sigma T gamma))) (hgammaTerminalMu2 : gamma ∈
        MissingColors G mu2 (T.vertex (Fin.last T.length))) (hfixedThroughY :
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < A.length + j → mu2 (T.edge t) = sigma
        (T.edge t)) (prefixMissing :
    ∀ (W : TreeSequence G e0) (z : V ⊕ E) (rho : PartialEdgeColoring E k) (a b : Fin k) (hne : a ≠
        b) (hp : IsProperEdgeColoring G rho) (helem : ColoredVertexSetElementary G rho
        (TreeSequenceVertexSet W)) (u v : V) (huB : u ∈ TreeSequenceVertexSet W) (hvB : v ∈
        TreeSequenceVertexSet W) (hu : a ∈ MissingColors G rho u) (hv : b ∈ MissingColors G rho v)
        (hdu : Sum.inl u ∉ TwoColorComponent G rho a b z) (hdv : Sum.inl v ∉ TwoColorComponent G
        rho a b z),
    ∀ w ∈ TreeSequenceVertexSet W, MissingColors G (TwoColorComponentSwap G rho a b z) w =
        MissingColors G rho w) (firstPreserved :
    ∀ (W : TreeSequence G e0) (hWT : TreeSequenceInitialSegment W T) (rho sigma :
        PartialEdgeColoring E k) (c : Fin k) (helem : ColoredVertexSetElementary G rho
        (TreeSequenceVertexSet W)) (hmiss :
    ∀ v ∈ TreeSequenceVertexSet W, MissingColors G sigma v = MissingColors G rho v) (hc : c ∈
        TreeMissingColors rho W), HierarchyFirstMissingPosition sigma T c =
        HierarchyFirstMissingPosition rho T c) (firstUnaffected :
    ∀ (z : V ⊕ E) (rho : PartialEdgeColoring E k) (a b c : Fin k) (hne : a ≠ b) (hp :
        IsProperEdgeColoring G rho) (hca : c ≠ a) (hcb : c ≠ b), HierarchyFirstMissingPosition
        (TwoColorComponentSwap G rho a b z) T c = HierarchyFirstMissingPosition rho T c)
        (hmissingMu2 :
    ∀ v ∈ TreeSequenceVertexSet Z, MissingColors G mu2 v = MissingColors G sigma v)
        (missingTransport :
    ∀ (old new : PartialEdgeColoring E k) (hm :
    ∀ v ∈ TreeSequenceVertexSet Z, MissingColors G new v = MissingColors G old v) (W :
        TreeSequence G e0) (hWZ : TreeSequenceInitialSegment W Z), TreeMissingColors new W =
        TreeMissingColors old W), False

private theorem helper_hthetaFirstIndex_397.{u_1, u_2} :
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
        (↑(HierarchyFirstMissingPosition sigma T d.theta) : ℕ) = Y.length := by
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

private theorem helper_routeToY_1012.{u_1, u_2} :
    helperRouteToY1012Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d j hj hpathLower R H q A ell
      X Y Z hAtoT commonPrefix hYlen hYtoT hXtoY hYtoZ hAtoY sameStarAll weakEdges hXYlen S nu hn
      hw hf hm
  as_aux_lemma =>
    have hj : 2 ≤ j := hpathLower
    clear * - G k e0 input T phi ett base C ctx S nu hn hw hf hm
      A X Y Z hAtoT hYtoT hXtoY hYtoZ hXYlen hAtoY hYlen hj j sameStarAll
      commonPrefix weakEdges
    clear_value A X Y Z
    let et := S.corresponding.replacementETT
    let K := S.counterexample.hierarchy
    let Tn := et.series.data.tree (Fin.last et.rounds).castSucc
    have hTnT : TreeSequenceInitialSegment Tn T := et.abovePenultimate
    have hTnA : Tn.length ≤ A.length := by
      by_cases hz : K.dividerCount = 0
      · have hi : (Fin.last K.dividerCount : Fin (K.dividerCount + 1)) = 0 := Fin.ext hz
        have hs := sameStarAll S
        change HierarchyStarredStage K (Fin.last K.dividerCount) = A at hs
        rw [hi] at hs
        change S.replacementBase.core = A at hs
        by_cases hp : et.series.data.kind (Fin.last et.rounds) =
            some TashkinovExtensionKind.PE
        · rw [← hs]; exact (Classical.choice (S.replacementBase.parallel hp).2.2).leftSegment.1
        · rw [← hs, S.replacementBase.nonparallel hp]
      · have hi : (Fin.last K.dividerCount : Fin (K.dividerCount + 1)) =
            (⟨K.dividerCount - 1, by omega⟩ : Fin K.dividerCount).succ :=
          Fin.ext (by simp only [Fin.val_last, Fin.val_succ]; omega)
        have hs := sameStarAll S
        change HierarchyStarredStage K (Fin.last K.dividerCount) = A at hs
        rw [hi] at hs
        have hmono : Monotone (fun i : Fin (K.dividerCount + 2) => (K.stage i).length) :=
          Fin.monotone_iff_le_succ.mpr (fun i => (K.nested i).1)
        rw [← hs]
        change Tn.length ≤ (K.stage _).length
        rw [show Tn = K.stage 0 from K.baseStage.symm]
        exact hmono (Fin.zero_le _)
    have hAYstrict : A.length < Y.length := by
      clear * - hj hYlen
      omega
    have fixedA : ∀ t : Fin A.length, nu (A.edge t) = S.coloring (A.edge t) := by
      have he := weakEdges S.coloring nu et S.replacementBase K hw
        S.minimumContext.oneEdgeUncolored hn
      change ∀ t : Fin (HierarchyStarredStage S.counterexample.hierarchy
        (Fin.last S.counterexample.hierarchy.dividerCount)).length,
          nu ((HierarchyStarredStage S.counterexample.hierarchy
            (Fin.last S.counterexample.hierarchy.dividerCount)).edge t) =
          S.coloring ((HierarchyStarredStage S.counterexample.hierarchy
            (Fin.last S.counterexample.hierarchy.dividerCount)).edge t) at he
      rw [sameStarAll S] at he
      exact he
    have fixedY : ∀ t : Fin Y.length, nu (Y.edge t) = S.coloring (Y.edge t) := by
      intro t
      let tT : Fin T.length := Fin.castLE hYtoT.1 t
      have he : T.edge tT = Y.edge t := hYtoT.2.2 t
      by_cases ht : t.val < A.length
      · let tA : Fin A.length := ⟨t.val, ht⟩
        have hcast : Fin.castLE hAtoT.1 tA = tT := Fin.ext rfl
        rw [← he, ← hcast, hAtoT.2.2 tA]
        exact fixedA tA
      · rw [← he]
        exact hf tT (Nat.le_of_not_gt ht) t.isLt
    have transport (W : TreeSequence G e0)
        (hr : TashkinovAugmentationSequence S.coloring W Y) :
        TashkinovAugmentationSequence nu W Y :=
      TashkinovAugmentationSequenceColoringTransport S.coloring nu W X Y hr
        hXtoY hXYlen (fun t _ => fixedY t)
        (fun v hv => hm v (TreeSequenceInitialSegmentVertexSetSubset hYtoZ
          (TreeSequenceInitialSegmentVertexSetSubset hXtoY hv)))
    rcases P2813_T1_TerminalRoute G k e0 S.corresponding.replacementInput T
      S.coloring et with ⟨hp, hr⟩ | ⟨hk, f, seed, he, ha, _, _, hr⟩
    · have hTY : TreeSequenceInitialSegment Tn Y :=
        commonPrefix hTnT hYtoT (hTnA.trans hAtoY.1)
      exact Or.inl ⟨hp, transport Tn
        (TashkinovAugmentationSequenceRestrict S.coloring Tn Y T hr hTY hYtoT)⟩
    · have hseedT : TreeSequenceInitialSegment seed T :=
        TashkinovAugmentationSequenceInitialSegment S.coloring seed T hr
      have hseedY : TreeSequenceInitialSegment seed Y :=
        commonPrefix hseedT hYtoT (by
          have hl := ha.1
          change seed.length = Tn.length + 1 at hl
          clear * - hl hTnA hAYstrict
          omega)
      exact Or.inr ⟨hk, f, seed, he, ha, transport seed
        (TashkinovAugmentationSequenceRestrict S.coloring seed Y T hr hseedY hYtoT)⟩

private theorem helper_hthetaMissingY_553.{u_1, u_2} :
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
        (Y.vertex (Fin.last Y.length)) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d j hj R sigma Y
  have ht := d.thetaMissingAtJ
  change d.theta ∈ MissingColors G d.switched.coloring
    ((HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy)).vertex
      (Fin.last (HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy)).length)) at ht
  rw [hj] at ht
  exact ht

private theorem helper_hgammaNeBeta_569.{u_1, u_2} :
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
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q; beta ∈ D →
    ∀ gamma ∈ TreeMissingColors sigma A, gamma ≠ beta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d R sigma H q A D hbetaStored
      gamma hgammaA heq
  have hnot : beta ∉ TreeMissingColors sigma A := by
    intro hmiss
    exact (Finset.mem_sdiff.mp hbetaStored).2 hmiss
  exact hnot (heq ▸ hgammaA)

private theorem helper_sameStar_577.{u_1, u_2} :
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
        (Fin.last C.hierarchy.dividerCount) = A := by
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

private theorem helper_hcutJstrict_610.{u_1, u_2} :
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
        T.length := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d j hj R H q A ell sameStar
      hAtoT hjUpper
  have hj : j < T.length - A.length := by
    simpa only [ell, HierarchyFullTailLength, sameStar] using hjUpper
  have hAT := hAtoT.1
  clear * - hj hAT
  clear_value A
  omega

private theorem helper_prefixToTree_623.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
  (T : TreeSequence G e0) (m : ℕ) (hm : (1 : ℕ) ≤ m) (hmT : m ≤ T.length),
  TreeSequenceInitialSegment (TreeSequencePrefix T m hm hmT) T := by
  classical
  intro V E G e0 T m hm hmT
  as_aux_lemma =>
    refine ⟨hmT, ?_, ?_⟩
    · intro i
      simp [TreeSequencePrefix]
    · intro i
      simp [TreeSequencePrefix]

private theorem helper_commonPrefix_632.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E) (T : TreeSequence G e0)
        {U W : TreeSequence G e0}, TreeSequenceInitialSegment U T → TreeSequenceInitialSegment W T
        → U.length ≤ W.length → TreeSequenceInitialSegment U W := by
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

private theorem helper_hElemZ_717.{u_1, u_2} :
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
        ℕ)) = Z → ColoredVertexSetElementary G sigma (TreeSequenceVertexSet Z) := by
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

private theorem helper_firstWitness_734.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (T : TreeSequence G e0)
  (rho : PartialEdgeColoring E k) (W : TreeSequence G e0),
  TreeSequenceInitialSegment W T →
  ∀ c ∈ TreeMissingColors rho W,
  c ∈ MissingColors G rho (T.vertex (HierarchyFirstMissingPosition rho T c)) ∧
    (↑(HierarchyFirstMissingPosition rho T c) : ℕ) ≤ W.length := by
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

private theorem helper_vertexMemT_768.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E) (T W : TreeSequence G
        e0), TreeSequenceInitialSegment W T →
    ∀ (i : Fin (T.length + (1 : ℕ))), (↑i : ℕ) ≤ W.length → T.vertex i ∈ TreeSequenceVertexSet W
  := by
  classical
  intro V E G e0 T W hWT i hi
  as_aux_lemma =>
    let jW : Fin (W.length + 1) := ⟨i.val, Nat.lt_succ_of_le hi⟩
    have hcast : Fin.castLE (Nat.succ_le_succ hWT.1) jW = i := Fin.ext rfl
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨jW, ?_⟩
    rw [← hWT.2.1 jW, hcast]

private theorem helper_hthetaY_789.{u_1, u_2} :
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
        d.theta ∈ TreeMissingColors sigma Y := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d j R sigma Y hthetaMissingY
      vertexMemSelf treeMissingIntro
  as_aux_lemma =>
    clear_value Y
    exact treeMissingIntro sigma Y (Y.vertex (Fin.last Y.length)) d.theta
      (vertexMemSelf Y (Fin.last Y.length)) hthetaMissingY

private theorem helper_hbetaAfterA_813.{u_1, u_2} :
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
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ));
        TreeSequenceInitialSegment A T → beta ∈ MissingColors G sigma (T.vertex
        (HierarchyFirstMissingPosition sigma T beta)) ∧ (↑(HierarchyFirstMissingPosition sigma T
        beta) : ℕ) ≤ B.length → (
    ∀ (W : TreeSequence G e0), TreeSequenceInitialSegment W T →
    ∀ (i : Fin (T.length + (1 : ℕ))), (↑i : ℕ) ≤ W.length → T.vertex i ∈ TreeSequenceVertexSet W)
        → (
    ∀ (rho : PartialEdgeColoring E k) (W : TreeSequence G e0) (v : V) (c : Fin k), v ∈
        TreeSequenceVertexSet W → c ∈ MissingColors G rho v → c ∈ TreeMissingColors rho W) → beta
        ∉ TreeMissingColors sigma A → A.length < (↑(HierarchyFirstMissingPosition sigma T beta) :
        ℕ) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d j R sigma H q A B hAtoT
      hbetaFirst vertexMemT treeMissingIntro hbetaNotA
  by_contra hnot
  have hpos : (HierarchyFirstMissingPosition sigma T beta).val ≤ A.length :=
    Nat.le_of_not_gt hnot
  have hvA := vertexMemT A hAtoT (HierarchyFirstMissingPosition sigma T beta) hpos
  exact hbetaNotA (treeMissingIntro sigma A
    (T.vertex (HierarchyFirstMissingPosition sigma T beta)) beta hvA hbetaFirst.1)

private theorem helper_hgammaUnusedBeforeBeta_834.{u_1, u_2} :
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
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ)); Disjoint
        (R.counterexample.good.gamma q beta ∪ ({ beta } : Finset (Fin k))) ({c : Fin k |
    ∃ (r : Fin T.length), A.length ≤ (↑r : ℕ) ∧ (↑r : ℕ) < A.length + j ∧ sigma (T.edge r) = some
        c} : Finset (Fin k)) →
    ∀ gamma ∈ R.counterexample.good.gamma q beta, (↑(HierarchyFirstMissingPosition sigma T beta) :
        ℕ) ≤ B.length → B.length ≤ A.length + j → gamma ∉ ({c : Fin k |
    ∃ (t : Fin T.length), A.length ≤ (↑t : ℕ) ∧ (↑t : ℕ) < (↑(HierarchyFirstMissingPosition sigma
        T beta) : ℕ) ∧ sigma (T.edge t) = some c} : Finset (Fin k)) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d j R sigma H q A B hbetaTail
      gamma hgammaBeta hbetaFirstLe hBcutoff hc
  obtain ⟨_, t, hlo, hhi, hcolor⟩ := Finset.mem_filter.mp hc
  have htailMem : gamma ∈
      (Finset.univ : Finset (Fin k)).filter fun c =>
        ∃ r : Fin T.length, A.length ≤ r.val ∧ r.val < A.length + j ∧
          sigma (T.edge r) = some c := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, t, hlo, ?_, hcolor⟩
    exact lt_of_lt_of_le hhi (le_trans hbetaFirstLe hBcutoff)
  apply (Finset.disjoint_left.mp hbetaTail)
    (Finset.mem_union.mpr (Or.inl hgammaBeta))
  exact htailMem

private theorem helper_treeMissingSubset_868.{u_1, u_2} :
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
    ∀ {U W : TreeSequence G e0}, TreeSequenceInitialSegment U W → TreeMissingColors sigma U ⊆
        TreeMissingColors sigma W := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d R sigma U W hUW
  as_aux_lemma =>
    intro c hc
    obtain ⟨v, hv, hmiss⟩ := Finset.mem_biUnion.mp hc
    exact Finset.mem_biUnion.mpr ⟨v,
      TreeSequenceInitialSegmentVertexSetSubset hUW hv, hmiss⟩

private theorem helper_firstChange_904.{u_1, u_2} :
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
    ∀ (gamma : Fin k), gamma ≠ beta → HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount) = A → beta ∉ TreeMissingColors sigma A → ( gamma ∉
        TreeMissingColors sigma A ∨ beta ∉ TreeMissingColors sigma A → TreeVertexOrder T (T.vertex
        (HierarchyFirstMissingPosition sigma T gamma)) (T.vertex (HierarchyFirstMissingPosition
        sigma T beta)) ∧ gamma ∉ ({c : Fin k |
    ∃ (t : Fin T.length), A.length ≤ (↑t : ℕ) ∧ (↑t : ℕ) < (↑(HierarchyFirstMissingPosition sigma
        T beta) : ℕ) ∧ sigma (T.edge t) = some c} : Finset (Fin k))) → ColoredVertexSetElementary
        G sigma (TreeSequenceVertexSet (HierarchyFullTailPrefix R.counterexample
        (HierarchyFullTailLength R.counterexample - (1 : ℕ)))) → gamma ∈ TreeMissingColors sigma
        (HierarchyFullTailPrefix R.counterexample (HierarchyFullTailLength R.counterexample - (1 :
        ℕ))) ∧ beta ∈ TreeMissingColors sigma (HierarchyFullTailPrefix R.counterexample
        (HierarchyFullTailLength R.counterexample - (1 : ℕ))) →
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
        ({ gamma } : Finset (Fin k)) → sameComponent ∧ TreeInterchangeable G A sigma gamma beta)
  := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d R sigma H q A gamma
      hgammaNeBeta sameStar hbetaNotA horderedUnusedGammaBeta hchangeElementary hchangeMissing
  as_aux_lemma =>
    exact ChangeLemma G k e0 R.corresponding.replacementInput T sigma
      R.corresponding.replacementETT R.replacementBase R.counterexample
      R.minimumContext.proper R.minimumContext.oneEdgeUncolored
      R.minimumContext.lowerRung R.minimumContext.fewerDividers
      R.minimumContext.lexicographicMinimality hchangeElementary
      R.minimumContext.largeMissingSet gamma beta hgammaNeBeta hchangeMissing
      (by
        change (gamma ∉ TreeMissingColors sigma A ∨ beta ∉ TreeMissingColors sigma A) →
          TreeVertexOrder T
              (T.vertex (HierarchyFirstMissingPosition sigma T gamma))
              (T.vertex (HierarchyFirstMissingPosition sigma T beta)) ∧
            gamma ∉ (Finset.univ.filter fun c =>
              ∃ t : Fin T.length, A.length ≤ t.val ∧
                t.val < (HierarchyFirstMissingPosition sigma T beta).val ∧
                  sigma (T.edge t) = some c)
        exact horderedUnusedGammaBeta)

private theorem helper_hApositive_927.{u_1, u_2} :
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
    ⟩ : Fin (H.dividerCount + (2 : ℕ))) := by
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

private theorem helper_sameGammaBeta_943.{u_1, u_2} :
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
        (Sum.inl (T.vertex (HierarchyFirstMissingPosition sigma T beta))) := by
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

private theorem helper_hBlt_1027.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
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
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ)); A.length + j < T.length
        → (
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
    )) → B.length < T.length := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d j R H q A B hcutJstrict
      fullPrefixEq
  change (HierarchyFullTailPrefix C (j - 2)).length < T.length
  rw [fullPrefixEq]
  simp only [TreeSequencePrefix]
  exact lt_of_le_of_lt (Nat.min_le_left _ _)
    (lt_of_le_of_lt (Nat.add_le_add_left (Nat.sub_le j 2) _) hcutJstrict)

private theorem helper_hgammaTerminalDistinct_1040.{u_1, u_2} :
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
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    ∀ (gamma : Fin k), A.length + j < T.length → (↑(HierarchyFirstMissingPosition sigma T gamma) :
        ℕ) ≤ A.length → T.vertex (HierarchyFirstMissingPosition sigma T gamma) ≠ T.vertex
        (Fin.last T.length) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d j R sigma H q A gamma
      hcutJstrict hgammaFirstLe he
  have hi := T.vertex_injective he
  have hv := congrArg Fin.val hi
  simp only [Fin.val_last] at hv
  exact (Nat.ne_of_lt (hgammaFirstLe.trans_lt
    (lt_of_le_of_lt (Nat.le_add_right _ _) hcutJstrict))) hv

private theorem helper_hbetaTerminalDistinct_1049.{u_1, u_2} :
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
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ));
        (↑(HierarchyFirstMissingPosition sigma T beta) : ℕ) ≤ B.length → B.length < T.length →
        T.vertex (HierarchyFirstMissingPosition sigma T beta) ≠ T.vertex (Fin.last T.length) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d j R sigma B hbetaFirstLe
      hBlt he
  have hi := T.vertex_injective he
  have hv := congrArg Fin.val hi
  simp only [Fin.val_last] at hv
  exact (Nat.ne_of_lt (hbetaFirstLe.trans_lt hBlt)) hv

private theorem helper_hmu2One_1069.{u_1, u_2} :
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
        IsOneEdgeUncolored mu2 e0 := by
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

private theorem helper_hfirstBetaOutside_1094.{u_1, u_2} :
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
        (HierarchyFirstMissingPosition sigma T beta)) ∉ TwoColorComponent G sigma gamma beta z := by
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

private theorem helper_hfixedThroughY_1119.{u_1, u_2} :
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
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q; Disjoint (R.counterexample.good.gamma
        q beta ∪ ({ beta } : Finset (Fin k))) ({c : Fin k |
    ∃ (r : Fin T.length), A.length ≤ (↑r : ℕ) ∧ (↑r : ℕ) < A.length + j ∧ sigma (T.edge r) = some
        c} : Finset (Fin k)) →
    ∀ gamma ∈ R.counterexample.good.gamma q beta,
    let z : V ⊕ E := Sum.inl (T.vertex (Fin.last T.length));
    let mu2 : PartialEdgeColoring E k := TwoColorComponentSwap G sigma gamma beta z;
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < A.length + j → mu2 (T.edge t) = sigma
        (T.edge t) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d j R sigma H q A hbetaTail
      gamma hgammaBeta z mu2
  as_aux_lemma =>
    intro t hlo hhi
    have hgammaUnused : sigma (T.edge t) ≠ some gamma := by
      intro hc
      have hmem : gamma ∈ (Finset.univ : Finset (Fin k)).filter fun c =>
          ∃ r : Fin T.length, A.length ≤ r.val ∧ r.val < A.length + j ∧
            sigma (T.edge r) = some c := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, t, hlo, hhi, hc⟩
      exact (Finset.disjoint_left.mp hbetaTail)
        (Finset.mem_union.mpr (Or.inl hgammaBeta)) hmem
    have hbetaUnused : sigma (T.edge t) ≠ some beta := by
      intro hc
      have hmem : beta ∈ (Finset.univ : Finset (Fin k)).filter fun c =>
          ∃ r : Fin T.length, A.length ≤ r.val ∧ r.val < A.length + j ∧
            sigma (T.edge r) = some c := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, t, hlo, hhi, hc⟩
      exact (Finset.disjoint_left.mp hbetaTail)
        (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl))) hmem
    by_cases hcomponent : Sum.inr (T.edge t) ∈ TwoColorComponent G sigma gamma beta z
    · simp [mu2, TwoColorComponentSwap, hcomponent, hgammaUnused, hbetaUnused]
    · simp [mu2, TwoColorComponentSwap, hcomponent]

private theorem helper_firstPreserved_1154.{u_1, u_2} :
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
        HierarchyFirstMissingPosition rho T c := by
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

private theorem helper_firstUnaffected_1179.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (T : TreeSequence G e0) (z : V ⊕ E) (rho : PartialEdgeColoring E k) (a b c : Fin
        k), a ≠ b → IsProperEdgeColoring G rho → c ≠ a → c ≠ b → HierarchyFirstMissingPosition
        (TwoColorComponentSwap G rho a b z) T c = HierarchyFirstMissingPosition rho T c := by
  classical
  intro V E _ _ G k e0 T z rho a b c hne hp hca hcb
  let _ := Fintype.ofFinite V
  have hb := TwoColorComponentSwapMissingBehavior G rho a b hne hp z
  have he : (Finset.univ.filter fun i : Fin (T.length + 1) =>
      c ∈ MissingColors G (TwoColorComponentSwap G rho a b z) (T.vertex i)) =
      (Finset.univ.filter fun i : Fin (T.length + 1) =>
        c ∈ MissingColors G rho (T.vertex i)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hb.2.2.2 _ c hca hcb
  unfold HierarchyFirstMissingPosition
  rw [he]

private theorem helper_hmissingMu2_1194.{u_1, u_2} :
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
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength C;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ));
    let Z : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
    ∀ (gamma : Fin k), gamma ≠ beta → TreeSequenceInitialSegment Z T → ColoredVertexSetElementary
        G sigma (TreeSequenceVertexSet Z) → gamma ∈ MissingColors G sigma (T.vertex
        (HierarchyFirstMissingPosition sigma T gamma)) ∧ (↑(HierarchyFirstMissingPosition sigma T
        gamma) : ℕ) ≤ A.length → beta ∈ MissingColors G sigma (T.vertex
        (HierarchyFirstMissingPosition sigma T beta)) ∧ (↑(HierarchyFirstMissingPosition sigma T
        beta) : ℕ) ≤ B.length → (↑(HierarchyFirstMissingPosition sigma T gamma) : ℕ) ≤ A.length →
        (↑(HierarchyFirstMissingPosition sigma T beta) : ℕ) ≤ B.length → (
    ∀ (W : TreeSequence G e0), TreeSequenceInitialSegment W T →
    ∀ (i : Fin (T.length + (1 : ℕ))), (↑i : ℕ) ≤ W.length → T.vertex i ∈ TreeSequenceVertexSet W)
        → TreeSequenceInitialSegment A Z → TreeSequenceInitialSegment B Z →
    let z : V ⊕ E := Sum.inl (T.vertex (Fin.last T.length));
    let mu2 : PartialEdgeColoring E k := TwoColorComponentSwap G sigma gamma beta z; Sum.inl
        (T.vertex (HierarchyFirstMissingPosition sigma T gamma)) ∉ TwoColorComponent G sigma gamma
        beta z → Sum.inl (T.vertex (HierarchyFirstMissingPosition sigma T beta)) ∉
        TwoColorComponent G sigma gamma beta z → (
    ∀ (W : TreeSequence G e0) (z : V ⊕ E) (rho : PartialEdgeColoring E k) (a b : Fin k), a ≠ b →
        IsProperEdgeColoring G rho → ColoredVertexSetElementary G rho (TreeSequenceVertexSet W) →
    ∀ (u v : V), u ∈ TreeSequenceVertexSet W → v ∈ TreeSequenceVertexSet W → a ∈ MissingColors G
        rho u → b ∈ MissingColors G rho v → Sum.inl u ∉ TwoColorComponent G rho a b z → Sum.inl v
        ∉ TwoColorComponent G rho a b z →
    ∀ w ∈ TreeSequenceVertexSet W, MissingColors G (TwoColorComponentSwap G rho a b z) w =
        MissingColors G rho w) →
    ∀ v ∈ TreeSequenceVertexSet Z, MissingColors G mu2 v = MissingColors G sigma v := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d j R sigma H q A ell B Z
      gamma hgammaNeBeta hZtoT hElemZ hgammaFirst hbetaFirst hgammaFirstLe hbetaFirstLe
      vertexMemT hAtoZ hBtoZ z mu2 hfirstGammaOutside hfirstBetaOutside prefixMissing
  have hgZ : T.vertex (HierarchyFirstMissingPosition sigma T gamma) ∈ TreeSequenceVertexSet Z :=
    vertexMemT Z hZtoT (HierarchyFirstMissingPosition sigma T gamma)
      (hgammaFirstLe.trans hAtoZ.1)
  have hbZ : T.vertex (HierarchyFirstMissingPosition sigma T beta) ∈ TreeSequenceVertexSet Z :=
    vertexMemT Z hZtoT (HierarchyFirstMissingPosition sigma T beta)
      (hbetaFirstLe.trans hBtoZ.1)
  intro v hv
  exact prefixMissing Z z sigma gamma beta hgammaNeBeta R.minimumContext.proper
    hElemZ (T.vertex (HierarchyFirstMissingPosition sigma T gamma))
    (T.vertex (HierarchyFirstMissingPosition sigma T beta))
    hgZ hbZ hgammaFirst.1 hbetaFirst.1 hfirstGammaOutside hfirstBetaOutside v hv

private theorem helper_missingTransport_1207.{u_1, u_2} :
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
        TreeMissingColors old W := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ell Z old new hm W hWZ
  as_aux_lemma =>
    clear_value Z
    clear * - old new hm W hWZ Z
    unfold TreeMissingColors
    exact Finset.biUnion_congr rfl (fun v hv =>
      hm v (TreeSequenceInitialSegmentVertexSetSubset hWZ hv))

private theorem helper_hstoredMu2_1218.{u_1, u_2} :
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
  := by
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

private theorem helper_hgammaCutoff_1230.{u_1, u_2} :
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
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ));
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ));
    let Y : TreeSequence G e0 := HierarchyFullTailPrefix C j;
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q; beta ∈ D →
    ∀ gamma ∈ R.counterexample.good.gamma q beta, TreeSequenceInitialSegment B X →
        TreeSequenceInitialSegment X Y → (↑(HierarchyFirstMissingPosition sigma T beta) : ℕ) ≤
        B.length →
    ∀ eta ∈ D, gamma ∈ R.counterexample.good.gamma q eta ∨ beta ∈ R.counterexample.good.gamma q
        eta → (↑(HierarchyFirstMissingPosition sigma T eta) : ℕ) ≤ Y.length := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d j R sigma H q X B Y D
      hbetaStored gamma hgammaBeta hBtoX hXtoY hbetaFirstLe eta heta hmem
  have he : eta = beta := by
    by_contra hne
    rcases hmem with hg | hb
    · exact Finset.disjoint_left.mp
        (R.counterexample.good.disjointPairs q eta beta heta hbetaStored hne)
        hg hgammaBeta
    · exact d.betaOutsideGamma (Finset.mem_biUnion.mpr ⟨eta, heta, hb⟩)
  subst eta
  exact hbetaFirstLe.trans (hBtoX.1.trans hXtoY.1)

private theorem helper_originalStar_1244.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (S :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), HierarchyStarredStage
        C.hierarchy (Fin.last C.hierarchy.dividerCount) = HierarchyStarredStage
        S.counterexample.hierarchy (Fin.last S.counterexample.hierarchy.dividerCount) := by
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

private theorem helper_lastData_1275.{u_1, u_2} :
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
        S.counterexample.good.gamma (Fin.last S.counterexample.hierarchy.dividerCount) eta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx S
  as_aux_lemma =>
    obtain ⟨hc, hd⟩ := S.sameGood.2
    have hi : Fin.cast (congrArg (fun n => n + 1) hc)
        (Fin.last C.hierarchy.dividerCount) =
          Fin.last S.counterexample.hierarchy.dividerCount := Fin.ext hc
    simpa only [hi] using hd (Fin.last C.hierarchy.dividerCount)

private theorem helper_sameLast_1290.{u_1, u_2} :
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
        S.counterexample.hierarchy.dividerCount) eta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d R H q D lastData S
  refine ⟨(lastData R).1.symm.trans (lastData S).1, ?_⟩
  intro eta heta
  have hc : eta ∈ HierarchyStoredColorsAt C.hierarchy
      (Fin.last C.hierarchy.dividerCount) := (lastData R).1.symm ▸ heta
  exact ((lastData R).2 eta hc).symm.trans ((lastData S).2 eta hc)

private theorem helper_weakEdges_1301.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (T : TreeSequence G e0)
        {input' : PartialEdgeColoring E k} (old new : PartialEdgeColoring E k) (et :
        ExtendedTashkinovTree G k e0 input' T old) (bs : HierarchyBase et old) (K :
        TashkinovHierarchy et bs), HierarchyWeaklyStable K (Fin.last K.dividerCount) new →
        IsOneEdgeUncolored old e0 → IsOneEdgeUncolored new e0 →
    ∀ (t : Fin (HierarchyStarredStage K (Fin.last K.dividerCount)).length), new
        ((HierarchyStarredStage K (Fin.last K.dividerCount)).edge t) = old ((HierarchyStarredStage
        K (Fin.last K.dividerCount)).edge t) := by
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

private theorem helper_hXYlen_1327.{u_1, u_2} :
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
    )) → Y.length = X.length + (1 : ℕ) := by
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

private theorem helper_caseGamma_1360.{u_1, u_2} :
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
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q; beta ∈ D →
    ∀ gamma ∈ R.counterexample.good.gamma q beta, (
    ∀ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), D =
        HierarchyStoredColorsAt S.counterexample.hierarchy (Fin.last
        S.counterexample.hierarchy.dividerCount) ∧
    ∀ eta ∈ D, R.counterexample.good.gamma q eta = S.counterexample.good.gamma (Fin.last
        S.counterexample.hierarchy.dividerCount) eta) →
    ∀ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), (0 : ℕ) <
        S.counterexample.hierarchy.dividerCount ∧ gamma ∈ TreeMissingColors S.coloring
        (S.counterexample.hierarchy.stage (⟨S.counterexample.hierarchy.dividerCount,
    by
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    ⟩ : Fin (S.counterexample.hierarchy.dividerCount + (2 : ℕ)))) ∨
        S.counterexample.hierarchy.dividerCount = (0 : ℕ) ∧ gamma ∈ TreeMissingColors S.coloring
        (S.corresponding.replacementETT.series.data.tree (Fin.last
        S.corresponding.replacementETT.rounds).castSucc) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d R H q D hbetaStored gamma
      hgammaBeta sameLast S
  as_aux_lemma =>
    have hs : beta ∈ HierarchyStoredColorsAt S.counterexample.hierarchy
        (Fin.last S.counterexample.hierarchy.dividerCount) := (sameLast S).1 ▸ hbetaStored
    have hg : gamma ∈ S.counterexample.good.gamma
        (Fin.last S.counterexample.hierarchy.dividerCount) beta :=
      (sameLast S).2 beta hbetaStored ▸ hgammaBeta
    have hm := (Finset.mem_sdiff.mp (S.counterexample.good.avoidance _ beta hs hg)).1
    clear * - S gamma hm
    let K := S.counterexample.hierarchy
    cases hi : (Fin.last K.dividerCount : Fin (K.dividerCount + 1)) using Fin.cases with
    | zero =>
      have hz : K.dividerCount = 0 := congrArg Fin.val hi
      refine Or.inr ⟨hz, ?_⟩
      change gamma ∈ HierarchyStageMissingColors K (Fin.last K.dividerCount) at hm
      rw [hi] at hm
      exact hm
    | succ i =>
      have hv : K.dividerCount = i.val + 1 := congrArg Fin.val hi
      have hc : i.succ.castSucc =
          (⟨K.dividerCount, Nat.lt_add_of_pos_right (by decide)⟩ : Fin (K.dividerCount + 2)) :=
        Fin.ext hv.symm
      refine Or.inl ⟨Nat.lt_of_lt_of_eq (Nat.succ_pos i.val) hv.symm, ?_⟩
      change gamma ∈ HierarchyStageMissingColors K (Fin.last K.dividerCount) at hm
      rw [hi] at hm
      change gamma ∈ TreeMissingColors S.coloring (K.stage i.succ.castSucc) at hm
      rw [hc] at hm
      exact hm

private theorem helper_hweak1_1415.{u_1, u_2} :
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
        HierarchyWeaklyStable H q mu2 := by
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

private theorem helper_thetaRawIfUsed_1463.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k)
        (d : HierarchySituationThreeDisjointData G k e0 input T phi ett base C ctx P alpha beta)
        (j : ℕ), (2 : ℕ) ≤ j → j < HierarchyFullTailLength C →
    let R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx := d.switched;
    let sigma : PartialEdgeColoring E k := R.coloring;
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let _ : ℕ := HierarchyFullTailLength C;
    let Y : TreeSequence G e0 := HierarchyFullTailPrefix C j; d.theta ∈ MissingColors G sigma
        (Y.vertex (Fin.last Y.length)) → HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount) = A → ColoredVertexSetElementary G sigma (TreeSequenceVertexSet
        (HierarchyFullTailPrefix R.counterexample (HierarchyFullTailLength R.counterexample - (1 :
        ℕ)))) → (
    ∀ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (m : ℕ),
        HierarchyFullTailPrefix S.counterexample m = HierarchyFullTailPrefix C m) →
    ∀ (t : Fin Y.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < A.length + j → sigma (Y.edge t) = some
        d.theta → d.theta ∈ TashkinovStoredColors R.corresponding.replacementETT.series.data
        (Fin.last R.corresponding.replacementETT.rounds) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d j hpathLower hpathUpper R
      sigma H q A ell Y hthetaMissingY sameStar hchangeElementary sameFullPrefix
  have hpref : HierarchyFullTailPrefix R.counterexample j = Y := sameFullPrefix R j
  rw [← hpref]
  intro t hlo hhi hc
  obtain ⟨_, _, _, f, _, _, _, _, _, hraw⟩ :=
    HierarchyTailMissingColorExclusion G k e0 R.corresponding.replacementInput T sigma
      R.corresponding.replacementETT R.replacementBase H hchangeElementary j
      (le_trans (by decide) hpathLower)
      (by change j < T.length - A.length
          simpa only [ell, HierarchyFullTailLength, sameStar] using hpathUpper)
      d.theta (by
        change d.theta ∈ MissingColors G sigma
          ((HierarchyFullTailPrefix R.counterexample j).vertex
            (Fin.last (HierarchyFullTailPrefix R.counterexample j).length))
        rw [hpref]
        exact hthetaMissingY) t hlo hhi hc
  exact hraw

private theorem helper_hthetaUnused_1483.{u_1, u_2} :
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
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let Y : TreeSequence G e0 := HierarchyFullTailPrefix C j; Y.length = A.length + j →
        TreeSequenceInitialSegment Y T → d.theta ∉ TashkinovStoredColors
        R.corresponding.replacementETT.series.data (Fin.last
        R.corresponding.replacementETT.rounds) → (
    ∀ (t : Fin Y.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < A.length + j → sigma (Y.edge t) = some
        d.theta → d.theta ∈ TashkinovStoredColors R.corresponding.replacementETT.series.data
        (Fin.last R.corresponding.replacementETT.rounds)) →
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < Y.length → sigma (T.edge t) ≠ some
        d.theta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d j R sigma H q A Y hYlen
      hYtoT hthetaNotRaw thetaRawIfUsed t hlo hhi hc
  let tY : Fin Y.length := ⟨t.val, hhi⟩
  have hi : Fin.castLE hYtoT.1 tY = t := Fin.ext rfl
  have he : sigma (Y.edge tY) = some d.theta := by
    rw [← hYtoT.2.2 tY, hi]
    exact hc
  exact hthetaNotRaw (thetaRawIfUsed tY hlo (hYlen ▸ hhi) he)

private theorem helper_changeRho_1547.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k)
        (d : HierarchySituationThreeDisjointData G k e0 input T phi ett base C ctx P alpha beta)
        (j : ℕ),
    let R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx := d.switched;
    let sigma : PartialEdgeColoring E k := R.coloring;
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength C;
    let Y : TreeSequence G e0 := HierarchyFullTailPrefix C j;
    let Z : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
    ∀ (gamma : Fin k), (↑(HierarchyFirstMissingPosition d.switched.coloring T d.theta) : ℕ) =
        (HierarchyFullTailPrefix C j).length → gamma ≠ d.theta → (
    ∀ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage S.counterexample.hierarchy (Fin.last
        S.counterexample.hierarchy.dividerCount) = A) → (
    ∀ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyFullTailPrefix S.counterexample (HierarchyFullTailLength S.counterexample - (1 :
        ℕ)) = Z) →
    ∀ (R1 : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let rho : PartialEdgeColoring E k := R1.coloring; ColoredVertexSetElementary G rho
        (TreeSequenceVertexSet Z) → HierarchyFirstMissingPosition rho T gamma =
        HierarchyFirstMissingPosition sigma T gamma → HierarchyFirstMissingPosition rho T d.theta
        = HierarchyFirstMissingPosition sigma T d.theta → (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < Y.length → rho (T.edge t) ≠ some gamma)
        → (↑(HierarchyFirstMissingPosition sigma T gamma) : ℕ) < (↑(HierarchyFirstMissingPosition
        sigma T d.theta) : ℕ) → gamma ∈ TreeMissingColors rho Z ∧ d.theta ∈ TreeMissingColors rho
        Z →
    let H : TashkinovHierarchy R1.corresponding.replacementETT R1.replacementBase :=
        R1.counterexample.hierarchy;
    have q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    have n : Fin (R1.corresponding.replacementETT.rounds + (1 : ℕ)) := Fin.last
        R1.corresponding.replacementETT.rounds;
    have A : TreeSequence G e0 := HierarchyStarredStage H q;
    have Tnq : TreeSequence G e0 := H.stage (⟨H.dividerCount,
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)));
    have Tn : TreeSequence G e0 := R1.corresponding.replacementETT.series.data.tree n.castSucc;
    have Dn : Finset (Fin k) := TashkinovStoredColors R1.corresponding.replacementETT.series.data
        n;
    have Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q;
    have va : V := T.vertex (HierarchyFirstMissingPosition rho T gamma);
    have vb : V := T.vertex (HierarchyFirstMissingPosition rho T d.theta);
    have sameComponent : Prop := TwoColorComponent G rho gamma d.theta (Sum.inl va) =
        TwoColorComponent G rho gamma d.theta (Sum.inl vb); ( (0 : ℕ) < H.dividerCount ∧ (gamma ∈
        TreeMissingColors rho Tnq ∨ Disjoint (insert gamma ({ d.theta } : Finset (Fin k)) : Finset
        (Fin k)) Dnq) → sameComponent) ∧ ( H.dividerCount = (0 : ℕ) ∧ (gamma ∈ TreeMissingColors
        rho Tn ∨ Disjoint (insert gamma ({ d.theta } : Finset (Fin k)) : Finset (Fin k)) Dn) →
        sameComponent) ∧ ( gamma ∈ TreeMissingColors rho A ∧ TreeColorSetClosed G rho A ({ gamma }
        : Finset (Fin k)) → sameComponent ∧ TreeInterchangeable G A rho gamma d.theta) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d j R sigma H q A ell Y Z
      gamma hthetaFirstIndex hgammaNeTheta sameStarAll samePenultimate R1 rho hElemRho
      hfirstGammaRho hfirstThetaRho hgammaUnusedRho hgammaBeforeTheta hpairMissingRho
  as_aux_lemma =>
    exact ChangeLemma G k e0 R1.corresponding.replacementInput T rho
      R1.corresponding.replacementETT R1.replacementBase R1.counterexample
      R1.minimumContext.proper R1.minimumContext.oneEdgeUncolored R1.minimumContext.lowerRung
      R1.minimumContext.fewerDividers R1.minimumContext.lexicographicMinimality
      (by change ColoredVertexSetElementary G rho
            (TreeSequenceVertexSet (HierarchyFullTailPrefix R1.counterexample
              (HierarchyFullTailLength R1.counterexample - 1)))
          rw [samePenultimate R1]; exact hElemRho)
      R1.minimumContext.largeMissingSet gamma d.theta hgammaNeTheta
      (by change gamma ∈ TreeMissingColors rho
            (HierarchyFullTailPrefix R1.counterexample (HierarchyFullTailLength R1.counterexample
                - 1)) ∧
            d.theta ∈ TreeMissingColors rho
              (HierarchyFullTailPrefix R1.counterexample (HierarchyFullTailLength
                  R1.counterexample - 1))
          rw [samePenultimate R1]; exact hpairMissingRho)
      (by
        dsimp only
        rw [sameStarAll R1, hfirstGammaRho, hfirstThetaRho]
        intro _
        refine ⟨⟨_, _, rfl, rfl, hgammaBeforeTheta⟩, ?_⟩
        intro hc
        obtain ⟨_, t, hlo, hhi, he⟩ := Finset.mem_filter.mp hc
        rw [hthetaFirstIndex] at hhi
        exact hgammaUnusedRho t hlo hhi he)

private theorem helper_sameGammaTheta_1572.{u_1, u_2} :
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
    ∀ (gamma : Fin k), (
    ∀ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), (0 : ℕ) <
        S.counterexample.hierarchy.dividerCount ∧ gamma ∈ TreeMissingColors S.coloring
        (S.counterexample.hierarchy.stage (⟨S.counterexample.hierarchy.dividerCount,
    by
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    ⟩ : Fin (S.counterexample.hierarchy.dividerCount + (2 : ℕ)))) ∨
        S.counterexample.hierarchy.dividerCount = (0 : ℕ) ∧ gamma ∈ TreeMissingColors S.coloring
        (S.corresponding.replacementETT.series.data.tree (Fin.last
        S.corresponding.replacementETT.rounds).castSucc)) →
    ∀ (R1 : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let rho : PartialEdgeColoring E k := R1.coloring; HierarchyFirstMissingPosition rho T gamma =
        HierarchyFirstMissingPosition sigma T gamma → HierarchyFirstMissingPosition rho T d.theta
        = HierarchyFirstMissingPosition sigma T d.theta → (
    let H : TashkinovHierarchy R1.corresponding.replacementETT R1.replacementBase :=
        R1.counterexample.hierarchy;
    have q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    have n : Fin (R1.corresponding.replacementETT.rounds + (1 : ℕ)) := Fin.last
        R1.corresponding.replacementETT.rounds;
    have A : TreeSequence G e0 := HierarchyStarredStage H q;
    have Tnq : TreeSequence G e0 := H.stage (⟨H.dividerCount,
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)));
    have Tn : TreeSequence G e0 := R1.corresponding.replacementETT.series.data.tree n.castSucc;
    have Dn : Finset (Fin k) := TashkinovStoredColors R1.corresponding.replacementETT.series.data
        n;
    have Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q;
    have va : V := T.vertex (HierarchyFirstMissingPosition rho T gamma);
    have vb : V := T.vertex (HierarchyFirstMissingPosition rho T d.theta);
    have sameComponent : Prop := TwoColorComponent G rho gamma d.theta (Sum.inl va) =
        TwoColorComponent G rho gamma d.theta (Sum.inl vb); ( (0 : ℕ) < H.dividerCount ∧ (gamma ∈
        TreeMissingColors rho Tnq ∨ Disjoint (insert gamma ({ d.theta } : Finset (Fin k)) : Finset
        (Fin k)) Dnq) → sameComponent) ∧ ( H.dividerCount = (0 : ℕ) ∧ (gamma ∈ TreeMissingColors
        rho Tn ∨ Disjoint (insert gamma ({ d.theta } : Finset (Fin k)) : Finset (Fin k)) Dn) →
        sameComponent) ∧ ( gamma ∈ TreeMissingColors rho A ∧ TreeColorSetClosed G rho A ({ gamma }
        : Finset (Fin k)) → sameComponent ∧ TreeInterchangeable G A rho gamma d.theta)) →
        TwoColorComponent G rho gamma d.theta (Sum.inl (T.vertex (HierarchyFirstMissingPosition
        sigma T gamma))) = TwoColorComponent G rho gamma d.theta (Sum.inl (T.vertex
        (HierarchyFirstMissingPosition sigma T d.theta))) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d R sigma gamma caseGamma R1
      rho hfirstGammaRho hfirstThetaRho changeRho
  have he : TwoColorComponent G rho gamma d.theta
        (Sum.inl (T.vertex (HierarchyFirstMissingPosition rho T gamma))) =
      TwoColorComponent G rho gamma d.theta
        (Sum.inl (T.vertex (HierarchyFirstMissingPosition rho T d.theta))) := by
    rcases caseGamma R1 with ⟨hp, hm⟩ | ⟨hz, hm⟩
    · exact changeRho.1 ⟨hp, Or.inl hm⟩
    · exact changeRho.2.1 ⟨hz, Or.inl hm⟩
  rw [hfirstGammaRho, hfirstThetaRho] at he
  exact he

private theorem helper_hthetaTerminalDistinct_1589.{u_1, u_2} :
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
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let Y : TreeSequence G e0 := HierarchyFullTailPrefix C j; A.length + j < T.length → Y.length =
        A.length + j → (↑(HierarchyFirstMissingPosition d.switched.coloring T d.theta) : ℕ) =
        (HierarchyFullTailPrefix C j).length → T.vertex (HierarchyFirstMissingPosition sigma T
        d.theta) ≠ T.vertex (Fin.last T.length) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d j R sigma H q A Y
      hcutJstrict hYlen hthetaFirstIndex he
  have hv := congrArg Fin.val (T.vertex_injective he)
  simp only [Fin.val_last] at hv
  rw [hthetaFirstIndex] at hv
  have hlt : Y.length < T.length := hYlen.symm ▸ hcutJstrict
  exact Nat.ne_of_lt hlt hv

private theorem helper_swapOne_1608.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
  (T : TreeSequence G e0),
  let z : V ⊕ E := Sum.inl (T.vertex (Fin.last T.length));
  ∀ (old : PartialEdgeColoring E k) (a b : Fin k),
  IsOneEdgeUncolored old e0 →
  IsOneEdgeUncolored (TwoColorComponentSwap G old a b z) e0 := by
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

private theorem helper_hweak3_1679.{u_1, u_2} :
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
        R1.counterexample.hierarchy (Fin.last R1.counterexample.hierarchy.dividerCount) mu3 := by
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

private theorem helper_hstored3_1693.{u_1, u_2} :
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
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q;
    ∀ gamma ∈ TreeMissingColors sigma A, d.theta ∉ D → gamma ≠ d.theta →
    let z : V ⊕ E := Sum.inl (T.vertex (Fin.last T.length)); (
    ∀ (z : V ⊕ E) (rho : PartialEdgeColoring E k) (a b c : Fin k), a ≠ b → IsProperEdgeColoring G
        rho → c ≠ a → c ≠ b → HierarchyFirstMissingPosition (TwoColorComponentSwap G rho a b z) T
        c = HierarchyFirstMissingPosition rho T c) → (
    ∀ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), D =
        HierarchyStoredColorsAt S.counterexample.hierarchy (Fin.last
        S.counterexample.hierarchy.dividerCount) ∧
    ∀ eta ∈ D, R.counterexample.good.gamma q eta = S.counterexample.good.gamma (Fin.last
        S.counterexample.hierarchy.dividerCount) eta) →
    ∀ (R1 : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let rho : PartialEdgeColoring E k := R1.coloring;
    let mu3 : PartialEdgeColoring E k := TwoColorComponentSwap G rho gamma d.theta z;
    ∀ eta ∈ HierarchyStoredColorsAt R1.counterexample.hierarchy (Fin.last
        R1.counterexample.hierarchy.dividerCount), HierarchyFirstMissingPosition mu3 T eta =
        HierarchyFirstMissingPosition rho T eta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d R sigma H q A D gamma
      hgammaA hthetaUnstored' hgammaNeTheta z firstUnaffected sameLast R1 rho mu3 eta heta
  have hetaD : eta ∈ D := (sameLast R1).1.symm ▸ heta
  have hneGamma : eta ≠ gamma := by
    intro he
    exact (Finset.mem_sdiff.mp hetaD).2 (he.symm ▸ hgammaA)
  have hneTheta : eta ≠ d.theta := by
    intro he
    exact hthetaUnstored' (he ▸ hetaD)
  exact firstUnaffected z rho gamma d.theta eta hgammaNeTheta
    R1.minimumContext.proper hneGamma hneTheta

private theorem helper_hgammaCutoff3_1706.{u_1, u_2} :
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
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ));
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ));
    let Y : TreeSequence G e0 := HierarchyFullTailPrefix C j;
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q; beta ∈ D →
    ∀ gamma ∈ R.counterexample.good.gamma q beta, TreeSequenceInitialSegment B X →
        TreeSequenceInitialSegment X Y → (↑(HierarchyFirstMissingPosition sigma T beta) : ℕ) ≤
        B.length → d.theta ∉ D.biUnion (R.counterexample.good.gamma q) → (
    ∀ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), D =
        HierarchyStoredColorsAt S.counterexample.hierarchy (Fin.last
        S.counterexample.hierarchy.dividerCount) ∧
    ∀ eta ∈ D, R.counterexample.good.gamma q eta = S.counterexample.good.gamma (Fin.last
        S.counterexample.hierarchy.dividerCount) eta) →
    ∀ (R1 : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let rho : PartialEdgeColoring E k := R1.coloring; HierarchyFirstMissingPosition rho T beta =
        HierarchyFirstMissingPosition sigma T beta →
    ∀ eta ∈ HierarchyStoredColorsAt R1.counterexample.hierarchy (Fin.last
        R1.counterexample.hierarchy.dividerCount), gamma ∈ R1.counterexample.good.gamma (Fin.last
        R1.counterexample.hierarchy.dividerCount) eta ∨ d.theta ∈ R1.counterexample.good.gamma
        (Fin.last R1.counterexample.hierarchy.dividerCount) eta → (↑(HierarchyFirstMissingPosition
        rho T eta) : ℕ) ≤ Y.length := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d j R sigma H q X B Y D
      hbetaStored gamma hgammaBeta hBtoX hXtoY hbetaFirstLe hthetaOutsideGamma sameLast R1 rho
      hfirstBetaRho eta heta hmem
  have hetaD : eta ∈ D := (sameLast R1).1.symm ▸ heta
  rw [← (sameLast R1).2 eta hetaD] at hmem
  have he : eta = beta := by
    by_contra hne
    rcases hmem with hg | ht
    · exact Finset.disjoint_left.mp
        (R.counterexample.good.disjointPairs q eta beta hetaD hbetaStored hne)
        hg hgammaBeta
    · exact hthetaOutsideGamma (Finset.mem_biUnion.mpr ⟨eta, hetaD, ht⟩)
  subst eta
  rw [hfirstBetaRho]
  exact hbetaFirstLe.trans (hBtoX.1.trans hXtoY.1)

private theorem helper_hYTerminalDistinct_1753.{u_1, u_2} :
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
        (Fin.last T.length) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d j R H q A Y hcutJstrict
      hYlen hYtoT he
  have hi := T.vertex_injective ((hYtoT.2.1 (Fin.last Y.length)).trans he)
  have hv := congrArg Fin.val hi
  simp only [Fin.val_castLE, Fin.val_last] at hv
  exact Nat.ne_of_lt (hYlen.symm ▸ hcutJstrict) hv

private theorem helper_hjEligible_1763.{u_1, u_2} :
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
        → j ∈ HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx := by
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

private theorem helper_continuation_3731.{u_1, u_2} :
    helperContinuation3731Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta hvertexMissing d j hj
      hpathLower hpathUpper R sigma H q A ell X B Y Z D hbetaStored gamma hgammaBeta hgammaA
      hgammaNeBeta hthetaUnstored' hcutJstrict hYlen hYtoT hBtoX hXtoY hYtoZ hZtoT hAtoY
      hgammaFirstLe hbetaFirstLe vertexMemT vertexMemSelf hthetaY hthetaFirst hthetaOutsideGamma
      hgammaNeTheta hAtoZ treeMissingSubset componentSelf componentLeaf separateComponents
      hgammaTerminalDistinct z mu2 prefixMissing firstUnaffected missingTransport sameStarAll
      samePenultimate sameLast routeToY caseGamma hsuffixY hsplitMissing2 hAYstrict R1 hR1 rho
      hmissingRho hElemRho hfirstGammaRho hfirstBetaRho hgammaWitnessRho hthetaWitnessRho
      hthetaYRho hgammaTerminalRho hgammaUnusedRho hthetaUnusedRho hpairMissingRho sameGammaTheta
      hgammaThetaDistinct hthetaTerminalDistinct
  have hdisjoint3 := separateComponents rho gamma d.theta hgammaNeTheta R1.minimumContext.proper
    (T.vertex (HierarchyFirstMissingPosition sigma T gamma))
    (T.vertex (HierarchyFirstMissingPosition sigma T d.theta))
    (T.vertex (Fin.last T.length)) hgammaThetaDistinct hgammaTerminalDistinct
    hthetaTerminalDistinct hgammaWitnessRho hthetaWitnessRho (Or.inl hgammaTerminalRho)
    sameGammaTheta
  let mu3 := TwoColorComponentSwap G rho gamma d.theta z
  have hpath3 : TwoColorPathComponent G rho gamma d.theta z :=
    ⟨hgammaNeTheta, _, componentSelf rho gamma d.theta _,
      componentLeaf rho gamma d.theta hgammaNeTheta R1.minimumContext.proper _
        (Or.inl hgammaTerminalRho)⟩
  have swapOne (old : PartialEdgeColoring E k) (a b : Fin k)
      (ho : IsOneEdgeUncolored old e0) :
      IsOneEdgeUncolored (TwoColorComponentSwap G old a b z) e0 := by
    exact helper_swapOne_1608 (@G) (@k) (@e0) (@T) (@old) (@a) (@b) (@ho)
  have hmu3One : IsOneEdgeUncolored mu3 e0 := swapOne rho gamma d.theta
      R1.minimumContext.oneEdgeUncolored
  have hgammaOutside3 : Sum.inl (T.vertex (HierarchyFirstMissingPosition sigma T gamma)) ∉
      TwoColorComponent G rho gamma d.theta z := by
    intro hm
    exact Set.disjoint_left.mp hdisjoint3 hm (componentSelf rho gamma d.theta _)
  have hthetaOutside3 : Sum.inl (T.vertex (HierarchyFirstMissingPosition sigma T d.theta)) ∉
      TwoColorComponent G rho gamma d.theta z := by
    intro hm
    apply Set.disjoint_left.mp hdisjoint3 hm
    rw [sameGammaTheta]
    exact componentSelf rho gamma d.theta _
  have hmissing3 : ∀ v ∈ TreeSequenceVertexSet Z,
      MissingColors G mu3 v = MissingColors G rho v :=
    prefixMissing Z z rho gamma d.theta hgammaNeTheta R1.minimumContext.proper hElemRho
      (T.vertex (HierarchyFirstMissingPosition sigma T gamma))
      (T.vertex (HierarchyFirstMissingPosition sigma T d.theta))
      (vertexMemT Z hZtoT (HierarchyFirstMissingPosition sigma T gamma)
        (hgammaFirstLe.trans hAtoZ.1))
      (vertexMemT Z hZtoT (HierarchyFirstMissingPosition sigma T d.theta)
        (hthetaFirst.2.trans hYtoZ.1))
      hgammaWitnessRho hthetaWitnessRho hgammaOutside3 hthetaOutside3
  have hfixed3 : ∀ t : Fin T.length, A.length ≤ t.val → t.val < Y.length →
      mu3 (T.edge t) = rho (T.edge t) := by
    intro t hlo hhi
    simp only [mu3, TwoColorComponentSwap, hgammaUnusedRho t hlo hhi,
      hthetaUnusedRho t hlo hhi, ite_false, ite_self]
  have hcase3 :
      let K := R1.counterexample.hierarchy
      (0 < K.dividerCount ∧ gamma ∈ TreeMissingColors rho
        (K.stage ⟨K.dividerCount, Nat.lt_add_of_pos_right (by decide)⟩)) ∨
      (K.dividerCount = 0 ∧
        (gamma ∈ TreeMissingColors rho
            (R1.corresponding.replacementETT.series.data.tree
              (Fin.last R1.corresponding.replacementETT.rounds).castSucc) ∨
          (gamma ∈ TreeMissingColors rho (HierarchyStarredStage K (Fin.last K.dividerCount)) ∧
            gamma ∉ TashkinovStoredColors R1.corresponding.replacementETT.series.data
              (Fin.last R1.corresponding.replacementETT.rounds) ∧
            d.theta ∉ TashkinovStoredColors R1.corresponding.replacementETT.series.data
              (Fin.last R1.corresponding.replacementETT.rounds)))) := by
    rcases caseGamma R1 with h | ⟨hz, hm⟩
    · exact Or.inl h
    · exact Or.inr ⟨hz, Or.inl hm⟩
  have hdisjoint3First : Disjoint (TwoColorComponent G rho gamma d.theta z)
      (TwoColorComponent G rho gamma d.theta
        (Sum.inl (T.vertex (HierarchyFirstMissingPosition rho T gamma)))) := by
    rw [hfirstGammaRho]
    exact hdisjoint3
  have hmissingPairCurrent : gamma ∈ TreeMissingColors rho
        (HierarchyFullTailPrefix R1.counterexample (HierarchyFullTailLength R1.counterexample -
            1)) ∧
      d.theta ∈ TreeMissingColors rho
        (HierarchyFullTailPrefix R1.counterexample (HierarchyFullTailLength R1.counterexample -
            1)) := by
    rw [samePenultimate R1]
    exact hpairMissingRho
  have hweak3 : HierarchyWeaklyStable R1.counterexample.hierarchy
      (Fin.last R1.counterexample.hierarchy.dividerCount) mu3 := by
    exact helper_hweak3_1679 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
        (@alpha) (@beta) (@d) (@gamma) (@hgammaNeTheta) (@samePenultimate) (@R1) (@hElemRho)
        (@hpath3) (@hcase3)
        (@hdisjoint3First) (@hmissingPairCurrent)
  have hstored3 : ∀ eta ∈ HierarchyStoredColorsAt R1.counterexample.hierarchy
        (Fin.last R1.counterexample.hierarchy.dividerCount),
      HierarchyFirstMissingPosition mu3 T eta = HierarchyFirstMissingPosition rho T eta := by
    exact helper_hstored3_1693 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
        (@P) (@alpha) (@beta) (@d) (@gamma) (@hgammaA) (@hthetaUnstored') (@hgammaNeTheta)
        (@firstUnaffected)
        (@sameLast) (@R1)
  have hgammaCutoff3 : ∀ eta ∈ HierarchyStoredColorsAt R1.counterexample.hierarchy
        (Fin.last R1.counterexample.hierarchy.dividerCount),
      (gamma ∈ R1.counterexample.good.gamma (Fin.last R1.counterexample.hierarchy.dividerCount)
          eta ∨
        d.theta ∈ R1.counterexample.good.gamma (Fin.last
            R1.counterexample.hierarchy.dividerCount) eta) →
      (HierarchyFirstMissingPosition rho T eta).val ≤ Y.length := by
    exact helper_hgammaCutoff3_1706 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@ctx) (@P) (@alpha) (@beta) (@d) (@j) (@hbetaStored) (@gamma) (@hgammaBeta) (@hBtoX)
        (@hXtoY)
        (@hbetaFirstLe) (@hthetaOutsideGamma) (@sameLast) (@R1) (@hfirstBetaRho)
  have hsuffixMu2 : TashkinovAugmentationSequence mu2 Y T :=
    TashkinovAugmentationSequenceComponentSwap G k e0 sigma gamma beta hgammaNeBeta z
      Y T hsuffixY hsplitMissing2.1 hsplitMissing2.2
  have hsuffixRho : TashkinovAugmentationSequence rho Y T := by
    change TashkinovAugmentationSequence R1.coloring Y T
    rw [hR1]
    exact hsuffixMu2
  have hsplitMissing3 : gamma ∈ TreeMissingColors mu3 Y ∧ d.theta ∈ TreeMissingColors mu3 Y := by
    rw [missingTransport rho mu3 hmissing3 Y hYtoZ,
      missingTransport sigma rho hmissingRho Y hYtoZ]
    exact ⟨treeMissingSubset hAtoY hgammaA, hthetaY⟩
  have hroute3 := routeToY R1 mu3 hmu3One hweak3 hfixed3 hmissing3
  obtain ⟨_, _, corr2, hmax2, bs2, K2, good2, same2⟩ :=
    StableChangeCasesOneTwoSplitTail G k e0 R1.corresponding.replacementInput T rho
      R1.corresponding.replacementETT R1.replacementBase R1.counterexample R1.minimumContext
      gamma d.theta hgammaNeTheta hmissingPairCurrent z hpath3 mu3 rfl hcase3 hdisjoint3First
      Y (by dsimp only; rw [sameStarAll R1]; exact hAtoY)
      (by dsimp only; rw [sameStarAll R1]; exact hAYstrict)
      (by rw [samePenultimate R1]; exact hYtoZ)
      (by dsimp only; rw [sameStarAll R1]; exact hfixed3) hroute3 hsuffixRho
      hsplitMissing3 (by rw [samePenultimate R1]; exact hmissing3)
      hstored3 hgammaCutoff3
  have hthetaTerminalMu3 : d.theta ∈ MissingColors G mu3 (T.vertex (Fin.last T.length)) :=
    (TwoColorComponentSwapMissingBehavior G rho gamma d.theta hgammaNeTheta
      R1.minimumContext.proper z).2.1 _ (componentSelf rho gamma d.theta _) hgammaTerminalRho
  have hthetaYMu3 : d.theta ∈ MissingColors G mu3 (Y.vertex (Fin.last Y.length)) := by
    rw [hmissing3 _ (TreeSequenceInitialSegmentVertexSetSubset hYtoZ
      (vertexMemSelf Y (Fin.last Y.length)))]
    exact hthetaYRho
  have hYTerminalDistinct : Y.vertex (Fin.last Y.length) ≠ T.vertex (Fin.last T.length) := by
    exact helper_hYTerminalDistinct_1753 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@ctx) (@P) (@alpha) (@beta) (@d) (@j) (@hcutJstrict) (@hYlen) (@hYtoT)
  let C2 : HierarchyCounterexample bs2 := by
    exact @helperC21693 (@V) (@E) inferInstance inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha) (@beta) (@d)
        (@j) (@gamma) (@hYtoT) (@vertexMemSelf) (@R1) (@corr2) (@hmax2) (@bs2) (@K2) (@good2)
        (@hthetaTerminalMu3) (@hthetaYMu3) (@hYTerminalDistinct)
  obtain ⟨R2, hR2⟩ := HierarchyReplacementPresentationTrans G k e0 input T phi
    ett base C ctx R1 mu3 corr2 bs2 C2 same2
  have hjEligible : j ∈ HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx
     := by
    exact helper_hjEligible_1763 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
        (@P) (@alpha) (@beta) (@d) (@j) (@hpathLower) (@hpathUpper) (@gamma) (@R1)
        (@hthetaTerminalMu3) (@hthetaYMu3) (@R2) (@hR2)
  have hbound := HierarchySituationThreeEligibleIndexBound G k e0 input T phi ett base C ctx
    (by rw [hj]; exact hpathLower) (by rw [hj]; exact hpathUpper) hvertexMissing j hjEligible
  rw [hj] at hbound
  exact Nat.lt_irrefl j hbound

private theorem helper_continuation_3727.{u_1, u_2} :
    helperContinuation3727Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta hvertexMissing d j hj
      hpathLower hpathUpper R sigma H q A ell X B Y Z D hbetaStored hbetaTail hthetaMissingY
      gamma hgammaBeta hgammaA hgammaNeBeta hthetaUnstored' sameStar hcutJstrict hYlen hYtoT
      hBtoX hXtoY hYtoZ hZtoT hAtoY hElemZ hgammaFirst hgammaFirstLe hbetaFirstLe vertexMemT
      vertexMemSelf hthetaY hthetaFirst hthetaFirstIndex hthetaOutsideGamma hgammaNeTheta hAtoZ
      treeMissingSubset hgammaMissingZ hbetaMissingZ hchangeElementary componentSelf
      componentLeaf separateComponents hgammaTerminalDistinct z mu2 hgammaTerminalMu2
      hfixedThroughY prefixMissing firstPreserved firstUnaffected hmissingMu2 missingTransport
      sameStarAll samePenultimate sameLast routeToY caseGamma hsuffixY hsplitMissing2 hAYstrict
      R1 hR1 sameFullPrefix hthetaNotRaw
  have thetaRawIfUsed : ∀ t : Fin Y.length, A.length ≤ t.val →
      t.val < A.length + j → sigma (Y.edge t) = some d.theta →
      d.theta ∈ TashkinovStoredColors R.corresponding.replacementETT.series.data
        (Fin.last R.corresponding.replacementETT.rounds) := by
    exact helper_thetaRawIfUsed_1463 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@ctx) (@P) (@alpha) (@beta) (@d) (@j) (@hpathLower) (@hpathUpper) (@hthetaMissingY)
        (@sameStar)
        (@hchangeElementary) (@sameFullPrefix)
  have hthetaUnused : ∀ t : Fin T.length, A.length ≤ t.val → t.val < Y.length →
      sigma (T.edge t) ≠ some d.theta := by
    exact helper_hthetaUnused_1483 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@ctx) (@P) (@alpha) (@beta) (@d) (@j) (@hYlen) (@hYtoT) (@hthetaNotRaw) (@thetaRawIfUsed)
  let rho := R1.coloring
  have hmissingRho : ∀ v ∈ TreeSequenceVertexSet Z,
      MissingColors G rho v = MissingColors G sigma v := by
    rw [show rho = mu2 from hR1]
    exact hmissingMu2
  have hElemRho : ColoredVertexSetElementary G rho (TreeSequenceVertexSet Z) := by
    intro u hu v hv huv
    rw [hmissingRho u hu, hmissingRho v hv]
    exact hElemZ hu hv huv
  have hthetaMissingZ : d.theta ∈ TreeMissingColors sigma Z := treeMissingSubset hYtoZ hthetaY
  have hfirstGammaRho : HierarchyFirstMissingPosition rho T gamma =
      HierarchyFirstMissingPosition sigma T gamma :=
    firstPreserved Z hZtoT sigma rho gamma hElemZ hmissingRho hgammaMissingZ
  have hfirstThetaRho : HierarchyFirstMissingPosition rho T d.theta =
      HierarchyFirstMissingPosition sigma T d.theta :=
    firstPreserved Z hZtoT sigma rho d.theta hElemZ hmissingRho hthetaMissingZ
  have hfirstBetaRho : HierarchyFirstMissingPosition rho T beta =
      HierarchyFirstMissingPosition sigma T beta :=
    firstPreserved Z hZtoT sigma rho beta hElemZ hmissingRho hbetaMissingZ
  have hgammaWitnessRho : gamma ∈ MissingColors G rho
      (T.vertex (HierarchyFirstMissingPosition sigma T gamma)) := by
    rw [hmissingRho _ (vertexMemT Z hZtoT (HierarchyFirstMissingPosition sigma T gamma)
      (hgammaFirstLe.trans hAtoZ.1))]
    exact hgammaFirst.1
  have hthetaWitnessRho : d.theta ∈ MissingColors G rho
      (T.vertex (HierarchyFirstMissingPosition sigma T d.theta)) := by
    rw [hmissingRho _ (vertexMemT Z hZtoT (HierarchyFirstMissingPosition sigma T d.theta)
      (hthetaFirst.2.trans hYtoZ.1))]
    exact hthetaFirst.1
  have hthetaYRho : d.theta ∈ MissingColors G rho (Y.vertex (Fin.last Y.length)) := by
    rw [hmissingRho _ (TreeSequenceInitialSegmentVertexSetSubset hYtoZ
      (vertexMemSelf Y (Fin.last Y.length)))]
    exact hthetaMissingY
  have hgammaTerminalRho : gamma ∈ MissingColors G rho (T.vertex (Fin.last T.length)) := by
    rw [show rho = mu2 from hR1]
    exact hgammaTerminalMu2
  have hgammaUnusedRho : ∀ t : Fin T.length, A.length ≤ t.val → t.val < Y.length →
      rho (T.edge t) ≠ some gamma := by
    intro t hlo hhi hc
    rw [show rho = mu2 from hR1, hfixedThroughY t hlo (hYlen ▸ hhi)] at hc
    exact Finset.disjoint_left.mp hbetaTail (Finset.mem_union_left _ hgammaBeta)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, hlo, hYlen ▸ hhi, hc⟩)
  have hthetaUnusedRho : ∀ t : Fin T.length, A.length ≤ t.val → t.val < Y.length →
      rho (T.edge t) ≠ some d.theta := by
    intro t hlo hhi
    rw [show rho = mu2 from hR1, hfixedThroughY t hlo (hYlen ▸ hhi)]
    exact hthetaUnused t hlo hhi
  have hgammaBeforeTheta : (HierarchyFirstMissingPosition sigma T gamma).val <
      (HierarchyFirstMissingPosition sigma T d.theta).val := by
    rw [hthetaFirstIndex]
    exact hgammaFirstLe.trans_lt hAYstrict
  have hpairMissingRho : gamma ∈ TreeMissingColors rho Z ∧ d.theta ∈ TreeMissingColors rho Z := by
    have he := missingTransport sigma rho hmissingRho Z ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
    rw [he]
    exact ⟨hgammaMissingZ, hthetaMissingZ⟩
  have changeRho := by
    exact helper_changeRho_1547 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
        (@P) (@alpha) (@beta) (@d) (@j) (@gamma) (@hthetaFirstIndex) (@hgammaNeTheta) (@sameStarAll)
        (@samePenultimate) (@R1) (@hElemRho) (@hfirstGammaRho) (@hfirstThetaRho)
        (@hgammaUnusedRho) (@hgammaBeforeTheta) (@hpairMissingRho)
  have sameGammaTheta : TwoColorComponent G rho gamma d.theta
        (Sum.inl (T.vertex (HierarchyFirstMissingPosition sigma T gamma))) =
      TwoColorComponent G rho gamma d.theta
        (Sum.inl (T.vertex (HierarchyFirstMissingPosition sigma T d.theta))) := by
    exact helper_sameGammaTheta_1572 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@ctx) (@P) (@alpha) (@beta) (@d) (@gamma) (@caseGamma) (@R1) (@hfirstGammaRho)
        (@hfirstThetaRho)
        (@changeRho)
  have hgammaThetaDistinct : T.vertex (HierarchyFirstMissingPosition sigma T gamma) ≠
      T.vertex (HierarchyFirstMissingPosition sigma T d.theta) := by
    intro he
    exact ne_of_lt hgammaBeforeTheta (congrArg Fin.val (T.vertex_injective he))
  have hthetaTerminalDistinct : T.vertex (HierarchyFirstMissingPosition sigma T d.theta) ≠
      T.vertex (Fin.last T.length) := by
    exact helper_hthetaTerminalDistinct_1589 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base)
        (@C) (@ctx) (@P) (@alpha) (@beta) (@d) (@j) (@hcutJstrict) (@hYlen) (@hthetaFirstIndex)
  exact @helper_continuation_3731 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha)
      (@beta) (@hvertexMissing) (@d) (@j) (@hj) (@hpathLower) (@hpathUpper) (@hbetaStored)
      (@gamma) (@hgammaBeta) (@hgammaA) (@hgammaNeBeta) (@hthetaUnstored') (@hcutJstrict)
      (@hYlen) (@hYtoT) (@hBtoX) (@hXtoY) (@hYtoZ) (@hZtoT) (@hAtoY) (@hgammaFirstLe)
      (@hbetaFirstLe) (@vertexMemT) (@vertexMemSelf) (@hthetaY) (@hthetaFirst)
      (@hthetaOutsideGamma) (@hgammaNeTheta) (@hAtoZ) (@treeMissingSubset) (@componentSelf)
      (@componentLeaf) (@separateComponents) (@hgammaTerminalDistinct) (@prefixMissing)
      (@firstUnaffected) (@missingTransport) (@sameStarAll) (@samePenultimate) (@sameLast)
      (@routeToY) (@caseGamma) (@hsuffixY) (@hsplitMissing2) (@hAYstrict) (@R1) (@hR1)
      (@hmissingRho) (@hElemRho) (@hfirstGammaRho) (@hfirstBetaRho) (@hgammaWitnessRho)
      (@hthetaWitnessRho) (@hthetaYRho) (@hgammaTerminalRho) (@hgammaUnusedRho)
      (@hthetaUnusedRho) (@hpairMissingRho) (@sameGammaTheta) (@hgammaThetaDistinct)
      (@hthetaTerminalDistinct)

private theorem helper_continuation_3042.{u_1, u_2} :
    helperContinuation3042Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta hvertexMissing d j hj
      hpathLower hpathUpper R sigma H q A ell X B Y Z D hbetaStored hbetaB hbetaTail
      hthetaMissingY gamma hgammaBeta hgammaA hgammaNeBeta hthetaUnstored' sameStar hAtoT
      hcutJstrict commonPrefix hYlen hBtoT hYtoT hBtoX hXtoY hYtoZ hZtoT hAtoY
      penultimatePrefixEq hElemZ firstWitness hgammaFirst hgammaFirstLe hbetaFirstLe vertexMemT
      vertexMemSelf hthetaY hthetaFirst hthetaFirstIndex hthetaOutsideGamma hgammaNeTheta hAtoZ
      treeMissingSubset hgammaMissingZ hbetaMissingZ hchangeElementary hchangeMissing
      componentSelf componentLeaf separateComponents hgammaTerminalDistinct hterminalDisjoint z
      mu2 hmu2One hgammaFirstMu2 hgammaTerminalMu2 hfixedThroughY prefixMissing firstPreserved
      firstUnaffected hmissingMu2 missingTransport hstoredMu2 hgammaCutoff sameStarAll
      samePenultimate sameLast routeToY
  have caseGamma (S : HierarchyReplacementPresentation
      G k e0 input T phi ett base C ctx) :
      (0 < S.counterexample.hierarchy.dividerCount ∧
        gamma ∈ TreeMissingColors S.coloring (S.counterexample.hierarchy.stage
          ⟨S.counterexample.hierarchy.dividerCount, Nat.lt_add_of_pos_right (by decide)⟩)) ∨
      (S.counterexample.hierarchy.dividerCount = 0 ∧
        gamma ∈ TreeMissingColors S.coloring
          (S.corresponding.replacementETT.series.data.tree
            (Fin.last S.corresponding.replacementETT.rounds).castSucc)) := by
    exact helper_caseGamma_1360 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
        (@P) (@alpha) (@beta) (@d) (@hbetaStored) (@gamma) (@hgammaBeta) (@sameLast) (@S)
  have hcase1 :
      (0 < H.dividerCount ∧ gamma ∈ TreeMissingColors sigma
        (H.stage ⟨H.dividerCount, Nat.lt_add_of_pos_right (by decide)⟩)) ∨
      (H.dividerCount = 0 ∧
        (gamma ∈ TreeMissingColors sigma
            (R.corresponding.replacementETT.series.data.tree
              (Fin.last R.corresponding.replacementETT.rounds).castSucc) ∨
          (gamma ∈ TreeMissingColors sigma A ∧
            gamma ∉ TashkinovStoredColors R.corresponding.replacementETT.series.data
              (Fin.last R.corresponding.replacementETT.rounds) ∧
            beta ∉ TashkinovStoredColors R.corresponding.replacementETT.series.data
              (Fin.last R.corresponding.replacementETT.rounds)))) := by
    rcases caseGamma R with h | ⟨hz, hm⟩
    · exact Or.inl h
    · exact Or.inr ⟨hz, Or.inl hm⟩
  have hpath1 : TwoColorPathComponent G sigma gamma beta z :=
    ⟨hgammaNeBeta, _, componentSelf sigma gamma beta _,
      componentLeaf sigma gamma beta hgammaNeBeta R.minimumContext.proper _
        (Or.inr d.betaMissingTerminal)⟩
  have hweak1 : HierarchyWeaklyStable H q mu2 := by
    exact helper_hweak1_1415 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
        (@alpha) (@beta) (@d) (@gamma) (@hgammaNeBeta) (@hchangeElementary) (@hchangeMissing)
        (@hterminalDisjoint)
        (@hcase1) (@hpath1)
  have hsuffixX : TashkinovAugmentationSequence sigma X T := by
    simpa only [X, sigma, R, hj] using d.transportedSuffix
  have hsuffixY : TashkinovAugmentationSequence sigma Y T :=
    TashkinovAugmentationSequenceSuffix sigma X Y T hsuffixX hXtoY hYtoT
  have hsplitMissing2 : gamma ∈ TreeMissingColors mu2 Y ∧ beta ∈ TreeMissingColors mu2 Y := by
    rw [missingTransport sigma mu2 hmissingMu2 Y hYtoZ]
    exact ⟨treeMissingSubset hAtoY hgammaA,
      treeMissingSubset (commonPrefix hBtoT hYtoT (hBtoX.1.trans hXtoY.1)) hbetaB⟩
  have hAYstrict : A.length < Y.length := by
    have hj : 2 ≤ j := hpathLower
    clear * - hj hYlen
    omega
  have hroute2 := routeToY R mu2 hmu2One hweak1
    (fun t hlo hhi => hfixedThroughY t hlo (hYlen ▸ hhi)) hmissingMu2
  obtain ⟨_, _, corr1, hmax1, bs1, K1, good1, same1⟩ :=
    StableChangeCasesOneTwoSplitTail G k e0 R.corresponding.replacementInput T sigma
      R.corresponding.replacementETT R.replacementBase R.counterexample R.minimumContext
      gamma beta hgammaNeBeta hchangeMissing z hpath1 mu2 rfl hcase1 hterminalDisjoint
      Y hAtoY hAYstrict (by rw [penultimatePrefixEq]; exact hYtoZ)
      (fun t hlo hhi => hfixedThroughY t hlo (hYlen ▸ hhi)) hroute2 hsuffixY
      hsplitMissing2 (by rw [penultimatePrefixEq]; exact hmissingMu2)
      hstoredMu2 hgammaCutoff
  let C1 : HierarchyCounterexample bs1 := by
    exact @helperC11319 (@V) (@E) inferInstance inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha) (@beta) (@d)
        (@gamma) (@vertexMemSelf) (@hgammaTerminalDistinct) (@hgammaFirstMu2)
        (@hgammaTerminalMu2) (@corr1) (@hmax1) (@bs1) (@K1) (@good1)
  obtain ⟨R1, hR1⟩ := HierarchyReplacementPresentationTrans G k e0 input T phi
    ett base C ctx R mu2 corr1 bs1 C1 same1
  have sameFullPrefix (S : HierarchyReplacementPresentation
      G k e0 input T phi ett base C ctx) (m : ℕ) :
      HierarchyFullTailPrefix S.counterexample m = HierarchyFullTailPrefix C m := by
    simp only [HierarchyFullTailPrefix, sameStarAll S, sameStar]
  have hthetaNotA : d.theta ∉ TreeMissingColors sigma A := by
    intro hm
    have hle := (firstWitness sigma A hAtoT d.theta hm).2
    rw [hthetaFirstIndex] at hle
    exact Nat.not_le_of_gt hAYstrict hle
  have hthetaNotRaw : d.theta ∉ TashkinovStoredColors
      R.corresponding.replacementETT.series.data
        (Fin.last R.corresponding.replacementETT.rounds) := by
    intro hm
    exact hthetaUnstored' (Finset.mem_sdiff.mpr ⟨hm, hthetaNotA⟩)
  exact @helper_continuation_3727 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha)
      (@beta) (@hvertexMissing) (@d) (@j) (@hj) (@hpathLower) (@hpathUpper) (@hbetaStored)
      (@hbetaTail) (@hthetaMissingY) (@gamma) (@hgammaBeta) (@hgammaA) (@hgammaNeBeta)
      (@hthetaUnstored') (@sameStar) (@hcutJstrict) (@hYlen) (@hYtoT) (@hBtoX) (@hXtoY) (@hYtoZ)
      (@hZtoT) (@hAtoY) (@hElemZ) (@hgammaFirst) (@hgammaFirstLe) (@hbetaFirstLe) (@vertexMemT)
      (@vertexMemSelf) (@hthetaY) (@hthetaFirst) (@hthetaFirstIndex) (@hthetaOutsideGamma)
      (@hgammaNeTheta) (@hAtoZ) (@treeMissingSubset) (@hgammaMissingZ) (@hbetaMissingZ)
      (@hchangeElementary) (@componentSelf) (@componentLeaf) (@separateComponents)
      (@hgammaTerminalDistinct) (@hgammaTerminalMu2) (@hfixedThroughY) (@prefixMissing)
      (@firstPreserved) (@firstUnaffected) (@hmissingMu2) (@missingTransport) (@sameStarAll)
      (@samePenultimate) (@sameLast) (@routeToY) (@caseGamma) (@hsuffixY) (@hsplitMissing2)
      (@hAYstrict) (@R1) (@hR1) (@sameFullPrefix) (@hthetaNotRaw)
private theorem helper_continuation_3933.{u_1, u_2} :
    helperContinuation3933Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta hvertexMissing d j hj
      hpathLower hpathUpper R sigma H q A ell X B Y Z D hbetaStored hbetaB hbetaTail
      hthetaMissingY gamma hgammaBeta hgammaA hgammaNeBeta hthetaUnstored' sameStar hAtoT htail
      hcutJstrict fullPrefixEq commonPrefix hYlen hBtoT hYtoT hBtoX hXtoY hYtoZ hZtoT hAtoY
      penultimatePrefixEq hElemZ firstWitness hgammaFirst hgammaFirstLe hbetaFirstLe vertexMemT
      vertexMemSelf hthetaY hthetaFirst hthetaFirstIndex hthetaOutsideGamma hgammaNeTheta hAtoZ
      treeMissingSubset hgammaMissingZ hbetaMissingZ hchangeElementary hchangeMissing
      componentSelf componentLeaf separateComponents hgammaTerminalDistinct hterminalDisjoint z
      mu2 hmu2One hgammaFirstMu2 hgammaTerminalMu2 hfixedThroughY prefixMissing firstPreserved
      firstUnaffected hmissingMu2 missingTransport
  have hstoredMu2 : ∀ eta ∈ D,
      HierarchyFirstMissingPosition mu2 T eta =
        HierarchyFirstMissingPosition sigma T eta := by
    exact helper_hstoredMu2_1218 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
        (@P) (@alpha) (@beta) (@d) (@gamma) (@hgammaA) (@hgammaNeBeta) (@hZtoT) (@hElemZ)
        (@hbetaMissingZ) (@firstPreserved) (@firstUnaffected) (@hmissingMu2)
  have hgammaCutoff : ∀ eta ∈ D,
      (gamma ∈ R.counterexample.good.gamma q eta ∨
        beta ∈ R.counterexample.good.gamma q eta) →
      (HierarchyFirstMissingPosition sigma T eta).val ≤ Y.length := by
    exact helper_hgammaCutoff_1230 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@ctx) (@P) (@alpha) (@beta) (@d) (@j) (@hbetaStored) (@gamma) (@hgammaBeta) (@hBtoX)
        (@hXtoY)
        (@hbetaFirstLe)
  have originalStar (S : HierarchyReplacementPresentation
      G k e0 input T phi ett base C ctx) :
      HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) =
        HierarchyStarredStage S.counterexample.hierarchy
          (Fin.last S.counterexample.hierarchy.dividerCount) := by
    exact helper_originalStar_1244 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@ctx) (@S)
  have sameStarAll (S : HierarchyReplacementPresentation
      G k e0 input T phi ett base C ctx) :
      HierarchyStarredStage S.counterexample.hierarchy
        (Fin.last S.counterexample.hierarchy.dividerCount) = A :=
    (originalStar S).symm.trans sameStar
  have samePenultimate (S : HierarchyReplacementPresentation
      G k e0 input T phi ett base C ctx) :
      HierarchyFullTailPrefix S.counterexample
        (HierarchyFullTailLength S.counterexample - 1) = Z := by
    simp only [HierarchyFullTailPrefix, HierarchyFullTailLength, sameStarAll S]
    simp only [Z, ell, HierarchyFullTailPrefix, HierarchyFullTailLength, sameStar]
  have lastData (S : HierarchyReplacementPresentation
      G k e0 input T phi ett base C ctx) :
      HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount) =
        HierarchyStoredColorsAt S.counterexample.hierarchy
          (Fin.last S.counterexample.hierarchy.dividerCount) ∧
      ∀ eta ∈ HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount),
        C.good.gamma (Fin.last C.hierarchy.dividerCount) eta =
          S.counterexample.good.gamma (Fin.last S.counterexample.hierarchy.dividerCount) eta := by
    exact helper_lastData_1275 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@S)
  have sameLast (S : HierarchyReplacementPresentation
      G k e0 input T phi ett base C ctx) :
      D = HierarchyStoredColorsAt S.counterexample.hierarchy
        (Fin.last S.counterexample.hierarchy.dividerCount) ∧
      ∀ eta ∈ D, R.counterexample.good.gamma q eta =
        S.counterexample.good.gamma (Fin.last S.counterexample.hierarchy.dividerCount) eta := by
    exact helper_sameLast_1290 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
        (@P) (@alpha) (@beta) (@d) (@lastData) (@S)
  have weakEdges {input' : PartialEdgeColoring E k}
      (old new : PartialEdgeColoring E k)
      (et : ExtendedTashkinovTree G k e0 input' T old)
      (bs : HierarchyBase et old) (K : TashkinovHierarchy et bs)
      (hw : HierarchyWeaklyStable K (Fin.last K.dividerCount) new)
      (ho : IsOneEdgeUncolored old e0) (hn : IsOneEdgeUncolored new e0) :
      ∀ t : Fin (HierarchyStarredStage K (Fin.last K.dividerCount)).length,
        new ((HierarchyStarredStage K (Fin.last K.dividerCount)).edge t) =
          old ((HierarchyStarredStage K (Fin.last K.dividerCount)).edge t) := by
    exact helper_weakEdges_1301 (@G) (@k) (@e0) (@T) (@old) (@new) (@et) (@bs) (@K) (@hw) (@ho)
        (@hn)
  have hXYlen : Y.length = X.length + 1 := by
    exact helper_hXYlen_1327 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
        (@alpha) (@beta) (@d) (@j) (@hj) (@hpathLower) (@hAtoT) (@htail) (@fullPrefixEq)
  have routeToY (S : HierarchyReplacementPresentation
      G k e0 input T phi ett base C ctx) (nu : PartialEdgeColoring E k)
      (hn : IsOneEdgeUncolored nu e0)
      (hw : HierarchyWeaklyStable S.counterexample.hierarchy
        (Fin.last S.counterexample.hierarchy.dividerCount) nu)
      (hf : ∀ t : Fin T.length, A.length ≤ t.val → t.val < Y.length →
        nu (T.edge t) = S.coloring (T.edge t))
      (hm : ∀ v ∈ TreeSequenceVertexSet Z,
        MissingColors G nu v = MissingColors G S.coloring v) :
      let et := S.corresponding.replacementETT
      let n := Fin.last et.rounds
      let Tn := et.series.data.tree n.castSucc
      (et.series.data.kind n = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence nu Tn Y) ∨
      ((et.series.data.kind n = some TashkinovExtensionKind.SE ∨
        et.series.data.kind n = some TashkinovExtensionKind.RE) ∧
        ∃ (f : E) (seed : TreeSequence G e0),
          et.series.data.connectingEdges n = {f} ∧
          TreeSequenceAdjoinEdge Tn f seed ∧
          TashkinovAugmentationSequence nu seed Y) := by
    exact @helper_routeToY_1012 V E inferInstance inferInstance inferInstance inferInstance G k
        e0 input T phi ett base C ctx P alpha beta d j hj hpathLower hAtoT commonPrefix hYlen
        hYtoT hXtoY hYtoZ hAtoY sameStarAll weakEdges hXYlen S nu hn hw hf hm
  exact @helper_continuation_3042 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha)
      (@beta) (@hvertexMissing) (@d) (@j) (@hj) (@hpathLower) (@hpathUpper) (@hbetaStored)
      (@hbetaB) (@hbetaTail) (@hthetaMissingY) (@gamma) (@hgammaBeta) (@hgammaA) (@hgammaNeBeta)
      (@hthetaUnstored') (@sameStar) (@hAtoT) (@hcutJstrict) (@commonPrefix) (@hYlen) (@hBtoT)
      (@hYtoT) (@hBtoX) (@hXtoY) (@hYtoZ) (@hZtoT) (@hAtoY) (@penultimatePrefixEq) (@hElemZ)
      (@firstWitness) (@hgammaFirst) (@hgammaFirstLe) (@hbetaFirstLe) (@vertexMemT)
      (@vertexMemSelf) (@hthetaY) (@hthetaFirst) (@hthetaFirstIndex) (@hthetaOutsideGamma)
      (@hgammaNeTheta) (@hAtoZ) (@treeMissingSubset) (@hgammaMissingZ) (@hbetaMissingZ)
      (@hchangeElementary) (@hchangeMissing) (@componentSelf) (@componentLeaf)
      (@separateComponents) (@hgammaTerminalDistinct) (@hterminalDisjoint) (@hmu2One)
      (@hgammaFirstMu2) (@hgammaTerminalMu2) (@hfixedThroughY) (@prefixMissing) (@firstPreserved)
      (@firstUnaffected) (@hmissingMu2) (@missingTransport) (@hstoredMu2) (@hgammaCutoff)
      (@sameStarAll) (@samePenultimate) (@sameLast) (@routeToY)

private theorem helper_continuation_2662.{u_1, u_2} :
    helperContinuation2662Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta hvertexMissing d j hj
      hpathLower hpathUpper R sigma H q A ell X B Y Z D hbetaStored hbetaB hbetaTail
      hthetaMissingY gamma hgammaBeta hgammaA hgammaNeBeta hthetaUnstored' sameStar hAtoT htail
      hcutJstrict fullPrefixEq commonPrefix hYlen hBtoT hYtoT hBtoX hXtoY hYtoZ hZtoT hAtoY
      penultimatePrefixEq hElemZ firstWitness hgammaFirst hbetaFirst hgammaFirstLe hbetaFirstLe
      vertexMemT vertexMemSelf hthetaY hthetaFirst hthetaFirstIndex hthetaOutsideGamma
      hgammaNeTheta hAtoZ hBtoZ treeMissingSubset hgammaMissingZ hbetaMissingZ hchangeElementary
      hchangeMissing sameGammaBeta componentSelf componentLeaf separateComponents hBlt
      hindicesDistinct hgammaTerminalDistinct
  have hbetaTerminalDistinct :
      T.vertex (HierarchyFirstMissingPosition sigma T beta) ≠
        T.vertex (Fin.last T.length) := by
    exact helper_hbetaTerminalDistinct_1049 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base)
        (@C) (@ctx) (@P) (@alpha) (@beta) (@d) (@j) (@hbetaFirstLe) (@hBlt)
  have hterminalDisjoint := separateComponents sigma gamma beta hgammaNeBeta
      R.minimumContext.proper
      (T.vertex (HierarchyFirstMissingPosition sigma T gamma))
      (T.vertex (HierarchyFirstMissingPosition sigma T beta))
      (T.vertex (Fin.last T.length)) hindicesDistinct hgammaTerminalDistinct
      hbetaTerminalDistinct hgammaFirst.1 hbetaFirst.1 (Or.inr d.betaMissingTerminal)
      sameGammaBeta
  let z : Sum V E := Sum.inl (T.vertex (Fin.last T.length))
  let mu2 := TwoColorComponentSwap G sigma gamma beta z
  have hmu2Proper : IsProperEdgeColoring G mu2 := by
    exact TwoColorComponentSwapProper G sigma gamma beta hgammaNeBeta
      R.minimumContext.proper z
  have hmu2One : IsOneEdgeUncolored mu2 e0 := by
    exact helper_hmu2One_1069 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
        (@P) (@alpha) (@beta) (@d) (@gamma)
  have hfirstGammaOutside : Sum.inl
      (T.vertex (HierarchyFirstMissingPosition sigma T gamma)) ∉
        TwoColorComponent G sigma gamma beta z := by
    intro hv
    exact (Set.disjoint_left.mp hterminalDisjoint) hv
      (componentSelf sigma gamma beta
        (T.vertex (HierarchyFirstMissingPosition sigma T gamma)))
  have hfirstBetaOutside : Sum.inl
      (T.vertex (HierarchyFirstMissingPosition sigma T beta)) ∉
        TwoColorComponent G sigma gamma beta z := by
    exact helper_hfirstBetaOutside_1094 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@ctx) (@P) (@alpha) (@beta) (@d) (@gamma) (@sameGammaBeta) (@componentSelf)
        (@hterminalDisjoint)
  have hswapBehavior := TwoColorComponentSwapMissingBehavior G sigma gamma beta
    hgammaNeBeta R.minimumContext.proper z
  have hgammaFirstMu2 : gamma ∈ MissingColors G mu2
      (T.vertex (HierarchyFirstMissingPosition sigma T gamma)) := by
    rw [(hswapBehavior.1 _ hfirstGammaOutside)]
    exact hgammaFirst.1
  have hbetaFirstMu2 : beta ∈ MissingColors G mu2
      (T.vertex (HierarchyFirstMissingPosition sigma T beta)) := by
    rw [(hswapBehavior.1 _ hfirstBetaOutside)]
    exact hbetaFirst.1
  have hgammaTerminalMu2 : gamma ∈ MissingColors G mu2
      (T.vertex (Fin.last T.length)) := by
    exact hswapBehavior.2.2.1 _ (componentSelf sigma gamma beta
      (T.vertex (Fin.last T.length))) d.betaMissingTerminal
  have hfixedThroughY : ∀ t : Fin T.length, A.length ≤ t.val →
      t.val < A.length + j → mu2 (T.edge t) = sigma (T.edge t) := by
    exact helper_hfixedThroughY_1119 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@ctx) (@P) (@alpha) (@beta) (@d) (@j) (@hbetaTail) (@gamma) (@hgammaBeta)
  have prefixMissing (W : TreeSequence G e0) (z : Sum V E) (rho : PartialEdgeColoring E k) (a b :
      Fin k) (hne : a ≠ b)
      (hp : IsProperEdgeColoring G rho)
      (helem : ColoredVertexSetElementary G rho (TreeSequenceVertexSet W))
      (u v : V) (huB : u ∈ TreeSequenceVertexSet W) (hvB : v ∈ TreeSequenceVertexSet W)
      (hu : a ∈ MissingColors G rho u) (hv : b ∈ MissingColors G rho v)
      (hdu : Sum.inl u ∉ TwoColorComponent G rho a b z)
      (hdv : Sum.inl v ∉ TwoColorComponent G rho a b z) :
      ∀ w ∈ TreeSequenceVertexSet W,
        MissingColors G (TwoColorComponentSwap G rho a b z) w = MissingColors G rho w := by
    exact TwoColorComponentSwapMissingOnElementarySet (TreeSequenceVertexSet W) rho a b
      hne hp helem z u v huB hvB hu hv hdu hdv
  have firstPreserved (W : TreeSequence G e0)
      (hWT : TreeSequenceInitialSegment W T) (rho sigma : PartialEdgeColoring E k) (c : Fin k)
      (helem : ColoredVertexSetElementary G rho (TreeSequenceVertexSet W))
      (hmiss : ∀ v ∈ TreeSequenceVertexSet W, MissingColors G sigma v = MissingColors G rho v)
      (hc : c ∈ TreeMissingColors rho W) :
      HierarchyFirstMissingPosition sigma T c = HierarchyFirstMissingPosition rho T c := by
    exact helper_firstPreserved_1154 (@G) (@k) (@e0) (@T) (@j) (@firstWitness) (@W) (@hWT) (@rho)
        (@sigma) (@c) (@helem) (@hmiss) (@hc)
  have firstUnaffected (z : Sum V E) (rho : PartialEdgeColoring E k) (a b c : Fin k)
      (hne : a ≠ b) (hp : IsProperEdgeColoring G rho) (hca : c ≠ a) (hcb : c ≠ b) :
      HierarchyFirstMissingPosition (TwoColorComponentSwap G rho a b z) T c =
        HierarchyFirstMissingPosition rho T c := by
    exact helper_firstUnaffected_1179 (@G) (@k) (@e0) (@T) (@z) (@rho) (@a) (@b) (@c) (@hne)
        (@hp) (@hca) (@hcb)
  have hmissingMu2 : ∀ v ∈ TreeSequenceVertexSet Z,
      MissingColors G mu2 v = MissingColors G sigma v := by
    exact helper_hmissingMu2_1194 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
        (@P) (@alpha) (@beta) (@d) (@j) (@gamma) (@hgammaNeBeta) (@hZtoT) (@hElemZ) (@hgammaFirst)
        (@hbetaFirst) (@hgammaFirstLe) (@hbetaFirstLe) (@vertexMemT) (@hAtoZ) (@hBtoZ)
        (@hfirstGammaOutside) (@hfirstBetaOutside) (@prefixMissing)
  have missingTransport (old new : PartialEdgeColoring E k)
      (hm : ∀ v ∈ TreeSequenceVertexSet Z,
        MissingColors G new v = MissingColors G old v)
      (W : TreeSequence G e0) (hWZ : TreeSequenceInitialSegment W Z) :
      TreeMissingColors new W = TreeMissingColors old W := by
    exact helper_missingTransport_1207 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@old) (@new)
        (@hm) (@W) (@hWZ)
  exact @helper_continuation_3933 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha)
      (@beta) (@hvertexMissing) (@d) (@j) (@hj) (@hpathLower) (@hpathUpper) (@hbetaStored)
      (@hbetaB) (@hbetaTail) (@hthetaMissingY) (@gamma) (@hgammaBeta) (@hgammaA) (@hgammaNeBeta)
      (@hthetaUnstored') (@sameStar) (@hAtoT) (@htail) (@hcutJstrict) (@fullPrefixEq)
      (@commonPrefix) (@hYlen) (@hBtoT) (@hYtoT) (@hBtoX) (@hXtoY) (@hYtoZ) (@hZtoT) (@hAtoY)
      (@penultimatePrefixEq) (@hElemZ) (@firstWitness) (@hgammaFirst) (@hgammaFirstLe)
      (@hbetaFirstLe) (@vertexMemT) (@vertexMemSelf) (@hthetaY) (@hthetaFirst)
      (@hthetaFirstIndex) (@hthetaOutsideGamma) (@hgammaNeTheta) (@hAtoZ) (@treeMissingSubset)
      (@hgammaMissingZ) (@hbetaMissingZ) (@hchangeElementary) (@hchangeMissing) (@componentSelf)
      (@componentLeaf) (@separateComponents) (@hgammaTerminalDistinct) (@hterminalDisjoint)
      (@hmu2One) (@hgammaFirstMu2) (@hgammaTerminalMu2) (@hfixedThroughY) (@prefixMissing)
      (@firstPreserved) (@firstUnaffected) (@hmissingMu2) (@missingTransport)
private theorem helper_continuation_2578.{u_1, u_2} :
    helperContinuation2578Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta hvertexMissing d j hj
      hpathLower hpathUpper R sigma H q A ell X B Y Z D hbetaStored hbetaB hbetaTail
      hthetaMissingY gamma hgammaBeta hgammaA hgammaNeBeta hthetaUnstored' sameStar hAtoT htail
      hcutJstrict fullPrefixEq commonPrefix hYlen hBtoT hYtoT hBtoX hXtoY hYtoZ hZtoT hAtoY
      penultimatePrefixEq hElemZ firstWitness hgammaFirst hbetaFirst hgammaFirstLe hbetaFirstLe
      vertexMemT
  have vertexMemSelf (W : TreeSequence G e0) (i : Fin (W.length + 1)) :
      W.vertex i ∈ TreeSequenceVertexSet W := by
    as_aux_lemma =>
      clear * - W i
      simp [TreeSequenceVertexSet]
  have treeMissingIntro (rho : PartialEdgeColoring E k) (W : TreeSequence G e0)
      (v : V) (c : Fin k) (hv : v ∈ TreeSequenceVertexSet W)
      (hc : c ∈ MissingColors G rho v) : c ∈ TreeMissingColors rho W := by
    as_aux_lemma =>
      clear * - rho W v c hv hc
      exact Finset.mem_biUnion.mpr ⟨v, hv, hc⟩
  have hthetaY : d.theta ∈ TreeMissingColors sigma Y := by
    exact helper_hthetaY_789 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
        (@alpha) (@beta) (@d) (@j) (@hthetaMissingY) (@vertexMemSelf) (@treeMissingIntro)
  have hthetaFirst : d.theta ∈ MissingColors G sigma
        (T.vertex (HierarchyFirstMissingPosition sigma T d.theta)) ∧
      (HierarchyFirstMissingPosition sigma T d.theta).val ≤ Y.length := by
    as_aux_lemma =>
      clear * - G T sigma Y d hYtoT hthetaY firstWitness
      clear_value Y
      exact firstWitness sigma Y hYtoT d.theta hthetaY
  have hthetaFirstIndex :=
    helper_hthetaFirstIndex_397 G k e0 input T phi ett base C ctx P alpha beta d j hthetaMissingY
        hYtoT hYtoZ hZtoT hElemZ
        vertexMemT hthetaFirst
  have hthetaOutsideGamma : d.theta ∉ D.biUnion (R.counterexample.good.gamma q) := by
    simpa [R, H, q, D] using d.thetaOutsideGamma
  have hgammaInGammaUnion : gamma ∈ D.biUnion (R.counterexample.good.gamma q) :=
    Finset.mem_biUnion.mpr ⟨beta, hbetaStored, hgammaBeta⟩
  have hgammaNeTheta : gamma ≠ d.theta := by
    intro heq
    exact hthetaOutsideGamma (heq ▸ hgammaInGammaUnion)
  have hbetaNotA : beta ∉ TreeMissingColors sigma A :=
    (Finset.mem_sdiff.mp hbetaStored).2
  have hbetaAfterA : A.length < (HierarchyFirstMissingPosition sigma T beta).val := by
    exact helper_hbetaAfterA_813 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
        (@P) (@alpha) (@beta) (@d) (@j) (@hAtoT) (@hbetaFirst) (@vertexMemT) (@treeMissingIntro)
        (@hbetaNotA)
  have hgammaBeforeBeta :
      (HierarchyFirstMissingPosition sigma T gamma).val <
        (HierarchyFirstMissingPosition sigma T beta).val :=
    lt_of_le_of_lt hgammaFirstLe hbetaAfterA
  have horderGammaBeta : TreeVertexOrder T
      (T.vertex (HierarchyFirstMissingPosition sigma T gamma))
      (T.vertex (HierarchyFirstMissingPosition sigma T beta)) :=
    ⟨HierarchyFirstMissingPosition sigma T gamma,
      HierarchyFirstMissingPosition sigma T beta, rfl, rfl, hgammaBeforeBeta⟩
  have hBcutoff : B.length ≤ A.length + j := by
    change (HierarchyFullTailPrefix C (j - 2)).length ≤ A.length + j
    rw [fullPrefixEq]
    simp only [TreeSequencePrefix]
    exact le_trans (min_le_left _ _) (Nat.add_le_add_left (Nat.sub_le j 2) _)
  have hgammaUnusedBeforeBeta :
      gamma ∉ (Finset.univ.filter fun c =>
        ∃ t : Fin T.length,
          A.length ≤ t.val ∧
            t.val < (HierarchyFirstMissingPosition sigma T beta).val ∧
              sigma (T.edge t) = some c) := by
    exact helper_hgammaUnusedBeforeBeta_834 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base)
        (@C) (@ctx) (@P) (@alpha) (@beta) (@d) (@j) (@hbetaTail) (@gamma) (@hgammaBeta)
        (@hbetaFirstLe) (@hBcutoff)
  have horderedUnusedGammaBeta :
      (gamma ∉ TreeMissingColors sigma A ∨ beta ∉ TreeMissingColors sigma A) →
        TreeVertexOrder T
            (T.vertex (HierarchyFirstMissingPosition sigma T gamma))
            (T.vertex (HierarchyFirstMissingPosition sigma T beta)) ∧
          gamma ∉ (Finset.univ.filter fun c =>
            ∃ t : Fin T.length,
              A.length ≤ t.val ∧
                t.val < (HierarchyFirstMissingPosition sigma T beta).val ∧
                  sigma (T.edge t) = some c) := by
    intro _
    exact ⟨horderGammaBeta, hgammaUnusedBeforeBeta⟩
  have hAtoZ : TreeSequenceInitialSegment A Z :=
    commonPrefix hAtoT hZtoT (hAtoY.1.trans hYtoZ.1)
  have hBtoZ : TreeSequenceInitialSegment B Z :=
    commonPrefix hBtoT hZtoT (hBtoX.1.trans (hXtoY.1.trans hYtoZ.1))
  have treeMissingSubset {U W : TreeSequence G e0}
      (hUW : TreeSequenceInitialSegment U W) :
      TreeMissingColors sigma U ⊆ TreeMissingColors sigma W := by
    exact @helper_treeMissingSubset_868 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
        (@alpha) (@beta) (@d) (@U) (@W) (@hUW)
  have hgammaMissingZ : gamma ∈ TreeMissingColors sigma Z :=
    treeMissingSubset hAtoZ hgammaA
  have hbetaMissingZ : beta ∈ TreeMissingColors sigma Z :=
    treeMissingSubset hBtoZ hbetaB
  have htailSame : HierarchyFullTailLength R.counterexample = ell := by
    change T.length - A.length =
      T.length - (HierarchyStarredStage C.hierarchy
        (Fin.last C.hierarchy.dividerCount)).length
    rw [← sameStar]
  have hEll : ell = T.length - A.length := by
    simp [ell, HierarchyFullTailLength, sameStar]
  have hstarR : HierarchyStarredStage R.counterexample.hierarchy
      (Fin.last R.counterexample.hierarchy.dividerCount) = A := rfl
  have hchangeElementary :
      ColoredVertexSetElementary G sigma
        (TreeSequenceVertexSet (HierarchyFullTailPrefix R.counterexample
          (HierarchyFullTailLength R.counterexample - 1))) := by
    rw [penultimatePrefixEq]
    exact hElemZ
  have hchangeMissing : gamma ∈ TreeMissingColors sigma
      (HierarchyFullTailPrefix R.counterexample
        (HierarchyFullTailLength R.counterexample - 1)) ∧
      beta ∈ TreeMissingColors sigma
        (HierarchyFullTailPrefix R.counterexample
          (HierarchyFullTailLength R.counterexample - 1)) := by
    rw [penultimatePrefixEq]
    exact ⟨hgammaMissingZ, hbetaMissingZ⟩
  have firstChange := by
    exact helper_firstChange_904 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
        (@P) (@alpha) (@beta) (@d) (@gamma) (@hgammaNeBeta) (@sameStar) (@hbetaNotA)
        (@horderedUnusedGammaBeta) (@hchangeElementary) (@hchangeMissing)
  have hgammaStageMissing : gamma ∈ HierarchyStageMissingColors H q :=
    (Finset.mem_sdiff.mp
      (R.counterexample.good.avoidance q beta hbetaStored hgammaBeta)).1
  have hApositive (hq : 0 < H.dividerCount) :
      A = H.stage ⟨H.dividerCount, Nat.lt_add_of_pos_right (by decide)⟩ := by
    exact helper_hApositive_927 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
        (@P) (@alpha) (@beta) (@d) (@hq)
  have sameGammaBeta :
      TwoColorComponent G sigma gamma beta
          (Sum.inl (T.vertex (HierarchyFirstMissingPosition sigma T gamma))) =
        TwoColorComponent G sigma gamma beta
          (Sum.inl (T.vertex (HierarchyFirstMissingPosition sigma T beta))) := by
    exact helper_sameGammaBeta_943 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@ctx) (@P) (@alpha) (@beta) (@d) (@gamma) (@hgammaA) (@firstChange)
        (@hgammaStageMissing) (@hApositive)
  have componentSelf (rho : PartialEdgeColoring E k) (a b : Fin k) (v : V) :
      Sum.inl v ∈ TwoColorComponent G rho a b (Sum.inl v) := by
    change (TwoColorIncidenceGraph G rho a b).connectedComponentMk (Sum.inl v) = _
    rfl
  have componentLeaf := TwoColorMissingVertexLeaf G k
  have separateComponents (rho : PartialEdgeColoring E k) (a b : Fin k)
      (hne : a ≠ b) (hp : IsProperEdgeColoring G rho) (u v w : V)
      (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
      (hu : a ∈ MissingColors G rho u) (hv : b ∈ MissingColors G rho v)
      (hw : a ∈ MissingColors G rho w ∨ b ∈ MissingColors G rho w)
      (hsame : TwoColorComponent G rho a b (Sum.inl u) =
        TwoColorComponent G rho a b (Sum.inl v)) :
      Disjoint (TwoColorComponent G rho a b (Sum.inl w))
        (TwoColorComponent G rho a b (Sum.inl u)) := by
    exact TwoColorMissingVerticesDisjoint G k rho a b hne hp u v w huv huw hvw hu hv hw hsame
  have hBlt : B.length < T.length := by
    exact helper_hBlt_1027 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
        (@alpha) (@beta) (@d) (@j) (@hcutJstrict) (@fullPrefixEq)
  have hindicesDistinct :
      T.vertex (HierarchyFirstMissingPosition sigma T gamma) ≠
        T.vertex (HierarchyFirstMissingPosition sigma T beta) := by
    intro he
    have hi := T.vertex_injective he
    have hv := congrArg Fin.val hi
    exact (ne_of_lt hgammaBeforeBeta) hv
  have hgammaTerminalDistinct :
      T.vertex (HierarchyFirstMissingPosition sigma T gamma) ≠
        T.vertex (Fin.last T.length) := by
    exact helper_hgammaTerminalDistinct_1040 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base)
        (@C) (@ctx) (@P) (@alpha) (@beta) (@d) (@j) (@gamma) (@hcutJstrict) (@hgammaFirstLe)
  exact @helper_continuation_2662 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha)
      (@beta) (@hvertexMissing) (@d) (@j) (@hj) (@hpathLower) (@hpathUpper) (@hbetaStored)
      (@hbetaB) (@hbetaTail) (@hthetaMissingY) (@gamma) (@hgammaBeta) (@hgammaA) (@hgammaNeBeta)
      (@hthetaUnstored') (@sameStar) (@hAtoT) (@htail) (@hcutJstrict) (@fullPrefixEq)
      (@commonPrefix) (@hYlen) (@hBtoT) (@hYtoT) (@hBtoX) (@hXtoY) (@hYtoZ) (@hZtoT) (@hAtoY)
      (@penultimatePrefixEq) (@hElemZ) (@firstWitness) (@hgammaFirst) (@hbetaFirst)
      (@hgammaFirstLe) (@hbetaFirstLe) (@vertexMemT) (@vertexMemSelf) (@hthetaY) (@hthetaFirst)
      (@hthetaFirstIndex) (@hthetaOutsideGamma) (@hgammaNeTheta) (@hAtoZ) (@hBtoZ)
      (@treeMissingSubset) (@hgammaMissingZ) (@hbetaMissingZ) (@hchangeElementary)
      (@hchangeMissing) (@sameGammaBeta) (@componentSelf) (@componentLeaf) (@separateComponents)
      (@hBlt) (@hindicesDistinct) (@hgammaTerminalDistinct)
theorem HierarchySituationThreeDisjointThetaUnstoredBetaStoredImpossible
    {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (P : HierarchyReplacementPresentation
      G k e0 input T phi ett base C ctx)
    (alpha beta : Fin k)
    (hpathLower : 2 <= HierarchyPathNumber C.hierarchy)
    (hpathUpper :
      HierarchyPathNumber C.hierarchy < HierarchyFullTailLength C)
    (hvertexMissing : forall (mu : PartialEdgeColoring E k),
      IsProperEdgeColoring G mu -> IsOneEdgeUncolored mu e0 ->
        forall v : V, (MissingColors G mu v).Nonempty)
    (d : HierarchySituationThreeDisjointData
      G k e0 input T phi ett base C ctx P alpha beta)
    (hthetaUnstored :
      let H := d.switched.counterexample.hierarchy
      d.theta ∉ HierarchyStoredColorsAt H (Fin.last H.dividerCount : Fin (H.dividerCount + 1)))
    (hconditionStored :
      let H := d.switched.counterexample.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      beta ∈ HierarchyStoredColorsAt H q ∧
      beta ∈
          TreeMissingColors d.switched.coloring
            (HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy - 2)) ∧
        Disjoint (d.switched.counterexample.good.gamma q beta ∪ { beta })
          ((Finset.univ : Finset (Fin k)).filter fun c =>
            exists r : Fin T.length,
              (HierarchyStarredStage H q).length ≤ r.val ∧
                r.val <
                    (HierarchyStarredStage H q).length + HierarchyPathNumber C.hierarchy ∧
                  d.switched.coloring (T.edge r) = some c)) : False := by
  as_aux_lemma =>
    classical
    generalize hj : HierarchyPathNumber C.hierarchy = j at hpathLower hpathUpper hconditionStored
    let R := d.switched
    let sigma := R.coloring
    let H := R.counterexample.hierarchy
    let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
    let A := HierarchyStarredStage H q
    let ell := HierarchyFullTailLength C
    let X := HierarchyFullTailPrefix C (j - 1)
    let B := HierarchyFullTailPrefix C (j - 2)
    let Y := HierarchyFullTailPrefix C j
    let Z := HierarchyFullTailPrefix C (ell - 1)
    let D := HierarchyStoredColorsAt H q
    have hcondition : beta ∈ D ∧ beta ∈ TreeMissingColors sigma B ∧
        Disjoint (R.counterexample.good.gamma q beta ∪ {beta})
          ((Finset.univ : Finset (Fin k)).filter fun c =>
            ∃ r : Fin T.length, A.length ≤ r.val ∧ r.val < A.length + j ∧
              sigma (T.edge r) = some c) := by
      simpa [R, sigma, H, q, A, B, D, hj] using hconditionStored
    rcases hcondition with ⟨hbetaStored, hbetaB, hbetaTail⟩
    have hthetaMissingY : d.theta ∈ MissingColors G sigma
        (Y.vertex (Fin.last Y.length)) := by
      exact helper_hthetaMissingY_553 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
          (@ctx) (@P) (@alpha) (@beta) (@d) (@j) (@hj)
    obtain ⟨gamma, gamma₂, hgammaNe₂, hgammaPair⟩ :=
      Finset.card_eq_two.mp (R.counterexample.good.twoColors q beta hbetaStored)
    have hgammaBeta : gamma ∈ R.counterexample.good.gamma q beta := by
      rw [hgammaPair]
      simp
    have hgammaA : gamma ∈ TreeMissingColors sigma A :=
      (GoodHierarchyReservedDisjoint R.counterexample.good q).1 beta hbetaStored
        hgammaBeta
    have hgammaNeBeta : gamma ≠ beta := by
      exact helper_hgammaNeBeta_569 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
          (@ctx) (@P) (@alpha) (@beta) (@d) (@hbetaStored) (@gamma) (@hgammaA)
    have hthetaUnstored' : d.theta ∉ D := by
      simpa [R, H, q, D] using hthetaUnstored
    have sameStar : HierarchyStarredStage C.hierarchy
        (Fin.last C.hierarchy.dividerCount) = A := by
      exact helper_sameStar_577 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
          (@P) (@alpha) (@beta) (@d) (@j)
    have starNext (i : Fin (H.dividerCount + 1)) :
        TreeSequenceInitialSegment (HierarchyStarredStage H i) (H.stage i.succ) :=
      Fin.cases H.coreInsideFirst (fun t => H.nested t.succ) i
    have hAtoT : TreeSequenceInitialSegment A T := by
      simpa only [q, Fin.succ_last, H.terminalStage] using starNext q
    have htail : j ≤ T.length - A.length := by
      have h := hpathUpper
      simpa [ell, HierarchyFullTailLength, sameStar] using Nat.le_of_lt h
    have hjLower : 2 ≤ j := hpathLower
    have hjUpper : j < ell := hpathUpper
    have hcutJ : A.length + j ≤ T.length := by
      have hAT := hAtoT.1
      clear * - htail hAT
      clear_value A
      omega
    have hcutJstrict : A.length + j < T.length := by
      exact helper_hcutJstrict_610 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
          (@ctx) (@P) (@alpha) (@beta) (@d) (@j) (@hj) (@sameStar) (@hAtoT) (@hjUpper)
    have fullPrefixEq (m : ℕ) : HierarchyFullTailPrefix C m =
        TreeSequencePrefix T (min (A.length + m) T.length)
          (le_min (A.positive.trans (Nat.le_add_right _ _)) T.positive)
          (Nat.min_le_right _ _) := by
      unfold HierarchyFullTailPrefix
      simp only [sameStar]
    have prefixToTree (m : ℕ) (hm : 1 ≤ m) (hmT : m ≤ T.length) :
        TreeSequenceInitialSegment (TreeSequencePrefix T m hm hmT) T := by
      exact helper_prefixToTree_623 (@G) (@e0) (@T) (@m) (@hm) (@hmT)
    have commonPrefix {U W : TreeSequence G e0}
        (hUT : TreeSequenceInitialSegment U T)
        (hWT : TreeSequenceInitialSegment W T) (hUW : U.length ≤ W.length) :
        TreeSequenceInitialSegment U W := by
      exact helper_commonPrefix_632 (@G) (@e0) (@T) (@hUT) (@hWT) (@hUW)
    have hYlen : Y.length = A.length + j := by
      change (HierarchyFullTailPrefix C j).length = A.length + j
      rw [fullPrefixEq j]
      simp only [TreeSequencePrefix, min_eq_left hcutJ]
    have hBtoT : TreeSequenceInitialSegment B T := by
      change TreeSequenceInitialSegment (HierarchyFullTailPrefix C (j - 2)) T
      rw [fullPrefixEq]
      exact prefixToTree _ (le_min (A.positive.trans (Nat.le_add_right _ _)) T.positive)
        (min_le_right _ _)
    have hXtoT : TreeSequenceInitialSegment X T := by
      change TreeSequenceInitialSegment (HierarchyFullTailPrefix C (j - 1)) T
      rw [fullPrefixEq]
      exact prefixToTree _ (le_min (A.positive.trans (Nat.le_add_right _ _)) T.positive)
        (min_le_right _ _)
    have hYtoT : TreeSequenceInitialSegment Y T := by
      change TreeSequenceInitialSegment (HierarchyFullTailPrefix C j) T
      rw [fullPrefixEq]
      exact prefixToTree _ (le_min (A.positive.trans (Nat.le_add_right _ _)) T.positive)
        (min_le_right _ _)
    have hBtoX : TreeSequenceInitialSegment B X :=
      commonPrefix hBtoT hXtoT (by
        change (HierarchyFullTailPrefix C (j - 2)).length ≤
          (HierarchyFullTailPrefix C (j - 1)).length
        rw [fullPrefixEq (j - 2), fullPrefixEq (j - 1)]
        simp only [TreeSequencePrefix]
        exact min_le_min_right _ (Nat.add_le_add_left (Nat.sub_le_sub_left (by decide) j) _))
    have hXtoY : TreeSequenceInitialSegment X Y :=
      commonPrefix hXtoT hYtoT (by
        change (HierarchyFullTailPrefix C (j - 1)).length ≤
          (HierarchyFullTailPrefix C j).length
        rw [fullPrefixEq (j - 1), fullPrefixEq j]
        simp only [TreeSequencePrefix]
        exact min_le_min_right _ (Nat.add_le_add_left (Nat.sub_le j 1) _))
    have hYtoZ : TreeSequenceInitialSegment Y Z :=
      commonPrefix hYtoT (by
        change TreeSequenceInitialSegment (HierarchyFullTailPrefix C (ell - 1)) T
        rw [fullPrefixEq]
        exact prefixToTree _ (le_min (A.positive.trans (Nat.le_add_right _ _)) T.positive)
          (min_le_right _ _))
        (by
          change (HierarchyFullTailPrefix C j).length ≤
            (HierarchyFullTailPrefix C (ell - 1)).length
          rw [fullPrefixEq j, fullPrefixEq (ell - 1)]
          simp only [TreeSequencePrefix]
          exact min_le_min_right _ (Nat.add_le_add_left (Nat.le_sub_one_of_lt hjUpper) _))
    have hZtoT : TreeSequenceInitialSegment Z T := by
        change TreeSequenceInitialSegment (HierarchyFullTailPrefix C (ell - 1)) T
        rw [fullPrefixEq]
        exact prefixToTree _ (le_min (A.positive.trans (Nat.le_add_right _ _)) T.positive)
          (min_le_right _ _)
    have hAtoY : TreeSequenceInitialSegment A Y :=
      commonPrefix hAtoT hYtoT (by rw [hYlen]; exact Nat.le_add_right _ _)
    have hAtoB : TreeSequenceInitialSegment A B :=
      commonPrefix hAtoT hBtoT (by
        change A.length ≤ (HierarchyFullTailPrefix C (j - 2)).length
        rw [fullPrefixEq]
        simp only [TreeSequencePrefix]
        exact le_min (Nat.le_add_right _ _) hAtoT.1)
    have penultimatePrefixEq : HierarchyFullTailPrefix R.counterexample
        (HierarchyFullTailLength R.counterexample - 1) = Z := by
      simp only [Z, ell, HierarchyFullTailPrefix, HierarchyFullTailLength, sameStar]
      rfl
    have hElemZ : ColoredVertexSetElementary G sigma (TreeSequenceVertexSet Z) := by
      exact helper_hElemZ_717 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
          (@P) (@alpha) (@beta) (@d) (@penultimatePrefixEq)
    have firstWitness (rho : PartialEdgeColoring E k) (W : TreeSequence G e0)
        (hWT : TreeSequenceInitialSegment W T) (c : Fin k)
        (hc : c ∈ TreeMissingColors rho W) :
        c ∈ MissingColors G rho (T.vertex (HierarchyFirstMissingPosition rho T c)) ∧
          (HierarchyFirstMissingPosition rho T c).val ≤ W.length := by
      exact helper_firstWitness_734 (@G) (@k) (@e0) (@T) (@rho) (@W) (@hWT) (@c) (@hc)
    have hgammaFirst := firstWitness sigma A hAtoT gamma hgammaA
    have hbetaFirst := firstWitness sigma B hBtoT beta hbetaB
    have hgammaFirstLe : (HierarchyFirstMissingPosition sigma T gamma).val ≤ A.length :=
      hgammaFirst.2
    have hbetaFirstLe : (HierarchyFirstMissingPosition sigma T beta).val ≤ B.length :=
      hbetaFirst.2
    have vertexMemT (W : TreeSequence G e0) (hWT : TreeSequenceInitialSegment W T)
        (i : Fin (T.length + 1)) (hi : i.val ≤ W.length) :
        T.vertex i ∈ TreeSequenceVertexSet W := by
      exact helper_vertexMemT_768 (@G) (@e0) (@T) (@W) (@hWT) (@i) (@hi)
    exact @helper_continuation_2578 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
        (@alpha) (@beta) (@hvertexMissing) (@d) (@j) (@hj) (@hpathLower) (@hpathUpper)
        (@hbetaStored) (@hbetaB) (@hbetaTail) (@hthetaMissingY) (@gamma) (@hgammaBeta) (@hgammaA)
        (@hgammaNeBeta) (@hthetaUnstored') (@sameStar) (@hAtoT) (@htail) (@hcutJstrict)
        (@fullPrefixEq) (@commonPrefix) (@hYlen) (@hBtoT) (@hYtoT) (@hBtoX) (@hXtoY) (@hYtoZ)
        (@hZtoT) (@hAtoY) (@penultimatePrefixEq) (@hElemZ) (@firstWitness) (@hgammaFirst)
        (@hbetaFirst) (@hgammaFirstLe) (@hbetaFirstLe) (@vertexMemT)
end GoldbergSeymour

end
