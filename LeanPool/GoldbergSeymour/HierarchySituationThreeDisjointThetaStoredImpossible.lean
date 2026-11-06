/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.SharedFacts.DisjointThetaRoutes


public import LeanPool.GoldbergSeymour.SharedFacts.DisjointThetaTransport

public import LeanPool.GoldbergSeymour.SharedFacts.SecondSituationTransport

public import LeanPool.GoldbergSeymour.HierarchyFullTailLength
public import LeanPool.GoldbergSeymour.HierarchySituationThreeDisjointData
public import LeanPool.GoldbergSeymour.HierarchySituationThreeEligibleIndexBound

/-!
# Hierarchy Situation Three Disjoint Theta Stored Impossible

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev helperContinuation2252Conditions.{u_1, u_2} : Prop :=
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
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q; d.theta ∈ D → beta ∈ TreeMissingColors
        sigma B → (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < A.length + j → sigma (T.edge t) ≠ some
        beta) → d.theta ∈ MissingColors G sigma (Y.vertex (Fin.last Y.length)) →
    ∀ gamma ∈ R.counterexample.good.gamma q d.theta, gamma ∈ TreeMissingColors sigma A → gamma ∈
        D.biUnion (R.counterexample.good.gamma q) → gamma ≠ beta → HierarchyStarredStage
        C.hierarchy (Fin.last C.hierarchy.dividerCount) = A → TreeSequenceInitialSegment A T → j ≤
        T.length - A.length → A.length + j < T.length → (
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

private abbrev helperContinuation2327Conditions.{u_1, u_2} : Prop :=
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
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q; d.theta ∈ D → beta ∈ TreeMissingColors
        sigma B → d.theta ∈ MissingColors G sigma (Y.vertex (Fin.last Y.length)) →
    ∀ gamma ∈ R.counterexample.good.gamma q d.theta, gamma ∈ TreeMissingColors sigma A → gamma ≠
        beta → HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) = A →
        TreeSequenceInitialSegment A T → j ≤ T.length - A.length → A.length + j < T.length → (
    ∀ (m : ℕ), HierarchyFullTailPrefix C m = TreeSequencePrefix T (min (A.length + m) T.length) (
    have this : (1 : ℕ) ≤ T.length := T.positive;
    have this_1 : (1 : ℕ) ≤ A.length := A.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤
        min (A.length + m) T.length) ↦
    by omega
    ) (
    have this : (1 : ℕ) ≤ T.length := T.positive;
    have this : (1 : ℕ) ≤ A.length := A.positive; Decidable.byContradiction fun (a : ¬min
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
        sigma (TreeSequenceVertexSet Z) → gamma ∈ MissingColors G sigma (T.vertex
        (HierarchyFirstMissingPosition sigma T gamma)) ∧ (↑(HierarchyFirstMissingPosition sigma T
        gamma) : ℕ) ≤ A.length → (↑(HierarchyFirstMissingPosition sigma T gamma) : ℕ) ≤ A.length →
        (
    ∀ (W : TreeSequence G e0), TreeSequenceInitialSegment W T →
    ∀ (i : Fin (T.length + (1 : ℕ))), (↑i : ℕ) ≤ W.length → T.vertex i ∈ TreeSequenceVertexSet W)
        → (
    ∀ (W : TreeSequence G e0) (i : Fin (W.length + (1 : ℕ))), W.vertex i ∈ TreeSequenceVertexSet
        W) → d.theta ∈ TreeMissingColors sigma Y → d.theta ∈ MissingColors G sigma (T.vertex
        (HierarchyFirstMissingPosition sigma T d.theta)) ∧ (↑(HierarchyFirstMissingPosition sigma
        T d.theta) : ℕ) ≤ Y.length → (↑(HierarchyFirstMissingPosition sigma T d.theta) : ℕ) =
        Y.length → d.theta ∉ D.biUnion (R.counterexample.good.gamma q) → gamma ≠ d.theta → (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < Y.length → sigma (T.edge t) ≠ some
        gamma) → TreeSequenceInitialSegment A Z → (
    ∀ {U W : TreeSequence G e0}, TreeSequenceInitialSegment U W → TreeMissingColors sigma U ⊆
        TreeMissingColors sigma W) → gamma ∈ TreeMissingColors sigma Z → beta ∈ TreeMissingColors
        sigma Z → ColoredVertexSetElementary G sigma (TreeSequenceVertexSet
        (HierarchyFullTailPrefix R.counterexample (HierarchyFullTailLength R.counterexample - (1 :
        ℕ)))) → gamma ∈ TreeMissingColors sigma (HierarchyFullTailPrefix R.counterexample
        (HierarchyFullTailLength R.counterexample - (1 : ℕ))) ∧ beta ∈ TreeMissingColors sigma
        (HierarchyFullTailPrefix R.counterexample (HierarchyFullTailLength R.counterexample - (1 :
        ℕ))) → (
    ∀ (rho : PartialEdgeColoring E k) (a b : Fin k) (v : V), Sum.inl v ∈ TwoColorComponent G rho a
        b (Sum.inl v)) → T.vertex (HierarchyFirstMissingPosition sigma T gamma) ≠ T.vertex
        (Fin.last T.length) → (Disjoint (TwoColorComponent G sigma gamma beta (Sum.inl (T.vertex
        (Fin.last T.length)))) (TwoColorComponent G sigma gamma beta (Sum.inl (T.vertex
        (HierarchyFirstMissingPosition sigma T gamma)))) ∧ TwoColorPathComponent G sigma gamma
        beta (Sum.inl (T.vertex (Fin.last T.length))) ∧
    ∀ x ∈ TreeSequenceVertexSet Z, MissingColors G (TwoColorComponentSwap G sigma gamma beta
        (Sum.inl (T.vertex (Fin.last T.length)))) x = MissingColors G sigma x) → Disjoint
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
    ∀ (W : TreeSequence G e0), TreeSequenceInitialSegment W T →
    ∀ (rho sigma : PartialEdgeColoring E k) (c : Fin k), ColoredVertexSetElementary G rho
        (TreeSequenceVertexSet W) → (
    ∀ v ∈ TreeSequenceVertexSet W, MissingColors G sigma v = MissingColors G rho v) → c ∈
        TreeMissingColors rho W → HierarchyFirstMissingPosition sigma T c =
        HierarchyFirstMissingPosition rho T c) → False

private abbrev helperContinuation3145Conditions.{u_1, u_2} : Prop :=
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
    let Y : TreeSequence G e0 := HierarchyFullTailPrefix C j;
    let Z : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q; d.theta ∈ D →
    ∀ gamma ∈ R.counterexample.good.gamma q d.theta, gamma ∈ TreeMissingColors sigma A → gamma ≠
        beta → HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) = A →
        TreeSequenceInitialSegment A T → A.length + j < T.length → Y.length = A.length + j →
        TreeSequenceInitialSegment Y T → TreeSequenceInitialSegment Y Z →
        TreeSequenceInitialSegment Z T → TreeSequenceInitialSegment A Y → (
    ∀ (W : TreeSequence G e0) (i : Fin (W.length + (1 : ℕ))), W.vertex i ∈ TreeSequenceVertexSet
        W) → d.theta ∈ TreeMissingColors sigma Y → d.theta ∈ MissingColors G sigma (T.vertex
        (HierarchyFirstMissingPosition sigma T d.theta)) ∧ (↑(HierarchyFirstMissingPosition sigma
        T d.theta) : ℕ) ≤ Y.length → d.theta ∉ D.biUnion (R.counterexample.good.gamma q) → gamma ≠
        d.theta → (
    ∀ {U W : TreeSequence G e0}, TreeSequenceInitialSegment U W → TreeMissingColors sigma U ⊆
        TreeMissingColors sigma W) → (
    ∀ (rho : PartialEdgeColoring E k) (a b : Fin k) (v : V), Sum.inl v ∈ TwoColorComponent G rho a
        b (Sum.inl v)) →
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
    have this : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a :
        ¬S.counterexample.hierarchy.dividerCount < S.counterexample.hierarchy.dividerCount + (2 :
        ℕ)) ↦
    by omega
    ⟩ : Fin (S.counterexample.hierarchy.dividerCount + (2 : ℕ)))) ∨
        S.counterexample.hierarchy.dividerCount = (0 : ℕ) ∧ gamma ∈ TreeMissingColors S.coloring
        (S.corresponding.replacementETT.series.data.tree (Fin.last
        S.corresponding.replacementETT.rounds).castSucc)) → TashkinovAugmentationSequence sigma Y
        T → gamma ∈ TreeMissingColors mu2 Y ∧ beta ∈ TreeMissingColors mu2 Y → A.length < Y.length
        →
    ∀ (R1 : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), R1.coloring = mu2
        → (
    ∀ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (m : ℕ),
        HierarchyFullTailPrefix S.counterexample m = HierarchyFullTailPrefix C m) →
    let rho : PartialEdgeColoring E k := R1.coloring; (
    ∀ v ∈ TreeSequenceVertexSet Z, MissingColors G rho v = MissingColors G sigma v) →
        ColoredVertexSetElementary G rho (TreeSequenceVertexSet Z) → HierarchyFirstMissingPosition
        rho T gamma = HierarchyFirstMissingPosition sigma T gamma → HierarchyFirstMissingPosition
        rho T d.theta = HierarchyFirstMissingPosition sigma T d.theta → d.theta ∈ MissingColors G
        rho (Y.vertex (Fin.last Y.length)) → gamma ∈ MissingColors G rho (T.vertex (Fin.last
        T.length)) → (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < Y.length → rho (T.edge t) ≠ some gamma)
        → gamma ∈ TreeMissingColors rho Z ∧ d.theta ∈ TreeMissingColors rho Z → Disjoint
        (TwoColorComponent G rho gamma d.theta (Sum.inl (T.vertex (Fin.last T.length))))
        (TwoColorComponent G rho gamma d.theta (Sum.inl (T.vertex (HierarchyFirstMissingPosition
        sigma T gamma)))) →
    let mu3 : PartialEdgeColoring E k := TwoColorComponentSwap G rho gamma d.theta z;
        TwoColorPathComponent G rho gamma d.theta z → IsOneEdgeUncolored mu3 e0 → (
    ∀ v ∈ TreeSequenceVertexSet Z, MissingColors G mu3 v = MissingColors G rho v) → False

private abbrev helperContinuation2545Conditions.{u_1, u_2} : Prop :=
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
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q; d.theta ∈ D → beta ∈ TreeMissingColors
        sigma B → d.theta ∈ MissingColors G sigma (Y.vertex (Fin.last Y.length)) →
    ∀ gamma ∈ R.counterexample.good.gamma q d.theta, gamma ∈ TreeMissingColors sigma A → gamma ≠
        beta → HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) = A →
        TreeSequenceInitialSegment A T → A.length + j < T.length → (
    ∀ {U W : TreeSequence G e0}, TreeSequenceInitialSegment U T → TreeSequenceInitialSegment W T →
        U.length ≤ W.length → TreeSequenceInitialSegment U W) → Y.length = A.length + j →
        TreeSequenceInitialSegment B T → TreeSequenceInitialSegment Y T →
        TreeSequenceInitialSegment B X → TreeSequenceInitialSegment X Y →
        TreeSequenceInitialSegment Y Z → TreeSequenceInitialSegment Z T →
        TreeSequenceInitialSegment A Y → HierarchyFullTailPrefix R.counterexample
        (HierarchyFullTailLength R.counterexample - (1 : ℕ)) = Z → ColoredVertexSetElementary G
        sigma (TreeSequenceVertexSet Z) → gamma ∈ MissingColors G sigma (T.vertex
        (HierarchyFirstMissingPosition sigma T gamma)) ∧ (↑(HierarchyFirstMissingPosition sigma T
        gamma) : ℕ) ≤ A.length → (↑(HierarchyFirstMissingPosition sigma T gamma) : ℕ) ≤ A.length →
        (
    ∀ (W : TreeSequence G e0), TreeSequenceInitialSegment W T →
    ∀ (i : Fin (T.length + (1 : ℕ))), (↑i : ℕ) ≤ W.length → T.vertex i ∈ TreeSequenceVertexSet W)
        → (
    ∀ (W : TreeSequence G e0) (i : Fin (W.length + (1 : ℕ))), W.vertex i ∈ TreeSequenceVertexSet
        W) → d.theta ∈ TreeMissingColors sigma Y → d.theta ∈ MissingColors G sigma (T.vertex
        (HierarchyFirstMissingPosition sigma T d.theta)) ∧ (↑(HierarchyFirstMissingPosition sigma
        T d.theta) : ℕ) ≤ Y.length → (↑(HierarchyFirstMissingPosition sigma T d.theta) : ℕ) =
        Y.length → d.theta ∉ D.biUnion (R.counterexample.good.gamma q) → gamma ≠ d.theta → (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < Y.length → sigma (T.edge t) ≠ some
        gamma) → TreeSequenceInitialSegment A Z → (
    ∀ {U W : TreeSequence G e0}, TreeSequenceInitialSegment U W → TreeMissingColors sigma U ⊆
        TreeMissingColors sigma W) → gamma ∈ TreeMissingColors sigma Z → beta ∈ TreeMissingColors
        sigma Z → ColoredVertexSetElementary G sigma (TreeSequenceVertexSet
        (HierarchyFullTailPrefix R.counterexample (HierarchyFullTailLength R.counterexample - (1 :
        ℕ)))) → gamma ∈ TreeMissingColors sigma (HierarchyFullTailPrefix R.counterexample
        (HierarchyFullTailLength R.counterexample - (1 : ℕ))) ∧ beta ∈ TreeMissingColors sigma
        (HierarchyFullTailPrefix R.counterexample (HierarchyFullTailLength R.counterexample - (1 :
        ℕ))) → (
    ∀ (rho : PartialEdgeColoring E k) (a b : Fin k) (v : V), Sum.inl v ∈ TwoColorComponent G rho a
        b (Sum.inl v)) → T.vertex (HierarchyFirstMissingPosition sigma T gamma) ≠ T.vertex
        (Fin.last T.length) → (Disjoint (TwoColorComponent G sigma gamma beta (Sum.inl (T.vertex
        (Fin.last T.length)))) (TwoColorComponent G sigma gamma beta (Sum.inl (T.vertex
        (HierarchyFirstMissingPosition sigma T gamma)))) ∧ TwoColorPathComponent G sigma gamma
        beta (Sum.inl (T.vertex (Fin.last T.length))) ∧
    ∀ x ∈ TreeSequenceVertexSet Z, MissingColors G (TwoColorComponentSwap G sigma gamma beta
        (Sum.inl (T.vertex (Fin.last T.length)))) x = MissingColors G sigma x) → Disjoint
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
        TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence nu seed Y) → (
    ∀ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), (0 : ℕ) <
        S.counterexample.hierarchy.dividerCount ∧ gamma ∈ TreeMissingColors S.coloring
        (S.counterexample.hierarchy.stage (⟨S.counterexample.hierarchy.dividerCount,
    by
         have :=
          GoldbergSeymour.TreeSequence.positive
           T
         omega
    ⟩ : Fin (S.counterexample.hierarchy.dividerCount + (2 : ℕ)))) ∨
        S.counterexample.hierarchy.dividerCount = (0 : ℕ) ∧ gamma ∈ TreeMissingColors S.coloring
        (S.corresponding.replacementETT.series.data.tree (Fin.last
        S.corresponding.replacementETT.rounds).castSucc)) → False

private abbrev helperContinuation3542Conditions.{u_1, u_2} : Prop :=
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
    ∀ (hthetaStored' : d.theta ∈ D) (hbetaB : beta ∈ TreeMissingColors sigma B) (hbetaUnused :
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < A.length + j → sigma (T.edge t) ≠ some
        beta) (hthetaMissingY : d.theta ∈ MissingColors G sigma (Y.vertex (Fin.last Y.length)))
        (gamma : Fin k) (hgammaTheta : gamma ∈ R.counterexample.good.gamma q d.theta) (hgammaA :
        gamma ∈ TreeMissingColors sigma A) (hgammaNeBeta : gamma ≠ beta) (sameStar :
        HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) = A) (hAtoT :
        TreeSequenceInitialSegment A T) (htail : j ≤ T.length - A.length) (hcutJstrict : A.length
        + j < T.length) (fullPrefixEq :
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
        gamma) : ℕ) ≤ A.length) (hbetaFirst : beta ∈ MissingColors G sigma (T.vertex
        (HierarchyFirstMissingPosition sigma T beta)) ∧ (↑(HierarchyFirstMissingPosition sigma T
        beta) : ℕ) ≤ B.length) (hgammaFirstLe : (↑(HierarchyFirstMissingPosition sigma T gamma) :
        ℕ) ≤ A.length) (hbetaFirstLe : (↑(HierarchyFirstMissingPosition sigma T beta) : ℕ) ≤
        B.length) (vertexMemT :
    ∀ (W : TreeSequence G e0), TreeSequenceInitialSegment W T →
    ∀ (i : Fin (T.length + (1 : ℕ))), (↑i : ℕ) ≤ W.length → T.vertex i ∈ TreeSequenceVertexSet W)
        (vertexMemSelf :
    ∀ (W : TreeSequence G e0) (i : Fin (W.length + (1 : ℕ))), W.vertex i ∈ TreeSequenceVertexSet
        W) (hthetaY : d.theta ∈ TreeMissingColors sigma Y) (hthetaFirst : d.theta ∈ MissingColors
        G sigma (T.vertex (HierarchyFirstMissingPosition sigma T d.theta)) ∧
        (↑(HierarchyFirstMissingPosition sigma T d.theta) : ℕ) ≤ Y.length) (hthetaFirstIndex :
        (↑(HierarchyFirstMissingPosition sigma T d.theta) : ℕ) = Y.length) (hthetaOutsideGamma :
        d.theta ∉ D.biUnion (R.counterexample.good.gamma q)) (hgammaNeTheta : gamma ≠ d.theta)
        (hgammaUnused :
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < Y.length → sigma (T.edge t) ≠ some
        gamma) (hAtoZ : TreeSequenceInitialSegment A Z) (hBtoZ : TreeSequenceInitialSegment B Z)
        (treeMissingSubset :
    ∀ {U W : TreeSequence G e0} (hUW : TreeSequenceInitialSegment U W), TreeMissingColors sigma U
        ⊆ TreeMissingColors sigma W) (hgammaMissingZ : gamma ∈ TreeMissingColors sigma Z)
        (hbetaMissingZ : beta ∈ TreeMissingColors sigma Z) (hchangeElementary :
        ColoredVertexSetElementary G sigma (TreeSequenceVertexSet (HierarchyFullTailPrefix
        R.counterexample (HierarchyFullTailLength R.counterexample - (1 : ℕ))))) (hchangeMissing :
        gamma ∈ TreeMissingColors sigma (HierarchyFullTailPrefix R.counterexample
        (HierarchyFullTailLength R.counterexample - (1 : ℕ))) ∧ beta ∈ TreeMissingColors sigma
        (HierarchyFullTailPrefix R.counterexample (HierarchyFullTailLength R.counterexample - (1 :
        ℕ)))) (firstChange :
    let H : TashkinovHierarchy d.switched.corresponding.replacementETT d.switched.replacementBase
        := d.switched.counterexample.hierarchy;
    have q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    have n : Fin (d.switched.corresponding.replacementETT.rounds + (1 : ℕ)) := Fin.last
        d.switched.corresponding.replacementETT.rounds;
    have A : TreeSequence G e0 := HierarchyStarredStage H q;
    have Tnq : TreeSequence G e0 := H.stage (⟨H.dividerCount,
    have this : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a :
        ¬H.dividerCount < H.dividerCount + (2 : ℕ)) ↦
    by
   omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)));
    have Tn : TreeSequence G e0 := d.switched.corresponding.replacementETT.series.data.tree
        n.castSucc;
    have Dn : Finset (Fin k) := TashkinovStoredColors
        d.switched.corresponding.replacementETT.series.data n;
    have Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q;
    have va : V := T.vertex (HierarchyFirstMissingPosition d.switched.coloring T gamma);
    have vb : V := T.vertex (HierarchyFirstMissingPosition d.switched.coloring T beta);
    have sameComponent : Prop := TwoColorComponent G d.switched.coloring gamma beta (Sum.inl va) =
        TwoColorComponent G d.switched.coloring gamma beta (Sum.inl vb); ( (0 : ℕ) <
        H.dividerCount ∧ (gamma ∈ TreeMissingColors d.switched.coloring Tnq ∨ Disjoint (insert
        gamma ({ beta } : Finset (Fin k)) : Finset (Fin k)) Dnq) → sameComponent) ∧ (
        H.dividerCount = (0 : ℕ) ∧ (gamma ∈ TreeMissingColors d.switched.coloring Tn ∨ Disjoint
        (insert gamma ({ beta } : Finset (Fin k)) : Finset (Fin k)) Dn) → sameComponent) ∧ ( gamma
        ∈ TreeMissingColors d.switched.coloring A ∧ TreeColorSetClosed G d.switched.coloring A
        ({ gamma } : Finset (Fin k)) → sameComponent ∧ TreeInterchangeable G A d.switched.coloring
        gamma beta)), False

private theorem helper_hfixed3_1220.{u_1, u_2} :
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
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength C;
    let Y : TreeSequence G e0 := HierarchyFullTailPrefix C j;
    let Z : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
    ∀ (gamma : Fin k), HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) = A →
        TreeSequenceInitialSegment A T → Y.length = A.length + j → TreeSequenceInitialSegment Y T
        → (
    ∀ (W : TreeSequence G e0) (i : Fin (W.length + (1 : ℕ))), W.vertex i ∈ TreeSequenceVertexSet
        W) →
    let z : V ⊕ E := Sum.inl (T.vertex (Fin.last T.length)); (
    ∀ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage S.counterexample.hierarchy (Fin.last
        S.counterexample.hierarchy.dividerCount) = A) → (
    ∀ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyFullTailPrefix S.counterexample (HierarchyFullTailLength S.counterexample - (1 :
        ℕ)) = Z) →
    ∀ (R1 : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), (
    ∀ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (m : ℕ),
        HierarchyFullTailPrefix S.counterexample m = HierarchyFullTailPrefix C m) →
    let rho : PartialEdgeColoring E k := R1.coloring; ColoredVertexSetElementary G rho
        (TreeSequenceVertexSet Z) → d.theta ∈ MissingColors G rho (Y.vertex (Fin.last Y.length)) →
        (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < Y.length → rho (T.edge t) ≠ some gamma)
        →
    let mu3 : PartialEdgeColoring E k := TwoColorComponentSwap G rho gamma d.theta z;
        HierarchyWeaklyStable R1.counterexample.hierarchy (Fin.last
        R1.counterexample.hierarchy.dividerCount) mu3 →
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < Y.length → mu3 (T.edge t) = rho (T.edge
        t) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d j hpathLower hpathUpper R H
      q A ell Y Z gamma sameStar hAtoT hYlen hYtoT vertexMemSelf z sameStarAll samePenultimate R1
      sameFullPrefix rho hElemRho hthetaYRho hgammaUnusedRho mu3 hweak3
  as_aux_lemma =>
    let K := R1.counterexample.hierarchy
    let et := R1.corresponding.replacementETT
    let n := Fin.last et.rounds
    let Tn := et.series.data.tree n.castSucc
    have hpref : HierarchyFullTailPrefix R1.counterexample j = Y :=
      sameFullPrefix R1 j
    have exclusion := HierarchyTailMissingColorExclusion G k e0
      R1.corresponding.replacementInput T rho et R1.replacementBase K
      (by
        change ColoredVertexSetElementary G rho
          (TreeSequenceVertexSet (HierarchyFullTailPrefix R1.counterexample
            (HierarchyFullTailLength R1.counterexample - 1)))
        rw [samePenultimate R1]
        exact hElemRho)
      j ((by decide : 1 ≤ 2).trans hpathLower)
      (by
        change j < T.length - (HierarchyStarredStage R1.counterexample.hierarchy
          (Fin.last R1.counterexample.hierarchy.dividerCount)).length
        rw [sameStarAll R1]
        simpa only [ell, HierarchyFullTailLength, sameStar] using hpathUpper)
      d.theta (by
        change d.theta ∈ MissingColors G rho
          ((HierarchyFullTailPrefix R1.counterexample j).vertex
            (Fin.last (HierarchyFullTailPrefix R1.counterexample j).length))
        rw [hpref]
        exact hthetaYRho)
    intro t hlo hhi
    have hga := hgammaUnusedRho t hlo hhi
    by_cases htheta : rho (T.edge t) = some d.theta
    · let tY : Fin Y.length := ⟨t.val, hhi⟩
      have hcast : Fin.castLE hYtoT.1 tY = t := Fin.ext rfl
      have hc : rho (Y.edge tY) = some d.theta := by
        rw [← hYtoT.2.2 tY, hcast]
        exact htheta
      change ∀ t : Fin (HierarchyFullTailPrefix R1.counterexample j).length,
        (HierarchyStarredStage K (Fin.last K.dividerCount)).length ≤ t.val →
        t.val < (HierarchyStarredStage K (Fin.last K.dividerCount)).length + j →
        rho ((HierarchyFullTailPrefix R1.counterexample j).edge t) = some d.theta →
        K.dividerCount = 0 ∧ R1.replacementBase.core = Tn ∧
          t.val = (HierarchyStarredStage K (Fin.last K.dividerCount)).length ∧
          ∃ f : E,
            TashkinovSeriesStep G k et.rounds e0 R1.corresponding.replacementInput
              et.series.data n ∧
            (et.series.data.kind n = some TashkinovExtensionKind.SE ∨
              et.series.data.kind n = some TashkinovExtensionKind.RE) ∧
            et.series.data.connectingEdges n = {f} ∧
            (HierarchyFullTailPrefix R1.counterexample j).edge t = f ∧
            rho f = some d.theta ∧ d.theta ∈ TashkinovStoredColors et.series.data n
        at exclusion
      rw [hpref, sameStarAll R1] at exclusion
      obtain ⟨hz, hcore, hpos, f, hcert, hkind, hedges, hedge, hfc, hraw⟩ :=
        exclusion tY hlo (hYlen ▸ hhi) hc
      have hzero : (Fin.last K.dividerCount : Fin (K.dividerCount + 1)) = 0 :=
        Fin.ext hz
      have hTnA : Tn = A := by
        have hs := sameStarAll R1
        change HierarchyStarredStage K (Fin.last K.dividerCount) = A at hs
        rw [hzero] at hs
        change R1.replacementBase.core = A at hs
        exact hcore.symm.trans hs
      have hincident : TreeIncidentEdge Tn (T.edge t) := by
        rw [hTnA]
        obtain ⟨i, hi⟩ := T.attaches t
        let iA : Fin (A.length + 1) := ⟨i.val, by
          have hiLt := i.isLt
          change t.val = A.length at hpos
          omega⟩
        have hiEq : Fin.castLE (Nat.succ_le_succ hAtoT.1) iA =
            Fin.castLT i (Nat.lt_trans i.isLt (Nat.succ_lt_succ t.isLt)) :=
          Fin.ext rfl
        refine ⟨A.vertex iA, vertexMemSelf A iA, ?_⟩
        rw [← hAtoT.2.1 iA, hiEq, Incident, hi]
        exact Sym2.mem_mk_right _ _
      have hw := hweak3
      change HierarchyWeaklyStable K (Fin.last K.dividerCount) mu3 at hw
      rw [hzero] at hw
      change (if et.series.data.kind n = some TashkinovExtensionKind.PE then
        CombinedStableColoring Tn R1.replacementBase.closure
          (TashkinovStoredColors et.series.data n) rho mu3
        else StableColoring Tn (TashkinovStoredColors et.series.data n) rho mu3) at hw
      have hstable : StableColoring Tn (TashkinovStoredColors et.series.data n)
          rho mu3 := by
        split_ifs at hw with hp
        · exact hw.1
        · exact hw
      exact hstable.1 _ hincident
        ⟨d.theta, Finset.mem_union_right _ hraw, htheta⟩
    · simp only [mu3, TwoColorComponentSwap, hga, htheta, ite_false, ite_self]

private theorem helper_caseGamma_1171.{u_1, u_2} :
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
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q; d.theta ∈ D →
    ∀ gamma ∈ R.counterexample.good.gamma q d.theta, (
    ∀ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), D =
        HierarchyStoredColorsAt S.counterexample.hierarchy (Fin.last
        S.counterexample.hierarchy.dividerCount) ∧
    ∀ eta ∈ D, R.counterexample.good.gamma q eta = S.counterexample.good.gamma (Fin.last
        S.counterexample.hierarchy.dividerCount) eta) →
    ∀ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), (0 : ℕ) <
        S.counterexample.hierarchy.dividerCount ∧ gamma ∈ TreeMissingColors S.coloring
        (S.counterexample.hierarchy.stage (⟨S.counterexample.hierarchy.dividerCount,
        Nat.lt_add_of_pos_right (of_decide_eq_true (id (Eq.refl true)))⟩ : Fin
        (S.counterexample.hierarchy.dividerCount + (2 : ℕ)))) ∨
        S.counterexample.hierarchy.dividerCount = (0 : ℕ) ∧ gamma ∈ TreeMissingColors S.coloring
        (S.corresponding.replacementETT.series.data.tree (Fin.last
        S.corresponding.replacementETT.rounds).castSucc) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d R H q D hthetaStored' gamma
      hgammaTheta sameLast S
  as_aux_lemma =>
    have hs : d.theta ∈ HierarchyStoredColorsAt S.counterexample.hierarchy
        (Fin.last S.counterexample.hierarchy.dividerCount) := (sameLast S).1 ▸ hthetaStored'
    have hg : gamma ∈ S.counterexample.good.gamma
        (Fin.last S.counterexample.hierarchy.dividerCount) d.theta :=
      (sameLast S).2 d.theta hthetaStored' ▸ hgammaTheta
    have hm := (Finset.mem_sdiff.mp (S.counterexample.good.avoidance _ d.theta hs hg)).1
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

private theorem helper_hbetaUnused_658.{u_1, u_2} :
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
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let _ : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ));
    let _ : Finset (Fin k) := HierarchyStoredColorsAt H q;
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < A.length + j → sigma (T.edge t) ≠ some
        beta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d j hj R sigma H q A B D
  as_aux_lemma =>
    have hc := d.conditionNine
    rw [hj] at hc
    change (beta ∉ _ ∧ beta ∉ _ ∧ beta ∉ _ ∧ beta ∉ D) ∨
      (beta ∈ D ∧ beta ∈ TreeMissingColors sigma B ∧
        Disjoint (R.counterexample.good.gamma q beta ∪ {beta})
          (Finset.univ.filter fun c => ∃ t : Fin T.length,
            A.length ≤ t.val ∧ t.val < A.length + j ∧
              sigma (T.edge t) = some c)) at hc
    intro t hlo hhi he
    have hm : beta ∈ (Finset.univ.filter fun c => ∃ t : Fin T.length,
        A.length ≤ t.val ∧ t.val < A.length + j ∧ sigma (T.edge t) = some c) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, hlo, hhi, he⟩
    rcases hc with hc | hc
    · exact hc.2.1 hm
    · exact Finset.disjoint_left.mp hc.2.2 (by simp) hm

private theorem helper_hgammaUnused_907.{u_1, u_2} :
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
    let Y : TreeSequence G e0 := HierarchyFullTailPrefix C j;
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q; d.theta ∈ D →
    ∀ gamma ∈ R.counterexample.good.gamma q d.theta, (↑(HierarchyFirstMissingPosition sigma T
        d.theta) : ℕ) = Y.length →
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < Y.length → sigma (T.edge t) ≠ some
        gamma := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d j R sigma H q A Y D
      hthetaStored' gamma hgammaTheta hthetaFirstIndex
  as_aux_lemma =>
    have havoid : gamma ∉ HierarchySegmentColors H q d.theta :=
      (Finset.mem_sdiff.mp
        (R.counterexample.good.avoidance q d.theta hthetaStored' hgammaTheta)).2
    have hterminal : H.stage q.succ = T := by
      simpa only [q, Fin.succ_last] using H.terminalStage
    unfold HierarchySegmentColors at havoid
    dsimp only at havoid
    rw [hterminal, hthetaFirstIndex] at havoid
    intro t hlo hhi hc
    exact havoid (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, t, hlo, Nat.lt_min.mpr ⟨hhi, t.isLt⟩, hc⟩)

private theorem helper_horderedUnusedGammaBeta_921.{u_1, u_2} :
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
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ));
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ));
    let Y : TreeSequence G e0 := HierarchyFullTailPrefix C j;
    ∀ gamma ∈ TreeMissingColors sigma A, TreeSequenceInitialSegment A T →
        TreeSequenceInitialSegment B X → TreeSequenceInitialSegment X Y → beta ∈ MissingColors G
        sigma (T.vertex (HierarchyFirstMissingPosition sigma T beta)) ∧
        (↑(HierarchyFirstMissingPosition sigma T beta) : ℕ) ≤ B.length →
        (↑(HierarchyFirstMissingPosition sigma T gamma) : ℕ) ≤ A.length →
        (↑(HierarchyFirstMissingPosition sigma T beta) : ℕ) ≤ B.length → (
    ∀ (W : TreeSequence G e0), TreeSequenceInitialSegment W T →
    ∀ (i : Fin (T.length + (1 : ℕ))), (↑i : ℕ) ≤ W.length → T.vertex i ∈ TreeSequenceVertexSet W)
        → (
    ∀ (rho : PartialEdgeColoring E k) (W : TreeSequence G e0) (v : V) (c : Fin k), v ∈
        TreeSequenceVertexSet W → c ∈ MissingColors G rho v → c ∈ TreeMissingColors rho W) → (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < Y.length → sigma (T.edge t) ≠ some
        gamma) → gamma ∉ TreeMissingColors sigma A ∨ beta ∉ TreeMissingColors sigma A →
        TreeVertexOrder T (T.vertex (HierarchyFirstMissingPosition sigma T gamma)) (T.vertex
        (HierarchyFirstMissingPosition sigma T beta)) ∧ gamma ∉ ({c : Fin k |
    ∃ (t : Fin T.length), A.length ≤ (↑t : ℕ) ∧ (↑t : ℕ) < (↑(HierarchyFirstMissingPosition sigma
        T beta) : ℕ) ∧ sigma (T.edge t) = some c} : Finset (Fin k)) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d j R sigma H q A X B Y gamma
      hgammaA hAtoT hBtoX hXtoY hbetaFirst hgammaFirstLe hbetaFirstLe vertexMemT treeMissingIntro
      hgammaUnused
  as_aux_lemma =>
    intro h
    rcases h with h | h
    · exact (h hgammaA).elim
    · have hafter : A.length < (HierarchyFirstMissingPosition sigma T beta).val := by
        by_contra hh
        have hb := vertexMemT A hAtoT (HierarchyFirstMissingPosition sigma T beta)
          (Nat.le_of_not_gt hh)
        exact h (treeMissingIntro sigma A _ beta hb hbetaFirst.1)
      refine ⟨⟨_, _, rfl, rfl, hgammaFirstLe.trans_lt hafter⟩, ?_⟩
      intro hc
      obtain ⟨_, t, hlo, hhi, he⟩ := Finset.mem_filter.mp hc
      exact hgammaUnused t hlo
        (hhi.trans_le (hbetaFirstLe.trans (hBtoX.1.trans hXtoY.1))) he

private theorem helper_hgammaTerminalDistinct_1048.{u_1, u_2} :
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
  have hv := congrArg Fin.val (T.vertex_injective he)
  simp only [Fin.val_last] at hv
  have hlt : A.length < T.length := (Nat.le_add_right A.length j).trans_lt hcutJstrict
  exact Nat.ne_of_lt (hgammaFirstLe.trans_lt hlt) hv

private theorem helper_hbetaTerminalDistinct_1056.{u_1, u_2} :
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
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ));
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ));
    let Y : TreeSequence G e0 := HierarchyFullTailPrefix C j; A.length + j < T.length → Y.length =
        A.length + j → TreeSequenceInitialSegment B X → TreeSequenceInitialSegment X Y →
        (↑(HierarchyFirstMissingPosition sigma T beta) : ℕ) ≤ B.length → T.vertex
        (HierarchyFirstMissingPosition sigma T beta) ≠ T.vertex (Fin.last T.length) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d j R sigma H q A X B Y
      hcutJstrict hYlen hBtoX hXtoY hbetaFirstLe he
  have hv := congrArg Fin.val (T.vertex_injective he)
  simp only [Fin.val_last] at hv
  have hlt : Y.length < T.length := hYlen.symm ▸ hcutJstrict
  exact Nat.ne_of_lt
    ((hbetaFirstLe.trans (hBtoX.1.trans hXtoY.1)).trans_lt hlt) hv

private theorem helper_hfixedThroughY_1130.{u_1, u_2} :
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
    let Y : TreeSequence G e0 := HierarchyFullTailPrefix C j; (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < A.length + j → sigma (T.edge t) ≠ some
        beta) →
    ∀ (gamma : Fin k), Y.length = A.length + j → (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < Y.length → sigma (T.edge t) ≠ some
        gamma) →
    let z : V ⊕ E := Sum.inl (T.vertex (Fin.last T.length));
    let mu2 : PartialEdgeColoring E k := TwoColorComponentSwap G sigma gamma beta z;
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < A.length + j → mu2 (T.edge t) = sigma
        (T.edge t) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d j R sigma H q A Y
      hbetaUnused gamma hYlen hgammaUnused z mu2
  as_aux_lemma =>
    intro t hlo hhi
    have hga := hgammaUnused t hlo (hYlen.symm ▸ hhi)
    have hbe := hbetaUnused t hlo hhi
    simp only [mu2, TwoColorComponentSwap, hga, hbe, ite_false, ite_self]

private theorem helper_hgammaCutoff_1202.{u_1, u_2} :
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
    let Y : TreeSequence G e0 := HierarchyFullTailPrefix C j;
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q; d.theta ∈ D →
    ∀ gamma ∈ R.counterexample.good.gamma q d.theta, d.theta ∈ MissingColors G sigma (T.vertex
        (HierarchyFirstMissingPosition sigma T d.theta)) ∧ (↑(HierarchyFirstMissingPosition sigma
        T d.theta) : ℕ) ≤ Y.length →
    ∀ eta ∈ D, gamma ∈ R.counterexample.good.gamma q eta ∨ beta ∈ R.counterexample.good.gamma q
        eta → (↑(HierarchyFirstMissingPosition sigma T eta) : ℕ) ≤ Y.length := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d j R sigma H q Y D
      hthetaStored' gamma hgammaTheta hthetaFirst eta heta hmem
  have he : eta = d.theta := by
    by_contra hne
    rcases hmem with hg | hb
    · exact Finset.disjoint_left.mp
        (R.counterexample.good.disjointPairs q eta d.theta heta hthetaStored' hne)
        hg hgammaTheta
    · exact d.betaOutsideGamma (Finset.mem_biUnion.mpr ⟨eta, heta, hb⟩)
  subst eta
  exact hthetaFirst.2

private theorem helper_hstored3_1568.{u_1, u_2} :
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
    ∀ gamma ∈ TreeMissingColors sigma A, TreeSequenceInitialSegment Z T → gamma ≠ d.theta →
    let z : V ⊕ E := Sum.inl (T.vertex (Fin.last T.length)); (
    ∀ (W : TreeSequence G e0), TreeSequenceInitialSegment W T →
    ∀ (rho sigma : PartialEdgeColoring E k) (c : Fin k), ColoredVertexSetElementary G rho
        (TreeSequenceVertexSet W) → (
    ∀ v ∈ TreeSequenceVertexSet W, MissingColors G sigma v = MissingColors G rho v) → c ∈
        TreeMissingColors rho W → HierarchyFirstMissingPosition sigma T c =
        HierarchyFirstMissingPosition rho T c) → (
    ∀ (z : V ⊕ E) (rho : PartialEdgeColoring E k) (a b c : Fin k), a ≠ b → IsProperEdgeColoring G
        rho → c ≠ a → c ≠ b → HierarchyFirstMissingPosition (TwoColorComponentSwap G rho a b z) T
        c = HierarchyFirstMissingPosition rho T c) → (
    ∀ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), D =
        HierarchyStoredColorsAt S.counterexample.hierarchy (Fin.last
        S.counterexample.hierarchy.dividerCount) ∧
    ∀ eta ∈ D, R.counterexample.good.gamma q eta = S.counterexample.good.gamma (Fin.last
        S.counterexample.hierarchy.dividerCount) eta) →
    ∀ (R1 : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let rho : PartialEdgeColoring E k := R1.coloring; ColoredVertexSetElementary G rho
        (TreeSequenceVertexSet Z) → gamma ∈ TreeMissingColors rho Z ∧ d.theta ∈ TreeMissingColors
        rho Z →
    let mu3 : PartialEdgeColoring E k := TwoColorComponentSwap G rho gamma d.theta z; (
    ∀ v ∈ TreeSequenceVertexSet Z, MissingColors G mu3 v = MissingColors G rho v) →
    ∀ eta ∈ HierarchyStoredColorsAt R1.counterexample.hierarchy (Fin.last
        R1.counterexample.hierarchy.dividerCount), HierarchyFirstMissingPosition mu3 T eta =
        HierarchyFirstMissingPosition rho T eta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d R sigma H q A ell Z D gamma
      hgammaA hZtoT hgammaNeTheta z firstPreserved firstUnaffected sameLast R1 rho hElemRho
      hpairMissingRho mu3 hmissing3 eta heta
  have hetaD : eta ∈ D := (sameLast R1).1.symm ▸ heta
  have hneGamma : eta ≠ gamma := by
    intro he
    exact (Finset.mem_sdiff.mp hetaD).2 (he.symm ▸ hgammaA)
  by_cases he : eta = d.theta
  · subst eta
    exact firstPreserved Z hZtoT rho mu3 d.theta hElemRho hmissing3 hpairMissingRho.2
  · exact firstUnaffected z rho gamma d.theta eta hgammaNeTheta
      R1.minimumContext.proper hneGamma he

private theorem helper_hgammaCutoff3_1581.{u_1, u_2} :
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
    let Y : TreeSequence G e0 := HierarchyFullTailPrefix C j;
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q; d.theta ∈ D →
    ∀ gamma ∈ R.counterexample.good.gamma q d.theta, d.theta ∈ MissingColors G sigma (T.vertex
        (HierarchyFirstMissingPosition sigma T d.theta)) ∧ (↑(HierarchyFirstMissingPosition sigma
        T d.theta) : ℕ) ≤ Y.length → d.theta ∉ D.biUnion (R.counterexample.good.gamma q) → (
    ∀ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), D =
        HierarchyStoredColorsAt S.counterexample.hierarchy (Fin.last
        S.counterexample.hierarchy.dividerCount) ∧
    ∀ eta ∈ D, R.counterexample.good.gamma q eta = S.counterexample.good.gamma (Fin.last
        S.counterexample.hierarchy.dividerCount) eta) →
    ∀ (R1 : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let rho : PartialEdgeColoring E k := R1.coloring; HierarchyFirstMissingPosition rho T d.theta
        = HierarchyFirstMissingPosition sigma T d.theta →
    ∀ eta ∈ HierarchyStoredColorsAt R1.counterexample.hierarchy (Fin.last
        R1.counterexample.hierarchy.dividerCount), gamma ∈ R1.counterexample.good.gamma (Fin.last
        R1.counterexample.hierarchy.dividerCount) eta ∨ d.theta ∈ R1.counterexample.good.gamma
        (Fin.last R1.counterexample.hierarchy.dividerCount) eta → (↑(HierarchyFirstMissingPosition
        rho T eta) : ℕ) ≤ Y.length := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d j R sigma H q Y D
      hthetaStored' gamma hgammaTheta hthetaFirst hthetaOutsideGamma sameLast R1 rho
      hfirstThetaRho eta heta hmem
  have hetaD : eta ∈ D := (sameLast R1).1.symm ▸ heta
  rw [← (sameLast R1).2 eta hetaD] at hmem
  have he : eta = d.theta := by
    by_contra hne
    rcases hmem with hg | ht
    · exact Finset.disjoint_left.mp
        (R.counterexample.good.disjointPairs q eta d.theta hetaD hthetaStored' hne)
        hg hgammaTheta
    · exact hthetaOutsideGamma (Finset.mem_biUnion.mpr ⟨eta, hetaD, ht⟩)
  subst eta
  rw [hfirstThetaRho]
  exact hthetaFirst.2

private theorem helper_continuation_3145.{u_1, u_2} :
    helperContinuation3145Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta hvertexMissing d j hj
      hpathLower hpathUpper R sigma H q A ell Y Z D hthetaStored' gamma hgammaTheta hgammaA
      hgammaNeBeta sameStar hAtoT hcutJstrict hYlen hYtoT hYtoZ hZtoT hAtoY vertexMemSelf hthetaY
      hthetaFirst hthetaOutsideGamma hgammaNeTheta treeMissingSubset componentSelf z mu2
      firstPreserved firstUnaffected missingTransport sameStarAll samePenultimate sameLast
      routeToY caseGamma hsuffixY hsplitMissing2 hAYstrict R1 hR1 sameFullPrefix rho hmissingRho
      hElemRho hfirstGammaRho hfirstThetaRho hthetaYRho hgammaTerminalRho hgammaUnusedRho
      hpairMissingRho hdisjoint3 mu3 hpath3 hmu3One hmissing3
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
    exact @SharedFacts.DisjointThetaTransport.hweak3 (@V) (@E) inferInstance inferInstance
        inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha) (@beta)
        (@d) (@gamma) (@hgammaNeTheta) (@samePenultimate) (@R1) (@hElemRho) (@hpath3) (@hcase3)
        (@hdisjoint3First) (@hmissingPairCurrent)
  have hfixed3 : ∀ t : Fin T.length, A.length ≤ t.val → t.val < Y.length →
      mu3 (T.edge t) = rho (T.edge t) := by
    exact @helper_hfixed3_1220 V E inferInstance inferInstance inferInstance inferInstance G k e0
        input T phi ett base C ctx P alpha beta d j hpathLower hpathUpper gamma sameStar hAtoT
        hYlen hYtoT vertexMemSelf sameStarAll samePenultimate R1 sameFullPrefix hElemRho
        hthetaYRho hgammaUnusedRho hweak3
  have hstored3 : ∀ eta ∈ HierarchyStoredColorsAt R1.counterexample.hierarchy
        (Fin.last R1.counterexample.hierarchy.dividerCount),
      HierarchyFirstMissingPosition mu3 T eta = HierarchyFirstMissingPosition rho T eta := by
    exact @helper_hstored3_1568 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha) (@beta)
        (@d) (@gamma) (@hgammaA) (@hZtoT) (@hgammaNeTheta) (@firstPreserved) (@firstUnaffected)
        (@sameLast) (@R1) (@hElemRho) (@hpairMissingRho) (@hmissing3)
  have hgammaCutoff3 : ∀ eta ∈ HierarchyStoredColorsAt R1.counterexample.hierarchy
        (Fin.last R1.counterexample.hierarchy.dividerCount),
      (gamma ∈ R1.counterexample.good.gamma (Fin.last R1.counterexample.hierarchy.dividerCount)
          eta ∨
        d.theta ∈ R1.counterexample.good.gamma (Fin.last
            R1.counterexample.hierarchy.dividerCount) eta) →
      (HierarchyFirstMissingPosition rho T eta).val ≤ Y.length := by
    exact @helper_hgammaCutoff3_1581 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
        (@alpha) (@beta) (@d) (@j) (@hthetaStored') (@gamma) (@hgammaTheta) (@hthetaFirst)
        (@hthetaOutsideGamma) (@sameLast) (@R1) (@hfirstThetaRho)
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
    exact @SharedFacts.DisjointThetaTransport.yTerminalDistinct (@V) (@E) inferInstance
        inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
        (@alpha) (@beta) (@d) (@j) (@hcutJstrict) (@hYlen) (@hYtoT)
  let C2 : HierarchyCounterexample bs2 := {
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
  obtain ⟨R2, hR2⟩ := HierarchyReplacementPresentationTrans G k e0 input T phi
    ett base C ctx R1 mu3 corr2 bs2 C2 same2
  have hjEligible : j ∈ HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx
     := by
    exact @SharedFacts.DisjointThetaTransport.hjEligible (@V) (@E) inferInstance inferInstance
        inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
        (@alpha) (@beta) (@d) (@j) (@hpathLower) (@hpathUpper) (@gamma) (@R1)
        (@hthetaTerminalMu3) (@hthetaYMu3) (@R2) (@hR2)
  have hbound := HierarchySituationThreeEligibleIndexBound G k e0 input T phi ett base C ctx
    (by rw [hj]; exact hpathLower) (by rw [hj]; exact hpathUpper) hvertexMissing j hjEligible
  rw [hj] at hbound
  exact Nat.lt_irrefl j hbound

private theorem helper_continuation_2545.{u_1, u_2} :
    helperContinuation2545Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta hvertexMissing d j hj
      hpathLower hpathUpper R sigma H q A ell X B Y Z D hthetaStored' hbetaB hthetaMissingY gamma
      hgammaTheta hgammaA hgammaNeBeta sameStar hAtoT hcutJstrict commonPrefix hYlen hBtoT hYtoT
      hBtoX hXtoY hYtoZ hZtoT hAtoY penultimatePrefixEq hElemZ hgammaFirst hgammaFirstLe
      vertexMemT vertexMemSelf hthetaY hthetaFirst hthetaFirstIndex hthetaOutsideGamma
      hgammaNeTheta hgammaUnused hAtoZ treeMissingSubset hgammaMissingZ hbetaMissingZ
      hchangeElementary hchangeMissing componentSelf hgammaTerminalDistinct separation1
      hterminalDisjoint z mu2 hmu2One hgammaFirstMu2 hgammaTerminalMu2 hfixedThroughY
      firstPreserved firstUnaffected hmissingMu2 missingTransport hstoredMu2 hgammaCutoff
      sameStarAll samePenultimate sameLast routeToY caseGamma
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
  have hpath1 : TwoColorPathComponent G sigma gamma beta z := separation1.2.1
  have hweak1 : HierarchyWeaklyStable H q mu2 := by
    exact @SharedFacts.DisjointThetaTransport.hweak1 (@V) (@E) inferInstance inferInstance
        inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha) (@beta)
        (@d) (@gamma) (@hgammaNeBeta) (@hchangeElementary) (@hchangeMissing) (@hterminalDisjoint)
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
  let C1 : HierarchyCounterexample bs1 := {
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
  obtain ⟨R1, hR1⟩ := HierarchyReplacementPresentationTrans G k e0 input T phi
    ett base C ctx R mu2 corr1 bs1 C1 same1
  have sameFullPrefix (S : HierarchyReplacementPresentation
      G k e0 input T phi ett base C ctx) (m : ℕ) :
      HierarchyFullTailPrefix S.counterexample m = HierarchyFullTailPrefix C m := by
    simp only [HierarchyFullTailPrefix, sameStarAll S, sameStar]
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
    exact hgammaUnused t hlo hhi hc
  have hgammaBeforeTheta : (HierarchyFirstMissingPosition sigma T gamma).val <
      (HierarchyFirstMissingPosition sigma T d.theta).val := by
    rw [hthetaFirstIndex]
    exact hgammaFirstLe.trans_lt hAYstrict
  have hpairMissingRho : gamma ∈ TreeMissingColors rho Z ∧ d.theta ∈ TreeMissingColors rho Z := by
    have he := missingTransport sigma rho hmissingRho Z ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
    rw [he]
    exact ⟨hgammaMissingZ, hthetaMissingZ⟩
  have changeRho := by
    exact @SharedFacts.DisjointThetaRoutes.changeReplacementColoring V E inferInstance inferInstance
        inferInstance inferInstance G k
        e0 input T phi ett base C ctx P alpha beta d j gamma hthetaFirstIndex hgammaNeTheta
        sameStarAll samePenultimate R1 hElemRho hfirstGammaRho hfirstThetaRho hgammaUnusedRho
        hgammaBeforeTheta hpairMissingRho
  have sameGammaTheta : TwoColorComponent G rho gamma d.theta
        (Sum.inl (T.vertex (HierarchyFirstMissingPosition sigma T gamma))) =
      TwoColorComponent G rho gamma d.theta
        (Sum.inl (T.vertex (HierarchyFirstMissingPosition sigma T d.theta))) := by
    have equal : TwoColorComponent G rho gamma d.theta
        (Sum.inl (T.vertex (HierarchyFirstMissingPosition rho T gamma))) =
        TwoColorComponent G rho gamma d.theta
          (Sum.inl (T.vertex (HierarchyFirstMissingPosition rho T d.theta))) :=
      (caseGamma R1).elim
        (fun missing => changeRho.1 ⟨missing.1, Or.inl missing.2⟩)
        (fun missing => changeRho.2.1 ⟨missing.1, Or.inl missing.2⟩)
    rw [hfirstGammaRho, hfirstThetaRho] at equal
    exact equal
  have hgammaThetaDistinct : T.vertex (HierarchyFirstMissingPosition sigma T gamma) ≠
      T.vertex (HierarchyFirstMissingPosition sigma T d.theta) := by
    intro he
    exact ne_of_lt hgammaBeforeTheta (congrArg Fin.val (T.vertex_injective he))
  have hthetaTerminalDistinct : T.vertex (HierarchyFirstMissingPosition sigma T d.theta) ≠
      T.vertex (Fin.last T.length) := by
    apply T.vertex_injective.ne
    intro equal
    have values := congrArg Fin.val equal
    change (HierarchyFirstMissingPosition sigma T d.theta).val = T.length at values
    rw [hthetaFirstIndex] at values
    have strict : Y.length < T.length := hYlen.symm ▸ hcutJstrict
    exact (Nat.ne_of_lt strict) values
  have separation3 := P2905_T2_ElementaryTerminalComponent G rho gamma d.theta
    hgammaNeTheta R1.minimumContext.proper (TreeSequenceVertexSet Z) hElemRho
    (T.vertex (HierarchyFirstMissingPosition sigma T gamma))
    (T.vertex (HierarchyFirstMissingPosition sigma T d.theta))
    (T.vertex (Fin.last T.length))
    (vertexMemT Z hZtoT _ (hgammaFirstLe.trans hAtoZ.1))
    (vertexMemT Z hZtoT _ (hthetaFirst.2.trans hYtoZ.1))
    hgammaTerminalDistinct.symm hthetaTerminalDistinct.symm
    hgammaWitnessRho hthetaWitnessRho (Or.inl hgammaTerminalRho) sameGammaTheta
  have hdisjoint3 := separation3.1
  let mu3 := TwoColorComponentSwap G rho gamma d.theta z
  have hpath3 : TwoColorPathComponent G rho gamma d.theta z := separation3.2.1
  have swapOne (old : PartialEdgeColoring E k) (a b : Fin k)
      (ho : IsOneEdgeUncolored old e0) :
      IsOneEdgeUncolored (TwoColorComponentSwap G old a b z) e0 := by
    exact @SharedFacts.DisjointThetaTransport.swapOne (@V) (@E) (@G) (@k) (@e0) (@T) (@old)
        (@a) (@b) (@ho)
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
      MissingColors G mu3 v = MissingColors G rho v := separation3.2.2
  exact @helper_continuation_3145 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha)
      (@beta) (@hvertexMissing) (@d) (@j) (@hj) (@hpathLower) (@hpathUpper) (@hthetaStored')
      (@gamma) (@hgammaTheta) (@hgammaA) (@hgammaNeBeta) (@sameStar) (@hAtoT) (@hcutJstrict)
      (@hYlen) (@hYtoT) (@hYtoZ) (@hZtoT) (@hAtoY) (@vertexMemSelf) (@hthetaY) (@hthetaFirst)
      (@hthetaOutsideGamma) (@hgammaNeTheta) (@treeMissingSubset) (@componentSelf)
      (@firstPreserved) (@firstUnaffected) (@missingTransport) (@sameStarAll) (@samePenultimate)
      (@sameLast) (@routeToY) (@caseGamma) (@hsuffixY) (@hsplitMissing2) (@hAYstrict) (@R1)
      (@hR1) (@sameFullPrefix) (@hmissingRho) (@hElemRho) (@hfirstGammaRho) (@hfirstThetaRho)
      (@hthetaYRho) (@hgammaTerminalRho) (@hgammaUnusedRho) (@hpairMissingRho) (@hdisjoint3)
      (@hpath3) (@hmu3One) (@hmissing3)
private theorem helper_continuation_2327.{u_1, u_2} :
    helperContinuation2327Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta hvertexMissing d j hj
      hpathLower hpathUpper R sigma H q A ell X B Y Z D hthetaStored' hbetaB hthetaMissingY gamma
      hgammaTheta hgammaA hgammaNeBeta sameStar hAtoT htail hcutJstrict fullPrefixEq commonPrefix
      hYlen hBtoT hYtoT hBtoX hXtoY hYtoZ hZtoT hAtoY penultimatePrefixEq hElemZ hgammaFirst
      hgammaFirstLe vertexMemT vertexMemSelf hthetaY hthetaFirst hthetaFirstIndex
      hthetaOutsideGamma hgammaNeTheta hgammaUnused hAtoZ treeMissingSubset hgammaMissingZ
      hbetaMissingZ hchangeElementary hchangeMissing componentSelf hgammaTerminalDistinct
      separation1 hterminalDisjoint z mu2 hmu2One hgammaFirstMu2 hgammaTerminalMu2 hfixedThroughY
      firstPreserved
  have firstUnaffected (z : Sum V E) (rho : PartialEdgeColoring E k) (a b c : Fin k)
      (hne : a ≠ b) (hp : IsProperEdgeColoring G rho) (hca : c ≠ a) (hcb : c ≠ b) :
      HierarchyFirstMissingPosition (TwoColorComponentSwap G rho a b z) T c =
        HierarchyFirstMissingPosition rho T c := by
    exact @SharedFacts.SecondSituationTransport.firstUnaffected (@V) (@E) inferInstance
        inferInstance (@G) (@k) (@e0) (@T)
        (@z) (@rho) (@a) (@b) (@c) (@hne) (@hp) (@hca) (@hcb)
  have hmissingMu2 : ∀ v ∈ TreeSequenceVertexSet Z,
      MissingColors G mu2 v = MissingColors G sigma v := separation1.2.2
  have missingTransport (old new : PartialEdgeColoring E k)
      (hm : ∀ v ∈ TreeSequenceVertexSet Z,
        MissingColors G new v = MissingColors G old v)
      (W : TreeSequence G e0) (hWZ : TreeSequenceInitialSegment W Z) :
      TreeMissingColors new W = TreeMissingColors old W := by
    exact @SharedFacts.DisjointThetaTransport.missingTransport (@V) (@E) inferInstance
        inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@old) (@new)
        (@hm) (@W) (@hWZ)
  have hstoredMu2 : ∀ eta ∈ D,
      HierarchyFirstMissingPosition mu2 T eta =
        HierarchyFirstMissingPosition sigma T eta := by
    exact @SharedFacts.DisjointThetaTransport.hstoredMu2 (@V) (@E) inferInstance inferInstance
        inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
        (@alpha) (@beta) (@d) (@gamma) (@hgammaA) (@hgammaNeBeta) (@hZtoT) (@hElemZ)
        (@hbetaMissingZ) (@firstPreserved) (@firstUnaffected) (@hmissingMu2)
  have hgammaCutoff : ∀ eta ∈ D,
      (gamma ∈ R.counterexample.good.gamma q eta ∨
        beta ∈ R.counterexample.good.gamma q eta) →
      (HierarchyFirstMissingPosition sigma T eta).val ≤ Y.length := by
    exact @helper_hgammaCutoff_1202 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
        (@alpha) (@beta) (@d) (@j) (@hthetaStored') (@gamma) (@hgammaTheta) (@hthetaFirst)
  have originalStar (S : HierarchyReplacementPresentation
      G k e0 input T phi ett base C ctx) :
      HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) =
        HierarchyStarredStage S.counterexample.hierarchy
          (Fin.last S.counterexample.hierarchy.dividerCount) := by
    exact @SharedFacts.DisjointThetaTransport.originalStar (@V) (@E) inferInstance
        inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@S)
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
    exact @SharedFacts.DisjointThetaTransport.lastData (@V) (@E) inferInstance inferInstance
        inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@S)
  have sameLast (S : HierarchyReplacementPresentation
      G k e0 input T phi ett base C ctx) :
      D = HierarchyStoredColorsAt S.counterexample.hierarchy
        (Fin.last S.counterexample.hierarchy.dividerCount) ∧
      ∀ eta ∈ D, R.counterexample.good.gamma q eta =
        S.counterexample.good.gamma (Fin.last S.counterexample.hierarchy.dividerCount) eta := by
    exact @SharedFacts.DisjointThetaTransport.sameLast (@V) (@E) inferInstance inferInstance
        inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha) (@beta)
        (@d) (@lastData) (@S)
  have weakEdges {input' : PartialEdgeColoring E k}
      (old new : PartialEdgeColoring E k)
      (et : ExtendedTashkinovTree G k e0 input' T old)
      (bs : HierarchyBase et old) (K : TashkinovHierarchy et bs)
      (hw : HierarchyWeaklyStable K (Fin.last K.dividerCount) new)
      (ho : IsOneEdgeUncolored old e0) (hn : IsOneEdgeUncolored new e0) :
      ∀ t : Fin (HierarchyStarredStage K (Fin.last K.dividerCount)).length,
        new ((HierarchyStarredStage K (Fin.last K.dividerCount)).edge t) =
          old ((HierarchyStarredStage K (Fin.last K.dividerCount)).edge t) := by
    exact @SharedFacts.DisjointThetaTransport.weakEdges (@V) (@E) inferInstance inferInstance
        inferInstance
        inferInstance (@G) (@k) (@e0) (@T) (@input') (@old) (@new) (@et) (@bs) (@K) (@hw) (@ho)
        (@hn)
  have hXYlen : Y.length = X.length + 1 := by
    exact @SharedFacts.DisjointThetaTransport.xYlen (@V) (@E) inferInstance inferInstance
        inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha) (@beta)
        (@d) (@j) (@hj) (@hpathLower) (@hAtoT) (@htail) (@fullPrefixEq)
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
    exact @SharedFacts.DisjointThetaRoutes.terminalRouteToPrefix V E inferInstance inferInstance
        inferInstance inferInstance G k e0
        input T phi ett base C ctx P alpha beta d j hj hpathLower hAtoT commonPrefix hYlen hYtoT
        hXtoY hYtoZ hAtoY sameStarAll weakEdges hXYlen S nu hn hw hf hm
  have caseGamma (S : HierarchyReplacementPresentation
      G k e0 input T phi ett base C ctx) :
      (0 < S.counterexample.hierarchy.dividerCount ∧
        gamma ∈ TreeMissingColors S.coloring (S.counterexample.hierarchy.stage
          ⟨S.counterexample.hierarchy.dividerCount, Nat.lt_add_of_pos_right (by decide)⟩)) ∨
      (S.counterexample.hierarchy.dividerCount = 0 ∧
        gamma ∈ TreeMissingColors S.coloring
          (S.corresponding.replacementETT.series.data.tree
            (Fin.last S.corresponding.replacementETT.rounds).castSucc)) := by
    exact @helper_caseGamma_1171 V E inferInstance inferInstance inferInstance inferInstance G k
        e0 input T phi ett base C ctx P alpha beta d hthetaStored' gamma hgammaTheta sameLast S
  exact @helper_continuation_2545 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha)
      (@beta) (@hvertexMissing) (@d) (@j) (@hj) (@hpathLower) (@hpathUpper) (@hthetaStored')
      (@hbetaB) (@hthetaMissingY) (@gamma) (@hgammaTheta) (@hgammaA) (@hgammaNeBeta) (@sameStar)
      (@hAtoT) (@hcutJstrict) (@commonPrefix) (@hYlen) (@hBtoT) (@hYtoT) (@hBtoX) (@hXtoY)
      (@hYtoZ) (@hZtoT) (@hAtoY) (@penultimatePrefixEq) (@hElemZ) (@hgammaFirst) (@hgammaFirstLe)
      (@vertexMemT) (@vertexMemSelf) (@hthetaY) (@hthetaFirst) (@hthetaFirstIndex)
      (@hthetaOutsideGamma) (@hgammaNeTheta) (@hgammaUnused) (@hAtoZ) (@treeMissingSubset)
      (@hgammaMissingZ) (@hbetaMissingZ) (@hchangeElementary) (@hchangeMissing) (@componentSelf)
      (@hgammaTerminalDistinct) (@separation1) (@hterminalDisjoint) (@hmu2One) (@hgammaFirstMu2)
      (@hgammaTerminalMu2) (@hfixedThroughY) (@firstPreserved) (@firstUnaffected) (@hmissingMu2)
      (@missingTransport) (@hstoredMu2) (@hgammaCutoff) (@sameStarAll) (@samePenultimate)
      (@sameLast) (@routeToY) (@caseGamma)
private theorem helper_continuation_3542.{u_1, u_2} :
    helperContinuation3542Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta hvertexMissing d j hj
      hpathLower hpathUpper R sigma H q A ell X B Y Z D hthetaStored' hbetaB hbetaUnused
      hthetaMissingY gamma hgammaTheta hgammaA hgammaNeBeta sameStar hAtoT htail hcutJstrict
      fullPrefixEq commonPrefix hYlen hBtoT hYtoT hBtoX hXtoY hYtoZ hZtoT hAtoY
      penultimatePrefixEq hElemZ firstWitness hgammaFirst hbetaFirst hgammaFirstLe hbetaFirstLe
      vertexMemT vertexMemSelf hthetaY hthetaFirst hthetaFirstIndex hthetaOutsideGamma
      hgammaNeTheta hgammaUnused hAtoZ hBtoZ treeMissingSubset hgammaMissingZ hbetaMissingZ
      hchangeElementary hchangeMissing firstChange
  have hgammaStageMissing : gamma ∈ HierarchyStageMissingColors H q :=
    (Finset.mem_sdiff.mp
      (R.counterexample.good.avoidance q d.theta hthetaStored' hgammaTheta)).1
  have hApositive (hq : 0 < H.dividerCount) :
      A = H.stage ⟨H.dividerCount, Nat.lt_add_of_pos_right (by decide)⟩ := by
    exact @SharedFacts.DisjointThetaTransport.apositive (@V) (@E) inferInstance inferInstance
        inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
        (@alpha) (@beta) (@d) (@hq)
  have sameGammaBeta :
      TwoColorComponent G sigma gamma beta
          (Sum.inl (T.vertex (HierarchyFirstMissingPosition sigma T gamma))) =
        TwoColorComponent G sigma gamma beta
          (Sum.inl (T.vertex (HierarchyFirstMissingPosition sigma T beta))) := by
    exact @SharedFacts.DisjointThetaTransport.sameGammaBeta (@V) (@E) inferInstance
        inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
        (@alpha) (@beta) (@d) (@gamma) (@hgammaA) (@firstChange) (@hgammaStageMissing) (@hApositive)
  have componentSelf (rho : PartialEdgeColoring E k) (a b : Fin k) (v : V) :
      Sum.inl v ∈ TwoColorComponent G rho a b (Sum.inl v) := by rfl
  have hgammaTerminalDistinct :
      T.vertex (HierarchyFirstMissingPosition sigma T gamma) ≠
        T.vertex (Fin.last T.length) := by
    exact @helper_hgammaTerminalDistinct_1048 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
        (@alpha) (@beta) (@d) (@j) (@gamma) (@hcutJstrict) (@hgammaFirstLe)
  have hbetaTerminalDistinct :
      T.vertex (HierarchyFirstMissingPosition sigma T beta) ≠
        T.vertex (Fin.last T.length) := by
    exact @helper_hbetaTerminalDistinct_1056 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
        (@alpha) (@beta) (@d) (@j) (@hcutJstrict) (@hYlen) (@hBtoX) (@hXtoY) (@hbetaFirstLe)
  have separation1 := P2905_T2_ElementaryTerminalComponent G sigma gamma beta
    hgammaNeBeta R.minimumContext.proper (TreeSequenceVertexSet Z) hElemZ
    (T.vertex (HierarchyFirstMissingPosition sigma T gamma))
    (T.vertex (HierarchyFirstMissingPosition sigma T beta))
    (T.vertex (Fin.last T.length))
    (vertexMemT Z hZtoT _ (hgammaFirstLe.trans hAtoZ.1))
    (vertexMemT Z hZtoT _ (hbetaFirstLe.trans hBtoZ.1))
    hgammaTerminalDistinct.symm hbetaTerminalDistinct.symm
    hgammaFirst.1 hbetaFirst.1 (Or.inr d.betaMissingTerminal) sameGammaBeta
  have hterminalDisjoint := separation1.1
  let z : Sum V E := Sum.inl (T.vertex (Fin.last T.length))
  let mu2 := TwoColorComponentSwap G sigma gamma beta z
  have hmu2Proper : IsProperEdgeColoring G mu2 := by
    exact TwoColorComponentSwapProper G sigma gamma beta hgammaNeBeta
      R.minimumContext.proper z
  have hmu2One : IsOneEdgeUncolored mu2 e0 := by
    exact @SharedFacts.DisjointThetaTransport.hmu2One (@V) (@E) inferInstance inferInstance
        inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha) (@beta)
        (@d) (@gamma)
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
    exact @SharedFacts.DisjointThetaTransport.hfirstBetaOutside (@V) (@E) inferInstance
        inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
        (@alpha) (@beta) (@d) (@gamma) (@sameGammaBeta) (@componentSelf) (@hterminalDisjoint)
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
    exact @helper_hfixedThroughY_1130 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
        (@alpha) (@beta) (@d) (@j) (@hbetaUnused) (@gamma) (@hYlen) (@hgammaUnused)
  have firstPreserved (W : TreeSequence G e0)
      (hWT : TreeSequenceInitialSegment W T) (rho sigma : PartialEdgeColoring E k) (c : Fin k)
      (helem : ColoredVertexSetElementary G rho (TreeSequenceVertexSet W))
      (hmiss : ∀ v ∈ TreeSequenceVertexSet W, MissingColors G sigma v = MissingColors G rho v)
      (hc : c ∈ TreeMissingColors rho W) :
      HierarchyFirstMissingPosition sigma T c = HierarchyFirstMissingPosition rho T c := by
    exact @SharedFacts.DisjointThetaTransport.firstPreserved (@V) (@E) inferInstance
        inferInstance (@G) (@k) (@e0) (@T)
        (@j) (@firstWitness) (@W) (@hWT) (@rho) (@sigma) (@c) (@helem) (@hmiss) (@hc)
  exact @helper_continuation_2327 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha)
      (@beta) (@hvertexMissing) (@d) (@j) (@hj) (@hpathLower) (@hpathUpper) (@hthetaStored')
      (@hbetaB) (@hthetaMissingY) (@gamma) (@hgammaTheta) (@hgammaA) (@hgammaNeBeta) (@sameStar)
      (@hAtoT) (@htail) (@hcutJstrict) (@fullPrefixEq) (@commonPrefix) (@hYlen) (@hBtoT) (@hYtoT)
      (@hBtoX) (@hXtoY) (@hYtoZ) (@hZtoT) (@hAtoY) (@penultimatePrefixEq) (@hElemZ)
      (@hgammaFirst) (@hgammaFirstLe) (@vertexMemT) (@vertexMemSelf) (@hthetaY) (@hthetaFirst)
      (@hthetaFirstIndex) (@hthetaOutsideGamma) (@hgammaNeTheta) (@hgammaUnused) (@hAtoZ)
      (@treeMissingSubset) (@hgammaMissingZ) (@hbetaMissingZ) (@hchangeElementary)
      (@hchangeMissing) (@componentSelf) (@hgammaTerminalDistinct) (@separation1)
      (@hterminalDisjoint) (@hmu2One) (@hgammaFirstMu2) (@hgammaTerminalMu2) (@hfixedThroughY)
      (@firstPreserved)

private theorem helper_continuation_2252.{u_1, u_2} :
    helperContinuation2252Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta hvertexMissing d j hj
      hpathLower hpathUpper R sigma H q A ell X B Y Z D hthetaStored' hbetaB hbetaUnused
      hthetaMissingY gamma hgammaTheta hgammaA hgammaInGammaUnion hgammaNeBeta sameStar hAtoT
      htail hcutJstrict fullPrefixEq commonPrefix hYlen hBtoT hYtoT hBtoX hXtoY hYtoZ hZtoT hAtoY
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
    exact @SharedFacts.DisjointThetaTransport.hthetaY (@V) (@E) inferInstance inferInstance
        inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha) (@beta)
        (@d) (@j) (@hthetaMissingY) (@vertexMemSelf) (@treeMissingIntro)
  have hthetaFirst : d.theta ∈ MissingColors G sigma
        (T.vertex (HierarchyFirstMissingPosition sigma T d.theta)) ∧
      (HierarchyFirstMissingPosition sigma T d.theta).val ≤ Y.length := by
    as_aux_lemma =>
      clear * - G T sigma Y d hYtoT hthetaY firstWitness
      clear_value Y
      exact firstWitness sigma Y hYtoT d.theta hthetaY
  have hthetaFirstIndex : (HierarchyFirstMissingPosition sigma T d.theta).val = Y.length := by
    exact @SharedFacts.DisjointThetaTransport.hthetaFirstIndex V E inferInstance inferInstance
        inferInstance
        inferInstance G k e0 input T phi ett base C ctx P alpha beta d j hthetaMissingY hYtoT
        hYtoZ hZtoT hElemZ vertexMemT hthetaFirst
  have hthetaOutsideGamma : d.theta ∉ D.biUnion (R.counterexample.good.gamma q) := by
    simpa [R, H, q, D] using d.thetaOutsideGamma
  have hgammaNeTheta : gamma ≠ d.theta := by
    intro heq
    exact hthetaOutsideGamma (heq ▸ hgammaInGammaUnion)
  have hgammaUnused : ∀ t : Fin T.length, A.length ≤ t.val →
      t.val < Y.length → sigma (T.edge t) ≠ some gamma := by
    exact @helper_hgammaUnused_907 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
        (@alpha) (@beta) (@d) (@j) (@hthetaStored') (@gamma) (@hgammaTheta) (@hthetaFirstIndex)
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
    exact @helper_horderedUnusedGammaBeta_921 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
        (@alpha) (@beta) (@d) (@j) (@gamma) (@hgammaA) (@hAtoT) (@hBtoX) (@hXtoY) (@hbetaFirst)
        (@hgammaFirstLe) (@hbetaFirstLe) (@vertexMemT) (@treeMissingIntro) (@hgammaUnused)
  have hAtoZ : TreeSequenceInitialSegment A Z :=
    commonPrefix hAtoT hZtoT (hAtoY.1.trans hYtoZ.1)
  have hBtoZ : TreeSequenceInitialSegment B Z :=
    commonPrefix hBtoT hZtoT (hBtoX.1.trans (hXtoY.1.trans hYtoZ.1))
  have treeMissingSubset {U W : TreeSequence G e0}
      (hUW : TreeSequenceInitialSegment U W) :
      TreeMissingColors sigma U ⊆ TreeMissingColors sigma W := by
    exact TreeSequenceInitialSegment.treeMissingColors_subset hUW
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
    exact @SharedFacts.DisjointThetaRoutes.firstReplacementChange (@V) (@E) inferInstance
        inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
        (@alpha) (@beta) (@d) (@gamma) (@hgammaNeBeta) (@sameStar) (@horderedUnusedGammaBeta)
        (@hchangeElementary) (@hchangeMissing)
  exact @helper_continuation_3542 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha)
      (@beta) (@hvertexMissing) (@d) (@j) (@hj) (@hpathLower) (@hpathUpper) (@hthetaStored')
      (@hbetaB) (@hbetaUnused) (@hthetaMissingY) (@gamma) (@hgammaTheta) (@hgammaA)
      (@hgammaNeBeta) (@sameStar) (@hAtoT) (@htail) (@hcutJstrict) (@fullPrefixEq)
      (@commonPrefix) (@hYlen) (@hBtoT) (@hYtoT) (@hBtoX) (@hXtoY) (@hYtoZ) (@hZtoT) (@hAtoY)
      (@penultimatePrefixEq) (@hElemZ) (@firstWitness) (@hgammaFirst) (@hbetaFirst)
      (@hgammaFirstLe) (@hbetaFirstLe) (@vertexMemT) (@vertexMemSelf) (@hthetaY) (@hthetaFirst)
      (@hthetaFirstIndex) (@hthetaOutsideGamma) (@hgammaNeTheta) (@hgammaUnused) (@hAtoZ)
      (@hBtoZ) (@treeMissingSubset) (@hgammaMissingZ) (@hbetaMissingZ) (@hchangeElementary)
      (@hchangeMissing) (@firstChange)
theorem HierarchySituationThreeDisjointThetaStoredImpossible
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
    (hthetaStored :
      let H := d.switched.counterexample.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      d.theta ∈ HierarchyStoredColorsAt H q) : False := by
  as_aux_lemma =>
    classical
    generalize hj : HierarchyPathNumber C.hierarchy = j at hpathLower hpathUpper
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
    have hthetaStored' : d.theta ∈ D := hthetaStored
    have hbetaB : beta ∈ TreeMissingColors sigma B := by
      simpa only [B, sigma, R, hj] using d.betaMissingTwoBefore
    have hbetaUnused : ∀ t : Fin T.length, A.length ≤ t.val →
        t.val < A.length + j → sigma (T.edge t) ≠ some beta := by
      exact @helper_hbetaUnused_658 (@V) (@E) inferInstance inferInstance inferInstance
          inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
          (@alpha) (@beta) (@d) (@j) (@hj)
    have hthetaMissingY : d.theta ∈ MissingColors G sigma
        (Y.vertex (Fin.last Y.length)) := by
      exact @SharedFacts.DisjointThetaTransport.hthetaMissingY (@V) (@E) inferInstance
          inferInstance inferInstance
          inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
          (@alpha) (@beta) (@d) (@j) (@hj)
    obtain ⟨gamma, gamma₂, hgammaNe₂, hgammaPair⟩ :=
      Finset.card_eq_two.mp (R.counterexample.good.twoColors q d.theta hthetaStored')
    have hgammaTheta : gamma ∈ R.counterexample.good.gamma q d.theta := by
      rw [hgammaPair]
      simp
    have hgammaA : gamma ∈ TreeMissingColors sigma A :=
      (GoodHierarchyReservedDisjoint R.counterexample.good q).1 d.theta hthetaStored'
        hgammaTheta
    have hgammaInGammaUnion : gamma ∈ D.biUnion (R.counterexample.good.gamma q) :=
      Finset.mem_biUnion.mpr ⟨d.theta, hthetaStored', hgammaTheta⟩
    have hgammaNeBeta : gamma ≠ beta := by
      intro heq
      exact d.betaOutsideGamma (heq ▸ hgammaInGammaUnion)
    have sameStar : HierarchyStarredStage C.hierarchy
        (Fin.last C.hierarchy.dividerCount) = A := by
      exact @SharedFacts.DisjointThetaTransport.sameStar (@V) (@E) inferInstance inferInstance
          inferInstance
          inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
          (@alpha) (@beta) (@d) (@j)
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
      exact @SharedFacts.DisjointThetaTransport.hcutJstrict (@V) (@E) inferInstance
          inferInstance inferInstance
          inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
          (@alpha) (@beta) (@d) (@j) (@hj) (@sameStar) (@hAtoT) (@hjUpper)
    have fullPrefixEq (m : ℕ) : HierarchyFullTailPrefix C m =
        TreeSequencePrefix T (min (A.length + m) T.length)
          (le_min (A.positive.trans (Nat.le_add_right _ _)) T.positive)
          (Nat.min_le_right _ _) := by
      unfold HierarchyFullTailPrefix
      simp only [sameStar]
    have prefixToTree (m : ℕ) (hm : 1 ≤ m) (hmT : m ≤ T.length) :
        TreeSequenceInitialSegment (TreeSequencePrefix T m hm hmT) T := by
      exact @SharedFacts.DisjointThetaTransport.prefixToTree (@V) (@E) (@G) (@e0) (@T) (@m)
          (@hm) (@hmT)
    have commonPrefix {U W : TreeSequence G e0}
        (hUT : TreeSequenceInitialSegment U T)
        (hWT : TreeSequenceInitialSegment W T) (hUW : U.length ≤ W.length) :
        TreeSequenceInitialSegment U W := by
      exact @SharedFacts.DisjointThetaTransport.comparableInitialSegments (@V) (@E) (@G) (@e0)
          (@T) (@U) (@W) (@hUT) (@hWT) (@hUW)
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
      exact @SharedFacts.DisjointThetaTransport.elemZ (@V) (@E) inferInstance inferInstance
          inferInstance inferInstance
          (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha) (@beta)
          (@d) (@penultimatePrefixEq)
    have firstWitness (rho : PartialEdgeColoring E k) (W : TreeSequence G e0)
        (hWT : TreeSequenceInitialSegment W T) (c : Fin k)
        (hc : c ∈ TreeMissingColors rho W) :
        c ∈ MissingColors G rho (T.vertex (HierarchyFirstMissingPosition rho T c)) ∧
          (HierarchyFirstMissingPosition rho T c).val ≤ W.length := by
      exact @SharedFacts.DisjointThetaTransport.firstWitness V E inferInstance inferInstance G
          k e0 T rho W hWT c hc
    have hgammaFirst := firstWitness sigma A hAtoT gamma hgammaA
    have hbetaFirst := firstWitness sigma B hBtoT beta hbetaB
    have hgammaFirstLe : (HierarchyFirstMissingPosition sigma T gamma).val ≤ A.length :=
      hgammaFirst.2
    have hbetaFirstLe : (HierarchyFirstMissingPosition sigma T beta).val ≤ B.length :=
      hbetaFirst.2
    have vertexMemT (W : TreeSequence G e0) (hWT : TreeSequenceInitialSegment W T)
        (i : Fin (T.length + 1)) (hi : i.val ≤ W.length) :
        T.vertex i ∈ TreeSequenceVertexSet W := by
      exact @SharedFacts.DisjointThetaTransport.vertexMemT (@V) (@E) (@G) (@e0) (@T) (@W)
          (@hWT) (@i) (@hi)
    exact @helper_continuation_2252 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
        (@alpha) (@beta) (@hvertexMissing) (@d) (@j) (@hj) (@hpathLower) (@hpathUpper)
        (@hthetaStored') (@hbetaB) (@hbetaUnused) (@hthetaMissingY) (@gamma) (@hgammaTheta)
        (@hgammaA) (@hgammaInGammaUnion) (@hgammaNeBeta) (@sameStar) (@hAtoT) (@htail)
        (@hcutJstrict) (@fullPrefixEq) (@commonPrefix) (@hYlen) (@hBtoT) (@hYtoT) (@hBtoX)
        (@hXtoY) (@hYtoZ) (@hZtoT) (@hAtoY) (@penultimatePrefixEq) (@hElemZ) (@firstWitness)
        (@hgammaFirst) (@hbetaFirst) (@hgammaFirstLe) (@hbetaFirstLe) (@vertexMemT)
end GoldbergSeymour

end
