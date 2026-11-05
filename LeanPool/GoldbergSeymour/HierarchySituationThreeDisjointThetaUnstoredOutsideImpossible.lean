/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyFullTailLength
public import LeanPool.GoldbergSeymour.HierarchySituationThreeDisjointData
public import LeanPool.GoldbergSeymour.HierarchySituationThreeEligibleIndexBound

/-!
# Hierarchy Situation Three Disjoint Theta Unstored Outside Impossible

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev helperContinuation286Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (beta : Fin k), (2 :
        ℕ) ≤ HierarchyPathNumber C.hierarchy → HierarchyPathNumber C.hierarchy <
        HierarchyFullTailLength C → (
    ∀ (mu : PartialEdgeColoring E k), IsProperEdgeColoring G mu → IsOneEdgeUncolored mu e0 →
    ∀ (v : V), (MissingColors G mu v).Nonempty) →
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), (
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let j : ℕ := HierarchyPathNumber C.hierarchy;
    let n : Fin (R.corresponding.replacementETT.rounds + (1 : ℕ)) := Fin.last
        R.corresponding.replacementETT.rounds;
    let Tn : TreeSequence G e0 := R.corresponding.replacementETT.series.data.tree n.castSucc;
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let Gamma : Finset (Fin k) := D.biUnion (R.counterexample.good.gamma q);
    let baseExtraMissing : Finset (Fin k) := (TreeSequenceVertexSet R.replacementBase.core \
        TreeSequenceVertexSet Tn).biUnion fun (v : V) ↦ MissingColors G R.coloring v;
    let tailUsedThroughJ : Finset (Fin k) := ({c : Fin k |
    ∃ (r : Fin T.length), A.length ≤ (↑r : ℕ) ∧ (↑r : ℕ) < A.length + j ∧ R.coloring (T.edge r) =
        some c} : Finset (Fin k)); beta ∉ baseExtraMissing ∧ beta ∉ tailUsedThroughJ ∧ beta ∉
        Gamma ∧ beta ∉ D) → beta ∈ TreeMissingColors R.coloring (HierarchyFullTailPrefix C
        (HierarchyPathNumber C.hierarchy - (2 : ℕ))) → beta ∈ MissingColors G R.coloring (T.vertex
        (Fin.last T.length)) → (
    let j : ℕ := HierarchyPathNumber C.hierarchy;
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ));
        TashkinovAugmentationSequence R.coloring X T) →
    ∀ (theta : Fin k), (
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount; theta ∉
        HierarchyStoredColorsAt H q) → (
    let j : ℕ := HierarchyPathNumber C.hierarchy;
    let Y : TreeSequence G e0 := HierarchyFullTailPrefix C j; theta ∈ MissingColors G R.coloring
        (Y.vertex (Fin.last Y.length))) → (
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let Gamma : Finset (Fin k) := D.biUnion (R.counterexample.good.gamma q); theta ∉ Gamma) → (
    ∀ (psi : PartialEdgeColoring E k) (a b : Fin k), a ≠ b → IsProperEdgeColoring G psi →
    ∀ (B : Finset V), ColoredVertexSetElementary G psi B →
    ∀ (u v w : V), u ∈ B → v ∈ B → u ≠ v → w ≠ u → w ≠ v → a ∈ MissingColors G psi u → b ∈
        MissingColors G psi v → a ∈ MissingColors G psi w ∨ b ∈ MissingColors G psi w →
        TwoColorComponent G psi a b (Sum.inl u) = TwoColorComponent G psi a b (Sum.inl v) →
        Disjoint (TwoColorComponent G psi a b (Sum.inl w)) (TwoColorComponent G psi a b (Sum.inl
        u)) ∧ TwoColorPathComponent G psi a b (Sum.inl w) ∧
    ∀ x ∈ B, MissingColors G (TwoColorComponentSwap G psi a b (Sum.inl w)) x = MissingColors G psi
        x) → (
    ∀ (psi : PartialEdgeColoring E k) (U : TreeSequence G e0) (i : Fin (U.length + (1 : ℕ))),
    ∀ c ∈ MissingColors G psi (U.vertex i), c ∈ MissingColors G psi (U.vertex
        (HierarchyFirstMissingPosition psi U c)) ∧ (↑(HierarchyFirstMissingPosition psi U c) : ℕ)
        ≤ (↑i : ℕ)) →
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let _ : TreeSequence G e0 := HierarchyStarredStage H q; False

private abbrev helperContinuation344Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (beta : Fin k)
        (hpathLower : (2 : ℕ) ≤ HierarchyPathNumber C.hierarchy), HierarchyPathNumber C.hierarchy
        < HierarchyFullTailLength C → (
    ∀ (mu : PartialEdgeColoring E k), IsProperEdgeColoring G mu → IsOneEdgeUncolored mu e0 →
    ∀ (v : V), (MissingColors G mu v).Nonempty) →
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), (
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let j : ℕ := HierarchyPathNumber C.hierarchy;
    let n : Fin (R.corresponding.replacementETT.rounds + (1 : ℕ)) := Fin.last
        R.corresponding.replacementETT.rounds;
    let Tn : TreeSequence G e0 := R.corresponding.replacementETT.series.data.tree n.castSucc;
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let Gamma : Finset (Fin k) := D.biUnion (R.counterexample.good.gamma q);
    let baseExtraMissing : Finset (Fin k) := (TreeSequenceVertexSet R.replacementBase.core \
        TreeSequenceVertexSet Tn).biUnion fun (v : V) ↦ MissingColors G R.coloring v;
    let tailUsedThroughJ : Finset (Fin k) := ({c : Fin k |
    ∃ (r : Fin T.length), A.length ≤ (↑r : ℕ) ∧ (↑r : ℕ) < A.length + j ∧ R.coloring (T.edge r) =
        some c} : Finset (Fin k)); beta ∉ baseExtraMissing ∧ beta ∉ tailUsedThroughJ ∧ beta ∉
        Gamma ∧ beta ∉ D) → beta ∈ TreeMissingColors R.coloring (HierarchyFullTailPrefix C
        (HierarchyPathNumber C.hierarchy - (2 : ℕ))) → beta ∈ MissingColors G R.coloring (T.vertex
        (Fin.last T.length)) → (
    let j : ℕ := HierarchyPathNumber C.hierarchy;
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ));
        TashkinovAugmentationSequence R.coloring X T) →
    ∀ (theta : Fin k), (
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount; theta ∉
        HierarchyStoredColorsAt H q) → (
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let Gamma : Finset (Fin k) := D.biUnion (R.counterexample.good.gamma q); theta ∉ Gamma) → (
    ∀ (psi : PartialEdgeColoring E k) (a b : Fin k), a ≠ b → IsProperEdgeColoring G psi →
    ∀ (B : Finset V), ColoredVertexSetElementary G psi B →
    ∀ (u v w : V), u ∈ B → v ∈ B → u ≠ v → w ≠ u → w ≠ v → a ∈ MissingColors G psi u → b ∈
        MissingColors G psi v → a ∈ MissingColors G psi w ∨ b ∈ MissingColors G psi w →
        TwoColorComponent G psi a b (Sum.inl u) = TwoColorComponent G psi a b (Sum.inl v) →
        Disjoint (TwoColorComponent G psi a b (Sum.inl w)) (TwoColorComponent G psi a b (Sum.inl
        u)) ∧ TwoColorPathComponent G psi a b (Sum.inl w) ∧
    ∀ x ∈ B, MissingColors G (TwoColorComponentSwap G psi a b (Sum.inl w)) x = MissingColors G psi
        x) → (
    ∀ (psi : PartialEdgeColoring E k) (U : TreeSequence G e0) (i : Fin (U.length + (1 : ℕ))),
    ∀ c ∈ MissingColors G psi (U.vertex i), c ∈ MissingColors G psi (U.vertex
        (HierarchyFirstMissingPosition psi U c)) ∧ (↑(HierarchyFirstMissingPosition psi U c) : ℕ)
        ≤ (↑i : ℕ)) →
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let j : ℕ := HierarchyPathNumber C.hierarchy;
    let ell : ℕ := HierarchyFullTailLength R.counterexample;
    ∀ (Y : TreeSequence G e0), HierarchyFullTailPrefix C j = Y →
    let Z : TreeSequence G e0 := HierarchyFullTailPrefix R.counterexample (ell - (1 : ℕ));
    let n : Fin (R.corresponding.replacementETT.rounds + (1 : ℕ)) := Fin.last
        R.corresponding.replacementETT.rounds;
    let Tn : TreeSequence G e0 := R.corresponding.replacementETT.series.data.tree n.castSucc;
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q; HierarchyStarredStage C.hierarchy
        (Fin.last C.hierarchy.dividerCount) = A → TreeSequenceInitialSegment A T →
        HierarchyFullTailLength C = ell → ell = T.length - A.length → j < ell →
    ∀ (hstrict : A.length + j < T.length), Z.length = T.length - (1 : ℕ) →
    ∀ (hYlen : Y.length = A.length + j), TreeSequenceInitialSegment Y T →
        TreeSequenceInitialSegment Z T →
    ∀ (YR : TreeSequence G e0), TreeSequencePrefix T (min (A.length + j) T.length) (
    have hApos : (1 : ℕ) ≤ A.length := A.positive;
    have hTpos : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤
        min (A.length + j) T.length) ↦
    by omega
    ) (
    by
                                have := GoldbergSeymour.TreeSequence.positive T
                                have := GoldbergSeymour.TreeSequence.positive A
                                omega
    ) = YR → YR.length = A.length + j → TreeSequenceInitialSegment YR T → YR.vertex (Fin.last
        YR.length) = Y.vertex (Fin.last Y.length) → (
    ∀ {S U W : TreeSequence G e0}, TreeSequenceInitialSegment S W → TreeSequenceInitialSegment U W
        → S.length ≤ U.length → TreeSequenceInitialSegment S U) → TreeSequenceInitialSegment Y Z →
        ColoredVertexSetElementary G R.coloring (TreeSequenceVertexSet Z) → (
    ∀ (S : TreeSequence G e0) (i : Fin (S.length + (1 : ℕ))), S.vertex i ∈ TreeSequenceVertexSet
        S) → theta ∈ MissingColors G R.coloring (Y.vertex (Fin.last Y.length)) → theta ∈
        MissingColors G R.coloring (YR.vertex (Fin.last YR.length)) → theta ∉ TreeMissingColors
        R.coloring A → False

private abbrev helperContinuation460Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (beta : Fin k), (2 :
        ℕ) ≤ HierarchyPathNumber C.hierarchy → HierarchyPathNumber C.hierarchy <
        HierarchyFullTailLength C → (
    ∀ (mu : PartialEdgeColoring E k), IsProperEdgeColoring G mu → IsOneEdgeUncolored mu e0 →
    ∀ (v : V), (MissingColors G mu v).Nonempty) →
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), beta ∈
        MissingColors G R.coloring (T.vertex (Fin.last T.length)) → (
    let j : ℕ := HierarchyPathNumber C.hierarchy;
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ));
        TashkinovAugmentationSequence R.coloring X T) →
    ∀ (theta : Fin k), (
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount; theta ∉
        HierarchyStoredColorsAt H q) → (
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let Gamma : Finset (Fin k) := D.biUnion (R.counterexample.good.gamma q); theta ∉ Gamma) → (
    ∀ (psi : PartialEdgeColoring E k) (a b : Fin k), a ≠ b → IsProperEdgeColoring G psi →
    ∀ (B : Finset V), ColoredVertexSetElementary G psi B →
    ∀ (u v w : V), u ∈ B → v ∈ B → u ≠ v → w ≠ u → w ≠ v → a ∈ MissingColors G psi u → b ∈
        MissingColors G psi v → a ∈ MissingColors G psi w ∨ b ∈ MissingColors G psi w →
        TwoColorComponent G psi a b (Sum.inl u) = TwoColorComponent G psi a b (Sum.inl v) →
        Disjoint (TwoColorComponent G psi a b (Sum.inl w)) (TwoColorComponent G psi a b (Sum.inl
        u)) ∧ TwoColorPathComponent G psi a b (Sum.inl w) ∧
    ∀ x ∈ B, MissingColors G (TwoColorComponentSwap G psi a b (Sum.inl w)) x = MissingColors G psi
        x) → (
    ∀ (psi : PartialEdgeColoring E k) (U : TreeSequence G e0) (i : Fin (U.length + (1 : ℕ))),
    ∀ c ∈ MissingColors G psi (U.vertex i), c ∈ MissingColors G psi (U.vertex
        (HierarchyFirstMissingPosition psi U c)) ∧ (↑(HierarchyFirstMissingPosition psi U c) : ℕ)
        ≤ (↑i : ℕ)) →
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let j : ℕ := HierarchyPathNumber C.hierarchy;
    let ell : ℕ := HierarchyFullTailLength R.counterexample;
    ∀ (Y : TreeSequence G e0), HierarchyFullTailPrefix C j = Y →
    let Z : TreeSequence G e0 := HierarchyFullTailPrefix R.counterexample (ell - (1 : ℕ));
    let n : Fin (R.corresponding.replacementETT.rounds + (1 : ℕ)) := Fin.last
        R.corresponding.replacementETT.rounds;
    let _ : TreeSequence G e0 := R.corresponding.replacementETT.series.data.tree n.castSucc;
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q; HierarchyStarredStage C.hierarchy
        (Fin.last C.hierarchy.dividerCount) = A → TreeSequenceInitialSegment A T →
        HierarchyFullTailLength C = ell → ell = T.length - A.length → A.length + j < T.length →
        Z.length = T.length - (1 : ℕ) → Y.length = A.length + j → TreeSequenceInitialSegment Y T →
        TreeSequenceInitialSegment Z T →
    ∀ (YR : TreeSequence G e0), YR.length = A.length + j → TreeSequenceInitialSegment YR T →
        YR.vertex (Fin.last YR.length) = Y.vertex (Fin.last Y.length) → (
    ∀ {S U W : TreeSequence G e0}, TreeSequenceInitialSegment S W → TreeSequenceInitialSegment U W
        → S.length ≤ U.length → TreeSequenceInitialSegment S U) → TreeSequenceInitialSegment Y Z →
        ColoredVertexSetElementary G R.coloring (TreeSequenceVertexSet Z) → (
    ∀ (S : TreeSequence G e0) (i : Fin (S.length + (1 : ℕ))), S.vertex i ∈ TreeSequenceVertexSet
        S) → theta ∈ MissingColors G R.coloring (Y.vertex (Fin.last Y.length)) → theta ∈
        MissingColors G R.coloring (YR.vertex (Fin.last YR.length)) → theta ∉
        TashkinovStoredColors R.corresponding.replacementETT.series.data n → (
    ∀ (r : Fin T.length), A.length ≤ (↑r : ℕ) → (↑r : ℕ) < A.length + j → R.coloring (T.edge r) ≠
        some theta) → beta ∉ D ∧ beta ∉ ({c : Fin k |
    ∃ (r : Fin T.length), A.length ≤ (↑r : ℕ) ∧ (↑r : ℕ) < A.length + j ∧ R.coloring (T.edge r) =
        some c} : Finset (Fin k)) ∧ beta ∉ D.biUnion (R.counterexample.good.gamma q) →
        (H.dividerCount = (0 : ℕ) → beta ∉ TashkinovStoredColors
        R.corresponding.replacementETT.series.data n) → (
    ∀ (r : Fin T.length), A.length ≤ (↑r : ℕ) → (↑r : ℕ) < A.length + j → R.coloring (T.edge r) ≠
        some beta) →
    ∀ (B : TreeSequence G e0), B.length = A.length + (j - (2 : ℕ)) → TreeSequenceInitialSegment B
        T → TreeSequenceInitialSegment B Z → TreeSequenceInitialSegment YR Z → beta ∈
        TreeMissingColors R.coloring B → beta ∈ TreeMissingColors R.coloring Z → theta ∈
        TreeMissingColors R.coloring Z → beta ≠ theta → False

private abbrev helperContinuation783Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (beta : Fin k), (2 :
        ℕ) ≤ HierarchyPathNumber C.hierarchy → HierarchyPathNumber C.hierarchy <
        HierarchyFullTailLength C → (
    ∀ (mu : PartialEdgeColoring E k), IsProperEdgeColoring G mu → IsOneEdgeUncolored mu e0 →
    ∀ (v : V), (MissingColors G mu v).Nonempty) →
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), (
    let j : ℕ := HierarchyPathNumber C.hierarchy;
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ));
        TashkinovAugmentationSequence R.coloring X T) →
    ∀ (theta : Fin k), (
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount; theta ∉
        HierarchyStoredColorsAt H q) →
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let j : ℕ := HierarchyPathNumber C.hierarchy;
    let ell : ℕ := HierarchyFullTailLength R.counterexample;
    ∀ (Y : TreeSequence G e0), HierarchyFullTailPrefix C j = Y →
    let Z : TreeSequence G e0 := HierarchyFullTailPrefix R.counterexample (ell - (1 : ℕ));
    let n : Fin (R.corresponding.replacementETT.rounds + (1 : ℕ)) := Fin.last
        R.corresponding.replacementETT.rounds;
    let Tn : TreeSequence G e0 := R.corresponding.replacementETT.series.data.tree n.castSucc;
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q; TreeSequenceInitialSegment A T →
        HierarchyFullTailLength C = ell → ell = T.length - A.length → Y.length = A.length + j →
        TreeSequenceInitialSegment Y T →
    ∀ (YR : TreeSequence G e0), YR.length = A.length + j →
    ∀ (hYRT : TreeSequenceInitialSegment YR T), (
    ∀ {S U W : TreeSequence G e0}, TreeSequenceInitialSegment S W → TreeSequenceInitialSegment U W
        → S.length ≤ U.length → TreeSequenceInitialSegment S U) → TreeSequenceInitialSegment Y Z →
        ColoredVertexSetElementary G R.coloring (TreeSequenceVertexSet Z) → theta ∉
        TashkinovStoredColors R.corresponding.replacementETT.series.data n → beta ∉ D ∧ beta ∉ ({c
        : Fin k |
    ∃ (r : Fin T.length), A.length ≤ (↑r : ℕ) ∧ (↑r : ℕ) < A.length + j ∧ R.coloring (T.edge r) =
        some c} : Finset (Fin k)) ∧ beta ∉ D.biUnion (R.counterexample.good.gamma q) →
        (H.dividerCount = (0 : ℕ) → beta ∉ TashkinovStoredColors
        R.corresponding.replacementETT.series.data n) → (
    ∀ (r : Fin T.length), A.length ≤ (↑r : ℕ) → (↑r : ℕ) < A.length + j → R.coloring (T.edge r) ≠
        some beta) →
    ∀ (B : TreeSequence G e0), B.length = A.length + (j - (2 : ℕ)) → beta ∈ TreeMissingColors
        R.coloring Z → theta ∈ TreeMissingColors R.coloring Z → beta ≠ theta →
    let Xfull : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ)); Xfull.length =
        A.length + (j - (1 : ℕ)) → TreeSequenceInitialSegment Xfull Z → (
    ∀ (S : TreeSequence G e0), TreeSequenceInitialSegment S T →
    ∀ (i : Fin (T.length + (1 : ℕ))), (↑i : ℕ) ≤ S.length → T.vertex i ∈ TreeSequenceVertexSet S)
        → (↑(HierarchyFirstMissingPosition R.coloring T theta) : ℕ) = YR.length → TreeVertexOrder
        T (T.vertex (HierarchyFirstMissingPosition R.coloring T beta)) (T.vertex
        (HierarchyFirstMissingPosition R.coloring T theta)) → HierarchyFirstMissingPosition
        R.coloring T theta = Fin.castLE (Nat.succ_le_succ hYRT.1) (Fin.last YR.length) →
    let vb : V := T.vertex (HierarchyFirstMissingPosition R.coloring T beta);
    let vj : V := Y.vertex (Fin.last Y.length);
    let vl : V := T.vertex (Fin.last T.length); beta ∈ MissingColors G R.coloring vb → Disjoint
        (TwoColorComponent G R.coloring beta theta (Sum.inl vl)) (TwoColorComponent G R.coloring
        beta theta (Sum.inl vb)) → TwoColorPathComponent G R.coloring beta theta (Sum.inl vl) → (
    ∀ x ∈ TreeSequenceVertexSet Z, MissingColors G (TwoColorComponentSwap G R.coloring beta theta
        (Sum.inl vl)) x = MissingColors G R.coloring x) →
    let tau : PartialEdgeColoring E k := TwoColorComponentSwap G R.coloring beta theta (Sum.inl
        vl); IsOneEdgeUncolored tau e0 → theta ∈ MissingColors G tau vl → theta ∈ MissingColors G
        tau vj → ¬ColoredVertexSetElementary G tau (TreeSequenceVertexSet T) →
        TreeSequenceInitialSegment A Y → A.length < Y.length → TreeSequenceInitialSegment Xfull Y
        → Y.length = Xfull.length + (1 : ℕ) → (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < Y.length → tau (T.edge t) = R.coloring
        (T.edge t)) → beta ∈ TreeMissingColors tau Y ∧ theta ∈ TreeMissingColors tau Y → (
    ∀ eta ∈ D, HierarchyFirstMissingPosition tau T eta = HierarchyFirstMissingPosition R.coloring
        T eta) → (
    ∀ eta ∈ D, beta ∈ R.counterexample.good.gamma q eta ∨ theta ∈ R.counterexample.good.gamma q
        eta → (↑(HierarchyFirstMissingPosition R.coloring T eta) : ℕ) ≤ Y.length) → (
    ∀ {S U W : TreeSequence G e0}, TreeSequenceInitialSegment S U → TreeSequenceInitialSegment U W
        → TreeSequenceInitialSegment S W) → (H.dividerCount ≠ (0 : ℕ) → A = H.stage
        (⟨H.dividerCount,
    by
                                                             have :=
                                                              GoldbergSeymour.TreeSequence.positive
                                                               T
                                                             omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) → False

private abbrev helperContinuation590Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (beta : Fin k), (2 :
        ℕ) ≤ HierarchyPathNumber C.hierarchy → HierarchyPathNumber C.hierarchy <
        HierarchyFullTailLength C → (
    ∀ (mu : PartialEdgeColoring E k), IsProperEdgeColoring G mu → IsOneEdgeUncolored mu e0 →
    ∀ (v : V), (MissingColors G mu v).Nonempty) →
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), beta ∈
        MissingColors G R.coloring (T.vertex (Fin.last T.length)) → (
    let j : ℕ := HierarchyPathNumber C.hierarchy;
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ));
        TashkinovAugmentationSequence R.coloring X T) →
    ∀ (theta : Fin k), (
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount; theta ∉
        HierarchyStoredColorsAt H q) → (
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let Gamma : Finset (Fin k) := D.biUnion (R.counterexample.good.gamma q); theta ∉ Gamma) → (
    ∀ (psi : PartialEdgeColoring E k) (a b : Fin k), a ≠ b → IsProperEdgeColoring G psi →
    ∀ (B : Finset V), ColoredVertexSetElementary G psi B →
    ∀ (u v w : V), u ∈ B → v ∈ B → u ≠ v → w ≠ u → w ≠ v → a ∈ MissingColors G psi u → b ∈
        MissingColors G psi v → a ∈ MissingColors G psi w ∨ b ∈ MissingColors G psi w →
        TwoColorComponent G psi a b (Sum.inl u) = TwoColorComponent G psi a b (Sum.inl v) →
        Disjoint (TwoColorComponent G psi a b (Sum.inl w)) (TwoColorComponent G psi a b (Sum.inl
        u)) ∧ TwoColorPathComponent G psi a b (Sum.inl w) ∧
    ∀ x ∈ B, MissingColors G (TwoColorComponentSwap G psi a b (Sum.inl w)) x = MissingColors G psi
        x) →
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let j : ℕ := HierarchyPathNumber C.hierarchy;
    let ell : ℕ := HierarchyFullTailLength R.counterexample;
    ∀ (Y : TreeSequence G e0), HierarchyFullTailPrefix C j = Y →
    let Z : TreeSequence G e0 := HierarchyFullTailPrefix R.counterexample (ell - (1 : ℕ));
    let n : Fin (R.corresponding.replacementETT.rounds + (1 : ℕ)) := Fin.last
        R.corresponding.replacementETT.rounds;
    let _ : TreeSequence G e0 := R.corresponding.replacementETT.series.data.tree n.castSucc;
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q; TreeSequenceInitialSegment A T →
        HierarchyFullTailLength C = ell → ell = T.length - A.length → Z.length = T.length - (1 :
        ℕ) → Y.length = A.length + j → TreeSequenceInitialSegment Y T → TreeSequenceInitialSegment
        Z T →
    ∀ (YR : TreeSequence G e0), YR.length = A.length + j →
    ∀ (hYRT : TreeSequenceInitialSegment YR T), (
    ∀ {S U W : TreeSequence G e0}, TreeSequenceInitialSegment S W → TreeSequenceInitialSegment U W
        → S.length ≤ U.length → TreeSequenceInitialSegment S U) → TreeSequenceInitialSegment Y Z →
        ColoredVertexSetElementary G R.coloring (TreeSequenceVertexSet Z) → (
    ∀ (S : TreeSequence G e0) (i : Fin (S.length + (1 : ℕ))), S.vertex i ∈ TreeSequenceVertexSet
        S) → theta ∈ MissingColors G R.coloring (Y.vertex (Fin.last Y.length)) → theta ∉
        TashkinovStoredColors R.corresponding.replacementETT.series.data n → (
    ∀ (r : Fin T.length), A.length ≤ (↑r : ℕ) → (↑r : ℕ) < A.length + j → R.coloring (T.edge r) ≠
        some theta) → beta ∉ D ∧ beta ∉ ({c : Fin k |
    ∃ (r : Fin T.length), A.length ≤ (↑r : ℕ) ∧ (↑r : ℕ) < A.length + j ∧ R.coloring (T.edge r) =
        some c} : Finset (Fin k)) ∧ beta ∉ D.biUnion (R.counterexample.good.gamma q) →
        (H.dividerCount = (0 : ℕ) → beta ∉ TashkinovStoredColors
        R.corresponding.replacementETT.series.data n) → (
    ∀ (r : Fin T.length), A.length ≤ (↑r : ℕ) → (↑r : ℕ) < A.length + j → R.coloring (T.edge r) ≠
        some beta) →
    ∀ (B : TreeSequence G e0), B.length = A.length + (j - (2 : ℕ)) → TreeSequenceInitialSegment B
        T → TreeSequenceInitialSegment B Z → beta ∈ TreeMissingColors R.coloring Z → theta ∈
        TreeMissingColors R.coloring Z → beta ≠ theta →
    let Xfull : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ)); Xfull.length =
        A.length + (j - (1 : ℕ)) → TreeSequenceInitialSegment Xfull T → TreeSequenceInitialSegment
        Xfull Z → (
    ∀ (S : TreeSequence G e0), TreeSequenceInitialSegment S T →
    ∀ (i : Fin (T.length + (1 : ℕ))), (↑i : ℕ) ≤ S.length → T.vertex i ∈ TreeSequenceVertexSet S)
        → beta ∈ MissingColors G R.coloring (T.vertex (HierarchyFirstMissingPosition R.coloring T
        beta)) ∧ (↑(HierarchyFirstMissingPosition R.coloring T beta) : ℕ) ≤ B.length →
        (↑(HierarchyFirstMissingPosition R.coloring T theta) : ℕ) = YR.length → TreeVertexOrder T
        (T.vertex (HierarchyFirstMissingPosition R.coloring T beta)) (T.vertex
        (HierarchyFirstMissingPosition R.coloring T theta)) → TwoColorComponent G R.coloring beta
        theta (Sum.inl (T.vertex (HierarchyFirstMissingPosition R.coloring T beta))) =
        TwoColorComponent G R.coloring beta theta (Sum.inl (T.vertex
        (HierarchyFirstMissingPosition R.coloring T theta))) → HierarchyFirstMissingPosition
        R.coloring T theta = Fin.castLE (Nat.succ_le_succ hYRT.1) (Fin.last YR.length) → T.vertex
        (HierarchyFirstMissingPosition R.coloring T theta) = Y.vertex (Fin.last Y.length) → False

private theorem helper_continuation_783.{u_1, u_2} :
    helperContinuation783Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx beta hpathLower hpathUpper hvertexMissing R
      initialSuffix theta hthetaUnstored H q A j ell Y hYdef Z n Tn D hAT hellSame hell hYlen hYT
      YR hYRlen hYRT commonPrefix hYZ hZ hthetaRawUnstored houtside hbetaRawUnstored hbetaUnused
      B hBlen hbetaZ hthetaZ hne Xfull hXlen hXfullZ prefixVertexMem hthetaIndex hordered
      hthetaFirstIndex vb vj vl hbetaAt hdisjoint hpath hmissingPenultimate tau htauOne
      hthetaLastTau hthetaJTau hnotElementary hAY hAYstrict hXY hYnext hfixedTail hsplitMissing
      hstoredFirst hgammaCutoff segTrans lastPositive
  have hrebuilt : ∃ corr : CorrespondingExtendedTashkinovTree
      G k e0 R.corresponding.replacementETT tau T,
      MaximumProperty corr.replacementETT ∧
      ∃ bs : HierarchyBase corr.replacementETT tau,
      ∃ K : TashkinovHierarchy corr.replacementETT bs,
      ∃ good : GoodHierarchy K, SameGoodHierarchy R.counterexample.good good := by
    by_cases hcase :
        (0 < H.dividerCount ∧ beta ∈ TreeMissingColors R.coloring
          (H.stage ⟨H.dividerCount, by omega⟩)) ∨
        (H.dividerCount = 0 ∧ (beta ∈ TreeMissingColors R.coloring Tn ∨
          (beta ∈ TreeMissingColors R.coloring A ∧
            beta ∉ TashkinovStoredColors R.corresponding.replacementETT.series.data n ∧
            theta ∉ TashkinovStoredColors R.corresponding.replacementETT.series.data n)))
    · have hweak : HierarchyWeaklyStable H q tau := by
        exact (StableChangeCasesOneTwo G k e0 R.corresponding.replacementInput T R.coloring
          R.corresponding.replacementETT R.replacementBase R.counterexample
          R.minimumContext.proper R.minimumContext.oneEdgeUncolored R.minimumContext.lowerRung
          R.minimumContext.fewerDividers R.minimumContext.lexicographicMinimality hZ
          R.minimumContext.largeMissingSet beta theta hne ⟨hbetaZ, hthetaZ⟩
          (Sum.inl vl) hpath tau rfl hcase hdisjoint).1
      have baseStable : if R.corresponding.replacementETT.series.data.kind n =
          some TashkinovExtensionKind.PE then
          CombinedStableColoring Tn R.replacementBase.closure
            (TashkinovStoredColors R.corresponding.replacementETT.series.data n) R.coloring tau
        else StableColoring Tn (TashkinovStoredColors R.corresponding.replacementETT.series.data n)
          R.coloring tau := by
        have extract (i : Fin (H.dividerCount + 1)) : HierarchyWeaklyStable H i tau →
            (if R.corresponding.replacementETT.series.data.kind n = some
                TashkinovExtensionKind.PE then
              CombinedStableColoring Tn R.replacementBase.closure
                (TashkinovStoredColors R.corresponding.replacementETT.series.data n) R.coloring tau
            else StableColoring Tn (TashkinovStoredColors
                R.corresponding.replacementETT.series.data n)
              R.coloring tau) := Fin.cases (fun h => h) (fun _ h => h.1) i
        exact extract q hweak
      have fixedA : ∀ t : Fin A.length, tau (A.edge t) = R.coloring (A.edge t) := by
        have fixed (i : Fin (H.dividerCount + 1)) : HierarchyWeaklyStable H i tau →
            ∀ t : Fin (HierarchyStarredStage H i).length,
              tau ((HierarchyStarredStage H i).edge t) = R.coloring ((HierarchyStarredStage H
                  i).edge t) := by
          refine Fin.cases ?_ (fun i => ?_) i
          · intro _
            exact P2813_T1_BaseDisplayedEdges G k e0 R.corresponding.replacementInput T R.coloring
              R.corresponding.replacementETT R.replacementBase tau
              R.minimumContext.oneEdgeUncolored htauOne baseStable
          · intro hh t
            change tau ((H.stage i.succ.castSucc).edge t) = R.coloring ((H.stage
                i.succ.castSucc).edge t)
            by_cases ht : t.val = 0
            · have he : (H.stage i.succ.castSucc).edge t = e0 := by
                rw [show t = ⟨0, (H.stage i.succ.castSucc).positive⟩ from Fin.ext ht]
                exact (H.stage i.succ.castSucc).first_edge
              rw [he, htauOne.1, R.minimumContext.oneEdgeUncolored.1]
            · exact hh.2.1 t (by omega)
        exact fixed q hweak
      have fixedY : ∀ t : Fin Y.length, tau (Y.edge t) = R.coloring (Y.edge t) := by
        intro t
        by_cases ht : t.val < A.length
        · let s : Fin A.length := ⟨t.val, ht⟩
          have he : Fin.castLE hAY.1 s = t := Fin.ext rfl
          rw [← he, hAY.2.2 s]
          exact fixedA s
        · rw [← hYT.2.2 t]
          exact hfixedTail (Fin.castLE hYT.1 t) (by change A.length ≤ t.val; omega) t.isLt
      have coreToA : TreeSequenceInitialSegment R.replacementBase.core A := by
        by_cases hz : H.dividerCount = 0
        · have he : A = R.replacementBase.core := by simp [A, q, HierarchyStarredStage, hz,
            Fin.last]
          rw [he]
          exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
        · have stageSegment (a m : Nat) (hb : a + m ≤ H.dividerCount + 1) :
              TreeSequenceInitialSegment (H.stage ⟨a, by omega⟩) (H.stage ⟨a + m, by omega⟩) := by
            induction m with
            | zero => exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
            | succ m ih => exact segTrans (ih (by omega)) (H.nested ⟨a + m, by omega⟩)
          rw [lastPositive hz]
          have hs := stageSegment 1 (H.dividerCount - 1) (by omega)
          have he : 1 + (H.dividerCount - 1) = H.dividerCount := by omega
          simpa [he] using segTrans H.coreInsideFirst hs
      have TnToA : TreeSequenceInitialSegment Tn A := by
        have TnToCore : TreeSequenceInitialSegment Tn R.replacementBase.core := by
          by_cases hp : R.corresponding.replacementETT.series.data.kind n = some
              TashkinovExtensionKind.PE
          · exact (Classical.choice (R.replacementBase.parallel hp).2.2).leftSegment
          · rw [R.replacementBase.nonparallel hp]
            exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
        exact segTrans TnToCore coreToA
      have routes :
          (R.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.PE ∧
            TashkinovAugmentationSequence tau Tn Y) ∨
          ((R.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.SE ∨
            R.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.RE) ∧
            ∃ f seed, R.corresponding.replacementETT.series.data.connectingEdges n = {f} ∧
              TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence tau seed Y) := by
        rcases P2813_T1_TerminalRoute G k e0 R.corresponding.replacementInput T R.coloring
            R.corresponding.replacementETT with ⟨hp, hseq⟩ |
            ⟨hp, f, seed, hedges, hseed, _, _, hseq⟩
        · have hsourceY := segTrans TnToA hAY
          have hpre := TashkinovAugmentationSequenceRestrict R.coloring Tn Y T hseq hsourceY hYT
          exact Or.inl ⟨hp, TashkinovAugmentationSequenceColoringTransport R.coloring tau
            Tn Xfull Y hpre hXY hYnext (fun t _ => fixedY t)
              (fun v hv =>
                  hmissingPenultimate v (TreeSequenceInitialSegmentVertexSetSubset hXfullZ hv))⟩
        · have hseedY : TreeSequenceInitialSegment seed Y :=
            commonPrefix (TashkinovAugmentationSequenceInitialSegment R.coloring seed T hseq) hYT
              (by have hl := hseed.1; have := TnToA.1
                  change seed.length = Tn.length + 1 at hl; omega)
          have hpre := TashkinovAugmentationSequenceRestrict R.coloring seed Y T hseq hseedY hYT
          exact Or.inr ⟨hp, f, seed, hedges, hseed,
            TashkinovAugmentationSequenceColoringTransport R.coloring tau
              seed Xfull Y hpre hXY hYnext (fun t _ => fixedY t)
                (fun v hv =>
                    hmissingPenultimate v (TreeSequenceInitialSegmentVertexSetSubset hXfullZ hv))⟩
      have hsuffix : TashkinovAugmentationSequence R.coloring Y T :=
        TashkinovAugmentationSequenceSuffix R.coloring Xfull Y T initialSuffix hXY hYT
      exact (StableChangeCasesOneTwoSplitTail G k e0 R.corresponding.replacementInput T R.coloring
        R.corresponding.replacementETT R.replacementBase R.counterexample R.minimumContext
        beta theta hne ⟨hbetaZ, hthetaZ⟩ (Sum.inl vl) hpath tau rfl hcase hdisjoint
        Y hAY hAYstrict hYZ hfixedTail routes hsuffix hsplitMissing
        hmissingPenultimate hstoredFirst hgammaCutoff).2.2
    · have hbetaNotA : beta ∉ TreeMissingColors R.coloring A := by
        intro hb
        apply hcase
        by_cases hz : H.dividerCount = 0
        · exact Or.inr ⟨hz, Or.inr ⟨hb, hbetaRawUnstored hz, hthetaRawUnstored⟩⟩
        · exact Or.inl ⟨by omega, by rw [← lastPositive hz]; exact hb⟩
      have hbetaAfterA : A.length < (HierarchyFirstMissingPosition R.coloring T beta).val := by
        by_contra hn
        have hle : (HierarchyFirstMissingPosition R.coloring T beta).val ≤ A.length := by omega
        exact hbetaNotA (Finset.mem_biUnion.mpr ⟨vb,
          prefixVertexMem A hAT (HierarchyFirstMissingPosition R.coloring T beta) hle, hbetaAt⟩)
      have hprecedes : ∀ v ∈ TreeSequenceVertexSet A,
          TreeVertexOrder T v (T.vertex (HierarchyFirstMissingPosition R.coloring T beta)) := by
        intro v hv
        obtain ⟨i, hi⟩ : ∃ i : Fin (A.length + 1), A.vertex i = v := by
          simpa only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] using hv
        exact ⟨Fin.castLE (Nat.succ_le_succ hAT.1) i, _, (hAT.2.1 i).trans hi, rfl,
          by change i.val < (HierarchyFirstMissingPosition R.coloring T beta).val
             have := i.isLt; omega⟩
      have hunusedBetween : beta ∉ (Finset.univ.filter fun c : Fin k =>
          ∃ t : Fin T.length,
            (HierarchyFirstMissingPosition R.coloring T beta).val ≤ t.val ∧
            t.val < (HierarchyFirstMissingPosition R.coloring T theta).val ∧
            R.coloring (T.edge t) = some c) := by
        intro hh
        obtain ⟨_, t, hlo, hhi, hc⟩ := Finset.mem_filter.mp hh
        exact hbetaUnused t (by omega) (by rw [hthetaIndex, hYRlen] at hhi; exact hhi) hc
      obtain ⟨_, _, _, _, corr, hmaximum, bs, K, good, hsameGood⟩ :=
        StableChangeCaseThree G k e0 R.corresponding.replacementInput T R.coloring
          R.corresponding.replacementETT R.replacementBase R.counterexample
          R.minimumContext.proper R.minimumContext.oneEdgeUncolored R.minimumContext.lowerRung
          R.minimumContext.fewerDividers R.minimumContext.lexicographicMinimality hZ
          R.minimumContext.largeMissingSet beta theta hne ⟨hbetaZ, hthetaZ⟩
          (Sum.inl vl) tau rfl hprecedes hordered ⟨houtside.1, hthetaUnstored⟩ hunusedBetween
      exact ⟨corr, hmaximum, bs, K, good, hsameGood⟩
  obtain ⟨corr, hmaximum, bs, K, good, hsameGood⟩ := hrebuilt
  let Ctau : HierarchyCounterexample bs := {
    positive := by rw [corr.rungAgreement]; exact R.counterexample.positive
    hierarchy := K
    good := good
    maximum := hmaximum
    notElementary := hnotElementary }
  obtain ⟨S, hS⟩ := HierarchyReplacementPresentationTrans G k e0 input T phi ett base C ctx
    R tau corr bs Ctau hsameGood
  have hjEligible : j ∈ HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx
     := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by rw [hellSame]; omega⟩,
      S, theta, ?_, ?_⟩
    · rw [hS]
      rw [hYdef]
      exact hthetaJTau
    · rw [hS]
      exact hthetaLastTau
  have hbound := HierarchySituationThreeEligibleIndexBound G k e0 input T phi ett base C ctx
    hpathLower hpathUpper hvertexMissing j hjEligible
  exact Nat.lt_irrefl j hbound

private theorem helper_continuation_590.{u_1, u_2} :
    helperContinuation590Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx beta hpathLower hpathUpper hvertexMissing R
      initialBetaLast initialSuffix theta hthetaUnstored initialThetaGamma componentData H q A j
      ell Y hYdef Z n Tn D hAT hellSame hell hZlen hYlen hYT hZT YR hYRlen hYRT commonPrefix hYZ
      hZ vertexMem hthetaY hthetaRawUnstored hthetaUnused houtside hbetaRawUnstored hbetaUnused B
      hBlen hBT hBZ hbetaZ hthetaZ hne Xfull hXlen hXfullT hXfullZ prefixVertexMem hbetaFirst
      hthetaIndex hordered hsame hthetaFirstIndex hthetaRootY
  let vb := T.vertex (HierarchyFirstMissingPosition R.coloring T beta)
  let vj := Y.vertex (Fin.last Y.length)
  let vl := T.vertex (Fin.last T.length)
  have hvbB : vb ∈ TreeSequenceVertexSet B :=
    prefixVertexMem B hBT (HierarchyFirstMissingPosition R.coloring T beta)
      hbetaFirst.2
  have hvbZ : vb ∈ TreeSequenceVertexSet Z :=
    TreeSequenceInitialSegmentVertexSetSubset hBZ hvbB
  have hvjZ : vj ∈ TreeSequenceVertexSet Z := by
    exact TreeSequenceInitialSegmentVertexSetSubset hYZ
      (vertexMem Y (Fin.last Y.length))
  have hvlNotZ : vl ∉ TreeSequenceVertexSet Z := by
    clear * - hZT hZlen
    intro hm
    have hindex : ∃ i : Fin (Z.length + 1), Z.vertex i = vl := by
      simpa only [TreeSequenceVertexSet, Finset.mem_image,
        Finset.mem_univ, true_and] using hm
    rcases hindex with ⟨i, hi⟩
    have htoT : T.vertex (Fin.castLE (Nat.succ_le_succ hZT.1) i) = vl :=
      (hZT.2.1 i).trans hi
    have hinj := T.vertex_injective htoT
    have hval := congrArg Fin.val hinj
    change i.val = T.length at hval
    have hiBound : i.val ≤ Z.length := Nat.le_of_lt_succ i.isLt
    have hpositive := T.positive
    omega
  have hvbNeVj : vb ≠ vj := by
    clear * - hordered hthetaRootY
    intro heq
    rcases hordered with ⟨i, m, hi, hm, hlt⟩
    have heq' : T.vertex i = T.vertex m := by
      rw [hi, hm, hthetaRootY]
      exact heq
    have hinj := T.vertex_injective heq'
    have hval := congrArg Fin.val hinj
    omega
  have hvbNeVl : vb ≠ vl := by
    intro heq
    exact hvlNotZ (heq ▸ hvbZ)
  have hvjNeVl : vj ≠ vl := by
    intro heq
    exact hvlNotZ (heq ▸ hvjZ)
  have hbetaAt : beta ∈ MissingColors G R.coloring vb := by
    simpa [vb] using hbetaFirst.1
  have hthetaAt : theta ∈ MissingColors G R.coloring vj := by
    simpa [vj] using hthetaY
  have hbetaLast : beta ∈ MissingColors G R.coloring vl := by
    simpa [vl] using initialBetaLast
  have hsameToJ : TwoColorComponent G R.coloring beta theta (Sum.inl vb) =
      TwoColorComponent G R.coloring beta theta (Sum.inl vj) := by
    simpa [vb, vj, hthetaRootY] using hsame
  obtain ⟨hdisjoint, hpath, hmissingPenultimate⟩ :=
    componentData R.coloring beta theta hne R.minimumContext.proper
      (TreeSequenceVertexSet Z) hZ vb vj vl hvbZ hvjZ hvbNeVj
      hvbNeVl.symm hvjNeVl.symm hbetaAt hthetaAt (Or.inl hbetaLast) hsameToJ
  let tau := TwoColorComponentSwap G R.coloring beta theta (Sum.inl vl)
  have htauProper : IsProperEdgeColoring G tau := by
    exact TwoColorComponentSwapProper G R.coloring beta theta hne
      R.minimumContext.proper (Sum.inl vl)
  have htauOne : IsOneEdgeUncolored tau e0 := by
    clear * - R hne
    refine ⟨?_, ?_⟩
    · simp [tau, TwoColorComponentSwap, R.minimumContext.oneEdgeUncolored.1]
    · intro f hf
      obtain ⟨c, hc⟩ := R.minimumContext.oneEdgeUncolored.2 f hf
      by_cases hm : Sum.inr f ∈ TwoColorComponent G R.coloring beta theta (Sum.inl vl)
      · by_cases hcb : c = beta
        · subst c
          exact ⟨theta, by simp [tau, TwoColorComponentSwap, hm, hc]⟩
        · by_cases hct : c = theta
          · subst c
            exact ⟨beta, by simp [tau, TwoColorComponentSwap, hm, hc, hne.symm]⟩
          · exact ⟨c, by simp [tau, TwoColorComponentSwap, hm, hc, hcb, hct]⟩
      · exact ⟨c, by simp [tau, TwoColorComponentSwap, hm, hc]⟩
  have hthetaLastTau : theta ∈ MissingColors G tau vl := by
    exact (TwoColorComponentSwapMissingBehavior G R.coloring beta theta hne
      R.minimumContext.proper (Sum.inl vl)).2.1 vl (by rfl) hbetaLast
  have hthetaJTau : theta ∈ MissingColors G tau vj := by
    rw [hmissingPenultimate vj hvjZ]
    exact hthetaAt
  have hnotElementary : ¬ ColoredVertexSetElementary G tau (TreeSequenceVertexSet T) := by
    intro he
    exact Finset.disjoint_left.mp
      (he (TreeSequenceInitialSegmentVertexSetSubset hYT
        (vertexMem Y (Fin.last Y.length))) (vertexMem T (Fin.last T.length))
          hvjNeVl) hthetaJTau hthetaLastTau
  have hAY : TreeSequenceInitialSegment A Y :=
    commonPrefix hAT hYT (by rw [hYlen]; omega)
  have hAYstrict : A.length < Y.length := by
    clear * - hYlen hpathLower
    omega
  have hXY : TreeSequenceInitialSegment Xfull Y :=
    commonPrefix hXfullT hYT (by rw [hXlen, hYlen]; omega)
  have hYnext : Y.length = Xfull.length + 1 := by
    clear * - hYlen hXlen hpathLower
    omega
  have hBY : TreeSequenceInitialSegment B Y :=
    commonPrefix hBT hYT (by rw [hBlen, hYlen]; omega)
  have hfixedTail : ∀ t : Fin T.length, A.length ≤ t.val → t.val < Y.length →
      tau (T.edge t) = R.coloring (T.edge t) := by
    clear * - hbetaUnused hthetaUnused hYlen
    intro t hlo hhi
    rw [hYlen] at hhi
    have hb := hbetaUnused t hlo hhi
    have ht := hthetaUnused t hlo hhi
    simp [tau, TwoColorComponentSwap, hb, ht]
  have hsplitMissing : beta ∈ TreeMissingColors tau Y ∧ theta ∈ TreeMissingColors tau Y := by
    clear * - hvbB hBY hmissingPenultimate hvbZ hbetaAt vertexMem hthetaJTau
    unfold TreeMissingColors
    refine ⟨Finset.mem_biUnion.mpr ⟨vb,
      TreeSequenceInitialSegmentVertexSetSubset hBY hvbB, ?_⟩,
      Finset.mem_biUnion.mpr ⟨vj, vertexMem Y (Fin.last Y.length), hthetaJTau⟩⟩
    rw [hmissingPenultimate vb hvbZ]
    exact hbetaAt
  have hstoredFirst : ∀ eta, eta ∈ D →
      HierarchyFirstMissingPosition tau T eta = HierarchyFirstMissingPosition R.coloring T eta := by
    clear * - houtside hthetaUnstored hne
    intro eta heta
    have heb : eta ≠ beta := fun he => houtside.1 (he ▸ heta)
    have het : eta ≠ theta := fun he => hthetaUnstored (he ▸ heta)
    have hmissing := (TwoColorComponentSwapMissingBehavior G R.coloring beta theta hne
      R.minimumContext.proper (Sum.inl vl)).2.2.2
    have hcandidates :
        (Finset.univ.filter fun i : Fin (T.length + 1) => eta ∈ MissingColors G tau (T.vertex i)) =
        (Finset.univ.filter fun i : Fin (T.length + 1) =>
            eta ∈ MissingColors G R.coloring (T.vertex i)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hmissing (T.vertex i) eta heb het
    unfold HierarchyFirstMissingPosition
    simp only [hcandidates]
  have hgammaCutoff : ∀ eta, eta ∈ D →
      (beta ∈ R.counterexample.good.gamma q eta ∨
        theta ∈ R.counterexample.good.gamma q eta) →
      (HierarchyFirstMissingPosition R.coloring T eta).val ≤ Y.length := by
    intro eta heta hc
    rcases hc with hc | hc
    · exact (houtside.2.2 (Finset.mem_biUnion.mpr ⟨eta, heta, hc⟩)).elim
    · exact (initialThetaGamma (Finset.mem_biUnion.mpr ⟨eta, heta, hc⟩)).elim
  have segTrans {S U W : TreeSequence G e0}
      (hSU : TreeSequenceInitialSegment S U) (hUW : TreeSequenceInitialSegment U W) :
      TreeSequenceInitialSegment S W := by
    clear * - hSU hUW
    exact ⟨hSU.1.trans hUW.1,
      fun i => (hUW.2.1 (Fin.castLE (Nat.succ_le_succ hSU.1) i)).trans (hSU.2.1 i),
      fun i => (hUW.2.2 (Fin.castLE hSU.1 i)).trans (hSU.2.2 i)⟩
  have lastPositive (hz : H.dividerCount ≠ 0) : A = H.stage ⟨H.dividerCount, by omega⟩ := by
    clear * - hz
    obtain hzero | ⟨i, hi⟩ := Fin.eq_zero_or_eq_succ q
    · have hv := congrArg Fin.val hzero
      simp only [Fin.val_last, Fin.coe_ofNat_eq_mod, Nat.zero_mod, q] at hv
      exact (hz hv).elim
    · simp only [A, HierarchyStarredStage, hi, Fin.cases_succ]
      congr 1
      apply Fin.ext
      have hv := congrArg Fin.val hi
      simpa [q] using hv.symm
  exact @helper_continuation_783 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@beta)
      (@hpathLower) (@hpathUpper) (@hvertexMissing) (@R) (@initialSuffix) (@theta)
      (@hthetaUnstored) (@Y) (@hYdef) (@hAT) (@hellSame) (@hell) (@hYlen) (@hYT) (@YR) (@hYRlen)
      (@hYRT) (@commonPrefix) (@hYZ) (@hZ) (@hthetaRawUnstored) (@houtside) (@hbetaRawUnstored)
      (@hbetaUnused) (@B) (@hBlen) (@hbetaZ) (@hthetaZ) (@hne) (@hXlen) (@hXfullZ)
      (@prefixVertexMem) (@hthetaIndex) (@hordered) (@hthetaFirstIndex) (@hbetaAt) (@hdisjoint)
      (@hpath) (@hmissingPenultimate) (@htauOne) (@hthetaLastTau) (@hthetaJTau) (@hnotElementary)
      (@hAY) (@hAYstrict) (@hXY) (@hYnext) (@hfixedTail) (@hsplitMissing) (@hstoredFirst)
      (@hgammaCutoff) (@segTrans) (@lastPositive)
private theorem helper_continuation_460.{u_1, u_2} :
    helperContinuation460Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx beta hpathLower hpathUpper hvertexMissing R
      initialBetaLast initialSuffix theta hthetaUnstored initialThetaGamma componentData
      firstMissingVertex H q A j ell Y hYdef Z n Tn D hA hAT hellSame hell hstrict hZlen hYlen
      hYT hZT YR hYRlen hYRT hYRlast commonPrefix hYZ hZ vertexMem hthetaY hthetaYR
      hthetaRawUnstored hthetaUnused houtside hbetaRawUnstored hbetaUnused B hBlen hBT hBZ hYRZ
      hbetaB hbetaZ hthetaZ hne
  let Xfull := HierarchyFullTailPrefix C (j - 1)
  have hXlen : Xfull.length = A.length + (j - 1) := by
    clear * - hA hstrict
    have hbound : A.length + (j - 1) ≤ T.length := by omega
    simp only [Xfull, HierarchyFullTailPrefix, hA, TreeSequencePrefix, min_eq_left hbound]
  have hXfullT : TreeSequenceInitialSegment Xfull T := by
    clear * - hXlen hstrict
    refine ⟨by rw [hXlen]; omega, ?_, ?_⟩
    · intro i
      rfl
    · intro i
      rfl
  have hXfullZ : TreeSequenceInitialSegment Xfull Z :=
    commonPrefix hXfullT hZT (by rw [hXlen, hZlen]; omega)
  have prefixVertexMem (S : TreeSequence G e0)
      (hST : TreeSequenceInitialSegment S T) (i : Fin (T.length + 1))
      (hi : i.val ≤ S.length) : T.vertex i ∈ TreeSequenceVertexSet S := by
    clear * - S hST i hi
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    let iS : Fin (S.length + 1) := ⟨i.val, by omega⟩
    refine ⟨iS, ?_⟩
    have hcast : Fin.castLE (Nat.succ_le_succ hST.1) iS = i := Fin.ext rfl
    rw [← hcast]
    exact (hST.2.1 iS).symm
  have hbetaFirst :
      beta ∈ MissingColors G R.coloring
        (T.vertex (HierarchyFirstMissingPosition R.coloring T beta)) ∧
      (HierarchyFirstMissingPosition R.coloring T beta).val ≤ B.length := by
    clear * - firstMissingVertex hBT hbetaB
    unfold TreeMissingColors at hbetaB
    obtain ⟨v, hv, hm⟩ := Finset.mem_biUnion.mp hbetaB
    obtain ⟨i, hi⟩ : ∃ i : Fin (B.length + 1), B.vertex i = v := by
      simpa only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] using hv
    have hmT : beta ∈ MissingColors G R.coloring
        (T.vertex (Fin.castLE (Nat.succ_le_succ hBT.1) i)) := by
      rw [hBT.2.1 i, hi]
      exact hm
    have hf := firstMissingVertex R.coloring T
      (Fin.castLE (Nat.succ_le_succ hBT.1) i) beta hmT
    exact ⟨hf.1, hf.2.trans (Nat.le_of_lt_succ i.isLt)⟩
  have hthetaFirst :
      theta ∈ MissingColors G R.coloring
        (T.vertex (HierarchyFirstMissingPosition R.coloring T theta)) ∧
      (HierarchyFirstMissingPosition R.coloring T theta).val ≤ YR.length := by
    clear * - firstMissingVertex hYRT hthetaYR
    have hmT : theta ∈ MissingColors G R.coloring
        (T.vertex (Fin.castLE (Nat.succ_le_succ hYRT.1) (Fin.last YR.length))) := by
      rw [hYRT.2.1 (Fin.last YR.length)]
      exact hthetaYR
    exact firstMissingVertex R.coloring T
      (Fin.castLE (Nat.succ_le_succ hYRT.1) (Fin.last YR.length)) theta hmT
  have hthetaIndex :
      (HierarchyFirstMissingPosition R.coloring T theta).val = YR.length := by
    have hfirstMem : T.vertex (HierarchyFirstMissingPosition R.coloring T theta) ∈
        TreeSequenceVertexSet YR :=
      prefixVertexMem YR hYRT (HierarchyFirstMissingPosition R.coloring T theta) hthetaFirst.2
    have heq : T.vertex (HierarchyFirstMissingPosition R.coloring T theta) =
        YR.vertex (Fin.last YR.length) := by
      by_contra hn
      exact Finset.disjoint_left.mp
        (hZ (TreeSequenceInitialSegmentVertexSetSubset hYRZ hfirstMem)
          (TreeSequenceInitialSegmentVertexSetSubset hYRZ
            (vertexMem YR (Fin.last YR.length))) hn) hthetaFirst.1 hthetaYR
    have hi := T.vertex_injective (heq.trans (hYRT.2.1 (Fin.last YR.length)).symm)
    exact congrArg Fin.val hi
  have hordered : TreeVertexOrder T
      (T.vertex (HierarchyFirstMissingPosition R.coloring T beta))
      (T.vertex (HierarchyFirstMissingPosition R.coloring T theta)) := by
    clear * - hthetaIndex hBlen hbetaFirst hYRlen hpathLower
    refine ⟨_, _, rfl, rfl, ?_⟩
    rw [hthetaIndex]
    rw [hBlen] at hbetaFirst
    have hbetaPos := hbetaFirst.2
    omega
  have hunused : beta ∉ (Finset.univ.filter fun c : Fin k =>
      ∃ r : Fin T.length,
        A.length ≤ r.val ∧
          r.val < (HierarchyFirstMissingPosition R.coloring T theta).val ∧
            R.coloring (T.edge r) = some c) := by
    clear * - hthetaIndex hYRlen hbetaUnused
    intro hc
    rcases Finset.mem_filter.mp hc with ⟨_, ⟨r, hrA, hrTheta, hcol⟩⟩
    have hrJ : r.val < A.length + j := by omega
    exact hbetaUnused r hrA hrJ hcol
  have horderedUnused :
      (beta ∉ TreeMissingColors R.coloring A ∨
        theta ∉ TreeMissingColors R.coloring A) →
      TreeVertexOrder T
          (T.vertex (HierarchyFirstMissingPosition R.coloring T beta))
          (T.vertex (HierarchyFirstMissingPosition R.coloring T theta)) ∧
        beta ∉ (Finset.univ.filter fun c : Fin k =>
          ∃ r : Fin T.length,
            A.length ≤ r.val ∧
              r.val < (HierarchyFirstMissingPosition R.coloring T theta).val ∧
                R.coloring (T.edge r) = some c) := by
    intro _
    exact ⟨hordered, hunused⟩
  have hthetaNotD : theta ∉ D := by
    exact hthetaUnstored
  have hdisStored : Disjoint ({beta, theta} : Finset (Fin k)) D := by
    clear * - houtside hthetaNotD
    apply Finset.disjoint_left.mpr
    intro c hc hcD
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with hc | hc
    · subst c
      exact houtside.1 hcD
    · subst c
      exact hthetaNotD hcD
  have hsame : TwoColorComponent G R.coloring beta theta
      (Sum.inl (T.vertex (HierarchyFirstMissingPosition R.coloring T beta))) =
    TwoColorComponent G R.coloring beta theta
      (Sum.inl (T.vertex (HierarchyFirstMissingPosition R.coloring T theta))) := by
    clear * - R hZ hbetaZ hthetaZ hne horderedUnused hbetaRawUnstored hthetaRawUnstored hdisStored
    dsimp only [H, q, A, ell, Z, D, n] at hZ hbetaZ hthetaZ horderedUnused
    dsimp only [H, q, A, ell, Z, D, n] at hbetaRawUnstored hthetaRawUnstored hdisStored
    have hchange := ChangeLemma G k e0 R.corresponding.replacementInput T
      R.coloring R.corresponding.replacementETT R.replacementBase R.counterexample
      R.minimumContext.proper R.minimumContext.oneEdgeUncolored
      R.minimumContext.lowerRung R.minimumContext.fewerDividers
      R.minimumContext.lexicographicMinimality hZ R.minimumContext.largeMissingSet
      beta theta hne ⟨hbetaZ, hthetaZ⟩ horderedUnused
    by_cases hqzero : R.counterexample.hierarchy.dividerCount = 0
    · have hdisRaw : Disjoint ({beta, theta} : Finset (Fin k))
          (TashkinovStoredColors R.corresponding.replacementETT.series.data n) := by
        clear * - hqzero hbetaRawUnstored hthetaRawUnstored
        apply Finset.disjoint_left.mpr
        intro c hc hcRaw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hc
        rcases hc with hc | hc
        · subst c
          exact hbetaRawUnstored hqzero hcRaw
        · subst c
          exact hthetaRawUnstored hcRaw
      exact hchange.2.1 ⟨hqzero, Or.inr hdisRaw⟩
    · have hqpos : 0 < R.counterexample.hierarchy.dividerCount := by omega
      exact hchange.1 ⟨hqpos, Or.inr hdisStored⟩
  have hthetaFirstIndex :
      HierarchyFirstMissingPosition R.coloring T theta =
        Fin.castLE (Nat.succ_le_succ hYRT.1) (Fin.last YR.length) := by
    apply Fin.ext
    simp only [Fin.val_castLE, Fin.val_last]
    exact hthetaIndex
  have hthetaRoot :
      T.vertex (HierarchyFirstMissingPosition R.coloring T theta) =
        YR.vertex (Fin.last YR.length) := by
    rw [hthetaFirstIndex]
    exact hYRT.2.1 _
  have hthetaRootY :
      T.vertex (HierarchyFirstMissingPosition R.coloring T theta) =
        Y.vertex (Fin.last Y.length) := by
    rw [hthetaRoot, hYRlast]
  exact @helper_continuation_590 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@beta)
      (@hpathLower) (@hpathUpper) (@hvertexMissing) (@R) (@initialBetaLast) (@initialSuffix)
      (@theta) (@hthetaUnstored) (@initialThetaGamma) (@componentData) (@Y) (@hYdef) (@hAT)
      (@hellSame) (@hell) (@hZlen) (@hYlen) (@hYT) (@hZT) (@YR) (@hYRlen) (@hYRT) (@commonPrefix)
      (@hYZ) (@hZ) (@vertexMem) (@hthetaY) (@hthetaRawUnstored) (@hthetaUnused) (@houtside)
      (@hbetaRawUnstored) (@hbetaUnused) (@B) (@hBlen) (@hBT) (@hBZ) (@hbetaZ) (@hthetaZ) (@hne)
      (@hXlen) (@hXfullT) (@hXfullZ) (@prefixVertexMem) (@hbetaFirst) (@hthetaIndex) (@hordered)
      (@hsame) (@hthetaFirstIndex) (@hthetaRootY)
private theorem helper_continuation_344.{u_1, u_2} :
    helperContinuation344Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx beta hpathLower hpathUpper hvertexMissing R
      hconditionOutside initialBetaBefore initialBetaLast initialSuffix theta hthetaUnstored
      initialThetaGamma componentData firstMissingVertex H q A j ell Y hYdef Z n Tn D hA hAT
      hellSame hell hjlt hstrict hZlen hYlen hYT hZT YR hYRdef hYRlen hYRT hYRlast commonPrefix
      hYZ hZ vertexMem hthetaY hthetaYR hthetaNotA
  have hthetaRawUnstored : theta ∉
      TashkinovStoredColors R.corresponding.replacementETT.series.data n := by
    intro hraw
    apply hthetaUnstored
    change theta ∈ HierarchyStoredColorsAt H q
    change theta ∈ TashkinovStoredColors
      R.corresponding.replacementETT.series.data n \
        TreeMissingColors R.coloring A
    exact Finset.mem_sdiff.mpr ⟨hraw, hthetaNotA⟩
  have hthetaUnused : ∀ r : Fin T.length, A.length ≤ r.val →
      r.val < A.length + j → R.coloring (T.edge r) ≠ some theta := by
    clear * - hYRdef hYRlen hYRT hZ hjlt hthetaYR hthetaRawUnstored hpathLower
    subst YR
    let YR : TreeSequence G e0 := TreeSequencePrefix T (min (A.length + j) T.length)
      (by have := A.positive; have := T.positive; omega) (Nat.min_le_right _ _)
    intro r hrA hrJ hcolor
    let t : Fin YR.length := ⟨r.val, by rw [hYRlen]; omega⟩
    change Fin ((fun i : ℕ => TreeSequencePrefix T
      (min (A.length + i) T.length)
      (by have hApos := A.positive; have hTpos := T.positive; omega)
      (Nat.min_le_right _ _)) j).length at t
    have hcast : Fin.castLE hYRT.1 t = r := Fin.ext rfl
    have hedge : YR.edge t = T.edge r := by
      have h := hYRT.2.2 t
      rw [hcast] at h
      exact h.symm
    have hcolorQ : R.coloring (((fun i : ℕ => TreeSequencePrefix T
        (min (A.length + i) T.length)
        (by have hApos := A.positive; have hTpos := T.positive; omega)
        (Nat.min_le_right _ _)) j).edge t) = some theta := by
      change R.coloring (YR.edge t) = some theta
      rw [hedge]
      exact hcolor
    have htail := HierarchyTailMissingColorExclusion G k e0
      R.corresponding.replacementInput T R.coloring R.corresponding.replacementETT
      R.replacementBase H hZ j (by omega) hjlt theta hthetaYR t
      (by change A.length ≤ r.val; exact hrA)
      (by change r.val < A.length + j; exact hrJ)
      hcolorQ
    rcases htail with ⟨_, _, _, f, _, _, _, _, _, hstored⟩
    exact hthetaRawUnstored (by simpa [n] using hstored)
  have houtside : beta ∉ D ∧ beta ∉ (Finset.univ.filter fun c : Fin k =>
      ∃ r : Fin T.length, A.length ≤ r.val ∧ r.val < A.length + j ∧
        R.coloring (T.edge r) = some c) ∧ beta ∉
      D.biUnion (R.counterexample.good.gamma q) := by
    rcases hconditionOutside with ⟨_, hu, hg, hd⟩
    exact ⟨hd, hu, hg⟩
  have hbaseExtra : beta ∉
      ((TreeSequenceVertexSet R.replacementBase.core \
        TreeSequenceVertexSet Tn).biUnion fun v => MissingColors G R.coloring v) := by
    rcases hconditionOutside with ⟨hb, _, _, _⟩
    exact hb
  have hbetaRawUnstored : H.dividerCount = 0 → beta ∉
      TashkinovStoredColors R.corresponding.replacementETT.series.data n := by
    clear * - houtside hbaseExtra
    intro hqzero hraw
    have hbetaMissingA : beta ∈ TreeMissingColors R.coloring A := by
      by_contra hnot
      exact houtside.1 (Finset.mem_sdiff.mpr ⟨hraw, hnot⟩)
    have hAcore : A = R.replacementBase.core := by
      simp [A, q, HierarchyStarredStage, hqzero, Fin.last]
    have hbetaCore : beta ∈ TreeMissingColors R.coloring R.replacementBase.core := by
      simpa [hAcore] using hbetaMissingA
    have hnotTn : beta ∉ TreeMissingColors R.coloring Tn := by
      have hn : n.val ≠ 0 := by
        exact Nat.ne_of_gt R.counterexample.positive
      have hmem := hraw
      unfold TashkinovStoredColors at hmem
      rw [ite_eq_right hn] at hmem
      simp only [Finset.mem_sdiff] at hmem
      have hterminalColor :
          R.corresponding.replacementETT.series.data.coloring n = R.coloring := by
        simpa [n] using R.corresponding.replacementETT.generatingColoring.symm
      rw [hterminalColor] at hmem
      exact hmem.2
    by_cases hpe : R.corresponding.replacementETT.series.data.kind n =
        some TashkinovExtensionKind.PE
    · let U : OrderedTreeUnion Tn R.replacementBase.closure
          R.replacementBase.core := Classical.choice
            (R.replacementBase.parallel hpe).2.2
      rcases Finset.mem_biUnion.mp hbetaCore with ⟨v, hv, hmiss⟩
      have hvUnion : v ∈ TreeSequenceVertexSet Tn ∪
          TreeSequenceVertexSet R.replacementBase.closure := by
        simpa [U.vertexSet] using hv
      rcases Finset.mem_union.mp hvUnion with hvT | hvClosure
      · exact hnotTn (Finset.mem_biUnion.mpr ⟨v, hvT, hmiss⟩)
      · by_cases hvT : v ∈ TreeSequenceVertexSet Tn
        · exact hnotTn (Finset.mem_biUnion.mpr ⟨v, hvT, hmiss⟩)
        · exact hbaseExtra (Finset.mem_biUnion.mpr ⟨v,
            Finset.mem_sdiff.mpr ⟨hv, hvT⟩, hmiss⟩)
    · have hcoreEq : R.replacementBase.core = Tn :=
        R.replacementBase.nonparallel hpe
      have hmTn : beta ∈ TreeMissingColors R.coloring Tn := by
        simpa [hAcore, hcoreEq] using hbetaMissingA
      exact hnotTn hmTn
  have hbetaUnused : ∀ r : Fin T.length, A.length ≤ r.val →
      r.val < A.length + j → R.coloring (T.edge r) ≠ some beta := by
    intro r hrA hrJ hcol
    apply houtside.2.1
    simp only [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, ⟨r, hrA, hrJ, hcol⟩⟩
  change beta ∈ TreeMissingColors R.coloring
    (HierarchyFullTailPrefix C (j - 2)) at initialBetaBefore
  generalize hBdef : HierarchyFullTailPrefix C (j - 2) = B at initialBetaBefore
  have hBlen : B.length = A.length + (j - 2) := by
    clear * - hBdef hA hstrict
    rw [← hBdef]
    have hbound : A.length + (j - 2) ≤ T.length := by omega
    simp only [HierarchyFullTailPrefix, hA, TreeSequencePrefix, min_eq_left hbound]
  have hBT : TreeSequenceInitialSegment B T := by
    clear * - hBdef
    rw [← hBdef]
    refine ⟨Nat.min_le_right _ _, ?_, ?_⟩
    · intro i
      rfl
    · intro i
      rfl
  have hBZ : TreeSequenceInitialSegment B Z :=
    commonPrefix hBT hZT (by rw [hBlen, hZlen]; omega)
  have hYRZ : TreeSequenceInitialSegment YR Z :=
    commonPrefix hYRT hZT (by rw [hYRlen, hZlen]; omega)
  have hbetaB : beta ∈ TreeMissingColors R.coloring B := by
    as_aux_lemma => exact initialBetaBefore
  have hbetaZ : beta ∈ TreeMissingColors R.coloring Z := by
    clear * - hbetaB hBZ
    unfold TreeMissingColors at hbetaB ⊢
    rcases Finset.mem_biUnion.mp hbetaB with ⟨v, hv, hmiss⟩
    exact Finset.mem_biUnion.mpr ⟨v,
      TreeSequenceInitialSegmentVertexSetSubset hBZ hv, hmiss⟩
  have hthetaZ : theta ∈ TreeMissingColors R.coloring Z := by
    exact Finset.mem_biUnion.mpr ⟨YR.vertex (Fin.last YR.length),
      TreeSequenceInitialSegmentVertexSetSubset hYRZ
        (vertexMem YR (Fin.last YR.length)), hthetaYR⟩
  have hne : beta ≠ theta := by
    clear * - hZ hbetaB hthetaYR hBZ hYRZ vertexMem hBlen hYRlen hpathLower
    intro heq
    rw [← heq] at hthetaYR
    unfold TreeMissingColors at hbetaB
    rcases Finset.mem_biUnion.mp hbetaB with ⟨vB, hvB, hmissB⟩
    have hindex : ∃ iB : Fin (B.length + 1), B.vertex iB = vB := by
      simpa only [TreeSequenceVertexSet, Finset.mem_image,
        Finset.mem_univ, true_and] using hvB
    rcases hindex with ⟨iB, hBvertex⟩
    have hZB : Z.vertex (Fin.castLE (Nat.succ_le_succ hBZ.1) iB) = vB :=
      (hBZ.2.1 iB).trans hBvertex
    have hZY : Z.vertex
        (Fin.castLE (Nat.succ_le_succ hYRZ.1) (Fin.last YR.length)) =
          YR.vertex (Fin.last YR.length) := hYRZ.2.1 _
    have hneV : vB ≠ YR.vertex (Fin.last YR.length) := by
      intro heqV
      have hi := Z.vertex_injective (hZB.trans (heqV.trans hZY.symm))
      have hval := congrArg Fin.val hi
      simp only [Fin.val_castLE, Fin.val_last] at hval
      have hBbound : iB.val ≤ B.length := Nat.le_of_lt_succ iB.isLt
      clear * - hval hBbound hBlen hYRlen hpathLower
      omega
    have hdis := hZ
      (TreeSequenceInitialSegmentVertexSetSubset hBZ hvB)
      (TreeSequenceInitialSegmentVertexSetSubset hYRZ
        (vertexMem YR (Fin.last YR.length))) hneV
    exact Finset.disjoint_left.mp hdis hmissB hthetaYR
  exact @helper_continuation_460 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@beta)
      (@hpathLower) (@hpathUpper) (@hvertexMissing) (@R) (@initialBetaLast) (@initialSuffix)
      (@theta) (@hthetaUnstored) (@initialThetaGamma) (@componentData) (@firstMissingVertex) (@Y)
      (@hYdef) (@hA) (@hAT) (@hellSame) (@hell) (@hstrict) (@hZlen) (@hYlen) (@hYT) (@hZT) (@YR)
      (@hYRlen) (@hYRT) (@hYRlast) (@commonPrefix) (@hYZ) (@hZ) (@vertexMem) (@hthetaY)
      (@hthetaYR) (@hthetaRawUnstored) (@hthetaUnused) (@houtside) (@hbetaRawUnstored)
      (@hbetaUnused) (@B) (@hBlen) (@hBT) (@hBZ) (@hYRZ) (@hbetaB) (@hbetaZ) (@hthetaZ) (@hne)
private theorem helper_continuation_286.{u_1, u_2} :
    helperContinuation286Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx beta hpathLower hpathUpper hvertexMissing R
      hconditionOutside initialBetaBefore initialBetaLast initialSuffix theta hthetaUnstored
      initialThetaJ initialThetaGamma componentData firstMissingVertex H q A
  let j := HierarchyPathNumber C.hierarchy
  let ell := HierarchyFullTailLength R.counterexample
  change theta ∈ MissingColors G R.coloring
    ((HierarchyFullTailPrefix C j).vertex
      (Fin.last (HierarchyFullTailPrefix C j).length)) at initialThetaJ
  generalize hYdef : HierarchyFullTailPrefix C j = Y at initialThetaJ
  let Z := HierarchyFullTailPrefix R.counterexample (ell - 1)
  let n : Fin (R.corresponding.replacementETT.rounds + 1) :=
    Fin.last R.corresponding.replacementETT.rounds
  let Tn := R.corresponding.replacementETT.series.data.tree n.castSucc
  let D := HierarchyStoredColorsAt H q
  have sameLast {a b : ℕ}
      (s : Fin (a + 2) → TreeSequence G e0)
      (t : Fin (b + 2) → TreeSequence G e0)
      (u v : TreeSequence G e0) (hab : a = b) (hst : HEq s t)
      (huv : u = v) :
      Fin.cases (motive := fun _ => TreeSequence G e0)
          u (fun i : Fin a => s i.castSucc.succ) (Fin.last a) =
        Fin.cases (motive := fun _ => TreeSequence G e0)
            v (fun i : Fin b => t i.castSucc.succ) (Fin.last b) := by
    clear * - s t u v hab hst huv
    cases hab
    have he : s = t := eq_of_heq hst
    cases he
    cases huv
    rfl
  have hA : HierarchyStarredStage C.hierarchy
      (Fin.last C.hierarchy.dividerCount) = A := by
    exact sameLast C.hierarchy.stage R.counterexample.hierarchy.stage
      base.core R.replacementBase.core R.sameGood.1.2.1
      R.sameGood.1.2.2.1 R.sameGood.1.1
  have hAT : TreeSequenceInitialSegment A T := by
    clear * - H
    have starNext (i : Fin (H.dividerCount + 1)) :
        TreeSequenceInitialSegment (HierarchyStarredStage H i) (H.stage i.succ) :=
      Fin.cases H.coreInsideFirst (fun i => H.nested i.succ) i
    simpa only [Fin.succ_last, H.terminalStage] using starNext (Fin.last H.dividerCount)
  have hellSame : HierarchyFullTailLength C = ell := by
    change T.length - (HierarchyStarredStage C.hierarchy
      (Fin.last C.hierarchy.dividerCount)).length = T.length - A.length
    rw [hA]
  have hell : ell = T.length - A.length := by
    rfl
  have hjlt : j < ell := by rw [← hellSame]; exact hpathUpper
  have hAlen : A.length ≤ T.length := hAT.1
  have hjltT : j < T.length - A.length := by
    simpa [HierarchyFullTailLength, hA] using hpathUpper
  have hstrict : A.length + j < T.length := by
    clear * - hAlen hjltT
    omega
  have hZlen : Z.length = T.length - 1 := by
    clear * - hell hjlt hpathLower hAlen
    have hmin : min (A.length + (ell - 1)) T.length = T.length - 1 := by
      rw [hell]
      omega
    change min (A.length + (ell - 1)) T.length = T.length - 1
    exact hmin
  have hYlen : Y.length = A.length + j := by
    rw [← hYdef]
    have hbound : A.length + j ≤ T.length := Nat.le_of_lt hstrict
    simp only [HierarchyFullTailPrefix, hA, TreeSequencePrefix, min_eq_left hbound]
  have hYT : TreeSequenceInitialSegment Y T := by
    clear * - hYdef
    rw [← hYdef]
    refine ⟨Nat.min_le_right _ _, ?_, ?_⟩
    · intro i
      rfl
    · intro i
      rfl
  have hZT : TreeSequenceInitialSegment Z T := by
    clear * - hZlen
    refine ⟨by rw [hZlen]; omega, ?_, ?_⟩
    · intro i
      rfl
    · intro i
      simp [Z, HierarchyFullTailPrefix, TreeSequencePrefix]
  generalize hYRdef :
    TreeSequencePrefix T (min (A.length + j) T.length)
      (by have hApos := A.positive; have hTpos := T.positive; omega)
      (Nat.min_le_right _ _) = YR
  have hYRlen : YR.length = A.length + j := by
    rw [← hYRdef]
    have hbound : A.length + j ≤ T.length := Nat.le_of_lt hstrict
    change min (A.length + j) T.length = A.length + j
    exact min_eq_left hbound
  have hYRT : TreeSequenceInitialSegment YR T := by
    rw [← hYRdef]
    refine ⟨Nat.min_le_right _ _, ?_, ?_⟩
    · intro i
      rfl
    · intro i
      rfl
  have hYRlast : YR.vertex (Fin.last YR.length) = Y.vertex (Fin.last Y.length) := by
    have hidx : Fin.castLE (Nat.succ_le_succ hYRT.1) (Fin.last YR.length) =
        Fin.castLE (Nat.succ_le_succ hYT.1) (Fin.last Y.length) := by
      apply Fin.ext
      simp [hYRlen, hYlen]
    calc
      YR.vertex (Fin.last YR.length) =
          T.vertex (Fin.castLE (Nat.succ_le_succ hYRT.1) (Fin.last YR.length)) :=
        (hYRT.2.1 _).symm
      _ = T.vertex (Fin.castLE (Nat.succ_le_succ hYT.1) (Fin.last Y.length)) :=
        congrArg T.vertex hidx
      _ = Y.vertex (Fin.last Y.length) := hYT.2.1 _
  have commonPrefix {S U W : TreeSequence G e0}
      (hSW : TreeSequenceInitialSegment S W)
      (hUW : TreeSequenceInitialSegment U W)
      (hlen : S.length ≤ U.length) : TreeSequenceInitialSegment S U := by
    clear * - hSW hUW hlen
    refine ⟨hlen, ?_, ?_⟩
    · intro i
      calc
        U.vertex (Fin.castLE (Nat.succ_le_succ hlen) i) =
            W.vertex (Fin.castLE (Nat.succ_le_succ hUW.1)
              (Fin.castLE (Nat.succ_le_succ hlen) i)) := (hUW.2.1 _).symm
        _ = W.vertex (Fin.castLE (Nat.succ_le_succ hSW.1) i) := by congr 1
        _ = S.vertex i := hSW.2.1 i
    · intro i
      calc
        U.edge (Fin.castLE hlen i) = W.edge (Fin.castLE hUW.1 (Fin.castLE hlen i)) :=
          (hUW.2.2 _).symm
        _ = W.edge (Fin.castLE hSW.1 i) := by congr 1
        _ = S.edge i := hSW.2.2 i
  have hAZ : TreeSequenceInitialSegment A Z :=
    commonPrefix hAT hZT (by rw [hZlen]; have := hAT.1; omega)
  have hYZ : TreeSequenceInitialSegment Y Z :=
    commonPrefix hYT hZT (by rw [hYlen, hZlen]; omega)
  have hZ : ColoredVertexSetElementary G R.coloring (TreeSequenceVertexSet Z) := by
    exact HierarchyCounterexamplePenultimateElementary G k e0
      R.corresponding.replacementInput T R.coloring R.corresponding.replacementETT
      R.replacementBase R.counterexample R.minimumContext.proper
      R.minimumContext.oneEdgeUncolored R.minimumContext.lowerRung
      R.minimumContext.fewerDividers R.minimumContext.lexicographicMinimality
      R.minimumContext.largeMissingSet
  have vertexMem (S : TreeSequence G e0) (i : Fin (S.length + 1)) :
      S.vertex i ∈ TreeSequenceVertexSet S := by
    clear * - S i
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨i, rfl⟩
  have hthetaY : theta ∈ MissingColors G R.coloring
      (Y.vertex (Fin.last Y.length)) := by
    exact initialThetaJ
  have hthetaYR : theta ∈ MissingColors G R.coloring
      (YR.vertex (Fin.last YR.length)) := by
    rw [hYRlast]
    exact hthetaY
  have hthetaNotA : theta ∉ TreeMissingColors R.coloring A := by
    clear * - hZ hAZ hYZ hthetaY vertexMem hYlen hpathLower
    intro hmA
    rcases Finset.mem_biUnion.mp hmA with ⟨vA, hvA, hmva⟩
    have hindex : ∃ iA : Fin (A.length + 1), A.vertex iA = vA := by
      simpa only [TreeSequenceVertexSet, Finset.mem_image,
        Finset.mem_univ, true_and] using hvA
    rcases hindex with ⟨iA, hAvertex⟩
    have hvAMem : vA ∈ TreeSequenceVertexSet Z :=
      TreeSequenceInitialSegmentVertexSetSubset hAZ hvA
    have hvYMem : Y.vertex (Fin.last Y.length) ∈ TreeSequenceVertexSet Z :=
      TreeSequenceInitialSegmentVertexSetSubset hYZ (vertexMem Y (Fin.last Y.length))
    have hne : vA ≠ Y.vertex (Fin.last Y.length) := by
      intro heq
      have hZA : Z.vertex (Fin.castLE (Nat.succ_le_succ hAZ.1) iA) = vA :=
        (hAZ.2.1 iA).trans hAvertex
      have hZY : Z.vertex
          (Fin.castLE (Nat.succ_le_succ hYZ.1) (Fin.last Y.length)) =
            Y.vertex (Fin.last Y.length) := hYZ.2.1 _
      have hi := Z.vertex_injective (hZA.trans (heq.trans hZY.symm))
      have hval := congrArg Fin.val hi
      have hlast : (Fin.last Y.length).val = Y.length := rfl
      have hia : iA.val ≤ A.length := Nat.le_of_lt_succ iA.isLt
      simp only [Fin.val_castLE, hlast] at hval
      clear * - hval hia hYlen hpathLower
      omega
    have hdis := hZ hvAMem hvYMem hne
    exact Finset.disjoint_left.mp hdis hmva hthetaY
  exact @helper_continuation_344 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@beta)
      (@hpathLower) (@hpathUpper) (@hvertexMissing) (@R) (@hconditionOutside)
      (@initialBetaBefore) (@initialBetaLast) (@initialSuffix) (@theta) (@hthetaUnstored)
      (@initialThetaGamma) (@componentData) (@firstMissingVertex) (@Y) (@hYdef) (@hA) (@hAT)
      (@hellSame) (@hell) (@hjlt) (@hstrict) (@hZlen) (@hYlen) (@hYT) (@hZT) (@YR) (@hYRdef)
      (@hYRlen) (@hYRT) (@hYRlast) (@commonPrefix) (@hYZ) (@hZ) (@vertexMem) (@hthetaY)
      (@hthetaYR) (@hthetaNotA)
theorem HierarchySituationThreeDisjointThetaUnstoredOutsideImpossible
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
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      d.theta ∉ HierarchyStoredColorsAt H q)
    (hconditionOutside :
      let H := d.switched.counterexample.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      let A := HierarchyStarredStage H q
      let j := HierarchyPathNumber C.hierarchy
      let n : Fin (d.switched.corresponding.replacementETT.rounds + 1) :=
        Fin.last d.switched.corresponding.replacementETT.rounds
      let Tn := d.switched.corresponding.replacementETT.series.data.tree
        n.castSucc
      let D := HierarchyStoredColorsAt H q
      let Gamma := D.biUnion (d.switched.counterexample.good.gamma q)
      let baseExtraMissing :=
        ((TreeSequenceVertexSet d.switched.replacementBase.core \
            TreeSequenceVertexSet Tn).biUnion
          fun v => MissingColors G d.switched.coloring v)
      let tailUsedThroughJ :=
        (Finset.univ : Finset (Fin k)).filter fun c =>
          exists r : Fin T.length,
            A.length <= r.val ∧ r.val < A.length + j ∧
              d.switched.coloring (T.edge r) = some c
      beta ∉ baseExtraMissing ∧ beta ∉ tailUsedThroughJ ∧
        beta ∉ Gamma ∧ beta ∉ D) :
    False := by
  classical
  have initialBetaBefore : beta ∈ TreeMissingColors d.switched.coloring
      (HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy - 2)) := by
    with_reducible exact d.betaMissingTwoBefore
  have initialThetaJ := d.thetaMissingAtJ
  have initialBetaLast := d.betaMissingTerminal
  have initialThetaGamma := d.thetaOutsideGamma
  have initialSuffix := d.transportedSuffix
  generalize hR : d.switched = R at *
  generalize hTheta : d.theta = theta at *
  clear hR hTheta d
  have componentData (psi : PartialEdgeColoring E k) (a b : Fin k)
      (hne : a ≠ b) (hproper : IsProperEdgeColoring G psi)
      (B : Finset V) (helem : ColoredVertexSetElementary G psi B)
      (u v w : V) (hu : u ∈ B) (hv : v ∈ B) (huv : u ≠ v)
      (hwu : w ≠ u) (hwv : w ≠ v)
      (hau : a ∈ MissingColors G psi u) (hbv : b ∈ MissingColors G psi v)
      (hw : a ∈ MissingColors G psi w ∨ b ∈ MissingColors G psi w)
      (hsame : TwoColorComponent G psi a b (Sum.inl u) =
        TwoColorComponent G psi a b (Sum.inl v)) :
      Disjoint (TwoColorComponent G psi a b (Sum.inl w))
          (TwoColorComponent G psi a b (Sum.inl u)) ∧
        TwoColorPathComponent G psi a b (Sum.inl w) ∧
        (∀ x ∈ B,
          MissingColors G (TwoColorComponentSwap G psi a b (Sum.inl w)) x =
            MissingColors G psi x) := by
    clear * - G psi a b hne hproper B helem u v w hu hv huv hwu hwv hau hbv hw hsame
    let J := TwoColorIncidenceGraph G psi a b
    have leaf (x : V) (hx : a ∈ MissingColors G psi x ∨ b ∈ MissingColors G psi x) :
        (J.neighborSet (Sum.inl x)).Subsingleton := by
      have hd : @SimpleGraph.degree _ J (Sum.inl x) (Fintype.ofFinite _) ≤ 1 := by
        rcases hx with hx | hx
        · exact MissingColorIncidenceEndpoint G psi a b hne hproper x hx
        · have hJ : TwoColorIncidenceGraph G psi b a = J := by
            ext z z'
            cases z <;> cases z' <;> simp [J, TwoColorIncidenceGraph, or_comm]
          rw [← hJ]
          exact MissingColorIncidenceEndpoint G psi b a hne.symm hproper x hx
      let : Fintype (J.neighborSet (Sum.inl x)) := Fintype.ofFinite _
      have hc : Fintype.card (J.neighborSet (Sum.inl x)) ≤ 1 := by
        rw [SimpleGraph.card_neighborSet_eq_degree]
        exact hd
      intro z hz z' hz'
      exact congrArg Subtype.val
        (Fintype.card_le_one_iff.mp hc ⟨z, hz⟩ ⟨z', hz'⟩)
    have hnot : Sum.inl w ∉ TwoColorComponent G psi a b (Sum.inl u) := by
      intro hwC
      obtain ⟨s, t, p, hp, hsupport⟩ :=
        TwoColorComponentSpanningPath G psi a b hproper (Sum.inl u)
      have endpoint (x : V)
          (hxC : Sum.inl x ∈ TwoColorComponent G psi a b (Sum.inl u))
          (hx : a ∈ MissingColors G psi x ∨ b ∈ MissingColors G psi x) :
          Sum.inl x = s ∨ Sum.inl x = t := by
        by_contra hh
        push Not at hh
        have hxP : Sum.inl x ∈ p.support := by
          change Sum.inl x ∈ {z | z ∈ p.support}
          rw [hsupport]
          exact hxC
        exact (hp.isTrail.notMem_support_of_subsingleton_neighborSet
          hh.1 hh.2 (leaf x hx)) hxP
      have huE := endpoint u (by rfl) (Or.inl hau)
      have hvE := endpoint v (by rw [hsame]; rfl) (Or.inr hbv)
      have hwE := endpoint w hwC hw
      rcases huE with huE | huE <;> rcases hvE with hvE | hvE <;>
        rcases hwE with hwE | hwE
      all_goals first
        | exact huv (Sum.inl.inj (huE.trans hvE.symm))
        | exact hwu (Sum.inl.inj (hwE.trans huE.symm))
        | exact hwv (Sum.inl.inj (hwE.trans hvE.symm))
    have hdis : Disjoint (TwoColorComponent G psi a b (Sum.inl w))
        (TwoColorComponent G psi a b (Sum.inl u)) := by
      rcases TwoColorComponentsDisjoint G psi a b (Sum.inl w) (Sum.inl u) with hh | hh
      · exact (hnot (by rw [← hh]; rfl)).elim
      · exact hh
    refine ⟨hdis, ⟨hne, Sum.inl w, by rfl, leaf w hw⟩, ?_⟩
    let Q := TwoColorComponent G psi a b (Sum.inl w)
    let tau := TwoColorComponentSwap G psi a b (Sum.inl w)
    have huQ : Sum.inl u ∉ Q := by
      intro hh
      exact Set.disjoint_left.mp hdis hh (by rfl)
    have hvQ : Sum.inl v ∉ Q := by
      intro hh
      exact Set.disjoint_left.mp hdis hh (by rw [hsame]; rfl)
    obtain ⟨outside, -, -, unaffected⟩ :=
      TwoColorComponentSwapMissingBehavior G psi a b hne hproper (Sum.inl w)
    have edgeIn {x : V} {e : E} (hx : Sum.inl x ∈ Q)
        (hi : Incident G x e) (hc : psi e = some a ∨ psi e = some b) :
        Sum.inr e ∈ Q := by
      change J.connectedComponentMk (Sum.inl x) = J.connectedComponentMk (Sum.inl w) at hx
      change J.connectedComponentMk (Sum.inr e) = J.connectedComponentMk (Sum.inl w)
      have ha : J.Adj (Sum.inr e) (Sum.inl x) := ⟨hi, hc⟩
      exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj ha).trans hx
    intro x hx
    by_cases hxQ : Sum.inl x ∈ Q
    · have haNot : a ∉ MissingColors G psi x := by
        intro ha
        by_cases hxu : x = u
        · exact huQ (hxu ▸ hxQ)
        · exact Finset.disjoint_left.mp (helem hx hu hxu) ha hau
      have hbNot : b ∉ MissingColors G psi x := by
        intro hb
        by_cases hxv : x = v
        · exact hvQ (hxv ▸ hxQ)
        · exact Finset.disjoint_left.mp (helem hx hv hxv) hb hbv
      have present (c : Fin k) (hc : c ∉ MissingColors G psi x) :
          ∃ e, Incident G x e ∧ psi e = some c := by
        simpa [MissingColors, PresentColors] using hc
      obtain ⟨ea, hia, hca⟩ := present a haNot
      obtain ⟨eb, hib, hcb⟩ := present b hbNot
      have haNew : a ∉ MissingColors G tau x := by
        have heQ := edgeIn hxQ hib (Or.inr hcb)
        have hcol : tau eb = some a := by
          simp [tau, TwoColorComponentSwap, show Sum.inr eb ∈
            TwoColorComponent G psi a b (Sum.inl w) from heQ, hcb, hne.symm]
        exact fun hm => (Finset.mem_sdiff.mp hm).2
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, eb, hib, hcol⟩)
      have hbNew : b ∉ MissingColors G tau x := by
        have heQ := edgeIn hxQ hia (Or.inl hca)
        have hcol : tau ea = some b := by
          simp [tau, TwoColorComponentSwap, show Sum.inr ea ∈
            TwoColorComponent G psi a b (Sum.inl w) from heQ, hca]
        exact fun hm => (Finset.mem_sdiff.mp hm).2
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ea, hia, hcol⟩)
      ext c
      by_cases hca : c = a
      · subst c
        exact iff_of_false haNew haNot
      · by_cases hcb : c = b
        · subst c
          exact iff_of_false hbNew hbNot
        · exact unaffected x c hca hcb
    · exact outside x hxQ
  have firstMissingVertex (psi : PartialEdgeColoring E k) (U : TreeSequence G e0)
      (i : Fin (U.length + 1)) (c : Fin k)
      (hc : c ∈ MissingColors G psi (U.vertex i)) :
      c ∈ MissingColors G psi (U.vertex (HierarchyFirstMissingPosition psi U c)) ∧
        (HierarchyFirstMissingPosition psi U c).val ≤ i.val := by as_aux_lemma =>
    clear * - psi U i c hc
    let candidates := Finset.univ.filter fun r : Fin (U.length + 1) =>
      c ∈ MissingColors G psi (U.vertex r)
    have hi : i ∈ candidates := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
    have hn : candidates.Nonempty := ⟨i, hi⟩
    unfold HierarchyFirstMissingPosition
    rw [dite_eq_left hn]
    exact ⟨(Finset.mem_filter.mp (Finset.min'_mem candidates hn)).2,
      Finset.min'_le candidates i hi⟩
  let H := R.counterexample.hierarchy
  let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
  let A := HierarchyStarredStage H q
  exact @helper_continuation_286 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@beta)
      (@hpathLower) (@hpathUpper) (@hvertexMissing) (@R) (@hconditionOutside)
      (@initialBetaBefore) (@initialBetaLast) (@initialSuffix) (@theta) (@hthetaUnstored)
      (@initialThetaJ) (@initialThetaGamma) (@componentData) (@firstMissingVertex)
end GoldbergSeymour

end
