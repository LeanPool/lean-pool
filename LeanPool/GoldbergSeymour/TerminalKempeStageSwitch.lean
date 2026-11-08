/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyTreeFacts

public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentFacts

public import LeanPool.GoldbergSeymour.TreeSequenceFirstMissingPositionInvariant


public import LeanPool.GoldbergSeymour.SharedFacts.TerminalKempeStageSwitch


public import LeanPool.GoldbergSeymour.HierarchyReplacementPresentationTrans
public import LeanPool.GoldbergSeymour.ElementaryTerminalComponent
public import LeanPool.GoldbergSeymour.ChangeLemma
public import LeanPool.GoldbergSeymour.StableChangeCasesOneTwoSplitTail

/-!
# P2963_T1_Terminal Kempe Stage Switch

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev helperContinuation1318Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (hTlen : (2 : ℕ) ≤
        T.length) (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (X :
        TreeSequence G e0) (a b eta : Fin k), eta ∈ HierarchyStoredColorsAt
        R.counterexample.hierarchy (Fin.last R.counterexample.hierarchy.dividerCount) → a ∈
        R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta →
        (↑(HierarchyFirstMissingPosition R.coloring T eta) : ℕ) ≤ X.length → a ∈ MissingColors G
        R.coloring (T.vertex (Fin.last T.length)) ∨ b ∈ MissingColors G R.coloring (T.vertex
        (Fin.last T.length)) →
    ∀ (jb : Fin ((TreeSequencePrefix T (T.length - (1 : ℕ)) (Decidable.byContradiction fun (a :
        ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) => (
    by omega
    )) (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) => (
    by omega
    ))).length + (1 : ℕ))), (↑jb : ℕ) ≤ X.length →
    let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount); (
    ∀ {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Y → TreeSequenceInitialSegment Y Z
        → TreeSequenceInitialSegment X Z) → (
    ∀ {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Z → TreeSequenceInitialSegment Y Z
        → X.length ≤ Y.length → TreeSequenceInitialSegment X Y) → (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount) = A) →
    let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ))
        (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) => (
    by omega
    )) (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) => (
    by omega
    )); TreeSequenceInitialSegment A X → A.length < X.length → TreeSequenceInitialSegment X B →
        A.length < (↑jb : ℕ) → b ∈ MissingColors G R.coloring (B.vertex jb) → (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → R.coloring (T.edge t) ≠ some
        a) → (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → R.coloring (T.edge t) = some
        b → TreeIncidentEdge (R.corresponding.replacementETT.series.data.tree (Fin.last
        R.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧ b ∈ TashkinovStoredColors
        R.corresponding.replacementETT.series.data (Fin.last
        R.corresponding.replacementETT.rounds)) →
    ∀ (hBT : TreeSequenceInitialSegment B T) (hAB : TreeSequenceInitialSegment A B), X.length ≤
        T.length - (1 : ℕ) → (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyFullTailPrefix R.counterexample (HierarchyFullTailLength R.counterexample - (1 :
        ℕ)) = B) → (
    ∀ (U : TreeSequence G e0) (j : Fin (U.length + (1 : ℕ))), U.vertex j ∈ TreeSequenceVertexSet
        U) → (
    ∀ (psi tau : PartialEdgeColoring E k), (
    ∀ v ∈ TreeSequenceVertexSet B, MissingColors G tau v = MissingColors G psi v) →
    ∀ (c : Fin k), HierarchyFirstMissingPosition tau T c = HierarchyFirstMissingPosition psi T c)
        →
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let n : Fin (R.corresponding.replacementETT.rounds + (1 : ℕ)) := Fin.last
        R.corresponding.replacementETT.rounds;
    let Tn : TreeSequence G e0 := R.corresponding.replacementETT.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors R.corresponding.replacementETT.series.data n;
        (H.dividerCount ≠ (0 : ℕ) → HierarchyStarredStage H q = H.stage (⟨H.dividerCount,
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) → TreeSequenceInitialSegment Tn A → (0 : ℕ) <
        H.dividerCount ∧ a ∈ TreeMissingColors R.coloring (H.stage (⟨H.dividerCount,
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) ∨ H.dividerCount = (0 : ℕ) ∧ a ∈ TreeMissingColors
        R.coloring Tn → b ∉ TreeMissingColors R.coloring A → a ≠ b → b ∈ TreeMissingColors
        R.coloring B → a ∈ TreeMissingColors R.coloring B →
    ∀ (iaLe : (↑(HierarchyFirstMissingPosition R.coloring T a) : ℕ) ≤ A.length),
        (↑(HierarchyFirstMissingPosition R.coloring T b) : ℕ) = (↑jb : ℕ) →
    let ja : Fin (B.length + (1 : ℕ)) := (⟨(↑(HierarchyFirstMissingPosition R.coloring T a) : ℕ),
    by
     have this : A.length ≤ B.length := hAB.1; omega
    ⟩ : Fin (B.length + (1 : ℕ))); Fin.castLE (Nat.succ_le_succ hBT.1) ja =
        HierarchyFirstMissingPosition R.coloring T a → Fin.castLE (Nat.succ_le_succ hBT.1) jb =
        HierarchyFirstMissingPosition R.coloring T b → a ∈ MissingColors G R.coloring (B.vertex
        ja) → (
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    have q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    have n : Fin (R.corresponding.replacementETT.rounds + (1 : ℕ)) := Fin.last
        R.corresponding.replacementETT.rounds;
    have A : TreeSequence G e0 := HierarchyStarredStage H q;
    have Tnq : TreeSequence G e0 := H.stage (⟨H.dividerCount,
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)));
    have Tn : TreeSequence G e0 := R.corresponding.replacementETT.series.data.tree n.castSucc;
    have Dn : Finset (Fin k) := TashkinovStoredColors R.corresponding.replacementETT.series.data
        n;
    have Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q;
    have va : V := T.vertex (HierarchyFirstMissingPosition R.coloring T a);
    have vb : V := T.vertex (HierarchyFirstMissingPosition R.coloring T b);
    have sameComponent : Prop := TwoColorComponent G R.coloring a b (Sum.inl va) =
        TwoColorComponent G R.coloring a b (Sum.inl vb); ((0 : ℕ) < H.dividerCount ∧ (a ∈
        TreeMissingColors R.coloring Tnq ∨ Disjoint { a, b } Dnq) → sameComponent) ∧
        (H.dividerCount = (0 : ℕ) ∧ (a ∈ TreeMissingColors R.coloring Tn ∨ Disjoint { a, b } Dn) →
        sameComponent) ∧ (a ∈ TreeMissingColors R.coloring A ∧ TreeColorSetClosed G R.coloring A
        { a } → sameComponent ∧ TreeInterchangeable G A R.coloring a b)) → TwoColorPathComponent G
        R.coloring a b (Sum.inl (T.vertex (Fin.last T.length))) → (
    ∀ x ∈ TreeSequenceVertexSet B, MissingColors G (TwoColorComponentSwap G R.coloring a b
        (Sum.inl (T.vertex (Fin.last T.length)))) x = MissingColors G R.coloring x) →
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G R.coloring a b (Sum.inl
        (T.vertex (Fin.last T.length))); IsOneEdgeUncolored sigma e0 → (0 : ℕ) < H.dividerCount ∧
        a ∈ TreeMissingColors R.coloring (H.stage (⟨H.dividerCount,
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) ∨ H.dividerCount = (0 : ℕ) ∧ (a ∈ TreeMissingColors
        R.coloring Tn ∨ a ∈ TreeMissingColors R.coloring (HierarchyStarredStage H q) ∧ a ∉ Dn ∧ b
        ∉ Dn) → Disjoint (TwoColorComponent G R.coloring a b (Sum.inl (T.vertex (Fin.last
        T.length)))) (TwoColorComponent G R.coloring a b (Sum.inl (T.vertex
        (HierarchyFirstMissingPosition R.coloring T a)))) → (
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    have n : Fin (R.corresponding.replacementETT.rounds + (1 : ℕ)) := Fin.last
        R.corresponding.replacementETT.rounds;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    have Tnq : TreeSequence G e0 := H.stage (⟨H.dividerCount,
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)));
    have Tn : TreeSequence G e0 := R.corresponding.replacementETT.series.data.tree n.castSucc;
    have Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q; HierarchyWeaklyStable H q sigma ∧
        ModColoring R.corresponding.replacementETT sigma ∧ (A = Tn ∨
    ∃ (inputA : PartialEdgeColoring E k) (ettA : ExtendedTashkinovTree G k e0 inputA A sigma),
        MaximumProperty ettA) ∧ ((0 : ℕ) < H.dividerCount →
    ∃ (inputA : PartialEdgeColoring E k) (ettA : ExtendedTashkinovTree G k e0 inputA A sigma)
        (baseA : HierarchyBase ettA sigma) (K : TashkinovHierarchy ettA baseA) (goodA :
        GoodHierarchy K), MaximumProperty ettA ∧ ettA.series.data.kind (Fin.last ettA.rounds) =
        R.corresponding.replacementETT.series.data.kind (Fin.last
        R.corresponding.replacementETT.rounds) ∧
    ∃ (hcount : K.dividerCount + (1 : ℕ) = H.dividerCount), baseA.core = R.replacementBase.core ∧
        baseA.closure = R.replacementBase.closure ∧ (
    ∀ (j : Fin (K.dividerCount + (2 : ℕ))), K.stage j = H.stage (⟨(↑j : ℕ),
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) ∧ (
    ∀ (j : Fin (K.dividerCount + (1 : ℕ))),
    have jH : Fin (H.dividerCount + (1 : ℕ)) := (⟨(↑j : ℕ),
    by omega
    ⟩ : Fin (H.dividerCount + (1 : ℕ))); HierarchyStoredColorsAt K j = HierarchyStoredColorsAt H
        jH ∧
    ∀ eta ∈ HierarchyStoredColorsAt K j, goodA.gamma j eta = R.counterexample.good.gamma jH eta) ∧
        TreeColorSetMinusClosed G sigma Tnq (Dnq.biUnion (R.counterexample.good.gamma
        (⟨R.counterexample.hierarchy.dividerCount - (1 : ℕ),
    by omega
    ⟩ : Fin (R.counterexample.hierarchy.dividerCount + (1 : ℕ))))))) →
    ∃ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), (
    ∀ v ∈ TreeSequenceVertexSet (TreeSequencePrefix T (T.length - (1 : ℕ))
        (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) => (
    by omega
    )) (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) => (
    by omega
    ))), MissingColors G S.coloring v = MissingColors G R.coloring v) ∧ (
    ∀ (t : Fin T.length), (HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount)).length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → S.coloring (T.edge t)
        = R.coloring (T.edge t)) ∧ (a ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length))
        → b ∈ MissingColors G S.coloring (T.vertex (Fin.last T.length))) ∧ (b ∈ MissingColors G
        R.coloring (T.vertex (Fin.last T.length)) → a ∈ MissingColors G S.coloring (T.vertex
        (Fin.last T.length)))

private abbrev helperContinuation1225Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (hTlen : (2 : ℕ) ≤
        T.length) (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (X :
        TreeSequence G e0) (a b eta : Fin k), eta ∈ HierarchyStoredColorsAt
        R.counterexample.hierarchy (Fin.last R.counterexample.hierarchy.dividerCount) → a ∈
        R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta →
        (↑(HierarchyFirstMissingPosition R.coloring T eta) : ℕ) ≤ X.length → a ∈ MissingColors G
        R.coloring (T.vertex (Fin.last T.length)) ∨ b ∈ MissingColors G R.coloring (T.vertex
        (Fin.last T.length)) →
    ∀ (jb : Fin ((TreeSequencePrefix T (T.length - (1 : ℕ)) (Decidable.byContradiction fun (a :
        ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) => (
    by omega
    )) (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) => (
    by omega
    ))).length + (1 : ℕ))), (↑jb : ℕ) ≤ X.length → (
    ∀ {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Y → TreeSequenceInitialSegment Y Z
        → TreeSequenceInitialSegment X Z) → (
    ∀ {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Z → TreeSequenceInitialSegment Y Z
        → X.length ≤ Y.length → TreeSequenceInitialSegment X Y) → (
    ∀ (psi : PartialEdgeColoring E k) (a b : Fin k), a ≠ b → IsProperEdgeColoring G psi →
    ∀ (B : Finset V), ColoredVertexSetElementary G psi B →
    ∀ (u v w : V), u ∈ B → v ∈ B → u ≠ v → w ≠ u → w ≠ v → a ∈ MissingColors G psi u → b ∈
        MissingColors G psi v → a ∈ MissingColors G psi w ∨ b ∈ MissingColors G psi w →
        TwoColorComponent G psi a b (Sum.inl u) = TwoColorComponent G psi a b (Sum.inl v) →
        Disjoint (TwoColorComponent G psi a b (Sum.inl w)) (TwoColorComponent G psi a b (Sum.inl
        u)) ∧ TwoColorPathComponent G psi a b (Sum.inl w) ∧
    ∀ x ∈ B, MissingColors G (TwoColorComponentSwap G psi a b (Sum.inl w)) x = MissingColors G psi
        x) → (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount) = (HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount) : TreeSequence G e0)) →
    let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ))
        (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) => (
    by omega
    )) (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) => (
    by omega
    )); TreeSequenceInitialSegment (HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount) : TreeSequence G e0) X → (HierarchyStarredStage C.hierarchy
        (Fin.last C.hierarchy.dividerCount) : TreeSequence G e0).length < X.length →
        TreeSequenceInitialSegment X B → (HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount) : TreeSequence G e0).length < (↑jb : ℕ) → b ∈ MissingColors G
        R.coloring (B.vertex jb) → (
    ∀ (t : Fin T.length), (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) :
        TreeSequence G e0).length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → R.coloring (T.edge t) ≠ some
        a) → (
    ∀ (t : Fin T.length), (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) :
        TreeSequence G e0).length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → R.coloring (T.edge t) = some
        b → TreeIncidentEdge (R.corresponding.replacementETT.series.data.tree (Fin.last
        R.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧ b ∈ TashkinovStoredColors
        R.corresponding.replacementETT.series.data (Fin.last
        R.corresponding.replacementETT.rounds)) → TreeSequenceInitialSegment B T →
        TreeSequenceInitialSegment (HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount) : TreeSequence G e0) B → X.length ≤ T.length - (1 : ℕ) → (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyFullTailPrefix R.counterexample (HierarchyFullTailLength R.counterexample - (1 :
        ℕ)) = B) → (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        ColoredVertexSetElementary G R.coloring (TreeSequenceVertexSet B)) → (
    ∀ (U : TreeSequence G e0) (j : Fin (U.length + (1 : ℕ))), U.vertex j ∈ TreeSequenceVertexSet
        U) → (
    ∀ (psi : PartialEdgeColoring E k) (c : Fin k), (↑(HierarchyFirstMissingPosition psi T c) : ℕ)
        < T.length → c ∈ MissingColors G psi (T.vertex (HierarchyFirstMissingPosition psi T c))) →
        (
    ∀ (psi tau : PartialEdgeColoring E k), (
    ∀ v ∈ TreeSequenceVertexSet B, MissingColors G tau v = MissingColors G psi v) →
    ∀ (c : Fin k), HierarchyFirstMissingPosition tau T c = HierarchyFirstMissingPosition psi T c)
        → ((R.counterexample.hierarchy : TashkinovHierarchy R.corresponding.replacementETT
        R.replacementBase).dividerCount ≠ (0 : ℕ) → HierarchyStarredStage
        (R.counterexample.hierarchy : TashkinovHierarchy R.corresponding.replacementETT
        R.replacementBase) (Fin.last (R.counterexample.hierarchy : TashkinovHierarchy
        R.corresponding.replacementETT R.replacementBase).dividerCount : Fin
        ((R.counterexample.hierarchy : TashkinovHierarchy R.corresponding.replacementETT
        R.replacementBase).dividerCount + (1 : ℕ))) = (R.counterexample.hierarchy :
        TashkinovHierarchy R.corresponding.replacementETT R.replacementBase).stage
        (⟨(R.counterexample.hierarchy : TashkinovHierarchy R.corresponding.replacementETT
        R.replacementBase).dividerCount,
    by omega
    ⟩ : Fin ((R.counterexample.hierarchy : TashkinovHierarchy R.corresponding.replacementETT
        R.replacementBase).dividerCount + (2 : ℕ)))) → TreeSequenceInitialSegment
        (R.corresponding.replacementETT.series.data.tree (Fin.last
        R.corresponding.replacementETT.rounds : Fin (R.corresponding.replacementETT.rounds + (1 :
        ℕ))).castSucc : TreeSequence G e0) (HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount) : TreeSequence G e0) → (0 : ℕ) < (R.counterexample.hierarchy :
        TashkinovHierarchy R.corresponding.replacementETT R.replacementBase).dividerCount ∧ a ∈
        TreeMissingColors R.coloring ((R.counterexample.hierarchy : TashkinovHierarchy
        R.corresponding.replacementETT R.replacementBase).stage (⟨(R.counterexample.hierarchy :
        TashkinovHierarchy R.corresponding.replacementETT R.replacementBase).dividerCount,
    by omega
    ⟩ : Fin ((R.counterexample.hierarchy : TashkinovHierarchy R.corresponding.replacementETT
        R.replacementBase).dividerCount + (2 : ℕ)))) ∨ (R.counterexample.hierarchy :
        TashkinovHierarchy R.corresponding.replacementETT R.replacementBase).dividerCount = (0 :
        ℕ) ∧ a ∈ TreeMissingColors R.coloring (R.corresponding.replacementETT.series.data.tree
        (Fin.last R.corresponding.replacementETT.rounds : Fin
        (R.corresponding.replacementETT.rounds + (1 : ℕ))).castSucc : TreeSequence G e0) → b ∉
        TreeMissingColors R.coloring (HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount) : TreeSequence G e0) → a ≠ b → b ∈ TreeMissingColors R.coloring
        B → a ∈ TreeMissingColors R.coloring B → (↑(HierarchyFirstMissingPosition R.coloring T a)
        : ℕ) ≤ (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) :
        TreeSequence G e0).length → (↑(HierarchyFirstMissingPosition R.coloring T b) : ℕ) = (↑jb :
        ℕ) →
    ∃ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), (
    ∀ v ∈ TreeSequenceVertexSet (TreeSequencePrefix T (T.length - (1 : ℕ))
        (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) => (
    by omega
    )) (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) => (
    by omega
    ))), MissingColors G S.coloring v = MissingColors G R.coloring v) ∧ (
    ∀ (t : Fin T.length), (HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount)).length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → S.coloring (T.edge t)
        = R.coloring (T.edge t)) ∧ (a ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length))
        → b ∈ MissingColors G S.coloring (T.vertex (Fin.last T.length))) ∧ (b ∈ MissingColors G
        R.coloring (T.vertex (Fin.last T.length)) → a ∈ MissingColors G S.coloring (T.vertex
        (Fin.last T.length)))

private theorem helper_routes_498.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (hTlen : (2 : ℕ) ≤
        T.length) (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (X :
        TreeSequence G e0) (a b _ : Fin k) (_ : Fin ((TreeSequencePrefix T (T.length - (1 : ℕ))
        (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) =>
    by
                  omega
    ) (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) =>
    by
                  omega
    )).length + (1 : ℕ))),
    let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount); (
    ∀ {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Y → TreeSequenceInitialSegment Y Z
        → TreeSequenceInitialSegment X Z) → (
    ∀ {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Z → TreeSequenceInitialSegment Y Z
        → X.length ≤ Y.length → TreeSequenceInitialSegment X Y) →
    let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ))
        (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) =>
    by omega
    ) (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) =>
    by omega
    ); TreeSequenceInitialSegment A X →
    ∀ (hAXlt : A.length < X.length), TreeSequenceInitialSegment X B →
    ∀ (_ : TreeSequenceInitialSegment B T) (_ : TreeSequenceInitialSegment A B),
    let n : Fin (R.corresponding.replacementETT.rounds + (1 : ℕ)) := Fin.last
        R.corresponding.replacementETT.rounds;
    let Tn : TreeSequence G e0 := R.corresponding.replacementETT.series.data.tree n.castSucc;
        TreeSequenceInitialSegment Tn A →
    ∀ (_ : (↑(HierarchyFirstMissingPosition R.coloring T a) : ℕ) ≤ A.length), (
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    have q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    have n : Fin (R.corresponding.replacementETT.rounds + (1 : ℕ)) := Fin.last
        R.corresponding.replacementETT.rounds;
    have A : TreeSequence G e0 := HierarchyStarredStage H q;
    have Tnq : TreeSequence G e0 := H.stage (⟨H.dividerCount,
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)));
    have Tn : TreeSequence G e0 := R.corresponding.replacementETT.series.data.tree n.castSucc;
    have Dn : Finset (Fin k) := TashkinovStoredColors R.corresponding.replacementETT.series.data
        n;
    have Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q;
    have va : V := T.vertex (HierarchyFirstMissingPosition R.coloring T a);
    have vb : V := T.vertex (HierarchyFirstMissingPosition R.coloring T b);
    have sameComponent : Prop := TwoColorComponent G R.coloring a b (Sum.inl va) =
        TwoColorComponent G R.coloring a b (Sum.inl vb); ((0 : ℕ) < H.dividerCount ∧ (a ∈
        TreeMissingColors R.coloring Tnq ∨ Disjoint { a, b } Dnq) → sameComponent) ∧
        (H.dividerCount = (0 : ℕ) ∧ (a ∈ TreeMissingColors R.coloring Tn ∨ Disjoint { a, b } Dn) →
        sameComponent) ∧ (a ∈ TreeMissingColors R.coloring A ∧ TreeColorSetClosed G R.coloring A
        { a } → sameComponent ∧ TreeInterchangeable G A R.coloring a b)) → (
    ∀ x ∈ TreeSequenceVertexSet B, MissingColors G (TwoColorComponentSwap G R.coloring a b
        (Sum.inl (T.vertex (Fin.last T.length)))) x = MissingColors G R.coloring x) →
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G R.coloring a b (Sum.inl
        (T.vertex (Fin.last T.length))); TreeSequenceInitialSegment X T →
    let XM : TreeSequence G e0 := TreeSequencePrefix X (X.length - (1 : ℕ)) (
    have this : (1 : ℕ) ≤ A.length := A.positive; Decidable.byContradiction fun (a_1 : ¬(1 : ℕ) ≤
        X.length - (1 : ℕ)) =>
    by omega
    ) (Decidable.byContradiction fun (a_1 : ¬X.length - (1 : ℕ) ≤ X.length) =>
    by omega
    ); TreeSequenceInitialSegment XM X → (
    ∀ (t : Fin X.length), Tn.length ≤ (↑t : ℕ) → sigma (X.edge t) = R.coloring (X.edge t)) →
        (R.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence sigma Tn X ∨
        (R.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.SE ∨
        R.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.RE) ∧
    ∃ (f : E) (seed : TreeSequence G e0),
        R.corresponding.replacementETT.series.data.connectingEdges n = { f } ∧
        TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence sigma seed X) ∧
        TashkinovAugmentationSequence R.coloring X T := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hTlen R X a b eta jb A trans common B hAX
      hAXlt hXB hBT hAB n Tn hTnA iaLe change hmissing sigma hXT XM hXMX prefixFixed
  rcases P2813_T1_TerminalRoute G k e0 R.corresponding.replacementInput T R.coloring
      R.corresponding.replacementETT with ⟨hp, hseq⟩ |
      ⟨hp, f, seed, hedges, hseed, hincident, hcontrol, hseq⟩
  · have hsourceX := trans hTnA hAX
    have hpre := TashkinovAugmentationSequenceRestrict R.coloring Tn X T hseq hsourceX hXT
    refine ⟨Or.inl ⟨hp, ?_⟩,
      TashkinovAugmentationSequenceSuffix R.coloring Tn X T hseq hsourceX hXT⟩
    exact TashkinovAugmentationSequenceColoringTransport R.coloring sigma Tn XM X
      hpre hXMX (by dsimp [XM, TreeSequencePrefix]; have := X.positive; omega) prefixFixed
      (fun v hv => hmissing v (TreeSequenceInitialSegmentVertexSetSubset
        (trans hXMX hXB) hv))
  · have hseedX := common
      (TashkinovAugmentationSequenceInitialSegment R.coloring seed T hseq) hXT
      (by have hl := hseed.1; have := hTnA.1; change seed.length = Tn.length + 1 at hl; omega)
    have hpre := TashkinovAugmentationSequenceRestrict R.coloring seed X T hseq hseedX hXT
    refine ⟨Or.inr ⟨hp, f, seed, hedges, hseed, ?_⟩,
      TashkinovAugmentationSequenceSuffix R.coloring seed X T hseq hseedX hXT⟩
    exact TashkinovAugmentationSequenceColoringTransport R.coloring sigma seed XM X
      hpre hXMX (by dsimp [XM, TreeSequencePrefix]; have := X.positive; omega)
      (fun t ht =>
          prefixFixed t (by have hl := hseed.1; change seed.length = Tn.length + 1 at hl; omega))
      (fun v hv => hmissing v (TreeSequenceInitialSegmentVertexSetSubset
        (trans hXMX hXB) hv))

private theorem helper_gammaCut_539.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (hTlen : (2 : ℕ) ≤
        T.length) (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (X :
        TreeSequence G e0) (a b eta : Fin k), eta ∈ HierarchyStoredColorsAt
        R.counterexample.hierarchy (Fin.last R.counterexample.hierarchy.dividerCount) → a ∈
        R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta →
        (↑(HierarchyFirstMissingPosition R.coloring T eta) : ℕ) ≤ X.length →
    ∀ (_ : Fin ((TreeSequencePrefix T (T.length - (1 : ℕ)) (Decidable.byContradiction fun (a : ¬(1
        : ℕ) ≤ T.length - (1 : ℕ)) =>
    by
                  omega
    ) (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) =>
    by
                  omega
    )).length + (1 : ℕ))),
    let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount); (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount) = A) →
    let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ))
        (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) =>
    by omega
    ) (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) =>
    by omega
    ); TreeSequenceInitialSegment B T → TreeSequenceInitialSegment A B →
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let n : Fin (R.corresponding.replacementETT.rounds + (1 : ℕ)) := Fin.last
        R.corresponding.replacementETT.rounds;
    let Tn : TreeSequence G e0 := R.corresponding.replacementETT.series.data.tree n.castSucc;
        TreeSequenceInitialSegment Tn A → (0 : ℕ) < H.dividerCount ∧ a ∈ TreeMissingColors
        R.coloring (H.stage (⟨H.dividerCount,
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) ∨ H.dividerCount = (0 : ℕ) ∧ a ∈ TreeMissingColors
        R.coloring Tn → b ∉ TreeMissingColors R.coloring A → (↑(HierarchyFirstMissingPosition
        R.coloring T a) : ℕ) ≤ A.length → (
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    have q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    have n : Fin (R.corresponding.replacementETT.rounds + (1 : ℕ)) := Fin.last
        R.corresponding.replacementETT.rounds;
    have A : TreeSequence G e0 := HierarchyStarredStage H q;
    have Tnq : TreeSequence G e0 := H.stage (⟨H.dividerCount,
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)));
    have Tn : TreeSequence G e0 := R.corresponding.replacementETT.series.data.tree n.castSucc;
    have Dn : Finset (Fin k) := TashkinovStoredColors R.corresponding.replacementETT.series.data
        n;
    have Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q;
    have va : V := T.vertex (HierarchyFirstMissingPosition R.coloring T a);
    have vb : V := T.vertex (HierarchyFirstMissingPosition R.coloring T b);
    have sameComponent : Prop := TwoColorComponent G R.coloring a b (Sum.inl va) =
        TwoColorComponent G R.coloring a b (Sum.inl vb); ((0 : ℕ) < H.dividerCount ∧ (a ∈
        TreeMissingColors R.coloring Tnq ∨ Disjoint { a, b } Dnq) → sameComponent) ∧
        (H.dividerCount = (0 : ℕ) ∧ (a ∈ TreeMissingColors R.coloring Tn ∨ Disjoint { a, b } Dn) →
        sameComponent) ∧ (a ∈ TreeMissingColors R.coloring A ∧ TreeColorSetClosed G R.coloring A
        { a } → sameComponent ∧ TreeInterchangeable G A R.coloring a b)) →
    ∀ eta' ∈ HierarchyStoredColorsAt H q, a ∈ R.counterexample.good.gamma q eta' ∨ b ∈
        R.counterexample.good.gamma q eta' → (↑(HierarchyFirstMissingPosition R.coloring T eta') :
        ℕ) ≤ X.length := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hTlen R X a b eta heta haGamma hetaCut jb A
      starEq B hBT hAB H q n Tn hTnA stageCase hbOutside iaLe change eta' heta' hh
  rcases hh with hh | hh
  · have he : eta' = eta := by
      by_contra hn
      exact Finset.disjoint_left.mp
        (R.counterexample.good.disjointPairs q eta' eta heta' heta hn) hh haGamma
    simpa only [he] using hetaCut
  · have hm := (Finset.mem_sdiff.mp (R.counterexample.good.avoidance q eta' heta' hh)).1
    have hmb : b ∈ TreeMissingColors R.coloring A := by
      rcases stageCase with ⟨hq, _⟩ | ⟨hq, _⟩
      · have hhq : H.dividerCount ≠ 0 := by omega
        unfold HierarchyStageMissingColors at hm
        dsimp only at hm
        obtain hz | ⟨i, hi⟩ := Fin.eq_zero_or_eq_succ q
        · exact (hhq (by simpa [q] using congrArg Fin.val hz)).elim
        · rw [hi] at hm
          simp only [Fin.cases_succ] at hm
          have he : HierarchyStarredStage H q = H.stage i.succ.castSucc := by
            change Fin.cases (motive := fun _ => TreeSequence G e0)
              R.replacementBase.core (fun i => H.stage i.succ.castSucc) q = _
            rw [hi]
            rfl
          rw [← starEq R, he]
          exact hm
      · have hmT : b ∈ TreeMissingColors R.coloring Tn := by
          simpa [HierarchyStageMissingColors, q, hq, Fin.last, Tn, n] using hm
        obtain ⟨v, hv, hc⟩ := Finset.mem_biUnion.mp hmT
        exact Finset.mem_biUnion.mpr ⟨v, TreeSequenceInitialSegmentVertexSetSubset hTnA hv, hc⟩
    exact (hbOutside hmb).elim

private theorem helper_stageCase_765.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (hTlen : (2 : ℕ) ≤
        T.length) (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (_ :
        TreeSequence G e0) (a eta : Fin k), eta ∈ HierarchyStoredColorsAt
        R.counterexample.hierarchy (Fin.last R.counterexample.hierarchy.dividerCount) → a ∈
        R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta →
    ∀ (_ : Fin ((TreeSequencePrefix T (T.length - (1 : ℕ)) (Decidable.byContradiction fun (a : ¬(1
        : ℕ) ≤ T.length - (1 : ℕ)) => (
    by omega
    )) (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) => (
    by omega
    ))).length + (1 : ℕ))),
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    let _ : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let n : Fin (R.corresponding.replacementETT.rounds + (1 : ℕ)) := Fin.last
        R.corresponding.replacementETT.rounds;
    let Tn : TreeSequence G e0 := R.corresponding.replacementETT.series.data.tree n.castSucc; (0 :
        ℕ) < H.dividerCount ∧ a ∈ TreeMissingColors R.coloring (H.stage (⟨H.dividerCount,
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) ∨ H.dividerCount = (0 : ℕ) ∧ a ∈ TreeMissingColors
        R.coloring Tn := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hTlen R X a eta heta haGamma jb H q n Tn
  have hm := (Finset.mem_sdiff.mp (R.counterexample.good.avoidance q eta heta haGamma)).1
  by_cases hq : H.dividerCount = 0
  · right
    refine ⟨hq, ?_⟩
    simpa [HierarchyStageMissingColors, q, hq, Fin.last, Tn, n] using hm
  · left
    refine ⟨by omega, ?_⟩
    unfold HierarchyStageMissingColors at hm
    dsimp only at hm
    obtain hz | ⟨i, hi⟩ := Fin.eq_zero_or_eq_succ q
    · exact (hq (by simpa [q] using congrArg Fin.val hz)).elim
    · rw [hi] at hm
      simp only [Fin.cases_succ] at hm
      have he : i.succ.castSucc = (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + 2)) :=
        Fin.ext (by simpa [q] using (congrArg Fin.val hi).symm)
      simpa only [he] using hm

private theorem helper_hbOutside_792.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (hTlen : (2 : ℕ) ≤
        T.length) (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (_ :
        TreeSequence G e0) (b _ : Fin k) (jb : Fin ((TreeSequencePrefix T (T.length - (1 : ℕ))
        (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) => (
    by omega
    )) (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) => (
    by omega
    ))).length + (1 : ℕ))),
    let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount); (
    ∀ {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Y → TreeSequenceInitialSegment Y Z
        → TreeSequenceInitialSegment X Z) → TreeSequenceInitialSegment A T →
    let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ))
        (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) => (
    by omega
    )) (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) => (
    by omega
    )); A.length < (↑jb : ℕ) → b ∈ MissingColors G R.coloring (B.vertex jb) →
        TreeSequenceInitialSegment B T → TreeSequenceInitialSegment A B → (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        ColoredVertexSetElementary G R.coloring (TreeSequenceVertexSet B)) → (
    ∀ (U : TreeSequence G e0) (j : Fin (U.length + (1 : ℕ))), U.vertex j ∈ TreeSequenceVertexSet
        U) → b ∉ TreeMissingColors R.coloring A := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hTlen R X b eta jb A trans hAT B hjb hb hBT
      hAB elementary vertexMem hm
  obtain ⟨v, hvA, hmv⟩ := Finset.mem_biUnion.mp hm
  obtain ⟨j, hj⟩ : ∃ j, A.vertex j = v := by simpa [TreeSequenceVertexSet] using hvA
  have hne : v ≠ B.vertex jb := by
    intro he
    have hh := T.vertex_injective ((hAT.2.1 j).trans
      (hj.trans (he.trans (hBT.2.1 jb).symm)))
    have hh := congrArg Fin.val hh
    have := j.isLt
    change j.val = jb.val at hh
    omega
  exact Finset.disjoint_left.mp (elementary R
    (TreeSequenceInitialSegmentVertexSetSubset hAB hvA) (vertexMem B jb) hne) hmv hb

private theorem helper_fixedA_949.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (hTlen : (2 : ℕ) ≤
        T.length) (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (_ :
        TreeSequence G e0) (a b _ : Fin k) (_ : Fin ((TreeSequencePrefix T (T.length - (1 : ℕ))
        (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) => (
    by omega
    )) (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) => (
    by omega
    ))).length + (1 : ℕ))),
    let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount); (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount) = A) →
    let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ))
        (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) => (
    by omega
    )) (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) => (
    by omega
    )); TreeSequenceInitialSegment B T → TreeSequenceInitialSegment A B →
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let n : Fin (R.corresponding.replacementETT.rounds + (1 : ℕ)) := Fin.last
        R.corresponding.replacementETT.rounds;
    let Tn : TreeSequence G e0 := R.corresponding.replacementETT.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors R.corresponding.replacementETT.series.data n;
        (↑(HierarchyFirstMissingPosition R.coloring T a) : ℕ) ≤ A.length → (
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    have q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    have n : Fin (R.corresponding.replacementETT.rounds + (1 : ℕ)) := Fin.last
        R.corresponding.replacementETT.rounds;
    have A : TreeSequence G e0 := HierarchyStarredStage H q;
    have Tnq : TreeSequence G e0 := H.stage (⟨H.dividerCount,
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)));
    have Tn : TreeSequence G e0 := R.corresponding.replacementETT.series.data.tree n.castSucc;
    have Dn : Finset (Fin k) := TashkinovStoredColors R.corresponding.replacementETT.series.data
        n;
    have Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q;
    have va : V := T.vertex (HierarchyFirstMissingPosition R.coloring T a);
    have vb : V := T.vertex (HierarchyFirstMissingPosition R.coloring T b);
    have sameComponent : Prop := TwoColorComponent G R.coloring a b (Sum.inl va) =
        TwoColorComponent G R.coloring a b (Sum.inl vb); ((0 : ℕ) < H.dividerCount ∧ (a ∈
        TreeMissingColors R.coloring Tnq ∨ Disjoint {a, b} Dnq) → sameComponent) ∧ (H.dividerCount
        = (0 : ℕ) ∧ (a ∈ TreeMissingColors R.coloring Tn ∨ Disjoint {a, b} Dn) → sameComponent) ∧
        (a ∈ TreeMissingColors R.coloring A ∧ TreeColorSetClosed G R.coloring A { a } →
        sameComponent ∧ TreeInterchangeable G A R.coloring a b)) →
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G R.coloring a b (Sum.inl
        (T.vertex (Fin.last T.length))); IsOneEdgeUncolored sigma e0 → HierarchyWeaklyStable H q
        sigma → (if R.corresponding.replacementETT.series.data.kind n = some
        TashkinovExtensionKind.PE then CombinedStableColoring Tn R.replacementBase.closure Dn
        R.coloring sigma else StableColoring Tn Dn R.coloring sigma) →
    ∀ (t : Fin A.length), sigma (A.edge t) = R.coloring (A.edge t) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hTlen R X a b eta jb A starEq B hBT hAB H q
      n Tn Dn iaLe change sigma hsone hweak baseStable
  have fixed (j : Fin (H.dividerCount + 1)) : HierarchyWeaklyStable H j sigma →
      ∀ t : Fin (HierarchyStarredStage H j).length,
        sigma ((HierarchyStarredStage H j).edge t) = R.coloring ((HierarchyStarredStage H j).edge
            t) := by
    refine Fin.cases ?_ (fun i => ?_) j
    · intro _
      exact P2813_T1_BaseDisplayedEdges G k e0 R.corresponding.replacementInput T R.coloring
        R.corresponding.replacementETT R.replacementBase sigma
        R.minimumContext.oneEdgeUncolored hsone baseStable
    · intro hh t
      change sigma ((H.stage i.succ.castSucc).edge t) =
        R.coloring ((H.stage i.succ.castSucc).edge t)
      by_cases ht : t.val = 0
      · have he : (H.stage i.succ.castSucc).edge t = e0 := by
          rw [show t = ⟨0, (H.stage i.succ.castSucc).positive⟩ from Fin.ext ht]
          exact (H.stage i.succ.castSucc).first_edge
        rw [he, hsone.1, R.minimumContext.oneEdgeUncolored.1]
      · exact hh.2.1 t (by omega)
  rw [← starEq R]
  exact fixed q hweak

private theorem helper_continuation_1318.{u_1, u_2} :
    helperContinuation1318Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hTlen R X a b eta heta haGamma hetaCut hw
      jb hjbX A trans common starEq B hAX hAXlt hXB hjb hb haUnused hbException hBT hAB hXlen
      fullB vertexMem firstFixed H q n Tn Dn lastPositive hTnA stageCase hbOutside hne hbB haB
      iaLe ibEq ja jaEq jbEq haFirstB change hpath hmissing sigma hsone hcase hdisFirst changed
  have hweak : HierarchyWeaklyStable H q sigma := changed.1
  have baseStable : if R.corresponding.replacementETT.series.data.kind n =
      some TashkinovExtensionKind.PE then
      CombinedStableColoring Tn R.replacementBase.closure Dn R.coloring sigma
    else StableColoring Tn Dn R.coloring sigma := by
    have extract (j : Fin (H.dividerCount + 1)) : HierarchyWeaklyStable H j sigma →
        (if R.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.PE then
          CombinedStableColoring Tn R.replacementBase.closure Dn R.coloring sigma
        else StableColoring Tn Dn R.coloring sigma) :=
      Fin.cases (fun h => h) (fun _ h => h.1) j
    exact extract q hweak
  have stable : StableColoring Tn Dn R.coloring sigma := by
    by_cases hp : R.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.PE
    · exact (ite_eq_left hp ▸ baseStable).1
    · simpa only [hp, ite_false] using baseStable
  have fixedA : ∀ t : Fin A.length, sigma (A.edge t) = R.coloring (A.edge t) := by
    exact @helper_fixedA_949 V E inferInstance inferInstance inferInstance inferInstance G k e0
        input T phi ett base C ctx hTlen R X a b eta jb starEq hBT hAB iaLe change hsone hweak
        baseStable
  have fixedPrefix : ∀ t : Fin T.length, A.length ≤ t.val → t.val < X.length →
      sigma (T.edge t) = R.coloring (T.edge t) := by
    intro t hlo hhi
    by_cases hbcol : R.coloring (T.edge t) = some b
    · obtain ⟨hi, hc⟩ := hbException t hlo hhi hbcol
      exact stable.1 _ hi ⟨b, Finset.mem_union_right _ hc, hbcol⟩
    · have haNo := haUnused t hlo hhi
      simp [sigma, TwoColorComponentSwap, haNo, hbcol]
  have hXT := trans hXB hBT
  let XM := TreeSequencePrefix X (X.length - 1) (by have := A.positive; omega) (by omega)
  have hXMX : TreeSequenceInitialSegment XM X :=
    ⟨by dsimp [XM, TreeSequencePrefix]; omega, fun _ => rfl, fun _ => rfl⟩
  have prefixFixed (t : Fin X.length) (ht : Tn.length ≤ t.val) :
      sigma (X.edge t) = R.coloring (X.edge t) := by
    by_cases hlow : t.val < A.length
    · let j : Fin A.length := ⟨t.val, hlow⟩
      have he : Fin.castLE hAX.1 j = t := Fin.ext rfl
      rw [← he, hAX.2.2 j]
      exact fixedA j
    · rw [← hXT.2.2 t]
      exact fixedPrefix (Fin.castLE hXT.1 t) (by change A.length ≤ t.val; omega) t.isLt
  have routes :
      ((R.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence sigma Tn X) ∨
      ((R.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.SE ∨
        R.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.RE) ∧
        ∃ f seed, R.corresponding.replacementETT.series.data.connectingEdges n = {f} ∧
          TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence sigma seed X)) ∧
      TashkinovAugmentationSequence R.coloring X T := by
    exact @helper_routes_498 V E inferInstance inferInstance inferInstance inferInstance G k e0
        input T phi ett base C ctx hTlen R X a b eta jb trans common hAX hAXlt hXB hBT hAB hTnA
        iaLe change hmissing hXT hXMX prefixFixed
  have hsplit : a ∈ TreeMissingColors sigma X ∧ b ∈ TreeMissingColors sigma X := by
    have subset (j : Fin (B.length + 1)) (hj : j.val ≤ X.length) :
        B.vertex j ∈ TreeSequenceVertexSet X := by
      let x : Fin (X.length + 1) := ⟨j.val, by omega⟩
      have hx : Fin.castLE (Nat.succ_le_succ hXB.1) x = j := Fin.ext rfl
      rw [← hx, hXB.2.1 x]
      exact vertexMem X x
    refine ⟨Finset.mem_biUnion.mpr ⟨B.vertex ja, subset ja (by dsimp [ja]; omega), ?_⟩,
      Finset.mem_biUnion.mpr ⟨B.vertex jb, subset jb hjbX, ?_⟩⟩
    · rw [hmissing _ (vertexMem B ja)]; exact haFirstB
    · rw [hmissing _ (vertexMem B jb)]; exact hb
  have gammaCut : ∀ eta', eta' ∈ HierarchyStoredColorsAt H q →
      (a ∈ R.counterexample.good.gamma q eta' ∨ b ∈ R.counterexample.good.gamma q eta') →
        (HierarchyFirstMissingPosition R.coloring T eta').val ≤ X.length := by
    exact @helper_gammaCut_539 V E inferInstance inferInstance inferInstance inferInstance G k e0
        input T phi ett base C ctx hTlen R X a b eta heta haGamma hetaCut jb starEq hBT hAB hTnA
        stageCase hbOutside iaLe change
  obtain ⟨_, _, corr, hmaximum, bs, K, goodK, hsameGood⟩ :=
    StableChangeCasesOneTwoSplitTail G k e0 R.corresponding.replacementInput T R.coloring
      R.corresponding.replacementETT R.replacementBase R.counterexample R.minimumContext
      a b hne (by rw [fullB R]; exact ⟨haB, hbB⟩)
      _ hpath sigma rfl hcase hdisFirst X (by dsimp only; rw [starEq R]; exact hAX)
      (by dsimp only; rw [starEq R]; exact hAXlt) (by rw [fullB R]; exact hXB)
      (by dsimp only; rw [starEq R]; exact fixedPrefix) routes.1 routes.2 hsplit
      (by rw [fullB R]; exact hmissing)
      (fun c _ => firstFixed R.coloring sigma hmissing c) gammaCut
  have terminal := TwoColorComponentSwapMissingBehavior G R.coloring a b hne
    R.minimumContext.proper (Sum.inl (T.vertex (Fin.last T.length)))
  have hterminalA : a ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)) →
      b ∈ MissingColors G sigma (T.vertex (Fin.last T.length)) :=
    terminal.2.1 _ (by rfl)
  have hterminalB : b ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)) →
      a ∈ MissingColors G sigma (T.vertex (Fin.last T.length)) :=
    terminal.2.2.1 _ (by rfl)
  have hnotElementary : ¬ ColoredVertexSetElementary G sigma (TreeSequenceVertexSet T) := by
    intro elementary
    have shorter : B.length < T.length := by
      have length : B.length = T.length - 1 := rfl
      omega
    have disjointTerminal (index : Fin (B.length + 1)) :
        Disjoint (MissingColors G sigma (B.vertex index))
          (MissingColors G sigma (T.vertex (Fin.last T.length))) :=
      elementary (hBT.vertexSet_subset (vertexMem B index))
        (vertexMem T (Fin.last T.length)) (hBT.last_vertex_ne shorter index).symm
    rcases hw with terminalA | terminalB
    · have missing : b ∈ MissingColors G sigma (B.vertex jb) := by
        rw [hmissing _ (vertexMem B jb)]
        exact hb
      exact Finset.disjoint_left.mp (disjointTerminal jb) missing (hterminalA terminalA)
    · have missing : a ∈ MissingColors G sigma (B.vertex ja) := by
        rw [hmissing _ (vertexMem B ja)]
        exact haFirstB
      exact Finset.disjoint_left.mp (disjointTerminal ja) missing (hterminalB terminalB)
  let CS : HierarchyCounterexample bs := {
    positive := by rw [corr.rungAgreement]; exact R.counterexample.positive
    hierarchy := K
    good := goodK
    maximum := hmaximum
    notElementary := hnotElementary }
  obtain ⟨S, hS⟩ := HierarchyReplacementPresentationTrans G k e0 input T phi ett base C ctx
    R sigma corr bs CS hsameGood
  refine ⟨S, ?_, ?_, ?_, ?_⟩ <;> rw [hS]
  · exact hmissing
  · exact fixedPrefix
  · exact hterminalA
  · exact hterminalB

private theorem helper_continuation_1225.{u_1, u_2} :
    helperContinuation1225Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hTlen R X a b eta heta haGamma hetaCut hw
      jb hjbX
  set A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
                      C.hierarchy.dividerCount)
  intro trans common componentData starEq B hAX hAXlt hXB hjb hb haUnused hbException hBT hAB
      hXlen fullB elementary vertexMem firstMem firstFixed
  set H : TashkinovHierarchy
                                                              R.corresponding.replacementETT
                                                            R.replacementBase :=
                                                                R.counterexample.hierarchy
  set q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount
  set n : Fin (R.corresponding.replacementETT.rounds + 1) :=
    Fin.last R.corresponding.replacementETT.rounds
  set Tn : TreeSequence G e0 := R.corresponding.replacementETT.series.data.tree n.castSucc
  let Dn : Finset (Fin k) :=
    TashkinovStoredColors
      R.corresponding.replacementETT.series.data
    n
  intro lastPositive hTnA stageCase hbOutside hne hbB haB iaLe ibEq
  have haFirst := firstMem R.coloring a (by
    have := hAB.1
    have hblen : B.length = T.length - 1 := rfl
    omega)
  let ja : Fin (B.length + 1) := ⟨(HierarchyFirstMissingPosition R.coloring T a).val,
    by have := hAB.1; omega⟩
  have jaEq : Fin.castLE (Nat.succ_le_succ hBT.1) ja =
      HierarchyFirstMissingPosition R.coloring T a := Fin.ext rfl
  have jbEq : Fin.castLE (Nat.succ_le_succ hBT.1) jb =
      HierarchyFirstMissingPosition R.coloring T b := Fin.ext ibEq.symm
  have haFirstB : a ∈ MissingColors G R.coloring (B.vertex ja) := by
    rw [← hBT.2.1 ja, jaEq]; exact haFirst
  have hordered : TreeVertexOrder T
      (T.vertex (HierarchyFirstMissingPosition R.coloring T a))
      (T.vertex (HierarchyFirstMissingPosition R.coloring T b)) :=
    ⟨_, _, rfl, rfl, by omega⟩
  have hunused : a ∉ (Finset.univ.filter fun c => ∃ t : Fin T.length,
      A.length ≤ t.val ∧ t.val < (HierarchyFirstMissingPosition R.coloring T b).val ∧
        R.coloring (T.edge t) = some c) := by
    intro hh
    obtain ⟨_, t, hlo, hhi, hc⟩ := Finset.mem_filter.mp hh
    exact haUnused t hlo (by omega) hc
  have hprefixR : ColoredVertexSetElementary G R.coloring
      (TreeSequenceVertexSet (HierarchyFullTailPrefix R.counterexample
        (HierarchyFullTailLength R.counterexample - 1))) := by
    rw [fullB R]
    exact elementary R
  have hmissingR : a ∈ TreeMissingColors R.coloring
      (HierarchyFullTailPrefix R.counterexample (HierarchyFullTailLength R.counterexample - 1)) ∧
      b ∈ TreeMissingColors R.coloring
      (HierarchyFullTailPrefix R.counterexample (HierarchyFullTailLength R.counterexample - 1))
         := by
    rw [fullB R]
    exact ⟨haB, hbB⟩
  have change := ChangeLemma G k e0 R.corresponding.replacementInput T R.coloring
    R.corresponding.replacementETT R.replacementBase R.counterexample
    R.minimumContext.proper R.minimumContext.oneEdgeUncolored R.minimumContext.lowerRung
    R.minimumContext.fewerDividers R.minimumContext.lexicographicMinimality
    hprefixR
    R.minimumContext.largeMissingSet a b hne
    hmissingR
    (by
      dsimp only
      rw [starEq R]
      intro _
      exact ⟨hordered, hunused⟩)
  have hsame : TwoColorComponent G R.coloring a b (Sum.inl (B.vertex ja)) =
      TwoColorComponent G R.coloring a b (Sum.inl (B.vertex jb)) := by
    have hh : TwoColorComponent G R.coloring a b
        (Sum.inl (T.vertex (HierarchyFirstMissingPosition R.coloring T a))) =
        TwoColorComponent G R.coloring a b
        (Sum.inl (T.vertex (HierarchyFirstMissingPosition R.coloring T b))) := by
      rcases stageCase with ⟨hq, hm⟩ | ⟨hq, hm⟩
      · exact change.1 ⟨hq, Or.inl hm⟩
      · exact change.2.1 ⟨hq, Or.inl hm⟩
    rw [← jaEq, ← jbEq, hBT.2.1 ja, hBT.2.1 jb] at hh
    exact hh
  obtain ⟨hdis, hpath, hmissing⟩ := componentData R.coloring a b hne
    R.minimumContext.proper (TreeSequenceVertexSet B) (elementary R)
    (B.vertex ja) (B.vertex jb) (T.vertex (Fin.last T.length))
    (vertexMem B ja) (vertexMem B jb)
    (by intro hh; have := congrArg Fin.val (B.vertex_injective hh); dsimp [ja] at this; omega)
    (by intro hh; have hh := T.vertex_injective (hh.trans (hBT.2.1 ja).symm)
        have hh := congrArg Fin.val hh
        change T.length = ja.val at hh
        have := ja.isLt
        have hblen : B.length = T.length - 1 := rfl
        omega)
    (by intro hh; have hh := T.vertex_injective (hh.trans (hBT.2.1 jb).symm)
        have hh := congrArg Fin.val hh
        change T.length = jb.val at hh
        have := jb.isLt
        have hblen : B.length = T.length - 1 := rfl
        omega)
    haFirstB hb hw hsame
  let sigma := TwoColorComponentSwap G R.coloring a b (Sum.inl (T.vertex (Fin.last T.length)))
  have hsproper : IsProperEdgeColoring G sigma :=
    TwoColorComponentSwapProper G R.coloring a b hne R.minimumContext.proper _
  have hsone : IsOneEdgeUncolored sigma e0 := by
    exact @SharedFacts.TerminalKempeStageSwitch.hsone V E inferInstance inferInstance
        inferInstance inferInstance G k e0
        input T phi ett base C ctx R a b hne
  have hcase :
      (0 < H.dividerCount ∧ a ∈ TreeMissingColors R.coloring (H.stage ⟨H.dividerCount, by omega⟩)) ∨
      (H.dividerCount = 0 ∧ (a ∈ TreeMissingColors R.coloring Tn ∨
        (a ∈ TreeMissingColors R.coloring (HierarchyStarredStage H q) ∧ a ∉ Dn ∧ b ∉ Dn))) := by
    rcases stageCase with h | ⟨hq, hm⟩
    · exact Or.inl h
    · exact Or.inr ⟨hq, Or.inl hm⟩
  have hdisFirst : Disjoint (TwoColorComponent G R.coloring a b
      (Sum.inl (T.vertex (Fin.last T.length))))
      (TwoColorComponent G R.coloring a b
        (Sum.inl (T.vertex (HierarchyFirstMissingPosition R.coloring T a)))) := by
    rw [← jaEq, hBT.2.1 ja]
    exact hdis
  have changed := StableChangeCasesOneTwo G k e0 R.corresponding.replacementInput T R.coloring
    R.corresponding.replacementETT R.replacementBase R.counterexample
    R.minimumContext.proper R.minimumContext.oneEdgeUncolored R.minimumContext.lowerRung
    R.minimumContext.fewerDividers R.minimumContext.lexicographicMinimality
    hprefixR
    R.minimumContext.largeMissingSet a b hne
    hmissingR
    _ hpath sigma rfl hcase hdisFirst
  exact @helper_continuation_1318 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 input T phi ett base C ctx hTlen R X a b eta heta haGamma hetaCut hw jb hjbX trans
      common starEq hAX hAXlt hXB hjb hb haUnused hbException hBT hAB hXlen fullB vertexMem
      firstFixed lastPositive hTnA stageCase hbOutside hne hbB haB iaLe ibEq jaEq jbEq haFirstB
      change hpath hmissing hsone hcase hdisFirst changed
private theorem helper_continuation_190.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (hTlen : (2 : ℕ) ≤
        T.length) (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (X :
        TreeSequence G e0) (a b eta : Fin k), eta ∈ HierarchyStoredColorsAt
        R.counterexample.hierarchy (Fin.last R.counterexample.hierarchy.dividerCount) → a ∈
        R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta →
        (↑(HierarchyFirstMissingPosition R.coloring T eta) : ℕ) ≤ X.length → a ∈ MissingColors G
        R.coloring (T.vertex (Fin.last T.length)) ∨ b ∈ MissingColors G R.coloring (T.vertex
        (Fin.last T.length)) →
    ∀ (jb : Fin ((TreeSequencePrefix T (T.length - (1 : ℕ)) (
    by omega
    ) (
    by omega
    )).length + (1 : ℕ))), (↑jb : ℕ) ≤ X.length → (
    ∀ {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Y → TreeSequenceInitialSegment Y Z
        → TreeSequenceInitialSegment X Z) → (
    ∀ {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Z → TreeSequenceInitialSegment Y Z
        → X.length ≤ Y.length → TreeSequenceInitialSegment X Y) → (
    ∀ (psi : PartialEdgeColoring E k) (a b : Fin k), a ≠ b → IsProperEdgeColoring G psi →
    ∀ (B : Finset V), ColoredVertexSetElementary G psi B →
    ∀ (u v w : V), u ∈ B → v ∈ B → u ≠ v → w ≠ u → w ≠ v → a ∈ MissingColors G psi u → b ∈
        MissingColors G psi v → a ∈ MissingColors G psi w ∨ b ∈ MissingColors G psi w →
        TwoColorComponent G psi a b (Sum.inl u) = TwoColorComponent G psi a b (Sum.inl v) →
        Disjoint (TwoColorComponent G psi a b (Sum.inl w)) (TwoColorComponent G psi a b (Sum.inl
        u)) ∧ TwoColorPathComponent G psi a b (Sum.inl w) ∧
    ∀ x ∈ B, MissingColors G (TwoColorComponentSwap G psi a b (Sum.inl w)) x = MissingColors G psi
        x) → (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount) = (HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount) : TreeSequence G e0)) → TreeSequenceInitialSegment
        (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) : TreeSequence G
        e0) T →
    let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ))
        (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) =>
    by omega
    ) (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) =>
    by omega
    ); TreeSequenceInitialSegment (HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount) : TreeSequence G e0) X → (HierarchyStarredStage C.hierarchy
        (Fin.last C.hierarchy.dividerCount) : TreeSequence G e0).length < X.length →
        TreeSequenceInitialSegment X B → (HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount) : TreeSequence G e0).length < (↑jb : ℕ) → b ∈ MissingColors G
        R.coloring (B.vertex jb) → (
    ∀ (t : Fin T.length), (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) :
        TreeSequence G e0).length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → R.coloring (T.edge t) ≠ some
        a) → (
    ∀ (t : Fin T.length), (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) :
        TreeSequence G e0).length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → R.coloring (T.edge t) = some
        b → TreeIncidentEdge (R.corresponding.replacementETT.series.data.tree (Fin.last
        R.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧ b ∈ TashkinovStoredColors
        R.corresponding.replacementETT.series.data (Fin.last
        R.corresponding.replacementETT.rounds)) → TreeSequenceInitialSegment B T →
        TreeSequenceInitialSegment (HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount) : TreeSequence G e0) B → X.length ≤ T.length - (1 : ℕ) → (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyFullTailPrefix R.counterexample (HierarchyFullTailLength R.counterexample - (1 :
        ℕ)) = B) → (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        ColoredVertexSetElementary G R.coloring (TreeSequenceVertexSet B)) →
    ∃ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), (
    ∀ v ∈ TreeSequenceVertexSet (TreeSequencePrefix T (T.length - (1 : ℕ)) (
    by omega
    ) (
    by omega
    )), MissingColors G S.coloring v = MissingColors G R.coloring v) ∧ (
    ∀ (t : Fin T.length), (HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount)).length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → S.coloring (T.edge t)
        = R.coloring (T.edge t)) ∧ (a ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length))
        → b ∈ MissingColors G S.coloring (T.vertex (Fin.last T.length))) ∧ (b ∈ MissingColors G
        R.coloring (T.vertex (Fin.last T.length)) → a ∈ MissingColors G S.coloring (T.vertex
        (Fin.last T.length))) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hTlen R X a b eta heta haGamma hetaCut hw
      jb hjbX
  set A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
                      C.hierarchy.dividerCount)
  intro trans common componentData starEq hAT B hAX hAXlt hXB hjb hb haUnused hbException hBT hAB
      hXlen fullB elementary
  have vertexMem (U : TreeSequence G e0) (j : Fin (U.length + 1)) :
      U.vertex j ∈ TreeSequenceVertexSet U := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨j, rfl⟩
  have firstMem (psi : PartialEdgeColoring E k) (c : Fin k)
      (hlt : (HierarchyFirstMissingPosition psi T c).val < T.length) :
      c ∈ MissingColors G psi (T.vertex (HierarchyFirstMissingPosition psi T c)) := by
    exact TreeSequenceFirstMissingPositionMem hlt
  have firstAt (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
      (c : Fin k) (j : Fin (B.length + 1))
      (hc : c ∈ MissingColors G R.coloring (B.vertex j)) :
      (HierarchyFirstMissingPosition R.coloring T c).val = j.val := by
    exact TreeSequenceFirstMissingPositionEqCast hBT (elementary R) hc
  have firstFixed (psi tau : PartialEdgeColoring E k)
      (hmissing : ∀ v ∈ TreeSequenceVertexSet B,
        MissingColors G tau v = MissingColors G psi v) (c : Fin k) :
      HierarchyFirstMissingPosition tau T c = HierarchyFirstMissingPosition psi T c := by
    exact T.firstMissingPosition_eq_of_prefix_agreement hBT
      (Nat.sub_add_cancel T.positive).ge hmissing c
  let H := R.counterexample.hierarchy
  let q := Fin.last H.dividerCount
  let n := Fin.last R.corresponding.replacementETT.rounds
  let Tn := R.corresponding.replacementETT.series.data.tree n.castSucc
  let Dn := TashkinovStoredColors R.corresponding.replacementETT.series.data n
  have chain : ∀ (j : ℕ) (hj : j < H.dividerCount + 2)
      (i : Fin (H.dividerCount + 2)), i.val ≤ j →
      TreeSequenceInitialSegment (H.stage i) (H.stage ⟨j, hj⟩) := by
    intro j hj i hi
    exact H.stageInitialSegmentOfLE i ⟨j, hj⟩ hi
  have lastPositive (hq : H.dividerCount ≠ 0) :
      HierarchyStarredStage H q = H.stage ⟨H.dividerCount, by omega⟩ := by
    unfold HierarchyStarredStage
    obtain hz | ⟨i, hi⟩ := Fin.eq_zero_or_eq_succ q
    · exact (hq (by simpa [q] using congrArg Fin.val hz)).elim
    · rw [hi]
      simp only [Fin.cases_succ]
      congr 1
      exact Fin.ext (by simpa [q] using (congrArg Fin.val hi).symm)
  have hTnCore : TreeSequenceInitialSegment Tn R.replacementBase.core := by
    exact R.replacementBase.lastRoundInitialSegmentCore
  have coreA : TreeSequenceInitialSegment R.replacementBase.core A := by
    rw [← starEq R]
    by_cases hq : H.dividerCount = 0
    · have he : HierarchyStarredStage H q = R.replacementBase.core := by
        simp [HierarchyStarredStage, q, hq, Fin.last]
      rw [he]
      exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
    · rw [lastPositive hq]
      exact trans H.coreInsideFirst (chain H.dividerCount (by omega) ⟨1, by omega⟩
        (by change 1 ≤ H.dividerCount; omega))
  have hTnA := trans hTnCore coreA
  have stageCase :
      (0 < H.dividerCount ∧ a ∈ TreeMissingColors R.coloring
        (H.stage ⟨H.dividerCount, by omega⟩)) ∨
      (H.dividerCount = 0 ∧ a ∈ TreeMissingColors R.coloring Tn) := by
    exact @helper_stageCase_765 V E inferInstance inferInstance inferInstance inferInstance G k
        e0 input T phi ett base C ctx hTlen R X a eta heta haGamma jb
  have haA : a ∈ TreeMissingColors R.coloring A := by
    rcases stageCase with ⟨hq, hm⟩ | ⟨hq, hm⟩
    · rw [← starEq R, lastPositive (by omega)]
      exact hm
    · obtain ⟨v, hv, hc⟩ := Finset.mem_biUnion.mp hm
      exact Finset.mem_biUnion.mpr ⟨v,
        TreeSequenceInitialSegmentVertexSetSubset hTnA hv, hc⟩
  have hbOutside : b ∉ TreeMissingColors R.coloring A := by
    exact @helper_hbOutside_792 V E inferInstance inferInstance inferInstance inferInstance G k
        e0 input T phi ett base C ctx hTlen R X b eta jb trans hAT hjb hb hBT hAB elementary
        vertexMem
  have hne : a ≠ b := by rintro rfl; exact hbOutside haA
  have hbB : b ∈ TreeMissingColors R.coloring B :=
    Finset.mem_biUnion.mpr ⟨B.vertex jb, vertexMem B jb, hb⟩
  have haB : a ∈ TreeMissingColors R.coloring B := by
    obtain ⟨v, hv, hc⟩ := Finset.mem_biUnion.mp haA
    exact Finset.mem_biUnion.mpr ⟨v, TreeSequenceInitialSegmentVertexSetSubset hAB hv, hc⟩
  have iaLe : (HierarchyFirstMissingPosition R.coloring T a).val ≤ A.length := by
    exact TreeSequenceFirstMissingPositionLePrefix hAT haA
  have ibEq := firstAt R b jb hb
  exact @helper_continuation_1225 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 input T phi ett base C ctx hTlen R X a b eta heta haGamma hetaCut hw jb hjbX trans
      common componentData starEq hAX hAXlt hXB hjb hb haUnused hbException hBT hAB hXlen fullB
      elementary vertexMem firstMem firstFixed lastPositive hTnA stageCase hbOutside hne hbB haB
      iaLe ibEq
theorem P2963_T1_TerminalKempeStageSwitch {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (A B : TreeSequence G e0) (hTlen : 2 ≤ T.length)
    (hA : HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) = A)
    (hB : B = TreeSequencePrefix T (T.length - 1) (by omega) (by omega))
    (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
    (X : TreeSequence G e0) (hAX : TreeSequenceInitialSegment A X)
    (hAXlt : A.length < X.length) (hXB : TreeSequenceInitialSegment X B)
    (a b eta : Fin k)
    (heta : eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy
      (Fin.last R.counterexample.hierarchy.dividerCount))
    (haGamma : a ∈ R.counterexample.good.gamma
      (Fin.last R.counterexample.hierarchy.dividerCount) eta)
    (hetaCut : (HierarchyFirstMissingPosition R.coloring T eta).val ≤ X.length)
    (jb : Fin (B.length + 1)) (hjb : A.length < jb.val)
    (hjbX : jb.val ≤ X.length)
    (hb : b ∈ MissingColors G R.coloring (B.vertex jb))
    (hw : a ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)) ∨
      b ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)))
    (haUnused : ∀ t : Fin T.length, A.length ≤ t.val → t.val < X.length →
      R.coloring (T.edge t) ≠ some a)
    (hbException : ∀ t : Fin T.length, A.length ≤ t.val → t.val < X.length →
      R.coloring (T.edge t) = some b →
        TreeIncidentEdge (R.corresponding.replacementETT.series.data.tree
          (Fin.last R.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧
        b ∈ TashkinovStoredColors R.corresponding.replacementETT.series.data
          (Fin.last R.corresponding.replacementETT.rounds)) :
    ∃ S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx,
      (∀ v ∈ TreeSequenceVertexSet B,
        MissingColors G S.coloring v = MissingColors G R.coloring v) ∧
      (∀ t : Fin T.length, A.length ≤ t.val → t.val < X.length →
        S.coloring (T.edge t) = R.coloring (T.edge t)) ∧
      (a ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)) →
        b ∈ MissingColors G S.coloring (T.vertex (Fin.last T.length))) ∧
      (b ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)) →
        a ∈ MissingColors G S.coloring (T.vertex (Fin.last T.length))) := by
  classical
  subst A
  subst B
  let A := HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)
  have trans {X Y Z : TreeSequence G e0}
      (hXY : TreeSequenceInitialSegment X Y)
      (hYZ : TreeSequenceInitialSegment Y Z) :
      TreeSequenceInitialSegment X Z := by
    exact hXY.trans hYZ
  have common {X Y Z : TreeSequence G e0}
      (hXZ : TreeSequenceInitialSegment X Z)
      (hYZ : TreeSequenceInitialSegment Y Z) (hXY : X.length ≤ Y.length) :
      TreeSequenceInitialSegment X Y := by
    exact hYZ.of_common_extension hXZ hXY
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
    exact P2905_T2_ElementaryTerminalComponent G psi a b hne hproper
      B helem u v w hu hv hwu hwv hau hbv hw hsame
  have sameLast :
    ∀ {a b : ℕ} (s : Fin (a + 2) → TreeSequence G e0) (t : Fin (b + 2) → TreeSequence G e0) (u v :
        TreeSequence G e0), a = b → HEq s t → u = v → Fin.cases (motive := fun _ => TreeSequence G
        e0) u (fun i : Fin a => s i.castSucc.succ) (Fin.last a) = Fin.cases (motive := fun _ =>
        TreeSequence G e0) v (fun i : Fin b => t i.castSucc.succ) (Fin.last b) := by
    clear * -
    intro a b s t u v hab hst huv
    cases hab
    have he : s = t := eq_of_heq hst
    cases he
    cases huv
    rfl
  have starEq (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) :
      HierarchyStarredStage R.counterexample.hierarchy
        (Fin.last R.counterexample.hierarchy.dividerCount) = A :=
    (sameLast _ _ _ _ R.sameGood.1.2.1 R.sameGood.1.2.2.1 R.sameGood.1.1).symm
  have hAT : TreeSequenceInitialSegment A T := by
    have starNext (j : Fin (C.hierarchy.dividerCount + 1)) :
        TreeSequenceInitialSegment (HierarchyStarredStage C.hierarchy j)
          (C.hierarchy.stage j.succ) :=
      Fin.cases C.hierarchy.coreInsideFirst (fun i => C.hierarchy.nested i.succ) j
    simpa only [Fin.succ_last, C.hierarchy.terminalStage] using
      starNext (Fin.last C.hierarchy.dividerCount)
  let B := TreeSequencePrefix T (T.length - 1) (by omega) (by omega)
  change TreeSequenceInitialSegment A X at hAX
  change A.length < X.length at hAXlt
  change TreeSequenceInitialSegment X B at hXB
  change A.length < jb.val at hjb
  change b ∈ MissingColors G R.coloring (B.vertex jb) at hb
  change ∀ t : Fin T.length, A.length ≤ t.val → t.val < X.length →
    R.coloring (T.edge t) ≠ some a at haUnused
  change ∀ t : Fin T.length, A.length ≤ t.val → t.val < X.length →
    R.coloring (T.edge t) = some b →
      TreeIncidentEdge (R.corresponding.replacementETT.series.data.tree
        (Fin.last R.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧
      b ∈ TashkinovStoredColors R.corresponding.replacementETT.series.data
        (Fin.last R.corresponding.replacementETT.rounds) at hbException
  have hBT : TreeSequenceInitialSegment B T :=
    ⟨by dsimp [B, TreeSequencePrefix]; omega, fun _ => rfl, fun _ => rfl⟩
  have hAB : TreeSequenceInitialSegment A B := trans hAX hXB
  have hXlen : X.length ≤ T.length - 1 := hXB.1
  have fullB (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) :
      HierarchyFullTailPrefix R.counterexample
        (HierarchyFullTailLength R.counterexample - 1) = B := by
    have hn : min ((HierarchyStarredStage R.counterexample.hierarchy
        (Fin.last R.counterexample.hierarchy.dividerCount)).length +
        (HierarchyFullTailLength R.counterexample - 1)) T.length = T.length - 1 := by
      unfold HierarchyFullTailLength
      dsimp only
      rw [starEq R]
      omega
    simp only [HierarchyFullTailPrefix, hn]
    rfl
  have elementary (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) :
      ColoredVertexSetElementary G R.coloring (TreeSequenceVertexSet B) := by
    have h : ColoredVertexSetElementary G R.coloring
      (TreeSequenceVertexSet (HierarchyFullTailPrefix R.counterexample
        (HierarchyFullTailLength R.counterexample - 1))) := by
      exact HierarchyCounterexamplePenultimateElementary G k e0
        R.corresponding.replacementInput T R.coloring R.corresponding.replacementETT
        R.replacementBase R.counterexample R.minimumContext.proper
        R.minimumContext.oneEdgeUncolored R.minimumContext.lowerRung
        R.minimumContext.fewerDividers R.minimumContext.lexicographicMinimality
        R.minimumContext.largeMissingSet
    intro u hu v hv hne
    exact h (by rw [fullB R]; exact hu) (by rw [fullB R]; exact hv) hne
  exact @helper_continuation_190 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 input T phi ett base C ctx hTlen R X a b eta heta haGamma hetaCut hw jb hjbX trans
      common componentData starEq hAT hAX hAXlt hXB hjb hb haUnused hbException hBT hAB hXlen
      fullB elementary
end GoldbergSeymour

end
