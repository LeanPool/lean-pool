/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.SharedFacts.OutsideAdvancement

public import LeanPool.GoldbergSeymour.SharedFacts.InsideAdvancement


public import LeanPool.GoldbergSeymour.TerminalKempeStageSwitch
public import LeanPool.GoldbergSeymour.HierarchyEligibleCommonMissingIndices
public import LeanPool.GoldbergSeymour.StableChangeCaseThree

/-!
# Hierarchy Situation One Advance Outside Stored

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev helperBranch520Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (hsituation :
        HierarchyPathNumber C.hierarchy = (1 : ℕ)) (_ : HierarchyReplacementPresentation G k e0
        input T phi ett base C ctx) (_ : Fin k),
    ∀ (hlen : (4 : ℕ) ≤ T.length),
    let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ))
        (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) => (
    by omega
    )) (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) => (
    by omega
    ));
    ∀ (_ : (
    ∀ (U : TreeSequence G e0) (j : Fin (U.length + (1 : ℕ))), U.vertex j ∈ TreeSequenceVertexSet
        U)) (_ : (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (c : Fin k) (j :
        Fin (B.length + (1 : ℕ))) (_ : c ∈ MissingColors G R.coloring (B.vertex j)),
        (↑(HierarchyFirstMissingPosition R.coloring T c) : ℕ) = (↑j : ℕ))) (_ : (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (X : TreeSequence G
        e0) (_ : TreeSequenceInitialSegment (HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount) : TreeSequence G e0) X) (_ : (HierarchyStarredStage C.hierarchy
        (Fin.last C.hierarchy.dividerCount) : TreeSequence G e0).length < X.length) (_ :
        TreeSequenceInitialSegment X B) (a b eta : Fin k) (_ : eta ∈ HierarchyStoredColorsAt
        R.counterexample.hierarchy (Fin.last R.counterexample.hierarchy.dividerCount)) (_ : a ∈
        R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta) (_ :
        (↑(HierarchyFirstMissingPosition R.coloring T eta) : ℕ) ≤ X.length) (jb : Fin (B.length +
        (1 : ℕ))) (_ : (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) :
        TreeSequence G e0).length < (↑jb : ℕ)) (_ : (↑jb : ℕ) ≤ X.length) (_ : b ∈ MissingColors G
        R.coloring (B.vertex jb)) (_ : a ∈ MissingColors G R.coloring (T.vertex (Fin.last
        T.length)) ∨ b ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length))) (_ : (
    ∀ (t : Fin T.length) (_ : (HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount) : TreeSequence G e0).length ≤ (↑t : ℕ)) (_ : (↑t : ℕ) <
        X.length), R.coloring (T.edge t) ≠ some a)) (_ : (
    ∀ (t : Fin T.length) (_ : (HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount) : TreeSequence G e0).length ≤ (↑t : ℕ)) (_ : (↑t : ℕ) <
        X.length) (_ : R.coloring (T.edge t) = some b), TreeIncidentEdge
        (R.corresponding.replacementETT.series.data.tree (Fin.last
        R.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧ b ∈ TashkinovStoredColors
        R.corresponding.replacementETT.series.data (Fin.last
        R.corresponding.replacementETT.rounds))),
    ∃ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), (
    ∀ v ∈ TreeSequenceVertexSet B, MissingColors G S.coloring v = MissingColors G R.coloring v) ∧
        (
    ∀ (t : Fin T.length), (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) :
        TreeSequence G e0).length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → S.coloring (T.edge t) =
        R.coloring (T.edge t)) ∧ (a ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)) →
        b ∈ MissingColors G S.coloring (T.vertex (Fin.last T.length))) ∧ (b ∈ MissingColors G
        R.coloring (T.vertex (Fin.last T.length)) → a ∈ MissingColors G S.coloring (T.vertex
        (Fin.last T.length))))) (_ : (
    ∀ (R S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∀ eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount), eta ∈ HierarchyStoredColorsAt
        S.counterexample.hierarchy (Fin.last S.counterexample.hierarchy.dividerCount) ∧
        R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta =
        S.counterexample.good.gamma (Fin.last S.counterexample.hierarchy.dividerCount) eta)) (_ :
        (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∀ eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount),
    ∀ (f : E),
    ∃ a ∈ R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta,
        R.coloring f ≠ some a)) (m : ℕ) (hmLower : HierarchyPathNumber C.hierarchy ≤ m) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∀ alpha ∈ MissingColors G P.coloring (T.vertex (Fin.last T.length)),
    ∀ (hmT : (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) : TreeSequence
        G e0).length + (m + (1 : ℕ)) < T.length),
    let X : TreeSequence G e0 := TreeSequencePrefix T ((HierarchyStarredStage C.hierarchy
        (Fin.last C.hierarchy.dividerCount) : TreeSequence G e0).length + (m + (1 : ℕ))) (
    have this : (1 : ℕ) ≤ (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) :
        TreeSequence G e0).length := (HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount) : TreeSequence G e0).positive; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) ≤ (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) :
        TreeSequence G e0).length + (m + (1 : ℕ))) =>
    by omega
    ) (Decidable.byContradiction fun (a : ¬(HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount) : TreeSequence G e0).length + (m + (1 : ℕ)) ≤ T.length) =>
    by omega
    ); TreeSequenceInitialSegment (HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount) : TreeSequence G e0) X → TreeSequenceInitialSegment X B →
        (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) : TreeSequence G
        e0).length < X.length →
    let jm : Fin (B.length + (1 : ℕ)) := (⟨(HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount) : TreeSequence G e0).length + m, id (Decidable.byContradiction
        fun (a : ¬(HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) :
        TreeSequence G e0).length + m < T.length - (1 : ℕ) + (1 : ℕ)) =>
    by omega
    )⟩ : Fin (B.length + (1 : ℕ)));
    let jnext : Fin (B.length + (1 : ℕ)) := (⟨(HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount) : TreeSequence G e0).length + (m + (1 : ℕ)), id
        (Decidable.byContradiction fun (a : ¬(HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount) : TreeSequence G e0).length + (m + (1 : ℕ)) < T.length - (1 : ℕ)
        + (1 : ℕ)) =>
    by omega
    )⟩ : Fin (B.length + (1 : ℕ)));
    let _ : Fin T.length := (⟨(HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount) : TreeSequence G e0).length + m,
    by omega
    ⟩ : Fin T.length); alpha ∈ MissingColors G P.coloring (B.vertex jm) →
    ∀ theta ∈ MissingColors G P.coloring (B.vertex jnext), (
    ∀ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∀ c ∈ MissingColors G S.coloring (B.vertex jnext), c ∈ MissingColors G S.coloring (T.vertex
        (Fin.last T.length)) → m + (1 : ℕ) ∈ HierarchyEligibleCommonMissingIndices G k e0 input T
        phi ett base C ctx) → (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∀ b ∈ MissingColors G R.coloring (B.vertex jnext),
    ∀ (t : Fin T.length), (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) :
        TreeSequence G e0).length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → R.coloring (T.edge t) = some
        b → TreeIncidentEdge (R.corresponding.replacementETT.series.data.tree (Fin.last
        R.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧ b ∈ TashkinovStoredColors
        R.corresponding.replacementETT.series.data (Fin.last
        R.corresponding.replacementETT.rounds)) → (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∀ b ∈ MissingColors G R.coloring (B.vertex jm),
    ∀ (t : Fin T.length), (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) :
        TreeSequence G e0).length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → R.coloring (T.edge t) = some
        b → TreeIncidentEdge (R.corresponding.replacementETT.series.data.tree (Fin.last
        R.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧ b ∈ TashkinovStoredColors
        R.corresponding.replacementETT.series.data (Fin.last
        R.corresponding.replacementETT.rounds)) → (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (eta a : Fin k),
        eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount) → a ∈ R.counterexample.good.gamma (Fin.last
        R.counterexample.hierarchy.dividerCount) eta → eta ∈ MissingColors G R.coloring (B.vertex
        jnext) →
    ∀ (t : Fin T.length), (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) :
        TreeSequence G e0).length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → R.coloring (T.edge t) ≠ some
        a) → theta ∈ HierarchyStoredColorsAt P.counterexample.hierarchy (Fin.last
        P.counterexample.hierarchy.dividerCount) → m + (1 : ℕ) ∈
        HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx

private abbrev helperBranch542Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (hsituation :
        HierarchyPathNumber C.hierarchy = (1 : ℕ)) (_ : HierarchyReplacementPresentation G k e0
        input T phi ett base C ctx) (_ : Fin k) (_ : (
    ∀ (psi : PartialEdgeColoring E k) (a b : Fin k) (_ : a ≠ b) (_ : IsProperEdgeColoring G psi)
        (B : Finset V) (_ : ColoredVertexSetElementary G psi B) (u v w : V) (_ : u ∈ B) (_ : v ∈
        B) (_ : u ≠ v) (_ : w ≠ u) (_ : w ≠ v) (_ : a ∈ MissingColors G psi u) (_ : b ∈
        MissingColors G psi v) (_ : a ∈ MissingColors G psi w ∨ b ∈ MissingColors G psi w) (_ :
        TwoColorComponent G psi a b (Sum.inl u) = TwoColorComponent G psi a b (Sum.inl v)),
        Disjoint (TwoColorComponent G psi a b (Sum.inl w)) (TwoColorComponent G psi a b (Sum.inl
        u)) ∧ TwoColorPathComponent G psi a b (Sum.inl w) ∧
    ∀ x ∈ B, MissingColors G (TwoColorComponentSwap G psi a b (Sum.inl w)) x = MissingColors G psi
        x)) (_ : (
    ∀ {X Y Z : TreeSequence G e0} (_ : TreeSequenceInitialSegment X Y) (_ :
        TreeSequenceInitialSegment Y Z), TreeSequenceInitialSegment X Z)),
    let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount);
    ∀ (_ : (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount) = A)) (_ : TreeSequenceInitialSegment A T) (hlen
        : (4 : ℕ) ≤ T.length),
    let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ))
        (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) => (
    by omega
    )) (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) => (
    by omega
    ));
    ∀ (_ : TreeSequenceInitialSegment B T) (_ : (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyFullTailPrefix R.counterexample (HierarchyFullTailLength R.counterexample - (1 :
        ℕ)) = B)) (_ : (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        ColoredVertexSetElementary G R.coloring (TreeSequenceVertexSet B))) (_ : (
    ∀ (U : TreeSequence G e0) (j : Fin (U.length + (1 : ℕ))), U.vertex j ∈ TreeSequenceVertexSet
        U)) (_ : (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (c : Fin k) (j :
        Fin (B.length + (1 : ℕ))) (_ : c ∈ MissingColors G R.coloring (B.vertex j)),
        (↑(HierarchyFirstMissingPosition R.coloring T c) : ℕ) = (↑j : ℕ))) (_ : (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (c : Fin k) (j :
        Fin (B.length + (1 : ℕ))) (_ : A.length < (↑j : ℕ)) (_ : c ∈ MissingColors G R.coloring
        (B.vertex j)), c ∉ TreeMissingColors R.coloring A)) (_ : (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∀ c ∉ TreeMissingColors R.coloring A, c ∉ HierarchyStoredColorsAt R.counterexample.hierarchy
        (Fin.last R.counterexample.hierarchy.dividerCount) → c ∉ TashkinovStoredColors
        R.corresponding.replacementETT.series.data (Fin.last
        R.corresponding.replacementETT.rounds))) (m : ℕ) (hmLower : HierarchyPathNumber
        C.hierarchy ≤ m) (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∀ alpha ∈ MissingColors G P.coloring ((HierarchyFullTailPrefix C m).vertex (Fin.last
        (HierarchyFullTailPrefix C m).length)), alpha ∈ MissingColors G P.coloring (T.vertex
        (Fin.last T.length)) → alpha ∉ HierarchyStoredColorsAt P.counterexample.hierarchy
        (Fin.last P.counterexample.hierarchy.dividerCount) →
    ∀ (hmT : A.length + (m + (1 : ℕ)) < T.length),
    let X : TreeSequence G e0 := TreeSequencePrefix T (A.length + (m + (1 : ℕ))) (
    have this : (1 : ℕ) ≤ A.length := A.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤
        A.length + (m + (1 : ℕ))) =>
    by omega
    ) (Decidable.byContradiction fun (a : ¬A.length + (m + (1 : ℕ)) ≤ T.length) =>
    by omega
    );
    let jm : Fin (B.length + (1 : ℕ)) := (⟨A.length + m, id (Decidable.byContradiction fun (a :
        ¬A.length + m < T.length - (1 : ℕ) + (1 : ℕ)) =>
    by
              omega
    )⟩ : Fin (B.length + (1 : ℕ)));
    let jnext : Fin (B.length + (1 : ℕ)) := (⟨A.length + (m + (1 : ℕ)), id
        (Decidable.byContradiction fun (a : ¬A.length + (m + (1 : ℕ)) < T.length - (1 : ℕ) + (1 :
        ℕ)) =>
    by omega
    )⟩ : Fin (B.length + (1 : ℕ))); alpha ∈ MissingColors G P.coloring (B.vertex jm) →
    ∀ theta ∈ MissingColors G P.coloring (B.vertex jnext), (
    ∀ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∀ c ∈ MissingColors G S.coloring (B.vertex jnext), c ∈ MissingColors G S.coloring (T.vertex
        (Fin.last T.length)) → m + (1 : ℕ) ∈ HierarchyEligibleCommonMissingIndices G k e0 input T
        phi ett base C ctx) → (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∀ b ∈ MissingColors G R.coloring (B.vertex jm),
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → R.coloring (T.edge t) = some
        b → TreeIncidentEdge (R.corresponding.replacementETT.series.data.tree (Fin.last
        R.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧ b ∈ TashkinovStoredColors
        R.corresponding.replacementETT.series.data (Fin.last
        R.corresponding.replacementETT.rounds)) → theta ∉ HierarchyStoredColorsAt
        P.counterexample.hierarchy (Fin.last P.counterexample.hierarchy.dividerCount) → m + (1 :
        ℕ) ∈ HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx

private abbrev helperAdvance481Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (_ :
        HierarchyPathNumber C.hierarchy = (1 : ℕ)) (_ : (
    ∀ (mu : PartialEdgeColoring E k) (_ : IsProperEdgeColoring G mu) (_ : IsOneEdgeUncolored mu
        e0) (v : V), (MissingColors G mu v).Nonempty)) (_ : ℕ) (_ :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (_ : Fin k) (_ : (
    ∀ (psi : PartialEdgeColoring E k) (a b : Fin k) (_ : a ≠ b) (_ : IsProperEdgeColoring G psi)
        (B : Finset V) (_ : ColoredVertexSetElementary G psi B) (u v w : V) (_ : u ∈ B) (_ : v ∈
        B) (_ : u ≠ v) (_ : w ≠ u) (_ : w ≠ v) (_ : a ∈ MissingColors G psi u) (_ : b ∈
        MissingColors G psi v) (_ : a ∈ MissingColors G psi w ∨ b ∈ MissingColors G psi w) (_ :
        TwoColorComponent G psi a b (Sum.inl u) = TwoColorComponent G psi a b (Sum.inl v)),
        Disjoint (TwoColorComponent G psi a b (Sum.inl w)) (TwoColorComponent G psi a b (Sum.inl
        u)) ∧ TwoColorPathComponent G psi a b (Sum.inl w) ∧
    ∀ x ∈ B, MissingColors G (TwoColorComponentSwap G psi a b (Sum.inl w)) x = MissingColors G psi
        x)) (_ : (
    ∀ {X Y Z : TreeSequence G e0} (_ : TreeSequenceInitialSegment X Y) (_ :
        TreeSequenceInitialSegment Y Z), TreeSequenceInitialSegment X Z)) (_ : (
    ∀ {X Y Z : TreeSequence G e0} (_ : TreeSequenceInitialSegment X Z) (_ :
        TreeSequenceInitialSegment Y Z) (_ : X.length ≤ Y.length), TreeSequenceInitialSegment X
        Y)) (_ : (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount) = (HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount) : TreeSequence G e0))) (_ : TreeSequenceInitialSegment
        (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) : TreeSequence G
        e0) T) (hlen : (4 : ℕ) ≤ T.length),
    let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ))
        (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) =>
    by omega
    ) (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) =>
    by omega
    );
    ∀ (_ : TreeSequenceInitialSegment B T) (_ : (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyFullTailPrefix R.counterexample (HierarchyFullTailLength R.counterexample - (1 :
        ℕ)) = B)) (_ : (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        ColoredVertexSetElementary G R.coloring (TreeSequenceVertexSet B))) (_ : (
    ∀ (U : TreeSequence G e0) (j : Fin (U.length + (1 : ℕ))), U.vertex j ∈ TreeSequenceVertexSet
        U)) (_ : (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (c : Fin k) (j :
        Fin (B.length + (1 : ℕ))) (_ : c ∈ MissingColors G R.coloring (B.vertex j)),
        (↑(HierarchyFirstMissingPosition R.coloring T c) : ℕ) = (↑j : ℕ))) (_ : (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (X : TreeSequence G
        e0) (_ : TreeSequenceInitialSegment (HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount) : TreeSequence G e0) X) (_ : (HierarchyStarredStage C.hierarchy
        (Fin.last C.hierarchy.dividerCount) : TreeSequence G e0).length < X.length) (_ :
        TreeSequenceInitialSegment X B) (a b eta : Fin k) (_ : eta ∈ HierarchyStoredColorsAt
        R.counterexample.hierarchy (Fin.last R.counterexample.hierarchy.dividerCount)) (_ : a ∈
        R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta) (_ :
        (↑(HierarchyFirstMissingPosition R.coloring T eta) : ℕ) ≤ X.length) (jb : Fin (B.length +
        (1 : ℕ))) (_ : (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) :
        TreeSequence G e0).length < (↑jb : ℕ)) (_ : (↑jb : ℕ) ≤ X.length) (_ : b ∈ MissingColors G
        R.coloring (B.vertex jb)) (_ : a ∈ MissingColors G R.coloring (T.vertex (Fin.last
        T.length)) ∨ b ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length))) (_ : (
    ∀ (t : Fin T.length) (_ : (HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount) : TreeSequence G e0).length ≤ (↑t : ℕ)) (_ : (↑t : ℕ) <
        X.length), R.coloring (T.edge t) ≠ some a)) (_ : (
    ∀ (t : Fin T.length) (_ : (HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount) : TreeSequence G e0).length ≤ (↑t : ℕ)) (_ : (↑t : ℕ) <
        X.length) (_ : R.coloring (T.edge t) = some b), TreeIncidentEdge
        (R.corresponding.replacementETT.series.data.tree (Fin.last
        R.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧ b ∈ TashkinovStoredColors
        R.corresponding.replacementETT.series.data (Fin.last
        R.corresponding.replacementETT.rounds))),
    ∃ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), (
    ∀ v ∈ TreeSequenceVertexSet B, MissingColors G S.coloring v = MissingColors G R.coloring v) ∧
        (
    ∀ (t : Fin T.length), (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) :
        TreeSequence G e0).length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → S.coloring (T.edge t) =
        R.coloring (T.edge t)) ∧ (a ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)) →
        b ∈ MissingColors G S.coloring (T.vertex (Fin.last T.length))) ∧ (b ∈ MissingColors G
        R.coloring (T.vertex (Fin.last T.length)) → a ∈ MissingColors G S.coloring (T.vertex
        (Fin.last T.length))))) (_ : (
    ∀ (R S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∀ eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount), eta ∈ HierarchyStoredColorsAt
        S.counterexample.hierarchy (Fin.last S.counterexample.hierarchy.dividerCount) ∧
        R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta =
        S.counterexample.good.gamma (Fin.last S.counterexample.hierarchy.dividerCount) eta)) (_ :
        (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (eta a : Fin k) (_
        : eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount)) (_ : a ∈ R.counterexample.good.gamma (Fin.last
        R.counterexample.hierarchy.dividerCount) eta) (t : Fin T.length) (_ :
        (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) : TreeSequence G
        e0).length ≤ (↑t : ℕ)) (_ : (↑t : ℕ) < (↑(HierarchyFirstMissingPosition R.coloring T eta)
        : ℕ)), R.coloring (T.edge t) ≠ some a)) (_ : (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (c : Fin k) (j :
        Fin (B.length + (1 : ℕ))) (_ : (HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount) : TreeSequence G e0).length < (↑j : ℕ)) (_ : c ∈ MissingColors G
        R.coloring (B.vertex j)), c ∉ TreeMissingColors R.coloring (HierarchyStarredStage
        C.hierarchy (Fin.last C.hierarchy.dividerCount) : TreeSequence G e0))) (_ : (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∀ c ∉ TreeMissingColors R.coloring (HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount) : TreeSequence G e0), c ∉ HierarchyStoredColorsAt
        R.counterexample.hierarchy (Fin.last R.counterexample.hierarchy.dividerCount) → c ∉
        TashkinovStoredColors R.corresponding.replacementETT.series.data (Fin.last
        R.corresponding.replacementETT.rounds))) (_ : (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (j : ℕ) (_ : (1 :
        ℕ) ≤ j) (_ : j < T.length - (HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount) : TreeSequence G e0).length),
    ∀ c ∈ MissingColors G R.coloring ((HierarchyFullTailPrefix C j).vertex (Fin.last
        (HierarchyFullTailPrefix C j).length)),
    ∀ (t : Fin T.length), (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) :
        TreeSequence G e0).length ≤ (↑t : ℕ) → (↑t : ℕ) < (HierarchyStarredStage C.hierarchy
        (Fin.last C.hierarchy.dividerCount) : TreeSequence G e0).length + j → R.coloring (T.edge
        t) = some c → TreeIncidentEdge (R.corresponding.replacementETT.series.data.tree (Fin.last
        R.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧ c ∈ TashkinovStoredColors
        R.corresponding.replacementETT.series.data (Fin.last
        R.corresponding.replacementETT.rounds))) (_ : (
    ∀ (t : Fin T.length) (_ : (HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount) : TreeSequence G e0).length + HierarchyPathNumber C.hierarchy ≤
        (↑t : ℕ)), G.ends (T.edge t) = s(T.vertex t.castSucc, T.vertex t.succ))) (_ : (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∀ eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount),
    ∀ (f : E),
    ∃ a ∈ R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta,
        R.coloring f ≠ some a)) (m : ℕ) (_ : HierarchyPathNumber C.hierarchy ≤ m) (_ : m <
        HierarchyFullTailLength C - (1 : ℕ)) (P : HierarchyReplacementPresentation G k e0 input T
        phi ett base C ctx),
    ∀ alpha ∈ MissingColors G P.coloring ((HierarchyFullTailPrefix C m).vertex (Fin.last
        (HierarchyFullTailPrefix C m).length)), alpha ∈ MissingColors G P.coloring (T.vertex
        (Fin.last T.length)) → alpha ∉ HierarchyStoredColorsAt P.counterexample.hierarchy
        (Fin.last P.counterexample.hierarchy.dividerCount) → m + (1 : ℕ) ∈
        HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx

private theorem helper_branch_520.{u_1, u_2} :
    helperBranch520Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hsituation P alpha
  set A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)
  intro hlen B vertexMem firstAt stageSwitch gammaTransport gammaChoice m hmLower P alpha haLast
      hmT X hAX hXB hAXlt jm jnext tnext haM theta htheta nextMember excNext excM avoidNext
      hThetaStored
  obtain ⟨gamma, hgamma, _⟩ := gammaChoice P theta hThetaStored (T.edge tnext)
  obtain ⟨P1, hmissing1, _, _, hterminal1⟩ := stageSwitch P X hAX hAXlt hXB
    gamma alpha theta hThetaStored hgamma
    (by rw [firstAt P theta jnext htheta]; exact le_rfl)
    jm (by dsimp [jm]; omega) (by dsimp [jm, X, TreeSequencePrefix]; omega)
    haM (Or.inr haLast) (avoidNext P theta gamma hThetaStored hgamma htheta)
    (excM P alpha haM)
  have hgLast : gamma ∈ MissingColors G P1.coloring (T.vertex (Fin.last T.length)) := hterminal1
      haLast
  have htheta1 : theta ∈ MissingColors G P1.coloring (B.vertex jnext) := by
    rw [hmissing1 _ (vertexMem B jnext)]; exact htheta
  obtain ⟨hThetaStored1, heqGamma⟩ := gammaTransport P P1 theta hThetaStored
  have hgamma1 : gamma ∈ P1.counterexample.good.gamma
      (Fin.last P1.counterexample.hierarchy.dividerCount) theta := by
    rw [← heqGamma]; exact hgamma
  obtain ⟨P2, hmissing2, _, hterminal2, _⟩ := stageSwitch P1 X hAX hAXlt hXB
    gamma theta theta hThetaStored1 hgamma1
    (by rw [firstAt P1 theta jnext htheta1]; exact le_rfl)
    jnext (by dsimp [jnext]; omega) (by rfl)
    htheta1 (Or.inl hgLast) (avoidNext P1 theta gamma hThetaStored1 hgamma1 htheta1)
    (excNext P1 theta htheta1)
  exact nextMember P2 theta (by rw [hmissing2 _ (vertexMem B jnext)]; exact htheta1)
    (hterminal2 hgLast)

private noncomputable abbrev helperCS615.{u_1, u_2} :
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
                                        (alpha theta : Fin k) →
                                          let sigma : PartialEdgeColoring E k :=
                                            TwoColorComponentSwap G P.coloring alpha theta
                                              (Sum.inl (T.vertex (Fin.last T.length)));
                                          (corr :
                                              CorrespondingExtendedTashkinovTree G k e0
                                                P.corresponding.replacementETT sigma T) →
                                            MaximumProperty corr.replacementETT →
                                              (bs : HierarchyBase corr.replacementETT sigma) →
                                                (K : TashkinovHierarchy corr.replacementETT bs) →
                                                  GoodHierarchy K →
                                                    ¬ColoredVertexSetElementary G sigma
                                                          (TreeSequenceVertexSet T) →
                                                      HierarchyCounterexample bs := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha theta sigma corr hmaximum bs K
      goodK hnot
  exact {
    positive := by rw [corr.rungAgreement]; exact P.counterexample.positive
    hierarchy := K
    good := goodK
    maximum := hmaximum
    notElementary := hnot }

private theorem helper_continuation_613.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (hsituation :
        HierarchyPathNumber C.hierarchy = (1 : ℕ)) (_ : HierarchyReplacementPresentation G k e0
        input T phi ett base C ctx) (_ : Fin k) (_ : (
    ∀ {X Y Z : TreeSequence G e0} (_ : TreeSequenceInitialSegment X Y) (_ :
        TreeSequenceInitialSegment Y Z), TreeSequenceInitialSegment X Z)),
    let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount);
    ∀ (_ : (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount) = A)) (hlen : (4 : ℕ) ≤ T.length),
    let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ))
        (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) => (
    by
            omega
    )) (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) => (
    by
            omega
    ));
    ∀ (_ : TreeSequenceInitialSegment B T) (_ : (
    ∀ (U : TreeSequence G e0) (j : Fin (U.length + (1 : ℕ))), U.vertex j ∈ TreeSequenceVertexSet
        U)) (m : ℕ) (hmLower : HierarchyPathNumber C.hierarchy ≤ m) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∀ alpha ∈ MissingColors G P.coloring (T.vertex (Fin.last T.length)), alpha ∉
        HierarchyStoredColorsAt P.counterexample.hierarchy (Fin.last
        P.counterexample.hierarchy.dividerCount) →
    ∀ (hmT : A.length + (m + (1 : ℕ)) < T.length),
    let X : TreeSequence G e0 := TreeSequencePrefix T (A.length + (m + (1 : ℕ))) (
    have this : (1 : ℕ) ≤ A.length := A.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤
        A.length + (m + (1 : ℕ))) => (
    by
            omega
    )) (Decidable.byContradiction fun (a : ¬A.length + (m + (1 : ℕ)) ≤ T.length) => (
    by
            omega
    ));
    let jm : Fin (B.length + (1 : ℕ)) := (⟨A.length + m, id (Decidable.byContradiction fun (a :
        ¬A.length + m < T.length - (1 : ℕ) + (1 : ℕ)) => (
    by
                omega
    ))⟩ : Fin (B.length + (1 : ℕ)));
    let jnext : Fin (B.length + (1 : ℕ)) := (⟨A.length + (m + (1 : ℕ)), id
        (Decidable.byContradiction fun (a : ¬A.length + (m + (1 : ℕ)) < T.length - (1 : ℕ) + (1 :
        ℕ)) => (
    by
                omega
    ))⟩ : Fin (B.length + (1 : ℕ)));
    ∀ theta ∈ MissingColors G P.coloring (B.vertex jnext), (
    ∀ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∀ c ∈ MissingColors G S.coloring (B.vertex jnext), c ∈ MissingColors G S.coloring (T.vertex
        (Fin.last T.length)) → m + (1 : ℕ) ∈ HierarchyEligibleCommonMissingIndices G k e0 input T
        phi ett base C ctx) → theta ∉ HierarchyStoredColorsAt P.counterexample.hierarchy (Fin.last
        P.counterexample.hierarchy.dividerCount) → (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → P.coloring (T.edge t) ≠ some
        alpha) → alpha ≠ theta → (↑(HierarchyFirstMissingPosition P.coloring T alpha) : ℕ) = (↑jm
        : ℕ) → (↑(HierarchyFirstMissingPosition P.coloring T theta) : ℕ) = (↑jnext : ℕ) →
        TreeVertexOrder T (T.vertex (HierarchyFirstMissingPosition P.coloring T alpha)) (T.vertex
        (HierarchyFirstMissingPosition P.coloring T theta)) → ColoredVertexSetElementary G
        P.coloring (TreeSequenceVertexSet (HierarchyFullTailPrefix P.counterexample
        (HierarchyFullTailLength P.counterexample - (1 : ℕ)))) → alpha ∈ TreeMissingColors
        P.coloring (HierarchyFullTailPrefix P.counterexample (HierarchyFullTailLength
        P.counterexample - (1 : ℕ))) ∧ theta ∈ TreeMissingColors P.coloring
        (HierarchyFullTailPrefix P.counterexample (HierarchyFullTailLength P.counterexample - (1 :
        ℕ))) → (
    ∀ x ∈ TreeSequenceVertexSet B, MissingColors G (TwoColorComponentSwap G P.coloring alpha theta
        (Sum.inl (T.vertex (Fin.last T.length)))) x = MissingColors G P.coloring x) →
    let _ : PartialEdgeColoring E k := TwoColorComponentSwap G P.coloring alpha theta (Sum.inl
        (T.vertex (Fin.last T.length))); (
    ∀ v ∈ TreeSequenceVertexSet A, TreeVertexOrder T v (T.vertex (HierarchyFirstMissingPosition
        P.coloring T alpha))) → m + (1 : ℕ) ∈ HierarchyEligibleCommonMissingIndices G k e0 input T
        phi ett base C ctx := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hsituation P alpha trans A starEq hlen B
      hBT vertexMem m hmLower P alpha haLast hAlphaStored hmT X jm jnext theta htheta nextMember
      hThetaStored haUnused hne iaEq ibEq hordered hprefixP hmissingP hmissing sigma hprecedes
  have hunusedBetween : alpha ∉ (Finset.univ.filter fun c => ∃ t : Fin T.length,
      (HierarchyFirstMissingPosition P.coloring T alpha).val ≤ t.val ∧
      t.val < (HierarchyFirstMissingPosition P.coloring T theta).val ∧
      P.coloring (T.edge t) = some c) := by
    intro hh
    obtain ⟨_, t, hlo, hhi, hc⟩ := Finset.mem_filter.mp hh
    rw [iaEq] at hlo
    rw [ibEq] at hhi
    exact haUnused t (by dsimp [jm] at hlo; omega) hhi hc
  obtain ⟨_, _, _, _, corr, hmaximum, bs, K, goodK, hsameGood⟩ :=
    StableChangeCaseThree G k e0 P.corresponding.replacementInput T P.coloring
      P.corresponding.replacementETT P.replacementBase P.counterexample
      P.minimumContext.proper P.minimumContext.oneEdgeUncolored P.minimumContext.lowerRung
      P.minimumContext.fewerDividers P.minimumContext.lexicographicMinimality hprefixP
      P.minimumContext.largeMissingSet alpha theta hne hmissingP _ sigma rfl
      (by rw [starEq P]; exact hprecedes) hordered
      ⟨hAlphaStored, hThetaStored⟩ hunusedBetween
  have hthetaLast : theta ∈ MissingColors G sigma (T.vertex (Fin.last T.length)) :=
    (TwoColorComponentSwapMissingBehavior G P.coloring alpha theta hne
      P.minimumContext.proper (Sum.inl (T.vertex (Fin.last T.length)))).2.1 _ (by rfl) haLast
  have hthetaNext : theta ∈ MissingColors G sigma (B.vertex jnext) := by
    rw [hmissing _ (vertexMem B jnext)]
    exact htheta
  have hnot : ¬ ColoredVertexSetElementary G sigma (TreeSequenceVertexSet T) := by
    intro he
    exact Finset.disjoint_left.mp (he
      (TreeSequenceInitialSegmentVertexSetSubset hBT (vertexMem B jnext))
      (vertexMem T (Fin.last T.length)) (by
        intro hh
        have hh := T.vertex_injective ((hBT.2.1 jnext).trans hh)
        have hh := congrArg Fin.val hh; dsimp [jnext] at hh; omega)) hthetaNext hthetaLast
  let CS : HierarchyCounterexample bs := by
    exact @helperCS615 (@V) (@E) inferInstance inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha) (@theta) (@corr)
        (@hmaximum) (@bs) (@K) (@goodK) (@hnot)
  obtain ⟨S, hS⟩ := HierarchyReplacementPresentationTrans G k e0 input T phi ett base C ctx
    P sigma corr bs CS hsameGood
  exact nextMember S theta (by rw [hS]; exact hthetaNext) (by rw [hS]; exact hthetaLast)

private theorem helper_branch_542.{u_1, u_2} :
    helperBranch542Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hsituation P alpha componentData trans A
      starEq hAT hlen B hBT fullB elementary vertexMem firstAt outsideA notRaw m hmLower P alpha
      ha haLast hAlphaStored hmT X jm jnext haM theta htheta nextMember excM hThetaStored
  have haOutside := outsideA P alpha jm (by dsimp [jm]; omega) haM
  have hthetaOutside := outsideA P theta jnext (by dsimp [jnext]; omega) htheta
  have haRaw := notRaw P alpha haOutside hAlphaStored
  have hthetaRaw := notRaw P theta hthetaOutside hThetaStored
  have haUnused : ∀ t : Fin T.length, A.length ≤ t.val → t.val < X.length →
      P.coloring (T.edge t) ≠ some alpha := by
    intro t hlo hhi hc
    exact haRaw (excM P alpha haM t hlo hhi hc).2
  have hne : alpha ≠ theta := by
    intro he
    have hvertices : B.vertex jm ≠ B.vertex jnext := by
      intro hh
      have hh := congrArg Fin.val (B.vertex_injective hh)
      dsimp [jm, jnext] at hh
      omega
    exact Finset.disjoint_left.mp (elementary P
      (vertexMem B jm) (vertexMem B jnext) hvertices) haM (he ▸ htheta)
  have iaEq := firstAt P alpha jm haM
  have ibEq := firstAt P theta jnext htheta
  have jaEq : Fin.castLE (Nat.succ_le_succ hBT.1) jm =
      HierarchyFirstMissingPosition P.coloring T alpha := Fin.ext iaEq.symm
  have jbEq : Fin.castLE (Nat.succ_le_succ hBT.1) jnext =
      HierarchyFirstMissingPosition P.coloring T theta := Fin.ext ibEq.symm
  have hordered : TreeVertexOrder T
      (T.vertex (HierarchyFirstMissingPosition P.coloring T alpha))
      (T.vertex (HierarchyFirstMissingPosition P.coloring T theta)) :=
    ⟨_, _, rfl, rfl, by dsimp [jm, jnext] at iaEq ibEq; omega⟩
  have hunused : alpha ∉ (Finset.univ.filter fun c => ∃ t : Fin T.length,
      A.length ≤ t.val ∧ t.val < (HierarchyFirstMissingPosition P.coloring T theta).val ∧
        P.coloring (T.edge t) = some c) := by
    intro hh
    obtain ⟨_, t, hlo, hhi, hc⟩ := Finset.mem_filter.mp hh
    exact haUnused t hlo (by rw [ibEq] at hhi; exact hhi) hc
  have haB : alpha ∈ TreeMissingColors P.coloring B :=
    Finset.mem_biUnion.mpr ⟨B.vertex jm, vertexMem B jm, haM⟩
  have hthetaB : theta ∈ TreeMissingColors P.coloring B :=
    Finset.mem_biUnion.mpr ⟨B.vertex jnext, vertexMem B jnext, htheta⟩
  have hprefixP : ColoredVertexSetElementary G P.coloring
      (TreeSequenceVertexSet (HierarchyFullTailPrefix P.counterexample
        (HierarchyFullTailLength P.counterexample - 1))) := by
    rw [fullB P]
    exact elementary P
  have hmissingP : alpha ∈ TreeMissingColors P.coloring
      (HierarchyFullTailPrefix P.counterexample (HierarchyFullTailLength P.counterexample - 1)) ∧
      theta ∈ TreeMissingColors P.coloring
      (HierarchyFullTailPrefix P.counterexample (HierarchyFullTailLength P.counterexample - 1))
         := by
    rw [fullB P]
    exact ⟨haB, hthetaB⟩
  have change := ChangeLemma G k e0 P.corresponding.replacementInput T P.coloring
    P.corresponding.replacementETT P.replacementBase P.counterexample
    P.minimumContext.proper P.minimumContext.oneEdgeUncolored P.minimumContext.lowerRung
    P.minimumContext.fewerDividers P.minimumContext.lexicographicMinimality hprefixP
    P.minimumContext.largeMissingSet alpha theta hne hmissingP
    (by dsimp only; rw [starEq P]; intro _; exact ⟨hordered, hunused⟩)
  have hdisStored : Disjoint ({alpha, theta} : Finset (Fin k))
      (HierarchyStoredColorsAt P.counterexample.hierarchy
        (Fin.last P.counterexample.hierarchy.dividerCount)) := by
    apply Finset.disjoint_left.mpr
    intro c hc hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl
    · exact hAlphaStored hd
    · exact hThetaStored hd
  have hdisRaw : Disjoint ({alpha, theta} : Finset (Fin k))
      (TashkinovStoredColors P.corresponding.replacementETT.series.data
        (Fin.last P.corresponding.replacementETT.rounds)) := by
    apply Finset.disjoint_left.mpr
    intro c hc hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl
    · exact haRaw hd
    · exact hthetaRaw hd
  have hsame : TwoColorComponent G P.coloring alpha theta (Sum.inl (B.vertex jm)) =
      TwoColorComponent G P.coloring alpha theta (Sum.inl (B.vertex jnext)) := by
    have hh : TwoColorComponent G P.coloring alpha theta
        (Sum.inl (T.vertex (HierarchyFirstMissingPosition P.coloring T alpha))) =
        TwoColorComponent G P.coloring alpha theta
        (Sum.inl (T.vertex (HierarchyFirstMissingPosition P.coloring T theta))) := by
      by_cases hq : P.counterexample.hierarchy.dividerCount = 0
      · exact change.2.1 ⟨hq, Or.inr hdisRaw⟩
      · exact change.1 ⟨by omega, Or.inr hdisStored⟩
    rw [← jaEq, ← jbEq, hBT.2.1 jm, hBT.2.1 jnext] at hh
    exact hh
  obtain ⟨hdis, hpath, hmissing⟩ := componentData P.coloring alpha theta hne
    P.minimumContext.proper (TreeSequenceVertexSet B) (elementary P)
    (B.vertex jm) (B.vertex jnext) (T.vertex (Fin.last T.length))
    (vertexMem B jm) (vertexMem B jnext)
    (by intro hh; have hh := congrArg Fin.val (B.vertex_injective hh)
        dsimp [jm, jnext] at hh; omega)
    (by intro hh; have hh := T.vertex_injective (hh.trans (hBT.2.1 jm).symm)
        have hh := congrArg Fin.val hh; dsimp [jm] at hh; omega)
    (by intro hh; have hh := T.vertex_injective (hh.trans (hBT.2.1 jnext).symm)
        have hh := congrArg Fin.val hh; dsimp [jnext] at hh; omega)
    haM htheta (Or.inl haLast) hsame
  let sigma := TwoColorComponentSwap G P.coloring alpha theta
    (Sum.inl (T.vertex (Fin.last T.length)))
  have hprecedes : ∀ v ∈ TreeSequenceVertexSet A,
      TreeVertexOrder T v (T.vertex (HierarchyFirstMissingPosition P.coloring T alpha)) := by
    intro v hv
    obtain ⟨j, hj⟩ : ∃ j, A.vertex j = v := by simpa [TreeSequenceVertexSet] using hv
    refine ⟨Fin.castLE (Nat.succ_le_succ hAT.1) j, _, (hAT.2.1 j).trans hj, rfl, ?_⟩
    change j.val < (HierarchyFirstMissingPosition P.coloring T alpha).val
    rw [iaEq]
    have := j.isLt
    dsimp [jm]
    omega
  exact helper_continuation_613 G k e0 input T phi ett base C ctx hsituation P alpha trans starEq
      hlen hBT vertexMem m hmLower
      P alpha haLast hAlphaStored hmT theta htheta nextMember hThetaStored haUnused hne iaEq ibEq
      hordered hprefixP hmissingP hmissing hprecedes
private theorem helper_excM_924.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (hsituation :
        HierarchyPathNumber C.hierarchy = (1 : ℕ)),
    let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount);
    ∀ (_ : TreeSequenceInitialSegment A T) (hlen : (4 : ℕ) ≤ T.length),
    let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ))
        (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) => (
    by
            omega
    )) (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) => (
    by
            omega
    ));
    ∀ (_ : (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (j : ℕ) (_ : (1 :
        ℕ) ≤ j) (_ : j < T.length - A.length),
    ∀ c ∈ MissingColors G R.coloring ((HierarchyFullTailPrefix C j).vertex (Fin.last
        (HierarchyFullTailPrefix C j).length)),
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < A.length + j → R.coloring (T.edge t) =
        some c → TreeIncidentEdge (R.corresponding.replacementETT.series.data.tree (Fin.last
        R.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧ c ∈ TashkinovStoredColors
        R.corresponding.replacementETT.series.data (Fin.last
        R.corresponding.replacementETT.rounds))) (_ : (
    ∀ (t : Fin T.length) (_ : A.length + HierarchyPathNumber C.hierarchy ≤ (↑t : ℕ)), G.ends
        (T.edge t) = s(T.vertex t.castSucc, T.vertex t.succ))) (m : ℕ) (hmLower :
        HierarchyPathNumber C.hierarchy ≤ m) (_ : (1 : ℕ) ≤ m) (hmT : A.length + (m + (1 : ℕ)) <
        T.length),
    let X : TreeSequence G e0 := TreeSequencePrefix T (A.length + (m + (1 : ℕ))) (
    have this : (1 : ℕ) ≤ A.length := A.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤
        A.length + (m + (1 : ℕ))) =>
    by omega
    ) (Decidable.byContradiction fun (a : ¬A.length + (m + (1 : ℕ)) ≤ T.length) => (
    by
            omega
    ));
    let Y : TreeSequence G e0 := TreeSequencePrefix T (A.length + m) (
    have this : (1 : ℕ) ≤ A.length := A.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤
        A.length + m) =>
    by omega
    ) (Decidable.byContradiction fun (a : ¬A.length + m ≤ T.length) =>
    by omega
    );
    let jm : Fin (B.length + (1 : ℕ)) := (⟨A.length + m, id (Decidable.byContradiction fun (a :
        ¬A.length + m < T.length - (1 : ℕ) + (1 : ℕ)) =>
    by omega
    )⟩ : Fin (B.length + (1 : ℕ)));
    let _ : Fin T.length := (⟨A.length + m,
    by omega
    ⟩ : Fin T.length);
    ∀ (_ : HierarchyFullTailPrefix C m = Y) (_ : Y.vertex (Fin.last Y.length) = B.vertex jm) (R :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∀ b ∈ MissingColors G R.coloring (B.vertex jm),
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → R.coloring (T.edge t) = some
        b → TreeIncidentEdge (R.corresponding.replacementETT.series.data.tree (Fin.last
        R.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧ b ∈ TashkinovStoredColors
        R.corresponding.replacementETT.series.data (Fin.last
        R.corresponding.replacementETT.rounds) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hsituation A hAT hlen B tailException
      consecutive m hmLower hm hmT X Y jm tnext hfullY hYvertex R b hb t hlo hhi hcol
  by_cases ht : t.val < A.length + m
  · exact tailException R m (by omega) (by have := hAT.1; omega) b
      (by rw [hfullY, hYvertex]; exact hb) t hlo ht hcol
  · have htEq : t = tnext := Fin.ext
      (by change t.val < A.length + (m + 1) at hhi; dsimp [tnext]; omega)
    subst t
    have he := consecutive tnext (by dsimp [tnext]; omega)
    have hv : T.vertex tnext.castSucc = B.vertex jm := rfl
    have hi : Incident G (B.vertex jm) (T.edge tnext) := by
      rw [Incident, he, hv]
      exact Sym2.mem_mk_left _ _
    exact ((Finset.mem_sdiff.mp hb).2
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, T.edge tnext, hi, hcol⟩)).elim

private theorem helper_advance_481.{u_1, u_2} :
    helperAdvance481Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hsituation hvertexMissing i P alpha
      componentData trans common
  set A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)
  intro starEq hAT hlen B hBT fullB elementary vertexMem firstAt stageSwitch gammaTransport
      gammaUnused outsideA notRaw tailException consecutive gammaChoice m hmLower hmUpper P alpha
      ha haLast hAlphaStored
  have hm : 1 ≤ m := by simpa only [hsituation] using hmLower
  have hmT : A.length + (m + 1) < T.length := by
    change m < (T.length - A.length) - 1 at hmUpper
    have := hAT.1
    omega
  let X := TreeSequencePrefix T (A.length + (m + 1)) (by have := A.positive; omega) (by omega)
  let Y := TreeSequencePrefix T (A.length + m) (by have := A.positive; omega) (by omega)
  have hXT : TreeSequenceInitialSegment X T := ⟨by exact le_of_lt hmT, fun _ => rfl, fun _ => rfl⟩
  have hAX : TreeSequenceInitialSegment A X := common hAT hXT
      (by dsimp [X, TreeSequencePrefix]; omega)
  have hXB : TreeSequenceInitialSegment X B :=
    common hXT hBT (by dsimp [X, B, TreeSequencePrefix]; omega)
  have hAXlt : A.length < X.length := by dsimp [X, TreeSequencePrefix]; omega
  let jm : Fin (B.length + 1) := ⟨A.length + m, by dsimp [B, TreeSequencePrefix]; omega⟩
  let jnext : Fin (B.length + 1) := ⟨A.length + (m + 1), by dsimp [B, TreeSequencePrefix]; omega⟩
  let tnext : Fin T.length := ⟨A.length + m, by omega⟩
  have hfullY : HierarchyFullTailPrefix C m = Y := by
    have hn : min (A.length + m) T.length = A.length + m := min_eq_left (by omega)
    simp only [HierarchyFullTailPrefix]
    change TreeSequencePrefix T (min (A.length + m) T.length) _ _ = Y
    simp only [hn]
    rfl
  have hfullX : HierarchyFullTailPrefix C (m + 1) = X := by
    have hn : min (A.length + (m + 1)) T.length = A.length + (m + 1) := min_eq_left (by omega)
    simp only [HierarchyFullTailPrefix]
    change TreeSequencePrefix T (min (A.length + (m + 1)) T.length) _ _ = X
    simp only [hn]
    rfl
  have hYvertex : Y.vertex (Fin.last Y.length) = B.vertex jm := rfl
  have hXvertex : X.vertex (Fin.last X.length) = B.vertex jnext := rfl
  have haM : alpha ∈ MissingColors G P.coloring (B.vertex jm) := by
    rw [hfullY, hYvertex] at ha
    exact ha
  obtain ⟨theta, htheta⟩ := hvertexMissing P.coloring P.minimumContext.proper
    P.minimumContext.oneEdgeUncolored (B.vertex jnext)
  have nextMember (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
      (c : Fin k) (hc : c ∈ MissingColors G S.coloring (B.vertex jnext))
      (hcLast : c ∈ MissingColors G S.coloring (T.vertex (Fin.last T.length))) :
      m + 1 ∈ HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, S, c, ?_, hcLast⟩
    rw [hfullX, hXvertex]
    exact hc
  have excNext (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
      (b : Fin k) (hb : b ∈ MissingColors G R.coloring (B.vertex jnext))
      (t : Fin T.length) (hlo : A.length ≤ t.val) (hhi : t.val < X.length)
      (hcol : R.coloring (T.edge t) = some b) :
      TreeIncidentEdge (R.corresponding.replacementETT.series.data.tree
        (Fin.last R.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧
      b ∈ TashkinovStoredColors R.corresponding.replacementETT.series.data
        (Fin.last R.corresponding.replacementETT.rounds) := by
    apply tailException R (m + 1) (by omega) (by have := hAT.1; omega) b
      (by rw [hfullX, hXvertex]; exact hb) t hlo
      (by exact hhi) hcol
  have excM (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
      (b : Fin k) (hb : b ∈ MissingColors G R.coloring (B.vertex jm))
      (t : Fin T.length) (hlo : A.length ≤ t.val) (hhi : t.val < X.length)
      (hcol : R.coloring (T.edge t) = some b) :
      TreeIncidentEdge (R.corresponding.replacementETT.series.data.tree
        (Fin.last R.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧
      b ∈ TashkinovStoredColors R.corresponding.replacementETT.series.data
        (Fin.last R.corresponding.replacementETT.rounds) := by
    exact helper_excM_924 G k e0 input T phi ett base C ctx hsituation hAT hlen tailException
        consecutive m hmLower hm hmT
        hfullY hYvertex R b hb t hlo hhi hcol
  have avoidNext (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
      (eta a : Fin k)
      (heta : eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy
        (Fin.last R.counterexample.hierarchy.dividerCount))
      (ha : a ∈ R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta)
      (he : eta ∈ MissingColors G R.coloring (B.vertex jnext)) :
      ∀ t : Fin T.length, A.length ≤ t.val → t.val < X.length →
        R.coloring (T.edge t) ≠ some a := by
    intro t hlo hhi
    apply gammaUnused R eta a heta ha t hlo
    rw [firstAt R eta jnext he]
    exact hhi
  have avoidM (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
      (eta a : Fin k)
      (heta : eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy
        (Fin.last R.counterexample.hierarchy.dividerCount))
      (ha : a ∈ R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta)
      (he : eta ∈ MissingColors G R.coloring (B.vertex jm))
      (hgap : R.coloring (T.edge tnext) ≠ some a) :
      ∀ t : Fin T.length, A.length ≤ t.val → t.val < X.length →
        R.coloring (T.edge t) ≠ some a := by
    intro t hlo hhi
    by_cases ht : t.val < A.length + m
    · apply gammaUnused R eta a heta ha t hlo
      rw [firstAt R eta jm he]
      exact ht
    · have htEq : t = tnext := Fin.ext
        (by change t.val < A.length + (m + 1) at hhi; dsimp [tnext]; omega)
      simpa only [htEq] using hgap
  by_cases hThetaStored : theta ∈ HierarchyStoredColorsAt P.counterexample.hierarchy
      (Fin.last P.counterexample.hierarchy.dividerCount)
  · exact @helper_branch_520 V E inferInstance inferInstance inferInstance inferInstance G k e0
      input T phi ett base C ctx hsituation P alpha hlen vertexMem firstAt stageSwitch
      gammaTransport gammaChoice m hmLower P alpha haLast hmT hAX hXB hAXlt haM theta htheta
      nextMember excNext excM avoidNext hThetaStored
  · exact @helper_branch_542 V E inferInstance inferInstance inferInstance inferInstance G k e0
      input T phi ett base C ctx hsituation P alpha componentData trans starEq hAT hlen hBT fullB
      elementary vertexMem firstAt outsideA notRaw m hmLower P alpha ha haLast hAlphaStored hmT
      haM theta htheta nextMember excM hThetaStored
private theorem helper_outsideA_1255.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (_ : ℕ) (_ : (
    ∀ {X Y Z : TreeSequence G e0} (_ : TreeSequenceInitialSegment X Y) (_ :
        TreeSequenceInitialSegment Y Z), TreeSequenceInitialSegment X Z)),
    let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount);
    ∀ (_ : TreeSequenceInitialSegment A T) (hlen : (4 : ℕ) ≤ T.length),
    let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ))
        (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) =>
    by omega
    ) (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) =>
    by omega
    );
    ∀ (_ : TreeSequenceInitialSegment B T) (_ : TreeSequenceInitialSegment A B) (_ : (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        ColoredVertexSetElementary G R.coloring (TreeSequenceVertexSet B))) (_ : (
    ∀ (U : TreeSequence G e0) (j : Fin (U.length + (1 : ℕ))), U.vertex j ∈ TreeSequenceVertexSet
        U)) (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (c : Fin k)
        (j : Fin (B.length + (1 : ℕ))) (_ : A.length < (↑j : ℕ)) (_ : c ∈ MissingColors G
        R.coloring (B.vertex j)), c ∉ TreeMissingColors R.coloring A := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx i trans A hAT hlen B hBT hAB elementary
      vertexMem R c j hj hc
  clear * - R c j hj hc hAT hBT hAB elementary vertexMem
  rintro hm
  obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hm
  obtain ⟨a, ha⟩ : ∃ a, A.vertex a = v := by simpa [TreeSequenceVertexSet] using hv
  have hne : v ≠ B.vertex j := by
    intro he
    have hh := T.vertex_injective ((hAT.2.1 a).trans
      (ha.trans (he.trans (hBT.2.1 j).symm)))
    have hh := congrArg Fin.val hh
    have := a.isLt
    change a.val = j.val at hh
    omega
  exact Finset.disjoint_left.mp (elementary R
    (TreeSequenceInitialSegmentVertexSetSubset hAB hv) (vertexMem B j) hne) hcv hc

private theorem helper_trans_1517.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E) (_ : ℕ)
        {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Y → TreeSequenceInitialSegment Y
        Z → TreeSequenceInitialSegment X Z := by
  classical
  intro V E G e0 i X Y Z hXY hYZ
  clear * - hXY hYZ
  refine ⟨hXY.1.trans hYZ.1, ?_, ?_⟩
  · intro i
    exact (hYZ.2.1 (Fin.castLE (Nat.succ_le_succ hXY.1) i)).trans (hXY.2.1 i)
  · intro i
    exact (hYZ.2.2 (Fin.castLE hXY.1 i)).trans (hXY.2.2 i)

private theorem helper_common_1527.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E) (_ : ℕ), (
    ∀ {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Y → TreeSequenceInitialSegment Y Z
        → TreeSequenceInitialSegment X Z) →
    ∀ {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Z → TreeSequenceInitialSegment Y Z
        → X.length ≤ Y.length → TreeSequenceInitialSegment X Y := by
  classical
  intro V E G e0 i trans X Y Z hXZ hYZ hXY
  clear * - hXZ hYZ hXY
  refine ⟨hXY, ?_, ?_⟩
  · intro i
    exact (hYZ.2.1 (Fin.castLE (Nat.succ_le_succ hXY) i)).symm.trans (hXZ.2.1 i)
  · intro i
    exact (hYZ.2.2 (Fin.castLE hXY i)).symm.trans (hXZ.2.2 i)

private theorem helper_hAT_1558.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (_ : ℕ),
    let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount); TreeSequenceInitialSegment A T := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C i A
  have starNext (j : Fin (C.hierarchy.dividerCount + 1)) :
      TreeSequenceInitialSegment (HierarchyStarredStage C.hierarchy j)
        (C.hierarchy.stage j.succ) :=
    Fin.cases C.hierarchy.coreInsideFirst (fun i => C.hierarchy.nested i.succ) j
  simpa only [Fin.succ_last, C.hierarchy.terminalStage] using
    starNext (Fin.last C.hierarchy.dividerCount)

private theorem helper_fullB_1581.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (_ : ℕ),
    let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount); (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount) = A) → (3 : ℕ) ≤ T.length - A.length →
    ∀ (hlen : (4 : ℕ) ≤ T.length),
    let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ)) (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ) (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    );
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyFullTailPrefix R.counterexample (HierarchyFullTailLength R.counterexample - (1 :
        ℕ)) = B := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx i A starEq htail hlen B R
  have hn : min ((HierarchyStarredStage R.counterexample.hierarchy
      (Fin.last R.counterexample.hierarchy.dividerCount)).length +
      (HierarchyFullTailLength R.counterexample - 1)) T.length = T.length - 1 := by
    unfold HierarchyFullTailLength
    dsimp only
    rw [starEq R]
    omega
  simp only [HierarchyFullTailPrefix, hn]
  rfl

private theorem helper_elementary_1593.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (_ : ℕ)
      (hlen : (4 : ℕ) ≤ T.length),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (T.length - (1 : ℕ))
        (by
          have := GoldbergSeymour.TreeSequence.positive T
          omega)
        (by
          have := GoldbergSeymour.TreeSequence.positive T
          omega);
    (∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyFullTailPrefix R.counterexample
            (HierarchyFullTailLength R.counterexample - (1 : ℕ)) =
          B) →
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ColoredVertexSetElementary G R.coloring (TreeSequenceVertexSet B) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx i hlen B fullB R
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

private theorem helper_advance_1736.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C), HierarchyPathNumber
        C.hierarchy = (1 : ℕ) → (
    ∀ (mu : PartialEdgeColoring E k), IsProperEdgeColoring G mu → IsOneEdgeUncolored mu e0 →
    ∀ (v : V), (MissingColors G mu v).Nonempty) →
    ∀ (_ : ℕ), (
    ∀ (psi : PartialEdgeColoring E k) (a b : Fin k), a ≠ b → IsProperEdgeColoring G psi →
    ∀ (B : Finset V), ColoredVertexSetElementary G psi B →
    ∀ (u v w : V), u ∈ B → v ∈ B → u ≠ v → w ≠ u → w ≠ v → a ∈ MissingColors G psi u → b ∈
        MissingColors G psi v → a ∈ MissingColors G psi w ∨ b ∈ MissingColors G psi w →
        TwoColorComponent G psi a b (Sum.inl u) = TwoColorComponent G psi a b (Sum.inl v) →
        Disjoint (TwoColorComponent G psi a b (Sum.inl w)) (TwoColorComponent G psi a b (Sum.inl
        u)) ∧ TwoColorPathComponent G psi a b (Sum.inl w) ∧
    ∀ x ∈ B, MissingColors G (TwoColorComponentSwap G psi a b (Sum.inl w)) x = MissingColors G psi
        x) → (
    ∀ {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Y → TreeSequenceInitialSegment Y Z
        → TreeSequenceInitialSegment X Z) → (
    ∀ {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Z → TreeSequenceInitialSegment Y Z
        → X.length ≤ Y.length → TreeSequenceInitialSegment X Y) →
    let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount); (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount) = A) → TreeSequenceInitialSegment A T →
    ∀ (hlen : (4 : ℕ) ≤ T.length),
    let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ)) (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ) (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ); TreeSequenceInitialSegment B T → (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyFullTailPrefix R.counterexample (HierarchyFullTailLength R.counterexample - (1 :
        ℕ)) = B) → (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        ColoredVertexSetElementary G R.coloring (TreeSequenceVertexSet B)) → (
    ∀ (U : TreeSequence G e0) (j : Fin (U.length + (1 : ℕ))), U.vertex j ∈ TreeSequenceVertexSet
        U) → (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (c : Fin k) (j :
        Fin (B.length + (1 : ℕ))), c ∈ MissingColors G R.coloring (B.vertex j) →
        (↑(HierarchyFirstMissingPosition R.coloring T c) : ℕ) = (↑j : ℕ)) → (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (X : TreeSequence G
        e0), TreeSequenceInitialSegment A X → A.length < X.length → TreeSequenceInitialSegment X B
        →
    ∀ (a b eta : Fin k), eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount) → a ∈ R.counterexample.good.gamma (Fin.last
        R.counterexample.hierarchy.dividerCount) eta → (↑(HierarchyFirstMissingPosition R.coloring
        T eta) : ℕ) ≤ X.length →
    ∀ (jb : Fin (B.length + (1 : ℕ))), A.length < (↑jb : ℕ) → (↑jb : ℕ) ≤ X.length → b ∈
        MissingColors G R.coloring (B.vertex jb) → a ∈ MissingColors G R.coloring (T.vertex
        (Fin.last T.length)) ∨ b ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)) → (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → R.coloring (T.edge t) ≠ some
        a) → (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → R.coloring (T.edge t) = some
        b → TreeIncidentEdge (R.corresponding.replacementETT.series.data.tree (Fin.last
        R.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧ b ∈ TashkinovStoredColors
        R.corresponding.replacementETT.series.data (Fin.last
        R.corresponding.replacementETT.rounds)) →
    ∃ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), (
    ∀ v ∈ TreeSequenceVertexSet B, MissingColors G S.coloring v = MissingColors G R.coloring v) ∧
        (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → S.coloring (T.edge t) =
        R.coloring (T.edge t)) ∧ (a ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)) →
        b ∈ MissingColors G S.coloring (T.vertex (Fin.last T.length))) ∧ (b ∈ MissingColors G
        R.coloring (T.vertex (Fin.last T.length)) → a ∈ MissingColors G S.coloring (T.vertex
        (Fin.last T.length)))) → (
    ∀ (R S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∀ eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount), eta ∈ HierarchyStoredColorsAt
        S.counterexample.hierarchy (Fin.last S.counterexample.hierarchy.dividerCount) ∧
        R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta =
        S.counterexample.good.gamma (Fin.last S.counterexample.hierarchy.dividerCount) eta) → (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (eta a : Fin k),
        eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount) → a ∈ R.counterexample.good.gamma (Fin.last
        R.counterexample.hierarchy.dividerCount) eta →
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < (↑(HierarchyFirstMissingPosition
        R.coloring T eta) : ℕ) → R.coloring (T.edge t) ≠ some a) → (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (c : Fin k) (j :
        Fin (B.length + (1 : ℕ))), A.length < (↑j : ℕ) → c ∈ MissingColors G R.coloring (B.vertex
        j) → c ∉ TreeMissingColors R.coloring A) → (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∀ c ∉ TreeMissingColors R.coloring A, c ∉ HierarchyStoredColorsAt R.counterexample.hierarchy
        (Fin.last R.counterexample.hierarchy.dividerCount) → c ∉ TashkinovStoredColors
        R.corresponding.replacementETT.series.data (Fin.last
        R.corresponding.replacementETT.rounds)) → (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (j : ℕ), (1 : ℕ) ≤
        j → j < T.length - A.length →
    ∀ c ∈ MissingColors G R.coloring ((HierarchyFullTailPrefix C j).vertex (Fin.last
        (HierarchyFullTailPrefix C j).length)),
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < A.length + j → R.coloring (T.edge t) =
        some c → TreeIncidentEdge (R.corresponding.replacementETT.series.data.tree (Fin.last
        R.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧ c ∈ TashkinovStoredColors
        R.corresponding.replacementETT.series.data (Fin.last
        R.corresponding.replacementETT.rounds)) → (
    ∀ (t : Fin T.length), A.length + HierarchyPathNumber C.hierarchy ≤ (↑t : ℕ) → G.ends (T.edge
        t) = s(T.vertex t.castSucc, T.vertex t.succ)) → (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∀ eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount),
    ∀ (f : E),
    ∃ a ∈ R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta,
        R.coloring f ≠ some a) →
    ∀ (m : ℕ), HierarchyPathNumber C.hierarchy ≤ m → m < HierarchyFullTailLength C - (1 : ℕ) →
    ∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∀ alpha ∈ MissingColors G P.coloring ((HierarchyFullTailPrefix C m).vertex (Fin.last
        (HierarchyFullTailPrefix C m).length)), alpha ∈ MissingColors G P.coloring (T.vertex
        (Fin.last T.length)) → alpha ∉ HierarchyStoredColorsAt P.counterexample.hierarchy
        (Fin.last P.counterexample.hierarchy.dividerCount) → m + (1 : ℕ) ∈
        HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hsituation hvertexMissing i componentData
      trans common A starEq hAT hlen B hBT fullB elementary vertexMem firstAt stageSwitch
      gammaTransport gammaUnused outsideA notRaw tailException consecutive gammaChoice m hmLower
      hmUpper P alpha ha haLast hAlphaStored
  exact @helper_advance_481 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 input T phi ett base C ctx hsituation hvertexMissing i P alpha componentData trans
      common starEq hAT hlen hBT fullB elementary vertexMem firstAt stageSwitch
      gammaTransport gammaUnused outsideA notRaw tailException consecutive gammaChoice m
      hmLower hmUpper P alpha ha haLast hAlphaStored

private theorem helper_advance_2294.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C), HierarchyPathNumber
        C.hierarchy = (1 : ℕ) → (
    ∀ (mu : PartialEdgeColoring E k), IsProperEdgeColoring G mu → IsOneEdgeUncolored mu e0 →
    ∀ (v : V), (MissingColors G mu v).Nonempty) →
    ∀ (_ : ℕ), (
    ∀ (psi : PartialEdgeColoring E k) (a b : Fin k), a ≠ b → IsProperEdgeColoring G psi →
    ∀ (B : Finset V), ColoredVertexSetElementary G psi B →
    ∀ (u v w : V), u ∈ B → v ∈ B → u ≠ v → w ≠ u → w ≠ v → a ∈ MissingColors G psi u → b ∈
        MissingColors G psi v → a ∈ MissingColors G psi w ∨ b ∈ MissingColors G psi w →
        TwoColorComponent G psi a b (Sum.inl u) = TwoColorComponent G psi a b (Sum.inl v) →
        Disjoint (TwoColorComponent G psi a b (Sum.inl w)) (TwoColorComponent G psi a b (Sum.inl
        u)) ∧ TwoColorPathComponent G psi a b (Sum.inl w) ∧
    ∀ x ∈ B, MissingColors G (TwoColorComponentSwap G psi a b (Sum.inl w)) x = MissingColors G psi
        x) → (
    ∀ {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Y → TreeSequenceInitialSegment Y Z
        → TreeSequenceInitialSegment X Z) → (
    ∀ {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Z → TreeSequenceInitialSegment Y Z
        → X.length ≤ Y.length → TreeSequenceInitialSegment X Y) →
    let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount); (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount) = A) → (
    have A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount); TreeSequenceInitialSegment A T) →
    ∀ (hlen : (4 : ℕ) ≤ T.length),
    let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ)) (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ) (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ); TreeSequenceInitialSegment B T → (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyFullTailPrefix R.counterexample (HierarchyFullTailLength R.counterexample - (1 :
        ℕ)) = B) → (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        ColoredVertexSetElementary G R.coloring (TreeSequenceVertexSet B)) → (
    ∀ (U : TreeSequence G e0) (j : Fin (U.length + (1 : ℕ))), U.vertex j ∈ TreeSequenceVertexSet
        U) → (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (c : Fin k) (j :
        Fin (B.length + (1 : ℕ))), c ∈ MissingColors G R.coloring (B.vertex j) →
        (↑(HierarchyFirstMissingPosition R.coloring T c) : ℕ) = (↑j : ℕ)) → (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (X : TreeSequence G
        e0), TreeSequenceInitialSegment A X → A.length < X.length → TreeSequenceInitialSegment X B
        →
    ∀ (a b eta : Fin k), eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount) → a ∈ R.counterexample.good.gamma (Fin.last
        R.counterexample.hierarchy.dividerCount) eta → (↑(HierarchyFirstMissingPosition R.coloring
        T eta) : ℕ) ≤ X.length →
    ∀ (jb : Fin (B.length + (1 : ℕ))), A.length < (↑jb : ℕ) → (↑jb : ℕ) ≤ X.length → b ∈
        MissingColors G R.coloring (B.vertex jb) → a ∈ MissingColors G R.coloring (T.vertex
        (Fin.last T.length)) ∨ b ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)) → (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → R.coloring (T.edge t) ≠ some
        a) → (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → R.coloring (T.edge t) = some
        b → TreeIncidentEdge (R.corresponding.replacementETT.series.data.tree (Fin.last
        R.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧ b ∈ TashkinovStoredColors
        R.corresponding.replacementETT.series.data (Fin.last
        R.corresponding.replacementETT.rounds)) →
    ∃ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), (
    ∀ v ∈ TreeSequenceVertexSet B, MissingColors G S.coloring v = MissingColors G R.coloring v) ∧
        (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → S.coloring (T.edge t) =
        R.coloring (T.edge t)) ∧ (a ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)) →
        b ∈ MissingColors G S.coloring (T.vertex (Fin.last T.length))) ∧ (b ∈ MissingColors G
        R.coloring (T.vertex (Fin.last T.length)) → a ∈ MissingColors G S.coloring (T.vertex
        (Fin.last T.length)))) → (
    ∀ (R S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∀ eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount), eta ∈ HierarchyStoredColorsAt
        S.counterexample.hierarchy (Fin.last S.counterexample.hierarchy.dividerCount) ∧
        R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta =
        S.counterexample.good.gamma (Fin.last S.counterexample.hierarchy.dividerCount) eta) → (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (eta a : Fin k),
        eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount) → a ∈ R.counterexample.good.gamma (Fin.last
        R.counterexample.hierarchy.dividerCount) eta →
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < (↑(HierarchyFirstMissingPosition
        R.coloring T eta) : ℕ) → R.coloring (T.edge t) ≠ some a) → (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (c : Fin k) (j :
        Fin (B.length + (1 : ℕ))), A.length < (↑j : ℕ) → c ∈ MissingColors G R.coloring (B.vertex
        j) → c ∉ TreeMissingColors R.coloring A) → (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∀ c ∉ TreeMissingColors R.coloring A, c ∉ HierarchyStoredColorsAt R.counterexample.hierarchy
        (Fin.last R.counterexample.hierarchy.dividerCount) → c ∉ TashkinovStoredColors
        R.corresponding.replacementETT.series.data (Fin.last
        R.corresponding.replacementETT.rounds)) → (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (j : ℕ), (1 : ℕ) ≤
        j → j < T.length - A.length →
    ∀ c ∈ MissingColors G R.coloring ((HierarchyFullTailPrefix C j).vertex (Fin.last
        (HierarchyFullTailPrefix C j).length)),
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < A.length + j → R.coloring (T.edge t) =
        some c → TreeIncidentEdge (R.corresponding.replacementETT.series.data.tree (Fin.last
        R.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧ c ∈ TashkinovStoredColors
        R.corresponding.replacementETT.series.data (Fin.last
        R.corresponding.replacementETT.rounds)) → (
    ∀ (t : Fin T.length), A.length + HierarchyPathNumber C.hierarchy ≤ (↑t : ℕ) → G.ends (T.edge
        t) = s(T.vertex t.castSucc, T.vertex t.succ)) → (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∀ eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount),
    ∀ (f : E),
    ∃ a ∈ R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta,
        R.coloring f ≠ some a) →
    ∀ (m : ℕ), HierarchyPathNumber C.hierarchy ≤ m → m < HierarchyFullTailLength C - (1 : ℕ) →
    ∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∀ alpha ∈ MissingColors G P.coloring ((HierarchyFullTailPrefix C m).vertex (Fin.last
        (HierarchyFullTailPrefix C m).length)), alpha ∈ MissingColors G P.coloring (T.vertex
        (Fin.last T.length)) → alpha ∉ HierarchyStoredColorsAt P.counterexample.hierarchy
        (Fin.last P.counterexample.hierarchy.dividerCount) → m + (1 : ℕ) ∈
        HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hsituation hvertexMissing i componentData
      trans common A starEq hAT hlen B hBT fullB elementary vertexMem firstAt stageSwitch
      gammaTransport gammaUnused outsideA notRaw tailException consecutive gammaChoice m hmLower
      hmUpper P alpha ha haLast hAlphaStored
  exact @helper_advance_1736 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
      (@hsituation) (@hvertexMissing) (@i) (@componentData) (@trans) (@common) (@starEq)
      (@hAT) (@hlen) (@hBT) (@fullB) (@elementary) (@vertexMem) (@firstAt) (@stageSwitch)
      (@gammaTransport) (@gammaUnused) (@outsideA) (@notRaw) (@tailException) (@consecutive)
      (@gammaChoice) (@m) (@hmLower) (@hmUpper) (@P) (@alpha) (@ha) (@haLast) (@hAlphaStored)

private theorem helper_advance_2571.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (_ :
        HierarchyPathNumber C.hierarchy = (1 : ℕ)) (_ :
    ∀ (mu : PartialEdgeColoring E k), IsProperEdgeColoring G mu → IsOneEdgeUncolored mu e0 →
    ∀ (v : V), (MissingColors G mu v).Nonempty) (_ : ℕ) (_ :
    ∀ (psi : PartialEdgeColoring E k) (a b : Fin k) (_ : a ≠ b) (_ : IsProperEdgeColoring G psi)
        (B : Finset V) (_ : ColoredVertexSetElementary G psi B) (u v w : V) (_ : u ∈ B) (_ : v ∈
        B) (_ : u ≠ v) (_ : w ≠ u) (_ : w ≠ v) (_ : a ∈ MissingColors G psi u) (_ : b ∈
        MissingColors G psi v) (_ : a ∈ MissingColors G psi w ∨ b ∈ MissingColors G psi w) (_ :
        TwoColorComponent G psi a b (Sum.inl u) = TwoColorComponent G psi a b (Sum.inl v)),
        Disjoint (TwoColorComponent G psi a b (Sum.inl w)) (TwoColorComponent G psi a b (Sum.inl
        u)) ∧ TwoColorPathComponent G psi a b (Sum.inl w) ∧
    ∀ x ∈ B, MissingColors G (TwoColorComponentSwap G psi a b (Sum.inl w)) x = MissingColors G psi
        x) (_ :
    ∀ {X Y Z : TreeSequence G e0} (_ : TreeSequenceInitialSegment X Y) (_ :
        TreeSequenceInitialSegment Y Z), TreeSequenceInitialSegment X Z) (_ :
    ∀ {X Y Z : TreeSequence G e0} (_ : TreeSequenceInitialSegment X Z) (_ :
        TreeSequenceInitialSegment Y Z) (_ : X.length ≤ Y.length), TreeSequenceInitialSegment X
        Y),
    let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount);
    ∀ (_ :
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount) = A) (_ :
    have A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount); TreeSequenceInitialSegment A T) (hlen : (4 : ℕ) ≤ T.length),
    let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ)) (
    by
          omega
    ) (
    by
          omega
    );
    ∀ (_ : TreeSequenceInitialSegment B T) (_ :
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyFullTailPrefix R.counterexample (HierarchyFullTailLength R.counterexample - (1 :
        ℕ)) = B) (_ :
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        ColoredVertexSetElementary G R.coloring (TreeSequenceVertexSet B)) (_ :
    ∀ (U : TreeSequence G e0) (j : Fin (U.length + (1 : ℕ))), U.vertex j ∈ TreeSequenceVertexSet
        U) (_ :
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (c : Fin k) (j :
        Fin (B.length + (1 : ℕ))) (_ : c ∈ MissingColors G R.coloring (B.vertex j)),
        (↑(HierarchyFirstMissingPosition R.coloring T c) : ℕ) = (↑j : ℕ)) (_ :
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (X : TreeSequence G
        e0) (_ : TreeSequenceInitialSegment A X) (_ : A.length < X.length) (_ :
        TreeSequenceInitialSegment X B) (a b eta : Fin k) (_ : eta ∈ HierarchyStoredColorsAt
        R.counterexample.hierarchy (Fin.last R.counterexample.hierarchy.dividerCount)) (_ : a ∈
        R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta) (_ :
        (↑(HierarchyFirstMissingPosition R.coloring T eta) : ℕ) ≤ X.length) (jb : Fin (B.length +
        (1 : ℕ))) (_ : A.length < (↑jb : ℕ)) (_ : (↑jb : ℕ) ≤ X.length) (_ : b ∈ MissingColors G
        R.coloring (B.vertex jb)) (_ : a ∈ MissingColors G R.coloring (T.vertex (Fin.last
        T.length)) ∨ b ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length))) (_ :
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → R.coloring (T.edge t) ≠ some
        a) (_ :
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → R.coloring (T.edge t) = some
        b → TreeIncidentEdge (R.corresponding.replacementETT.series.data.tree (Fin.last
        R.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧ b ∈ TashkinovStoredColors
        R.corresponding.replacementETT.series.data (Fin.last
        R.corresponding.replacementETT.rounds)),
    ∃ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), (
    ∀ v ∈ TreeSequenceVertexSet B, MissingColors G S.coloring v = MissingColors G R.coloring v) ∧
        (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → S.coloring (T.edge t) =
        R.coloring (T.edge t)) ∧ (a ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)) →
        b ∈ MissingColors G S.coloring (T.vertex (Fin.last T.length))) ∧ (b ∈ MissingColors G
        R.coloring (T.vertex (Fin.last T.length)) → a ∈ MissingColors G S.coloring (T.vertex
        (Fin.last T.length)))) (_ :
    ∀ (R S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (eta : Fin k) (_
        : eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount)), eta ∈ HierarchyStoredColorsAt
        S.counterexample.hierarchy (Fin.last S.counterexample.hierarchy.dividerCount) ∧
        R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta =
        S.counterexample.good.gamma (Fin.last S.counterexample.hierarchy.dividerCount) eta) (_ :
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (eta a : Fin k) (_
        : eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount)) (_ : a ∈ R.counterexample.good.gamma (Fin.last
        R.counterexample.hierarchy.dividerCount) eta) (t : Fin T.length) (_ : A.length ≤ (↑t : ℕ))
        (_ : (↑t : ℕ) < (↑(HierarchyFirstMissingPosition R.coloring T eta) : ℕ)), R.coloring
        (T.edge t) ≠ some a) (_ :
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (c : Fin k) (j :
        Fin (B.length + (1 : ℕ))) (_ : A.length < (↑j : ℕ)) (_ : c ∈ MissingColors G R.coloring
        (B.vertex j)), c ∉ TreeMissingColors R.coloring A) (_ :
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (c : Fin k) (_ : c
        ∉ TreeMissingColors R.coloring A) (_ : c ∉ HierarchyStoredColorsAt
        R.counterexample.hierarchy (Fin.last R.counterexample.hierarchy.dividerCount)), c ∉
        TashkinovStoredColors R.corresponding.replacementETT.series.data (Fin.last
        R.corresponding.replacementETT.rounds)) (_ :
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (j : ℕ) (_ : (1 :
        ℕ) ≤ j) (_ : j < T.length - A.length) (c : Fin k) (_ : c ∈ MissingColors G R.coloring
        ((HierarchyFullTailPrefix C j).vertex (Fin.last (HierarchyFullTailPrefix C j).length))) (t
        : Fin T.length) (_ : A.length ≤ (↑t : ℕ)) (_ : (↑t : ℕ) < A.length + j) (_ : R.coloring
        (T.edge t) = some c), TreeIncidentEdge (R.corresponding.replacementETT.series.data.tree
        (Fin.last R.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧ c ∈
        TashkinovStoredColors R.corresponding.replacementETT.series.data (Fin.last
        R.corresponding.replacementETT.rounds)) (_ :
    ∀ (t : Fin T.length) (_ : A.length + HierarchyPathNumber C.hierarchy ≤ (↑t : ℕ)), G.ends
        (T.edge t) = s(T.vertex t.castSucc, T.vertex t.succ)) (_ :
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (eta : Fin k) (_ :
        eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount)) (f : E),
    ∃ a ∈ R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta,
        R.coloring f ≠ some a) (m : ℕ) (_ : HierarchyPathNumber C.hierarchy ≤ m) (_ : m <
        HierarchyFullTailLength C - (1 : ℕ)) (P : HierarchyReplacementPresentation G k e0 input T
        phi ett base C ctx) (alpha : Fin k) (_ : alpha ∈ MissingColors G P.coloring
        ((HierarchyFullTailPrefix C m).vertex (Fin.last (HierarchyFullTailPrefix C m).length))) (_
        : alpha ∈ MissingColors G P.coloring (T.vertex (Fin.last T.length))) (_ : alpha ∉
        HierarchyStoredColorsAt P.counterexample.hierarchy (Fin.last
        P.counterexample.hierarchy.dividerCount)), m + (1 : ℕ) ∈
        HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hsituation hvertexMissing i componentData
      trans common A starEq hAT hlen B hBT fullB elementary vertexMem firstAt stageSwitch
      gammaTransport gammaUnused outsideA notRaw tailException consecutive gammaChoice m hmLower
      hmUpper P alpha ha haLast hAlphaStored
  exact @helper_advance_2294 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
      (@hsituation) (@hvertexMissing) (@i) (@componentData) (@trans) (@common) (@starEq)
      (@hAT) (@hlen) (@hBT) (@fullB) (@elementary) (@vertexMem) (@firstAt) (@stageSwitch)
      (@gammaTransport) (@gammaUnused) (@outsideA) (@notRaw) (@tailException) (@consecutive)
      (@gammaChoice) (@m) (@hmLower) (@hmUpper) (@P) (@alpha) (@ha) (@haLast) (@hAlphaStored)

theorem HierarchySituationOneAdvanceOutsideStored {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (hsituation : HierarchyPathNumber C.hierarchy = 1)
    (hvertexMissing : ∀ (mu : PartialEdgeColoring E k),
      IsProperEdgeColoring G mu → IsOneEdgeUncolored mu e0 →
        ∀ v : V, (MissingColors G mu v).Nonempty)
    (i : ℕ) (hiLower : 1 ≤ i)
    (hiUpper : i < HierarchyFullTailLength C - 1)
    (P : HierarchyReplacementPresentation
      G k e0 input T phi ett base C ctx)
    (alpha : Fin k)
    (hcommon :
      alpha ∈ MissingColors G P.coloring
          ((HierarchyFullTailPrefix C i).vertex
            (Fin.last (HierarchyFullTailPrefix C i).length)) ∧
        alpha ∈ MissingColors G P.coloring
          (T.vertex (Fin.last T.length)))
    (houtside :
      let H := P.counterexample.hierarchy
      alpha ∉ HierarchyStoredColorsAt H (Fin.last H.dividerCount)) :
    i + 1 ∈ HierarchyEligibleCommonMissingIndices
      G k e0 input T phi ett base C ctx := by
  classical
  have hpathUpper :
      HierarchyPathNumber C.hierarchy < HierarchyFullTailLength C := by
    rw [hsituation]
    omega
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
  classical
  open scoped Sym2 in
    have trans {X Y Z : TreeSequence G e0}
        (hXY : TreeSequenceInitialSegment X Y)
        (hYZ : TreeSequenceInitialSegment Y Z) :
        TreeSequenceInitialSegment X Z := by
      exact helper_trans_1517 (@G) (@e0) (@i) (@hXY) (@hYZ)
    have common {X Y Z : TreeSequence G e0}
        (hXZ : TreeSequenceInitialSegment X Z)
        (hYZ : TreeSequenceInitialSegment Y Z) (hXY : X.length ≤ Y.length) :
        TreeSequenceInitialSegment X Y := by
      exact @helper_common_1527 (@V) (@E) (@G) (@e0) (@i) (@trans) (@X) (@Y) (@Z) (@hXZ) (@hYZ)
          (@hXY)
    have sameLast :
    ∀ {a b : ℕ} (s : Fin (a + 2) → TreeSequence G e0) (t : Fin (b + 2) → TreeSequence G e0) (u v :
        TreeSequence G e0), a = b → HEq s t → u = v → Fin.cases (motive := fun _ => TreeSequence G
        e0) u (fun i : Fin a => s i.castSucc.succ) (Fin.last a) = Fin.cases (motive := fun _ =>
        TreeSequence G e0) v (fun i : Fin b => t i.castSucc.succ) (Fin.last b) := by
      exact @SharedFacts.OutsideAdvancement.sameLast (@V) (@E) (@G) (@e0)
    let A := HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)
    have starEq (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) :
        HierarchyStarredStage R.counterexample.hierarchy
          (Fin.last R.counterexample.hierarchy.dividerCount) = A :=
      (sameLast _ _ _ _ R.sameGood.1.2.1 R.sameGood.1.2.2.1 R.sameGood.1.1).symm
    have hAT :=
      helper_hAT_1558 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@i)
    have htail : 3 ≤ T.length - A.length := by
      have hu := hiUpper
      change i < (T.length - A.length) - 1 at hu
      omega
    have hlen : 4 ≤ T.length := by have := A.positive; omega
    let B := TreeSequencePrefix T (T.length - 1) (by omega) (by omega)
    have hBT : TreeSequenceInitialSegment B T := ⟨by dsimp [B, TreeSequencePrefix]; omega,
      fun _ => rfl, fun _ => rfl⟩
    have hAB : TreeSequenceInitialSegment A B :=
      common hAT hBT (by dsimp [B, TreeSequencePrefix]; omega)
    have fullEq (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
        (j : ℕ) : HierarchyFullTailPrefix R.counterexample j = HierarchyFullTailPrefix C j := by
      unfold HierarchyFullTailPrefix
      dsimp only
      simp only [starEq R]
      rfl
    have fullB (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) :
        HierarchyFullTailPrefix R.counterexample
          (HierarchyFullTailLength R.counterexample - 1) = B := by
      exact helper_fullB_1581 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
          (@i) (@starEq) (@htail)
          (@hlen) (@R)
    have elementary (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) :
        ColoredVertexSetElementary G R.coloring (TreeSequenceVertexSet B) := by
      exact helper_elementary_1593 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
          (@ctx) (@i) (@hlen) (@fullB) (@R)
    have vertexMem (U : TreeSequence G e0) (j : Fin (U.length + 1)) :
        U.vertex j ∈ TreeSequenceVertexSet U := by
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨j, rfl⟩
    have firstLe (psi : PartialEdgeColoring E k) (c : Fin k)
        (j : Fin (T.length + 1)) (hj : c ∈ MissingColors G psi (T.vertex j)) :
        HierarchyFirstMissingPosition psi T c ≤ j := by
      exact SharedFacts.OutsideAdvancement.firstMissingPositionUpperBound (@G) (@k) (@e0) (@T)
          (@psi) (@c) (@j) (@hj)
    have firstMem (psi : PartialEdgeColoring E k) (c : Fin k)
        (hlt : (HierarchyFirstMissingPosition psi T c).val < T.length) :
        c ∈ MissingColors G psi (T.vertex (HierarchyFirstMissingPosition psi T c)) := by
      exact TreeSequenceFirstMissingPositionMem hlt
    have firstAt (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
        (c : Fin k) (j : Fin (B.length + 1))
        (hc : c ∈ MissingColors G R.coloring (B.vertex j)) :
        (HierarchyFirstMissingPosition R.coloring T c).val = j.val := by
      exact TreeSequenceFirstMissingPositionEqCast hBT (elementary R) hc
    have stageSwitch := P2963_T1_TerminalKempeStageSwitch G k e0 input T phi ett base C ctx
      A B (by omega) rfl rfl
    have lastData (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) :
        HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount) =
          HierarchyStoredColorsAt R.counterexample.hierarchy
            (Fin.last R.counterexample.hierarchy.dividerCount) ∧
        ∀ eta ∈ HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount),
          C.good.gamma (Fin.last C.hierarchy.dividerCount) eta =
            R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta := by
      exact SharedFacts.OutsideAdvancement.lastData (@G) (@k) (@e0) (@input) (@T) (@phi)
          (@ett) (@base) (@C) (@ctx)
          (@R)
    have gammaTransport
        (R S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
        (eta : Fin k)
        (heta : eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy
          (Fin.last R.counterexample.hierarchy.dividerCount)) :
        eta ∈ HierarchyStoredColorsAt S.counterexample.hierarchy
          (Fin.last S.counterexample.hierarchy.dividerCount) ∧
        R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta =
          S.counterexample.good.gamma (Fin.last S.counterexample.hierarchy.dividerCount) eta := by
      exact @SharedFacts.OutsideAdvancement.gammaTransport (@V) (@E) inferInstance
          inferInstance inferInstance
          inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@trans)
          (@lastData) (@R) (@S) (@eta) (@heta)
    have gammaUnused (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
        (eta a : Fin k)
        (heta : eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy
          (Fin.last R.counterexample.hierarchy.dividerCount))
        (ha : a ∈ R.counterexample.good.gamma
          (Fin.last R.counterexample.hierarchy.dividerCount) eta)
        (t : Fin T.length) (hlo : A.length ≤ t.val)
        (hhi : t.val < (HierarchyFirstMissingPosition R.coloring T eta).val) :
        R.coloring (T.edge t) ≠ some a := by
      exact SharedFacts.OutsideAdvancement.gammaUnused (@G) (@k) (@e0) (@input) (@T) (@phi)
          (@ett) (@base) (@C)
          (@ctx) (@starEq)
          (@R) (@eta) (@a) (@heta) (@ha) (@t) (@hlo) (@hhi)
    have outsideA (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
        (c : Fin k) (j : Fin (B.length + 1)) (hj : A.length < j.val)
        (hc : c ∈ MissingColors G R.coloring (B.vertex j)) :
        c ∉ TreeMissingColors R.coloring A := by
      exact helper_outsideA_1255 G k e0 input T phi ett base C ctx i trans hAT hlen hBT hAB
          elementary vertexMem R c j hj hc
    have notRaw (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
        (c : Fin k) (hcA : c ∉ TreeMissingColors R.coloring A)
        (hcD : c ∉ HierarchyStoredColorsAt R.counterexample.hierarchy
          (Fin.last R.counterexample.hierarchy.dividerCount)) :
        c ∉ TashkinovStoredColors R.corresponding.replacementETT.series.data
          (Fin.last R.corresponding.replacementETT.rounds) := by
      exact SharedFacts.OutsideAdvancement.notRaw (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett)
          (@base) (@C) (@ctx)
          (@starEq) (@R) (@c)
          (@hcA) (@hcD)
    have tailException (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
        (j : ℕ) (hj : 1 ≤ j) (hjlt : j < T.length - A.length)
        (c : Fin k)
        (hc : c ∈ MissingColors G R.coloring
          ((HierarchyFullTailPrefix C j).vertex (Fin.last (HierarchyFullTailPrefix C j).length)))
        (t : Fin T.length) (hlo : A.length ≤ t.val) (hhi : t.val < A.length + j)
        (hcol : R.coloring (T.edge t) = some c) :
        TreeIncidentEdge (R.corresponding.replacementETT.series.data.tree
          (Fin.last R.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧
          c ∈ TashkinovStoredColors R.corresponding.replacementETT.series.data
            (Fin.last R.corresponding.replacementETT.rounds) := by
      exact SharedFacts.InsideAdvancement.tailException G k e0 input T phi ett base C ctx i
          trans starEq hAT hlen
          hBT fullEq fullB elementary
          vertexMem R j hj hjlt c hc t hlo hhi hcol
    have consecutive (t : Fin T.length)
        (ht : A.length + HierarchyPathNumber C.hierarchy ≤ t.val) :
        G.ends (T.edge t) = s(T.vertex t.castSucc, T.vertex t.succ) := by
      exact SharedFacts.InsideAdvancement.consecutive G k e0 input T phi ett base C i
          hpathUpper t ht
    have gammaChoice (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
        (eta : Fin k)
        (heta : eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy
          (Fin.last R.counterexample.hierarchy.dividerCount)) (f : E) :
        ∃ a ∈ R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta,
          R.coloring f ≠ some a := by
      exact @SharedFacts.OutsideAdvancement.gammaChoice (@V) (@E) inferInstance inferInstance
          inferInstance
          inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@trans)
          (@R) (@eta) (@heta) (@f)
    have advance (m : ℕ) (hmLower : HierarchyPathNumber C.hierarchy ≤ m)
        (hmUpper : m < HierarchyFullTailLength C - 1)
        (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
        (alpha : Fin k)
        (ha : alpha ∈ MissingColors G P.coloring
          ((HierarchyFullTailPrefix C m).vertex (Fin.last (HierarchyFullTailPrefix C m).length)))
        (haLast : alpha ∈ MissingColors G P.coloring (T.vertex (Fin.last T.length)))
        (hAlphaStored : alpha ∉ HierarchyStoredColorsAt P.counterexample.hierarchy
          (Fin.last P.counterexample.hierarchy.dividerCount)) :
        m + 1 ∈ HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx := by
      exact @helper_advance_2571 (@V) (@E) inferInstance inferInstance inferInstance
          inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
          (@hsituation) (@hvertexMissing) (@i) (@componentData) (@trans) (@common) (@starEq)
          (@hAT) (@hlen) (@hBT) (@fullB) (@elementary) (@vertexMem) (@firstAt) (@stageSwitch)
          (@gammaTransport) (@gammaUnused) (@outsideA) (@notRaw) (@tailException) (@consecutive)
          (@gammaChoice) (@m) (@hmLower) (@hmUpper) (@P) (@alpha) (@ha) (@haLast) (@hAlphaStored)
    exact advance i (by simpa only [hsituation] using hiLower) hiUpper
      P alpha hcommon.1 hcommon.2 houtside

end GoldbergSeymour

end
