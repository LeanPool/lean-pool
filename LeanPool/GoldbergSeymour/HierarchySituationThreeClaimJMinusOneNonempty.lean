/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module


public import LeanPool.GoldbergSeymour.SharedFacts.ReplacementPrefixes




public import LeanPool.GoldbergSeymour.HierarchyEligibleCommonMissingIndices
public import LeanPool.GoldbergSeymour.HierarchySituationThreeEligibleIndexBound
public import LeanPool.GoldbergSeymour.NineN

/-!
# Hierarchy Situation Three Claim JMinus One Nonempty

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private noncomputable abbrev helperCS778.{u_1, u_2} :
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
                                      (R :
                                          HierarchyReplacementPresentation G k e0 input T phi ett
                                            base C ctx) →
                                        (a b : Fin k) →
                                          let sigma : PartialEdgeColoring E k :=
                                            TwoColorComponentSwap G R.coloring a b
                                              (Sum.inl (T.vertex (Fin.last T.length)));
                                          (corr :
                                              CorrespondingExtendedTashkinovTree G k e0
                                                R.corresponding.replacementETT sigma T) →
                                            MaximumProperty corr.replacementETT →
                                              (bs : HierarchyBase corr.replacementETT sigma) →
                                                (K : TashkinovHierarchy corr.replacementETT bs) →
                                                  GoodHierarchy K →
                                                    ¬ColoredVertexSetElementary G sigma
                                                          (TreeSequenceVertexSet T) →
                                                      HierarchyCounterexample bs := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx R a b sigma corr hmaximum bs K goodK
      hnotElementary
  exact {
    positive := by rw [corr.rungAgreement]; exact R.counterexample.positive
    hierarchy := K
    good := goodK
    maximum := hmaximum
    notElementary := hnotElementary }

private noncomputable abbrev helperCS1504.{u_1, u_2} :
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
                                          let sigma : PartialEdgeColoring E k :=
                                            TwoColorComponentSwap G P.coloring beta alpha
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
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta sigma corr hmaximum bs K goodK
      hnot
  exact {
    positive := by rw [corr.rungAgreement]; exact P.counterexample.positive
    hierarchy := K
    good := goodK
    maximum := hmaximum
    notElementary := hnot }

private abbrev helperBranch1365Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (hnonempty :
        (HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx).Nonempty) (j :
        ℕ) (_ : (2 : ℕ) ≤ j) (hpathUpper : j < HierarchyFullTailLength C), (
    ∀ {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Y → TreeSequenceInitialSegment Y Z
        → TreeSequenceInitialSegment X Z) →
    let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount);
    ∀ (htail : (3 : ℕ) ≤ T.length - A.length) (hlen : (4 : ℕ) ≤ T.length),
    let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ)) (
    by
        have := GoldbergSeymour.TreeSequence.positive T
        omega
    ) (
    by
        have := GoldbergSeymour.TreeSequence.positive T
        omega
    ); TreeSequenceInitialSegment B T → (
    ∀ (U : TreeSequence G e0) (j : Fin (U.length + (1 : ℕ))), U.vertex j ∈ TreeSequenceVertexSet
        U) → (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (c : Fin k) (j :
        Fin (B.length + (1 : ℕ))), c ∈ MissingColors G R.coloring (B.vertex j) →
        (↑(HierarchyFirstMissingPosition R.coloring T c) : ℕ) = (↑j : ℕ)) → (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (X : TreeSequence G
        e0), TreeSequenceInitialSegment A X → A.length < X.length → TreeSequenceInitialSegment X B
        →
    ∀ (a b : Fin k), a ≠ b → a ∈ HierarchyStageMissingColors R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount) →
    ∀ (jb : Fin (B.length + (1 : ℕ))), (↑jb : ℕ) ≤ X.length → b ∈ MissingColors G R.coloring
        (B.vertex jb) → a ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)) ∨ b ∈
        MissingColors G R.coloring (T.vertex (Fin.last T.length)) → (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → R.coloring (T.edge t) ≠ some
        a) → (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → R.coloring (T.edge t) = some
        b → TreeIncidentEdge (R.corresponding.replacementETT.series.data.tree (Fin.last
        R.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧ b ∈ TashkinovStoredColors
        R.corresponding.replacementETT.series.data (Fin.last
        R.corresponding.replacementETT.rounds)) → (
    ∀ eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount), a ∈ R.counterexample.good.gamma (Fin.last
        R.counterexample.hierarchy.dividerCount) eta ∨ b ∈ R.counterexample.good.gamma (Fin.last
        R.counterexample.hierarchy.dividerCount) eta → (↑(HierarchyFirstMissingPosition R.coloring
        T eta) : ℕ) ≤ X.length) →
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
        R.coloring T eta) : ℕ) → R.coloring (T.edge t) ≠ some a) →
    let Extra : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx → Finset (Fin
        k) := fun (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) ↦
        (TreeSequenceVertexSet R.replacementBase.core \ TreeSequenceVertexSet
        (R.corresponding.replacementETT.series.data.tree (Fin.last
        R.corresponding.replacementETT.rounds).castSucc)).biUnion fun (v : V) ↦ MissingColors G
        R.coloring v;
    let Gamma : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx → Finset (Fin
        k) := fun (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) ↦
        (HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount)).biUnion (R.counterexample.good.gamma (Fin.last
        R.counterexample.hierarchy.dividerCount)); (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), Gamma R ⊆
        TreeMissingColors R.coloring A) →
    let Y : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ)); Y.length = A.length + (j
        - (2 : ℕ)) →
    ∀ (hYB : TreeSequenceInitialSegment Y B),
    let I : Finset ℕ := HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx;
    let i : ℕ := I.max' hnonempty;
    ∀ (hiUpper : i < j) (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∀ alpha ∈ MissingColors G P.coloring ((HierarchyFullTailPrefix C i).vertex (Fin.last
        (HierarchyFullTailPrefix C i).length)), alpha ∈ MissingColors G P.coloring (T.vertex
        (Fin.last T.length)) →
    ∀ (hSlen : (HierarchyFullTailPrefix C i).length = A.length + i),
    let ja : Fin (B.length + (1 : ℕ)) := (⟨A.length + i,
    have hb : B.length = T.length - (1 : ℕ) := rfl; id (fun (hpathUpper : j < T.length - A.length)
        ↦ Decidable.byContradiction fun (a : ¬A.length + i < B.length + (1 : ℕ)) ↦
    by
                        omega
    ) hpathUpper⟩ : Fin (B.length + (1 : ℕ))); alpha ∈ MissingColors G P.coloring (B.vertex ja) →
        alpha ∉ TreeMissingColors P.coloring A → alpha ∉ Gamma P ∪ Extra P → i = j - (1 : ℕ) →
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ)); X.length = A.length + (j
        - (1 : ℕ)) → TreeSequenceInitialSegment X B → TreeSequenceInitialSegment A X → A.length <
        X.length → X.length = Y.length + (1 : ℕ) → (↑ja : ℕ) = X.length →
    let D : Finset (Fin k) := HierarchyStoredColorsAt P.counterexample.hierarchy (Fin.last
        P.counterexample.hierarchy.dividerCount);
    ∀ (beta : Fin k) (yb : Fin (Y.length + (1 : ℕ))),
    let jb : Fin (B.length + (1 : ℕ)) := Fin.castLE (Nat.succ_le_succ hYB.1) yb; beta ∈
        MissingColors G P.coloring (B.vertex jb) → (↑jb : ℕ) ≤ Y.length →
        (↑(HierarchyFirstMissingPosition P.coloring T alpha) : ℕ) = X.length → alpha ≠ beta → (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → P.coloring (T.edge t) ≠ some
        beta) → (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → P.coloring (T.edge t) = some
        alpha → TreeIncidentEdge (P.corresponding.replacementETT.series.data.tree (Fin.last
        P.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧ alpha ∈
        TashkinovStoredColors P.corresponding.replacementETT.series.data (Fin.last
        P.corresponding.replacementETT.rounds)) → (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), (
    ∀ v ∈ TreeSequenceVertexSet B, MissingColors G R.coloring v = MissingColors G P.coloring v) →
    ∀ eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount), beta ∈ R.counterexample.good.gamma (Fin.last
        R.counterexample.hierarchy.dividerCount) eta → (↑(HierarchyFirstMissingPosition R.coloring
        T eta) : ℕ) ≤ Y.length) → (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), (
    ∀ v ∈ TreeSequenceVertexSet B, MissingColors G R.coloring v = MissingColors G P.coloring v) →
        beta ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)) → beta ∈
        TreeMissingColors R.coloring Y ∧ (beta ∉ Gamma R ∪ Extra R ∨
    ∃ eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount), beta ∈ R.counterexample.good.gamma (Fin.last
        R.counterexample.hierarchy.dividerCount) eta ∧ (↑(HierarchyFirstMissingPosition R.coloring
        T eta) : ℕ) ≤ Y.length)) → alpha ∈ D →
    ∃ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha : Fin k),
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
        P.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let n : Fin (P.corresponding.replacementETT.rounds + (1 : ℕ)) := Fin.last
        P.corresponding.replacementETT.rounds;
    let Tn : TreeSequence G e0 := P.corresponding.replacementETT.series.data.tree n.castSucc;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ));
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let Gamma : Finset (Fin k) := D.biUnion (P.counterexample.good.gamma q);
    let baseExtraMissing : Finset (Fin k) := (TreeSequenceVertexSet P.replacementBase.core \
        TreeSequenceVertexSet Tn).biUnion fun (v : V) ↦ MissingColors G P.coloring v; alpha ∈
        MissingColors G P.coloring (T.vertex (Fin.last T.length)) ∧ alpha ∈ TreeMissingColors
        P.coloring B ∧ (alpha ∉ Gamma ∪ baseExtraMissing ∨
    ∃ eta ∈ D, alpha ∈ P.counterexample.good.gamma q eta ∧ (↑(HierarchyFirstMissingPosition
        P.coloring T eta) : ℕ) ≤ B.length)

private abbrev helperBranch1435Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (hnonempty :
        (HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx).Nonempty) (j :
        ℕ) (_ : (2 : ℕ) ≤ j) (hpathUpper : j < HierarchyFullTailLength C), (
    ∀ {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Y → TreeSequenceInitialSegment Y Z
        → TreeSequenceInitialSegment X Z) →
    let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount);
    ∀ (htail : (3 : ℕ) ≤ T.length - A.length) (hlen : (4 : ℕ) ≤ T.length),
    let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ)) (
    by
        have := GoldbergSeymour.TreeSequence.positive T
        omega
    ) (
    by
        have := GoldbergSeymour.TreeSequence.positive T
        omega
    ); TreeSequenceInitialSegment B T → (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (X : TreeSequence G
        e0), TreeSequenceInitialSegment A X → A.length < X.length → TreeSequenceInitialSegment X B
        →
    ∀ (a b : Fin k), a ≠ b → a ∈ HierarchyStageMissingColors R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount) →
    ∀ (jb : Fin (B.length + (1 : ℕ))), (↑jb : ℕ) ≤ X.length → b ∈ MissingColors G R.coloring
        (B.vertex jb) → a ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)) ∨ b ∈
        MissingColors G R.coloring (T.vertex (Fin.last T.length)) → (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → R.coloring (T.edge t) ≠ some
        a) → (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → R.coloring (T.edge t) = some
        b → TreeIncidentEdge (R.corresponding.replacementETT.series.data.tree (Fin.last
        R.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧ b ∈ TashkinovStoredColors
        R.corresponding.replacementETT.series.data (Fin.last
        R.corresponding.replacementETT.rounds)) → (
    ∀ eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount), a ∈ R.counterexample.good.gamma (Fin.last
        R.counterexample.hierarchy.dividerCount) eta ∨ b ∈ R.counterexample.good.gamma (Fin.last
        R.counterexample.hierarchy.dividerCount) eta → (↑(HierarchyFirstMissingPosition R.coloring
        T eta) : ℕ) ≤ X.length) →
    ∃ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), (
    ∀ v ∈ TreeSequenceVertexSet B, MissingColors G S.coloring v = MissingColors G R.coloring v) ∧
        (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → S.coloring (T.edge t) =
        R.coloring (T.edge t)) ∧ (a ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)) →
        b ∈ MissingColors G S.coloring (T.vertex (Fin.last T.length))) ∧ (b ∈ MissingColors G
        R.coloring (T.vertex (Fin.last T.length)) → a ∈ MissingColors G S.coloring (T.vertex
        (Fin.last T.length)))) →
    let Extra : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx → Finset (Fin
        k) := fun (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) ↦
        (TreeSequenceVertexSet R.replacementBase.core \ TreeSequenceVertexSet
        (R.corresponding.replacementETT.series.data.tree (Fin.last
        R.corresponding.replacementETT.rounds).castSucc)).biUnion fun (v : V) ↦ MissingColors G
        R.coloring v;
    let Gamma : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx → Finset (Fin
        k) := fun (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) ↦
        (HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount)).biUnion (R.counterexample.good.gamma (Fin.last
        R.counterexample.hierarchy.dividerCount)); (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), Gamma R ⊆
        TreeMissingColors R.coloring A) →
    let Y : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ)); Y.length = A.length + (j
        - (2 : ℕ)) → TreeSequenceInitialSegment Y B →
    let I : Finset ℕ := HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx;
    let i : ℕ := I.max' hnonempty;
    ∀ (hiUpper : i < j) (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∀ alpha ∈ MissingColors G P.coloring (T.vertex (Fin.last T.length)),
    ∀ (hSlen : (HierarchyFullTailPrefix C i).length = A.length + i),
    let ja : Fin (B.length + (1 : ℕ)) := (⟨A.length + i,
    have hb : B.length = T.length - (1 : ℕ) := rfl; id (fun (hpathUpper : j < T.length - A.length)
        ↦ Decidable.byContradiction fun (a : ¬A.length + i < B.length + (1 : ℕ)) ↦
    by omega
    ) hpathUpper⟩ : Fin (B.length + (1 : ℕ))); alpha ∈ MissingColors G P.coloring (B.vertex ja) →
        alpha ∉ TreeMissingColors P.coloring A → i = j - (1 : ℕ) →
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ)); X.length = A.length + (j
        - (1 : ℕ)) → TreeSequenceInitialSegment X B → TreeSequenceInitialSegment A X → A.length <
        X.length → X.length = Y.length + (1 : ℕ) → (↑ja : ℕ) = X.length →
    ∀ (beta : Fin k) (_ : Fin (Y.length + (1 : ℕ))), alpha ≠ beta → (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → P.coloring (T.edge t) ≠ some
        beta) → (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → P.coloring (T.edge t) = some
        alpha → TreeIncidentEdge (P.corresponding.replacementETT.series.data.tree (Fin.last
        P.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧ alpha ∈
        TashkinovStoredColors P.corresponding.replacementETT.series.data (Fin.last
        P.corresponding.replacementETT.rounds)) → (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), (
    ∀ v ∈ TreeSequenceVertexSet B, MissingColors G R.coloring v = MissingColors G P.coloring v) →
    ∀ eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount), beta ∈ R.counterexample.good.gamma (Fin.last
        R.counterexample.hierarchy.dividerCount) eta → (↑(HierarchyFirstMissingPosition R.coloring
        T eta) : ℕ) ≤ Y.length) → (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), (
    ∀ v ∈ TreeSequenceVertexSet B, MissingColors G R.coloring v = MissingColors G P.coloring v) →
        beta ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)) → beta ∈
        TreeMissingColors R.coloring Y ∧ (beta ∉ Gamma R ∪ Extra R ∨
    ∃ eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount), beta ∈ R.counterexample.good.gamma (Fin.last
        R.counterexample.hierarchy.dividerCount) eta ∧ (↑(HierarchyFirstMissingPosition R.coloring
        T eta) : ℕ) ≤ Y.length)) → beta ∈ HierarchyStageMissingColors P.counterexample.hierarchy
        (Fin.last P.counterexample.hierarchy.dividerCount) →
    ∃ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha : Fin k),
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
        P.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let n : Fin (P.corresponding.replacementETT.rounds + (1 : ℕ)) := Fin.last
        P.corresponding.replacementETT.rounds;
    let Tn : TreeSequence G e0 := P.corresponding.replacementETT.series.data.tree n.castSucc;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ));
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let Gamma : Finset (Fin k) := D.biUnion (P.counterexample.good.gamma q);
    let baseExtraMissing : Finset (Fin k) := (TreeSequenceVertexSet P.replacementBase.core \
        TreeSequenceVertexSet Tn).biUnion fun (v : V) ↦ MissingColors G P.coloring v; alpha ∈
        MissingColors G P.coloring (T.vertex (Fin.last T.length)) ∧ alpha ∈ TreeMissingColors
        P.coloring B ∧ (alpha ∉ Gamma ∪ baseExtraMissing ∨
    ∃ eta ∈ D, alpha ∈ P.counterexample.good.gamma q eta ∧ (↑(HierarchyFirstMissingPosition
        P.coloring T eta) : ℕ) ≤ B.length)

private abbrev helperContinuation3823Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (hvertexMissing :
    ∀ (mu : PartialEdgeColoring E k), IsProperEdgeColoring G mu → IsOneEdgeUncolored mu e0 →
    ∀ (v : V), (MissingColors G mu v).Nonempty) (hnonempty :
        (HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx).Nonempty) (j :
        ℕ) (hj : HierarchyPathNumber C.hierarchy = j) (hpathLower : (2 : ℕ) ≤ j) (hpathUpper : j <
        HierarchyFullTailLength C) (finiteChoice :
    ∀ (M F D U W N : Finset (Fin k)) (g : Fin k → Finset (Fin k)) (hstep : W ⊆ U ∪ N) (hncard :
        N.card ≤ (1 : ℕ)) (hgM :
    ∀ eta ∈ D, g eta ⊆ M) (hgcard :
    ∀ eta ∈ D, (g eta).card = (2 : ℕ)) (hgdis :
    ∀ eta ∈ D,
    ∀ theta ∈ D, eta ≠ theta → Disjoint (g eta) (g theta)) (hgd : Disjoint (D.biUnion g) D) (hnine
        : (((M \ F) \ U) \ (D.biUnion g ∪ D)).card ≤ (4 : ℕ) →
    ∃ (eta : Fin (7 : ℕ) → Fin k), Function.Injective eta ∧
    ∀ (h : Fin (7 : ℕ)), eta h ∈ D ∧ eta h ∈ M ∧ Disjoint (g (eta h) ∪ ({eta h} : Finset (Fin k)))
        U),
    ∃ beta ∈ M, beta ∉ D ∧ beta ∉ W ∧ (beta ∉ D.biUnion g ∪ F ∨
    ∃ eta ∈ D, beta ∈ g eta ∧ eta ∈ M)) (componentData :
    ∀ (psi : PartialEdgeColoring E k) (a b : Fin k) (hne : a ≠ b) (hproper : IsProperEdgeColoring
        G psi) (B : Finset V) (helem : ColoredVertexSetElementary G psi B) (u v w : V) (hu : u ∈
        B) (hv : v ∈ B) (hwu : w ≠ u) (hwv : w ≠ v) (hau : a ∈ MissingColors G psi u) (hbv : b ∈
        MissingColors G psi v) (hw : a ∈ MissingColors G psi w ∨ b ∈ MissingColors G psi w) (hsame
        : TwoColorComponent G psi a b (Sum.inl u) = TwoColorComponent G psi a b (Sum.inl v)),
        Disjoint (TwoColorComponent G psi a b (Sum.inl w)) (TwoColorComponent G psi a b (Sum.inl
        u)) ∧ TwoColorPathComponent G psi a b (Sum.inl w) ∧
    ∀ x ∈ B, MissingColors G (TwoColorComponentSwap G psi a b (Sum.inl w)) x = MissingColors G psi
        x) (trans :
    ∀ {X Y Z : TreeSequence G e0} (hXY : TreeSequenceInitialSegment X Y) (hYZ :
        TreeSequenceInitialSegment Y Z), TreeSequenceInitialSegment X Z) (common :
    ∀ {X Y Z : TreeSequence G e0} (hXZ : TreeSequenceInitialSegment X Z) (hYZ :
        TreeSequenceInitialSegment Y Z) (hXY : X.length ≤ Y.length), TreeSequenceInitialSegment X
        Y),
    let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount);
    ∀ (starEq :
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount) = A) (hAT : TreeSequenceInitialSegment A T)
        (htail : (3 : ℕ) ≤ T.length - A.length) (hlen : (4 : ℕ) ≤ T.length),
    let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ)) (
    by omega
    ) (
    by omega
    );
    ∀ (hBT : TreeSequenceInitialSegment B T) (hAB : TreeSequenceInitialSegment A B) (fullEq :
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (j : ℕ),
        HierarchyFullTailPrefix R.counterexample j = HierarchyFullTailPrefix C j) (fullB :
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyFullTailPrefix R.counterexample (HierarchyFullTailLength R.counterexample - (1 :
        ℕ)) = B) (elementary :
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        ColoredVertexSetElementary G R.coloring (TreeSequenceVertexSet B)) (vertexMem :
    ∀ (U : TreeSequence G e0) (j : Fin (U.length + (1 : ℕ))), U.vertex j ∈ TreeSequenceVertexSet
        U) (firstLe :
    ∀ (psi : PartialEdgeColoring E k) (c : Fin k) (j : Fin (T.length + (1 : ℕ))) (hj : c ∈
        MissingColors G psi (T.vertex j)), HierarchyFirstMissingPosition psi T c ≤ j) (firstAt :
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (c : Fin k) (j :
        Fin (B.length + (1 : ℕ))) (hc : c ∈ MissingColors G R.coloring (B.vertex j)),
        (↑(HierarchyFirstMissingPosition R.coloring T c) : ℕ) = (↑j : ℕ)) (firstFixed :
    ∀ (psi tau : PartialEdgeColoring E k) (hmissing :
    ∀ v ∈ TreeSequenceVertexSet B, MissingColors G tau v = MissingColors G psi v) (c : Fin k),
        HierarchyFirstMissingPosition tau T c = HierarchyFirstMissingPosition psi T c)
        (stageSwitch :
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (X : TreeSequence G
        e0) (hAX : TreeSequenceInitialSegment A X) (hAXlt : A.length < X.length) (hXB :
        TreeSequenceInitialSegment X B) (a b : Fin k) (hne : a ≠ b) (haStage : a ∈
        HierarchyStageMissingColors R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount)) (jb : Fin (B.length + (1 : ℕ))) (hjbX : (↑jb :
        ℕ) ≤ X.length) (hb : b ∈ MissingColors G R.coloring (B.vertex jb)) (hw : a ∈ MissingColors
        G R.coloring (T.vertex (Fin.last T.length)) ∨ b ∈ MissingColors G R.coloring (T.vertex
        (Fin.last T.length))) (haUnused :
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → R.coloring (T.edge t) ≠ some
        a) (hbException :
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → R.coloring (T.edge t) = some
        b → TreeIncidentEdge (R.corresponding.replacementETT.series.data.tree (Fin.last
        R.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧ b ∈ TashkinovStoredColors
        R.corresponding.replacementETT.series.data (Fin.last
        R.corresponding.replacementETT.rounds)) (gammaCut :
    ∀ eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount), a ∈ R.counterexample.good.gamma (Fin.last
        R.counterexample.hierarchy.dividerCount) eta ∨ b ∈ R.counterexample.good.gamma (Fin.last
        R.counterexample.hierarchy.dividerCount) eta → (↑(HierarchyFirstMissingPosition R.coloring
        T eta) : ℕ) ≤ X.length),
    ∃ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), (
    ∀ v ∈ TreeSequenceVertexSet B, MissingColors G S.coloring v = MissingColors G R.coloring v) ∧
        (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → S.coloring (T.edge t) =
        R.coloring (T.edge t)) ∧ (a ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)) →
        b ∈ MissingColors G S.coloring (T.vertex (Fin.last T.length))) ∧ (b ∈ MissingColors G
        R.coloring (T.vertex (Fin.last T.length)) → a ∈ MissingColors G S.coloring (T.vertex
        (Fin.last T.length)))),
    ∃ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha : Fin k),
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
        P.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let n : Fin (P.corresponding.replacementETT.rounds + (1 : ℕ)) := Fin.last
        P.corresponding.replacementETT.rounds;
    let Tn : TreeSequence G e0 := P.corresponding.replacementETT.series.data.tree n.castSucc;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ));
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let Gamma : Finset (Fin k) := D.biUnion (P.counterexample.good.gamma q);
    let baseExtraMissing : Finset (Fin k) := (TreeSequenceVertexSet P.replacementBase.core \
        TreeSequenceVertexSet Tn).biUnion fun (v : V) ↦ MissingColors G P.coloring v; alpha ∈
        MissingColors G P.coloring (T.vertex (Fin.last T.length)) ∧ alpha ∈ TreeMissingColors
        P.coloring B ∧ (alpha ∉ Gamma ∪ baseExtraMissing ∨
    ∃ eta ∈ D, alpha ∈ P.counterexample.good.gamma q eta ∧ (↑(HierarchyFirstMissingPosition
        P.coloring T eta) : ℕ) ≤ B.length)

private abbrev helperContinuation3982Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (hnonempty :
        (HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx).Nonempty) (j :
        ℕ) (hpathLower : (2 : ℕ) ≤ j) (hpathUpper : j < HierarchyFullTailLength C) (finiteChoice :
    ∀ (M F D U W N : Finset (Fin k)) (g : Fin k → Finset (Fin k)) (hstep : W ⊆ U ∪ N) (hncard :
        N.card ≤ (1 : ℕ)) (hgM :
    ∀ eta ∈ D, g eta ⊆ M) (hgcard :
    ∀ eta ∈ D, (g eta).card = (2 : ℕ)) (hgdis :
    ∀ eta ∈ D,
    ∀ theta ∈ D, eta ≠ theta → Disjoint (g eta) (g theta)) (hgd : Disjoint (D.biUnion g) D) (hnine
        : (((M \ F) \ U) \ (D.biUnion g ∪ D)).card ≤ (4 : ℕ) →
    ∃ (eta : Fin (7 : ℕ) → Fin k), Function.Injective eta ∧
    ∀ (h : Fin (7 : ℕ)), eta h ∈ D ∧ eta h ∈ M ∧ Disjoint (g (eta h) ∪ ({eta h} : Finset (Fin k)))
        U),
    ∃ beta ∈ M, beta ∉ D ∧ beta ∉ W ∧ (beta ∉ D.biUnion g ∪ F ∨
    ∃ eta ∈ D, beta ∈ g eta ∧ eta ∈ M)) (componentData :
    ∀ (psi : PartialEdgeColoring E k) (a b : Fin k) (hne : a ≠ b) (hproper : IsProperEdgeColoring
        G psi) (B : Finset V) (helem : ColoredVertexSetElementary G psi B) (u v w : V) (hu : u ∈
        B) (hv : v ∈ B) (hwu : w ≠ u) (hwv : w ≠ v) (hau : a ∈ MissingColors G psi u) (hbv : b ∈
        MissingColors G psi v) (hw : a ∈ MissingColors G psi w ∨ b ∈ MissingColors G psi w) (hsame
        : TwoColorComponent G psi a b (Sum.inl u) = TwoColorComponent G psi a b (Sum.inl v)),
        Disjoint (TwoColorComponent G psi a b (Sum.inl w)) (TwoColorComponent G psi a b (Sum.inl
        u)) ∧ TwoColorPathComponent G psi a b (Sum.inl w) ∧
    ∀ x ∈ B, MissingColors G (TwoColorComponentSwap G psi a b (Sum.inl w)) x = MissingColors G psi
        x) (trans :
    ∀ {X Y Z : TreeSequence G e0} (hXY : TreeSequenceInitialSegment X Y) (hYZ :
        TreeSequenceInitialSegment Y Z), TreeSequenceInitialSegment X Z),
    let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount);
    ∀ (starEq :
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount) = A) (hAT : TreeSequenceInitialSegment A T)
        (htail : (3 : ℕ) ≤ T.length - A.length) (hlen : (4 : ℕ) ≤ T.length),
    let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ)) (
    by omega
    ) (
    by omega
    );
    ∀ (hBT : TreeSequenceInitialSegment B T) (hAB : TreeSequenceInitialSegment A B) (fullB :
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyFullTailPrefix R.counterexample (HierarchyFullTailLength R.counterexample - (1 :
        ℕ)) = B) (elementary :
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        ColoredVertexSetElementary G R.coloring (TreeSequenceVertexSet B)) (vertexMem :
    ∀ (U : TreeSequence G e0) (j : Fin (U.length + (1 : ℕ))), U.vertex j ∈ TreeSequenceVertexSet
        U) (firstLe :
    ∀ (psi : PartialEdgeColoring E k) (c : Fin k) (j : Fin (T.length + (1 : ℕ))) (hj : c ∈
        MissingColors G psi (T.vertex j)), HierarchyFirstMissingPosition psi T c ≤ j) (firstAt :
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (c : Fin k) (j :
        Fin (B.length + (1 : ℕ))) (hc : c ∈ MissingColors G R.coloring (B.vertex j)),
        (↑(HierarchyFirstMissingPosition R.coloring T c) : ℕ) = (↑j : ℕ)) (firstFixed :
    ∀ (psi tau : PartialEdgeColoring E k) (hmissing :
    ∀ v ∈ TreeSequenceVertexSet B, MissingColors G tau v = MissingColors G psi v) (c : Fin k),
        HierarchyFirstMissingPosition tau T c = HierarchyFirstMissingPosition psi T c)
        (stageSwitch :
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (X : TreeSequence G
        e0) (hAX : TreeSequenceInitialSegment A X) (hAXlt : A.length < X.length) (hXB :
        TreeSequenceInitialSegment X B) (a b : Fin k) (hne : a ≠ b) (haStage : a ∈
        HierarchyStageMissingColors R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount)) (jb : Fin (B.length + (1 : ℕ))) (hjbX : (↑jb :
        ℕ) ≤ X.length) (hb : b ∈ MissingColors G R.coloring (B.vertex jb)) (hw : a ∈ MissingColors
        G R.coloring (T.vertex (Fin.last T.length)) ∨ b ∈ MissingColors G R.coloring (T.vertex
        (Fin.last T.length))) (haUnused :
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → R.coloring (T.edge t) ≠ some
        a) (hbException :
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → R.coloring (T.edge t) = some
        b → TreeIncidentEdge (R.corresponding.replacementETT.series.data.tree (Fin.last
        R.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧ b ∈ TashkinovStoredColors
        R.corresponding.replacementETT.series.data (Fin.last
        R.corresponding.replacementETT.rounds)) (gammaCut :
    ∀ eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount), a ∈ R.counterexample.good.gamma (Fin.last
        R.counterexample.hierarchy.dividerCount) eta ∨ b ∈ R.counterexample.good.gamma (Fin.last
        R.counterexample.hierarchy.dividerCount) eta → (↑(HierarchyFirstMissingPosition R.coloring
        T eta) : ℕ) ≤ X.length),
    ∃ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), (
    ∀ v ∈ TreeSequenceVertexSet B, MissingColors G S.coloring v = MissingColors G R.coloring v) ∧
        (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → S.coloring (T.edge t) =
        R.coloring (T.edge t)) ∧ (a ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)) →
        b ∈ MissingColors G S.coloring (T.vertex (Fin.last T.length))) ∧ (b ∈ MissingColors G
        R.coloring (T.vertex (Fin.last T.length)) → a ∈ MissingColors G S.coloring (T.vertex
        (Fin.last T.length)))) (gammaTransport :
    ∀ (R S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (eta : Fin k)
        (heta : eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount)), eta ∈ HierarchyStoredColorsAt
        S.counterexample.hierarchy (Fin.last S.counterexample.hierarchy.dividerCount) ∧
        R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta =
        S.counterexample.good.gamma (Fin.last S.counterexample.hierarchy.dividerCount) eta)
        (gammaUnused :
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (eta a : Fin k)
        (heta : eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount)) (ha : a ∈ R.counterexample.good.gamma (Fin.last
        R.counterexample.hierarchy.dividerCount) eta) (t : Fin T.length) (hlo : A.length ≤ (↑t :
        ℕ)) (hhi : (↑t : ℕ) < (↑(HierarchyFirstMissingPosition R.coloring T eta) : ℕ)), R.coloring
        (T.edge t) ≠ some a) (notRaw :
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (c : Fin k) (hcA :
        c ∉ TreeMissingColors R.coloring A) (hcD : c ∉ HierarchyStoredColorsAt
        R.counterexample.hierarchy (Fin.last R.counterexample.hierarchy.dividerCount)), c ∉
        TashkinovStoredColors R.corresponding.replacementETT.series.data (Fin.last
        R.corresponding.replacementETT.rounds)) (tailException :
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (j : ℕ) (hj : (1 :
        ℕ) ≤ j) (hjlt : j < T.length - A.length) (c : Fin k) (hc : c ∈ MissingColors G R.coloring
        ((HierarchyFullTailPrefix C j).vertex (Fin.last (HierarchyFullTailPrefix C j).length))) (t
        : Fin T.length) (hlo : A.length ≤ (↑t : ℕ)) (hhi : (↑t : ℕ) < A.length + j) (hcol :
        R.coloring (T.edge t) = some c), TreeIncidentEdge
        (R.corresponding.replacementETT.series.data.tree (Fin.last
        R.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧ c ∈ TashkinovStoredColors
        R.corresponding.replacementETT.series.data (Fin.last
        R.corresponding.replacementETT.rounds)),
    let Extra : (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) → Finset
        (Fin k) := fun (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) ↦
        (TreeSequenceVertexSet R.replacementBase.core \ TreeSequenceVertexSet
        (R.corresponding.replacementETT.series.data.tree (Fin.last
        R.corresponding.replacementETT.rounds).castSucc)).biUnion fun (v : V) ↦ MissingColors G
        R.coloring v;
    let Gamma : (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) → Finset
        (Fin k) := fun (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) ↦
        (HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount)).biUnion (R.counterexample.good.gamma (Fin.last
        R.counterexample.hierarchy.dividerCount));
    ∀ (gammaSub :
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), Gamma R ⊆
        TreeMissingColors R.coloring A) (extraFixed :
    ∀ (R S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (hm :
    ∀ v ∈ TreeSequenceVertexSet B, MissingColors G S.coloring v = MissingColors G R.coloring v),
        Extra S = Extra R) (gammaFixed :
    ∀ (R S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), Gamma R = Gamma
        S),
    let Y : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ));
    ∀ (hYlen : Y.length = A.length + (j - (2 : ℕ))) (hYT : TreeSequenceInitialSegment Y T) (hYB :
        TreeSequenceInitialSegment Y B) (hAY : TreeSequenceInitialSegment A Y),
    let I : Finset ℕ := HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx;
    let i : ℕ := I.max' hnonempty;
    ∀ (hiLower : (1 : ℕ) ≤ i) (hiUpper : i < j) (P : HierarchyReplacementPresentation G k e0 input
        T phi ett base C ctx) (alpha : Fin k) (haPrefix : alpha ∈ MissingColors G P.coloring
        ((HierarchyFullTailPrefix C i).vertex (Fin.last (HierarchyFullTailPrefix C i).length)))
        (haTerminal : alpha ∈ MissingColors G P.coloring (T.vertex (Fin.last T.length))) (hSlen :
        (HierarchyFullTailPrefix C i).length = A.length + i),
    let ja : Fin (B.length + (1 : ℕ)) := (⟨A.length + i,
    have hb : B.length = T.length - (1 : ℕ) := rfl; id (fun (hpathUpper : j < T.length - A.length)
        ↦ Decidable.byContradiction fun (a : ¬A.length + i < B.length + (1 : ℕ)) ↦
    by omega
    ) hpathUpper⟩ : Fin (B.length + (1 : ℕ)));
    ∀ (ha : alpha ∈ MissingColors G P.coloring (B.vertex ja)) (haOutside : alpha ∉
        TreeMissingColors P.coloring A) (haGood : alpha ∉ Gamma P ∪ Extra P) (hiEq : i = j - (1 :
        ℕ)),
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ));
    ∀ (hXlen : X.length = A.length + (j - (1 : ℕ))) (hXB : TreeSequenceInitialSegment X B) (hAX :
        TreeSequenceInitialSegment A X) (hAXlt : A.length < X.length) (hYXlen : X.length =
        Y.length + (1 : ℕ)) (hjaX : (↑ja : ℕ) = X.length),
    let D : Finset (Fin k) := HierarchyStoredColorsAt P.counterexample.hierarchy (Fin.last
        P.counterexample.hierarchy.dividerCount);
    let used : (r : ℕ) → Finset (Fin k) := fun (r : ℕ) ↦ ({c : Fin k |
    ∃ (t : Fin T.length), A.length ≤ (↑t : ℕ) ∧ (↑t : ℕ) < A.length + r ∧ P.coloring (T.edge t) =
        some c} : Finset (Fin k));
    let tnew : Fin T.length := (⟨Y.length,
    have this : X.length ≤ B.length := hXB.1;
    have this : B.length ≤ T.length := hBT.1; Decidable.byContradiction fun (a : ¬Y.length <
        T.length) ↦
    by omega
    ⟩ : Fin T.length);
    let fresh : Finset (Fin k) := ({c : Fin k | P.coloring (T.edge tnew) = some c} : Finset (Fin
        k));
    ∀ (freshCard : fresh.card ≤ (1 : ℕ)) (usedStep : used (j - (1 : ℕ)) ⊆ used (j - (2 : ℕ)) ∪
        fresh) (nineY : (2 : ℕ) * P.corresponding.replacementETT.rounds + (11 : ℕ) ≤
        ((TreeMissingColors P.coloring Y \ Extra P) \ used (j - (2 : ℕ))).card ∧
        ((((TreeMissingColors P.coloring Y \ Extra P) \ used (j - (2 : ℕ))) \ (Gamma P ∪ D)).card
        ≤ (4 : ℕ) →
    ∃ (eta : Fin (7 : ℕ) → Fin k), Function.Injective eta ∧
    ∀ (h : Fin (7 : ℕ)), eta h ∈ D ∧ eta h ∈ TreeMissingColors P.coloring Y ∧ Disjoint
        (P.counterexample.good.gamma (Fin.last P.counterexample.hierarchy.dividerCount) (eta h) ∪
        ({eta h} : Finset (Fin k))) (used (j - (2 : ℕ))))),
    ∃ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha : Fin k),
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
        P.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let n : Fin (P.corresponding.replacementETT.rounds + (1 : ℕ)) := Fin.last
        P.corresponding.replacementETT.rounds;
    let Tn : TreeSequence G e0 := P.corresponding.replacementETT.series.data.tree n.castSucc;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ));
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let Gamma : Finset (Fin k) := D.biUnion (P.counterexample.good.gamma q);
    let baseExtraMissing : Finset (Fin k) := (TreeSequenceVertexSet P.replacementBase.core \
        TreeSequenceVertexSet Tn).biUnion fun (v : V) ↦ MissingColors G P.coloring v; alpha ∈
        MissingColors G P.coloring (T.vertex (Fin.last T.length)) ∧ alpha ∈ TreeMissingColors
        P.coloring B ∧ (alpha ∉ Gamma ∪ baseExtraMissing ∨
    ∃ eta ∈ D, alpha ∈ P.counterexample.good.gamma q eta ∧ (↑(HierarchyFirstMissingPosition
        P.coloring T eta) : ℕ) ≤ B.length)

private abbrev helperContinuation3797Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (hvertexMissing :
    ∀ (mu : PartialEdgeColoring E k), IsProperEdgeColoring G mu → IsOneEdgeUncolored mu e0 →
    ∀ (v : V), (MissingColors G mu v).Nonempty) (hnonempty :
        (HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx).Nonempty) (j :
        ℕ) (hj : HierarchyPathNumber C.hierarchy = j) (hpathLower : (2 : ℕ) ≤ j) (hpathUpper : j <
        HierarchyFullTailLength C) (finiteChoice :
    ∀ (M F D U W N : Finset (Fin k)) (g : Fin k → Finset (Fin k)) (hstep : W ⊆ U ∪ N) (hncard :
        N.card ≤ (1 : ℕ)) (hgM :
    ∀ eta ∈ D, g eta ⊆ M) (hgcard :
    ∀ eta ∈ D, (g eta).card = (2 : ℕ)) (hgdis :
    ∀ eta ∈ D,
    ∀ theta ∈ D, eta ≠ theta → Disjoint (g eta) (g theta)) (hgd : Disjoint (D.biUnion g) D) (hnine
        : (((M \ F) \ U) \ (D.biUnion g ∪ D)).card ≤ (4 : ℕ) →
    ∃ (eta : Fin (7 : ℕ) → Fin k), Function.Injective eta ∧
    ∀ (h : Fin (7 : ℕ)), eta h ∈ D ∧ eta h ∈ M ∧ Disjoint (g (eta h) ∪ ({eta h} : Finset (Fin k)))
        U),
    ∃ beta ∈ M, beta ∉ D ∧ beta ∉ W ∧ (beta ∉ D.biUnion g ∪ F ∨
    ∃ eta ∈ D, beta ∈ g eta ∧ eta ∈ M)) (componentData :
    ∀ (psi : PartialEdgeColoring E k) (a b : Fin k) (hne : a ≠ b) (hproper : IsProperEdgeColoring
        G psi) (B : Finset V) (helem : ColoredVertexSetElementary G psi B) (u v w : V) (hu : u ∈
        B) (hv : v ∈ B) (hwu : w ≠ u) (hwv : w ≠ v) (hau : a ∈ MissingColors G psi u) (hbv : b ∈
        MissingColors G psi v) (hw : a ∈ MissingColors G psi w ∨ b ∈ MissingColors G psi w) (hsame
        : TwoColorComponent G psi a b (Sum.inl u) = TwoColorComponent G psi a b (Sum.inl v)),
        Disjoint (TwoColorComponent G psi a b (Sum.inl w)) (TwoColorComponent G psi a b (Sum.inl
        u)) ∧ TwoColorPathComponent G psi a b (Sum.inl w) ∧
    ∀ x ∈ B, MissingColors G (TwoColorComponentSwap G psi a b (Sum.inl w)) x = MissingColors G psi
        x) (trans :
    ∀ {X Y Z : TreeSequence G e0} (hXY : TreeSequenceInitialSegment X Y) (hYZ :
        TreeSequenceInitialSegment Y Z), TreeSequenceInitialSegment X Z) (common :
    ∀ {X Y Z : TreeSequence G e0} (hXZ : TreeSequenceInitialSegment X Z) (hYZ :
        TreeSequenceInitialSegment Y Z) (hXY : X.length ≤ Y.length), TreeSequenceInitialSegment X
        Y),
    let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount);
    ∀ (starEq :
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount) = A) (hAT : TreeSequenceInitialSegment A T)
        (htail : (3 : ℕ) ≤ T.length - A.length) (hlen : (4 : ℕ) ≤ T.length),
    let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ)) (
    by omega
    ) (
    by omega
    );
    ∀ (hBT : TreeSequenceInitialSegment B T) (hAB : TreeSequenceInitialSegment A B) (fullEq :
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (j : ℕ),
        HierarchyFullTailPrefix R.counterexample j = HierarchyFullTailPrefix C j) (fullB :
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyFullTailPrefix R.counterexample (HierarchyFullTailLength R.counterexample - (1 :
        ℕ)) = B) (elementary :
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        ColoredVertexSetElementary G R.coloring (TreeSequenceVertexSet B)) (vertexMem :
    ∀ (U : TreeSequence G e0) (j : Fin (U.length + (1 : ℕ))), U.vertex j ∈ TreeSequenceVertexSet
        U) (firstLe :
    ∀ (psi : PartialEdgeColoring E k) (c : Fin k) (j : Fin (T.length + (1 : ℕ))) (hj : c ∈
        MissingColors G psi (T.vertex j)), HierarchyFirstMissingPosition psi T c ≤ j) (firstAt :
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (c : Fin k) (j :
        Fin (B.length + (1 : ℕ))) (hc : c ∈ MissingColors G R.coloring (B.vertex j)),
        (↑(HierarchyFirstMissingPosition R.coloring T c) : ℕ) = (↑j : ℕ)) (firstFixed :
    ∀ (psi tau : PartialEdgeColoring E k) (hmissing :
    ∀ v ∈ TreeSequenceVertexSet B, MissingColors G tau v = MissingColors G psi v) (c : Fin k),
        HierarchyFirstMissingPosition tau T c = HierarchyFirstMissingPosition psi T c)
        (stageSwitch :
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (X : TreeSequence G
        e0) (hAX : TreeSequenceInitialSegment A X) (hAXlt : A.length < X.length) (hXB :
        TreeSequenceInitialSegment X B) (a b : Fin k) (hne : a ≠ b) (haStage : a ∈
        HierarchyStageMissingColors R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount)) (jb : Fin (B.length + (1 : ℕ))) (hjbX : (↑jb :
        ℕ) ≤ X.length) (hb : b ∈ MissingColors G R.coloring (B.vertex jb)) (hw : a ∈ MissingColors
        G R.coloring (T.vertex (Fin.last T.length)) ∨ b ∈ MissingColors G R.coloring (T.vertex
        (Fin.last T.length))) (haUnused :
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → R.coloring (T.edge t) ≠ some
        a) (hbException :
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → R.coloring (T.edge t) = some
        b → TreeIncidentEdge (R.corresponding.replacementETT.series.data.tree (Fin.last
        R.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧ b ∈ TashkinovStoredColors
        R.corresponding.replacementETT.series.data (Fin.last
        R.corresponding.replacementETT.rounds)) (gammaCut :
    ∀ eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount), a ∈ R.counterexample.good.gamma (Fin.last
        R.counterexample.hierarchy.dividerCount) eta ∨ b ∈ R.counterexample.good.gamma (Fin.last
        R.counterexample.hierarchy.dividerCount) eta → (↑(HierarchyFirstMissingPosition R.coloring
        T eta) : ℕ) ≤ X.length),
    ∃ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), (
    ∀ v ∈ TreeSequenceVertexSet B, MissingColors G S.coloring v = MissingColors G R.coloring v) ∧
        (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → S.coloring (T.edge t) =
        R.coloring (T.edge t)) ∧ (a ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)) →
        b ∈ MissingColors G S.coloring (T.vertex (Fin.last T.length))) ∧ (b ∈ MissingColors G
        R.coloring (T.vertex (Fin.last T.length)) → a ∈ MissingColors G S.coloring (T.vertex
        (Fin.last T.length)))) (gammaTransport :
    ∀ (R S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (eta : Fin k)
        (heta : eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount)), eta ∈ HierarchyStoredColorsAt
        S.counterexample.hierarchy (Fin.last S.counterexample.hierarchy.dividerCount) ∧
        R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta =
        S.counterexample.good.gamma (Fin.last S.counterexample.hierarchy.dividerCount) eta)
        (gammaUnused :
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (eta a : Fin k)
        (heta : eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount)) (ha : a ∈ R.counterexample.good.gamma (Fin.last
        R.counterexample.hierarchy.dividerCount) eta) (t : Fin T.length) (hlo : A.length ≤ (↑t :
        ℕ)) (hhi : (↑t : ℕ) < (↑(HierarchyFirstMissingPosition R.coloring T eta) : ℕ)), R.coloring
        (T.edge t) ≠ some a) (outsideA :
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (c : Fin k) (j :
        Fin (B.length + (1 : ℕ))) (hj : A.length < (↑j : ℕ)) (hc : c ∈ MissingColors G R.coloring
        (B.vertex j)), c ∉ TreeMissingColors R.coloring A) (notRaw :
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (c : Fin k) (hcA :
        c ∉ TreeMissingColors R.coloring A) (hcD : c ∉ HierarchyStoredColorsAt
        R.counterexample.hierarchy (Fin.last R.counterexample.hierarchy.dividerCount)), c ∉
        TashkinovStoredColors R.corresponding.replacementETT.series.data (Fin.last
        R.corresponding.replacementETT.rounds)) (tailException :
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (j : ℕ) (hj : (1 :
        ℕ) ≤ j) (hjlt : j < T.length - A.length) (c : Fin k) (hc : c ∈ MissingColors G R.coloring
        ((HierarchyFullTailPrefix C j).vertex (Fin.last (HierarchyFullTailPrefix C j).length))) (t
        : Fin T.length) (hlo : A.length ≤ (↑t : ℕ)) (hhi : (↑t : ℕ) < A.length + j) (hcol :
        R.coloring (T.edge t) = some c), TreeIncidentEdge
        (R.corresponding.replacementETT.series.data.tree (Fin.last
        R.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧ c ∈ TashkinovStoredColors
        R.corresponding.replacementETT.series.data (Fin.last
        R.corresponding.replacementETT.rounds)) (coreA :
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        TreeSequenceInitialSegment R.replacementBase.core A),
    ∃ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha : Fin k),
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
        P.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let n : Fin (P.corresponding.replacementETT.rounds + (1 : ℕ)) := Fin.last
        P.corresponding.replacementETT.rounds;
    let Tn : TreeSequence G e0 := P.corresponding.replacementETT.series.data.tree n.castSucc;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ));
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let Gamma : Finset (Fin k) := D.biUnion (P.counterexample.good.gamma q);
    let baseExtraMissing : Finset (Fin k) := (TreeSequenceVertexSet P.replacementBase.core \
        TreeSequenceVertexSet Tn).biUnion fun (v : V) ↦ MissingColors G P.coloring v; alpha ∈
        MissingColors G P.coloring (T.vertex (Fin.last T.length)) ∧ alpha ∈ TreeMissingColors
        P.coloring B ∧ (alpha ∉ Gamma ∪ baseExtraMissing ∨
    ∃ eta ∈ D, alpha ∈ P.counterexample.good.gamma q eta ∧ (↑(HierarchyFirstMissingPosition
        P.coloring T eta) : ℕ) ≤ B.length)

private abbrev helperHunusedBetween1548Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (hnonempty :
        (HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx).Nonempty) (j :
        ℕ) (_ : (2 : ℕ) ≤ j) (hpathUpper : j < HierarchyFullTailLength C),
    let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount);
    ∀ (htail : (3 : ℕ) ≤ T.length - A.length) (hlen : (4 : ℕ) ≤ T.length),
    let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ)) (
    by
       have := GoldbergSeymour.TreeSequence.positive T
       omega
    ) (
    by
       have := GoldbergSeymour.TreeSequence.positive T
       omega
    );
    ∀ (hBT : TreeSequenceInitialSegment B T),
    let Y : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ)); Y.length = A.length + (j
        - (2 : ℕ)) →
    ∀ (hYB : TreeSequenceInitialSegment Y B),
    let I : Finset ℕ := HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx;
    let i : ℕ := I.max' hnonempty;
    ∀ (hiUpper : i < j) (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
        (alpha : Fin k) (hSlen : (HierarchyFullTailPrefix C i).length = A.length + i),
    let ja : Fin (B.length + (1 : ℕ)) := (⟨A.length + i,
    have hb : B.length = T.length - (1 : ℕ) := rfl; id (fun (hpathUpper : j < T.length - A.length)
        ↦ Decidable.byContradiction fun (a : ¬A.length + i < B.length + (1 : ℕ)) ↦
    by omega
    ) hpathUpper⟩ : Fin (B.length + (1 : ℕ))); i = j - (1 : ℕ) →
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ)); X.length = A.length + (j
        - (1 : ℕ)) → TreeSequenceInitialSegment X B → X.length = Y.length + (1 : ℕ) → (↑ja : ℕ) =
        X.length →
    ∀ (beta : Fin k) (yb : Fin (Y.length + (1 : ℕ))),
    let jb : Fin (B.length + (1 : ℕ)) := Fin.castLE (Nat.succ_le_succ hYB.1) yb;
        (↑(HierarchyFirstMissingPosition P.coloring T alpha) : ℕ) = X.length → (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → P.coloring (T.edge t) ≠ some
        beta) → A.length < (↑jb : ℕ) → (↑(HierarchyFirstMissingPosition P.coloring T beta) : ℕ) =
        (↑jb : ℕ) → Fin.castLE (Nat.succ_le_succ hBT.1) jb = HierarchyFirstMissingPosition
        P.coloring T beta → Fin.castLE (Nat.succ_le_succ hBT.1) ja = HierarchyFirstMissingPosition
        P.coloring T alpha → beta ∉ ({c : Fin k |
    ∃ (t : Fin T.length), (↑(HierarchyFirstMissingPosition P.coloring T beta) : ℕ) ≤ (↑t : ℕ) ∧
        (↑t : ℕ) < (↑(HierarchyFirstMissingPosition P.coloring T alpha) : ℕ) ∧ P.coloring (T.edge
        t) = some c} : Finset (Fin k))

private abbrev helperContinuation4396Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (hnonempty :
        (HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx).Nonempty) (j :
        ℕ) (hpathLower : (2 : ℕ) ≤ j) (hpathUpper : j < HierarchyFullTailLength C) (componentData
        :
    ∀ (psi : PartialEdgeColoring E k) (a b : Fin k) (hne : a ≠ b) (hproper : IsProperEdgeColoring
        G psi) (B : Finset V) (helem : ColoredVertexSetElementary G psi B) (u v w : V) (hu : u ∈
        B) (hv : v ∈ B) (hwu : w ≠ u) (hwv : w ≠ v) (hau : a ∈ MissingColors G psi u) (hbv : b ∈
        MissingColors G psi v) (hw : a ∈ MissingColors G psi w ∨ b ∈ MissingColors G psi w) (hsame
        : TwoColorComponent G psi a b (Sum.inl u) = TwoColorComponent G psi a b (Sum.inl v)),
        Disjoint (TwoColorComponent G psi a b (Sum.inl w)) (TwoColorComponent G psi a b (Sum.inl
        u)) ∧ TwoColorPathComponent G psi a b (Sum.inl w) ∧
    ∀ x ∈ B, MissingColors G (TwoColorComponentSwap G psi a b (Sum.inl w)) x = MissingColors G psi
        x) (trans :
    ∀ {X Y Z : TreeSequence G e0} (hXY : TreeSequenceInitialSegment X Y) (hYZ :
        TreeSequenceInitialSegment Y Z), TreeSequenceInitialSegment X Z),
    let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount);
    ∀ (starEq :
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount) = A) (hAT : TreeSequenceInitialSegment A T)
        (htail : (3 : ℕ) ≤ T.length - A.length) (hlen : (4 : ℕ) ≤ T.length),
    let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ)) (
    by omega
    ) (
    by omega
    );
    ∀ (hBT : TreeSequenceInitialSegment B T) (fullB :
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyFullTailPrefix R.counterexample (HierarchyFullTailLength R.counterexample - (1 :
        ℕ)) = B) (elementary :
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        ColoredVertexSetElementary G R.coloring (TreeSequenceVertexSet B)) (vertexMem :
    ∀ (U : TreeSequence G e0) (j : Fin (U.length + (1 : ℕ))), U.vertex j ∈ TreeSequenceVertexSet
        U),
    let Extra : (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) → Finset
        (Fin k) := fun (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) ↦
        (TreeSequenceVertexSet R.replacementBase.core \ TreeSequenceVertexSet
        (R.corresponding.replacementETT.series.data.tree (Fin.last
        R.corresponding.replacementETT.rounds).castSucc)).biUnion fun (v : V) ↦ MissingColors G
        R.coloring v;
    let Gamma : (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) → Finset
        (Fin k) := fun (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) ↦
        (HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount)).biUnion (R.counterexample.good.gamma (Fin.last
        R.counterexample.hierarchy.dividerCount));
    let Y : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ));
    ∀ (hYlen : Y.length = A.length + (j - (2 : ℕ))) (hYB : TreeSequenceInitialSegment Y B),
    let I : Finset ℕ := HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx;
    let i : ℕ := I.max' hnonempty;
    ∀ (hiUpper : i < j) (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
        (alpha : Fin k) (haPrefix : alpha ∈ MissingColors G P.coloring ((HierarchyFullTailPrefix C
        i).vertex (Fin.last (HierarchyFullTailPrefix C i).length))) (haTerminal : alpha ∈
        MissingColors G P.coloring (T.vertex (Fin.last T.length))) (hSlen :
        (HierarchyFullTailPrefix C i).length = A.length + i),
    let ja : Fin (B.length + (1 : ℕ)) := (⟨A.length + i,
    by
          first
          | omega
          | (
            have := GoldbergSeymour.TreeSequence.positive T
            have := hAT.1
            have := hBT.1
            have := hYB.1
            have :=
             GoldbergSeymour.TreeSequence.positive
              (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount))
            have :=
             GoldbergSeymour.TreeSequence.positive
              (TreeSequencePrefix T (T.length - (1 : ℕ)) (by omega) (by omega))
            have := GoldbergSeymour.TreeSequence.positive T
            dsimp only [GoldbergSeymour.HierarchyFullTailLength,
             GoldbergSeymour.HierarchyFullTailPrefix, GoldbergSeymour.TreeSequencePrefix] at *
            dsimp only [B, GoldbergSeymour.TreeSequencePrefix] at *
            all_goals omega)
    ⟩ : Fin (B.length + (1 : ℕ)));
    ∀ (ha : alpha ∈ MissingColors G P.coloring (B.vertex ja)) (haOutside : alpha ∉
        TreeMissingColors P.coloring A) (haGood : alpha ∉ Gamma P ∪ Extra P) (hiEq : i = j - (1 :
        ℕ)),
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ));
    ∀ (hXlen : X.length = A.length + (j - (1 : ℕ))) (hXB : TreeSequenceInitialSegment X B) (hYXlen
        : X.length = Y.length + (1 : ℕ)) (hjaX : (↑ja : ℕ) = X.length),
    let D : Finset (Fin k) := HierarchyStoredColorsAt P.counterexample.hierarchy (Fin.last
        P.counterexample.hierarchy.dividerCount);
    let used : (r : ℕ) → Finset (Fin k) := fun (r : ℕ) ↦ ({c : Fin k |
    ∃ (t : Fin T.length), A.length ≤ (↑t : ℕ) ∧ (↑t : ℕ) < A.length + r ∧ P.coloring (T.edge t) =
        some c} : Finset (Fin k));
    ∀ (beta : Fin k) (hbY : beta ∈ TreeMissingColors P.coloring Y) (hbD : beta ∉ D) (hbUsed : beta
        ∉ used (j - (1 : ℕ))) (hbChoice : beta ∉ Gamma P ∪ Extra P ∨
    ∃ eta ∈ D, beta ∈ P.counterexample.good.gamma (Fin.last
        P.counterexample.hierarchy.dividerCount) eta ∧ (↑(HierarchyFirstMissingPosition P.coloring
        T eta) : ℕ) ≤ Y.length) (vbeta : V) (hbeta : beta ∈ MissingColors G P.coloring vbeta) (yb
        : Fin (Y.length + (1 : ℕ))),
    let jb : Fin (B.length + (1 : ℕ)) := Fin.castLE (Nat.succ_le_succ hYB.1) yb;
    ∀ (hb : beta ∈ MissingColors G P.coloring (B.vertex jb)) (haFirst :
        (↑(HierarchyFirstMissingPosition P.coloring T alpha) : ℕ) = X.length) (habNe : alpha ≠
        beta) (hbUnused :
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → P.coloring (T.edge t) ≠ some
        beta) (haException :
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → P.coloring (T.edge t) = some
        alpha → TreeIncidentEdge (P.corresponding.replacementETT.series.data.tree (Fin.last
        P.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧ alpha ∈
        TashkinovStoredColors P.corresponding.replacementETT.series.data (Fin.last
        P.corresponding.replacementETT.rounds)) (cutBeta :
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (hm :
    ∀ v ∈ TreeSequenceVertexSet B, MissingColors G R.coloring v = MissingColors G P.coloring v),
    ∀ eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount), beta ∈ R.counterexample.good.gamma (Fin.last
        R.counterexample.hierarchy.dividerCount) eta → (↑(HierarchyFirstMissingPosition R.coloring
        T eta) : ℕ) ≤ Y.length) (finish :
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (hm :
    ∀ v ∈ TreeSequenceVertexSet B, MissingColors G R.coloring v = MissingColors G P.coloring v)
        (hterm : beta ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length))), beta ∈
        TreeMissingColors R.coloring Y ∧ (beta ∉ Gamma R ∪ Extra R ∨
    ∃ eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount), beta ∈ R.counterexample.good.gamma (Fin.last
        R.counterexample.hierarchy.dividerCount) eta ∧ (↑(HierarchyFirstMissingPosition R.coloring
        T eta) : ℕ) ≤ Y.length)) (hAlphaStored : alpha ∉ D) (hbStage : beta ∉
        HierarchyStageMissingColors P.counterexample.hierarchy (Fin.last
        P.counterexample.hierarchy.dividerCount)) (hbOutsideChoice : beta ∉ Gamma P ∪ Extra P)
        (hbOutside : beta ∉ TreeMissingColors P.coloring A) (hjbA : A.length < (↑jb : ℕ)) (haRaw :
        alpha ∉ TashkinovStoredColors P.corresponding.replacementETT.series.data (Fin.last
        P.corresponding.replacementETT.rounds)) (hbRaw : beta ∉ TashkinovStoredColors
        P.corresponding.replacementETT.series.data (Fin.last
        P.corresponding.replacementETT.rounds)) (ibEq : (↑(HierarchyFirstMissingPosition
        P.coloring T beta) : ℕ) = (↑jb : ℕ)) (iaEq : (↑(HierarchyFirstMissingPosition P.coloring T
        alpha) : ℕ) = (↑ja : ℕ)) (jbEq : Fin.castLE (Nat.succ_le_succ hBT.1) jb =
        HierarchyFirstMissingPosition P.coloring T beta) (jaEq : Fin.castLE (Nat.succ_le_succ
        hBT.1) ja = HierarchyFirstMissingPosition P.coloring T alpha) (hordered : TreeVertexOrder
        T (T.vertex (HierarchyFirstMissingPosition P.coloring T beta)) (T.vertex
        (HierarchyFirstMissingPosition P.coloring T alpha))) (hunused : beta ∉ ({c : Fin k |
    ∃ (t : Fin T.length), A.length ≤ (↑t : ℕ) ∧ (↑t : ℕ) < (↑(HierarchyFirstMissingPosition
        P.coloring T alpha) : ℕ) ∧ P.coloring (T.edge t) = some c} : Finset (Fin k))),
    ∃ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha : Fin k),
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
        P.counterexample.hierarchy;
    have q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    have n : Fin (P.corresponding.replacementETT.rounds + (1 : ℕ)) := Fin.last
        P.corresponding.replacementETT.rounds;
    have Tn : TreeSequence G e0 := P.corresponding.replacementETT.series.data.tree n.castSucc;
    have B : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ));
    have D : Finset (Fin k) := HierarchyStoredColorsAt H q;
    have Gamma : Finset (Fin k) := D.biUnion (P.counterexample.good.gamma q);
    have baseExtraMissing : Finset (Fin k) := (TreeSequenceVertexSet P.replacementBase.core \
        TreeSequenceVertexSet Tn).biUnion fun (v : V) ↦ MissingColors G P.coloring v; alpha ∈
        MissingColors G P.coloring (T.vertex (Fin.last T.length)) ∧ alpha ∈ TreeMissingColors
        P.coloring B ∧ (alpha ∉ Gamma ∪ baseExtraMissing ∨
    ∃ eta ∈ D, alpha ∈ P.counterexample.good.gamma q eta ∧ (↑(HierarchyFirstMissingPosition
        P.coloring T eta) : ℕ) ≤ B.length)

private abbrev helperCaseContinuation5383Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (j : ℕ) (trans :
    ∀ {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Y → TreeSequenceInitialSegment Y Z
        → TreeSequenceInitialSegment X Z) (common :
    ∀ {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Z → TreeSequenceInitialSegment Y Z
        → X.length ≤ Y.length → TreeSequenceInitialSegment X Y),
    let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount);
    ∀ (starEq :
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount) = A) (hlen : (4 : ℕ) ≤ T.length),
    let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ)) (
    by omega
    ) (
    by omega
    );
    ∀ (hBT : TreeSequenceInitialSegment B T) (hAB : TreeSequenceInitialSegment A B) (fullB :
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyFullTailPrefix R.counterexample (HierarchyFullTailLength R.counterexample - (1 :
        ℕ)) = B) (vertexMem :
    ∀ (U : TreeSequence G e0) (j : Fin (U.length + (1 : ℕ))), U.vertex j ∈ TreeSequenceVertexSet
        U) (firstFixed :
    ∀ (psi tau : PartialEdgeColoring E k), (
    ∀ v ∈ TreeSequenceVertexSet B, MissingColors G tau v = MissingColors G psi v) →
    ∀ (c : Fin k), HierarchyFirstMissingPosition tau T c = HierarchyFirstMissingPosition psi T c)
        (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (X : TreeSequence
        G e0) (hAX : TreeSequenceInitialSegment A X) (hAXlt : A.length < X.length) (hXB :
        TreeSequenceInitialSegment X B) (a b : Fin k) (hne : a ≠ b) (jb : Fin (B.length + (1 :
        ℕ))) (hjbX : (↑jb : ℕ) ≤ X.length) (hb : b ∈ MissingColors G R.coloring (B.vertex jb)) (hw
        : a ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)) ∨ b ∈ MissingColors G
        R.coloring (T.vertex (Fin.last T.length))) (haUnused :
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → R.coloring (T.edge t) ≠ some
        a) (hbException :
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → R.coloring (T.edge t) = some
        b → TreeIncidentEdge (R.corresponding.replacementETT.series.data.tree (Fin.last
        R.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧ b ∈ TashkinovStoredColors
        R.corresponding.replacementETT.series.data (Fin.last
        R.corresponding.replacementETT.rounds)) (gammaCut :
    ∀ eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount), a ∈ R.counterexample.good.gamma (Fin.last
        R.counterexample.hierarchy.dividerCount) eta ∨ b ∈ R.counterexample.good.gamma (Fin.last
        R.counterexample.hierarchy.dividerCount) eta → (↑(HierarchyFirstMissingPosition R.coloring
        T eta) : ℕ) ≤ X.length),
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let n : Fin (R.corresponding.replacementETT.rounds + (1 : ℕ)) := Fin.last
        R.corresponding.replacementETT.rounds;
    let Tn : TreeSequence G e0 := R.corresponding.replacementETT.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors R.corresponding.replacementETT.series.data n;
    ∀ (hTnA : TreeSequenceInitialSegment Tn A) (stageCase : (0 : ℕ) < H.dividerCount ∧ a ∈
        TreeMissingColors R.coloring (H.stage (⟨H.dividerCount,
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) ∨ H.dividerCount = (0 : ℕ) ∧ a ∈ TreeMissingColors
        R.coloring Tn) (hbB : b ∈ TreeMissingColors R.coloring B) (haB : a ∈ TreeMissingColors
        R.coloring B) (iaLe : (↑(HierarchyFirstMissingPosition R.coloring T a) : ℕ) ≤ A.length)
        (ibEq : (↑(HierarchyFirstMissingPosition R.coloring T b) : ℕ) = (↑jb : ℕ)),
    let ja : Fin (B.length + (1 : ℕ)) := (⟨(↑(HierarchyFirstMissingPosition R.coloring T a) : ℕ),
    have this : A.length ≤ B.length := hAB.1; Decidable.byContradiction fun (a_1 :
        ¬(↑(HierarchyFirstMissingPosition R.coloring T a) : ℕ) < B.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (B.length + (1 : ℕ)));
    ∀ (jaEq : Fin.castLE (Nat.succ_le_succ hBT.1) ja = HierarchyFirstMissingPosition R.coloring T
        a) (jbEq : Fin.castLE (Nat.succ_le_succ hBT.1) jb = HierarchyFirstMissingPosition
        R.coloring T b) (haFirstB : a ∈ MissingColors G R.coloring (B.vertex ja)) (hprefixR :
        ColoredVertexSetElementary G R.coloring (TreeSequenceVertexSet (HierarchyFullTailPrefix
        R.counterexample (HierarchyFullTailLength R.counterexample - (1 : ℕ))))) (hmissingR : a ∈
        TreeMissingColors R.coloring (HierarchyFullTailPrefix R.counterexample
        (HierarchyFullTailLength R.counterexample - (1 : ℕ))) ∧ b ∈ TreeMissingColors R.coloring
        (HierarchyFullTailPrefix R.counterexample (HierarchyFullTailLength R.counterexample - (1 :
        ℕ)))) (change :
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
        TreeMissingColors R.coloring Tnq ∨ Disjoint (insert a ({ b } : Finset (Fin k)) : Finset
        (Fin k)) Dnq) → sameComponent) ∧ (H.dividerCount = (0 : ℕ) ∧ (a ∈ TreeMissingColors
        R.coloring Tn ∨ Disjoint (insert a ({ b } : Finset (Fin k)) : Finset (Fin k)) Dn) →
        sameComponent) ∧ (a ∈ TreeMissingColors R.coloring A ∧ TreeColorSetClosed G R.coloring A
        ({ a } : Finset (Fin k)) → sameComponent ∧ TreeInterchangeable G A R.coloring a b)) (hdis
        : Disjoint (TwoColorComponent G R.coloring a b (Sum.inl (T.vertex (Fin.last T.length))))
        (TwoColorComponent G R.coloring a b (Sum.inl (B.vertex ja)))) (hpath :
        TwoColorPathComponent G R.coloring a b (Sum.inl (T.vertex (Fin.last T.length)))) (hmissing
        :
    ∀ x ∈ TreeSequenceVertexSet B, MissingColors G (TwoColorComponentSwap G R.coloring a b
        (Sum.inl (T.vertex (Fin.last T.length)))) x = MissingColors G R.coloring x),
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G R.coloring a b (Sum.inl
        (T.vertex (Fin.last T.length)));
    ∀ (hsone : IsOneEdgeUncolored sigma e0),
    ∃ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), (
    ∀ v ∈ TreeSequenceVertexSet B, MissingColors G S.coloring v = MissingColors G R.coloring v) ∧
        (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → S.coloring (T.edge t) =
        R.coloring (T.edge t)) ∧ (a ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)) →
        b ∈ MissingColors G S.coloring (T.vertex (Fin.last T.length))) ∧ (b ∈ MissingColors G
        R.coloring (T.vertex (Fin.last T.length)) → a ∈ MissingColors G S.coloring (T.vertex
        (Fin.last T.length)))

private abbrev helperContinuation3692Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (_ :
    ∀ (mu : PartialEdgeColoring E k), IsProperEdgeColoring G mu → IsOneEdgeUncolored mu e0 →
    ∀ (v : V), (MissingColors G mu v).Nonempty) (_ : (HierarchyEligibleCommonMissingIndices G k e0
        input T phi ett base C ctx).Nonempty) (j : ℕ) (_ : HierarchyPathNumber C.hierarchy = j) (_
        : (2 : ℕ) ≤ j) (_ : j < HierarchyFullTailLength C) (_ :
    ∀ (M F D U W N : Finset (Fin k)) (g : Fin k → Finset (Fin k)) (_ : W ⊆ U ∪ N) (_ : N.card ≤ (1
        : ℕ)) (_ :
    ∀ eta ∈ D, g eta ⊆ M) (_ :
    ∀ eta ∈ D, (g eta).card = (2 : ℕ)) (_ :
    ∀ eta ∈ D,
    ∀ theta ∈ D, eta ≠ theta → Disjoint (g eta) (g theta)) (_ : Disjoint (D.biUnion g) D) (_ :
        (((M \ F) \ U) \ (D.biUnion g ∪ D)).card ≤ (4 : ℕ) →
    ∃ (eta : Fin (7 : ℕ) → Fin k), Function.Injective eta ∧
    ∀ (h : Fin (7 : ℕ)), eta h ∈ D ∧ eta h ∈ M ∧ Disjoint (g (eta h) ∪ ({eta h} : Finset (Fin k)))
        U),
    ∃ beta ∈ M, beta ∉ D ∧ beta ∉ W ∧ (beta ∉ D.biUnion g ∪ F ∨
    ∃ eta ∈ D, beta ∈ g eta ∧ eta ∈ M)) (_ :
    ∀ (psi : PartialEdgeColoring E k) (a b : Fin k) (_ : a ≠ b) (_ : IsProperEdgeColoring G psi)
        (B : Finset V) (_ : ColoredVertexSetElementary G psi B) (u v w : V) (_ : u ∈ B) (_ : v ∈
        B) (_ : w ≠ u) (_ : w ≠ v) (_ : a ∈ MissingColors G psi u) (_ : b ∈ MissingColors G psi v)
        (_ : a ∈ MissingColors G psi w ∨ b ∈ MissingColors G psi w) (_ : TwoColorComponent G psi a
        b (Sum.inl u) = TwoColorComponent G psi a b (Sum.inl v)), Disjoint (TwoColorComponent G
        psi a b (Sum.inl w)) (TwoColorComponent G psi a b (Sum.inl u)) ∧ TwoColorPathComponent G
        psi a b (Sum.inl w) ∧
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
        R.counterexample.hierarchy.dividerCount) = A) (_ : TreeSequenceInitialSegment A T) (_ : (3
        : ℕ) ≤ T.length - A.length) (hlen : (4 : ℕ) ≤ T.length),
    let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ)) (
    by omega
    ) (
    by omega
    );
    ∀ (_ : TreeSequenceInitialSegment B T) (_ : TreeSequenceInitialSegment A B) (_ :
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (j : ℕ),
        HierarchyFullTailPrefix R.counterexample j = HierarchyFullTailPrefix C j) (_ :
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyFullTailPrefix R.counterexample (HierarchyFullTailLength R.counterexample - (1 :
        ℕ)) = B) (_ :
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        ColoredVertexSetElementary G R.coloring (TreeSequenceVertexSet B)) (_ :
    ∀ (U : TreeSequence G e0) (j : Fin (U.length + (1 : ℕ))), U.vertex j ∈ TreeSequenceVertexSet
        U) (_ :
    ∀ (psi : PartialEdgeColoring E k) (c : Fin k) (j : Fin (T.length + (1 : ℕ))) (_ : c ∈
        MissingColors G psi (T.vertex j)), HierarchyFirstMissingPosition psi T c ≤ j) (_ :
    ∀ (psi : PartialEdgeColoring E k) (c : Fin k) (_ : (↑(HierarchyFirstMissingPosition psi T c) :
        ℕ) < T.length), c ∈ MissingColors G psi (T.vertex (HierarchyFirstMissingPosition psi T
        c))) (_ :
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (c : Fin k) (j :
        Fin (B.length + (1 : ℕ))) (_ : c ∈ MissingColors G R.coloring (B.vertex j)),
        (↑(HierarchyFirstMissingPosition R.coloring T c) : ℕ) = (↑j : ℕ)) (_ :
    ∀ (psi tau : PartialEdgeColoring E k) (_ :
    ∀ v ∈ TreeSequenceVertexSet B, MissingColors G tau v = MissingColors G psi v) (c : Fin k),
        HierarchyFirstMissingPosition tau T c = HierarchyFirstMissingPosition psi T c),
    ∃ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha : Fin k),
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
        P.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let n : Fin (P.corresponding.replacementETT.rounds + (1 : ℕ)) := Fin.last
        P.corresponding.replacementETT.rounds;
    let Tn : TreeSequence G e0 := P.corresponding.replacementETT.series.data.tree n.castSucc;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ));
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let Gamma : Finset (Fin k) := D.biUnion (P.counterexample.good.gamma q);
    let baseExtraMissing : Finset (Fin k) := (TreeSequenceVertexSet P.replacementBase.core \
        TreeSequenceVertexSet Tn).biUnion fun (v : V) ↦ MissingColors G P.coloring v; alpha ∈
        MissingColors G P.coloring (T.vertex (Fin.last T.length)) ∧ alpha ∈ TreeMissingColors
        P.coloring B ∧ (alpha ∉ Gamma ∪ baseExtraMissing ∨
    ∃ eta ∈ D, alpha ∈ P.counterexample.good.gamma q eta ∧ (↑(HierarchyFirstMissingPosition
        P.coloring T eta) : ℕ) ≤ B.length)

private theorem helper_branch_237 :
    open scoped Classical in
    ∀ (k : ℕ) (M F D U W N : Finset (Fin k)) (g : Fin k → Finset (Fin k)), W ⊆ U ∪ N → N.card ≤ (1
        : ℕ) →
    let free : Finset (Fin k) := ((M \ F) \ U) \ (D.biUnion g ∪ D); (5 : ℕ) ≤ free.card →
    ∃ beta ∈ M, beta ∉ D ∧ beta ∉ W ∧ (beta ∉ D.biUnion g ∪ F ∨
    ∃ eta ∈ D, beta ∈ g eta ∧ eta ∈ M) := by
  classical
  intro k M F D U W N g hstep hncard free hlarge
  have hnon : (free \ N).Nonempty := by
    apply Finset.card_pos.mp
    have hc := Finset.card_le_card_sdiff_add_card (s := free) (t := N)
    omega
  obtain ⟨beta, hbeta⟩ := hnon
  obtain ⟨hbFree, hbFresh⟩ := Finset.mem_sdiff.mp hbeta
  obtain ⟨hbAvail, hbGD⟩ := Finset.mem_sdiff.mp hbFree
  obtain ⟨hbME, hbUsed⟩ := Finset.mem_sdiff.mp hbAvail
  obtain ⟨hbMissing, hbExtra⟩ := Finset.mem_sdiff.mp hbME
  refine ⟨beta, hbMissing, ?_, ?_, Or.inl ?_⟩
  · exact fun hc => hbGD (Finset.mem_union_right _ hc)
  · intro hc
    rcases Finset.mem_union.mp (hstep hc) with hc | hc
    · exact hbUsed hc
    · exact hbFresh hc
  · intro hc
    rcases Finset.mem_union.mp hc with hc | hc
    · exact hbGD (Finset.mem_union_left _ hc)
    · exact hbExtra hc

private theorem helper_branch_256 :
    open scoped Classical in
    ∀ (k : ℕ) (M F D U W N : Finset (Fin k)) (g : Fin k → Finset (Fin k)), W ⊆ U ∪ N → N.card ≤ (1
        : ℕ) → (
    ∀ eta ∈ D, g eta ⊆ M) → (
    ∀ eta ∈ D, (g eta).card = (2 : ℕ)) → (
    ∀ eta ∈ D,
    ∀ theta ∈ D, eta ≠ theta → Disjoint (g eta) (g theta)) → Disjoint (D.biUnion g) D → ((((M \ F)
        \ U) \ (D.biUnion g ∪ D)).card ≤ (4 : ℕ) →
    ∃ (eta : Fin (7 : ℕ) → Fin k), Function.Injective eta ∧
    ∀ (h : Fin (7 : ℕ)), eta h ∈ D ∧ eta h ∈ M ∧ Disjoint (g (eta h) ∪ ({eta h} : Finset (Fin k)))
        U) →
    let free : Finset (Fin k) := ((M \ F) \ U) \ (D.biUnion g ∪ D); ¬(5 : ℕ) ≤ free.card →
    ∃ beta ∈ M, beta ∉ D ∧ beta ∉ W ∧ (beta ∉ D.biUnion g ∪ F ∨
    ∃ eta ∈ D, beta ∈ g eta ∧ eta ∈ M) := by
  classical
  intro k M F D U W N g hstep hncard hgM hgcard hgdis hgd hnine free hlarge
  obtain ⟨eta, hinj, heta⟩ := hnine (by change free.card ≤ 4; omega)
  let pair := fun h : Fin 7 => g (eta h) ∪ {eta h}
  have hdis : Disjoint (pair 0) (pair 1) := by
    apply Finset.disjoint_left.mpr
    intro c hc hd
    have hneq : eta 0 ≠ eta 1 := fun hh => (by decide : (0 : Fin 7) ≠ 1) (hinj hh)
    simp only [pair, Finset.mem_union, Finset.mem_singleton] at hc hd
    rcases hc with hc | hc <;> rcases hd with hd | hd
    · exact Finset.disjoint_left.mp (hgdis _ (heta 0).1 _ (heta 1).1 hneq) hc hd
    · exact Finset.disjoint_left.mp hgd
        (Finset.mem_biUnion.mpr ⟨eta 0, (heta 0).1, hc⟩) (hd.symm ▸ (heta 1).1)
    · exact Finset.disjoint_left.mp hgd
        (Finset.mem_biUnion.mpr ⟨eta 1, (heta 1).1, hd⟩) (hc.symm ▸ (heta 0).1)
    · exact hneq (hc.symm.trans hd)
  have hm : ∃ m : Fin 7, Disjoint (pair m) N := by
    by_cases h0 : Disjoint (pair 0) N
    · exact ⟨0, h0⟩
    · obtain ⟨c, hc, hcN⟩ := Finset.not_disjoint_iff.mp h0
      refine ⟨1, Finset.disjoint_left.mpr ?_⟩
      intro d hd hdN
      have he : c = d := Finset.card_le_one.mp hncard c hcN d hdN
      exact Finset.disjoint_left.mp hdis hc (he.symm ▸ hd)
  obtain ⟨m, hm⟩ := hm
  have hpairUsed : Disjoint (pair m) W := by
    apply Finset.disjoint_left.mpr
    intro c hc hu
    rcases Finset.mem_union.mp (hstep hu) with hu | hu
    · exact Finset.disjoint_left.mp (heta m).2.2 hc hu
    · exact Finset.disjoint_left.mp hm hc hu
  have hnon : (g (eta m)).Nonempty := by
    apply Finset.card_pos.mp
    rw [hgcard _ (heta m).1]
    decide
  obtain ⟨beta, hbGamma⟩ := hnon
  refine ⟨beta, hgM _ (heta m).1 hbGamma, ?_, ?_,
    Or.inr ⟨eta m, (heta m).1, hbGamma, (heta m).2.1⟩⟩
  · intro hc
    exact Finset.disjoint_left.mp hgd (Finset.mem_biUnion.mpr ⟨eta m, (heta m).1, hbGamma⟩) hc
  · intro hc
    exact Finset.disjoint_left.mp hpairUsed (Finset.mem_union_left _ hbGamma) hc

private theorem helper_branch_410.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E)
      (k : ℕ) (e0 : E) (T : TreeSequence G e0) (psi : PartialEdgeColoring E k) (c : Fin k),
    (↑(HierarchyFirstMissingPosition psi T c) : ℕ) < T.length →
    let candidates : Finset (Fin (T.length + (1 : ℕ))) :=
      ({j : Fin (T.length + (1 : ℕ)) | c ∈ MissingColors G psi (T.vertex j)} :
        Finset (Fin (T.length + (1 : ℕ))));
    ¬candidates.Nonempty →
    c ∈ MissingColors G psi (T.vertex (HierarchyFirstMissingPosition psi T c)) := by
  classical
  intro V E _ _ G k e0 T psi c hlt candidates hn
  let _ := Fintype.ofFinite V
  have hh : (HierarchyFirstMissingPosition psi T c).val = T.length := by
    unfold HierarchyFirstMissingPosition
    rw [dite_eq_right hn]
    rfl
  omega

private theorem helper_branch_454.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (T : TreeSequence G e0), (
    ∀ (psi : PartialEdgeColoring E k) (c : Fin k) (j : Fin (T.length + (1 : ℕ))), c ∈
        MissingColors G psi (T.vertex j) → HierarchyFirstMissingPosition psi T c ≤ j) → (
    ∀ (psi : PartialEdgeColoring E k) (c : Fin k), (↑(HierarchyFirstMissingPosition psi T c) : ℕ)
        < T.length → c ∈ MissingColors G psi (T.vertex (HierarchyFirstMissingPosition psi T c))) →
    ∀ (psi tau : PartialEdgeColoring E k) (c : Fin k), (
    ∀ (j : Fin (T.length + (1 : ℕ))), (↑j : ℕ) < T.length → MissingColors G tau (T.vertex j) =
        MissingColors G psi (T.vertex j)) → (↑(HierarchyFirstMissingPosition tau T c) : ℕ) ≤
        (↑(HierarchyFirstMissingPosition psi T c) : ℕ) := by
  classical
  intro V E _ _ G k e0 T firstLe firstMem psi tau c early
  let _ := Fintype.ofFinite V
  by_contra hn
  have hlt : (HierarchyFirstMissingPosition psi T c).val < T.length := by
    have := (HierarchyFirstMissingPosition tau T c).isLt
    omega
  have hm := firstMem psi c hlt
  rw [← early _ hlt] at hm
  have := firstLe tau c _ hm
  omega

private theorem helper_branch_462.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (T : TreeSequence G e0), (
    ∀ (psi : PartialEdgeColoring E k) (c : Fin k) (j : Fin (T.length + (1 : ℕ))), c ∈
        MissingColors G psi (T.vertex j) → HierarchyFirstMissingPosition psi T c ≤ j) → (
    ∀ (psi : PartialEdgeColoring E k) (c : Fin k), (↑(HierarchyFirstMissingPosition psi T c) : ℕ)
        < T.length → c ∈ MissingColors G psi (T.vertex (HierarchyFirstMissingPosition psi T c))) →
    ∀ (psi tau : PartialEdgeColoring E k) (c : Fin k), (
    ∀ (j : Fin (T.length + (1 : ℕ))), (↑j : ℕ) < T.length → MissingColors G tau (T.vertex j) =
        MissingColors G psi (T.vertex j)) → (↑(HierarchyFirstMissingPosition psi T c) : ℕ) ≤
        (↑(HierarchyFirstMissingPosition tau T c) : ℕ) := by
  classical
  intro V E _ _ G k e0 T firstLe firstMem psi tau c early
  let _ := Fintype.ofFinite V
  by_contra hn
  have hlt : (HierarchyFirstMissingPosition tau T c).val < T.length := by
    have := (HierarchyFirstMissingPosition psi T c).isLt
    omega
  have hm := firstMem tau c hlt
  rw [early _ hlt] at hm
  have := firstLe psi c _ hm
  omega

private theorem helper_lastPositive_528.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (_ : ℕ) (hlen : (4 :
        ℕ) ≤ T.length),
    let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ)) (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ) (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    );
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (_ : TreeSequence G
        e0) (_ : Fin (B.length + (1 : ℕ))),
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount; H.dividerCount ≠ (0 : ℕ) →
        HierarchyStarredStage H q = H.stage (⟨H.dividerCount,
    by
            have := GoldbergSeymour.TreeSequence.positive T
            omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ))) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx j hlen B R X jb H q hq
  unfold HierarchyStarredStage
  obtain hz | ⟨i, hi⟩ := Fin.eq_zero_or_eq_succ q
  · exact (hq (by simpa [q] using congrArg Fin.val hz)).elim
  · rw [hi]
    simp only [Fin.cases_succ]
    congr 1
    exact Fin.ext (by simpa [q] using (congrArg Fin.val hi).symm)

private theorem helper_hTnCore_537.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (R :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let n : Fin (R.corresponding.replacementETT.rounds + (1 : ℕ)) := Fin.last
        R.corresponding.replacementETT.rounds;
    let Tn : TreeSequence G e0 := R.corresponding.replacementETT.series.data.tree n.castSucc;
        TreeSequenceInitialSegment Tn R.replacementBase.core := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx R n Tn
  by_cases hpe : R.corresponding.replacementETT.series.data.kind n =
      some TashkinovExtensionKind.PE
  · exact (R.replacementBase.parallel hpe).2.2.some.leftSegment
  · rw [R.replacementBase.nonparallel hpe]
    exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩

private theorem helper_coreA_543.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (_ : ℕ), (
    ∀ {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Y → TreeSequenceInitialSegment Y Z
        → TreeSequenceInitialSegment X Z) →
    let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount); (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount) = A) →
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
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (_ : TreeSequence G
        e0) (_ : Fin (B.length + (1 : ℕ))),
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount; (
    ∀ (j : ℕ) (hj : j < H.dividerCount + (2 : ℕ)) (i : Fin (H.dividerCount + (2 : ℕ))), (↑i : ℕ) ≤
        j → TreeSequenceInitialSegment (H.stage i) (H.stage (⟨j, hj⟩ : Fin (H.dividerCount + (2 :
        ℕ))))) → (H.dividerCount ≠ (0 : ℕ) → HierarchyStarredStage H q = H.stage (⟨H.dividerCount,
    by
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) → TreeSequenceInitialSegment R.replacementBase.core A := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx j trans A starEq hlen B R X jb H q chain
      lastPositive
  rw [← starEq R]
  by_cases hq : H.dividerCount = 0
  · have he : HierarchyStarredStage H q = R.replacementBase.core := by
      simp [HierarchyStarredStage, q, hq, Fin.last]
    rw [he]
    exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
  · rw [lastPositive hq]
    exact trans H.coreInsideFirst (chain H.dividerCount (by omega) ⟨1, by omega⟩
      (by change 1 ≤ H.dividerCount; omega))

private theorem helper_stageCase_554.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (_ : ℕ) (hlen : (4 :
        ℕ) ≤ T.length),
    let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ)) (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ) (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    );
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (_ : TreeSequence G
        e0),
    ∀ a ∈ HierarchyStageMissingColors R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount),
    ∀ (_ : Fin (B.length + (1 : ℕ))),
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    let _ : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let n : Fin (R.corresponding.replacementETT.rounds + (1 : ℕ)) := Fin.last
        R.corresponding.replacementETT.rounds;
    let Tn : TreeSequence G e0 := R.corresponding.replacementETT.series.data.tree n.castSucc; (0 :
        ℕ) < H.dividerCount ∧ a ∈ TreeMissingColors R.coloring (H.stage (⟨H.dividerCount,
    by
                  have := GoldbergSeymour.TreeSequence.positive T
                  omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) ∨ H.dividerCount = (0 : ℕ) ∧ a ∈ TreeMissingColors
        R.coloring Tn := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx j hlen B R X a haStage jb H q n Tn
  have hm : a ∈ HierarchyStageMissingColors H q := haStage
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

private theorem helper_haA_574.{u_1, u_2} :
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
        R.counterexample.hierarchy.dividerCount) = A) →
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
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (_ : TreeSequence G
        e0) (a : Fin k) (_ : Fin (B.length + (1 : ℕ))),
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let n : Fin (R.corresponding.replacementETT.rounds + (1 : ℕ)) := Fin.last
        R.corresponding.replacementETT.rounds;
    let Tn : TreeSequence G e0 := R.corresponding.replacementETT.series.data.tree n.castSucc;
        (H.dividerCount ≠ (0 : ℕ) → HierarchyStarredStage H q = H.stage (⟨H.dividerCount,
    by
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) → TreeSequenceInitialSegment Tn A → (0 : ℕ) <
        H.dividerCount ∧ a ∈ TreeMissingColors R.coloring (H.stage (⟨H.dividerCount,
    by
                    have := GoldbergSeymour.TreeSequence.positive T
                    omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) ∨ H.dividerCount = (0 : ℕ) ∧ a ∈ TreeMissingColors
        R.coloring Tn → a ∈ TreeMissingColors R.coloring A := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx j A starEq hlen B R X a jb H q n Tn
      lastPositive hTnA stageCase
  rcases stageCase with ⟨hq, hm⟩ | ⟨hq, hm⟩
  · rw [← starEq R, lastPositive (by omega)]
    exact hm
  · obtain ⟨v, hv, hc⟩ := Finset.mem_biUnion.mp hm
    exact Finset.mem_biUnion.mpr ⟨v,
      TreeSequenceInitialSegmentVertexSetSubset hTnA hv, hc⟩

private theorem helper_iaLe_586.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (_ : ℕ),
    let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount); TreeSequenceInitialSegment A T →
    ∀ (hlen : (4 : ℕ) ≤ T.length),
    let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ)) (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ) (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ); (
    ∀ (psi : PartialEdgeColoring E k) (c : Fin k) (j : Fin (T.length + (1 : ℕ))), c ∈
        MissingColors G psi (T.vertex j) → HierarchyFirstMissingPosition psi T c ≤ j) →
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (_ : TreeSequence G
        e0) (a : Fin k) (_ : Fin (B.length + (1 : ℕ))), a ∈ TreeMissingColors R.coloring A →
        (↑(HierarchyFirstMissingPosition R.coloring T a) : ℕ) ≤ A.length := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx j A hAT hlen B firstLe R X a jb haA
  obtain ⟨v, hv, hc⟩ := Finset.mem_biUnion.mp haA
  obtain ⟨j, hj⟩ : ∃ j, A.vertex j = v := by simpa [TreeSequenceVertexSet] using hv
  have hcT : a ∈ MissingColors G R.coloring
      (T.vertex (Fin.castLE (Nat.succ_le_succ hAT.1) j)) := by
    rw [hAT.2.1 j, hj]; exact hc
  have hh := firstLe R.coloring a _ hcT
  change (HierarchyFirstMissingPosition R.coloring T a).val ≤ j.val at hh
  have := j.isLt
  omega

private theorem helper_hjb_641.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (_ : ℕ),
    let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount);
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
    ∀ (hBT : TreeSequenceInitialSegment B T), TreeSequenceInitialSegment A B → (
    ∀ (U : TreeSequence G e0) (j : Fin (U.length + (1 : ℕ))), U.vertex j ∈ TreeSequenceVertexSet
        U) →
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (_ : TreeSequence G
        e0) (a b : Fin k) (jb : Fin (B.length + (1 : ℕ))), b ∈ MissingColors G R.coloring
        (B.vertex jb) → (↑(HierarchyFirstMissingPosition R.coloring T a) : ℕ) ≤ A.length →
        (↑(HierarchyFirstMissingPosition R.coloring T b) : ℕ) = (↑jb : ℕ) → Fin.castLE
        (Nat.succ_le_succ hBT.1) jb = HierarchyFirstMissingPosition R.coloring T b → b ∉
        TreeMissingColors R.coloring A → A.length < (↑jb : ℕ) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx j A hlen B hBT hAB vertexMem R X a b jb hb
      iaLe ibEq jbEq hbOut
  by_contra hh
  have hjle : jb.val ≤ A.length := by omega
  let x : Fin (A.length + 1) := ⟨jb.val, by omega⟩
  have hx : Fin.castLE (Nat.succ_le_succ hAB.1) x = jb := Fin.ext rfl
  apply hbOut
  exact Finset.mem_biUnion.mpr ⟨A.vertex x, vertexMem A x, by
    rw [← hAB.2.1 x, hx]; exact hb⟩

private theorem helper_hsame_650.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (_ : ℕ),
    let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount);
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
    ∀ (hBT : TreeSequenceInitialSegment B T) (hAB : TreeSequenceInitialSegment A B) (R :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (_ : TreeSequence G
        e0) (a b : Fin k) (jb : Fin (B.length + (1 : ℕ))),
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    let n : Fin (R.corresponding.replacementETT.rounds + (1 : ℕ)) := Fin.last
        R.corresponding.replacementETT.rounds;
    let Tn : TreeSequence G e0 := R.corresponding.replacementETT.series.data.tree n.castSucc; (0 :
        ℕ) < H.dividerCount ∧ a ∈ TreeMissingColors R.coloring (H.stage (⟨H.dividerCount,
    by
                    have := GoldbergSeymour.TreeSequence.positive T
                    omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) ∨ H.dividerCount = (0 : ℕ) ∧ a ∈ TreeMissingColors
        R.coloring Tn →
    ∀ (iaLe : (↑(HierarchyFirstMissingPosition R.coloring T a) : ℕ) ≤ A.length),
    let ja : Fin (B.length + (1 : ℕ)) := (⟨(↑(HierarchyFirstMissingPosition R.coloring T a) : ℕ),
    by
          have this : A.length ≤ B.length := hAB.1; omega
    ⟩ : Fin (B.length + (1 : ℕ))); Fin.castLE (Nat.succ_le_succ hBT.1) ja =
        HierarchyFirstMissingPosition R.coloring T a → Fin.castLE (Nat.succ_le_succ hBT.1) jb =
        HierarchyFirstMissingPosition R.coloring T b → (
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
    have va : V := T.vertex (HierarchyFirstMissingPosition R.coloring T a);
    have vb : V := T.vertex (HierarchyFirstMissingPosition R.coloring T b);
    have sameComponent : Prop := TwoColorComponent G R.coloring a b (Sum.inl va) =
        TwoColorComponent G R.coloring a b (Sum.inl vb); ((0 : ℕ) < H.dividerCount ∧ (a ∈
        TreeMissingColors R.coloring Tnq ∨ Disjoint (insert a ({ b } : Finset (Fin k)) : Finset
        (Fin k)) Dnq) → sameComponent) ∧ (H.dividerCount = (0 : ℕ) ∧ (a ∈ TreeMissingColors
        R.coloring Tn ∨ Disjoint (insert a ({ b } : Finset (Fin k)) : Finset (Fin k)) Dn) →
        sameComponent) ∧ (a ∈ TreeMissingColors R.coloring A ∧ TreeColorSetClosed G R.coloring A
        ({ a } : Finset (Fin k)) → sameComponent ∧ TreeInterchangeable G A R.coloring a b)) →
        TwoColorComponent G R.coloring a b (Sum.inl (B.vertex ja)) = TwoColorComponent G
        R.coloring a b (Sum.inl (B.vertex jb)) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx j A hlen B hBT hAB R X a b jb H n Tn
      stageCase iaLe ja jaEq jbEq change
  have hh : TwoColorComponent G R.coloring a b
      (Sum.inl (T.vertex (HierarchyFirstMissingPosition R.coloring T a))) =
      TwoColorComponent G R.coloring a b
      (Sum.inl (T.vertex (HierarchyFirstMissingPosition R.coloring T b))) := by
    rcases stageCase with ⟨hq, hm⟩ | ⟨hq, hm⟩
    · exact change.1 ⟨hq, Or.inl hm⟩
    · exact change.2.1 ⟨hq, Or.inl hm⟩
  rw [← jaEq, ← jbEq, hBT.2.1 ja, hBT.2.1 jb] at hh
  exact hh

private theorem helper_baseStable_716.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (_ : ℕ) (R :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (a b : Fin k),
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let n : Fin (R.corresponding.replacementETT.rounds + (1 : ℕ)) := Fin.last
        R.corresponding.replacementETT.rounds;
    let Tn : TreeSequence G e0 := R.corresponding.replacementETT.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors R.corresponding.replacementETT.series.data n;
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G R.coloring a b (Sum.inl
        (T.vertex (Fin.last T.length))); HierarchyWeaklyStable H q sigma → if
        R.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.PE then
        CombinedStableColoring Tn R.replacementBase.closure Dn R.coloring sigma else
        StableColoring Tn Dn R.coloring sigma := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx j R a b H q n Tn Dn sigma hweak
  have extract (j : Fin (H.dividerCount + 1)) : HierarchyWeaklyStable H j sigma →
      (if R.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.PE then
        CombinedStableColoring Tn R.replacementBase.closure Dn R.coloring sigma
      else StableColoring Tn Dn R.coloring sigma) :=
    Fin.cases (fun h => h) (fun _ h => h.1) j
  exact extract q hweak

private theorem helper_fixedA_730.{u_1, u_2} :
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
        R.counterexample.hierarchy.dividerCount) = A) →
    ∀ (hlen : (4 : ℕ) ≤ T.length),
    let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ)) (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ) (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ); TreeSequenceInitialSegment B T → TreeSequenceInitialSegment A B →
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (_ : TreeSequence G
        e0) (a b : Fin k) (_ : Fin (B.length + (1 : ℕ))),
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
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)));
    have Tn : TreeSequence G e0 := R.corresponding.replacementETT.series.data.tree n.castSucc;
    have Dn : Finset (Fin k) := TashkinovStoredColors R.corresponding.replacementETT.series.data
        n;
    have Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q;
    have va : V := T.vertex (HierarchyFirstMissingPosition R.coloring T a);
    have vb : V := T.vertex (HierarchyFirstMissingPosition R.coloring T b);
    have sameComponent : Prop := TwoColorComponent G R.coloring a b (Sum.inl va) =
        TwoColorComponent G R.coloring a b (Sum.inl vb); ((0 : ℕ) < H.dividerCount ∧ (a ∈
        TreeMissingColors R.coloring Tnq ∨ Disjoint (insert a ({ b } : Finset (Fin k)) : Finset
        (Fin k)) Dnq) → sameComponent) ∧ (H.dividerCount = (0 : ℕ) ∧ (a ∈ TreeMissingColors
        R.coloring Tn ∨ Disjoint (insert a ({ b } : Finset (Fin k)) : Finset (Fin k)) Dn) →
        sameComponent) ∧ (a ∈ TreeMissingColors R.coloring A ∧ TreeColorSetClosed G R.coloring A
        ({ a } : Finset (Fin k)) → sameComponent ∧ TreeInterchangeable G A R.coloring a b)) →
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G R.coloring a b (Sum.inl
        (T.vertex (Fin.last T.length))); IsOneEdgeUncolored sigma e0 → HierarchyWeaklyStable H q
        sigma → (if R.corresponding.replacementETT.series.data.kind n = some
        TashkinovExtensionKind.PE then CombinedStableColoring Tn R.replacementBase.closure Dn
        R.coloring sigma else StableColoring Tn Dn R.coloring sigma) →
    ∀ (t : Fin A.length), sigma (A.edge t) = R.coloring (A.edge t) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx j A starEq hlen B hBT hAB R X a b jb H q n
      Tn Dn iaLe change sigma hsone hweak baseStable
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

private theorem helper_fixedPrefix_750.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C),
    let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount);
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (X : TreeSequence G
        e0) (a b : Fin k), (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → R.coloring (T.edge t) ≠ some
        a) → (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → R.coloring (T.edge t) = some
        b → TreeIncidentEdge (R.corresponding.replacementETT.series.data.tree (Fin.last
        R.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧ b ∈ TashkinovStoredColors
        R.corresponding.replacementETT.series.data (Fin.last
        R.corresponding.replacementETT.rounds)) →
    let n : Fin (R.corresponding.replacementETT.rounds + (1 : ℕ)) := Fin.last
        R.corresponding.replacementETT.rounds;
    let Tn : TreeSequence G e0 := R.corresponding.replacementETT.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors R.corresponding.replacementETT.series.data n;
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G R.coloring a b (Sum.inl
        (T.vertex (Fin.last T.length))); StableColoring Tn Dn R.coloring sigma →
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → sigma (T.edge t) =
        R.coloring (T.edge t) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx A R X a b haUnused hbException n Tn Dn
      sigma stable t hlo hhi
  by_cases hbcol : R.coloring (T.edge t) = some b
  · obtain ⟨hi, hc⟩ := hbException t hlo hhi hbcol
    exact stable.1 _ hi ⟨b, Finset.mem_union_right _ hc, hbcol⟩
  · have haNo := haUnused t hlo hhi
    simp [sigma, TwoColorComponentSwap, haNo, hbcol]

private theorem helper_prefixFixed_762.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (_ : ℕ),
    let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount);
    ∀ (hlen : (4 : ℕ) ≤ T.length),
    let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ)) (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ) (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ); TreeSequenceInitialSegment B T → TreeSequenceInitialSegment A B →
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (X : TreeSequence G
        e0), TreeSequenceInitialSegment A X →
    ∀ (a b : Fin k) (_ : Fin (B.length + (1 : ℕ))), (↑(HierarchyFirstMissingPosition R.coloring T
        a) : ℕ) ≤ A.length → (
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
    have va : V := T.vertex (HierarchyFirstMissingPosition R.coloring T a);
    have vb : V := T.vertex (HierarchyFirstMissingPosition R.coloring T b);
    have sameComponent : Prop := TwoColorComponent G R.coloring a b (Sum.inl va) =
        TwoColorComponent G R.coloring a b (Sum.inl vb); ((0 : ℕ) < H.dividerCount ∧ (a ∈
        TreeMissingColors R.coloring Tnq ∨ Disjoint (insert a ({ b } : Finset (Fin k)) : Finset
        (Fin k)) Dnq) → sameComponent) ∧ (H.dividerCount = (0 : ℕ) ∧ (a ∈ TreeMissingColors
        R.coloring Tn ∨ Disjoint (insert a ({ b } : Finset (Fin k)) : Finset (Fin k)) Dn) →
        sameComponent) ∧ (a ∈ TreeMissingColors R.coloring A ∧ TreeColorSetClosed G R.coloring A
        ({ a } : Finset (Fin k)) → sameComponent ∧ TreeInterchangeable G A R.coloring a b)) →
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G R.coloring a b (Sum.inl
        (T.vertex (Fin.last T.length))); (
    ∀ (t : Fin A.length), sigma (A.edge t) = R.coloring (A.edge t)) → (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → sigma (T.edge t) =
        R.coloring (T.edge t)) → TreeSequenceInitialSegment X T →
    ∀ (t : Fin X.length), sigma (X.edge t) = R.coloring (X.edge t) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx j A hlen B hBT hAB R X hAX a b jb iaLe
      change sigma fixedA fixedPrefix hXT t
  by_cases hlow : t.val < A.length
  · let j : Fin A.length := ⟨t.val, hlow⟩
    have he : Fin.castLE hAX.1 j = t := Fin.ext rfl
    rw [← he, hAX.2.2 j]
    exact fixedA j
  · rw [← hXT.2.2 t]
    exact fixedPrefix (Fin.castLE hXT.1 t) (by change A.length ≤ t.val; omega) t.isLt

private theorem helper_routes_771.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (_ : ℕ), (
    ∀ {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Y → TreeSequenceInitialSegment Y Z
        → TreeSequenceInitialSegment X Z) → (
    ∀ {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Z → TreeSequenceInitialSegment Y Z
        → X.length ≤ Y.length → TreeSequenceInitialSegment X Y) →
    let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount);
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
    ∀ (_ : TreeSequenceInitialSegment B T) (_ : TreeSequenceInitialSegment A B) (R :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (X : TreeSequence G
        e0), TreeSequenceInitialSegment A X →
    ∀ (hAXlt : A.length < X.length), TreeSequenceInitialSegment X B →
    ∀ (a b : Fin k) (_ : Fin (B.length + (1 : ℕ))),
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
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)));
    have Tn : TreeSequence G e0 := R.corresponding.replacementETT.series.data.tree n.castSucc;
    have Dn : Finset (Fin k) := TashkinovStoredColors R.corresponding.replacementETT.series.data
        n;
    have Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q;
    have va : V := T.vertex (HierarchyFirstMissingPosition R.coloring T a);
    have vb : V := T.vertex (HierarchyFirstMissingPosition R.coloring T b);
    have sameComponent : Prop := TwoColorComponent G R.coloring a b (Sum.inl va) =
        TwoColorComponent G R.coloring a b (Sum.inl vb); ((0 : ℕ) < H.dividerCount ∧ (a ∈
        TreeMissingColors R.coloring Tnq ∨ Disjoint (insert a ({ b } : Finset (Fin k)) : Finset
        (Fin k)) Dnq) → sameComponent) ∧ (H.dividerCount = (0 : ℕ) ∧ (a ∈ TreeMissingColors
        R.coloring Tn ∨ Disjoint (insert a ({ b } : Finset (Fin k)) : Finset (Fin k)) Dn) →
        sameComponent) ∧ (a ∈ TreeMissingColors R.coloring A ∧ TreeColorSetClosed G R.coloring A
        ({ a } : Finset (Fin k)) → sameComponent ∧ TreeInterchangeable G A R.coloring a b)) → (
    ∀ x ∈ TreeSequenceVertexSet B, MissingColors G (TwoColorComponentSwap G R.coloring a b
        (Sum.inl (T.vertex (Fin.last T.length)))) x = MissingColors G R.coloring x) →
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G R.coloring a b (Sum.inl
        (T.vertex (Fin.last T.length))); TreeSequenceInitialSegment X T →
    let XM : TreeSequence G e0 := TreeSequencePrefix X (X.length - (1 : ℕ)) (
    have this : (1 : ℕ) ≤ A.length := A.positive; Decidable.byContradiction fun (a_1 : ¬(1 : ℕ) ≤
        X.length - (1 : ℕ)) ↦
    by omega
    ) (
    by
          have := GoldbergSeymour.TreeSequence.positive X
          omega
    ); TreeSequenceInitialSegment XM X → (
    ∀ (t : Fin X.length), Tn.length ≤ (↑t : ℕ) → sigma (X.edge t) = R.coloring (X.edge t)) →
        (R.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence sigma Tn X ∨
        (R.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.SE ∨
        R.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.RE) ∧
    ∃ (f : E) (seed : TreeSequence G e0),
        R.corresponding.replacementETT.series.data.connectingEdges n = ({ f } : Finset E) ∧
        TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence sigma seed X) ∧
        TashkinovAugmentationSequence R.coloring X T := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx j trans common A hlen B hBT hAB R X hAX
      hAXlt hXB a b jb n Tn hTnA iaLe change hmissing sigma hXT XM hXMX prefixFixed
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
      (fun t ht => prefixFixed t
          (by have hl := hseed.1; change seed.length = Tn.length + 1 at hl; omega))
      (fun v hv => hmissing v (TreeSequenceInitialSegmentVertexSetSubset
        (trans hXMX hXB) hv))

private theorem helper_hsplit_801.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (_ : ℕ),
    let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount);
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
    ∀ (hBT : TreeSequenceInitialSegment B T) (hAB : TreeSequenceInitialSegment A B), (
    ∀ (U : TreeSequence G e0) (j : Fin (U.length + (1 : ℕ))), U.vertex j ∈ TreeSequenceVertexSet
        U) →
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (X : TreeSequence G
        e0), A.length < X.length → TreeSequenceInitialSegment X B →
    ∀ (a b : Fin k) (jb : Fin (B.length + (1 : ℕ))), (↑jb : ℕ) ≤ X.length → b ∈ MissingColors G
        R.coloring (B.vertex jb) →
    ∀ (iaLe : (↑(HierarchyFirstMissingPosition R.coloring T a) : ℕ) ≤ A.length),
    let ja : Fin (B.length + (1 : ℕ)) := (⟨(↑(HierarchyFirstMissingPosition R.coloring T a) : ℕ),
    by
          have this : A.length ≤ B.length := hAB.1; omega
    ⟩ : Fin (B.length + (1 : ℕ))); Fin.castLE (Nat.succ_le_succ hBT.1) ja =
        HierarchyFirstMissingPosition R.coloring T a → a ∈ MissingColors G R.coloring (B.vertex
        ja) → (
    ∀ x ∈ TreeSequenceVertexSet B, MissingColors G (TwoColorComponentSwap G R.coloring a b
        (Sum.inl (T.vertex (Fin.last T.length)))) x = MissingColors G R.coloring x) →
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G R.coloring a b (Sum.inl
        (T.vertex (Fin.last T.length))); a ∈ TreeMissingColors sigma X ∧ b ∈ TreeMissingColors
        sigma X := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx j A hlen B hBT hAB vertexMem R X hAXlt hXB
      a b jb hjbX hb iaLe ja jaEq haFirstB hmissing sigma
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

private theorem helper_hnotElementary_829.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (_ : ℕ), (
    ∀ {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Y → TreeSequenceInitialSegment Y Z
        → TreeSequenceInitialSegment X Z) →
    let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount);
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
    ∀ (hBT : TreeSequenceInitialSegment B T) (hAB : TreeSequenceInitialSegment A B), (
    ∀ (U : TreeSequence G e0) (j : Fin (U.length + (1 : ℕ))), U.vertex j ∈ TreeSequenceVertexSet
        U) →
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (_ : TreeSequence G
        e0) (a b : Fin k) (jb : Fin (B.length + (1 : ℕ))), b ∈ MissingColors G R.coloring
        (B.vertex jb) → a ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)) ∨ b ∈
        MissingColors G R.coloring (T.vertex (Fin.last T.length)) →
    ∀ (iaLe : (↑(HierarchyFirstMissingPosition R.coloring T a) : ℕ) ≤ A.length),
        (↑(HierarchyFirstMissingPosition R.coloring T b) : ℕ) = (↑jb : ℕ) →
    let ja : Fin (B.length + (1 : ℕ)) := (⟨(↑(HierarchyFirstMissingPosition R.coloring T a) : ℕ),
    by
          have this : A.length ≤ B.length := hAB.1; omega
    ⟩ : Fin (B.length + (1 : ℕ))); Fin.castLE (Nat.succ_le_succ hBT.1) jb =
        HierarchyFirstMissingPosition R.coloring T b → a ∈ MissingColors G R.coloring (B.vertex
        ja) → (
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
    have va : V := T.vertex (HierarchyFirstMissingPosition R.coloring T a);
    have vb : V := T.vertex (HierarchyFirstMissingPosition R.coloring T b);
    have sameComponent : Prop := TwoColorComponent G R.coloring a b (Sum.inl va) =
        TwoColorComponent G R.coloring a b (Sum.inl vb); ((0 : ℕ) < H.dividerCount ∧ (a ∈
        TreeMissingColors R.coloring Tnq ∨ Disjoint (insert a ({ b } : Finset (Fin k)) : Finset
        (Fin k)) Dnq) → sameComponent) ∧ (H.dividerCount = (0 : ℕ) ∧ (a ∈ TreeMissingColors
        R.coloring Tn ∨ Disjoint (insert a ({ b } : Finset (Fin k)) : Finset (Fin k)) Dn) →
        sameComponent) ∧ (a ∈ TreeMissingColors R.coloring A ∧ TreeColorSetClosed G R.coloring A
        ({ a } : Finset (Fin k)) → sameComponent ∧ TreeInterchangeable G A R.coloring a b)) → (
    ∀ x ∈ TreeSequenceVertexSet B, MissingColors G (TwoColorComponentSwap G R.coloring a b
        (Sum.inl (T.vertex (Fin.last T.length)))) x = MissingColors G R.coloring x) →
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G R.coloring a b (Sum.inl
        (T.vertex (Fin.last T.length))); (a ∈ MissingColors G R.coloring (T.vertex (Fin.last
        T.length)) → b ∈ MissingColors G sigma (T.vertex (Fin.last T.length))) → (b ∈
        MissingColors G R.coloring (T.vertex (Fin.last T.length)) → a ∈ MissingColors G sigma
        (T.vertex (Fin.last T.length))) → ¬ColoredVertexSetElementary G sigma
        (TreeSequenceVertexSet T) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx j trans A hlen B hBT hAB vertexMem R X a b
      jb hb hw iaLe ibEq ja jbEq haFirstB change hmissing sigma hterminalA hterminalB he
  rcases hw with hw | hw
  · have hbNew : b ∈ MissingColors G sigma (B.vertex jb) := by
      rw [hmissing _ (vertexMem B jb)]; exact hb
    exact Finset.disjoint_left.mp (he
      (TreeSequenceInitialSegmentVertexSetSubset hBT (vertexMem B jb))
      (vertexMem T (Fin.last T.length)) (by
        intro hh
        have hh := T.vertex_injective ((hBT.2.1 jb).trans hh)
        have hh := congrArg Fin.val hh
        change jb.val = T.length at hh
        have := jb.isLt
        have hblen : B.length = T.length - 1 := rfl
        omega))
      hbNew (hterminalA hw)
  · have haNew : a ∈ MissingColors G sigma (B.vertex ja) := by
      rw [hmissing _ (vertexMem B ja)]; exact haFirstB
    exact Finset.disjoint_left.mp (he
      (TreeSequenceInitialSegmentVertexSetSubset hBT (vertexMem B ja))
      (vertexMem T (Fin.last T.length)) (by
        intro hh
        have hh := T.vertex_injective ((hBT.2.1 ja).trans hh)
        have hh := congrArg Fin.val hh
        change ja.val = T.length at hh
        have hja : ja.val ≤ A.length := iaLe
        have hab := hAB.1
        have hblen : B.length = T.length - 1 := rfl
        omega))
      haNew (hterminalB hw)

private theorem helper_hAn_999.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C),
    let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount); (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount) = A) →
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        R.counterexample.hierarchy.dividerCount = (0 : ℕ) → R.replacementBase.core =
        R.corresponding.replacementETT.series.data.tree (Fin.last
        R.corresponding.replacementETT.rounds).castSucc → A =
        R.corresponding.replacementETT.series.data.tree (Fin.last
        R.corresponding.replacementETT.rounds).castSucc := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx A starEq R hzero hcore
  rw [← starEq R]
  have hs : HierarchyStarredStage R.counterexample.hierarchy
      (Fin.last R.counterexample.hierarchy.dividerCount) = R.replacementBase.core := by
    simp [HierarchyStarredStage, hzero, Fin.last]
  exact hs.trans hcore

private theorem helper_branch_1043.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C), (
    ∀ {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Y → TreeSequenceInitialSegment Y Z
        → TreeSequenceInitialSegment X Z) →
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy; (
    ∀ (j : ℕ) (hj : j < H.dividerCount + (2 : ℕ)) (i : Fin (H.dividerCount + (2 : ℕ))), (↑i : ℕ) ≤
        j → TreeSequenceInitialSegment (H.stage i) (H.stage (⟨j, hj⟩ : Fin (H.dividerCount + (2 :
        ℕ))))) → ¬H.dividerCount = (0 : ℕ) → TreeSequenceInitialSegment R.replacementBase.core
        (HierarchyStarredStage R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount)) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx trans R H chain hq
  have he : HierarchyStarredStage H (Fin.last H.dividerCount) =
      H.stage ⟨H.dividerCount, by omega⟩ := by
    unfold HierarchyStarredStage
    obtain hz | ⟨i, hi⟩ := Fin.eq_zero_or_eq_succ (Fin.last H.dividerCount)
    · exact (hq (by simpa using congrArg Fin.val hz)).elim
    · rw [hi]
      simp only [Fin.cases_succ]
      congr 1
      exact Fin.ext (by simpa using (congrArg Fin.val hi).symm)
  rw [he]
  exact trans H.coreInsideFirst (chain H.dividerCount (by omega) ⟨1, by omega⟩
    (by change 1 ≤ H.dividerCount; omega))

private theorem helper_ha_1142.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (hnonempty :
        (HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx).Nonempty) (j :
        ℕ) (_ : (2 : ℕ) ≤ j) (hpathUpper : j < HierarchyFullTailLength C),
    let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount);
    ∀ (htail : (3 : ℕ) ≤ T.length - A.length) (hlen : (4 : ℕ) ≤ T.length),
    let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ)) (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ) (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ); TreeSequenceInitialSegment B T → (
    ∀ (r : ℕ), TreeSequenceInitialSegment (HierarchyFullTailPrefix C r) T) →
    let I : Finset ℕ := HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx;
    let i : ℕ := I.max' hnonempty;
    ∀ (hiUpper : i < j) (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∀ alpha ∈ MissingColors G P.coloring ((HierarchyFullTailPrefix C i).vertex (Fin.last
        (HierarchyFullTailPrefix C i).length)),
    ∀ (hSlen : (HierarchyFullTailPrefix C i).length = A.length + i),
    let ja : Fin (B.length + (1 : ℕ)) := (⟨A.length + i,
    have hb : B.length = T.length - (1 : ℕ) := rfl; id (fun (hpathUpper : j < T.length - A.length)
        ↦ Decidable.byContradiction fun (a : ¬A.length + i < B.length + (1 : ℕ)) ↦
    by
                omega
    ) hpathUpper⟩ : Fin (B.length + (1 : ℕ))); alpha ∈ MissingColors G P.coloring (B.vertex ja)
  := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hnonempty j hpathLower hpathUpper A htail
      hlen B hBT prefixT I i hiUpper P alpha haPrefix hSlen ja
  have he : (HierarchyFullTailPrefix C i).vertex (Fin.last (HierarchyFullTailPrefix C i).length) =
      B.vertex ja := by
    rw [← (prefixT i).2.1, ← hBT.2.1 ja]
    apply congrArg T.vertex
    apply Fin.ext
    exact hSlen
  rw [← he]
  exact haPrefix

private theorem helper_branch_1158.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (hnonempty :
        (HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx).Nonempty) (j :
        ℕ) (_ : (2 : ℕ) ≤ j) (hpathUpper : j < HierarchyFullTailLength C),
    let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount);
    ∀ (htail : (3 : ℕ) ≤ T.length - A.length) (hlen : (4 : ℕ) ≤ T.length),
    let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ)) (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ) (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ); (
    ∀ (U : TreeSequence G e0) (j : Fin (U.length + (1 : ℕ))), U.vertex j ∈ TreeSequenceVertexSet
        U) →
    let Extra : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx → Finset (Fin
        k) := fun (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) ↦
        (TreeSequenceVertexSet R.replacementBase.core \ TreeSequenceVertexSet
        (R.corresponding.replacementETT.series.data.tree (Fin.last
        R.corresponding.replacementETT.rounds).castSucc)).biUnion fun (v : V) ↦ MissingColors G
        R.coloring v;
    let Gamma : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx → Finset (Fin
        k) := fun (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) ↦
        (HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount)).biUnion (R.counterexample.good.gamma (Fin.last
        R.counterexample.hierarchy.dividerCount));
    let Y : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ)); Y.length = A.length + (j
        - (2 : ℕ)) → TreeSequenceInitialSegment Y B →
    let I : Finset ℕ := HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx;
    let i : ℕ := I.max' hnonempty;
    ∀ (hiUpper : i < j) (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∀ alpha ∈ MissingColors G P.coloring (T.vertex (Fin.last T.length)),
    ∀ (hSlen : (HierarchyFullTailPrefix C i).length = A.length + i),
    let ja : Fin (B.length + (1 : ℕ)) := (⟨A.length + i,
    have hb : B.length = T.length - (1 : ℕ) := rfl; id (fun (hpathUpper : j < T.length - A.length)
        ↦ Decidable.byContradiction fun (a : ¬A.length + i < B.length + (1 : ℕ)) ↦
    by
                omega
    ) hpathUpper⟩ : Fin (B.length + (1 : ℕ))); alpha ∈ MissingColors G P.coloring (B.vertex ja) →
        alpha ∉ Gamma P ∪ Extra P → i ≤ j - (2 : ℕ) →
    ∃ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha : Fin k),
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
        P.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let n : Fin (P.corresponding.replacementETT.rounds + (1 : ℕ)) := Fin.last
        P.corresponding.replacementETT.rounds;
    let Tn : TreeSequence G e0 := P.corresponding.replacementETT.series.data.tree n.castSucc;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ));
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let Gamma : Finset (Fin k) := D.biUnion (P.counterexample.good.gamma q);
    let baseExtraMissing : Finset (Fin k) := (TreeSequenceVertexSet P.replacementBase.core \
        TreeSequenceVertexSet Tn).biUnion fun (v : V) ↦ MissingColors G P.coloring v; alpha ∈
        MissingColors G P.coloring (T.vertex (Fin.last T.length)) ∧ alpha ∈ TreeMissingColors
        P.coloring B ∧ (alpha ∉ Gamma ∪ baseExtraMissing ∨
    ∃ eta ∈ D, alpha ∈ P.counterexample.good.gamma q eta ∧ (↑(HierarchyFirstMissingPosition
        P.coloring T eta) : ℕ) ≤ B.length) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hnonempty j hpathLower hpathUpper A htail
      hlen B vertexMem Extra Gamma Y hYlen hYB I i hiUpper P alpha haTerminal hSlen ja ha haGood
      hsmall
  refine ⟨P, alpha, haTerminal, ?_, Or.inl haGood⟩
  let x : Fin (Y.length + 1) := ⟨ja.val, by dsimp [ja]; omega⟩
  have hx : Fin.castLE (Nat.succ_le_succ hYB.1) x = ja := Fin.ext rfl
  exact Finset.mem_biUnion.mpr ⟨Y.vertex x, vertexMem Y x, by
    rw [← hYB.2.1 x, hx]; exact ha⟩

private theorem helper_choice_1225.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (hnonempty :
        (HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx).Nonempty) (j :
        ℕ) (hpathLower : (2 : ℕ) ≤ j) (hpathUpper : j < HierarchyFullTailLength C), (
    ∀ (M F D U W N : Finset (Fin k)) (g : Fin k → Finset (Fin k)), W ⊆ U ∪ N → N.card ≤ (1 : ℕ) →
        (
    ∀ eta ∈ D, g eta ⊆ M) → (
    ∀ eta ∈ D, (g eta).card = (2 : ℕ)) → (
    ∀ eta ∈ D,
    ∀ theta ∈ D, eta ≠ theta → Disjoint (g eta) (g theta)) → Disjoint (D.biUnion g) D → ((((M \ F)
        \ U) \ (D.biUnion g ∪ D)).card ≤ (4 : ℕ) →
    ∃ (eta : Fin (7 : ℕ) → Fin k), Function.Injective eta ∧
    ∀ (h : Fin (7 : ℕ)), eta h ∈ D ∧ eta h ∈ M ∧ Disjoint (g (eta h) ∪ ({eta h} : Finset (Fin k)))
        U) →
    ∃ beta ∈ M, beta ∉ D ∧ beta ∉ W ∧ (beta ∉ D.biUnion g ∪ F ∨
    ∃ eta ∈ D, beta ∈ g eta ∧ eta ∈ M)) → (
    ∀ {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Y → TreeSequenceInitialSegment Y Z
        → TreeSequenceInitialSegment X Z) →
    let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount);
    ∀ (htail : (3 : ℕ) ≤ T.length - A.length) (hlen : (4 : ℕ) ≤ T.length),
    let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ)) (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ) (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    );
    ∀ (hBT : TreeSequenceInitialSegment B T), (
    ∀ (psi : PartialEdgeColoring E k) (c : Fin k) (j : Fin (T.length + (1 : ℕ))), c ∈
        MissingColors G psi (T.vertex j) → HierarchyFirstMissingPosition psi T c ≤ j) →
    let Extra : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx → Finset (Fin
        k) := fun (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) ↦
        (TreeSequenceVertexSet R.replacementBase.core \ TreeSequenceVertexSet
        (R.corresponding.replacementETT.series.data.tree (Fin.last
        R.corresponding.replacementETT.rounds).castSucc)).biUnion fun (v : V) ↦ MissingColors G
        R.coloring v;
    let Gamma : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx → Finset (Fin
        k) := fun (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) ↦
        (HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount)).biUnion (R.counterexample.good.gamma (Fin.last
        R.counterexample.hierarchy.dividerCount)); (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), Gamma R ⊆
        TreeMissingColors R.coloring A) →
    let Y : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ));
    ∀ (hYlen : Y.length = A.length + (j - (2 : ℕ))), TreeSequenceInitialSegment Y T →
        TreeSequenceInitialSegment A Y →
    let I : Finset ℕ := HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx;
    let i : ℕ := I.max' hnonempty;
    ∀ (hiUpper : i < j) (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
        (hSlen : (HierarchyFullTailPrefix C i).length = A.length + i),
    let ja : Fin (B.length + (1 : ℕ)) := (⟨A.length + i,
    have hb : B.length = T.length - (1 : ℕ) := rfl; id (fun (hpathUpper : j < T.length - A.length)
        ↦ Decidable.byContradiction fun (a : ¬A.length + i < B.length + (1 : ℕ)) ↦
    by
                omega
    ) hpathUpper⟩ : Fin (B.length + (1 : ℕ)));
    ∀ (hiEq : i = j - (1 : ℕ)),
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ));
    ∀ (hXlen : X.length = A.length + (j - (1 : ℕ))) (hXB : TreeSequenceInitialSegment X B) (hYXlen
        : X.length = Y.length + (1 : ℕ)) (hjaX : (↑ja : ℕ) = X.length),
    let D : Finset (Fin k) := HierarchyStoredColorsAt P.counterexample.hierarchy (Fin.last
        P.counterexample.hierarchy.dividerCount);
    let used : ℕ → Finset (Fin k) := fun (r : ℕ) ↦ ({c : Fin k |
    ∃ (t : Fin T.length), A.length ≤ (↑t : ℕ) ∧ (↑t : ℕ) < A.length + r ∧ P.coloring (T.edge t) =
        some c} : Finset (Fin k));
    let tnew : Fin T.length := (⟨Y.length,
    by
          have _ : X.length ≤ B.length := hXB.1
          have this : B.length ≤ T.length := hBT.1
          omega
    ⟩ : Fin T.length);
    let fresh : Finset (Fin k) := ({c : Fin k | P.coloring (T.edge tnew) = some c} : Finset (Fin
        k)); fresh.card ≤ (1 : ℕ) → used (j - (1 : ℕ)) ⊆ used (j - (2 : ℕ)) ∪ fresh → (2 : ℕ) *
        P.corresponding.replacementETT.rounds + (11 : ℕ) ≤ ((TreeMissingColors P.coloring Y \
        Extra P) \ used (j - (2 : ℕ))).card ∧ ((((TreeMissingColors P.coloring Y \ Extra P) \ used
        (j - (2 : ℕ))) \ (Gamma P ∪ D)).card ≤ (4 : ℕ) →
    ∃ (eta : Fin (7 : ℕ) → Fin k), Function.Injective eta ∧
    ∀ (h : Fin (7 : ℕ)), eta h ∈ D ∧ eta h ∈ TreeMissingColors P.coloring Y ∧ Disjoint
        (P.counterexample.good.gamma (Fin.last P.counterexample.hierarchy.dividerCount) (eta h) ∪
        ({eta h} : Finset (Fin k))) (used (j - (2 : ℕ)))) →
    ∃ beta ∈ TreeMissingColors P.coloring Y, beta ∉ D ∧ beta ∉ used (j - (1 : ℕ)) ∧ (beta ∉ Gamma
        P ∪ Extra P ∨
    ∃ eta ∈ D, beta ∈ P.counterexample.good.gamma (Fin.last
        P.counterexample.hierarchy.dividerCount) eta ∧ (↑(HierarchyFirstMissingPosition P.coloring
        T eta) : ℕ) ≤ Y.length) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hnonempty j hpathLower hpathUpper
      finiteChoice trans A htail hlen B hBT firstLe Extra Gamma gammaSub Y hYlen hYT hAY I i
      hiUpper P hSlen ja hiEq X hXlen hXB hYXlen hjaX D used tnew fresh freshCard usedStep nineY
  clear * - P Y D used fresh usedStep freshCard finiteChoice Extra Gamma gammaSub hAY hYT firstLe
      nineY
  obtain ⟨beta, hbM, hbD, hbW, hc⟩ := finiteChoice
    (TreeMissingColors P.coloring Y) (Extra P) D (used (j - 2)) (used (j - 1)) fresh
    (P.counterexample.good.gamma (Fin.last P.counterexample.hierarchy.dividerCount))
    usedStep freshCard (fun eta heta c hc => by
      obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp (gammaSub P (Finset.mem_biUnion.mpr ⟨eta,
          heta, hc⟩))
      exact Finset.mem_biUnion.mpr ⟨v, TreeSequenceInitialSegmentVertexSetSubset hAY hv, hcv⟩)
    (P.counterexample.good.twoColors _) (fun eta heta theta htheta =>
      P.counterexample.good.disjointPairs _ eta theta heta htheta)
    (GoodHierarchyReservedDisjoint P.counterexample.good _).2 nineY.2
  refine ⟨beta, hbM, hbD, hbW, ?_⟩
  rcases hc with hc | ⟨eta, heta, hbGamma, heM⟩
  · exact Or.inl hc
  · right
    refine ⟨eta, heta, hbGamma, ?_⟩
    obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp heM
    obtain ⟨z, hz⟩ : ∃ z, Y.vertex z = v := by simpa [TreeSequenceVertexSet] using hv
    have hfirst := firstLe P.coloring eta (Fin.castLE (Nat.succ_le_succ hYT.1) z)
      (by rw [hYT.2.1 z, hz]; exact hcv)
    have := z.isLt
    change (HierarchyFirstMissingPosition P.coloring T eta).val ≤ z.val at hfirst
    exact hfirst.trans (Nat.le_of_lt_succ z.isLt)

private theorem helper_habNe_1264.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (hnonempty :
        (HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx).Nonempty) (j :
        ℕ) (_ : (2 : ℕ) ≤ j) (hpathUpper : j < HierarchyFullTailLength C),
    let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount);
    ∀ (htail : (3 : ℕ) ≤ T.length - A.length) (hlen : (4 : ℕ) ≤ T.length),
    let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ)) (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ) (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ); (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        ColoredVertexSetElementary G R.coloring (TreeSequenceVertexSet B)) → (
    ∀ (U : TreeSequence G e0) (j : Fin (U.length + (1 : ℕ))), U.vertex j ∈ TreeSequenceVertexSet
        U) →
    let Y : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ));
    ∀ (hYB : TreeSequenceInitialSegment Y B),
    let I : Finset ℕ := HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx;
    let i : ℕ := I.max' hnonempty;
    ∀ (hiUpper : i < j) (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
        (alpha : Fin k) (hSlen : (HierarchyFullTailPrefix C i).length = A.length + i),
    let ja : Fin (B.length + (1 : ℕ)) := (⟨A.length + i,
    have hb : B.length = T.length - (1 : ℕ) := rfl; id (fun (hpathUpper : j < T.length - A.length)
        ↦ Decidable.byContradiction fun (a : ¬A.length + i < B.length + (1 : ℕ)) ↦
    by
                omega
    ) hpathUpper⟩ : Fin (B.length + (1 : ℕ))); alpha ∈ MissingColors G P.coloring (B.vertex ja) →
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ)); X.length = Y.length + (1
        : ℕ) → (↑ja : ℕ) = X.length →
    ∀ (beta : Fin k) (yb : Fin (Y.length + (1 : ℕ))),
    let jb : Fin (B.length + (1 : ℕ)) := Fin.castLE (Nat.succ_le_succ hYB.1) yb; beta ∈
        MissingColors G P.coloring (B.vertex jb) → (↑jb : ℕ) ≤ Y.length → alpha ≠ beta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hnonempty j hpathLower hpathUpper A htail
      hlen B elementary vertexMem Y hYB I i hiUpper P alpha hSlen ja ha X hYXlen hjaX beta yb jb
      hb hjbY he
  have hneq : B.vertex ja ≠ B.vertex jb := by
    intro hh
    have hh := congrArg Fin.val (B.vertex_injective hh)
    clear * - hh hjaX hjbY hYXlen
    omega
  exact Finset.disjoint_left.mp (elementary P (vertexMem B ja) (vertexMem B jb) hneq) ha (he.symm
      ▸ hb)

private theorem helper_branch_1298.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (j : ℕ) (hlen : (4 :
        ℕ) ≤ T.length),
    let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ)) (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ) (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ); (
    ∀ (psi tau : PartialEdgeColoring E k), (
    ∀ v ∈ TreeSequenceVertexSet B, MissingColors G tau v = MissingColors G psi v) →
    ∀ (c : Fin k), HierarchyFirstMissingPosition tau T c = HierarchyFirstMissingPosition psi T c)
        →
    let Y : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ));
    ∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let D : Finset (Fin k) := HierarchyStoredColorsAt P.counterexample.hierarchy (Fin.last
        P.counterexample.hierarchy.dividerCount);
    ∀ (beta : Fin k) (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), (
    ∀ v ∈ TreeSequenceVertexSet B, MissingColors G R.coloring v = MissingColors G P.coloring v) →
    ∀ eta ∈ HierarchyStoredColorsAt P.counterexample.hierarchy (Fin.last
        P.counterexample.hierarchy.dividerCount), beta ∈ P.counterexample.good.gamma (Fin.last
        P.counterexample.hierarchy.dividerCount) eta →
    ∀ owner ∈ D, beta ∈ P.counterexample.good.gamma (Fin.last
        P.counterexample.hierarchy.dividerCount) owner → (↑(HierarchyFirstMissingPosition
        P.coloring T owner) : ℕ) ≤ Y.length → (↑(HierarchyFirstMissingPosition R.coloring T eta) :
        ℕ) ≤ Y.length := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx j hlen B firstFixed Y P D beta R hm eta heP
      hcP owner howner hbOwner hcut
  have he : eta = owner := by
    by_contra hn
    exact Finset.disjoint_left.mp (P.counterexample.good.disjointPairs _ eta owner heP howner hn)
        hcP hbOwner
  rw [firstFixed P.coloring R.coloring hm eta, he]
  exact hcut

private theorem helper_branch_1318.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (j : ℕ) (hlen : (4 :
        ℕ) ≤ T.length),
    let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ)) (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ) (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ); (
    ∀ (psi tau : PartialEdgeColoring E k), (
    ∀ v ∈ TreeSequenceVertexSet B, MissingColors G tau v = MissingColors G psi v) →
    ∀ (c : Fin k), HierarchyFirstMissingPosition tau T c = HierarchyFirstMissingPosition psi T c)
        → (
    ∀ (R S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∀ eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount), eta ∈ HierarchyStoredColorsAt
        S.counterexample.hierarchy (Fin.last S.counterexample.hierarchy.dividerCount) ∧
        R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta =
        S.counterexample.good.gamma (Fin.last S.counterexample.hierarchy.dividerCount) eta) →
    let Extra : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx → Finset (Fin
        k) := fun (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) ↦
        (TreeSequenceVertexSet R.replacementBase.core \ TreeSequenceVertexSet
        (R.corresponding.replacementETT.series.data.tree (Fin.last
        R.corresponding.replacementETT.rounds).castSucc)).biUnion fun (v : V) ↦ MissingColors G
        R.coloring v;
    let Gamma : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx → Finset (Fin
        k) := fun (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) ↦
        (HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount)).biUnion (R.counterexample.good.gamma (Fin.last
        R.counterexample.hierarchy.dividerCount)); (
    ∀ (R S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), (
    ∀ v ∈ TreeSequenceVertexSet B, MissingColors G S.coloring v = MissingColors G R.coloring v) →
        Extra S = Extra R) → (
    ∀ (R S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), Gamma R = Gamma
        S) →
    let Y : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ));
    ∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let D : Finset (Fin k) := HierarchyStoredColorsAt P.counterexample.hierarchy (Fin.last
        P.counterexample.hierarchy.dividerCount);
    ∀ (beta : Fin k), (beta ∉ Gamma P ∪ Extra P ∨
    ∃ eta ∈ D, beta ∈ P.counterexample.good.gamma (Fin.last
        P.counterexample.hierarchy.dividerCount) eta ∧ (↑(HierarchyFirstMissingPosition P.coloring
        T eta) : ℕ) ≤ Y.length) →
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), (
    ∀ v ∈ TreeSequenceVertexSet B, MissingColors G R.coloring v = MissingColors G P.coloring v) →
        beta ∉ Gamma R ∪ Extra R ∨
    ∃ eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount), beta ∈ R.counterexample.good.gamma (Fin.last
        R.counterexample.hierarchy.dividerCount) eta ∧ (↑(HierarchyFirstMissingPosition R.coloring
        T eta) : ℕ) ≤ Y.length := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx j hlen B firstFixed gammaTransport Extra
      Gamma extraFixed gammaFixed Y P D beta hbChoice R hm
  rcases hbChoice with hout | ⟨eta, heta, hbGamma, hcut⟩
  · left
    have he : Gamma R ∪ Extra R = Gamma P ∪ Extra P :=
      congrArg₂ (fun s t : Finset (Fin k) => s ∪ t)
        (gammaFixed P R).symm (extraFixed P R hm)
    exact he.symm ▸ hout
  · obtain ⟨hetaR, hgR⟩ := gammaTransport P R eta heta
    right
    exact ⟨eta, hetaR, hgR ▸ hbGamma, by rw [firstFixed P.coloring R.coloring hm eta]; exact hcut⟩

private theorem helper_branch_1335.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C),
    let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount); (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount) = A) →
    let Extra : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx → Finset (Fin
        k) := fun (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) ↦
        (TreeSequenceVertexSet R.replacementBase.core \ TreeSequenceVertexSet
        (R.corresponding.replacementETT.series.data.tree (Fin.last
        R.corresponding.replacementETT.rounds).castSucc)).biUnion fun (v : V) ↦ MissingColors G
        R.coloring v;
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∀ c ∈ TreeMissingColors R.coloring A, c ∉ Extra R →
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    let _ : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount; H.dividerCount = (0 : ℕ) →
        c ∈ HierarchyStageMissingColors R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx A starEq Extra R c hcA hcExtra H q hq
  have hAcore : A = R.replacementBase.core := by
    rw [← starEq R]
    simp [HierarchyStarredStage, hq, Fin.last, H]
  obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hcA
  rw [hAcore] at hv
  have hvTn : v ∈ TreeSequenceVertexSet (R.corresponding.replacementETT.series.data.tree
      (Fin.last R.corresponding.replacementETT.rounds).castSucc) := by
    by_contra hh
    exact hcExtra (Finset.mem_biUnion.mpr ⟨v, Finset.mem_sdiff.mpr ⟨hv, hh⟩, hcv⟩)
  have hm : c ∈ TreeMissingColors R.coloring (R.corresponding.replacementETT.series.data.tree
      (Fin.last R.corresponding.replacementETT.rounds).castSucc) :=
    Finset.mem_biUnion.mpr ⟨v, hvTn, hcv⟩
  simpa [HierarchyStageMissingColors, H, q, hq, Fin.last] using hm

private theorem helper_branch_1348.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C),
    let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount); (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount) = A) →
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∀ c ∈ TreeMissingColors R.coloring A,
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    let _ : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount; ¬H.dividerCount = (0 : ℕ) →
        c ∈ HierarchyStageMissingColors R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx A starEq R c hcA H q hq
  have posEq : HierarchyStageMissingColors H q = TreeMissingColors R.coloring A := by
    rw [← starEq R]
    unfold HierarchyStageMissingColors HierarchyStarredStage
    dsimp only
    change Fin.cases (TreeMissingColors R.coloring
        (R.corresponding.replacementETT.series.data.tree
          (Fin.last R.corresponding.replacementETT.rounds).castSucc))
        (fun i : Fin H.dividerCount => TreeMissingColors R.coloring (H.stage i.succ.castSucc)) q =
      TreeMissingColors R.coloring (Fin.cases R.replacementBase.core
        (fun i : Fin H.dividerCount => H.stage i.succ.castSucc) q)
    obtain hz | ⟨i, hi⟩ := Fin.eq_zero_or_eq_succ q
    · exact (hq (by simpa [q] using congrArg Fin.val hz)).elim
    · rw [hi]
      rfl
  rw [posEq]
  exact hcA

private theorem helper_branch_1365.{u_1, u_2} :
    helperBranch1365Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hnonempty j hpathLower hpathUpper trans A
      htail hlen B hBT vertexMem firstAt stageSwitch gammaTransport gammaUnused Extra Gamma
      gammaSub Y hYlen hYB I i hiUpper P alpha haPrefix haTerminal hSlen ja ha haOutside haGood
      hiEq X hXlen hXB hAX hAXlt hYXlen hjaX D beta yb jb hb hjbY haFirst habNe hbUnused
      haException cutBeta finish hAlphaStored
  have hgNon : (P.counterexample.good.gamma (Fin.last P.counterexample.hierarchy.dividerCount)
      alpha).Nonempty := by
    apply Finset.card_pos.mp
    rw [P.counterexample.good.twoColors _ _ hAlphaStored]
    decide
  obtain ⟨gamma, hg⟩ := hgNon
  have hgStage : gamma ∈ HierarchyStageMissingColors P.counterexample.hierarchy
      (Fin.last P.counterexample.hierarchy.dividerCount) :=
    (Finset.mem_sdiff.mp (P.counterexample.good.avoidance _ _ hAlphaStored hg)).1
  have hgA : gamma ∈ TreeMissingColors P.coloring A := gammaSub P
    (Finset.mem_biUnion.mpr ⟨alpha, hAlphaStored, hg⟩)
  have hgAlpha : gamma ≠ alpha := by rintro rfl; exact haOutside hgA
  have hgBeta : gamma ≠ beta := by
    intro he
    have hcut := cutBeta P (fun _ _ => rfl) alpha hAlphaStored (he ▸ hg)
    clear * - hcut haFirst hYXlen
    omega
  have hgUnused : ∀ t : Fin T.length, A.length ≤ t.val → t.val < X.length →
      P.coloring (T.edge t) ≠ some gamma := by
    intro t hlo hhi
    exact gammaUnused P alpha gamma hAlphaStored hg t hlo (by rw [haFirst]; exact hhi)
  have cutGamma : ∀ eta ∈ D,
      gamma ∈ P.counterexample.good.gamma (Fin.last P.counterexample.hierarchy.dividerCount) eta →
        (HierarchyFirstMissingPosition P.coloring T eta).val ≤ X.length := by
    intro eta heta hc
    have he : eta = alpha := by
      by_contra hn
      exact Finset.disjoint_left.mp (P.counterexample.good.disjointPairs _ eta alpha heta
          hAlphaStored hn) hc hg
    rw [he, haFirst]
  obtain ⟨P1, hm1, hf1, _, ht1⟩ := stageSwitch P X hAX hAXlt hXB gamma alpha hgAlpha hgStage
    ja (by omega) ha (Or.inr haTerminal) hgUnused haException (by
      intro eta heta hc
      rcases hc with hc | hc
      · exact cutGamma eta heta hc
      · exact (haOutside (gammaSub P (Finset.mem_biUnion.mpr ⟨eta, heta, hc⟩))).elim)
  have hgTerm : gamma ∈ MissingColors G P1.coloring (T.vertex (Fin.last T.length)) := ht1 haTerminal
  obtain ⟨hAlphaStored1, hgammaEq⟩ := gammaTransport P P1 alpha hAlphaStored
  have hg1 : gamma ∈ P1.counterexample.good.gamma (Fin.last
      P1.counterexample.hierarchy.dividerCount) alpha :=
    hgammaEq ▸ hg
  have hgStage1 : gamma ∈ HierarchyStageMissingColors P1.counterexample.hierarchy
      (Fin.last P1.counterexample.hierarchy.dividerCount) :=
    (Finset.mem_sdiff.mp (P1.counterexample.good.avoidance _ _ hAlphaStored1 hg1)).1
  have hb1 : beta ∈ MissingColors G P1.coloring (B.vertex jb) := by
    rw [hm1 _ (vertexMem B jb)]
    exact hb
  have ha1 : alpha ∈ MissingColors G P1.coloring (B.vertex ja) := by
    rw [hm1 _ (vertexMem B ja)]
    exact ha
  have haFirst1 : (HierarchyFirstMissingPosition P1.coloring T alpha).val = X.length := by
    rw [firstAt P1 alpha ja ha1, hjaX]
  have hgUnused1 : ∀ t : Fin T.length, A.length ≤ t.val → t.val < X.length →
      P1.coloring (T.edge t) ≠ some gamma := by
    intro t hlo hhi
    exact gammaUnused P1 alpha gamma hAlphaStored1 hg1 t hlo (by rw [haFirst1]; exact hhi)
  have hbUnused1 : ∀ t : Fin T.length, A.length ≤ t.val → t.val < X.length →
      P1.coloring (T.edge t) ≠ some beta := by
    intro t hlo hhi
    rw [hf1 t hlo hhi]
    exact hbUnused t hlo hhi
  obtain ⟨P2, hm2, _, ht2, _⟩ := stageSwitch P1 X hAX hAXlt hXB gamma beta hgBeta hgStage1
    jb (by omega) hb1 (Or.inl hgTerm) hgUnused1 (by
      intro t hlo hhi hc
      exact (hbUnused1 t hlo hhi hc).elim) (by
      intro eta heta hc
      rcases hc with hc | hc
      · have he : eta = alpha := by
          by_contra hn
          exact Finset.disjoint_left.mp (P1.counterexample.good.disjointPairs _ eta alpha heta
              hAlphaStored1 hn) hc hg1
        rw [he, haFirst1]
      · exact (cutBeta P1 hm1 eta heta hc).trans (by omega))
  have hm : ∀ v ∈ TreeSequenceVertexSet B, MissingColors G P2.coloring v = MissingColors G
      P.coloring v :=
    fun v hv => (hm2 v hv).trans (hm1 v hv)
  exact ⟨P2, beta, ht2 hgTerm, finish P2 hm (ht2 hgTerm)⟩

private theorem helper_branch_1435.{u_1, u_2} :
    helperBranch1435Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hnonempty j hpathLower hpathUpper trans A
      htail hlen B hBT stageSwitch Extra Gamma gammaSub Y hYlen hYB I i hiUpper P alpha
      haTerminal hSlen ja ha haOutside hiEq X hXlen hXB hAX hAXlt hYXlen hjaX beta yb habNe
      hbUnused haException cutBeta finish hbStage
  obtain ⟨S, hm, _, _, ht⟩ := stageSwitch P X hAX hAXlt hXB beta alpha habNe.symm hbStage
    ja (by omega) ha (Or.inr haTerminal) hbUnused haException (by
      intro eta heta hc
      rcases hc with hc | hc
      · exact (cutBeta P (fun _ _ => rfl) eta heta hc).trans (by omega)
      · exact (haOutside (gammaSub P (Finset.mem_biUnion.mpr ⟨eta, heta, hc⟩))).elim)
  exact ⟨S, beta, ht haTerminal, finish S hm (ht haTerminal)⟩

private theorem helper_hjbA_1449.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (hnonempty :
        (HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx).Nonempty) (j :
        ℕ) (_ : (2 : ℕ) ≤ j) (hpathUpper : j < HierarchyFullTailLength C),
    let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount);
    ∀ (htail : (3 : ℕ) ≤ T.length - A.length) (hlen : (4 : ℕ) ≤ T.length),
    let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ)) (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ) (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ); TreeSequenceInitialSegment B T → TreeSequenceInitialSegment A B → (
    ∀ (U : TreeSequence G e0) (j : Fin (U.length + (1 : ℕ))), U.vertex j ∈ TreeSequenceVertexSet
        U) →
    let Y : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ)); Y.length = A.length + (j
        - (2 : ℕ)) →
    ∀ (hYB : TreeSequenceInitialSegment Y B),
    let I : Finset ℕ := HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx;
    let i : ℕ := I.max' hnonempty;
    ∀ (hiUpper : i < j) (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
        (alpha : Fin k) (hSlen : (HierarchyFullTailPrefix C i).length = A.length + i),
    let ja : Fin (B.length + (1 : ℕ)) := (⟨A.length + i,
    have hb : B.length = T.length - (1 : ℕ) := rfl; id (fun (hpathUpper : j < T.length - A.length)
        ↦ Decidable.byContradiction fun (a : ¬A.length + i < B.length + (1 : ℕ)) ↦
    by
                omega
    ) hpathUpper⟩ : Fin (B.length + (1 : ℕ))); i = j - (1 : ℕ) →
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ)); X.length = A.length + (j
        - (1 : ℕ)) → TreeSequenceInitialSegment X B → X.length = Y.length + (1 : ℕ) → (↑ja : ℕ) =
        X.length →
    ∀ (beta : Fin k) (yb : Fin (Y.length + (1 : ℕ))),
    let jb : Fin (B.length + (1 : ℕ)) := Fin.castLE (Nat.succ_le_succ hYB.1) yb; beta ∈
        MissingColors G P.coloring (B.vertex jb) → (↑(HierarchyFirstMissingPosition P.coloring T
        alpha) : ℕ) = X.length → beta ∉ TreeMissingColors P.coloring A → A.length < (↑jb : ℕ) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hnonempty j hpathLower hpathUpper A htail
      hlen B hBT hAB vertexMem Y hYlen hYB I i hiUpper P alpha hSlen ja hiEq X hXlen hXB hYXlen
      hjaX beta yb jb hb haFirst hbOutside
  by_contra hh
  have hjle : jb.val ≤ A.length := by omega
  let x : Fin (A.length + 1) := ⟨jb.val, by omega⟩
  have hx : Fin.castLE (Nat.succ_le_succ hAB.1) x = jb := Fin.ext rfl
  apply hbOutside
  exact Finset.mem_biUnion.mpr ⟨A.vertex x, vertexMem A x, by
    rw [← hAB.2.1 x, hx]; exact hb⟩

private theorem helper_hsame_1512.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (hnonempty :
        (HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx).Nonempty) (j :
        ℕ) (_ : (2 : ℕ) ≤ j) (hpathUpper : j < HierarchyFullTailLength C),
    let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount);
    ∀ (htail : (3 : ℕ) ≤ T.length - A.length) (hlen : (4 : ℕ) ≤ T.length),
    let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ)) (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ) (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    );
    ∀ (hBT : TreeSequenceInitialSegment B T),
    let Y : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ)); Y.length = A.length + (j
        - (2 : ℕ)) →
    ∀ (hYB : TreeSequenceInitialSegment Y B),
    let I : Finset ℕ := HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx;
    let i : ℕ := I.max' hnonempty;
    ∀ (hiUpper : i < j) (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
        (alpha : Fin k) (hSlen : (HierarchyFullTailPrefix C i).length = A.length + i),
    let ja : Fin (B.length + (1 : ℕ)) := (⟨A.length + i,
    have hb : B.length = T.length - (1 : ℕ) := rfl; id (fun (hpathUpper : j < T.length - A.length)
        ↦ Decidable.byContradiction fun (a : ¬A.length + i < B.length + (1 : ℕ)) ↦
    by
                omega
    ) hpathUpper⟩ : Fin (B.length + (1 : ℕ))); i = j - (1 : ℕ) →
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ)); X.length = A.length + (j
        - (1 : ℕ)) → TreeSequenceInitialSegment X B → X.length = Y.length + (1 : ℕ) → (↑ja : ℕ) =
        X.length →
    let D : Finset (Fin k) := HierarchyStoredColorsAt P.counterexample.hierarchy (Fin.last
        P.counterexample.hierarchy.dividerCount);
    ∀ (beta : Fin k) (yb : Fin (Y.length + (1 : ℕ))),
    let jb : Fin (B.length + (1 : ℕ)) := Fin.castLE (Nat.succ_le_succ hYB.1) yb; Fin.castLE
        (Nat.succ_le_succ hBT.1) jb = HierarchyFirstMissingPosition P.coloring T beta → Fin.castLE
        (Nat.succ_le_succ hBT.1) ja = HierarchyFirstMissingPosition P.coloring T alpha → (
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
        P.counterexample.hierarchy;
    have q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    have n : Fin (P.corresponding.replacementETT.rounds + (1 : ℕ)) := Fin.last
        P.corresponding.replacementETT.rounds;
    have A : TreeSequence G e0 := HierarchyStarredStage H q;
    have Tnq : TreeSequence G e0 := H.stage (⟨H.dividerCount,
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)));
    have Tn : TreeSequence G e0 := P.corresponding.replacementETT.series.data.tree n.castSucc;
    have Dn : Finset (Fin k) := TashkinovStoredColors P.corresponding.replacementETT.series.data
        n;
    have Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q;
    have va : V := T.vertex (HierarchyFirstMissingPosition P.coloring T beta);
    have vb : V := T.vertex (HierarchyFirstMissingPosition P.coloring T alpha);
    have sameComponent : Prop := TwoColorComponent G P.coloring beta alpha (Sum.inl va) =
        TwoColorComponent G P.coloring beta alpha (Sum.inl vb); ((0 : ℕ) < H.dividerCount ∧ (beta
        ∈ TreeMissingColors P.coloring Tnq ∨ Disjoint (insert beta ({ alpha } : Finset (Fin k)) :
        Finset (Fin k)) Dnq) → sameComponent) ∧ (H.dividerCount = (0 : ℕ) ∧ (beta ∈
        TreeMissingColors P.coloring Tn ∨ Disjoint (insert beta ({ alpha } : Finset (Fin k)) :
        Finset (Fin k)) Dn) → sameComponent) ∧ (beta ∈ TreeMissingColors P.coloring A ∧
        TreeColorSetClosed G P.coloring A ({ beta } : Finset (Fin k)) → sameComponent ∧
        TreeInterchangeable G A P.coloring beta alpha)) → Disjoint (insert beta ({ alpha } :
        Finset (Fin k)) : Finset (Fin k)) D → Disjoint (insert beta ({ alpha } : Finset (Fin k)) :
        Finset (Fin k)) (TashkinovStoredColors P.corresponding.replacementETT.series.data
        (Fin.last P.corresponding.replacementETT.rounds)) → TwoColorComponent G P.coloring beta
        alpha (Sum.inl (B.vertex jb)) = TwoColorComponent G P.coloring beta alpha (Sum.inl
        (B.vertex ja)) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hnonempty j hpathLower hpathUpper A htail
      hlen B hBT Y hYlen hYB I i hiUpper P alpha hSlen ja hiEq X hXlen hXB hYXlen hjaX D beta yb
      jb jbEq jaEq change hdisD hdisRaw
  have hh : TwoColorComponent G P.coloring beta alpha
      (Sum.inl (T.vertex (HierarchyFirstMissingPosition P.coloring T beta))) =
      TwoColorComponent G P.coloring beta alpha
        (Sum.inl (T.vertex (HierarchyFirstMissingPosition P.coloring T alpha))) := by
    by_cases hq : P.counterexample.hierarchy.dividerCount = 0
    · exact change.2.1 ⟨hq, Or.inr hdisRaw⟩
    · exact change.1 ⟨by omega, Or.inr hdisD⟩
  rw [← jbEq, ← jaEq, hBT.2.1 jb, hBT.2.1 ja] at hh
  exact hh

private theorem helper_hunusedBetween_1548.{u_1, u_2} :
    helperHunusedBetween1548Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hnonempty j hpathLower hpathUpper A htail
      hlen B hBT Y hYlen hYB I i hiUpper P alpha hSlen ja hiEq X hXlen hXB hYXlen hjaX beta yb jb
      haFirst hbUnused hjbA ibEq jbEq jaEq hh
  obtain ⟨_, t, hlo, hhi, hc⟩ := Finset.mem_filter.mp hh
  rw [ibEq] at hlo
  rw [haFirst] at hhi
  exact hbUnused t (by omega) hhi hc

private theorem helper_continuation_4396.{u_1, u_2} :
    helperContinuation4396Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hnonempty j hpathLower hpathUpper
      componentData trans A starEq hAT htail hlen B hBT fullB elementary vertexMem Extra Gamma Y
      hYlen hYB I i hiUpper P alpha haPrefix haTerminal hSlen ja ha haOutside haGood hiEq X hXlen
      hXB hYXlen hjaX D used beta hbY hbD hbUsed hbChoice vbeta hbeta yb jb hb haFirst habNe
      hbUnused haException cutBeta finish hAlphaStored hbStage hbOutsideChoice hbOutside hjbA
      haRaw hbRaw ibEq iaEq jbEq jaEq hordered hunused
  have hmissingP : beta ∈ TreeMissingColors P.coloring
      (HierarchyFullTailPrefix P.counterexample (HierarchyFullTailLength P.counterexample - 1)) ∧
      alpha ∈ TreeMissingColors P.coloring
        (HierarchyFullTailPrefix P.counterexample (HierarchyFullTailLength P.counterexample - 1))
           := by
    rw [fullB P]
    exact ⟨Finset.mem_biUnion.mpr ⟨B.vertex jb, vertexMem B jb, hb⟩,
      Finset.mem_biUnion.mpr ⟨B.vertex ja, vertexMem B ja, ha⟩⟩
  have hprefixP : ColoredVertexSetElementary G P.coloring
      (TreeSequenceVertexSet (HierarchyFullTailPrefix P.counterexample
        (HierarchyFullTailLength P.counterexample - 1))) := by
    rw [fullB P]
    exact elementary P
  have change := ChangeLemma G k e0 P.corresponding.replacementInput T P.coloring
    P.corresponding.replacementETT P.replacementBase P.counterexample
    P.minimumContext.proper P.minimumContext.oneEdgeUncolored P.minimumContext.lowerRung
    P.minimumContext.fewerDividers P.minimumContext.lexicographicMinimality hprefixP
    P.minimumContext.largeMissingSet beta alpha habNe.symm hmissingP
    (by dsimp only; rw [starEq P]; intro _; exact ⟨hordered, hunused⟩)
  have hdisD : Disjoint ({beta, alpha} : Finset (Fin k)) D := by
    exact Finset.disjoint_insert_left.mpr
      ⟨hbD, Finset.disjoint_singleton_left.mpr hAlphaStored⟩
  have hdisRaw : Disjoint ({beta, alpha} : Finset (Fin k))
      (TashkinovStoredColors P.corresponding.replacementETT.series.data
        (Fin.last P.corresponding.replacementETT.rounds)) := by
    exact Finset.disjoint_insert_left.mpr
      ⟨hbRaw, Finset.disjoint_singleton_left.mpr haRaw⟩
  have hsame : TwoColorComponent G P.coloring beta alpha (Sum.inl (B.vertex jb)) =
      TwoColorComponent G P.coloring beta alpha (Sum.inl (B.vertex ja)) := by
    exact helper_hsame_1512 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
        (@hnonempty) (@j) (@hpathLower) (@hpathUpper) (@htail) (@hlen) (@hBT) (@hYlen) (@hYB)
        (@hiUpper) (@P) (@alpha) (@hSlen) (@hiEq) (@hXlen) (@hXB) (@hYXlen) (@hjaX) (@beta) (@yb)
        (@jbEq) (@jaEq) (@change) (@hdisD) (@hdisRaw)
  have terminalNe (z : Fin (B.length + 1)) : T.vertex (Fin.last T.length) ≠ B.vertex z := by
    exact hBT.last_vertex_ne (by change T.length - 1 < T.length; omega) z
  obtain ⟨_, _, hmissing⟩ := componentData P.coloring beta alpha habNe.symm
    P.minimumContext.proper (TreeSequenceVertexSet B) (elementary P)
    (B.vertex jb) (B.vertex ja) (T.vertex (Fin.last T.length))
    (vertexMem B jb) (vertexMem B ja) (terminalNe jb) (terminalNe ja)
    hb ha (Or.inr haTerminal) hsame
  let sigma := TwoColorComponentSwap G P.coloring beta alpha
    (Sum.inl (T.vertex (Fin.last T.length)))
  have hprecedes : ∀ u ∈ TreeSequenceVertexSet A, TreeVertexOrder T u
      (T.vertex (HierarchyFirstMissingPosition P.coloring T beta)) := by
    intro vertex member
    exact hAT.vertex_precedes (by omega) member
  have hunusedBetween : beta ∉ (Finset.univ.filter fun c => ∃ t : Fin T.length,
      (HierarchyFirstMissingPosition P.coloring T beta).val ≤ t.val ∧
        t.val < (HierarchyFirstMissingPosition P.coloring T alpha).val ∧
          P.coloring (T.edge t) = some c) := by
    exact helper_hunusedBetween_1548 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@ctx) (@hnonempty) (@j) (@hpathLower) (@hpathUpper) (@htail) (@hlen) (@hBT) (@hYlen)
        (@hYB) (@hiUpper) (@P) (@alpha) (@hSlen) (@hiEq) (@hXlen) (@hXB) (@hYXlen) (@hjaX)
        (@beta) (@yb) (@haFirst) (@hbUnused) (@hjbA) (@ibEq) (@jbEq) (@jaEq)
  obtain ⟨_, _, _, _, corr, hmaximum, bs, K, goodK, hsameGood⟩ :=
    StableChangeCaseThree G k e0 P.corresponding.replacementInput T P.coloring
      P.corresponding.replacementETT P.replacementBase P.counterexample
      P.minimumContext.proper P.minimumContext.oneEdgeUncolored P.minimumContext.lowerRung
      P.minimumContext.fewerDividers P.minimumContext.lexicographicMinimality hprefixP
      P.minimumContext.largeMissingSet beta alpha habNe.symm hmissingP _ sigma rfl
      (by rw [starEq P]; exact hprecedes) hordered ⟨hbD, hAlphaStored⟩ hunusedBetween
  have hbetaTerminal : beta ∈ MissingColors G sigma (T.vertex (Fin.last T.length)) :=
    (TwoColorComponentSwapMissingBehavior G P.coloring beta alpha habNe.symm
      P.minimumContext.proper (Sum.inl (T.vertex (Fin.last T.length)))).2.2.1 _ (by rfl) haTerminal
  have hbNew : beta ∈ MissingColors G sigma (B.vertex jb) := by
    rw [hmissing _ (vertexMem B jb)]
    exact hb
  have hnot : ¬ ColoredVertexSetElementary G sigma (TreeSequenceVertexSet T) := by
    intro he
    exact Finset.disjoint_left.mp (he
      (TreeSequenceInitialSegmentVertexSetSubset hBT (vertexMem B jb))
      (vertexMem T (Fin.last T.length)) (terminalNe jb).symm) hbNew hbetaTerminal
  let CS : HierarchyCounterexample bs := by
    exact @helperCS1504 (@V) (@E) inferInstance inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha) (@beta) (@corr)
        (@hmaximum) (@bs) (@K) (@goodK) (@hnot)
  obtain ⟨S, hS⟩ := HierarchyReplacementPresentationTrans G k e0 input T phi ett base C ctx
    P sigma corr bs CS hsameGood
  have hm : ∀ v ∈ TreeSequenceVertexSet B, MissingColors G S.coloring v = MissingColors G
      P.coloring v := by
    rw [hS]
    exact hmissing
  have ht : beta ∈ MissingColors G S.coloring (T.vertex (Fin.last T.length)) := by
    rw [hS]
    exact hbetaTerminal
  exact ⟨S, beta, ht, finish S hm ht⟩

private theorem helper_continuation_3982.{u_1, u_2} :
    helperContinuation3982Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hnonempty j hpathLower hpathUpper
      finiteChoice componentData trans A starEq hAT htail hlen B hBT hAB fullB elementary
      vertexMem firstLe firstAt firstFixed stageSwitch gammaTransport gammaUnused notRaw
      tailException Extra Gamma gammaSub extraFixed gammaFixed Y hYlen hYT hYB hAY I i hiLower
      hiUpper P alpha haPrefix haTerminal hSlen ja ha haOutside haGood hiEq X hXlen hXB hAX hAXlt
      hYXlen hjaX D used tnew fresh freshCard usedStep nineY
  have choice : ∃ beta : Fin k,
      beta ∈ TreeMissingColors P.coloring Y ∧ beta ∉ D ∧ beta ∉ used (j - 1) ∧
        (beta ∉ Gamma P ∪ Extra P ∨
          ∃ eta, eta ∈ D ∧ beta ∈ P.counterexample.good.gamma
            (Fin.last P.counterexample.hierarchy.dividerCount) eta ∧
            (HierarchyFirstMissingPosition P.coloring T eta).val ≤ Y.length) := by
    apply helper_choice_1225 <;> assumption
  obtain ⟨beta, hbY, hbD, hbUsed, hbChoice⟩ := choice
  obtain ⟨vbeta, hvbeta, hbeta⟩ := Finset.mem_biUnion.mp hbY
  obtain ⟨yb, hyb⟩ : ∃ yb, Y.vertex yb = vbeta := by
    simpa [TreeSequenceVertexSet] using hvbeta
  let jb : Fin (B.length + 1) := Fin.castLE (Nat.succ_le_succ hYB.1) yb
  have hb : beta ∈ MissingColors G P.coloring (B.vertex jb) := by
    rw [hYB.2.1 yb, hyb]
    exact hbeta
  have hjbY : jb.val ≤ Y.length := by have := yb.isLt; dsimp [jb]; omega
  have haFirst : (HierarchyFirstMissingPosition P.coloring T alpha).val = X.length := by
    rw [firstAt P alpha ja ha, hjaX]
  have habNe : alpha ≠ beta := by
    exact helper_habNe_1264 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
        (@hnonempty) (@j) (@hpathLower) (@hpathUpper) (@htail) (@hlen) (@elementary) (@vertexMem)
        (@hYB) (@hiUpper) (@P) (@alpha) (@hSlen) (@ha) (@hYXlen) (@hjaX) (@beta) (@yb) (@hb) (@hjbY)
  have hbUnused : ∀ t : Fin T.length, A.length ≤ t.val → t.val < X.length →
      P.coloring (T.edge t) ≠ some beta := by
    intro t hlo hhi hc
    exact hbUsed (Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, hlo, by omega, hc⟩)
  have haException : ∀ t : Fin T.length, A.length ≤ t.val → t.val < X.length →
      P.coloring (T.edge t) = some alpha →
        TreeIncidentEdge (P.corresponding.replacementETT.series.data.tree
          (Fin.last P.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧
        alpha ∈ TashkinovStoredColors P.corresponding.replacementETT.series.data
          (Fin.last P.corresponding.replacementETT.rounds) := by
    intro t hlo hhi hc
    exact tailException P i hiLower (by change j < T.length - A.length at hpathUpper; omega)
      alpha haPrefix t hlo (by omega) hc
  have cutBeta (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
      (hm : ∀ v ∈ TreeSequenceVertexSet B,
        MissingColors G R.coloring v = MissingColors G P.coloring v) :
      ∀ eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy
        (Fin.last R.counterexample.hierarchy.dividerCount),
        beta ∈ R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta →
          (HierarchyFirstMissingPosition R.coloring T eta).val ≤ Y.length := by as_aux_lemma =>
    clear * - R P beta hm hbChoice Gamma D Y gammaTransport firstFixed
    intro eta heta hbe
    obtain ⟨heP, hgP⟩ := gammaTransport R P eta heta
    have hcP : beta ∈ P.counterexample.good.gamma (Fin.last
        P.counterexample.hierarchy.dividerCount) eta := hgP ▸ hbe
    rcases hbChoice with hout | ⟨owner, howner, hbOwner, hcut⟩
    · exact (hout (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨eta, heP, hcP⟩))).elim
    · exact helper_branch_1298 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
        (@j) (@hlen) (@firstFixed) (@P) (@beta) (@R) (@hm) (@eta) (@heP) (@hcP) (@owner)
        (@howner) (@hbOwner) (@hcut)
  have finish (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
      (hm : ∀ v ∈ TreeSequenceVertexSet B,
        MissingColors G R.coloring v = MissingColors G P.coloring v)
      (hterm : beta ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length))) :
      beta ∈ TreeMissingColors R.coloring Y ∧
        (beta ∉ Gamma R ∪ Extra R ∨
          ∃ eta, eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy
              (Fin.last R.counterexample.hierarchy.dividerCount) ∧
            beta ∈ R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount)
                eta ∧
            (HierarchyFirstMissingPosition R.coloring T eta).val ≤ Y.length) := by as_aux_lemma =>
    clear * - R P beta hm hbY hbChoice Y B hYB Gamma Extra gammaFixed extraFixed gammaTransport
        firstFixed
    constructor
    · obtain ⟨v, hv, hc⟩ := Finset.mem_biUnion.mp hbY
      exact Finset.mem_biUnion.mpr ⟨v, hv, by
        rw [hm v (TreeSequenceInitialSegmentVertexSetSubset hYB hv)]; exact hc⟩
    · exact helper_branch_1318 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
        (@j) (@hlen) (@firstFixed) (@gammaTransport) (@extraFixed) (@gammaFixed) (@P) (@beta)
        (@hbChoice) (@R) (@hm)
  have stageInside (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
      (c : Fin k) (hcA : c ∈ TreeMissingColors R.coloring A) (hcExtra : c ∉ Extra R) :
      c ∈ HierarchyStageMissingColors R.counterexample.hierarchy
        (Fin.last R.counterexample.hierarchy.dividerCount) := by as_aux_lemma =>
    clear * - R A c hcA hcExtra Extra starEq
    let H := R.counterexample.hierarchy
    let q := Fin.last H.dividerCount
    by_cases hq : H.dividerCount = 0
    · exact helper_branch_1335 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
        (@starEq) (@R) (@c) (@hcA) (@hcExtra) (@hq)
    · exact helper_branch_1348 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
        (@starEq) (@R) (@c) (@hcA) (@hq)
  by_cases hAlphaStored : alpha ∈ D
  · exact @helper_branch_1365 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@hnonempty) (@j)
      (@hpathLower) (@hpathUpper) (@trans) (@htail) (@hlen) (@hBT) (@vertexMem) (@firstAt)
      (@stageSwitch) (@gammaTransport) (@gammaUnused) (@gammaSub) (@hYlen) (@hYB) (@hiUpper) (@P)
      (@alpha) (@haPrefix) (@haTerminal) (@hSlen) (@ha) (@haOutside) (@haGood) (@hiEq) (@hXlen)
      (@hXB) (@hAX) (@hAXlt) (@hYXlen) (@hjaX) (@beta) (@yb) (@hb) (@hjbY) (@haFirst) (@habNe)
      (@hbUnused) (@haException) (@cutBeta) (@finish) (@hAlphaStored)
  by_cases hbStage : beta ∈ HierarchyStageMissingColors P.counterexample.hierarchy
      (Fin.last P.counterexample.hierarchy.dividerCount)
  · exact @helper_branch_1435 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@hnonempty) (@j)
      (@hpathLower) (@hpathUpper) (@trans) (@htail) (@hlen) (@hBT) (@stageSwitch) (@gammaSub)
      (@hYlen) (@hYB) (@hiUpper) (@P) (@alpha) (@haTerminal) (@hSlen) (@ha) (@haOutside) (@hiEq)
      (@hXlen) (@hXB) (@hAX) (@hAXlt) (@hYXlen) (@hjaX) (@beta) (@yb) (@habNe) (@hbUnused)
      (@haException) (@cutBeta) (@finish) (@hbStage)
  have hbOutsideChoice : beta ∉ Gamma P ∪ Extra P := by
    rcases hbChoice with h | ⟨eta, heta, hbe, _⟩
    · exact h
    · exact (hbStage (Finset.mem_sdiff.mp (P.counterexample.good.avoidance _ _ heta hbe)).1).elim
  have hbOutside : beta ∉ TreeMissingColors P.coloring A := by
    intro hc
    exact hbStage (stageInside P beta hc (fun he => hbOutsideChoice (Finset.mem_union_right _ he)))
  have hjbA : A.length < jb.val := by
    exact helper_hjbA_1449 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
        (@hnonempty) (@j) (@hpathLower) (@hpathUpper) (@htail) (@hlen) (@hBT) (@hAB) (@vertexMem)
        (@hYlen) (@hYB) (@hiUpper) (@P) (@alpha) (@hSlen) (@hiEq) (@hXlen) (@hXB) (@hYXlen)
        (@hjaX) (@beta) (@yb) (@hb) (@haFirst) (@hbOutside)
  have haRaw := notRaw P alpha haOutside hAlphaStored
  have hbRaw := notRaw P beta hbOutside hbD
  have ibEq := firstAt P beta jb hb
  have iaEq := firstAt P alpha ja ha
  have jbEq : Fin.castLE (Nat.succ_le_succ hBT.1) jb =
      HierarchyFirstMissingPosition P.coloring T beta := Fin.ext ibEq.symm
  have jaEq : Fin.castLE (Nat.succ_le_succ hBT.1) ja =
      HierarchyFirstMissingPosition P.coloring T alpha := Fin.ext iaEq.symm
  have hordered : TreeVertexOrder T
      (T.vertex (HierarchyFirstMissingPosition P.coloring T beta))
      (T.vertex (HierarchyFirstMissingPosition P.coloring T alpha)) := by
    refine ⟨_, _, rfl, rfl, ?_⟩
    clear * - ibEq iaEq hjaX hjbY hYXlen
    omega
  have hunused : beta ∉ (Finset.univ.filter fun c => ∃ t : Fin T.length,
      A.length ≤ t.val ∧ t.val < (HierarchyFirstMissingPosition P.coloring T alpha).val ∧
        P.coloring (T.edge t) = some c) := by
    intro hh
    obtain ⟨_, t, hlo, hhi, hc⟩ := Finset.mem_filter.mp hh
    rw [haFirst] at hhi
    exact hbUnused t hlo hhi hc
  exact @helper_continuation_4396 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@hnonempty)
      (@j) (@hpathLower) (@hpathUpper) (@componentData) (@trans) (@starEq) (@hAT) (@htail)
      (@hlen) (@hBT) (@fullB) (@elementary) (@vertexMem) (@hYlen) (@hYB) (@hiUpper) (@P) (@alpha)
      (@haPrefix) (@haTerminal) (@hSlen) (@ha) (@haOutside) (@haGood) (@hiEq) (@hXlen) (@hXB)
      (@hYXlen) (@hjaX) (@beta) (@hbY) (@hbD) (@hbUsed) (@hbChoice) (@vbeta) (@hbeta) (@yb) (@hb)
      (@haFirst) (@habNe) (@hbUnused) (@haException) (@cutBeta) (@finish) (@hAlphaStored)
      (@hbStage) (@hbOutsideChoice) (@hbOutside) (@hjbA) (@haRaw) (@hbRaw) (@ibEq) (@iaEq)
      (@jbEq) (@jaEq) (@hordered) (@hunused)
private theorem helper_continuation_3797.{u_1, u_2} :
    helperContinuation3797Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hvertexMissing hnonempty j hj hpathLower
      hpathUpper finiteChoice componentData trans common A starEq hAT htail hlen B hBT hAB fullEq
      fullB elementary vertexMem firstLe firstAt firstFixed stageSwitch gammaTransport
      gammaUnused outsideA notRaw tailException coreA
  let Extra := fun R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx =>
    ((TreeSequenceVertexSet R.replacementBase.core \
      TreeSequenceVertexSet (R.corresponding.replacementETT.series.data.tree
        (Fin.last R.corresponding.replacementETT.rounds).castSucc)).biUnion
      fun v => MissingColors G R.coloring v)
  let Gamma := fun R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx =>
    (HierarchyStoredColorsAt R.counterexample.hierarchy
      (Fin.last R.counterexample.hierarchy.dividerCount)).biUnion
      (R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount))
  have gammaSub (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) :
      Gamma R ⊆ TreeMissingColors R.coloring A := by as_aux_lemma =>
    intro c hc
    obtain ⟨eta, heta, hce⟩ := Finset.mem_biUnion.mp hc
    have hm := (GoodHierarchyReservedDisjoint R.counterexample.good
      (Fin.last R.counterexample.hierarchy.dividerCount)).1 eta heta hce
    rw [starEq R] at hm
    exact hm
  have extraSub (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) :
      Extra R ⊆ TreeMissingColors R.coloring A := by as_aux_lemma =>
    intro c hc
    obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hc
    exact Finset.mem_biUnion.mpr ⟨v,
      TreeSequenceInitialSegmentVertexSetSubset (coreA R) (Finset.mem_sdiff.mp hv).1, hcv⟩
  have tnEq (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) :
      R.corresponding.replacementETT.series.data.tree
          (Fin.last R.corresponding.replacementETT.rounds).castSucc =
        ett.series.data.tree (Fin.last ett.rounds).castSucc := by as_aux_lemma =>
    have hs := (Fin.heq_fun_iff
      (congrArg (fun q => q + 2) R.sameGood.1.2.1)).mp R.sameGood.1.2.2.1 0
    have hs' : C.hierarchy.stage 0 = R.counterexample.hierarchy.stage 0 := hs
    rw [C.hierarchy.baseStage, R.counterexample.hierarchy.baseStage] at hs'
    exact hs'.symm
  have extraFixed (R S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
      (hm : ∀ v ∈ TreeSequenceVertexSet B,
        MissingColors G S.coloring v = MissingColors G R.coloring v) : Extra S = Extra R := by
            as_aux_lemma =>
    unfold Extra
    rw [tnEq R, tnEq S, ← R.sameGood.1.1, ← S.sameGood.1.1]
    apply Finset.biUnion_congr rfl
    intro v hv
    apply hm
    have hvR : v ∈ TreeSequenceVertexSet R.replacementBase.core := by
      rw [← R.sameGood.1.1]
      exact (Finset.mem_sdiff.mp hv).1
    exact TreeSequenceInitialSegmentVertexSetSubset (trans (coreA R) hAB) hvR
  have gammaFixed (R S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) :
      Gamma R = Gamma S := by as_aux_lemma =>
    ext c
    simp only [Gamma, Finset.mem_biUnion]
    constructor
    · rintro ⟨eta, heta, hc⟩
      obtain ⟨hs, he⟩ := gammaTransport R S eta heta
      exact ⟨eta, hs, he ▸ hc⟩
    · rintro ⟨eta, heta, hc⟩
      obtain ⟨hs, he⟩ := gammaTransport S R eta heta
      exact ⟨eta, hs, he ▸ hc⟩
  have prefixLen (r : ℕ) (hr : r ≤ T.length - A.length) :
      (HierarchyFullTailPrefix C r).length = A.length + r := by as_aux_lemma =>
    change min (A.length + r) T.length = A.length + r
    have := hAT.1
    omega
  have prefixT (r : ℕ) : TreeSequenceInitialSegment (HierarchyFullTailPrefix C r) T :=
    ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
  let Y := HierarchyFullTailPrefix C (j - 2)
  have hYlen : Y.length = A.length + (j - 2) := prefixLen _ (by
    change j < T.length - A.length at hpathUpper
    omega)
  have hYT : TreeSequenceInitialSegment Y T := prefixT _
  have hYB : TreeSequenceInitialSegment Y B := common hYT hBT (by
    have hb : B.length = T.length - 1 := rfl
    change j < T.length - A.length at hpathUpper
    omega)
  have hAY : TreeSequenceInitialSegment A Y := common hAT hYT (by omega)
  let I := HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx
  let i := I.max' hnonempty
  have hi : i ∈ I := Finset.max'_mem I hnonempty
  have hiLower : 1 ≤ i := (Finset.mem_Icc.mp (Finset.mem_filter.mp hi).1).1
  have hiUpper : i < j := by
    rw [← hj]
    exact HierarchySituationThreeEligibleIndexBound G k e0 input T phi ett base C ctx
      (by rw [hj]; exact hpathLower) (by rw [hj]; exact hpathUpper) hvertexMissing i hi
  obtain ⟨P, alpha, haPrefix, haTerminal⟩ := (Finset.mem_filter.mp hi).2
  have hSlen : (HierarchyFullTailPrefix C i).length = A.length + i :=
    prefixLen _ (by change j < T.length - A.length at hpathUpper; omega)
  let ja : Fin (B.length + 1) := ⟨A.length + i, by
    have hb : B.length = T.length - 1 := rfl
    change j < T.length - A.length at hpathUpper
    omega⟩
  have ha : alpha ∈ MissingColors G P.coloring (B.vertex ja) := by
    exact helper_ha_1142 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
        (@hnonempty) (@j) (@hpathLower) (@hpathUpper) (@htail) (@hlen) (@hBT) (@prefixT)
        (@hiUpper) (@P) (@alpha) (@haPrefix) (@hSlen)
  have haOutside := outsideA P alpha ja (by dsimp [ja]; omega) ha
  have haGood : alpha ∉ Gamma P ∪ Extra P := by
    intro hc
    rcases Finset.mem_union.mp hc with hc | hc
    · exact haOutside (gammaSub P hc)
    · exact haOutside (extraSub P hc)
  by_cases hsmall : i ≤ j - 2
  · exact helper_branch_1158 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
      (@hnonempty) (@j) (@hpathLower) (@hpathUpper) (@htail) (@hlen) (@vertexMem) (@hYlen) (@hYB)
      (@hiUpper) (@P) (@alpha) (@haTerminal) (@hSlen) (@ha) (@haGood) (@hsmall)
  have hiEq : i = j - 1 := by omega
  let X := HierarchyFullTailPrefix C (j - 1)
  have hXlen : X.length = A.length + (j - 1) := prefixLen _ (by
    change j < T.length - A.length at hpathUpper; omega)
  have hXT : TreeSequenceInitialSegment X T := prefixT _
  have hXB : TreeSequenceInitialSegment X B := common hXT hBT (by
    have hb : B.length = T.length - 1 := rfl
    change j < T.length - A.length at hpathUpper; omega)
  have hAX : TreeSequenceInitialSegment A X := common hAT hXT (by omega)
  have hAXlt : A.length < X.length := by change 2 ≤ j at hpathLower; omega
  have hYX : TreeSequenceInitialSegment Y X := common hYT hXT (by omega)
  have hYXlen : X.length = Y.length + 1 := by change 2 ≤ j at hpathLower; omega
  have hjaX : ja.val = X.length := by dsimp [ja]; omega
  let D := HierarchyStoredColorsAt P.counterexample.hierarchy
    (Fin.last P.counterexample.hierarchy.dividerCount)
  let used := fun r : ℕ => (Finset.univ : Finset (Fin k)).filter fun c =>
    ∃ t : Fin T.length, A.length ≤ t.val ∧ t.val < A.length + r ∧
      P.coloring (T.edge t) = some c
  let tnew : Fin T.length := ⟨Y.length, by have := hXB.1; have := hBT.1; omega⟩
  let fresh := (Finset.univ : Finset (Fin k)).filter fun c => P.coloring (T.edge tnew) = some c
  have freshCard : fresh.card ≤ 1 := by as_aux_lemma =>
    apply Finset.card_le_one.mpr
    intro c hc d hd
    exact Option.some.inj ((Finset.mem_filter.mp hc).2.symm.trans (Finset.mem_filter.mp hd).2)
  have usedStep : used (j - 1) ⊆ used (j - 2) ∪ fresh := by as_aux_lemma =>
    intro c hc
    obtain ⟨_, t, hlo, hhi, hcol⟩ := Finset.mem_filter.mp hc
    by_cases h : t.val < A.length + (j - 2)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, hlo, h, hcol⟩)
    · have ht : t = tnew := Fin.ext (by dsimp [tnew]; omega)
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht ▸ hcol⟩)
  have nine := NineN G k e0 P.corresponding.replacementInput T P.coloring
    P.corresponding.replacementETT P.counterexample.positive P.replacementBase
    P.counterexample.hierarchy P.counterexample.good
    (by
      change ColoredVertexSetElementary G P.coloring (TreeSequenceVertexSet
        (HierarchyFullTailPrefix P.counterexample (HierarchyFullTailLength P.counterexample - 1)))
      rw [fullB P]
      exact elementary P)
    P.minimumContext.largeMissingSet
  have nineY :
      2 * P.corresponding.replacementETT.rounds + 11 ≤
        ((TreeMissingColors P.coloring Y \ Extra P) \ used (j - 2)).card ∧
      ((((TreeMissingColors P.coloring Y \ Extra P) \ used (j - 2)) \ (Gamma P ∪ D)).card ≤ 4 →
        ∃ eta : Fin 7 → Fin k, Function.Injective eta ∧
          ∀ h : Fin 7, eta h ∈ D ∧ eta h ∈ TreeMissingColors P.coloring Y ∧
            Disjoint (P.counterexample.good.gamma
              (Fin.last P.counterexample.hierarchy.dividerCount) (eta h) ∪ {eta h}) (used (j -
                  2))) := by
    have hn := nine (j - 2) (by
      rw [starEq P]
      change j < T.length - A.length at hpathUpper
      omega)
    dsimp only at hn
    have hy : TreeSequencePrefix T
        (min ((HierarchyStarredStage P.counterexample.hierarchy
          (Fin.last P.counterexample.hierarchy.dividerCount)).length + (j - 2)) T.length)
        (by have := (HierarchyStarredStage P.counterexample.hierarchy
          (Fin.last P.counterexample.hierarchy.dividerCount)).positive; have := T.positive; omega)
        (Nat.min_le_right _ _) = Y := fullEq P (j - 2)
    rw [hy] at hn
    simp only [starEq P] at hn
    exact hn
  exact @helper_continuation_3982 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@hnonempty)
      (@j) (@hpathLower) (@hpathUpper) (@finiteChoice) (@componentData) (@trans) (@starEq) (@hAT)
      (@htail) (@hlen) (@hBT) (@hAB) (@fullB) (@elementary) (@vertexMem) (@firstLe) (@firstAt)
      (@firstFixed) (@stageSwitch) (@gammaTransport) (@gammaUnused) (@notRaw) (@tailException)
      (@gammaSub) (@extraFixed) (@gammaFixed) (@hYlen) (@hYT) (@hYB) (@hAY) (@hiLower) (@hiUpper)
      (@P) (@alpha) (@haPrefix) (@haTerminal) (@hSlen) (@ha) (@haOutside) (@haGood) (@hiEq)
      (@hXlen) (@hXB) (@hAX) (@hAXlt) (@hYXlen) (@hjaX) (@freshCard) (@usedStep) (@nineY)
private theorem helper_continuation_3823.{u_1, u_2} :
    helperContinuation3823Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hvertexMissing hnonempty j hj hpathLower
      hpathUpper finiteChoice componentData trans common A starEq hAT htail hlen B hBT hAB fullEq
      fullB elementary vertexMem firstLe firstAt firstFixed stageSwitch
  have lastData (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) :
      HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount) =
        HierarchyStoredColorsAt R.counterexample.hierarchy
          (Fin.last R.counterexample.hierarchy.dividerCount) ∧
      ∀ eta ∈ HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount),
        C.good.gamma (Fin.last C.hierarchy.dividerCount) eta =
          R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta :=
              by as_aux_lemma =>
    clear * - R
    obtain ⟨hcount, hdata⟩ := R.sameGood.2
    have hh := hdata (Fin.last C.hierarchy.dividerCount)
    have hidx : Fin.cast (congrArg (fun q => q + 1) hcount)
        (Fin.last C.hierarchy.dividerCount) =
        Fin.last R.counterexample.hierarchy.dividerCount := Fin.ext hcount
    simpa only [hidx] using hh
  have gammaTransport
      (R S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
      (eta : Fin k)
      (heta : eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy
        (Fin.last R.counterexample.hierarchy.dividerCount)) :
      eta ∈ HierarchyStoredColorsAt S.counterexample.hierarchy
        (Fin.last S.counterexample.hierarchy.dividerCount) ∧
      R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta =
        S.counterexample.good.gamma (Fin.last S.counterexample.hierarchy.dividerCount) eta := by
            as_aux_lemma =>
    clear * - R S eta heta lastData
    have hOrig : eta ∈ HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount) := by
      rw [(lastData R).1]; exact heta
    refine ⟨?_, ((lastData R).2 eta hOrig).symm.trans ((lastData S).2 eta hOrig)⟩
    rw [← (lastData S).1]
    exact hOrig
  have gammaUnused (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
      (eta a : Fin k)
      (heta : eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy
        (Fin.last R.counterexample.hierarchy.dividerCount))
      (ha : a ∈ R.counterexample.good.gamma
        (Fin.last R.counterexample.hierarchy.dividerCount) eta)
      (t : Fin T.length) (hlo : A.length ≤ t.val)
      (hhi : t.val < (HierarchyFirstMissingPosition R.coloring T eta).val) :
      R.coloring (T.edge t) ≠ some a := by as_aux_lemma =>
    clear * - R eta a heta ha t hlo hhi starEq
    intro hc
    have hnot := (Finset.mem_sdiff.mp (R.counterexample.good.avoidance
      (Fin.last R.counterexample.hierarchy.dividerCount) eta heta ha)).2
    apply hnot
    unfold HierarchySegmentColors
    dsimp only
    rw [starEq R, Fin.succ_last, R.counterexample.hierarchy.terminalStage]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, hlo,
      lt_min hhi t.isLt, hc⟩
  have outsideA (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
      (c : Fin k) (j : Fin (B.length + 1)) (hj : A.length < j.val)
      (hc : c ∈ MissingColors G R.coloring (B.vertex j)) :
      c ∉ TreeMissingColors R.coloring A := by as_aux_lemma =>
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
  have notRaw (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
      (c : Fin k) (hcA : c ∉ TreeMissingColors R.coloring A)
      (hcD : c ∉ HierarchyStoredColorsAt R.counterexample.hierarchy
        (Fin.last R.counterexample.hierarchy.dividerCount)) :
      c ∉ TashkinovStoredColors R.corresponding.replacementETT.series.data
        (Fin.last R.corresponding.replacementETT.rounds) := by as_aux_lemma =>
    clear * - R c hcA hcD starEq
    intro hm
    apply hcD
    unfold HierarchyStoredColorsAt
    dsimp only
    rw [starEq R]
    exact Finset.mem_sdiff.mpr ⟨hm, hcA⟩
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
          (Fin.last R.corresponding.replacementETT.rounds) := by as_aux_lemma =>
    clear * - R j hj hjlt c hc t hlo hhi hcol starEq hAT hBT fullEq fullB elementary vertexMem
    let U := HierarchyFullTailPrefix R.counterexample j
    have hUlen : U.length = A.length + j := by
      simp only [U, HierarchyFullTailPrefix, TreeSequencePrefix]
      rw [starEq R]
      exact min_eq_left (by have := hAT.1; omega)
    have hUT : TreeSequenceInitialSegment U T :=
      ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
    let u : Fin U.length := ⟨t.val, by rw [hUlen]; omega⟩
    have hut : Fin.castLE hUT.1 u = t := Fin.ext rfl
    have hcU : c ∈ MissingColors G R.coloring (U.vertex (Fin.last U.length)) := by
      dsimp only [U]
      rw [fullEq R]
      exact hc
    have hcolU : R.coloring (U.edge u) = some c := by
      rw [← hUT.2.2 u, hut]; exact hcol
    have hex := HierarchyTailMissingColorExclusion G k e0 R.corresponding.replacementInput T
      R.coloring R.corresponding.replacementETT R.replacementBase R.counterexample.hierarchy
      (by
        change ColoredVertexSetElementary G R.coloring (TreeSequenceVertexSet
          (HierarchyFullTailPrefix R.counterexample (HierarchyFullTailLength R.counterexample - 1)))
        rw [fullB R]
        exact elementary R)
      j hj (by
        rw [starEq R]
        exact hjlt) c hcU u
      (by
        change (HierarchyStarredStage R.counterexample.hierarchy
          (Fin.last R.counterexample.hierarchy.dividerCount)).length ≤ t.val
        rw [starEq R]
        exact hlo)
      (by
        change t.val < (HierarchyStarredStage R.counterexample.hierarchy
          (Fin.last R.counterexample.hierarchy.dividerCount)).length + j
        rw [starEq R]
        exact hhi) hcolU
    obtain ⟨hzero, hcore, hval, f, hstep, hkind, hedges, hedge, hcF, hstored⟩ := hex
    have hAval : t.val = A.length := by
      change u.val = _ at hval
      rw [starEq R] at hval
      exact hval
    have hAn : A = R.corresponding.replacementETT.series.data.tree
        (Fin.last R.corresponding.replacementETT.rounds).castSucc := by
      exact helper_hAn_999 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
          (@starEq) (@R) (@hzero) (@hcore)
    obtain ⟨i, hi⟩ := T.attaches t
    let a : Fin (A.length + 1) := ⟨i.val, by simpa only [hAval] using i.isLt⟩
    let old : Fin (T.length + 1) :=
      Fin.castLT i (Nat.lt_trans i.isLt (Nat.succ_lt_succ t.isLt))
    have ha : Fin.castLE (Nat.succ_le_succ hAT.1) a = old := Fin.ext rfl
    refine ⟨⟨T.vertex old, ?_, ?_⟩, hstored⟩
    · rw [← hAn, ← ha, hAT.2.1 a]
      exact vertexMem A a
    · rw [Incident, hi]
      exact Sym2.mem_mk_right _ _
  have coreA (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) :
      TreeSequenceInitialSegment R.replacementBase.core A := by as_aux_lemma =>
    clear * - R A starEq trans
    let H := R.counterexample.hierarchy
    have chain : ∀ (j : ℕ) (hj : j < H.dividerCount + 2)
        (i : Fin (H.dividerCount + 2)), i.val ≤ j →
        TreeSequenceInitialSegment (H.stage i) (H.stage ⟨j, hj⟩) := by
      intro j hj i hi
      exact H.stageInitialSegmentOfLE i ⟨j, hj⟩ hi
    rw [← starEq R]
    by_cases hq : H.dividerCount = 0
    · have he : HierarchyStarredStage H (Fin.last H.dividerCount) = R.replacementBase.core := by
        simp [HierarchyStarredStage, hq, Fin.last]
      rw [he]
      exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
    · apply helper_branch_1043 <;> assumption
  apply helper_continuation_3797 <;> assumption
private theorem helper_caseContinuation_5383.{u_1, u_2} :
    helperCaseContinuation5383Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx j trans common A starEq hlen B hBT hAB
      fullB vertexMem firstFixed R X hAX hAXlt hXB a b hne jb hjbX hb hw haUnused hbException
      gammaCut H q n Tn Dn hTnA stageCase hbB haB iaLe ibEq ja jaEq jbEq haFirstB hprefixR
      hmissingR change hdis hpath hmissing sigma hsone
  have hcase :
      (0 < H.dividerCount ∧ a ∈ TreeMissingColors R.coloring (H.stage ⟨H.dividerCount, by
          omega⟩)) ∨
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
  have hweak : HierarchyWeaklyStable H q sigma := changed.1
  have baseStable : if R.corresponding.replacementETT.series.data.kind n =
      some TashkinovExtensionKind.PE then
      CombinedStableColoring Tn R.replacementBase.closure Dn R.coloring sigma
    else StableColoring Tn Dn R.coloring sigma := by
    exact helper_baseStable_716 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
        (@j) (@R) (@a) (@b) (@hweak)
  have stable : StableColoring Tn Dn R.coloring sigma := by
    by_cases hp : R.corresponding.replacementETT.series.data.kind n = some
        TashkinovExtensionKind.PE
    · exact (ite_eq_left hp ▸ baseStable).1
    · simpa only [hp, ite_false] using baseStable
  have fixedA : ∀ t : Fin A.length, sigma (A.edge t) = R.coloring (A.edge t) := by
    exact helper_fixedA_730 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
        (@j) (@starEq) (@hlen) (@hBT) (@hAB) (@R) (@X) (@a) (@b) (@jb) (@iaLe) (@change)
        (@hsone) (@hweak) (@baseStable)
  have fixedPrefix : ∀ t : Fin T.length, A.length ≤ t.val → t.val < X.length →
      sigma (T.edge t) = R.coloring (T.edge t) := by
    exact helper_fixedPrefix_750 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@ctx) (@R) (@X) (@a) (@b) (@haUnused) (@hbException) (@stable)
  have hXT := trans hXB hBT
  let XM := TreeSequencePrefix X (X.length - 1) (by have := A.positive; omega) (by omega)
  have hXMX : TreeSequenceInitialSegment XM X :=
    ⟨by dsimp [XM, TreeSequencePrefix]; omega, fun _ => rfl, fun _ => rfl⟩
  have prefixFixed (t : Fin X.length) (ht : Tn.length ≤ t.val) :
      sigma (X.edge t) = R.coloring (X.edge t) := by
    exact helper_prefixFixed_762 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@ctx) (@j) (@hlen) (@hBT) (@hAB) (@R) (@X) (@hAX) (@a) (@b) (@jb) (@iaLe) (@change)
        (@fixedA) (@fixedPrefix) (@hXT) (@t)
  have routes :
      ((R.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence sigma Tn X) ∨
      ((R.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.SE ∨
        R.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.RE) ∧
        ∃ f seed, R.corresponding.replacementETT.series.data.connectingEdges n = {f} ∧
          TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence sigma seed X)) ∧
      TashkinovAugmentationSequence R.coloring X T := by
    apply helper_routes_771 <;> assumption
  have hsplit : a ∈ TreeMissingColors sigma X ∧ b ∈ TreeMissingColors sigma X := by
    exact helper_hsplit_801 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
        (@j) (@hlen) (@hBT) (@hAB) (@vertexMem) (@R) (@X) (@hAXlt) (@hXB) (@a) (@b) (@jb)
        (@hjbX) (@hb) (@iaLe) (@jaEq) (@haFirstB) (@hmissing)
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
    apply helper_hnotElementary_829 <;> assumption
  let CS : HierarchyCounterexample bs := by
    exact @helperCS778 (@V) (@E) inferInstance inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@R) (@a) (@b) (@corr)
        (@hmaximum) (@bs) (@K) (@goodK) (@hnotElementary)
  obtain ⟨S, hS⟩ := HierarchyReplacementPresentationTrans G k e0 input T phi ett base C ctx
    R sigma corr bs CS hsameGood
  refine ⟨S, ?_, ?_, ?_, ?_⟩ <;> rw [hS]
  · exact hmissing
  · exact fixedPrefix
  · exact hterminalA
  · exact hterminalB

private theorem helper_continuation_3692.{u_1, u_2} :
    helperContinuation3692Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hvertexMissing hnonempty j hj hpathLower
      hpathUpper finiteChoice componentData trans common A starEq hAT htail hlen B hBT hAB fullEq
      fullB elementary vertexMem firstLe firstMem firstAt firstFixed
  have stageSwitch (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
      (X : TreeSequence G e0) (hAX : TreeSequenceInitialSegment A X)
      (hAXlt : A.length < X.length) (hXB : TreeSequenceInitialSegment X B)
      (a b : Fin k) (hne : a ≠ b)
      (haStage : a ∈ HierarchyStageMissingColors R.counterexample.hierarchy
        (Fin.last R.counterexample.hierarchy.dividerCount))
      (jb : Fin (B.length + 1))
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
            (Fin.last R.corresponding.replacementETT.rounds))
      (gammaCut : ∀ eta, eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy
        (Fin.last R.counterexample.hierarchy.dividerCount) →
        (a ∈ R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta ∨
          b ∈ R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta) →
          (HierarchyFirstMissingPosition R.coloring T eta).val ≤ X.length) :
      ∃ S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx,
        (∀ v ∈ TreeSequenceVertexSet B,
          MissingColors G S.coloring v = MissingColors G R.coloring v) ∧
        (∀ t : Fin T.length, A.length ≤ t.val → t.val < X.length →
          S.coloring (T.edge t) = R.coloring (T.edge t)) ∧
        (a ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)) →
          b ∈ MissingColors G S.coloring (T.vertex (Fin.last T.length))) ∧
        (b ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)) →
          a ∈ MissingColors G S.coloring (T.vertex (Fin.last T.length))) := by as_aux_lemma =>
    clear * - G T A B R X hAX hAXlt hXB a b hne haStage jb hjbX hb hw
      haUnused hbException gammaCut trans common starEq hAT hAB hBT elementary vertexMem firstLe
      firstMem firstAt firstFixed componentData fullB
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
      exact helper_lastPositive_528 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
          (@ctx) (@j) (@hlen) (@R) (@X) (@jb) (@hq)
    have hTnCore : TreeSequenceInitialSegment Tn R.replacementBase.core := by
      exact helper_hTnCore_537 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@R)
    have coreA : TreeSequenceInitialSegment R.replacementBase.core A := by
      apply helper_coreA_543 <;> assumption
    have hTnA := trans hTnCore coreA
    have stageCase :
        (0 < H.dividerCount ∧ a ∈ TreeMissingColors R.coloring
          (H.stage ⟨H.dividerCount, by omega⟩)) ∨
        (H.dividerCount = 0 ∧ a ∈ TreeMissingColors R.coloring Tn) := by
      exact helper_stageCase_554 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
          (@j) (@hlen) (@R) (@X) (@a) (@haStage) (@jb)
    have haA : a ∈ TreeMissingColors R.coloring A := by
      exact helper_haA_574 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@j)
          (@starEq) (@hlen) (@R) (@X) (@a) (@jb) (@lastPositive) (@hTnA) (@stageCase)
    have hbB : b ∈ TreeMissingColors R.coloring B :=
      Finset.mem_biUnion.mpr ⟨B.vertex jb, vertexMem B jb, hb⟩
    have haB : a ∈ TreeMissingColors R.coloring B := by
      obtain ⟨v, hv, hc⟩ := Finset.mem_biUnion.mp haA
      exact Finset.mem_biUnion.mpr ⟨v, TreeSequenceInitialSegmentVertexSetSubset hAB hv, hc⟩
    have iaLe : (HierarchyFirstMissingPosition R.coloring T a).val ≤ A.length := by
      exact helper_iaLe_586 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@j)
          (@hAT) (@hlen) (@firstLe) (@R) (@X) (@a) (@jb) (@haA)
    have ibEq := firstAt R b jb hb
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
        intro hout
        have hbOut : b ∉ TreeMissingColors R.coloring A := by
          rcases hout with h | h
          · exact (h haA).elim
          · exact h
        have hjb : A.length < jb.val := by
          exact helper_hjb_641 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
              (@j) (@hlen) (@hBT) (@hAB) (@vertexMem) (@R) (@X) (@a) (@b) (@jb) (@hb) (@iaLe)
              (@ibEq) (@jbEq) (@hbOut)
        exact ⟨⟨_, _, rfl, rfl, by omega⟩, hunused⟩)
    have hsame : TwoColorComponent G R.coloring a b (Sum.inl (B.vertex ja)) =
        TwoColorComponent G R.coloring a b (Sum.inl (B.vertex jb)) := by
      exact helper_hsame_650 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@j)
          (@hlen) (@hBT) (@hAB) (@R) (@X) (@a) (@b) (@jb) (@stageCase) (@iaLe) (@jaEq) (@jbEq)
          (@change)
    obtain ⟨hdis, hpath, hmissing⟩ := componentData R.coloring a b hne
      R.minimumContext.proper (TreeSequenceVertexSet B) (elementary R)
      (B.vertex ja) (B.vertex jb) (T.vertex (Fin.last T.length))
      (vertexMem B ja) (vertexMem B jb)
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
      exact SharedFacts.TerminalKempeStageSwitch.hsone (@G) (@k) (@e0) (@input) (@T) (@phi)
          (@ett) (@base) (@C) (@ctx) (@R)
          (@a) (@b) (@hne)
    exact @helper_caseContinuation_5383 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@j)
        (@trans) (@common) (@starEq) (@hlen) (@hBT) (@hAB) (@fullB) (@vertexMem) (@firstFixed)
        (@R) (@X) (@hAX) (@hAXlt) (@hXB) (@a) (@b) (@hne) (@jb) (@hjbX) (@hb) (@hw) (@haUnused)
        (@hbException) (@gammaCut) (@hTnA) (@stageCase) (@hbB) (@haB) (@iaLe) (@ibEq) (@jaEq)
        (@jbEq) (@haFirstB) (@hprefixR) (@hmissingR) (@change) (@hdis) (@hpath) (@hmissing) (@hsone)
  apply helper_continuation_3823 <;> assumption
theorem HierarchySituationThreeClaimJMinusOneNonempty {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (hpathLower : 2 ≤ HierarchyPathNumber C.hierarchy)
    (hpathUpper :
      HierarchyPathNumber C.hierarchy < HierarchyFullTailLength C)
    (hvertexMissing : ∀ (mu : PartialEdgeColoring E k),
      IsProperEdgeColoring G mu → IsOneEdgeUncolored mu e0 →
        ∀ v : V, (MissingColors G mu v).Nonempty)
    (hnonempty : (HierarchyEligibleCommonMissingIndices
      G k e0 input T phi ett base C ctx).Nonempty) :
    ∃ P : HierarchyReplacementPresentation
        G k e0 input T phi ett base C ctx,
      ∃ alpha : Fin k,
        let H := P.counterexample.hierarchy
        let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
        let n : Fin (P.corresponding.replacementETT.rounds + 1) :=
          Fin.last P.corresponding.replacementETT.rounds
        let Tn := P.corresponding.replacementETT.series.data.tree n.castSucc
        let B := HierarchyFullTailPrefix C
          (HierarchyPathNumber C.hierarchy - 2)
        let D := HierarchyStoredColorsAt H q
        let Gamma := D.biUnion (P.counterexample.good.gamma q)
        let baseExtraMissing :=
          ((TreeSequenceVertexSet P.replacementBase.core \
              TreeSequenceVertexSet Tn).biUnion
            fun v => MissingColors G P.coloring v)
        alpha ∈ MissingColors G P.coloring
            (T.vertex (Fin.last T.length)) ∧
          alpha ∈ TreeMissingColors P.coloring B ∧
          (alpha ∉ Gamma ∪ baseExtraMissing ∨
            ∃ eta : Fin k, eta ∈ D ∧
              alpha ∈ P.counterexample.good.gamma q eta ∧
              (HierarchyFirstMissingPosition P.coloring T eta).val ≤
                B.length) := by
  classical
  generalize hj : HierarchyPathNumber C.hierarchy = j at hpathLower hpathUpper ⊢
  have finiteChoice (M F D U W N : Finset (Fin k)) (g : Fin k → Finset (Fin k))
      (hstep : W ⊆ U ∪ N) (hncard : N.card ≤ 1)
      (hgM : ∀ eta ∈ D, g eta ⊆ M)
      (hgcard : ∀ eta ∈ D, (g eta).card = 2)
      (hgdis : ∀ eta ∈ D, ∀ theta ∈ D, eta ≠ theta → Disjoint (g eta) (g theta))
      (hgd : Disjoint (D.biUnion g) D)
      (hnine : (((M \ F) \ U) \ (D.biUnion g ∪ D)).card ≤ 4 →
        ∃ eta : Fin 7 → Fin k, Function.Injective eta ∧
          ∀ h, eta h ∈ D ∧ eta h ∈ M ∧ Disjoint (g (eta h) ∪ {eta h}) U) :
      ∃ beta, beta ∈ M ∧ beta ∉ D ∧ beta ∉ W ∧
        (beta ∉ D.biUnion g ∪ F ∨
          ∃ eta, eta ∈ D ∧ beta ∈ g eta ∧ eta ∈ M) := by as_aux_lemma =>
    clear * - M F D U W N g hstep hncard hgM hgcard hgdis hgd hnine
    let free := ((M \ F) \ U) \ (D.biUnion g ∪ D)
    by_cases hlarge : 5 ≤ free.card
    · apply helper_branch_237 <;> assumption
    · apply helper_branch_256 <;> assumption
  have componentData := P2905_T2_ElementaryTerminalComponent (k := k) G
  have trans {X Y Z : TreeSequence G e0}
      (hXY : TreeSequenceInitialSegment X Y)
      (hYZ : TreeSequenceInitialSegment Y Z) :
      TreeSequenceInitialSegment X Z := by as_aux_lemma =>
    clear * - hXY hYZ
    refine ⟨hXY.1.trans hYZ.1, ?_, ?_⟩
    · intro i
      exact (hYZ.2.1 (Fin.castLE (Nat.succ_le_succ hXY.1) i)).trans (hXY.2.1 i)
    · intro i
      exact (hYZ.2.2 (Fin.castLE hXY.1 i)).trans (hXY.2.2 i)
  have common {X Y Z : TreeSequence G e0}
      (hXZ : TreeSequenceInitialSegment X Z)
      (hYZ : TreeSequenceInitialSegment Y Z) (hXY : X.length ≤ Y.length) :
      TreeSequenceInitialSegment X Y := by as_aux_lemma =>
    clear * - hXZ hYZ hXY
    refine ⟨hXY, ?_, ?_⟩
    · intro i
      exact (hYZ.2.1 (Fin.castLE (Nat.succ_le_succ hXY) i)).symm.trans (hXZ.2.1 i)
    · intro i
      exact (hYZ.2.2 (Fin.castLE hXY i)).symm.trans (hXZ.2.2 i)
  have sameLast :
    ∀ {a b : ℕ} (s : Fin (a + 2) → TreeSequence G e0) (t : Fin (b + 2) → TreeSequence G e0) (u v :
        TreeSequence G e0), a = b → HEq s t → u = v → Fin.cases (motive := fun _ => TreeSequence G
        e0) u (fun i : Fin a => s i.castSucc.succ) (Fin.last a) = Fin.cases (motive := fun _ =>
        TreeSequence G e0) v (fun i : Fin b => t i.castSucc.succ) (Fin.last b) := by as_aux_lemma =>
    clear * -
    intro a b s t u v hab hst huv
    cases hab
    have he : s = t := eq_of_heq hst
    cases he
    cases huv
    rfl
  let A := HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)
  have starEq (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) :
      HierarchyStarredStage R.counterexample.hierarchy
        (Fin.last R.counterexample.hierarchy.dividerCount) = A :=
    (sameLast _ _ _ _ R.sameGood.1.2.1 R.sameGood.1.2.2.1 R.sameGood.1.1).symm
  have hAT : TreeSequenceInitialSegment A T := by
    exact C.hierarchy.lastStarredInitialSegment
  have htail : 3 ≤ T.length - A.length := by
    change j < T.length - A.length at hpathUpper
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
    exact SharedFacts.ReplacementPrefixes.penultimatePrefixEquality (@G) (@k) (@e0) (@input) (@T)
        (@phi) (@ett) (@base) (@C) (@ctx) (@j)
        (@starEq) (@htail) (@hlen) (@R)
  have elementary (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) :
      ColoredVertexSetElementary G R.coloring (TreeSequenceVertexSet B) := by
    exact SharedFacts.ReplacementPrefixes.penultimatePrefixElementary (@G) (@k) (@e0) (@input) (@T)
        (@phi) (@ett) (@base) (@C) (@ctx)
        (@j) (@hlen) (@fullB) (@R)
  have vertexMem (U : TreeSequence G e0) (j : Fin (U.length + 1)) :
      U.vertex j ∈ TreeSequenceVertexSet U := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨j, rfl⟩
  have firstLe (psi : PartialEdgeColoring E k) (c : Fin k)
      (j : Fin (T.length + 1)) (hj : c ∈ MissingColors G psi (T.vertex j)) :
      HierarchyFirstMissingPosition psi T c ≤ j := by as_aux_lemma =>
    clear * - G T psi c j hj
    let candidates := Finset.univ.filter fun j : Fin (T.length + 1) =>
      c ∈ MissingColors G psi (T.vertex j)
    have hm : j ∈ candidates := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
    have hn : candidates.Nonempty := ⟨j, hm⟩
    unfold HierarchyFirstMissingPosition
    rw [dite_eq_left hn]
    exact Finset.min'_le candidates j hm
  have firstMem (psi : PartialEdgeColoring E k) (c : Fin k)
      (hlt : (HierarchyFirstMissingPosition psi T c).val < T.length) :
      c ∈ MissingColors G psi (T.vertex (HierarchyFirstMissingPosition psi T c)) := by
          as_aux_lemma =>
    clear * - G T psi c hlt
    let candidates := Finset.univ.filter fun j : Fin (T.length + 1) =>
      c ∈ MissingColors G psi (T.vertex j)
    by_cases hn : candidates.Nonempty
    · unfold HierarchyFirstMissingPosition
      rw [dite_eq_left hn]
      exact (Finset.mem_filter.mp (Finset.min'_mem candidates hn)).2
    · exact helper_branch_410 (@G) (@k) (@e0) (@T) (@psi) (@c) (@hlt) (@hn)
  have firstAt (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
      (c : Fin k) (j : Fin (B.length + 1))
      (hc : c ∈ MissingColors G R.coloring (B.vertex j)) :
      (HierarchyFirstMissingPosition R.coloring T c).val = j.val := by as_aux_lemma =>
    clear * - G T B R c j hc elementary vertexMem firstLe firstMem hBT
    have hcT : c ∈ MissingColors G R.coloring
        (T.vertex (Fin.castLE (Nat.succ_le_succ hBT.1) j)) := by
      rw [hBT.2.1 j]; exact hc
    have hle := firstLe R.coloring c _ hcT
    have hlt : (HierarchyFirstMissingPosition R.coloring T c).val < T.length := by
      have := j.isLt
      change (HierarchyFirstMissingPosition R.coloring T c).val ≤ j.val at hle
      have hblen : B.length = T.length - 1 := rfl
      omega
    let x : Fin (B.length + 1) := ⟨(HierarchyFirstMissingPosition R.coloring T c).val, by
      change (HierarchyFirstMissingPosition R.coloring T c).val ≤ j.val at hle
      omega⟩
    have hxT : Fin.castLE (Nat.succ_le_succ hBT.1) x =
        HierarchyFirstMissingPosition R.coloring T c := Fin.ext rfl
    have hcx : c ∈ MissingColors G R.coloring (B.vertex x) := by
      rw [← hBT.2.1 x, hxT]
      exact firstMem R.coloring c hlt
    have he : B.vertex x = B.vertex j := by
      by_contra hn
      exact Finset.disjoint_left.mp (elementary R (vertexMem B x) (vertexMem B j) hn) hcx hc
    exact congrArg Fin.val (B.vertex_injective he)
  have firstFixed (psi tau : PartialEdgeColoring E k)
      (hmissing : ∀ v ∈ TreeSequenceVertexSet B,
        MissingColors G tau v = MissingColors G psi v) (c : Fin k) :
      HierarchyFirstMissingPosition tau T c = HierarchyFirstMissingPosition psi T c := by
          as_aux_lemma =>
    clear * - G T B psi tau hmissing c firstLe firstMem hBT vertexMem
    have early (j : Fin (T.length + 1)) (hj : j.val < T.length) :
        MissingColors G tau (T.vertex j) = MissingColors G psi (T.vertex j) := by
      let x : Fin (B.length + 1) := ⟨j.val, by dsimp [B, TreeSequencePrefix]; omega⟩
      have hx : Fin.castLE (Nat.succ_le_succ hBT.1) x = j := Fin.ext rfl
      rw [← hx, hBT.2.1 x]
      exact hmissing _ (vertexMem B x)
    apply Fin.ext
    apply Nat.le_antisymm
    · exact helper_branch_454 (@G) (@k) (@e0) (@T) (@firstLe) (@firstMem) (@psi) (@tau) (@c)
        (@early)
    · exact helper_branch_462 (@G) (@k) (@e0) (@T) (@firstLe) (@firstMem) (@psi) (@tau) (@c)
        (@early)
  exact helper_continuation_3692 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
      (@hvertexMissing) (@hnonempty) (@j) (@hj) (@hpathLower) (@hpathUpper) (@finiteChoice)
      (@componentData) (@trans) (@common) (@starEq) (@hAT) (@htail) (@hlen) (@hBT) (@hAB)
      (@fullEq) (@fullB) (@elementary) (@vertexMem) (@firstLe) (@firstMem) (@firstAt) (@firstFixed)
end GoldbergSeymour

end
