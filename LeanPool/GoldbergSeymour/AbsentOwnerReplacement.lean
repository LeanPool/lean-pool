/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyTreeFacts

public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentFacts

public import LeanPool.GoldbergSeymour.TreeSequenceColoringFacts

public import LeanPool.GoldbergSeymour.TreeSequenceFirstMissingPositionInvariant

public import LeanPool.GoldbergSeymour.StableChangeCasesOneTwoFullTail
public import LeanPool.GoldbergSeymour.ChangeLemma
public import LeanPool.GoldbergSeymour.NineN
public import LeanPool.GoldbergSeymour.HierarchyReplacementPresentationTrans
public import LeanPool.GoldbergSeymour.ElementaryTerminalComponent

/-!
# P2905_T2_Absent Owner Replacement

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev helperHbetaExists392Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength C;
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
    let Tn : TreeSequence G e0 := ett.series.data.tree (Fin.last ett.rounds).castSucc;
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let Gamma : Finset (Fin k) := D.biUnion (C.good.gamma q);
    let M0 : Finset (Fin k) := (TreeSequenceVertexSet base.core \ TreeSequenceVertexSet
        Tn).biUnion fun (v : V) ↦ MissingColors G phi v;
    ∀ (htailA : (3 : ℕ) ≤ T.length - A.length) (hell : ell = T.length - A.length),
        TreeSequenceVertexSet base.core ⊆ TreeSequenceVertexSet A →
    ∀ (hNine : (2 : ℕ) * ett.rounds + (11 : ℕ) ≤ ((fun (i : ℕ) ↦ (TreeMissingColors phi ((fun (i :
        ℕ) ↦ TreeSequencePrefix T (min ((HierarchyStarredStage H (Fin.last H.dividerCount)).length
        + i) T.length) (
    by
                   have := GoldbergSeymour.TreeSequence.positive T
                   have :=
                    GoldbergSeymour.TreeSequence.positive
                     (HierarchyStarredStage H (Fin.last H.dividerCount))
                   have := GoldbergSeymour.TreeSequence.positive T
                   omega
    ) (
    by
                   have := GoldbergSeymour.TreeSequence.positive T
                   have :=
                    GoldbergSeymour.TreeSequence.positive
                     (HierarchyStarredStage H (Fin.last H.dividerCount))
                   have := GoldbergSeymour.TreeSequence.positive T
                   omega
    )) i) \ (TreeSequenceVertexSet base.core \ TreeSequenceVertexSet (ett.series.data.tree
        (Fin.last ett.rounds).castSucc)).biUnion fun (v : V) ↦ MissingColors G phi v) \ (fun (i :
        ℕ) ↦ ({c : Fin k |
    ∃ (r : Fin T.length), (HierarchyStarredStage H (Fin.last H.dividerCount)).length ≤ (↑r : ℕ) ∧
        (↑r : ℕ) < (HierarchyStarredStage H (Fin.last H.dividerCount)).length + i ∧ phi (T.edge r)
        = some c} : Finset (Fin k))) i) (ell - (2 : ℕ))).card ∧ (((fun (i : ℕ) ↦
        (TreeMissingColors phi ((fun (i : ℕ) ↦ TreeSequencePrefix T (min ((HierarchyStarredStage H
        (Fin.last H.dividerCount)).length + i) T.length) (
    by
                     have := GoldbergSeymour.TreeSequence.positive T
                     have :=
                      GoldbergSeymour.TreeSequence.positive
                       (HierarchyStarredStage H (Fin.last H.dividerCount))
                     have := GoldbergSeymour.TreeSequence.positive T
                     omega
    ) (
    by
                     have := GoldbergSeymour.TreeSequence.positive T
                     have :=
                      GoldbergSeymour.TreeSequence.positive
                       (HierarchyStarredStage H (Fin.last H.dividerCount))
                     have := GoldbergSeymour.TreeSequence.positive T
                     omega
    )) i) \ (TreeSequenceVertexSet base.core \ TreeSequenceVertexSet (ett.series.data.tree
        (Fin.last ett.rounds).castSucc)).biUnion fun (v : V) ↦ MissingColors G phi v) \ (fun (i :
        ℕ) ↦ ({c : Fin k |
    ∃ (r : Fin T.length), (HierarchyStarredStage H (Fin.last H.dividerCount)).length ≤ (↑r : ℕ) ∧
        (↑r : ℕ) < (HierarchyStarredStage H (Fin.last H.dividerCount)).length + i ∧ phi (T.edge r)
        = some c} : Finset (Fin k))) i) (ell - (2 : ℕ)) \ ((HierarchyStoredColorsAt H (Fin.last
        H.dividerCount)).biUnion (C.good.gamma (Fin.last H.dividerCount)) ∪
        HierarchyStoredColorsAt H (Fin.last H.dividerCount))).card ≤ (4 : ℕ) →
    ∃ (eta : Fin (7 : ℕ) → Fin k), Function.Injective eta ∧
    ∀ (h : Fin (7 : ℕ)), eta h ∈ HierarchyStoredColorsAt H (Fin.last H.dividerCount) ∧ eta h ∈
        TreeMissingColors phi ((fun (i : ℕ) ↦ TreeSequencePrefix T (min ((HierarchyStarredStage H
        (Fin.last H.dividerCount)).length + i) T.length) (
    by
                    have := GoldbergSeymour.TreeSequence.positive T
                    have :=
                     GoldbergSeymour.TreeSequence.positive
                      (HierarchyStarredStage H (Fin.last H.dividerCount))
                    have := GoldbergSeymour.TreeSequence.positive T
                    omega
    ) (
    by
                    have := GoldbergSeymour.TreeSequence.positive T
                    have :=
                     GoldbergSeymour.TreeSequence.positive
                      (HierarchyStarredStage H (Fin.last H.dividerCount))
                    have := GoldbergSeymour.TreeSequence.positive T
                    omega
    )) (ell - (2 : ℕ))) ∧ Disjoint (C.good.gamma (Fin.last H.dividerCount) (eta h) ∪ ({eta h} :
        Finset (Fin k))) ((fun (i : ℕ) ↦ ({c : Fin k |
    ∃ (r : Fin T.length), (HierarchyStarredStage H (Fin.last H.dividerCount)).length ≤ (↑r : ℕ) ∧
        (↑r : ℕ) < (HierarchyStarredStage H (Fin.last H.dividerCount)).length + i ∧ phi (T.edge r)
        = some c} : Finset (Fin k))) (ell - (2 : ℕ))))),
    let U : Finset (Fin k) := ({c : Fin k |
    ∃ (r : Fin T.length), A.length ≤ (↑r : ℕ) ∧ (↑r : ℕ) < A.length + (ell - (2 : ℕ)) ∧ phi
        (T.edge r) = some c} : Finset (Fin k));
    let Avail : Finset (Fin k) := (TreeMissingColors phi X \ M0) \ U;
    ∀ (hNineAt hNi : (2 : ℕ) * ett.rounds + (11 : ℕ) ≤ ((TreeMissingColors phi (TreeSequencePrefix
        T (min ((HierarchyStarredStage H (Fin.last H.dividerCount)).length + (T.length -
        (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length - (2 : ℕ)))
        T.length) (
    by
                have := GoldbergSeymour.TreeSequence.positive T
                have :=
                 GoldbergSeymour.TreeSequence.positive
                  (HierarchyStarredStage H (Fin.last H.dividerCount))
                have := GoldbergSeymour.TreeSequence.positive T
                have :=
                 GoldbergSeymour.TreeSequence.positive
                  (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount))
                omega
    ) (
    by
                have := GoldbergSeymour.TreeSequence.positive T
                have :=
                 GoldbergSeymour.TreeSequence.positive
                  (HierarchyStarredStage H (Fin.last H.dividerCount))
                have := GoldbergSeymour.TreeSequence.positive T
                have :=
                 GoldbergSeymour.TreeSequence.positive
                  (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount))
                omega
    )) \ (TreeSequenceVertexSet base.core \ TreeSequenceVertexSet (ett.series.data.tree (Fin.last
        ett.rounds).castSucc)).biUnion fun (v : V) ↦ MissingColors G phi v) \ ({c : Fin k |
    ∃ (r : Fin T.length), (HierarchyStarredStage H (Fin.last H.dividerCount)).length ≤ (↑r : ℕ) ∧
        (↑r : ℕ) < (HierarchyStarredStage H (Fin.last H.dividerCount)).length + (T.length -
        (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length - (2 : ℕ))
        ∧ phi (T.edge r) = some c} : Finset (Fin k))).card ∧ ((((TreeMissingColors phi
        (TreeSequencePrefix T (min ((HierarchyStarredStage H (Fin.last H.dividerCount)).length +
        (T.length - (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length
        - (2 : ℕ))) T.length) (
    by
                  have := GoldbergSeymour.TreeSequence.positive T
                  have :=
                   GoldbergSeymour.TreeSequence.positive
                    (HierarchyStarredStage H (Fin.last H.dividerCount))
                  have := GoldbergSeymour.TreeSequence.positive T
                  have :=
                   GoldbergSeymour.TreeSequence.positive
                    (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount))
                  omega
    ) (
    by
                  have := GoldbergSeymour.TreeSequence.positive T
                  have :=
                   GoldbergSeymour.TreeSequence.positive
                    (HierarchyStarredStage H (Fin.last H.dividerCount))
                  have := GoldbergSeymour.TreeSequence.positive T
                  have :=
                   GoldbergSeymour.TreeSequence.positive
                    (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount))
                  omega
    )) \ (TreeSequenceVertexSet base.core \ TreeSequenceVertexSet (ett.series.data.tree (Fin.last
        ett.rounds).castSucc)).biUnion fun (v : V) ↦ MissingColors G phi v) \ ({c : Fin k |
    ∃ (r : Fin T.length), (HierarchyStarredStage H (Fin.last H.dividerCount)).length ≤ (↑r : ℕ) ∧
        (↑r : ℕ) < (HierarchyStarredStage H (Fin.last H.dividerCount)).length + (T.length -
        (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length - (2 : ℕ))
        ∧ phi (T.edge r) = some c} : Finset (Fin k))) \ ((HierarchyStoredColorsAt H (Fin.last
        H.dividerCount)).biUnion (C.good.gamma (Fin.last H.dividerCount)) ∪
        HierarchyStoredColorsAt H (Fin.last H.dividerCount))).card ≤ (4 : ℕ) →
    ∃ (eta : Fin (7 : ℕ) → Fin k), Function.Injective eta ∧
    ∀ (h : Fin (7 : ℕ)), eta h ∈ HierarchyStoredColorsAt H (Fin.last H.dividerCount) ∧ eta h ∈
        TreeMissingColors phi (TreeSequencePrefix T (min ((HierarchyStarredStage H (Fin.last
        H.dividerCount)).length + (T.length - (HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount)).length - (2 : ℕ))) T.length) (
    by
                   have := GoldbergSeymour.TreeSequence.positive T
                   have :=
                    GoldbergSeymour.TreeSequence.positive
                     (HierarchyStarredStage H (Fin.last H.dividerCount))
                   have := GoldbergSeymour.TreeSequence.positive T
                   have :=
                    GoldbergSeymour.TreeSequence.positive
                     (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount))
                   omega
    ) (
    by
                   have := GoldbergSeymour.TreeSequence.positive T
                   have :=
                    GoldbergSeymour.TreeSequence.positive
                     (HierarchyStarredStage H (Fin.last H.dividerCount))
                   have := GoldbergSeymour.TreeSequence.positive T
                   have :=
                    GoldbergSeymour.TreeSequence.positive
                     (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount))
                   omega
    )) ∧ Disjoint (C.good.gamma (Fin.last H.dividerCount) (eta h) ∪ ({eta h} : Finset (Fin k)))
        ({c : Fin k |
    ∃ (r : Fin T.length), (HierarchyStarredStage H (Fin.last H.dividerCount)).length ≤ (↑r : ℕ) ∧
        (↑r : ℕ) < (HierarchyStarredStage H (Fin.last H.dividerCount)).length + (T.length -
        (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length - (2 : ℕ))
        ∧ phi (T.edge r) = some c} : Finset (Fin k)))), Disjoint Gamma D →
    let r0 : Fin T.length := (⟨T.length - (2 : ℕ),
    have this : (3 : ℕ) ≤ T.length - A.length := htailA; Decidable.byContradiction fun (a :
        ¬T.length - (2 : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length);
    let r1 : Fin T.length := (⟨T.length - (1 : ℕ),
    have this : (3 : ℕ) ≤ T.length - A.length := htailA; Decidable.byContradiction fun (a :
        ¬T.length - (1 : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length);
    let N : Finset (Fin k) := (phi (T.edge r0)).toList.toFinset ∪ (phi (T.edge
        r1)).toList.toFinset; N.card ≤ (2 : ℕ) →
    let Free : Finset (Fin k) := Avail \ (Gamma ∪ D); ((Avail \ (Gamma ∪ D)).card ≤ (4 : ℕ) →
    ∃ (rho : Fin (7 : ℕ) → Fin k), Function.Injective rho ∧
    ∀ (i : Fin (7 : ℕ)), rho i ∈ D ∧ rho i ∈ TreeMissingColors phi X ∧ Disjoint (C.good.gamma q
        (rho i) ∪ ({rho i} : Finset (Fin k))) U) →
    ∃ beta ∈ TreeMissingColors phi X, beta ∉ M0 ∧ beta ∉ Gamma ∧ beta ∉ U ∧ beta ∉ N

private abbrev helperHibLt530Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (alpha :
        Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength C;
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
    ∀ (htailA : (3 : ℕ) ≤ T.length - A.length) (hell : ell = T.length - A.length) (hXprefix :
        TreeSequenceInitialSegment X T), X.length = T.length - (2 : ℕ) →
    ∀ (hNine : (2 : ℕ) * ett.rounds + (11 : ℕ) ≤ ((fun (i : ℕ) ↦ (TreeMissingColors phi ((fun (i :
        ℕ) ↦ TreeSequencePrefix T (min ((HierarchyStarredStage H (Fin.last H.dividerCount)).length
        + i) T.length) (
    by
                   have := GoldbergSeymour.TreeSequence.positive T
                   have := hXprefix.1
                   have :=
                    GoldbergSeymour.TreeSequence.positive
                     (HierarchyStarredStage H (Fin.last H.dividerCount))
                   have := GoldbergSeymour.TreeSequence.positive T
                   omega
    ) (
    by
                   have := GoldbergSeymour.TreeSequence.positive T
                   have := hXprefix.1
                   have :=
                    GoldbergSeymour.TreeSequence.positive
                     (HierarchyStarredStage H (Fin.last H.dividerCount))
                   have := GoldbergSeymour.TreeSequence.positive T
                   omega
    )) i) \ (TreeSequenceVertexSet base.core \ TreeSequenceVertexSet (ett.series.data.tree
        (Fin.last ett.rounds).castSucc)).biUnion fun (v : V) ↦ MissingColors G phi v) \ (fun (i :
        ℕ) ↦ ({c : Fin k |
    ∃ (r : Fin T.length), (HierarchyStarredStage H (Fin.last H.dividerCount)).length ≤ (↑r : ℕ) ∧
        (↑r : ℕ) < (HierarchyStarredStage H (Fin.last H.dividerCount)).length + i ∧ phi (T.edge r)
        = some c} : Finset (Fin k))) i) (ell - (2 : ℕ))).card ∧ (((fun (i : ℕ) ↦
        (TreeMissingColors phi ((fun (i : ℕ) ↦ TreeSequencePrefix T (min ((HierarchyStarredStage H
        (Fin.last H.dividerCount)).length + i) T.length) (
    by
                     have := GoldbergSeymour.TreeSequence.positive T
                     have := hXprefix.1
                     have :=
                      GoldbergSeymour.TreeSequence.positive
                       (HierarchyStarredStage H (Fin.last H.dividerCount))
                     have := GoldbergSeymour.TreeSequence.positive T
                     omega
    ) (
    by
                     have := GoldbergSeymour.TreeSequence.positive T
                     have := hXprefix.1
                     have :=
                      GoldbergSeymour.TreeSequence.positive
                       (HierarchyStarredStage H (Fin.last H.dividerCount))
                     have := GoldbergSeymour.TreeSequence.positive T
                     omega
    )) i) \ (TreeSequenceVertexSet base.core \ TreeSequenceVertexSet (ett.series.data.tree
        (Fin.last ett.rounds).castSucc)).biUnion fun (v : V) ↦ MissingColors G phi v) \ (fun (i :
        ℕ) ↦ ({c : Fin k |
    ∃ (r : Fin T.length), (HierarchyStarredStage H (Fin.last H.dividerCount)).length ≤ (↑r : ℕ) ∧
        (↑r : ℕ) < (HierarchyStarredStage H (Fin.last H.dividerCount)).length + i ∧ phi (T.edge r)
        = some c} : Finset (Fin k))) i) (ell - (2 : ℕ)) \ ((HierarchyStoredColorsAt H (Fin.last
        H.dividerCount)).biUnion (C.good.gamma (Fin.last H.dividerCount)) ∪
        HierarchyStoredColorsAt H (Fin.last H.dividerCount))).card ≤ (4 : ℕ) →
    ∃ (eta : Fin (7 : ℕ) → Fin k), Function.Injective eta ∧
    ∀ (h : Fin (7 : ℕ)), eta h ∈ HierarchyStoredColorsAt H (Fin.last H.dividerCount) ∧ eta h ∈
        TreeMissingColors phi ((fun (i : ℕ) ↦ TreeSequencePrefix T (min ((HierarchyStarredStage H
        (Fin.last H.dividerCount)).length + i) T.length) (
    by
                    have := GoldbergSeymour.TreeSequence.positive T
                    have := hXprefix.1
                    have :=
                     GoldbergSeymour.TreeSequence.positive
                      (HierarchyStarredStage H (Fin.last H.dividerCount))
                    have := GoldbergSeymour.TreeSequence.positive T
                    omega
    ) (
    by
                    have := GoldbergSeymour.TreeSequence.positive T
                    have := hXprefix.1
                    have :=
                     GoldbergSeymour.TreeSequence.positive
                      (HierarchyStarredStage H (Fin.last H.dividerCount))
                    have := GoldbergSeymour.TreeSequence.positive T
                    omega
    )) (ell - (2 : ℕ))) ∧ Disjoint (C.good.gamma (Fin.last H.dividerCount) (eta h) ∪ ({eta h} :
        Finset (Fin k))) ((fun (i : ℕ) ↦ ({c : Fin k |
    ∃ (r : Fin T.length), (HierarchyStarredStage H (Fin.last H.dividerCount)).length ≤ (↑r : ℕ) ∧
        (↑r : ℕ) < (HierarchyStarredStage H (Fin.last H.dividerCount)).length + i ∧ phi (T.edge r)
        = some c} : Finset (Fin k))) (ell - (2 : ℕ))))) (hNineAt hNi : (2 : ℕ) * ett.rounds + (11
        : ℕ) ≤ ((TreeMissingColors phi (TreeSequencePrefix T (min ((HierarchyStarredStage H
        (Fin.last H.dividerCount)).length + (T.length - (HierarchyStarredStage C.hierarchy
        (Fin.last C.hierarchy.dividerCount)).length - (2 : ℕ))) T.length) (
    by
               have := GoldbergSeymour.TreeSequence.positive T
               have := hXprefix.1
               have :=
                GoldbergSeymour.TreeSequence.positive
                 (HierarchyStarredStage H (Fin.last H.dividerCount))
               have := GoldbergSeymour.TreeSequence.positive T
               have :=
                GoldbergSeymour.TreeSequence.positive
                 (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount))
               omega
    ) (
    by
               have := GoldbergSeymour.TreeSequence.positive T
               have := hXprefix.1
               have :=
                GoldbergSeymour.TreeSequence.positive
                 (HierarchyStarredStage H (Fin.last H.dividerCount))
               have := GoldbergSeymour.TreeSequence.positive T
               have :=
                GoldbergSeymour.TreeSequence.positive
                 (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount))
               omega
    )) \ (TreeSequenceVertexSet base.core \ TreeSequenceVertexSet (ett.series.data.tree (Fin.last
        ett.rounds).castSucc)).biUnion fun (v : V) ↦ MissingColors G phi v) \ ({c : Fin k |
    ∃ (r : Fin T.length), (HierarchyStarredStage H (Fin.last H.dividerCount)).length ≤ (↑r : ℕ) ∧
        (↑r : ℕ) < (HierarchyStarredStage H (Fin.last H.dividerCount)).length + (T.length -
        (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length - (2 : ℕ))
        ∧ phi (T.edge r) = some c} : Finset (Fin k))).card ∧ ((((TreeMissingColors phi
        (TreeSequencePrefix T (min ((HierarchyStarredStage H (Fin.last H.dividerCount)).length +
        (T.length - (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length
        - (2 : ℕ))) T.length) (
    by
                 have := GoldbergSeymour.TreeSequence.positive T
                 have := hXprefix.1
                 have :=
                  GoldbergSeymour.TreeSequence.positive
                   (HierarchyStarredStage H (Fin.last H.dividerCount))
                 have := GoldbergSeymour.TreeSequence.positive T
                 have :=
                  GoldbergSeymour.TreeSequence.positive
                   (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount))
                 omega
    ) (
    by
                 have := GoldbergSeymour.TreeSequence.positive T
                 have := hXprefix.1
                 have :=
                  GoldbergSeymour.TreeSequence.positive
                   (HierarchyStarredStage H (Fin.last H.dividerCount))
                 have := GoldbergSeymour.TreeSequence.positive T
                 have :=
                  GoldbergSeymour.TreeSequence.positive
                   (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount))
                 omega
    )) \ (TreeSequenceVertexSet base.core \ TreeSequenceVertexSet (ett.series.data.tree (Fin.last
        ett.rounds).castSucc)).biUnion fun (v : V) ↦ MissingColors G phi v) \ ({c : Fin k |
    ∃ (r : Fin T.length), (HierarchyStarredStage H (Fin.last H.dividerCount)).length ≤ (↑r : ℕ) ∧
        (↑r : ℕ) < (HierarchyStarredStage H (Fin.last H.dividerCount)).length + (T.length -
        (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length - (2 : ℕ))
        ∧ phi (T.edge r) = some c} : Finset (Fin k))) \ ((HierarchyStoredColorsAt H (Fin.last
        H.dividerCount)).biUnion (C.good.gamma (Fin.last H.dividerCount)) ∪
        HierarchyStoredColorsAt H (Fin.last H.dividerCount))).card ≤ (4 : ℕ) →
    ∃ (eta : Fin (7 : ℕ) → Fin k), Function.Injective eta ∧
    ∀ (h : Fin (7 : ℕ)), eta h ∈ HierarchyStoredColorsAt H (Fin.last H.dividerCount) ∧ eta h ∈
        TreeMissingColors phi (TreeSequencePrefix T (min ((HierarchyStarredStage H (Fin.last
        H.dividerCount)).length + (T.length - (HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount)).length - (2 : ℕ))) T.length) (
    by
                  have := GoldbergSeymour.TreeSequence.positive T
                  have := hXprefix.1
                  have :=
                   GoldbergSeymour.TreeSequence.positive
                    (HierarchyStarredStage H (Fin.last H.dividerCount))
                  have := GoldbergSeymour.TreeSequence.positive T
                  have :=
                   GoldbergSeymour.TreeSequence.positive
                    (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount))
                  omega
    ) (
    by
                  have := GoldbergSeymour.TreeSequence.positive T
                  have := hXprefix.1
                  have :=
                   GoldbergSeymour.TreeSequence.positive
                    (HierarchyStarredStage H (Fin.last H.dividerCount))
                  have := GoldbergSeymour.TreeSequence.positive T
                  have :=
                   GoldbergSeymour.TreeSequence.positive
                    (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount))
                  omega
    )) ∧ Disjoint (C.good.gamma (Fin.last H.dividerCount) (eta h) ∪ ({eta h} : Finset (Fin k)))
        ({c : Fin k |
    ∃ (r : Fin T.length), (HierarchyStarredStage H (Fin.last H.dividerCount)).length ≤ (↑r : ℕ) ∧
        (↑r : ℕ) < (HierarchyStarredStage H (Fin.last H.dividerCount)).length + (T.length -
        (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length - (2 : ℕ))
        ∧ phi (T.edge r) = some c} : Finset (Fin k)))),
    let r0 : Fin T.length := (⟨T.length - (2 : ℕ),
    have this : (3 : ℕ) ≤ T.length - A.length := htailA; Decidable.byContradiction fun (a :
        ¬T.length - (2 : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length); (↑r0 : ℕ) = T.length - (2 : ℕ) →
    ∀ (beta : Fin k) (ubIdx : Fin (X.length + (1 : ℕ))), (↑(HierarchyFirstMissingPosition phi T
        beta) : ℕ) ≤ (↑(Fin.castLE (Nat.succ_le_succ hXprefix.1) ubIdx) : ℕ) →
        (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) < T.length

private abbrev helperHcase665Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (alpha :
        Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength C;
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
    let Tn : TreeSequence G e0 := ett.series.data.tree (Fin.last ett.rounds).castSucc;
    ∀ (htailA : (3 : ℕ) ≤ T.length - A.length) (hell : ell = T.length - A.length) (hXprefix :
        TreeSequenceInitialSegment X T) (hNine : (2 : ℕ) * ett.rounds + (11 : ℕ) ≤ ((fun (i : ℕ) ↦
        (TreeMissingColors phi ((fun (i : ℕ) ↦ TreeSequencePrefix T (min ((HierarchyStarredStage H
        (Fin.last H.dividerCount)).length + i) T.length) (
    by
                 have := GoldbergSeymour.TreeSequence.positive T
                 have := hXprefix.1
                 have :=
                  GoldbergSeymour.TreeSequence.positive
                   (HierarchyStarredStage H (Fin.last H.dividerCount))
                 have := GoldbergSeymour.TreeSequence.positive T
                 omega
    ) (
    by
                 have := GoldbergSeymour.TreeSequence.positive T
                 have := hXprefix.1
                 have :=
                  GoldbergSeymour.TreeSequence.positive
                   (HierarchyStarredStage H (Fin.last H.dividerCount))
                 have := GoldbergSeymour.TreeSequence.positive T
                 omega
    )) i) \ (TreeSequenceVertexSet base.core \ TreeSequenceVertexSet (ett.series.data.tree
        (Fin.last ett.rounds).castSucc)).biUnion fun (v : V) ↦ MissingColors G phi v) \ (fun (i :
        ℕ) ↦ ({c : Fin k |
    ∃ (r : Fin T.length), (HierarchyStarredStage H (Fin.last H.dividerCount)).length ≤ (↑r : ℕ) ∧
        (↑r : ℕ) < (HierarchyStarredStage H (Fin.last H.dividerCount)).length + i ∧ phi (T.edge r)
        = some c} : Finset (Fin k))) i) (ell - (2 : ℕ))).card ∧ (((fun (i : ℕ) ↦
        (TreeMissingColors phi ((fun (i : ℕ) ↦ TreeSequencePrefix T (min ((HierarchyStarredStage H
        (Fin.last H.dividerCount)).length + i) T.length) (
    by
                   have := GoldbergSeymour.TreeSequence.positive T
                   have := hXprefix.1
                   have :=
                    GoldbergSeymour.TreeSequence.positive
                     (HierarchyStarredStage H (Fin.last H.dividerCount))
                   have := GoldbergSeymour.TreeSequence.positive T
                   omega
    ) (
    by
                   have := GoldbergSeymour.TreeSequence.positive T
                   have := hXprefix.1
                   have :=
                    GoldbergSeymour.TreeSequence.positive
                     (HierarchyStarredStage H (Fin.last H.dividerCount))
                   have := GoldbergSeymour.TreeSequence.positive T
                   omega
    )) i) \ (TreeSequenceVertexSet base.core \ TreeSequenceVertexSet (ett.series.data.tree
        (Fin.last ett.rounds).castSucc)).biUnion fun (v : V) ↦ MissingColors G phi v) \ (fun (i :
        ℕ) ↦ ({c : Fin k |
    ∃ (r : Fin T.length), (HierarchyStarredStage H (Fin.last H.dividerCount)).length ≤ (↑r : ℕ) ∧
        (↑r : ℕ) < (HierarchyStarredStage H (Fin.last H.dividerCount)).length + i ∧ phi (T.edge r)
        = some c} : Finset (Fin k))) i) (ell - (2 : ℕ)) \ ((HierarchyStoredColorsAt H (Fin.last
        H.dividerCount)).biUnion (C.good.gamma (Fin.last H.dividerCount)) ∪
        HierarchyStoredColorsAt H (Fin.last H.dividerCount))).card ≤ (4 : ℕ) →
    ∃ (eta : Fin (7 : ℕ) → Fin k), Function.Injective eta ∧
    ∀ (h : Fin (7 : ℕ)), eta h ∈ HierarchyStoredColorsAt H (Fin.last H.dividerCount) ∧ eta h ∈
        TreeMissingColors phi ((fun (i : ℕ) ↦ TreeSequencePrefix T (min ((HierarchyStarredStage H
        (Fin.last H.dividerCount)).length + i) T.length) (
    by
                  have := GoldbergSeymour.TreeSequence.positive T
                  have := hXprefix.1
                  have :=
                   GoldbergSeymour.TreeSequence.positive
                    (HierarchyStarredStage H (Fin.last H.dividerCount))
                  have := GoldbergSeymour.TreeSequence.positive T
                  omega
    ) (
    by
                  have := GoldbergSeymour.TreeSequence.positive T
                  have := hXprefix.1
                  have :=
                   GoldbergSeymour.TreeSequence.positive
                    (HierarchyStarredStage H (Fin.last H.dividerCount))
                  have := GoldbergSeymour.TreeSequence.positive T
                  omega
    )) (ell - (2 : ℕ))) ∧ Disjoint (C.good.gamma (Fin.last H.dividerCount) (eta h) ∪ ({eta h} :
        Finset (Fin k))) ((fun (i : ℕ) ↦ ({c : Fin k |
    ∃ (r : Fin T.length), (HierarchyStarredStage H (Fin.last H.dividerCount)).length ≤ (↑r : ℕ) ∧
        (↑r : ℕ) < (HierarchyStarredStage H (Fin.last H.dividerCount)).length + i ∧ phi (T.edge r)
        = some c} : Finset (Fin k))) (ell - (2 : ℕ))))) (hNineAt hNi : (2 : ℕ) * ett.rounds + (11
        : ℕ) ≤ ((TreeMissingColors phi (TreeSequencePrefix T (min ((HierarchyStarredStage H
        (Fin.last H.dividerCount)).length + (T.length - (HierarchyStarredStage C.hierarchy
        (Fin.last C.hierarchy.dividerCount)).length - (2 : ℕ))) T.length) (
    by
             have := GoldbergSeymour.TreeSequence.positive T
             have := hXprefix.1
             have :=
              GoldbergSeymour.TreeSequence.positive
               (HierarchyStarredStage H (Fin.last H.dividerCount))
             have := GoldbergSeymour.TreeSequence.positive T
             have :=
              GoldbergSeymour.TreeSequence.positive
               (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount))
             omega
    ) (
    by
             have := GoldbergSeymour.TreeSequence.positive T
             have := hXprefix.1
             have :=
              GoldbergSeymour.TreeSequence.positive
               (HierarchyStarredStage H (Fin.last H.dividerCount))
             have := GoldbergSeymour.TreeSequence.positive T
             have :=
              GoldbergSeymour.TreeSequence.positive
               (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount))
             omega
    )) \ (TreeSequenceVertexSet base.core \ TreeSequenceVertexSet (ett.series.data.tree (Fin.last
        ett.rounds).castSucc)).biUnion fun (v : V) ↦ MissingColors G phi v) \ ({c : Fin k |
    ∃ (r : Fin T.length), (HierarchyStarredStage H (Fin.last H.dividerCount)).length ≤ (↑r : ℕ) ∧
        (↑r : ℕ) < (HierarchyStarredStage H (Fin.last H.dividerCount)).length + (T.length -
        (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length - (2 : ℕ))
        ∧ phi (T.edge r) = some c} : Finset (Fin k))).card ∧ ((((TreeMissingColors phi
        (TreeSequencePrefix T (min ((HierarchyStarredStage H (Fin.last H.dividerCount)).length +
        (T.length - (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length
        - (2 : ℕ))) T.length) (
    by
               have := GoldbergSeymour.TreeSequence.positive T
               have := hXprefix.1
               have :=
                GoldbergSeymour.TreeSequence.positive
                 (HierarchyStarredStage H (Fin.last H.dividerCount))
               have := GoldbergSeymour.TreeSequence.positive T
               have :=
                GoldbergSeymour.TreeSequence.positive
                 (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount))
               omega
    ) (
    by
               have := GoldbergSeymour.TreeSequence.positive T
               have := hXprefix.1
               have :=
                GoldbergSeymour.TreeSequence.positive
                 (HierarchyStarredStage H (Fin.last H.dividerCount))
               have := GoldbergSeymour.TreeSequence.positive T
               have :=
                GoldbergSeymour.TreeSequence.positive
                 (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount))
               omega
    )) \ (TreeSequenceVertexSet base.core \ TreeSequenceVertexSet (ett.series.data.tree (Fin.last
        ett.rounds).castSucc)).biUnion fun (v : V) ↦ MissingColors G phi v) \ ({c : Fin k |
    ∃ (r : Fin T.length), (HierarchyStarredStage H (Fin.last H.dividerCount)).length ≤ (↑r : ℕ) ∧
        (↑r : ℕ) < (HierarchyStarredStage H (Fin.last H.dividerCount)).length + (T.length -
        (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length - (2 : ℕ))
        ∧ phi (T.edge r) = some c} : Finset (Fin k))) \ ((HierarchyStoredColorsAt H (Fin.last
        H.dividerCount)).biUnion (C.good.gamma (Fin.last H.dividerCount)) ∪
        HierarchyStoredColorsAt H (Fin.last H.dividerCount))).card ≤ (4 : ℕ) →
    ∃ (eta : Fin (7 : ℕ) → Fin k), Function.Injective eta ∧
    ∀ (h : Fin (7 : ℕ)), eta h ∈ HierarchyStoredColorsAt H (Fin.last H.dividerCount) ∧ eta h ∈
        TreeMissingColors phi (TreeSequencePrefix T (min ((HierarchyStarredStage H (Fin.last
        H.dividerCount)).length + (T.length - (HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount)).length - (2 : ℕ))) T.length) (
    by
                have := GoldbergSeymour.TreeSequence.positive T
                have := hXprefix.1
                have :=
                 GoldbergSeymour.TreeSequence.positive
                  (HierarchyStarredStage H (Fin.last H.dividerCount))
                have := GoldbergSeymour.TreeSequence.positive T
                have :=
                 GoldbergSeymour.TreeSequence.positive
                  (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount))
                omega
    ) (
    by
                have := GoldbergSeymour.TreeSequence.positive T
                have := hXprefix.1
                have :=
                 GoldbergSeymour.TreeSequence.positive
                  (HierarchyStarredStage H (Fin.last H.dividerCount))
                have := GoldbergSeymour.TreeSequence.positive T
                have :=
                 GoldbergSeymour.TreeSequence.positive
                  (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount))
                omega
    )) ∧ Disjoint (C.good.gamma (Fin.last H.dividerCount) (eta h) ∪ ({eta h} : Finset (Fin k)))
        ({c : Fin k |
    ∃ (r : Fin T.length), (HierarchyStarredStage H (Fin.last H.dividerCount)).length ≤ (↑r : ℕ) ∧
        (↑r : ℕ) < (HierarchyStarredStage H (Fin.last H.dividerCount)).length + (T.length -
        (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length - (2 : ℕ))
        ∧ phi (T.edge r) = some c} : Finset (Fin k)))) (beta : Fin k) (ubIdx : Fin (X.length + (1
        : ℕ))), alpha ∈ HierarchyStageMissingColors H q → (0 : ℕ) < H.dividerCount ∧ alpha ∈
        TreeMissingColors phi (H.stage (⟨H.dividerCount,
    by
            have := GoldbergSeymour.TreeSequence.positive T
            have := hXprefix.1
            omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) ∨ H.dividerCount = (0 : ℕ) ∧ (alpha ∈ TreeMissingColors
        phi Tn ∨ alpha ∈ TreeMissingColors phi A ∧ alpha ∉ TashkinovStoredColors ett.series.data
        (Fin.last ett.rounds) ∧ beta ∉ TashkinovStoredColors ett.series.data (Fin.last
        ett.rounds))

private abbrev helperContinuation2632Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (alpha : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength C;
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
    let Tn : TreeSequence G e0 := ett.series.data.tree (Fin.last ett.rounds).castSucc;
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let Gamma : Finset (Fin k) := D.biUnion (C.good.gamma q);
    let M0 : Finset (Fin k) := (TreeSequenceVertexSet base.core \ TreeSequenceVertexSet
        Tn).biUnion fun (v : V) ↦ MissingColors G phi v;
    ∀ (htailA : (3 : ℕ) ≤ T.length - A.length) (hA : TreeSequenceInitialSegment A T) (hell : ell =
        T.length - A.length) (hBprefix : TreeSequenceInitialSegment B T) (hXprefix :
        TreeSequenceInitialSegment X T) (hlenX : X.length = T.length - (2 : ℕ)) (hAB :
        TreeSequenceInitialSegment A B) (hcoreB : TreeSequenceVertexSet base.core ⊆
        TreeSequenceVertexSet B) (hNine : (2 : ℕ) * ett.rounds + (11 : ℕ) ≤ ((fun (i : ℕ) ↦
        (TreeMissingColors phi ((fun (i : ℕ) ↦ TreeSequencePrefix T (min ((HierarchyStarredStage H
        (Fin.last H.dividerCount)).length + i) T.length) (
    have this : (1 : ℕ) ≤ T.length := T.positive;
    have this_1 : A.length ≤ T.length := hA.1;
    have this_2 : B.length ≤ T.length := hBprefix.1;
    have this_3 : X.length ≤ T.length := hXprefix.1;
    have this_4 : A.length ≤ B.length := hAB.1;
    have this_5 : (1 : ℕ) ≤ (HierarchyStarredStage H (Fin.last H.dividerCount)).length :=
        (HierarchyStarredStage H (Fin.last H.dividerCount)).positive;
    have this_6 : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤
        min ((HierarchyStarredStage H (Fin.last H.dividerCount)).length + i) T.length) ↦
    by omega
    ) (Nat.min_le_right ((HierarchyStarredStage H (Fin.last H.dividerCount)).length + i)
        T.length)) i) \ (TreeSequenceVertexSet base.core \ TreeSequenceVertexSet
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)).biUnion fun (v : V) ↦ MissingColors
        G phi v) \ (fun (i : ℕ) ↦ ({c : Fin k |
    ∃ (r : Fin T.length), (HierarchyStarredStage H (Fin.last H.dividerCount)).length ≤ (↑r : ℕ) ∧
        (↑r : ℕ) < (HierarchyStarredStage H (Fin.last H.dividerCount)).length + i ∧ phi (T.edge r)
        = some c} : Finset (Fin k))) i) (ell - (2 : ℕ))).card ∧ (((fun (i : ℕ) ↦
        (TreeMissingColors phi ((fun (i : ℕ) ↦ TreeSequencePrefix T (min ((HierarchyStarredStage H
        (Fin.last H.dividerCount)).length + i) T.length) (
    have this : (1 : ℕ) ≤ T.length := T.positive;
    have this_1 : A.length ≤ T.length := hA.1;
    have this_2 : B.length ≤ T.length := hBprefix.1;
    have this_3 : X.length ≤ T.length := hXprefix.1;
    have this_4 : A.length ≤ B.length := hAB.1;
    have this_5 : (1 : ℕ) ≤ (HierarchyStarredStage H (Fin.last H.dividerCount)).length :=
        (HierarchyStarredStage H (Fin.last H.dividerCount)).positive;
    have this_6 : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤
        min ((HierarchyStarredStage H (Fin.last H.dividerCount)).length + i) T.length) ↦
    by omega
    ) (Nat.min_le_right ((HierarchyStarredStage H (Fin.last H.dividerCount)).length + i)
        T.length)) i) \ (TreeSequenceVertexSet base.core \ TreeSequenceVertexSet
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)).biUnion fun (v : V) ↦ MissingColors
        G phi v) \ (fun (i : ℕ) ↦ ({c : Fin k |
    ∃ (r : Fin T.length), (HierarchyStarredStage H (Fin.last H.dividerCount)).length ≤ (↑r : ℕ) ∧
        (↑r : ℕ) < (HierarchyStarredStage H (Fin.last H.dividerCount)).length + i ∧ phi (T.edge r)
        = some c} : Finset (Fin k))) i) (ell - (2 : ℕ)) \ ((HierarchyStoredColorsAt H (Fin.last
        H.dividerCount)).biUnion (C.good.gamma (Fin.last H.dividerCount)) ∪
        HierarchyStoredColorsAt H (Fin.last H.dividerCount))).card ≤ (4 : ℕ) →
    ∃ (eta : Fin (7 : ℕ) → Fin k), Function.Injective eta ∧
    ∀ (h : Fin (7 : ℕ)), eta h ∈ HierarchyStoredColorsAt H (Fin.last H.dividerCount) ∧ eta h ∈
        TreeMissingColors phi ((fun (i : ℕ) ↦ TreeSequencePrefix T (min ((HierarchyStarredStage H
        (Fin.last H.dividerCount)).length + i) T.length) (
    have this : (1 : ℕ) ≤ T.length := T.positive;
    have this_1 : A.length ≤ T.length := hA.1;
    have this_2 : B.length ≤ T.length := hBprefix.1;
    have this_3 : X.length ≤ T.length := hXprefix.1;
    have this_4 : A.length ≤ B.length := hAB.1;
    have this_5 : (1 : ℕ) ≤ (HierarchyStarredStage H (Fin.last H.dividerCount)).length :=
        (HierarchyStarredStage H (Fin.last H.dividerCount)).positive;
    have this_6 : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤
        min ((HierarchyStarredStage H (Fin.last H.dividerCount)).length + i) T.length) ↦
    by omega
    ) (Nat.min_le_right ((HierarchyStarredStage H (Fin.last H.dividerCount)).length + i)
        T.length)) (ell - (2 : ℕ))) ∧ Disjoint (C.good.gamma (Fin.last H.dividerCount) (eta h) ∪
        ({eta h} : Finset (Fin k))) ((fun (i : ℕ) ↦ ({c : Fin k |
    ∃ (r : Fin T.length), (HierarchyStarredStage H (Fin.last H.dividerCount)).length ≤ (↑r : ℕ) ∧
        (↑r : ℕ) < (HierarchyStarredStage H (Fin.last H.dividerCount)).length + i ∧ phi (T.edge r)
        = some c} : Finset (Fin k))) (ell - (2 : ℕ))))) (hNineAt hNi : (2 : ℕ) * ett.rounds + (11
        : ℕ) ≤ ((TreeMissingColors phi (TreeSequencePrefix T (min ((HierarchyStarredStage H
        (Fin.last H.dividerCount)).length + (T.length - (HierarchyStarredStage C.hierarchy
        (Fin.last C.hierarchy.dividerCount)).length - (2 : ℕ))) T.length) (
    have this : (1 : ℕ) ≤ T.length := T.positive;
    have this_1 : A.length ≤ T.length := hA.1;
    have this_2 : B.length ≤ T.length := hBprefix.1;
    have this_3 : X.length ≤ T.length := hXprefix.1;
    have this_4 : A.length ≤ B.length := hAB.1;
    have this_5 : (1 : ℕ) ≤ (HierarchyStarredStage H (Fin.last H.dividerCount)).length :=
        (HierarchyStarredStage H (Fin.last H.dividerCount)).positive;
    have this_6 : (1 : ℕ) ≤ T.length := T.positive;
    have this_7 : (1 : ℕ) ≤ (HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount)).length := (HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount)).positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ min
        ((HierarchyStarredStage H (Fin.last H.dividerCount)).length + (T.length -
        (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length - (2 : ℕ)))
        T.length) ↦
    by omega
    ) (Nat.min_le_right ((HierarchyStarredStage H (Fin.last H.dividerCount)).length + (T.length -
        (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length - (2 : ℕ)))
        T.length)) \ (TreeSequenceVertexSet base.core \ TreeSequenceVertexSet
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)).biUnion fun (v : V) ↦ MissingColors
        G phi v) \ ({c : Fin k |
    ∃ (r : Fin T.length), (HierarchyStarredStage H (Fin.last H.dividerCount)).length ≤ (↑r : ℕ) ∧
        (↑r : ℕ) < (HierarchyStarredStage H (Fin.last H.dividerCount)).length + (T.length -
        (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length - (2 : ℕ))
        ∧ phi (T.edge r) = some c} : Finset (Fin k))).card ∧ ((((TreeMissingColors phi
        (TreeSequencePrefix T (min ((HierarchyStarredStage H (Fin.last H.dividerCount)).length +
        (T.length - (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length
        - (2 : ℕ))) T.length) (
    have this : (1 : ℕ) ≤ T.length := T.positive;
    have this_1 : A.length ≤ T.length := hA.1;
    have this_2 : B.length ≤ T.length := hBprefix.1;
    have this_3 : X.length ≤ T.length := hXprefix.1;
    have this_4 : A.length ≤ B.length := hAB.1;
    have this_5 : (1 : ℕ) ≤ (HierarchyStarredStage H (Fin.last H.dividerCount)).length :=
        (HierarchyStarredStage H (Fin.last H.dividerCount)).positive;
    have this_6 : (1 : ℕ) ≤ T.length := T.positive;
    have this_7 : (1 : ℕ) ≤ (HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount)).length := (HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount)).positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ min
        ((HierarchyStarredStage H (Fin.last H.dividerCount)).length + (T.length -
        (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length - (2 : ℕ)))
        T.length) ↦
    by omega
    ) (Nat.min_le_right ((HierarchyStarredStage H (Fin.last H.dividerCount)).length + (T.length -
        (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length - (2 : ℕ)))
        T.length)) \ (TreeSequenceVertexSet base.core \ TreeSequenceVertexSet
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)).biUnion fun (v : V) ↦ MissingColors
        G phi v) \ ({c : Fin k |
    ∃ (r : Fin T.length), (HierarchyStarredStage H (Fin.last H.dividerCount)).length ≤ (↑r : ℕ) ∧
        (↑r : ℕ) < (HierarchyStarredStage H (Fin.last H.dividerCount)).length + (T.length -
        (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length - (2 : ℕ))
        ∧ phi (T.edge r) = some c} : Finset (Fin k))) \ ((HierarchyStoredColorsAt H (Fin.last
        H.dividerCount)).biUnion (C.good.gamma (Fin.last H.dividerCount)) ∪
        HierarchyStoredColorsAt H (Fin.last H.dividerCount))).card ≤ (4 : ℕ) →
    ∃ (eta : Fin (7 : ℕ) → Fin k), Function.Injective eta ∧
    ∀ (h : Fin (7 : ℕ)), eta h ∈ HierarchyStoredColorsAt H (Fin.last H.dividerCount) ∧ eta h ∈
        TreeMissingColors phi (TreeSequencePrefix T (min ((HierarchyStarredStage H (Fin.last
        H.dividerCount)).length + (T.length - (HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount)).length - (2 : ℕ))) T.length) (
    have this : (1 : ℕ) ≤ T.length := T.positive;
    have this_1 : A.length ≤ T.length := hA.1;
    have this_2 : B.length ≤ T.length := hBprefix.1;
    have this_3 : X.length ≤ T.length := hXprefix.1;
    have this_4 : A.length ≤ B.length := hAB.1;
    have this_5 : (1 : ℕ) ≤ (HierarchyStarredStage H (Fin.last H.dividerCount)).length :=
        (HierarchyStarredStage H (Fin.last H.dividerCount)).positive;
    have this_6 : (1 : ℕ) ≤ T.length := T.positive;
    have this_7 : (1 : ℕ) ≤ (HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount)).length := (HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount)).positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ min
        ((HierarchyStarredStage H (Fin.last H.dividerCount)).length + (T.length -
        (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length - (2 : ℕ)))
        T.length) ↦
    by omega
    ) (Nat.min_le_right ((HierarchyStarredStage H (Fin.last H.dividerCount)).length + (T.length -
        (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length - (2 : ℕ)))
        T.length)) ∧ Disjoint (C.good.gamma (Fin.last H.dividerCount) (eta h) ∪ ({eta h} : Finset
        (Fin k))) ({c : Fin k |
    ∃ (r : Fin T.length), (HierarchyStarredStage H (Fin.last H.dividerCount)).length ≤ (↑r : ℕ) ∧
        (↑r : ℕ) < (HierarchyStarredStage H (Fin.last H.dividerCount)).length + (T.length -
        (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length - (2 : ℕ))
        ∧ phi (T.edge r) = some c} : Finset (Fin k)))),
    let r0 : Fin T.length := (⟨T.length - (2 : ℕ),
    have this : (3 : ℕ) ≤ T.length - A.length := htailA;
    by omega
    ⟩ : Fin T.length);
    ∀ (hr0val : (↑r0 : ℕ) = T.length - (2 : ℕ)) (beta : Fin k) (hbM0 : beta ∉ M0) (hbGamma : beta
        ∉ Gamma),
    let hia : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T alpha;
    let hib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    ∀ (hvB : T.vertex hib ∈ TreeSequenceVertexSet B) (hterminalPath : Disjoint (TwoColorComponent
        G phi alpha beta (Sum.inl (T.vertex (Fin.last T.length)))) (TwoColorComponent G phi alpha
        beta (Sum.inl (T.vertex hia))) ∧ TwoColorPathComponent G phi alpha beta (Sum.inl (T.vertex
        (Fin.last T.length))) ∧
    ∀ x ∈ TreeSequenceVertexSet B, MissingColors G (TwoColorComponentSwap G phi alpha beta
        (Sum.inl (T.vertex (Fin.last T.length)))) x = MissingColors G phi x),
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G phi alpha beta (Sum.inl
        (T.vertex (Fin.last T.length)));
    ∀ (hbetaTerminal : beta ∈ MissingColors G sigma (T.vertex (Fin.last T.length))) (hbetaX : beta
        ∈ TreeMissingColors sigma X) (hcut : A.length + (ell - (2 : ℕ)) = T.length - (2 : ℕ))
        (hstable :
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    have n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    have Tnq : TreeSequence G e0 := H.stage (⟨H.dividerCount,
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)));
    have Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    have Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q; HierarchyWeaklyStable H q sigma ∧
        ModColoring ett sigma ∧ (A = Tn ∨
    ∃ (inputA : PartialEdgeColoring E k) (ettA : ExtendedTashkinovTree G k e0 inputA A sigma),
        MaximumProperty ettA) ∧ (
    ∀ (hq : (0 : ℕ) < H.dividerCount),
    ∃ (inputA : PartialEdgeColoring E k) (ettA : ExtendedTashkinovTree G k e0 inputA A sigma)
        (baseA : HierarchyBase ettA sigma) (K : TashkinovHierarchy ettA baseA) (goodA :
        GoodHierarchy K), MaximumProperty ettA ∧
    ∃ (hcount : K.dividerCount + (1 : ℕ) = H.dividerCount), baseA.core = base.core ∧ baseA.closure
        = base.closure ∧ (
    ∀ (j : Fin (K.dividerCount + (2 : ℕ))), K.stage j = H.stage (⟨(↑j : ℕ),
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) ∧ (
    ∀ (j : Fin (K.dividerCount + (1 : ℕ))),
    have jH : Fin (H.dividerCount + (1 : ℕ)) := (⟨(↑j : ℕ),
    by omega
    ⟩ : Fin (H.dividerCount + (1 : ℕ))); HierarchyStoredColorsAt K j = HierarchyStoredColorsAt H
        jH ∧
    ∀ eta ∈ HierarchyStoredColorsAt K j, goodA.gamma j eta = C.good.gamma jH eta) ∧
        TreeColorSetMinusClosed G sigma Tnq (Dnq.biUnion (C.good.gamma (⟨C.hierarchy.dividerCount
        - (1 : ℕ),
    by omega
    ⟩ : Fin (C.hierarchy.dividerCount + (1 : ℕ)))))) ∧
    ∃ (corrT : CorrespondingExtendedTashkinovTree G k e0 ett sigma T), MaximumProperty
        corrT.replacementETT ∧
    ∃ (baseT : HierarchyBase corrT.replacementETT sigma) (K : TashkinovHierarchy
        corrT.replacementETT baseT) (goodT : GoodHierarchy K), SameGoodHierarchy C.good goodT),
    ∃ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∃ beta ∈ MissingColors G P.coloring (T.vertex (Fin.last T.length)), beta ∈ TreeMissingColors
        P.coloring (HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ))) ∧
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
        P.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let Tn : TreeSequence G e0 := P.corresponding.replacementETT.series.data.tree (Fin.last
        P.corresponding.replacementETT.rounds).castSucc; beta ∉ (HierarchyStoredColorsAt H
        q).biUnion (P.counterexample.good.gamma q) ∪ (TreeSequenceVertexSet P.replacementBase.core
        \ TreeSequenceVertexSet Tn).biUnion fun (v : V) ↦ MissingColors G P.coloring v

private abbrev helperContinuation2387Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (alpha : Fin k)
        (hterminal : alpha ∈ MissingColors G phi (T.vertex (Fin.last T.length))),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength C;
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
    let Tn : TreeSequence G e0 := ett.series.data.tree (Fin.last ett.rounds).castSucc;
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let Gamma : Finset (Fin k) := D.biUnion (C.good.gamma q);
    let M0 : Finset (Fin k) := (TreeSequenceVertexSet base.core \ TreeSequenceVertexSet
        Tn).biUnion fun (v : V) ↦ MissingColors G phi v;
    ∀ (htailA : (3 : ℕ) ≤ T.length - A.length) (hA : TreeSequenceInitialSegment A T) (hell : ell =
        T.length - A.length) (hBprefix : TreeSequenceInitialSegment B T) (hXprefix :
        TreeSequenceInitialSegment X T) (hlenB : B.length = T.length - (1 : ℕ)) (hlenX : X.length
        = T.length - (2 : ℕ)) (hAB : TreeSequenceInitialSegment A B) (hElem :
        ColoredVertexSetElementary G phi (TreeSequenceVertexSet B)) (hcoreB :
        TreeSequenceVertexSet base.core ⊆ TreeSequenceVertexSet B) (hAlphaAvoid :
    ∀ (r : Fin T.length), A.length ≤ (↑r : ℕ) → phi (T.edge r) ≠ some alpha) (hNine : (2 : ℕ) *
        ett.rounds + (11 : ℕ) ≤ ((fun (i : ℕ) ↦ (TreeMissingColors phi ((fun (i : ℕ) ↦
        TreeSequencePrefix T (min ((HierarchyStarredStage H (Fin.last H.dividerCount)).length + i)
        T.length) (
    by
                 first
                 | omega
                 | (
                   have := GoldbergSeymour.TreeSequence.positive T
                   have := hA.1
                   have := hBprefix.1
                   have := hXprefix.1
                   have := hAB.1
                   have :=
                    GoldbergSeymour.TreeSequence.positive
                     (HierarchyStarredStage H (Fin.last H.dividerCount))
                   have := GoldbergSeymour.TreeSequence.positive T
                   all_goals omega)
    ) (Nat.min_le_right ((HierarchyStarredStage H (Fin.last H.dividerCount)).length + i)
        T.length)) i) \ (TreeSequenceVertexSet base.core \ TreeSequenceVertexSet
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)).biUnion fun (v : V) ↦ MissingColors
        G phi v) \ (fun (i : ℕ) ↦ ({c : Fin k |
    ∃ (r : Fin T.length), (HierarchyStarredStage H (Fin.last H.dividerCount)).length ≤ (↑r : ℕ) ∧
        (↑r : ℕ) < (HierarchyStarredStage H (Fin.last H.dividerCount)).length + i ∧ phi (T.edge r)
        = some c} : Finset (Fin k))) i) (ell - (2 : ℕ))).card ∧ (((fun (i : ℕ) ↦
        (TreeMissingColors phi ((fun (i : ℕ) ↦ TreeSequencePrefix T (min ((HierarchyStarredStage H
        (Fin.last H.dividerCount)).length + i) T.length) (
    by
                   first
                   | omega
                   | (
                     have := GoldbergSeymour.TreeSequence.positive T
                     have := hA.1
                     have := hBprefix.1
                     have := hXprefix.1
                     have := hAB.1
                     have :=
                      GoldbergSeymour.TreeSequence.positive
                       (HierarchyStarredStage H (Fin.last H.dividerCount))
                     have := GoldbergSeymour.TreeSequence.positive T
                     all_goals omega)
    ) (Nat.min_le_right ((HierarchyStarredStage H (Fin.last H.dividerCount)).length + i)
        T.length)) i) \ (TreeSequenceVertexSet base.core \ TreeSequenceVertexSet
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)).biUnion fun (v : V) ↦ MissingColors
        G phi v) \ (fun (i : ℕ) ↦ ({c : Fin k |
    ∃ (r : Fin T.length), (HierarchyStarredStage H (Fin.last H.dividerCount)).length ≤ (↑r : ℕ) ∧
        (↑r : ℕ) < (HierarchyStarredStage H (Fin.last H.dividerCount)).length + i ∧ phi (T.edge r)
        = some c} : Finset (Fin k))) i) (ell - (2 : ℕ)) \ ((HierarchyStoredColorsAt H (Fin.last
        H.dividerCount)).biUnion (C.good.gamma (Fin.last H.dividerCount)) ∪
        HierarchyStoredColorsAt H (Fin.last H.dividerCount))).card ≤ (4 : ℕ) →
    ∃ (eta : Fin (7 : ℕ) → Fin k), Function.Injective eta ∧
    ∀ (h : Fin (7 : ℕ)), eta h ∈ HierarchyStoredColorsAt H (Fin.last H.dividerCount) ∧ eta h ∈
        TreeMissingColors phi ((fun (i : ℕ) ↦ TreeSequencePrefix T (min ((HierarchyStarredStage H
        (Fin.last H.dividerCount)).length + i) T.length) (
    by
                  first
                  | omega
                  | (
                    have := GoldbergSeymour.TreeSequence.positive T
                    have := hA.1
                    have := hBprefix.1
                    have := hXprefix.1
                    have := hAB.1
                    have :=
                     GoldbergSeymour.TreeSequence.positive
                      (HierarchyStarredStage H (Fin.last H.dividerCount))
                    have := GoldbergSeymour.TreeSequence.positive T
                    all_goals omega)
    ) (Nat.min_le_right ((HierarchyStarredStage H (Fin.last H.dividerCount)).length + i)
        T.length)) (ell - (2 : ℕ))) ∧ Disjoint (C.good.gamma (Fin.last H.dividerCount) (eta h) ∪
        ({eta h} : Finset (Fin k))) ((fun (i : ℕ) ↦ ({c : Fin k |
    ∃ (r : Fin T.length), (HierarchyStarredStage H (Fin.last H.dividerCount)).length ≤ (↑r : ℕ) ∧
        (↑r : ℕ) < (HierarchyStarredStage H (Fin.last H.dividerCount)).length + i ∧ phi (T.edge r)
        = some c} : Finset (Fin k))) (ell - (2 : ℕ))))),
    let U : Finset (Fin k) := ({c : Fin k |
    ∃ (r : Fin T.length), A.length ≤ (↑r : ℕ) ∧ (↑r : ℕ) < A.length + (ell - (2 : ℕ)) ∧ phi
        (T.edge r) = some c} : Finset (Fin k));
    ∀ (hNineAt hNi : (2 : ℕ) * ett.rounds + (11 : ℕ) ≤ ((TreeMissingColors phi (TreeSequencePrefix
        T (min ((HierarchyStarredStage H (Fin.last H.dividerCount)).length + (T.length -
        (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length - (2 : ℕ)))
        T.length) (
    by
              first
              | omega
              | (
                have := GoldbergSeymour.TreeSequence.positive T
                have := hA.1
                have := hBprefix.1
                have := hXprefix.1
                have := hAB.1
                have :=
                 GoldbergSeymour.TreeSequence.positive
                  (HierarchyStarredStage H (Fin.last H.dividerCount))
                have := GoldbergSeymour.TreeSequence.positive T
                have :=
                 GoldbergSeymour.TreeSequence.positive
                  (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount))
                all_goals omega)
    ) (Nat.min_le_right ((HierarchyStarredStage H (Fin.last H.dividerCount)).length + (T.length -
        (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length - (2 : ℕ)))
        T.length)) \ (TreeSequenceVertexSet base.core \ TreeSequenceVertexSet
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)).biUnion fun (v : V) ↦ MissingColors
        G phi v) \ ({c : Fin k |
    ∃ (r : Fin T.length), (HierarchyStarredStage H (Fin.last H.dividerCount)).length ≤ (↑r : ℕ) ∧
        (↑r : ℕ) < (HierarchyStarredStage H (Fin.last H.dividerCount)).length + (T.length -
        (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length - (2 : ℕ))
        ∧ phi (T.edge r) = some c} : Finset (Fin k))).card ∧ ((((TreeMissingColors phi
        (TreeSequencePrefix T (min ((HierarchyStarredStage H (Fin.last H.dividerCount)).length +
        (T.length - (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length
        - (2 : ℕ))) T.length) (
    by
                first
                | omega
                | (
                  have := GoldbergSeymour.TreeSequence.positive T
                  have := hA.1
                  have := hBprefix.1
                  have := hXprefix.1
                  have := hAB.1
                  have :=
                   GoldbergSeymour.TreeSequence.positive
                    (HierarchyStarredStage H (Fin.last H.dividerCount))
                  have := GoldbergSeymour.TreeSequence.positive T
                  have :=
                   GoldbergSeymour.TreeSequence.positive
                    (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount))
                  all_goals omega)
    ) (Nat.min_le_right ((HierarchyStarredStage H (Fin.last H.dividerCount)).length + (T.length -
        (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length - (2 : ℕ)))
        T.length)) \ (TreeSequenceVertexSet base.core \ TreeSequenceVertexSet
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)).biUnion fun (v : V) ↦ MissingColors
        G phi v) \ ({c : Fin k |
    ∃ (r : Fin T.length), (HierarchyStarredStage H (Fin.last H.dividerCount)).length ≤ (↑r : ℕ) ∧
        (↑r : ℕ) < (HierarchyStarredStage H (Fin.last H.dividerCount)).length + (T.length -
        (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length - (2 : ℕ))
        ∧ phi (T.edge r) = some c} : Finset (Fin k))) \ ((HierarchyStoredColorsAt H (Fin.last
        H.dividerCount)).biUnion (C.good.gamma (Fin.last H.dividerCount)) ∪
        HierarchyStoredColorsAt H (Fin.last H.dividerCount))).card ≤ (4 : ℕ) →
    ∃ (eta : Fin (7 : ℕ) → Fin k), Function.Injective eta ∧
    ∀ (h : Fin (7 : ℕ)), eta h ∈ HierarchyStoredColorsAt H (Fin.last H.dividerCount) ∧ eta h ∈
        TreeMissingColors phi (TreeSequencePrefix T (min ((HierarchyStarredStage H (Fin.last
        H.dividerCount)).length + (T.length - (HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount)).length - (2 : ℕ))) T.length) (
    by
                 first
                 | omega
                 | (
                   have := GoldbergSeymour.TreeSequence.positive T
                   have := hA.1
                   have := hBprefix.1
                   have := hXprefix.1
                   have := hAB.1
                   have :=
                    GoldbergSeymour.TreeSequence.positive
                     (HierarchyStarredStage H (Fin.last H.dividerCount))
                   have := GoldbergSeymour.TreeSequence.positive T
                   have :=
                    GoldbergSeymour.TreeSequence.positive
                     (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount))
                   all_goals omega)
    ) (Nat.min_le_right ((HierarchyStarredStage H (Fin.last H.dividerCount)).length + (T.length -
        (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length - (2 : ℕ)))
        T.length)) ∧ Disjoint (C.good.gamma (Fin.last H.dividerCount) (eta h) ∪ ({eta h} : Finset
        (Fin k))) ({c : Fin k |
    ∃ (r : Fin T.length), (HierarchyStarredStage H (Fin.last H.dividerCount)).length ≤ (↑r : ℕ) ∧
        (↑r : ℕ) < (HierarchyStarredStage H (Fin.last H.dividerCount)).length + (T.length -
        (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length - (2 : ℕ))
        ∧ phi (T.edge r) = some c} : Finset (Fin k)))),
    let r0 : Fin T.length := (⟨T.length - (2 : ℕ),
    have this : (3 : ℕ) ≤ T.length - A.length := htailA; Decidable.byContradiction fun (a :
        ¬T.length - (2 : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length);
    let r1 : Fin T.length := (⟨T.length - (1 : ℕ),
    have this : (3 : ℕ) ≤ T.length - A.length := htailA; Decidable.byContradiction fun (a :
        ¬T.length - (1 : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length);
    let N : Finset (Fin k) := (phi (T.edge r0)).toList.toFinset ∪ (phi (T.edge
        r1)).toList.toFinset;
    ∀ (hr0val : (↑r0 : ℕ) = T.length - (2 : ℕ)) (hSuffixN :
    ∀ (c : Fin k) (r : Fin T.length), X.length ≤ (↑r : ℕ) → phi (T.edge r) = some c → c ∈ N) (beta
        : Fin k) (hbX : beta ∈ TreeMissingColors phi X) (hbM0 : beta ∉ M0) (hbGamma : beta ∉
        Gamma) (hbU : beta ∉ U) (hbN : beta ∉ N) (hXB : TreeSequenceInitialSegment X B) (haB :
        alpha ∈ TreeMissingColors phi B) (hbB : beta ∈ TreeMissingColors phi B) (ubIdx : Fin
        (X.length + (1 : ℕ))) (hiaLe :
        (↑(HierarchyFirstMissingPosition phi T alpha) : ℕ) ≤ A.length) (hibLt :
        (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) < T.length) (hbetaFirst : beta ∈
        MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T beta))),
    let hia : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T alpha;
    let hib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    ∀ (hne : alpha ≠ beta) (hStageMiss : alpha ∈ HierarchyStageMissingColors H q) (hSame :
        TwoColorComponent G phi alpha beta (Sum.inl (T.vertex hia)) = TwoColorComponent G phi
        alpha beta (Sum.inl (T.vertex hib))),
    ∃ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∃ beta ∈ MissingColors G P.coloring (T.vertex (Fin.last T.length)), beta ∈ TreeMissingColors
        P.coloring (HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ))) ∧
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
        P.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let Tn : TreeSequence G e0 := P.corresponding.replacementETT.series.data.tree (Fin.last
        P.corresponding.replacementETT.rounds).castSucc; beta ∉ (HierarchyStoredColorsAt H
        q).biUnion (P.counterexample.good.gamma q) ∪ (TreeSequenceVertexSet P.replacementBase.core
        \ TreeSequenceVertexSet Tn).biUnion fun (v : V) ↦ MissingColors G P.coloring v

private abbrev helperContinuation212Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C),
    ∀ alpha ∈ MissingColors G phi (T.vertex (Fin.last T.length)), alpha ∈ TreeMissingColors phi
        (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)) →
    ∀ eta ∈ HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount), alpha ∈
        C.good.gamma (Fin.last C.hierarchy.dividerCount) eta →
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength C;
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
    let Tn : TreeSequence G e0 := ett.series.data.tree (Fin.last ett.rounds).castSucc;
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let _ : Finset (Fin k) := D.biUnion (C.good.gamma q);
    let _ : Finset (Fin k) := (TreeSequenceVertexSet base.core \ TreeSequenceVertexSet Tn).biUnion
        fun (v : V) ↦ MissingColors G phi v; (3 : ℕ) ≤ T.length - A.length →
        TreeSequenceInitialSegment A T → ell = T.length - A.length → TreeSequenceInitialSegment B
        T → TreeSequenceInitialSegment X T → B.length = T.length - (1 : ℕ) → X.length = T.length -
        (2 : ℕ) → (
    ∀ {S U W : TreeSequence G e0}, TreeSequenceInitialSegment S W → TreeSequenceInitialSegment U W
        → S.length ≤ U.length → TreeSequenceInitialSegment S U) → TreeSequenceInitialSegment A B →
        ColoredVertexSetElementary G phi (TreeSequenceVertexSet B) → TreeSequenceVertexSet
        base.core ⊆ TreeSequenceVertexSet A → TreeSequenceVertexSet base.core ⊆
        TreeSequenceVertexSet B → (
    ∀ (r : Fin T.length), A.length ≤ (↑r : ℕ) → phi (T.edge r) ≠ some alpha) →
    ∃ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∃ beta ∈ MissingColors G P.coloring (T.vertex (Fin.last T.length)), beta ∈ TreeMissingColors
        P.coloring (HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ))) ∧
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
        P.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let Tn : TreeSequence G e0 := P.corresponding.replacementETT.series.data.tree (Fin.last
        P.corresponding.replacementETT.rounds).castSucc; beta ∉ (HierarchyStoredColorsAt H
        q).biUnion (P.counterexample.good.gamma q) ∪ (TreeSequenceVertexSet P.replacementBase.core
        \ TreeSequenceVertexSet Tn).biUnion fun (v : V) ↦ MissingColors G P.coloring v

private theorem helper_hiaLt_371.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (alpha :
        Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q; (3 : ℕ) ≤ T.length - A.length →
    let hia : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T alpha; (↑hia : ℕ) ≤
        A.length → (↑hia : ℕ) < T.length := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha H q A htailA hia hiaBound
  have hAshort : A.length < T.length := by
    have h := htailA
    clear * - h
    omega
  exact Nat.lt_of_le_of_lt hiaBound hAshort

private theorem helper_hvB_389.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    let ell : ℕ := HierarchyFullTailLength C;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
        TreeSequenceInitialSegment B T → B.length = T.length - (1 : ℕ) →
    ∀ (beta : Fin k), (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) < T.length →
    let hib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta; T.vertex hib ∈
        TreeSequenceVertexSet B := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ell B hBprefix hlenB beta hibLt hib
  have hibBound : hib.val < B.length + 1 := by
    have h := hlenB
    clear * - h hibLt
    omega
  let iB : Fin (B.length + 1) := ⟨hib.val, hibBound⟩
  have hcast : Fin.castLE (Nat.succ_le_succ hBprefix.1) iB = hib := Fin.ext rfl
  have hvEq : T.vertex hib = B.vertex iB := by
    rw [← hcast]
    exact hBprefix.2.1 iB
  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨iB, hvEq.symm⟩

private theorem helper_hcut_466.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength C; (3 : ℕ) ≤ T.length - A.length →
        TreeSequenceInitialSegment A T → ell = T.length - A.length → A.length + (ell - (2 : ℕ)) =
        T.length - (2 : ℕ) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q A ell htailA hA hell
  rw [hell]
  have ha : A.length ≤ T.length := hA.1
  have ht : 3 ≤ T.length - A.length := htailA
  clear * - ha ht
  omega

private theorem helper_vertexMemB_487.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    let ell : ℕ := HierarchyFullTailLength C;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
        TreeSequenceInitialSegment B T → B.length = T.length - (1 : ℕ) →
    ∀ (i : Fin (T.length + (1 : ℕ))), (↑i : ℕ) < T.length → T.vertex i ∈ TreeSequenceVertexSet B
  := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ell B hBprefix hlenB i hi
  have hbnd : i.val < B.length + 1 := by
    have h := hlenB
    clear * - h hi
    omega
  let j : Fin (B.length + 1) := ⟨i.val, hbnd⟩
  have hcast : Fin.castLE (Nat.succ_le_succ hBprefix.1) j = i := Fin.ext rfl
  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
  refine ⟨j, ?_⟩
  have hvEq : T.vertex i = B.vertex j := by
    rw [← hcast]
    exact hBprefix.2.1 j
  exact hvEq.symm

private theorem helper_branch_724.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (alpha : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let ell : ℕ := HierarchyFullTailLength C;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
    let Tn : TreeSequence G e0 := ett.series.data.tree (Fin.last ett.rounds).castSucc;
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let Gamma : Finset (Fin k) := D.biUnion (C.good.gamma q);
    let M0 : Finset (Fin k) := (TreeSequenceVertexSet base.core \ TreeSequenceVertexSet
        Tn).biUnion fun (v : V) ↦ MissingColors G phi v; TreeSequenceVertexSet base.core ⊆
        TreeSequenceVertexSet B →
    ∀ beta ∉ M0, beta ∉ Gamma →
    let hia : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T alpha;
    let hib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta; T.vertex hib ∈
        TreeSequenceVertexSet B → (Disjoint (TwoColorComponent G phi alpha beta (Sum.inl (T.vertex
        (Fin.last T.length)))) (TwoColorComponent G phi alpha beta (Sum.inl (T.vertex hia))) ∧
        TwoColorPathComponent G phi alpha beta (Sum.inl (T.vertex (Fin.last T.length))) ∧
    ∀ x ∈ TreeSequenceVertexSet B, MissingColors G (TwoColorComponentSwap G phi alpha beta
        (Sum.inl (T.vertex (Fin.last T.length)))) x = MissingColors G phi x) →
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G phi alpha beta (Sum.inl
        (T.vertex (Fin.last T.length)));
    ∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), P.coloring = sigma
        → P.corresponding.replacementETT.series.data.tree (Fin.last
        P.corresponding.replacementETT.rounds).castSucc = Tn → base.core = P.replacementBase.core
        →
    let qNew : Fin (P.counterexample.hierarchy.dividerCount + (1 : ℕ)) := Fin.last
        P.counterexample.hierarchy.dividerCount; HierarchyStoredColorsAt
        P.counterexample.hierarchy qNew = D → (
    ∀ rho ∈ D, C.good.gamma q rho = P.counterexample.good.gamma qNew rho) →
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
        P.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let Tn : TreeSequence G e0 := P.corresponding.replacementETT.series.data.tree (Fin.last
        P.corresponding.replacementETT.rounds).castSucc; beta ∉ (HierarchyStoredColorsAt H
        q).biUnion (P.counterexample.good.gamma q) ∪ (TreeSequenceVertexSet P.replacementBase.core
        \ TreeSequenceVertexSet Tn).biUnion fun (v : V) ↦ MissingColors G P.coloring v := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx alpha H q ell B Tn D Gamma M0 hcoreB beta
      hbM0 hbGamma hia hib hvB hterminalPath sigma P hP hterminalTree hcoreEq qNew hD hGammaEq
  change beta ∉
    (HierarchyStoredColorsAt P.counterexample.hierarchy qNew).biUnion
        (P.counterexample.good.gamma qNew) ∪
      ((TreeSequenceVertexSet P.replacementBase.core \
          TreeSequenceVertexSet
            (P.corresponding.replacementETT.series.data.tree
              (Fin.last P.corresponding.replacementETT.rounds).castSucc)).biUnion
        fun v => MissingColors G P.coloring v)
  intro hbad
  rcases Finset.mem_union.mp hbad with hGammaNew | hMnew
  · obtain ⟨rho, hrho, hbetaGammaNew⟩ := Finset.mem_biUnion.mp hGammaNew
    have hrhoOld : rho ∈ D := by rw [← hD]; exact hrho
    have hbetaGammaOld : beta ∈ C.good.gamma q rho := by
      rw [hGammaEq rho hrhoOld]
      exact hbetaGammaNew
    exact hbGamma (Finset.mem_biUnion.mpr ⟨rho, hrhoOld, hbetaGammaOld⟩)
  · obtain ⟨v, hv, hbetaV⟩ := Finset.mem_biUnion.mp hMnew
    obtain ⟨hvCoreNew, hvNotTnew⟩ := Finset.mem_sdiff.mp hv
    have hvCoreOld : v ∈ TreeSequenceVertexSet base.core := by
      rw [hcoreEq]
      exact hvCoreNew
    have hvNotTn : v ∉ TreeSequenceVertexSet Tn := by
      intro hvTn
      apply hvNotTnew
      rw [hterminalTree]
      exact hvTn
    have hvB : v ∈ TreeSequenceVertexSet B := hcoreB hvCoreOld
    have hbetaPhi : beta ∈ MissingColors G phi v := by
      rw [hP] at hbetaV
      rw [hterminalPath.2.2 v hvB] at hbetaV
      exact hbetaV
    have hbetaM0 : beta ∈ M0 :=
      Finset.mem_biUnion.mpr
        ⟨v, Finset.mem_sdiff.mpr ⟨hvCoreOld, hvNotTn⟩, hbetaPhi⟩
    exact hbM0 hbetaM0

private theorem optionPair_card_le_two {α : Type*} [DecidableEq α]
    (first second : Option α) :
    (first.toList.toFinset ∪ second.toList.toFinset).card ≤ 2 := by
  calc
    _ ≤ first.toList.length + second.toList.length :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add
        (List.toFinset_card_le _) (List.toFinset_card_le _))
    _ ≤ 2 := by cases first <;> cases second <;> simp

private theorem color_mem_final_pair {α : Type*} [DecidableEq α] {length : ℕ}
    (color : Fin length → Option α) (first second : Fin length)
    (hfirst : first.val = length - 2) (hsecond : second.val = length - 1)
    (position : Fin length) (hposition : length - 2 ≤ position.val)
    {c : α} (hc : color position = some c) :
    c ∈ (color first).toList.toFinset ∪ (color second).toList.toFinset := by
  have hindex : position.val = first.val ∨ position.val = second.val := by omega
  rcases hindex with hindex | hindex
  · have hsame : position = first := Fin.ext hindex
    subst position
    simp [hc]
  · have hsame : position = second := Fin.ext hindex
    subst position
    simp [hc]

private theorem helper_hbetaExists_392.{u_1, u_2} :
    helperHbetaExists392Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q A ell X Tn D Gamma M0 htailA hell hcoreA
      hNine U Avail hNineAt hNi hGammaD r0 r1 N hNcard Free hNineSmall
  by_cases hlarge : 5 ≤ Free.card
  · have hremain : (Free \ N).Nonempty := by
      apply Finset.card_pos.mp
      have hc := Finset.card_le_card_sdiff_add_card (s := Free) (t := N)
      omega
    obtain ⟨beta, hb⟩ := hremain
    have hbfree := (Finset.mem_sdiff.mp hb).1
    have hbN := (Finset.mem_sdiff.mp hb).2
    obtain ⟨hbAvail, hbGD⟩ := Finset.mem_sdiff.mp hbfree
    obtain ⟨hbMissExtra, hbU⟩ := Finset.mem_sdiff.mp hbAvail
    obtain ⟨hbMiss, hbExtra⟩ := Finset.mem_sdiff.mp hbMissExtra
    refine ⟨beta, hbMiss, hbExtra, ?_, hbU, hbN⟩
    · intro hb
      exact hbGD (Finset.mem_union_left _ hb)
  · obtain ⟨rho, hinj, hrho⟩ := hNineSmall (by change Free.card ≤ 4; omega)
    let block := fun i : Fin 7 => C.good.gamma q (rho i) ∪ {rho i}
    have hblocks : ∀ i j : Fin 7, i ≠ j → Disjoint (block i) (block j) := by
      intro i j hij
      have hneq : rho i ≠ rho j := fun heq => hij (hinj heq)
      rw [Finset.disjoint_left]
      intro c hci hcj
      simp only [block, Finset.mem_union, Finset.mem_singleton] at hci hcj
      rcases hci with hci | hci <;> rcases hcj with hcj | hcj
      · exact Finset.disjoint_left.mp (C.good.disjointPairs q (rho i) (rho j)
          (hrho i).1 (hrho j).1 hneq) hci hcj
      · exact Finset.disjoint_left.mp hGammaD
          (Finset.mem_biUnion.mpr ⟨rho i, (hrho i).1, hci⟩) (hcj.symm ▸ (hrho j).1)
      · exact Finset.disjoint_left.mp hGammaD
          (Finset.mem_biUnion.mpr ⟨rho j, (hrho j).1, hcj⟩) (hci.symm ▸ (hrho i).1)
      · exact hneq (hci.symm.trans hcj)
    have hsomeBlock : ∃ i : Fin 7, Disjoint (block i) N := by
      by_contra hnone
      push Not at hnone
      let f : Fin 7 → {c // c ∈ N} := fun i =>
        ⟨Classical.choose (Finset.not_disjoint_iff.mp (hnone i)),
          (Classical.choose_spec (Finset.not_disjoint_iff.mp (hnone i))).2⟩
      have hf : Function.Injective f := by
        intro i j hij
        by_contra hne
        have hfi := Classical.choose_spec (Finset.not_disjoint_iff.mp (hnone i))
        have hfj := Classical.choose_spec (Finset.not_disjoint_iff.mp (hnone j))
        have heq : Classical.choose (Finset.not_disjoint_iff.mp (hnone i)) =
            Classical.choose (Finset.not_disjoint_iff.mp (hnone j)) :=
          congrArg Subtype.val hij
        exact (Finset.disjoint_left.mp (hblocks i j hne) hfi.1 (heq ▸ hfj.1))
      have hc := Fintype.card_le_of_injective f hf
      have hcard : Fintype.card {c // c ∈ N} = N.card := Fintype.card_coe N
      rw [hcard] at hc
      have : 7 ≤ 2 := by simpa using hc.trans hNcard
      omega
    obtain ⟨i, hiBlock⟩ := hsomeBlock
    let beta := rho i
    have hbTailMissing : beta ∈ TreeMissingColors phi X := (hrho i).2.1
    have hbD : beta ∈ D := (hrho i).1
    have hbGamma : beta ∉ Gamma := by
      intro hb
      exact (Finset.disjoint_left.mp hGammaD hb hbD)
    have hbM0 : beta ∉ M0 := by
      intro hb
      obtain ⟨v, hv, hmiss⟩ := Finset.mem_biUnion.mp hb
      have hvA : v ∈ TreeSequenceVertexSet A :=
        hcoreA (Finset.mem_sdiff.mp hv).1
      have hbA : beta ∈ TreeMissingColors phi A := Finset.mem_biUnion.mpr ⟨v, hvA, hmiss⟩
      exact (Finset.mem_sdiff.mp hbD).2 hbA
    have hbU : beta ∉ U := by
      intro hbU
      simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at hbU
      obtain ⟨r, hr, hlt, hcol⟩ := hbU
      have hblock := (hrho i).2.2
      exact (Finset.disjoint_left.mp hblock
        (Finset.mem_union_right _ (Finset.mem_singleton.mpr rfl))
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, r, hr, hlt, hcol⟩))
    have hbN : beta ∉ N := by
      intro hb
      exact (Finset.disjoint_left.mp hiBlock
        (Finset.mem_union_right _ (Finset.mem_singleton.mpr rfl)) hb)
    refine ⟨beta, hbTailMissing, hbM0, hbGamma, hbU, hbN⟩

private theorem helper_hibLt_530.{u_1, u_2} :
    helperHibLt530Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha H q A ell X htailA hell hXprefix hlenX
      hNine hNineAt hNi r0 hr0val beta ubIdx hibLe
  have hidxVal :
      (Fin.castLE (Nat.succ_le_succ hXprefix.1) ubIdx).val = ubIdx.val := rfl
  have huval : ubIdx.val < T.length := by omega
  have hcastLt :
      (Fin.castLE (Nat.succ_le_succ hXprefix.1) ubIdx).val < T.length := by
    rw [hidxVal]
    exact huval
  exact hibLe.trans_lt hcastLt

private theorem helper_hcase_665.{u_1, u_2} :
    helperHcase665Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha H q A ell X Tn htailA hell hXprefix hNine
      hNineAt hNi beta ubIdx hStageMiss
  by_cases hd : 0 < H.dividerCount
  · left
    refine ⟨hd, ?_⟩
    let r : Fin H.dividerCount := ⟨H.dividerCount - 1, by omega⟩
    have hq : q = r.succ := by
      apply Fin.ext
      simp [q, r]
      omega
    have hm := hStageMiss
    unfold HierarchyStageMissingColors at hm
    rw [hq] at hm
    change alpha ∈ TreeMissingColors phi (H.stage r.succ.castSucc) at hm
    have hidx : r.succ.castSucc = ⟨H.dividerCount, by omega⟩ := by
      apply Fin.ext
      simp [r]
      omega
    simpa only [hidx] using hm
  · have hz : H.dividerCount = 0 := by omega
    right
    refine ⟨hz, Or.inl ?_⟩
    have hq : q = 0 := Fin.ext (by simp [q, hz])
    have hm := hStageMiss
    unfold HierarchyStageMissingColors at hm
    rw [hq] at hm
    simpa [Tn] using hm

private theorem helper_continuation_2632.{u_1, u_2} :
    helperContinuation2632Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx alpha H q A ell X B Tn D Gamma M0 htailA hA
      hell hBprefix hXprefix hlenX hAB hcoreB hNine hNineAt hNi r0 hr0val beta hbM0 hbGamma hia
      hib hvB hterminalPath sigma hbetaTerminal hbetaX hcut hstable
  rcases hstable with ⟨_, _, _, _, hCorr⟩
  obtain ⟨corr, hmax, baseT, K, goodT, sameGood⟩ := hCorr
  have seriesFacts := ett.series.coloringProperties
  let corrRefl : CorrespondingExtendedTashkinovTree G k e0 ett phi T :=
    { replacementInput := input
      replacementSeries := ett.series
      replacementETT := ett
      rungAgreement := rfl
      seriesPresentation := HEq.rfl
      finalGeneratingColoring := ett.generatingColoring
      ladderTreesAgree := fun _ => rfl
      storedColorsAgree := fun _ => rfl
      connectingEdgesAgree := fun _ => rfl
      extensionKindsAgree := fun _ => rfl
      replacementProper := fun j => (seriesFacts j).1
      replacementOneUncolored := fun j => (seriesFacts j).2
      replacementStable := fun _ => ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩ }
  let PRefl : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx :=
    { coloring := phi
      corresponding := corrRefl
      maximum := C.maximum
      replacementBase := base
      counterexample := C
      sameGood := ⟨⟨rfl, rfl, HEq.rfl, HEq.rfl, Iff.rfl, fun _ => rfl⟩,
        rfl, fun _ => ⟨rfl, fun _ _ => rfl⟩⟩
      minimumContext := ctx }
  have hVpair : ∃ v ∈ TreeSequenceVertexSet T,
      beta ∈ MissingColors G sigma v ∧ v ≠ T.vertex (Fin.last T.length) := by
    obtain ⟨v, hv, hmiss⟩ := Finset.mem_biUnion.mp hbetaX
    obtain ⟨i, hi⟩ : ∃ i : Fin (X.length + 1), X.vertex i = v := by
      simpa only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] using hv
    let j : Fin (T.length + 1) := Fin.castLE (Nat.succ_le_succ hXprefix.1) i
    have hvT : v = T.vertex j := by
      rw [← hi]
      exact hXprefix.2.1 i
    have hjval : j.val = i.val := rfl
    have hiLE : i.val ≤ X.length := by
      have hiLt := i.isLt
      omega
    have hilen : i.val ≤ T.length - 2 := hiLE.trans_eq hlenX
    have hjlt : j.val < T.length := by
      rw [hjval]
      have hlen : T.length - 2 < T.length := by omega
      exact Nat.lt_of_le_of_lt hilen hlen
    refine ⟨v, ?_, hmiss, ?_⟩
    · rw [hvT]
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨j, rfl⟩
    · intro heq
      have hidx := T.vertex_injective (hvT.symm.trans heq)
      have hval := congrArg Fin.val hidx
      simp only [Fin.val_last] at hval
      omega
  let Cnew : HierarchyCounterexample baseT :=
    { positive := by rw [corr.rungAgreement]; exact C.positive
      hierarchy := K
      good := goodT
      maximum := hmax
      notElementary := by
        intro he
        obtain ⟨v, hv, hmissV, hneV⟩ := hVpair
        have hterm : T.vertex (Fin.last T.length) ∈ TreeSequenceVertexSet T := by
          simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
          exact ⟨Fin.last T.length, rfl⟩
        have hdisj := Finset.disjoint_left.mp (he hv hterm hneV)
        exact hdisj hmissV hbetaTerminal }
  obtain ⟨P, hP⟩ := HierarchyReplacementPresentationTrans G k e0 input T phi
    ett base C ctx PRefl sigma corr baseT Cnew sameGood
  have terminalTreeOf (rho : PartialEdgeColoring E k)
      (c : CorrespondingExtendedTashkinovTree G k e0 ett rho T) :
      c.replacementETT.series.data.tree
        (Fin.last c.replacementETT.rounds).castSucc = Tn := by
    exact c.terminalData.1
  have hterminalTree := terminalTreeOf P.coloring P.corresponding
  have hcoreEq : base.core = P.replacementBase.core := P.sameGood.1.1
  have hcount : H.dividerCount = P.counterexample.hierarchy.dividerCount :=
    P.sameGood.2.choose
  let qNew : Fin (P.counterexample.hierarchy.dividerCount + 1) :=
    Fin.last P.counterexample.hierarchy.dividerCount
  have hqCast : Fin.cast (congrArg (fun n => n + 1) hcount) q = qNew := by
    apply Fin.ext
    simp [qNew, q]
  have hsg := P.sameGood.2.choose_spec q
  have hD : HierarchyStoredColorsAt P.counterexample.hierarchy qNew = D := by
    have h := hsg.1
    rw [hqCast] at h
    exact h.symm
  have hGammaEq (rho : Fin k) (hrho : rho ∈ D) :
      C.good.gamma q rho = P.counterexample.good.gamma qNew rho := by
    have h := hsg.2 rho hrho
    rw [hqCast] at h
    exact h
  refine ⟨P, beta, ?_, ?_, ?_⟩
  · rw [hP]
    exact hbetaTerminal
  · rw [hP]
    exact hbetaX
  · exact @helper_branch_724 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@alpha) (@hcoreB) (@beta)
      (@hbM0) (@hbGamma) (@hvB) (@hterminalPath) (@P) (@hP) (@hterminalTree) (@hcoreEq) (@hD)
      (@hGammaEq)

private theorem helper_continuation_2387.{u_1, u_2} :
    helperContinuation2387Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx alpha hterminal H q A ell X B Tn D Gamma M0
      htailA hA hell hBprefix hXprefix hlenB hlenX hAB hElem hcoreB hAlphaAvoid hNine U hNineAt
      hNi r0 r1 N hr0val hSuffixN beta hbX hbM0 hbGamma hbU hbN hXB haB hbB ubIdx hiaLe
      hibLt hbetaFirst hia hib hne hStageMiss hSame
  have hiaBound : hia.val ≤ A.length := by simpa [hia] using hiaLe
  have hiaLt := @helper_hiaLt_371 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@htailA) (@hiaBound)
  have hAlphaFirst := TreeSequenceFirstMissingPositionMem hiaLt
  have huB : T.vertex hia ∈ TreeSequenceVertexSet B := by
    let iA : Fin (A.length + 1) := ⟨hia.val, by omega⟩
    have hcast : Fin.castLE (Nat.succ_le_succ hA.1) iA = hia := Fin.ext rfl
    have hvA : A.vertex iA ∈ TreeSequenceVertexSet A := by
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨iA, rfl⟩
    have hvEq : T.vertex hia = A.vertex iA := by
      rw [← hcast]
      exact hA.2.1 iA
    rw [hvEq]
    exact TreeSequenceInitialSegmentVertexSetSubset hAB hvA
  have hvB := @helper_hvB_389 (@V) (@E) inferInstance inferInstance inferInstance inferInstance (@G)
      (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hBprefix) (@hlenB) (@beta) (@hibLt)
  have hwu : T.vertex (Fin.last T.length) ≠ T.vertex hia := by
    intro heq
    have hidx := T.vertex_injective heq
    have hval := congrArg Fin.val hidx
    simp only [Fin.val_last] at hval
    omega
  have hwv : T.vertex (Fin.last T.length) ≠ T.vertex hib := by
    intro heq
    have hidx := T.vertex_injective heq
    have hval := congrArg Fin.val hidx
    simp only [Fin.val_last] at hval
    omega
  have hterminalPath :=
    P2905_T2_ElementaryTerminalComponent G phi alpha beta hne ctx.proper
      (TreeSequenceVertexSet B) hElem
      (T.vertex hia) (T.vertex hib) (T.vertex (Fin.last T.length))
      huB hvB hwu hwv hAlphaFirst hbetaFirst (Or.inl hterminal) hSame
  let sigma := TwoColorComponentSwap G phi alpha beta
      (Sum.inl (T.vertex (Fin.last T.length)))
  have hsigma : sigma = TwoColorComponentSwap G phi alpha beta
      (Sum.inl (T.vertex (Fin.last T.length))) := rfl
  have hswapMissing := TwoColorComponentSwapMissingBehavior
    G phi alpha beta hne ctx.proper (Sum.inl (T.vertex (Fin.last T.length)))
  have hbetaTerminal : beta ∈ MissingColors G sigma (T.vertex (Fin.last T.length)) := by
    exact hswapMissing.2.1 _ rfl hterminal
  have hbetaX : beta ∈ TreeMissingColors sigma X := by
    obtain ⟨v, hv, hmiss⟩ := Finset.mem_biUnion.mp hbX
    have hvB' : v ∈ TreeSequenceVertexSet B := TreeSequenceInitialSegmentVertexSetSubset hXB hv
    have heq := hterminalPath.2.2 v hvB'
    exact Finset.mem_biUnion.mpr ⟨v, hv, heq ▸ hmiss⟩
  have hmissingPrefix :
      alpha ∈ TreeMissingColors phi B ∧ beta ∈ TreeMissingColors phi B := ⟨haB, hbB⟩
  have hcase := @helper_hcase_665 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@htailA) (@hell)
      (@hXprefix) (@hNine) (@hNineAt) (@hNi) (@beta) (@ubIdx) (@hStageMiss)
  have hcut := @helper_hcut_466 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@htailA) (@hA) (@hell)
  have htailEdges : ∀ r : Fin T.length, A.length ≤ r.val →
      sigma (T.edge r) = phi (T.edge r) := by
    intro r hr
    have hnotAlpha := hAlphaAvoid r hr
    have hnotBeta : phi (T.edge r) ≠ some beta := by
      intro hc
      by_cases hbefore : r.val < X.length
      · apply hbU
        simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨r, hr, ?_, hc⟩
        rw [hlenX] at hbefore
        have two : 2 ≤ ell := by
          rw [hell]
          exact (by decide : 2 ≤ 3).trans htailA
        rw [← Nat.add_sub_assoc two, hell, Nat.add_sub_of_le hA.1]
        exact hbefore
      · apply hbN
        exact hSuffixN beta r (by omega) hc
    simp [sigma, TwoColorComponentSwap, hnotAlpha, hnotBeta]
  have vertexMemB := @helper_vertexMemB_487 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hBprefix) (@hlenB)
  have missingAtB (i : Fin (T.length + 1)) (hi : i.val < T.length) :
      MissingColors G sigma (T.vertex i) = MissingColors G phi (T.vertex i) :=
    hterminalPath.2.2 (T.vertex i) (vertexMemB i hi)
  have hstoredFirst :
      ∀ rho, rho ∈ D →
        HierarchyFirstMissingPosition sigma T rho =
          HierarchyFirstMissingPosition phi T rho := by
    intro rho _
    exact T.firstMissingPosition_eq_of_agreement missingAtB rho
  have hstable := StableChangeCasesOneTwoFullTail G k e0 input T phi ett
    base C ctx alpha beta hne hmissingPrefix
    (Sum.inl (T.vertex (Fin.last T.length))) hterminalPath.2.1 sigma rfl hcase
    hterminalPath.1 htailEdges hterminalPath.2.2 hstoredFirst
  exact @helper_continuation_2632 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@alpha)
      (@htailA) (@hA) (@hell) (@hBprefix) (@hXprefix) (@hlenX) (@hAB) (@hcoreB) (@hNine)
      (@hNineAt) (@hNi) (@hr0val) (@beta) (@hbM0) (@hbGamma) (@hvB) (@hterminalPath)
      (@hbetaTerminal) (@hbetaX) (@hcut) (@hstable)
private theorem helper_continuation_212.{u_1, u_2} :
    helperContinuation212Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx alpha hterminal hstar eta heta hgamma H q A
      ell X B Tn D Gamma M0 htailA hA hell hBprefix hXprefix hlenB hlenX commonPrefix hAB hElem
      hcoreA hcoreB hAlphaAvoid
  have hNineIndex : ell - 2 < ell := by omega
  have hNine := NineN G k e0 input T phi ett C.positive base H C.good hElem
    ctx.largeMissingSet (ell - 2) hNineIndex
  let U := (Finset.univ : Finset (Fin k)).filter fun c =>
    ∃ r : Fin T.length,
      A.length ≤ r.val ∧ r.val < A.length + (ell - 2) ∧ phi (T.edge r) = some c
  let Avail := (TreeMissingColors phi X \ M0) \ U
  have hNineAt := hNine
  dsimp [Tn, q, A, ell, HierarchyFullTailLength] at hNineAt
  have hNi := hNineAt
  have hNiCard : 2 * ett.rounds + 11 ≤ Avail.card := by
    exact hNi.1
  have hGoodAvoid := GoodHierarchyReservedDisjoint C.good q
  have hGammaD : Disjoint Gamma D := by
    simpa [Gamma, D] using hGoodAvoid.2
  have hEtaNotA : eta ∉ TreeMissingColors phi A := by
    intro hm
    have hD := (Finset.mem_sdiff.mp heta).2
    exact hD hm
  have hAlphaNotD : alpha ∉ D := by
    intro ha
    have hAlphaGamma : alpha ∈ Gamma := Finset.mem_biUnion.mpr ⟨eta, heta, hgamma⟩
    exact Finset.disjoint_left.mp hGammaD hAlphaGamma ha
  let r0 : Fin T.length := ⟨T.length - 2, by have := htailA; omega⟩
  let r1 : Fin T.length := ⟨T.length - 1, by have := htailA; omega⟩
  let N := (phi (T.edge r0)).toList.toFinset ∪ (phi (T.edge r1)).toList.toFinset
  have hNcard : N.card ≤ 2 := optionPair_card_le_two (phi (T.edge r0)) (phi (T.edge r1))
  have hr0val : r0.val = T.length - 2 := by simp [r0]
  have hr1val : r1.val = T.length - 1 := by simp [r1]
  have hSuffixN : ∀ (c : Fin k) (r : Fin T.length),
      X.length ≤ r.val → phi (T.edge r) = some c → c ∈ N := by
    intro c r hr hc
    exact color_mem_final_pair (fun position => phi (T.edge position)) r0 r1
      hr0val hr1val r (hlenX ▸ hr) hc
  let Free := Avail \ (Gamma ∪ D)
  have hNineSmall := hNi.2
  change (Avail \ (Gamma ∪ D)).card ≤ 4 →
    ∃ rho : Fin 7 → Fin k, Function.Injective rho ∧
      ∀ i, rho i ∈ D ∧ rho i ∈ TreeMissingColors phi X ∧
        Disjoint (C.good.gamma q (rho i) ∪ {rho i}) U at hNineSmall
  have hbetaExists := @helper_hbetaExists_392 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@htailA) (@hell)
      (@hcoreA) (@hNine) (@hNineAt) (@hNi) (@hGammaD) (@hNcard) (@hNineSmall)
  obtain ⟨beta, hbX, hbM0, hbGamma, hbU, hbN⟩ := hbetaExists
  have missingMono (psi : PartialEdgeColoring E k) {S R : TreeSequence G e0}
      (hSR : TreeSequenceInitialSegment S R) :
      TreeMissingColors psi S ⊆ TreeMissingColors psi R := by
    intro c hc
    obtain ⟨v, hv, hmiss⟩ := Finset.mem_biUnion.mp hc
    exact Finset.mem_biUnion.mpr
      ⟨v, TreeSequenceInitialSegmentVertexSetSubset hSR hv, hmiss⟩
  have hAX : TreeSequenceInitialSegment A X := commonPrefix hA hXprefix (by
    rw [hlenX]
    apply Nat.le_sub_of_add_le
    have bound := (Nat.add_le_add_right (by decide : 2 ≤ 3) A.length).trans
      (Nat.add_le_of_le_sub hA.1 htailA)
    simpa only [Nat.add_comm] using bound)
  have hXB : TreeSequenceInitialSegment X B := commonPrefix hXprefix hBprefix (by
    rw [hlenX, hlenB]
    omega)
  have haB : alpha ∈ TreeMissingColors phi B := missingMono phi hAB hstar
  have hbB : beta ∈ TreeMissingColors phi B := missingMono phi hXB hbX
  obtain ⟨ua, hua, hma⟩ := Finset.mem_biUnion.mp hstar
  obtain ⟨uaIdx, huaIdx⟩ :
      ∃ i : Fin (A.length + 1), A.vertex i = ua := by
    simpa only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] using hua
  obtain ⟨ub, hub, hmb⟩ := Finset.mem_biUnion.mp hbX
  obtain ⟨ubIdx, hubIdx⟩ :
      ∃ i : Fin (X.length + 1), X.vertex i = ub := by
    simpa only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] using hub
  have hiaLe : (HierarchyFirstMissingPosition phi T alpha).val ≤ A.length := by
    let iT := Fin.castLE (Nat.succ_le_succ hA.1) uaIdx
    have hmiss : alpha ∈ MissingColors G phi (T.vertex iT) := by
      rw [hA.2.1 uaIdx, huaIdx]
      exact hma
    have hle := TreeSequenceFirstMissingPositionLe hmiss
    change (HierarchyFirstMissingPosition phi T alpha).val ≤ uaIdx.val at hle
    have hi := uaIdx.isLt
    omega
  have hbetaWitness : beta ∈ MissingColors G phi
      (T.vertex (Fin.castLE (Nat.succ_le_succ hXprefix.1) ubIdx)) := by
    rw [hXprefix.2.1 ubIdx, hubIdx]
    exact hmb
  have hibLe : (HierarchyFirstMissingPosition phi T beta).val ≤
      (Fin.castLE (Nat.succ_le_succ hXprefix.1) ubIdx).val :=
    TreeSequenceFirstMissingPositionLe hbetaWitness
  have hibLt := @helper_hibLt_530 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@htailA) (@hell)
      (@hXprefix) (@hlenX) (@hNine) (@hNineAt) (@hNi) (@hr0val) (@beta) (@ubIdx) (@hibLe)
  have hbetaFirst : beta ∈ MissingColors G phi
      (T.vertex (HierarchyFirstMissingPosition phi T beta)) :=
    TreeSequenceFirstMissingPositionMem hibLt
  let hia := HierarchyFirstMissingPosition phi T alpha
  let hib := HierarchyFirstMissingPosition phi T beta
  have hiaVal : hia.val ≤ A.length := by simpa [hia] using hiaLe
  have hbetaPosAfterA (hbetaNotA : beta ∉ TreeMissingColors phi A) :
      A.length < hib.val := by
    by_contra hle
    have hiA : hib.val ≤ A.length := by omega
    let iA : Fin (A.length + 1) := ⟨hib.val, by omega⟩
    have hidx : Fin.castLE (Nat.succ_le_succ hA.1) iA = hib := Fin.ext rfl
    have vertexMem (S : TreeSequence G e0) (i : Fin (S.length + 1)) :
        S.vertex i ∈ TreeSequenceVertexSet S := by
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨i, rfl⟩
    have hbA : beta ∈ TreeMissingColors phi A := by
      refine Finset.mem_biUnion.mpr ⟨A.vertex iA, vertexMem A iA, ?_⟩
      rw [← hA.2.1 iA, hidx]
      simpa [hib] using hbetaFirst
    exact hbetaNotA hbA
  have horderedUnused :
      (alpha ∉ TreeMissingColors phi A ∨ beta ∉ TreeMissingColors phi A) →
        TreeVertexOrder T (T.vertex hia) (T.vertex hib) ∧
          alpha ∉ (Finset.univ.filter fun c =>
            ∃ t : Fin T.length, A.length ≤ t.val ∧ t.val < hib.val ∧
              phi (T.edge t) = some c) := by
    intro hout
    by_cases hbA : beta ∈ TreeMissingColors phi A
    · rcases hout with hna | hnb
      · exact (hna hstar).elim
      · exact (hnb hbA).elim
    · have hlt : hia.val < hib.val := by
        have := hbetaPosAfterA hbA
        omega
      refine ⟨⟨hia, hib, rfl, rfl, hlt⟩, ?_⟩
      intro ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      obtain ⟨t, htA, _, htc⟩ := ha
      exact hAlphaAvoid t htA htc
  have hne : alpha ≠ beta := by
    intro heq
    exact hbGamma (heq ▸ Finset.mem_biUnion.mpr ⟨eta, heta, hgamma⟩)
  have hchange := ChangeLemma G k e0 input T phi ett base C
    ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
    ctx.lexicographicMinimality hElem ctx.largeMissingSet alpha beta hne
    ⟨haB, hbB⟩ horderedUnused
  have hStageMiss : alpha ∈ HierarchyStageMissingColors H q :=
    (Finset.mem_sdiff.mp (C.good.avoidance q eta heta hgamma)).1
  have hSame : TwoColorComponent G phi alpha beta (Sum.inl (T.vertex hia)) =
      TwoColorComponent G phi alpha beta (Sum.inl (T.vertex hib)) := by
    by_cases hd : 0 < H.dividerCount
    · apply hchange.1
      refine ⟨hd, Or.inl ?_⟩
      let r : Fin H.dividerCount := ⟨H.dividerCount - 1, by omega⟩
      have hq : q = r.succ := by
        apply Fin.ext
        simp [q, r]
        omega
      have hm := hStageMiss
      unfold HierarchyStageMissingColors at hm
      rw [hq] at hm
      change alpha ∈ TreeMissingColors phi (H.stage r.succ.castSucc) at hm
      have hidx : r.succ.castSucc = ⟨H.dividerCount, by omega⟩ := by
        apply Fin.ext
        simp [r]
        omega
      rw [hidx] at hm
      exact hm
    · have hz : H.dividerCount = 0 := by omega
      apply hchange.2.1
      refine ⟨hz, Or.inl ?_⟩
      have hq : q = 0 := Fin.ext (by simp [q, hz])
      have hm := hStageMiss
      unfold HierarchyStageMissingColors at hm
      rw [hq] at hm
      exact hm
  exact @helper_continuation_2387 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@alpha)
      (@hterminal) (@htailA) (@hA) (@hell) (@hBprefix) (@hXprefix) (@hlenB) (@hlenX) (@hAB)
      (@hElem) (@hcoreB) (@hAlphaAvoid) (@hNine) (@hNineAt) (@hNi) (@hr0val) (@hSuffixN) (@beta)
      (@hbX) (@hbM0) (@hbGamma) (@hbU) (@hbN) (@hXB) (@haB) (@hbB) (@ubIdx) (@hiaLe)
      (@hibLt) (@hbetaFirst) (@hne) (@hStageMiss) (@hSame)
theorem P2905_T2_AbsentOwnerReplacement {V E : Type*}
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
    (hpathUpper : HierarchyPathNumber C.hierarchy < HierarchyFullTailLength C)
    (alpha : Fin k)
    (hterminal : alpha ∈ MissingColors G phi (T.vertex (Fin.last T.length)))
    (hstar : alpha ∈ TreeMissingColors phi (HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount)))
    (eta : Fin k) (heta : eta ∈ HierarchyStoredColorsAt C.hierarchy (Fin.last
        C.hierarchy.dividerCount))
    (hgamma : alpha ∈ C.good.gamma (Fin.last C.hierarchy.dividerCount) eta)
    (habsent : eta ∉ TreeMissingColors phi
      (HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1))) :
    ∃ P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx,
      ∃ beta : Fin k,
        beta ∈ MissingColors G P.coloring (T.vertex (Fin.last T.length)) ∧
        beta ∈ TreeMissingColors P.coloring
          (HierarchyFullTailPrefix C (HierarchyFullTailLength C - 2)) ∧
        (let H := P.counterexample.hierarchy
        let q := Fin.last H.dividerCount
        let Tn := P.corresponding.replacementETT.series.data.tree
          (Fin.last P.corresponding.replacementETT.rounds).castSucc
        beta ∉ (HierarchyStoredColorsAt H q).biUnion
          (P.counterexample.good.gamma q) ∪
          ((TreeSequenceVertexSet P.replacementBase.core \
              TreeSequenceVertexSet Tn).biUnion
            fun v => MissingColors G P.coloring v)) := by
  classical
  let H := C.hierarchy
  let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
  let A := HierarchyStarredStage H q
  let ell := HierarchyFullTailLength C
  let X := HierarchyFullTailPrefix C (ell - 2)
  let B := HierarchyFullTailPrefix C (ell - 1)
  let Tn := ett.series.data.tree (Fin.last ett.rounds).castSucc
  let D := HierarchyStoredColorsAt H q
  let Gamma := D.biUnion (C.good.gamma q)
  let M0 := (TreeSequenceVertexSet base.core \ TreeSequenceVertexSet Tn).biUnion
    fun v => MissingColors G phi v
  have htail : 3 ≤ ell := by
    change 2 ≤ HierarchyPathNumber H at hpathLower
    change HierarchyPathNumber H < ell at hpathUpper
    omega
  have htailA : 3 ≤ T.length - A.length := by
    simpa [ell, HierarchyFullTailLength, H] using htail
  have hA : TreeSequenceInitialSegment A T := by
    have starNext (i : Fin (H.dividerCount + 1)) :
        TreeSequenceInitialSegment (HierarchyStarredStage H i) (H.stage i.succ) :=
      Fin.cases H.coreInsideFirst (fun i => H.nested i.succ) i
    simpa only [Fin.succ_last, H.terminalStage] using
      starNext (Fin.last H.dividerCount)
  have hell : ell = T.length - A.length := rfl
  have hBprefix : TreeSequenceInitialSegment B T := by
    exact ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
  have hXprefix : TreeSequenceInitialSegment X T := by
    exact ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
  have hlenB : B.length = T.length - 1 := by
    change min (A.length + (ell - 1)) T.length = T.length - 1
    simp only [ell, HierarchyFullTailLength] at *
    omega
  have hlenX : X.length = T.length - 2 := by
    change min (A.length + (ell - 2)) T.length = T.length - 2
    simp only [ell, HierarchyFullTailLength] at *
    omega
  have commonPrefix {S U W : TreeSequence G e0}
      (hSW : TreeSequenceInitialSegment S W)
      (hUW : TreeSequenceInitialSegment U W) (hlen : S.length ≤ U.length) :
      TreeSequenceInitialSegment S U := by
    exact hUW.of_common_extension hSW hlen
  have hAB : TreeSequenceInitialSegment A B := by
    apply commonPrefix hA hBprefix
    rw [hlenB]
    omega
  have hElem : ColoredVertexSetElementary G phi (TreeSequenceVertexSet B) := by
    exact HierarchyCounterexamplePenultimateElementary G k e0 input T phi ett base C
      ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
      ctx.lexicographicMinimality ctx.largeMissingSet
  have hcoreA : TreeSequenceVertexSet base.core ⊆ TreeSequenceVertexSet A := by
    by_cases hz : H.dividerCount = 0
    · have hq : q = 0 := Fin.ext (by simp [q, hz])
      simp [A, HierarchyStarredStage, hq]
    · let r : Fin H.dividerCount := ⟨H.dividerCount - 1, by omega⟩
      have hq : q = r.succ := by apply Fin.ext; simp [q, r]; omega
      have hAs : A = H.stage r.succ.castSucc := by
        change HierarchyStarredStage H q = _
        rw [hq]
        rfl
      rw [hAs]
      have stageMono : Monotone (fun j : Fin (H.dividerCount + 2) =>
          TreeSequenceVertexSet (H.stage j)) := by
        apply Fin.monotone_iff_le_succ.mpr
        intro j
        exact TreeSequenceInitialSegmentVertexSetSubset (H.nested j)
      exact (TreeSequenceInitialSegmentVertexSetSubset H.coreInsideFirst).trans
        (stageMono (by change 1 ≤ r.val + 1; omega))
  have hTnCore : TreeSequenceVertexSet Tn ⊆ TreeSequenceVertexSet base.core := by
    exact TreeSequenceInitialSegmentVertexSetSubset base.lastRoundInitialSegmentCore
  have hcoreB : TreeSequenceVertexSet base.core ⊆ TreeSequenceVertexSet B := by
    exact hcoreA.trans (TreeSequenceInitialSegmentVertexSetSubset
      (commonPrefix hA hBprefix (by rw [hlenB]; omega)))
  have hTnB : TreeSequenceVertexSet Tn ⊆ TreeSequenceVertexSet B := hTnCore.trans hcoreB
  have hownerAbsent : eta ∉ TreeMissingColors phi B := by
    simpa [B, ell] using habsent
  have hfirstEta : HierarchyFirstMissingPosition phi T eta = Fin.last T.length := by
    exact TreeSequenceFirstMissingPositionEqLastOfNotMemPrefix hBprefix
      (by simpa only [hlenB, Nat.sub_add_cancel T.positive] using (le_refl T.length)) hownerAbsent
  have hAlphaAvoid : ∀ r : Fin T.length, A.length ≤ r.val →
      phi (T.edge r) ≠ some alpha := by
    intro r hr hcol
    have havoid := C.good.avoidance q eta heta
    have hseg : alpha ∉ HierarchySegmentColors H q eta := by
      exact (Finset.mem_sdiff.mp (havoid hgamma)).2
    have hqstage : H.stage q.succ = T := by
      simpa only [q, Fin.succ_last] using H.terminalStage
    have hTedge : A.length ≤ r.val ∧ r.val < min (HierarchyFirstMissingPosition phi T eta).val
        (H.stage q.succ).length := by
      rw [hfirstEta, Fin.val_last, hqstage]
      simp only [min_self]
      exact ⟨hr, r.isLt⟩
    have : alpha ∈ HierarchySegmentColors H q eta := by
      let hlen : (H.stage q.succ).length = T.length := congrArg TreeSequence.length hqstage
      let s : Fin (H.stage q.succ).length := Fin.cast hlen.symm r
      have hsval : s.val = r.val := rfl
      have hstageT : TreeSequenceInitialSegment (H.stage q.succ) T := by
        rw [hqstage]
        exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
      have hcast : Fin.castLE hstageT.1 s = r := by
        apply Fin.ext
        rfl
      have hedge := hstageT.2.2 s
      rw [hcast] at hedge
      have hcol' : phi ((H.stage q.succ).edge s) = some alpha := by
        rw [← hedge]
        exact hcol
      simp only [HierarchySegmentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨s, ?_⟩
      rw [hfirstEta, Fin.val_last]
      refine ⟨?_, ?_, hcol'⟩
      · simpa [hsval] using hr
      · rw [hsval]
        have hslt := s.isLt
        have hrl := r.isLt
        omega
    exact hseg this
  exact @helper_continuation_212 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@alpha)
      (@hterminal) (@hstar) (@eta) (@heta) (@hgamma) (@htailA) (@hA) (@hell) (@hBprefix)
      (@hXprefix) (@hlenB) (@hlenX) (@commonPrefix) (@hAB) (@hElem) (@hcoreA) (@hcoreB)
      (@hAlphaAvoid)
end GoldbergSeymour

end
