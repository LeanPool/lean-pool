/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceTransport
public import LeanPool.GoldbergSeymour.HierarchyTailContinuationFacts

public import LeanPool.GoldbergSeymour.HierarchyTreeFacts

public import LeanPool.GoldbergSeymour.HierarchyFirstMissingPositionPrefixCutoff

public import LeanPool.GoldbergSeymour.SharedFacts.FirstSubcaseTransport

public import LeanPool.GoldbergSeymour.TwoColorComponentColoringFacts


public import LeanPool.GoldbergSeymour.HierarchySituationTwoCaseOneTwoData
public import LeanPool.GoldbergSeymour.HierarchySituationTwoSubcaseTwoOne
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentFacts

/-!
# Hierarchy Situation Two Subcase One Two

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev helperHfixedOne2200Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoCaseOneTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
        B.length + (1 : ℕ) = T.length → TreeSequenceInitialSegment B T → (H.dividerCount = (0 : ℕ)
        → A = base.core) → TreeSequenceInitialSegment A T → (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → phi (T.edge t) ≠ some D.gammaOne) → (
    ∀ (t : Fin ((fun (i : ℕ) ↦ TreeSequencePrefix T (min ((HierarchyStarredStage H (Fin.last
        H.dividerCount)).length + i) T.length) (
    have this : (1 : ℕ) ≤ T.length := T.positive;
    have this_1 : (1 : ℕ) ≤ (HierarchyStarredStage H (Fin.last H.dividerCount)).length :=
        (HierarchyStarredStage H (Fin.last H.dividerCount)).positive;
    have this_2 : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤
        min ((HierarchyStarredStage H (Fin.last H.dividerCount)).length + i) T.length) ↦
    by omega
    ) (
    have this : (1 : ℕ) ≤ T.length := T.positive;
    have this : (1 : ℕ) ≤ (HierarchyStarredStage H (Fin.last H.dividerCount)).length :=
        (HierarchyStarredStage H (Fin.last H.dividerCount)).positive;
    have this : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a : ¬min
        ((HierarchyStarredStage H (Fin.last H.dividerCount)).length + i) T.length ≤ T.length) ↦
    by omega
    )) (HierarchyFullTailLength C - (1 : ℕ))).length), (HierarchyStarredStage H (Fin.last
        H.dividerCount)).length ≤ (↑t : ℕ) → (↑t : ℕ) < (HierarchyStarredStage H (Fin.last
        H.dividerCount)).length + (HierarchyFullTailLength C - (1 : ℕ)) → phi (((fun (i : ℕ) ↦
        TreeSequencePrefix T (min ((HierarchyStarredStage H (Fin.last H.dividerCount)).length + i)
        T.length) (
    have this : (1 : ℕ) ≤ T.length := T.positive;
    have this_1 : (1 : ℕ) ≤ (HierarchyStarredStage H (Fin.last H.dividerCount)).length :=
        (HierarchyStarredStage H (Fin.last H.dividerCount)).positive;
    have this_2 : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤
        min ((HierarchyStarredStage H (Fin.last H.dividerCount)).length + i) T.length) ↦
    by omega
    ) (
    have this : (1 : ℕ) ≤ T.length := T.positive;
    have this : (1 : ℕ) ≤ (HierarchyStarredStage H (Fin.last H.dividerCount)).length :=
        (HierarchyStarredStage H (Fin.last H.dividerCount)).positive;
    have this : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a : ¬min
        ((HierarchyStarredStage H (Fin.last H.dividerCount)).length + i) T.length ≤ T.length) ↦
    by omega
    )) (HierarchyFullTailLength C - (1 : ℕ))).edge t) = some D.alpha → H.dividerCount = (0 : ℕ) ∧
        base.core = ett.series.data.tree (Fin.last ett.rounds).castSucc ∧ (↑t : ℕ) =
        (HierarchyStarredStage H (Fin.last H.dividerCount)).length ∧
    ∃ (f : E), TashkinovSeriesStep G k ett.rounds e0 input ett.series.data (Fin.last ett.rounds) ∧
        (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.SE ∨
        ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.RE) ∧
        ett.series.data.connectingEdges (Fin.last ett.rounds) = ({ f } : Finset E) ∧ ((fun (i : ℕ)
        ↦ TreeSequencePrefix T (min ((HierarchyStarredStage H (Fin.last H.dividerCount)).length +
        i) T.length) (
    have this : (1 : ℕ) ≤ T.length := T.positive;
    have this_1 : (1 : ℕ) ≤ (HierarchyStarredStage H (Fin.last H.dividerCount)).length :=
        (HierarchyStarredStage H (Fin.last H.dividerCount)).positive;
    have this_2 : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤
        min ((HierarchyStarredStage H (Fin.last H.dividerCount)).length + i) T.length) ↦
    by omega
    ) (
    have this : (1 : ℕ) ≤ T.length := T.positive;
    have this : (1 : ℕ) ≤ (HierarchyStarredStage H (Fin.last H.dividerCount)).length :=
        (HierarchyStarredStage H (Fin.last H.dividerCount)).positive;
    have this : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a : ¬min
        ((HierarchyStarredStage H (Fin.last H.dividerCount)).length + i) T.length ≤ T.length) ↦
    by omega
    )) (HierarchyFullTailLength C - (1 : ℕ))).edge t = f ∧ phi f = some D.alpha ∧ D.alpha ∈
        TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) →
    let z : V ⊕ E := Sum.inl (T.vertex D.terminalVertexIndex);
    let muOne : PartialEdgeColoring E k := TwoColorComponentSwap G phi D.gammaOne D.alpha z; (
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    have n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    have Tnq : TreeSequence G e0 := H.stage (⟨H.dividerCount,
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)));
    have Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    have Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q; HierarchyWeaklyStable H q muOne ∧
        ModColoring ett muOne ∧ (A = Tn ∨
    ∃ (inputA : PartialEdgeColoring E k) (ettA : ExtendedTashkinovTree G k e0 inputA A muOne),
        MaximumProperty ettA) ∧ ((0 : ℕ) < H.dividerCount →
    ∃ (inputA : PartialEdgeColoring E k) (ettA : ExtendedTashkinovTree G k e0 inputA A muOne)
        (baseA : HierarchyBase ettA muOne) (K : TashkinovHierarchy ettA baseA) (goodA :
        GoodHierarchy K), MaximumProperty ettA ∧ ettA.series.data.kind (Fin.last ettA.rounds) =
        ett.series.data.kind (Fin.last ett.rounds) ∧
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
        TreeColorSetMinusClosed G muOne Tnq (Dnq.biUnion (C.good.gamma (⟨C.hierarchy.dividerCount
        - (1 : ℕ),
    by omega
    ⟩ : Fin (C.hierarchy.dividerCount + (1 : ℕ))))))) → (
    ∀ (X : TreeSequence G e0), TreeSequenceInitialSegment X T →
    ∀ (t : Fin T.length), (↑t : ℕ) = X.length → TreeIncidentEdge X (T.edge t)) → Incident G
        (T.vertex D.terminalVertexIndex) (T.edge D.lastEdgeIndex) → (
    ∀ (rho : PartialEdgeColoring E k) (c : Fin k) (v : V), c ∈ MissingColors G rho v →
    ∀ (e : E), Incident G v e → rho e ≠ some c) → (
    ∀ {input' : PartialEdgeColoring E k} (rho sigma : PartialEdgeColoring E k) (ett' :
        ExtendedTashkinovTree G k e0 input' T rho) (base' : HierarchyBase ett' rho) (K :
        TashkinovHierarchy ett' base'), HierarchyWeaklyStable K (Fin.last K.dividerCount) sigma →
        K.dividerCount = (0 : ℕ) → StableColoring (ett'.series.data.tree (Fin.last
        ett'.rounds).castSucc) (TashkinovStoredColors ett'.series.data (Fin.last ett'.rounds)) rho
        sigma) →
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → muOne (T.edge t) = phi (T.edge t)

private abbrev helperHfixedTailTwo2433Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoCaseOneTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
        B.length + (1 : ℕ) = T.length → TreeSequenceInitialSegment B T → (H.dividerCount = (0 : ℕ)
        → A = base.core) → TreeSequenceInitialSegment A T → (
    ∀ {c : Fin k}, c ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex) → c ∉
        TreeMissingColors phi A) → (
    ∀ (t : Fin ((fun (i : ℕ) ↦ TreeSequencePrefix T (min ((HierarchyStarredStage H (Fin.last
        H.dividerCount)).length + i) T.length) (
    have this : (1 : ℕ) ≤ T.length := T.positive;
    have this_1 : (1 : ℕ) ≤ (HierarchyStarredStage H (Fin.last H.dividerCount)).length :=
        (HierarchyStarredStage H (Fin.last H.dividerCount)).positive;
    have this_2 : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤
        min ((HierarchyStarredStage H (Fin.last H.dividerCount)).length + i) T.length) ↦
    by omega
    ) (
    have this : (1 : ℕ) ≤ T.length := T.positive;
    have this : (1 : ℕ) ≤ (HierarchyStarredStage H (Fin.last H.dividerCount)).length :=
        (HierarchyStarredStage H (Fin.last H.dividerCount)).positive;
    have this : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a : ¬min
        ((HierarchyStarredStage H (Fin.last H.dividerCount)).length + i) T.length ≤ T.length) ↦
    by omega
    )) (HierarchyFullTailLength C - (1 : ℕ))).length), (HierarchyStarredStage H (Fin.last
        H.dividerCount)).length ≤ (↑t : ℕ) → (↑t : ℕ) < (HierarchyStarredStage H (Fin.last
        H.dividerCount)).length + (HierarchyFullTailLength C - (1 : ℕ)) → phi (((fun (i : ℕ) ↦
        TreeSequencePrefix T (min ((HierarchyStarredStage H (Fin.last H.dividerCount)).length + i)
        T.length) (
    have this : (1 : ℕ) ≤ T.length := T.positive;
    have this_1 : (1 : ℕ) ≤ (HierarchyStarredStage H (Fin.last H.dividerCount)).length :=
        (HierarchyStarredStage H (Fin.last H.dividerCount)).positive;
    have this_2 : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤
        min ((HierarchyStarredStage H (Fin.last H.dividerCount)).length + i) T.length) ↦
    by omega
    ) (
    have this : (1 : ℕ) ≤ T.length := T.positive;
    have this : (1 : ℕ) ≤ (HierarchyStarredStage H (Fin.last H.dividerCount)).length :=
        (HierarchyStarredStage H (Fin.last H.dividerCount)).positive;
    have this : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a : ¬min
        ((HierarchyStarredStage H (Fin.last H.dividerCount)).length + i) T.length ≤ T.length) ↦
    by omega
    )) (HierarchyFullTailLength C - (1 : ℕ))).edge t) = some D.theta → H.dividerCount = (0 : ℕ) ∧
        base.core = ett.series.data.tree (Fin.last ett.rounds).castSucc ∧ (↑t : ℕ) =
        (HierarchyStarredStage H (Fin.last H.dividerCount)).length ∧
    ∃ (f : E), TashkinovSeriesStep G k ett.rounds e0 input ett.series.data (Fin.last ett.rounds) ∧
        (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.SE ∨
        ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.RE) ∧
        ett.series.data.connectingEdges (Fin.last ett.rounds) = ({ f } : Finset E) ∧ ((fun (i : ℕ)
        ↦ TreeSequencePrefix T (min ((HierarchyStarredStage H (Fin.last H.dividerCount)).length +
        i) T.length) (
    have this : (1 : ℕ) ≤ T.length := T.positive;
    have this_1 : (1 : ℕ) ≤ (HierarchyStarredStage H (Fin.last H.dividerCount)).length :=
        (HierarchyStarredStage H (Fin.last H.dividerCount)).positive;
    have this_2 : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤
        min ((HierarchyStarredStage H (Fin.last H.dividerCount)).length + i) T.length) ↦
    by omega
    ) (
    have this : (1 : ℕ) ≤ T.length := T.positive;
    have this : (1 : ℕ) ≤ (HierarchyStarredStage H (Fin.last H.dividerCount)).length :=
        (HierarchyStarredStage H (Fin.last H.dividerCount)).positive;
    have this : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a : ¬min
        ((HierarchyStarredStage H (Fin.last H.dividerCount)).length + i) T.length ≤ T.length) ↦
    by omega
    )) (HierarchyFullTailLength C - (1 : ℕ))).edge t = f ∧ phi f = some D.theta ∧ D.theta ∈
        TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) →
    let z : V ⊕ E := Sum.inl (T.vertex D.terminalVertexIndex);
    let muOne : PartialEdgeColoring E k := TwoColorComponentSwap G phi D.gammaOne D.alpha z; (
    ∀ (X : TreeSequence G e0), TreeSequenceInitialSegment X T →
    ∀ (t : Fin T.length), (↑t : ℕ) = X.length → TreeIncidentEdge X (T.edge t)) → (
    ∀ {input' : PartialEdgeColoring E k} (rho sigma : PartialEdgeColoring E k) (ett' :
        ExtendedTashkinovTree G k e0 input' T rho) (base' : HierarchyBase ett' rho) (K :
        TashkinovHierarchy ett' base'), HierarchyWeaklyStable K (Fin.last K.dividerCount) sigma →
        K.dividerCount = (0 : ℕ) → StableColoring (ett'.series.data.tree (Fin.last
        ett'.rounds).castSucc) (TashkinovStoredColors ett'.series.data (Fin.last ett'.rounds)) rho
        sigma) → (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → muOne (T.edge t) = phi (T.edge t)) →
    ∀ (POne : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), POne.coloring =
        muOne →
    let rho : PartialEdgeColoring E k := POne.coloring;
    let ettOne : ExtendedTashkinovTree G k e0 POne.corresponding.replacementInput T POne.coloring
        := POne.corresponding.replacementETT;
    let baseOne' : HierarchyBase POne.corresponding.replacementETT POne.coloring :=
        POne.replacementBase;
    let COne' : HierarchyCounterexample POne.replacementBase := POne.counterexample;
    let HOne : TashkinovHierarchy POne.corresponding.replacementETT POne.replacementBase :=
        COne'.hierarchy;
    let qOne : Fin (HOne.dividerCount + (1 : ℕ)) := Fin.last HOne.dividerCount; (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → rho (T.edge t) ≠ some D.gammaOne) →
    let muTwo : PartialEdgeColoring E k := TwoColorComponentSwap G rho D.gammaOne D.theta z; (
    let H : TashkinovHierarchy ettOne baseOne' := COne'.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    have n : Fin (ettOne.rounds + (1 : ℕ)) := Fin.last ettOne.rounds;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    have Tnq : TreeSequence G e0 := H.stage (⟨H.dividerCount,
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)));
    have Tn : TreeSequence G e0 := ettOne.series.data.tree n.castSucc;
    have Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q; HierarchyWeaklyStable H q muTwo ∧
        ModColoring ettOne muTwo ∧ (A = Tn ∨
    ∃ (inputA : PartialEdgeColoring E k) (ettA : ExtendedTashkinovTree G k e0 inputA A muTwo),
        MaximumProperty ettA) ∧ ((0 : ℕ) < H.dividerCount →
    ∃ (inputA : PartialEdgeColoring E k) (ettA : ExtendedTashkinovTree G k e0 inputA A muTwo)
        (baseA : HierarchyBase ettA muTwo) (K : TashkinovHierarchy ettA baseA) (goodA :
        GoodHierarchy K), MaximumProperty ettA ∧ ettA.series.data.kind (Fin.last ettA.rounds) =
        ettOne.series.data.kind (Fin.last ettOne.rounds) ∧
    ∃ (hcount : K.dividerCount + (1 : ℕ) = H.dividerCount), baseA.core = baseOne'.core ∧
        baseA.closure = baseOne'.closure ∧ (
    ∀ (j : Fin (K.dividerCount + (2 : ℕ))), K.stage j = H.stage (⟨(↑j : ℕ),
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) ∧ (
    ∀ (j : Fin (K.dividerCount + (1 : ℕ))),
    have jH : Fin (H.dividerCount + (1 : ℕ)) := (⟨(↑j : ℕ),
    by omega
    ⟩ : Fin (H.dividerCount + (1 : ℕ))); HierarchyStoredColorsAt K j = HierarchyStoredColorsAt H
        jH ∧
    ∀ eta ∈ HierarchyStoredColorsAt K j, goodA.gamma j eta = COne'.good.gamma jH eta) ∧
        TreeColorSetMinusClosed G muTwo Tnq (Dnq.biUnion (COne'.good.gamma
        (⟨COne'.hierarchy.dividerCount - (1 : ℕ),
    by omega
    ⟩ : Fin (COne'.hierarchy.dividerCount + (1 : ℕ))))))) →
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < B.length → muTwo (T.edge t) = rho
        (T.edge t)

private abbrev helperContinuation1912Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoCaseOneTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
        (2 : ℕ) ≤ T.length - A.length → B.length + (1 : ℕ) = T.length → TreeSequenceInitialSegment
        B T → (H.dividerCount = (0 : ℕ) → A = base.core) → TreeSequenceInitialSegment A T →
        TreeSequenceInitialSegment A B → T.vertex D.penultimateVertexIndex ∈ TreeSequenceVertexSet
        B → ColoredVertexSetElementary G phi (TreeSequenceVertexSet B) →
        HierarchyFirstMissingPosition phi T D.alpha = D.penultimateVertexIndex →
        HierarchyFirstMissingPosition phi T D.theta = D.penultimateVertexIndex → (
    ∀ {c : Fin k}, c ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex) → c ∉
        TreeMissingColors phi A) → D.gammaOne ∈ TreeMissingColors phi A → D.gammaOne ≠ D.theta →
        D.gammaOne ≠ D.alpha → (
    ∀ (t : Fin ((fun (i : ℕ) ↦ TreeSequencePrefix T (min ((HierarchyStarredStage H (Fin.last
        H.dividerCount)).length + i) T.length) (
    by
                          have := TreeSequence.positive T
                          have :=
                           TreeSequence.positive (HierarchyStarredStage H (Fin.last H.dividerCount))
                          have := TreeSequence.positive T
                          omega
    ) (
    by
                          have := TreeSequence.positive T
                          have :=
                           TreeSequence.positive (HierarchyStarredStage H (Fin.last H.dividerCount))
                          have := TreeSequence.positive T
                          omega
    )) (HierarchyFullTailLength C - (1 : ℕ))).length), (HierarchyStarredStage H (Fin.last
        H.dividerCount)).length ≤ (↑t : ℕ) → (↑t : ℕ) < (HierarchyStarredStage H (Fin.last
        H.dividerCount)).length + (HierarchyFullTailLength C - (1 : ℕ)) → phi (((fun (i : ℕ) ↦
        TreeSequencePrefix T (min ((HierarchyStarredStage H (Fin.last H.dividerCount)).length + i)
        T.length) (
    by
                              have := TreeSequence.positive T
                              have :=
                               TreeSequence.positive
                                (HierarchyStarredStage H (Fin.last H.dividerCount))
                              have := TreeSequence.positive T
                              omega
    ) (
    by
                              have := TreeSequence.positive T
                              have :=
                               TreeSequence.positive
                                (HierarchyStarredStage H (Fin.last H.dividerCount))
                              have := TreeSequence.positive T
                              omega
    )) (HierarchyFullTailLength C - (1 : ℕ))).edge t) = some D.theta → H.dividerCount = (0 : ℕ) ∧
        base.core = ett.series.data.tree (Fin.last ett.rounds).castSucc ∧ (↑t : ℕ) =
        (HierarchyStarredStage H (Fin.last H.dividerCount)).length ∧
    ∃ (f : E), TashkinovSeriesStep G k ett.rounds e0 input ett.series.data (Fin.last ett.rounds) ∧
        (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.SE ∨
        ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.RE) ∧
        ett.series.data.connectingEdges (Fin.last ett.rounds) = ({ f } : Finset E) ∧ ((fun (i : ℕ)
        ↦ TreeSequencePrefix T (min ((HierarchyStarredStage H (Fin.last H.dividerCount)).length +
        i) T.length) (
    by
                                     have := TreeSequence.positive T
                                     have :=
                                      TreeSequence.positive
                                       (HierarchyStarredStage H (Fin.last H.dividerCount))
                                     have := TreeSequence.positive T
                                     omega
    ) (
    by
                                     have := TreeSequence.positive T
                                     have :=
                                      TreeSequence.positive
                                       (HierarchyStarredStage H (Fin.last H.dividerCount))
                                     have := TreeSequence.positive T
                                     omega
    )) (HierarchyFullTailLength C - (1 : ℕ))).edge t = f ∧ phi f = some D.theta ∧ D.theta ∈
        TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) → (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → phi (T.edge t) ≠ some D.gammaOne) → (
    ∀ (t : Fin ((fun (i : ℕ) ↦ TreeSequencePrefix T (min ((HierarchyStarredStage H (Fin.last
        H.dividerCount)).length + i) T.length) (
    by
                            have := TreeSequence.positive T
                            have :=
                             TreeSequence.positive
                              (HierarchyStarredStage H (Fin.last H.dividerCount))
                            have := TreeSequence.positive T
                            omega
    ) (
    by
                            have := TreeSequence.positive T
                            have :=
                             TreeSequence.positive
                              (HierarchyStarredStage H (Fin.last H.dividerCount))
                            have := TreeSequence.positive T
                            omega
    )) (HierarchyFullTailLength C - (1 : ℕ))).length), (HierarchyStarredStage H (Fin.last
        H.dividerCount)).length ≤ (↑t : ℕ) → (↑t : ℕ) < (HierarchyStarredStage H (Fin.last
        H.dividerCount)).length + (HierarchyFullTailLength C - (1 : ℕ)) → phi (((fun (i : ℕ) ↦
        TreeSequencePrefix T (min ((HierarchyStarredStage H (Fin.last H.dividerCount)).length + i)
        T.length) (
    by
                                have := TreeSequence.positive T
                                have :=
                                 TreeSequence.positive
                                  (HierarchyStarredStage H (Fin.last H.dividerCount))
                                have := TreeSequence.positive T
                                omega
    ) (
    by
                                have := TreeSequence.positive T
                                have :=
                                 TreeSequence.positive
                                  (HierarchyStarredStage H (Fin.last H.dividerCount))
                                have := TreeSequence.positive T
                                omega
    )) (HierarchyFullTailLength C - (1 : ℕ))).edge t) = some D.alpha → H.dividerCount = (0 : ℕ) ∧
        base.core = ett.series.data.tree (Fin.last ett.rounds).castSucc ∧ (↑t : ℕ) =
        (HierarchyStarredStage H (Fin.last H.dividerCount)).length ∧
    ∃ (f : E), TashkinovSeriesStep G k ett.rounds e0 input ett.series.data (Fin.last ett.rounds) ∧
        (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.SE ∨
        ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.RE) ∧
        ett.series.data.connectingEdges (Fin.last ett.rounds) = ({ f } : Finset E) ∧ ((fun (i : ℕ)
        ↦ TreeSequencePrefix T (min ((HierarchyStarredStage H (Fin.last H.dividerCount)).length +
        i) T.length) (
    by
                                       have := TreeSequence.positive T
                                       have :=
                                        TreeSequence.positive
                                         (HierarchyStarredStage H (Fin.last H.dividerCount))
                                       have := TreeSequence.positive T
                                       omega
    ) (
    by
                                       have := TreeSequence.positive T
                                       have :=
                                        TreeSequence.positive
                                         (HierarchyStarredStage H (Fin.last H.dividerCount))
                                       have := TreeSequence.positive T
                                       omega
    )) (HierarchyFullTailLength C - (1 : ℕ))).edge t = f ∧ phi f = some D.alpha ∧ D.alpha ∈
        TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) → (
    ∀ (rho : PartialEdgeColoring E k) (X : TreeSequence G e0), TreeSequenceInitialSegment X T →
    ∀ c ∈ TreeMissingColors rho X, c ∈ MissingColors G rho (T.vertex
        (HierarchyFirstMissingPosition rho T c)) ∧ (↑(HierarchyFirstMissingPosition rho T c) : ℕ)
        ≤ X.length) →
    let ig : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T D.gammaOne;
        D.gammaOne ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T
        D.gammaOne)) ∧ (↑(HierarchyFirstMissingPosition phi T D.gammaOne) : ℕ) ≤ A.length →
        T.vertex ig ∈ TreeSequenceVertexSet B → (0 : ℕ) < H.dividerCount ∧ D.gammaOne ∈
        TreeMissingColors phi (H.stage (⟨H.dividerCount,
    by
                               have := TreeSequence.positive T
                               omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) ∨ H.dividerCount = (0 : ℕ) ∧ D.gammaOne ∈
        TreeMissingColors phi (ett.series.data.tree (Fin.last ett.rounds).castSucc) → D.gammaOne ∈
        TreeMissingColors phi B ∧ D.alpha ∈ TreeMissingColors phi B → TwoColorComponent G phi
        D.gammaOne D.alpha (Sum.inl (T.vertex ig)) = TwoColorComponent G phi D.gammaOne D.alpha
        (Sum.inl (T.vertex D.penultimateVertexIndex)) → (
    ∀ (rho : PartialEdgeColoring E k) (a b : Fin k) (v : V), Sum.inl v ∈ TwoColorComponent G rho a
        b (Sum.inl v)) → (
    ∀ (rho : PartialEdgeColoring E k) (a b : Fin k), a ≠ b → IsProperEdgeColoring G rho →
    ∀ (v : V), a ∈ MissingColors G rho v ∨ b ∈ MissingColors G rho v → ((TwoColorIncidenceGraph G
        rho a b).neighborSet (Sum.inl v)).Subsingleton) → (
    ∀ (rho : PartialEdgeColoring E k) (a b : Fin k), a ≠ b → IsProperEdgeColoring G rho →
    ∀ (u v w : V), u ≠ v → u ≠ w → v ≠ w → a ∈ MissingColors G rho u → b ∈ MissingColors G rho v →
        a ∈ MissingColors G rho w ∨ b ∈ MissingColors G rho w → TwoColorComponent G rho a b
        (Sum.inl u) = TwoColorComponent G rho a b (Sum.inl v) → Disjoint (TwoColorComponent G rho
        a b (Sum.inl w)) (TwoColorComponent G rho a b (Sum.inl u))) → T.vertex ig ≠ T.vertex
        D.penultimateVertexIndex → T.vertex ig ≠ T.vertex D.terminalVertexIndex → False

private abbrev helperContinuation2860Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoCaseOneTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
        (2 : ℕ) ≤ T.length - A.length → B.length + (1 : ℕ) = T.length → TreeSequenceInitialSegment
        B T → (H.dividerCount = (0 : ℕ) → A = base.core) → TreeSequenceInitialSegment A T →
        TreeSequenceInitialSegment A B → T.vertex D.penultimateVertexIndex ∈ TreeSequenceVertexSet
        B → ColoredVertexSetElementary G phi (TreeSequenceVertexSet B) →
        HierarchyFirstMissingPosition phi T D.alpha = D.penultimateVertexIndex →
        HierarchyFirstMissingPosition phi T D.theta = D.penultimateVertexIndex → (
    ∀ {c : Fin k}, c ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex) → c ∉
        TreeMissingColors phi A) → D.gammaOne ∈ TreeMissingColors phi A → D.gammaOne ≠ D.theta → (
    ∀ (t : Fin ((fun (i : ℕ) ↦ TreeSequencePrefix T (min ((HierarchyStarredStage H (Fin.last
        H.dividerCount)).length + i) T.length) (
    have this : (1 : ℕ) ≤ T.length := T.positive;
    have this_1 : (1 : ℕ) ≤ (HierarchyStarredStage H (Fin.last H.dividerCount)).length :=
        (HierarchyStarredStage H (Fin.last H.dividerCount)).positive;
    have this_2 : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤
        min ((HierarchyStarredStage H (Fin.last H.dividerCount)).length + i) T.length) ↦
    by omega
    ) (
    have this : (1 : ℕ) ≤ T.length := T.positive;
    have this : (1 : ℕ) ≤ (HierarchyStarredStage H (Fin.last H.dividerCount)).length :=
        (HierarchyStarredStage H (Fin.last H.dividerCount)).positive;
    have this : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a : ¬min
        ((HierarchyStarredStage H (Fin.last H.dividerCount)).length + i) T.length ≤ T.length) ↦
    by omega
    )) (HierarchyFullTailLength C - (1 : ℕ))).length), (HierarchyStarredStage H (Fin.last
        H.dividerCount)).length ≤ (↑t : ℕ) → (↑t : ℕ) < (HierarchyStarredStage H (Fin.last
        H.dividerCount)).length + (HierarchyFullTailLength C - (1 : ℕ)) → phi (((fun (i : ℕ) ↦
        TreeSequencePrefix T (min ((HierarchyStarredStage H (Fin.last H.dividerCount)).length + i)
        T.length) (
    have this : (1 : ℕ) ≤ T.length := T.positive;
    have this_1 : (1 : ℕ) ≤ (HierarchyStarredStage H (Fin.last H.dividerCount)).length :=
        (HierarchyStarredStage H (Fin.last H.dividerCount)).positive;
    have this_2 : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤
        min ((HierarchyStarredStage H (Fin.last H.dividerCount)).length + i) T.length) ↦
    by omega
    ) (
    have this : (1 : ℕ) ≤ T.length := T.positive;
    have this : (1 : ℕ) ≤ (HierarchyStarredStage H (Fin.last H.dividerCount)).length :=
        (HierarchyStarredStage H (Fin.last H.dividerCount)).positive;
    have this : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a : ¬min
        ((HierarchyStarredStage H (Fin.last H.dividerCount)).length + i) T.length ≤ T.length) ↦
    by omega
    )) (HierarchyFullTailLength C - (1 : ℕ))).edge t) = some D.theta → H.dividerCount = (0 : ℕ) ∧
        base.core = ett.series.data.tree (Fin.last ett.rounds).castSucc ∧ (↑t : ℕ) =
        (HierarchyStarredStage H (Fin.last H.dividerCount)).length ∧
    ∃ (f : E), TashkinovSeriesStep G k ett.rounds e0 input ett.series.data (Fin.last ett.rounds) ∧
        (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.SE ∨
        ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.RE) ∧
        ett.series.data.connectingEdges (Fin.last ett.rounds) = ({ f } : Finset E) ∧ ((fun (i : ℕ)
        ↦ TreeSequencePrefix T (min ((HierarchyStarredStage H (Fin.last H.dividerCount)).length +
        i) T.length) (
    have this : (1 : ℕ) ≤ T.length := T.positive;
    have this_1 : (1 : ℕ) ≤ (HierarchyStarredStage H (Fin.last H.dividerCount)).length :=
        (HierarchyStarredStage H (Fin.last H.dividerCount)).positive;
    have this_2 : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤
        min ((HierarchyStarredStage H (Fin.last H.dividerCount)).length + i) T.length) ↦
    by omega
    ) (
    have this : (1 : ℕ) ≤ T.length := T.positive;
    have this : (1 : ℕ) ≤ (HierarchyStarredStage H (Fin.last H.dividerCount)).length :=
        (HierarchyStarredStage H (Fin.last H.dividerCount)).positive;
    have this : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a : ¬min
        ((HierarchyStarredStage H (Fin.last H.dividerCount)).length + i) T.length ≤ T.length) ↦
    by omega
    )) (HierarchyFullTailLength C - (1 : ℕ))).edge t = f ∧ phi f = some D.theta ∧ D.theta ∈
        TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) → (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → phi (T.edge t) ≠ some D.gammaOne) →
    let ig : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T D.gammaOne;
        D.gammaOne ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T
        D.gammaOne)) ∧ (↑(HierarchyFirstMissingPosition phi T D.gammaOne) : ℕ) ≤ A.length →
        T.vertex ig ∈ TreeSequenceVertexSet B → D.gammaOne ∈ TreeMissingColors phi B ∧ D.alpha ∈
        TreeMissingColors phi B → (
    ∀ (rho : PartialEdgeColoring E k) (a b : Fin k) (v : V), Sum.inl v ∈ TwoColorComponent G rho a
        b (Sum.inl v)) → (
    ∀ (rho : PartialEdgeColoring E k) (a b : Fin k), a ≠ b → IsProperEdgeColoring G rho →
    ∀ (v : V), a ∈ MissingColors G rho v ∨ b ∈ MissingColors G rho v → ((TwoColorIncidenceGraph G
        rho a b).neighborSet (Sum.inl v)).Subsingleton) → (
    ∀ (rho : PartialEdgeColoring E k) (a b : Fin k), a ≠ b → IsProperEdgeColoring G rho →
    ∀ (u v w : V), u ≠ v → u ≠ w → v ≠ w → a ∈ MissingColors G rho u → b ∈ MissingColors G rho v →
        a ∈ MissingColors G rho w ∨ b ∈ MissingColors G rho w → TwoColorComponent G rho a b
        (Sum.inl u) = TwoColorComponent G rho a b (Sum.inl v) → Disjoint (TwoColorComponent G rho
        a b (Sum.inl w)) (TwoColorComponent G rho a b (Sum.inl u))) → T.vertex ig ≠ T.vertex
        D.penultimateVertexIndex → T.vertex ig ≠ T.vertex D.terminalVertexIndex → T.vertex
        D.penultimateVertexIndex ≠ T.vertex D.terminalVertexIndex →
    let z : V ⊕ E := Sum.inl (T.vertex D.terminalVertexIndex);
    let muOne : PartialEdgeColoring E k := TwoColorComponentSwap G phi D.gammaOne D.alpha z; (
    ∀ (rho : PartialEdgeColoring E k) (a b : Fin k), a ≠ b → IsProperEdgeColoring G rho →
        ColoredVertexSetElementary G rho (TreeSequenceVertexSet B) →
    ∀ (u v : V), u ∈ TreeSequenceVertexSet B → v ∈ TreeSequenceVertexSet B → a ∈ MissingColors G
        rho u → b ∈ MissingColors G rho v → Sum.inl u ∉ TwoColorComponent G rho a b z → Sum.inl v
        ∉ TwoColorComponent G rho a b z →
    ∀ w ∈ TreeSequenceVertexSet B, MissingColors G (TwoColorComponentSwap G rho a b z) w =
        MissingColors G rho w) → (
    ∀ (X : TreeSequence G e0), TreeSequenceInitialSegment X T →
    ∀ (t : Fin T.length), (↑t : ℕ) = X.length → TreeIncidentEdge X (T.edge t)) → Incident G
        (T.vertex D.terminalVertexIndex) (T.edge D.lastEdgeIndex) → (
    ∀ {input' : PartialEdgeColoring E k} (rho sigma : PartialEdgeColoring E k) (ett' :
        ExtendedTashkinovTree G k e0 input' T rho) (base' : HierarchyBase ett' rho) (K :
        TashkinovHierarchy ett' base'), HierarchyWeaklyStable K (Fin.last K.dividerCount) sigma →
        K.dividerCount = (0 : ℕ) → StableColoring (ett'.series.data.tree (Fin.last
        ett'.rounds).castSucc) (TashkinovStoredColors ett'.series.data (Fin.last ett'.rounds)) rho
        sigma) → (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → muOne (T.edge t) = phi (T.edge t)) → (
    ∀ (rho sigma : PartialEdgeColoring E k) (c : Fin k), (
    ∀ v ∈ TreeSequenceVertexSet B, MissingColors G sigma v = MissingColors G rho v) → c ∈
        TreeMissingColors rho B → HierarchyFirstMissingPosition sigma T c =
        HierarchyFirstMissingPosition rho T c) → (
    ∀ (rho : PartialEdgeColoring E k) (a b c : Fin k), a ≠ b → IsProperEdgeColoring G rho → c ≠ a
        → c ≠ b → HierarchyFirstMissingPosition (TwoColorComponentSwap G rho a b z) T c =
        HierarchyFirstMissingPosition rho T c) → D.gammaOne ∈ MissingColors G muOne (T.vertex
        D.terminalVertexIndex) →
    ∀ (POne : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), POne.coloring =
        muOne → (
    ∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage P.counterexample.hierarchy (Fin.last
        P.counterexample.hierarchy.dividerCount) = A) → (
    ∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyFullTailPrefix P.counterexample (HierarchyFullTailLength P.counterexample - (1 :
        ℕ)) = B) →
    let rho : PartialEdgeColoring E k := POne.coloring;
    let ettOne : ExtendedTashkinovTree G k e0 POne.corresponding.replacementInput T POne.coloring
        := POne.corresponding.replacementETT;
    let baseOne' : HierarchyBase POne.corresponding.replacementETT POne.coloring :=
        POne.replacementBase;
    let COne' : HierarchyCounterexample POne.replacementBase := POne.counterexample;
    let ctxOne : HierarchyMinimumCounterexampleContext G k e0 POne.corresponding.replacementInput
        T POne.coloring POne.corresponding.replacementETT POne.replacementBase POne.counterexample
        := POne.minimumContext;
    let HOne : TashkinovHierarchy POne.corresponding.replacementETT POne.replacementBase :=
        COne'.hierarchy;
    let qOne : Fin (HOne.dividerCount + (1 : ℕ)) := Fin.last HOne.dividerCount; (
    ∀ v ∈ TreeSequenceVertexSet B, MissingColors G rho v = MissingColors G phi v) → False

private theorem helper_hApositive_116.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q; (0 : ℕ) < H.dividerCount → A = H.stage
        (⟨H.dividerCount,
    by
            have := TreeSequence.positive T
            omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ))) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q A hq
  have hi : q = (⟨H.dividerCount - 1, by omega⟩ : Fin H.dividerCount).succ := by
    apply Fin.ext
    simp [q]
    omega
  change HierarchyStarredStage H q = _
  rw [hi]
  simp only [HierarchyStarredStage, Fin.cases_succ]
  congr 1
  apply Fin.ext
  simp
  omega

private theorem helper_hAB_146.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
        (2 : ℕ) ≤ T.length - A.length → B.length + (1 : ℕ) = T.length → ((0 : ℕ) < H.dividerCount
        → A = H.stage (⟨H.dividerCount,
    by
                have := TreeSequence.positive T
                omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) → (H.dividerCount = (0 : ℕ) → A = base.core) →
        TreeSequenceInitialSegment A T → TreeSequenceInitialSegment A B := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q A B htail hBlen hApositive hAzero hAT
  refine ⟨by omega, ?_, ?_⟩
  · intro i
    exact hAT.2.1 i
  · intro i
    exact hAT.2.2 i

private theorem helper_hBterminal_152.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoCaseOneTwoData G k e0 input T phi ett base C ctx),
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
        B.length + (1 : ℕ) = T.length → TreeSequenceInitialSegment B T → B.vertex (Fin.last
        B.length) = T.vertex D.penultimateVertexIndex := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D B hBlen hBT
  rw [← hBT.2.1 (Fin.last B.length)]
  congr 1
  apply Fin.ext
  have hp := D.penultimateVertexPosition
  simp only [Fin.val_castLE, Fin.val_last]
  omega

private theorem helper_hgammaUnused_232.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoCaseOneTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q; HierarchyFirstMissingPosition phi T
        D.alpha = D.penultimateVertexIndex → HierarchyFirstMissingPosition phi T D.theta =
        D.penultimateVertexIndex → D.gammaOne ∈ C.good.gamma q D.alpha → D.gammaOne ≠ D.theta →
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → phi (T.edge t) ≠ some D.gammaOne := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A hfirstAlpha hfirstTheta hgammaPair
      hgammaTheta t ht he
  by_cases hlast : t = D.lastEdgeIndex
  · rw [hlast, D.thetaOnLastEdge] at he
    exact hgammaTheta (Option.some.inj he).symm
  · have hav := (Finset.mem_sdiff.mp
      (C.good.avoidance q D.alpha D.alphaStored hgammaPair)).2
    apply hav
    unfold HierarchySegmentColors
    simp only
    have hend : H.stage q.succ = T := by
      convert H.terminalStage using 1
      congr 1
    rw [hend, hfirstAlpha]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, t, ht, ?_, he⟩
    have hp := D.penultimateVertexPosition
    have hl := D.lastEdgePosition
    have hvne : t.val ≠ D.lastEdgeIndex.val := fun he => hlast (Fin.ext he)
    have hb := t.isLt
    omega

private theorem helper_hcase_297.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoCaseOneTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount; D.gammaOne ∈
        HierarchyStageMissingColors H q → (0 : ℕ) < H.dividerCount ∧ D.gammaOne ∈
        TreeMissingColors phi (H.stage (⟨H.dividerCount,
    by
                  have := TreeSequence.positive T
                  omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) ∨ H.dividerCount = (0 : ℕ) ∧ D.gammaOne ∈
        TreeMissingColors phi (ett.series.data.tree (Fin.last ett.rounds).castSucc) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q hgammaStage
  by_cases hz : H.dividerCount = 0
  · right
    refine ⟨hz, ?_⟩
    have hi : q = 0 := by apply Fin.ext; simp [q, hz]
    simp only [hi, HierarchyStageMissingColors, Fin.cases] at hgammaStage
    convert hgammaStage using 1; congr 2
  · left
    refine ⟨Nat.pos_of_ne_zero hz, ?_⟩
    have hi : q = (⟨H.dividerCount - 1, by omega⟩ : Fin H.dividerCount).succ := by
      apply Fin.ext
      simp [q]
      omega
    have hg := hgammaStage
    rw [hi] at hg
    simp only [HierarchyStageMissingColors, Fin.castSucc_succ, Fin.succ_mk, Fin.cases_succ',
  Fin.castSucc_mk] at hg
    convert hg using 1; congr 2; apply Fin.ext; simp; omega

private theorem helper_hyt_415.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseOneTwoData G k e0 input T phi ett base C ctx),
    HierarchyFirstMissingPosition phi T D.theta = D.penultimateVertexIndex →
    T.vertex D.penultimateVertexIndex ≠ T.vertex D.terminalVertexIndex := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D hfirstTheta he
  have hi := congrArg Fin.val (T.vertex_injective he)
  have hp := D.penultimateVertexPosition
  have ht := D.terminalVertexPosition
  omega

private theorem helper_predecessorIncident_507.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Finite E] (G : LooplessMultigraph V E) (e0 : E) (T
        X : TreeSequence G e0), TreeSequenceInitialSegment X T →
    ∀ (t : Fin T.length), (↑t : ℕ) = X.length → TreeIncidentEdge X (T.edge t) := by
  classical
  intro V E _ _ G e0 T X hXT t ht
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite E
  obtain ⟨i, hi⟩ := T.attaches t
  let j : Fin (X.length + 1) := ⟨i.val, by have hib := i.isLt; omega⟩
  refine ⟨X.vertex j, ?_, ?_⟩
  · simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨j, rfl⟩
  · have hvertices : X.vertex j =
        T.vertex (Fin.castLT i (Nat.lt_trans i.isLt (Nat.succ_lt_succ t.isLt))) := by
      rw [← hXT.2.1 j]
      rfl
    rw [hvertices]
    change _ ∈ G.ends (T.edge t)
    rw [hi]
    exact Sym2.mem_mk_right _ _

private theorem helper_terminalIncident_524.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseOneTwoData G k e0 input T phi ett base C ctx),
    Incident G (T.vertex D.terminalVertexIndex) (T.edge D.lastEdgeIndex) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D
  obtain ⟨i, hi⟩ := T.attaches D.lastEdgeIndex
  have hj : D.lastEdgeIndex.succ = D.terminalVertexIndex := by
    apply Fin.ext
    have hl := D.lastEdgePosition
    have ht := D.terminalVertexPosition
    simp only [Fin.val_succ]
    omega
  change _ ∈ G.ends (T.edge D.lastEdgeIndex)
  rw [hi, hj]
  exact Sym2.mem_mk_left _ _

private theorem helper_missingNotColored_535.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (rho : PartialEdgeColoring E k) (c : Fin k) (v : V), c ∈ MissingColors G rho v →
    ∀ (e : E), Incident G v e → rho e ≠ some c := by
  classical
  intro V E _ _ G k rho c v hm e hi he
  let _ := Fintype.ofFinite V
  have hnot : c ∉ PresentColors G rho v := (Finset.mem_sdiff.mp hm).2
  apply hnot
  simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨e, hi, he⟩

private theorem helper_seedStable_543.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (T : TreeSequence G e0)
        {input' : PartialEdgeColoring E k} (rho sigma : PartialEdgeColoring E k) (ett' :
        ExtendedTashkinovTree G k e0 input' T rho) (base' : HierarchyBase ett' rho) (K :
        TashkinovHierarchy ett' base'), HierarchyWeaklyStable K (Fin.last K.dividerCount) sigma →
        K.dividerCount = (0 : ℕ) → StableColoring (ett'.series.data.tree (Fin.last
        ett'.rounds).castSucc) (TashkinovStoredColors ett'.series.data (Fin.last ett'.rounds)) rho
        sigma := by
  classical
  intro V E _ _ _ _ G k e0 T input' rho sigma ett' base' K hw hq
  have hi : (Fin.last K.dividerCount : Fin (K.dividerCount + 1)) = 0 := by
    apply Fin.ext
    simp [hq]
  rw [hi] at hw
  change (if ett'.series.data.kind (Fin.last ett'.rounds) =
      some TashkinovExtensionKind.PE then _ else _) at hw
  split_ifs at hw with hpe
  · exact hw.1
  · exact hw

private theorem helper_hstoredOne_643.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoCaseOneTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
        D.gammaOne ∈ TreeMissingColors phi A → D.gammaOne ≠ D.alpha → D.gammaOne ∈
        TreeMissingColors phi B ∧ D.alpha ∈ TreeMissingColors phi B →
    let z : V ⊕ E := Sum.inl (T.vertex D.terminalVertexIndex);
    let muOne : PartialEdgeColoring E k := TwoColorComponentSwap G phi D.gammaOne D.alpha z; (
    ∀ w ∈ TreeSequenceVertexSet B, MissingColors G (TwoColorComponentSwap G phi D.gammaOne D.alpha
        z) w = MissingColors G phi w) → (
    ∀ (rho sigma : PartialEdgeColoring E k) (c : Fin k), (
    ∀ v ∈ TreeSequenceVertexSet B, MissingColors G sigma v = MissingColors G rho v) → c ∈
        TreeMissingColors rho B → HierarchyFirstMissingPosition sigma T c =
        HierarchyFirstMissingPosition rho T c) → (
    ∀ (rho : PartialEdgeColoring E k) (a b c : Fin k), a ≠ b → IsProperEdgeColoring G rho → c ≠ a
        → c ≠ b → HierarchyFirstMissingPosition (TwoColorComponentSwap G rho a b z) T c =
        HierarchyFirstMissingPosition rho T c) →
    ∀ c ∈ HierarchyStoredColorsAt H q, HierarchyFirstMissingPosition muOne T c =
        HierarchyFirstMissingPosition phi T c := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B hgammaA hgammaAlpha hmissing z
      muOne hmissingOne firstPreserved firstUnaffected c hc
  have hcg : c ≠ D.gammaOne := by
    intro he
    exact (Finset.mem_sdiff.mp hc).2 (he ▸ hgammaA)
  by_cases hca : c = D.alpha
  · subst c
    exact firstPreserved phi muOne D.alpha hmissingOne hmissing.2
  · exact firstUnaffected phi D.gammaOne D.alpha c hgammaAlpha ctx.proper hcg hca

private theorem helper_hpairDataOne_800.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoCaseOneTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let _ : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    ∀ (POne : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let COne' : HierarchyCounterexample POne.replacementBase := POne.counterexample;
    let HOne : TashkinovHierarchy POne.corresponding.replacementETT POne.replacementBase :=
        COne'.hierarchy;
    let qOne : Fin (HOne.dividerCount + (1 : ℕ)) := Fin.last HOne.dividerCount; D.alpha ∈
        HierarchyStoredColorsAt HOne qOne ∧ POne.counterexample.good.gamma qOne D.alpha = (insert
        D.gammaOne ({ D.gammaTwo } : Finset (Fin k)) : Finset (Fin k)) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q POne COne' HOne qOne
  rcases POne.sameGood.2 with ⟨hcount, hdata⟩
  have hi : Fin.cast (congrArg (fun n => n + 1) hcount) q = qOne := by
    apply Fin.ext
    simp [q, qOne, H, HOne, COne']
  have hd := hdata q
  dsimp only at hd
  rw [hi] at hd
  refine ⟨hd.1 ▸ D.alphaStored, ?_⟩
  exact (hd.2 D.alpha D.alphaStored).symm.trans D.gammaPair

private theorem helper_hcaseOne_816.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoCaseOneTwoData G k e0 input T phi ett base C ctx) (POne :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let rho : PartialEdgeColoring E k := POne.coloring;
    let ettOne : ExtendedTashkinovTree G k e0 POne.corresponding.replacementInput T POne.coloring
        := POne.corresponding.replacementETT;
    let COne' : HierarchyCounterexample POne.replacementBase := POne.counterexample;
    let HOne : TashkinovHierarchy POne.corresponding.replacementETT POne.replacementBase :=
        COne'.hierarchy;
    let qOne : Fin (HOne.dividerCount + (1 : ℕ)) := Fin.last HOne.dividerCount; D.gammaOne ∈
        HierarchyStageMissingColors HOne qOne → (0 : ℕ) < HOne.dividerCount ∧ D.gammaOne ∈
        TreeMissingColors rho (HOne.stage (⟨HOne.dividerCount,
    by
                  have := TreeSequence.positive T
                  omega
    ⟩ : Fin (HOne.dividerCount + (2 : ℕ)))) ∨ HOne.dividerCount = (0 : ℕ) ∧ D.gammaOne ∈
        TreeMissingColors rho (ettOne.series.data.tree (Fin.last ettOne.rounds).castSucc) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D POne rho ettOne COne' HOne qOne
      hgammaStageOne
  by_cases hz : HOne.dividerCount = 0
  · right
    refine ⟨hz, ?_⟩
    have hi : qOne = 0 := by apply Fin.ext; simp [qOne, hz]
    simpa [hi, HierarchyStageMissingColors] using hgammaStageOne
  · left
    refine ⟨Nat.pos_of_ne_zero hz, ?_⟩
    have hi : qOne = (⟨HOne.dividerCount - 1, by omega⟩ : Fin HOne.dividerCount).succ := by
      apply Fin.ext
      simp [qOne]
      omega
    have hg := hgammaStageOne
    rw [hi] at hg
    simp only [HierarchyStageMissingColors, Fin.castSucc_succ, Fin.succ_mk, Fin.cases_succ',
  Fin.castSucc_mk] at hg
    convert hg using 1; congr 2; apply Fin.ext; simp; omega

private theorem helper_weakEdges_959.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (T : TreeSequence G e0), (
    ∀ (X Y : TreeSequence G e0) (h : X = Y) (i : Fin X.length), X.edge i = Y.edge (Fin.cast
        (congrArg TreeSequence.length h) i)) →
    ∀ {input' : PartialEdgeColoring E k} (old new : PartialEdgeColoring E k) (ett' :
        ExtendedTashkinovTree G k e0 input' T old) (base' : HierarchyBase ett' old) (K :
        TashkinovHierarchy ett' base'), TreeSequenceInitialSegment (HierarchyStarredStage K
        (Fin.last K.dividerCount)) T → HierarchyWeaklyStable K (Fin.last K.dividerCount) new →
        IsProperEdgeColoring G old → IsOneEdgeUncolored old e0 → IsProperEdgeColoring G new →
        IsOneEdgeUncolored new e0 →
    ∀ (t : Fin T.length), (↑t : ℕ) < (HierarchyStarredStage K (Fin.last K.dividerCount)).length →
        new (T.edge t) = old (T.edge t) := by
  classical
  intro V E _ _ _ _ G k e0 T edgeCast input' old new ett' base' K hST hw hp ho hnp hno
  let S := HierarchyStarredStage K (Fin.last K.dividerCount)
  intro t ht
  let tS : Fin S.length := ⟨t.val, ht⟩
  have hcast : Fin.castLE hST.1 tS = t := Fin.ext rfl
  rw [← hcast, hST.2.2 tS]
  by_cases hzero : K.dividerCount = 0
  · have hi : (Fin.last K.dividerCount : Fin (K.dividerCount + 1)) = 0 := by
      apply Fin.ext
      simp [hzero]
    have hS : S = base'.core := by change HierarchyStarredStage K _ = _; rw [hi]; rfl
    rw [hi] at hw
    change (if ett'.series.data.kind (Fin.last ett'.rounds) =
      some TashkinovExtensionKind.PE then _ else _) at hw
    by_cases hpe : ett'.series.data.kind (Fin.last ett'.rounds) = some TashkinovExtensionKind.PE
    · rw [ite_eq_left hpe] at hw
      have hc := CombinedStableClosurePreserved G k e0 input' T old old new ett'
        (by have h := ett'.roundsPositive; omega) base' ett'.generatingColoring hpe hp ho hnp hno hw
      obtain ⟨_, _, ⟨hunion⟩⟩ := base'.parallel hpe
      let tc : Fin base'.core.length := Fin.cast (congrArg TreeSequence.length hS) tS
      have he : S.edge tS = base'.core.edge tc := edgeCast S base'.core hS tS
      rw [he]
      by_cases hbelow : tc.val < (ett'.series.data.tree (Fin.last ett'.rounds).castSucc).length
      · let tn : Fin (ett'.series.data.tree (Fin.last ett'.rounds).castSucc).length := ⟨tc.val,
          hbelow⟩
        have heq : Fin.castLE hunion.leftSegment.1 tn = tc := Fin.ext rfl
        rw [← heq, hunion.leftSegment.2.2 tn]
        exact hc.1 tn
      · obtain ⟨j, heq, _⟩ := hunion.newEntryFromRight tc (by omega)
        rw [heq]
        exact hc.2.1 j
    · rw [ite_eq_right hpe] at hw
      have hcore := base'.nonparallel hpe
      have hS' := hS.trans hcore
      let tn : Fin (ett'.series.data.tree (Fin.last ett'.rounds).castSucc).length :=
        Fin.cast (congrArg TreeSequence.length hS') tS
      have he : S.edge tS = (ett'.series.data.tree (Fin.last ett'.rounds).castSucc).edge tn := by
        exact edgeCast S _ hS' tS
      rw [he]
      let r : Fin ett'.rounds := ⟨ett'.rounds - 1, by have h := ett'.roundsPositive; omega⟩
      have hr : r.succ = Fin.last ett'.rounds := by
        have hn := ett'.roundsPositive
        apply Fin.ext
        simp [r]
        omega
      have hfix := (HkuTreeColorsControlled G k ett'.rounds e0 input' ett'.series r).2.2 new
        hnp hno (by rw [hr, ← ett'.generatingColoring]; exact hw)
      rw [hr, ← ett'.generatingColoring] at hfix
      exact hfix tn
  · have hi : (Fin.last K.dividerCount : Fin (K.dividerCount + 1)) =
        (⟨K.dividerCount - 1, by omega⟩ : Fin K.dividerCount).succ := by
      apply Fin.ext
      simp
      omega
    have hS : S = K.stage (⟨K.dividerCount - 1, by omega⟩ : Fin K.dividerCount).succ.castSucc := by
      change HierarchyStarredStage K _ = _
      rw [hi]
      simp [HierarchyStarredStage]
    rw [hi] at hw
    simp only [HierarchyWeaklyStable, Fin.castSucc_succ, Fin.succ_mk, Fin.cases_succ',
        Fin.castSucc_mk] at hw
    have hinv : TreeColoringInvariant S old new := hS.symm ▸ hw.2
    by_cases hpos : 1 ≤ tS.val
    · exact hinv.1 tS hpos
    · have hi : tS = ⟨0, S.positive⟩ := by
        apply Fin.ext
        change tS.val = 0
        omega
      rw [hi, S.first_edge, hno.1, ho.1]

private theorem helper_hfixedCoreTwo_1036.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoCaseOneTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q; TreeSequenceInitialSegment A T →
    let z : V ⊕ E := Sum.inl (T.vertex D.terminalVertexIndex);
    ∀ (POne : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), (
    ∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage P.counterexample.hierarchy (Fin.last
        P.counterexample.hierarchy.dividerCount) = A) →
    let rho : PartialEdgeColoring E k := POne.coloring;
    let ettOne : ExtendedTashkinovTree G k e0 POne.corresponding.replacementInput T POne.coloring
        := POne.corresponding.replacementETT;
    let baseOne' : HierarchyBase POne.corresponding.replacementETT POne.coloring :=
        POne.replacementBase;
    let COne' : HierarchyCounterexample POne.replacementBase := POne.counterexample;
    let _ : HierarchyMinimumCounterexampleContext G k e0 POne.corresponding.replacementInput T
        POne.coloring POne.corresponding.replacementETT POne.replacementBase POne.counterexample
        := POne.minimumContext;
    let _ : TashkinovHierarchy POne.corresponding.replacementETT POne.replacementBase :=
        COne'.hierarchy;
    let muTwo : PartialEdgeColoring E k := TwoColorComponentSwap G rho D.gammaOne D.theta z; (
    let H : TashkinovHierarchy ettOne baseOne' := COne'.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    have n : Fin (ettOne.rounds + (1 : ℕ)) := Fin.last ettOne.rounds;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    have Tnq : TreeSequence G e0 := H.stage (⟨H.dividerCount,
    by
              have := TreeSequence.positive T
              omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)));
    have Tn : TreeSequence G e0 := ettOne.series.data.tree n.castSucc;
    have Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q; HierarchyWeaklyStable H q muTwo ∧
        ModColoring ettOne muTwo ∧ (A = Tn ∨
    ∃ (inputA : PartialEdgeColoring E k) (ettA : ExtendedTashkinovTree G k e0 inputA A muTwo),
        MaximumProperty ettA) ∧ ((0 : ℕ) < H.dividerCount →
    ∃ (inputA : PartialEdgeColoring E k) (ettA : ExtendedTashkinovTree G k e0 inputA A muTwo)
        (baseA : HierarchyBase ettA muTwo) (K : TashkinovHierarchy ettA baseA) (goodA :
        GoodHierarchy K), MaximumProperty ettA ∧ ettA.series.data.kind (Fin.last ettA.rounds) =
        ettOne.series.data.kind (Fin.last ettOne.rounds) ∧
    ∃ (hcount : K.dividerCount + (1 : ℕ) = H.dividerCount), baseA.core = baseOne'.core ∧
        baseA.closure = baseOne'.closure ∧ (
    ∀ (j : Fin (K.dividerCount + (2 : ℕ))), K.stage j = H.stage (⟨(↑j : ℕ),
    by
                                      have := TreeSequence.positive T
                                      omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) ∧ (
    ∀ (j : Fin (K.dividerCount + (1 : ℕ))),
    have jH : Fin (H.dividerCount + (1 : ℕ)) := (⟨(↑j : ℕ),
    by
                                      have := TreeSequence.positive T
                                      omega
    ⟩ : Fin (H.dividerCount + (1 : ℕ))); HierarchyStoredColorsAt K j = HierarchyStoredColorsAt H
        jH ∧
    ∀ eta ∈ HierarchyStoredColorsAt K j, goodA.gamma j eta = COne'.good.gamma jH eta) ∧
        TreeColorSetMinusClosed G muTwo Tnq (Dnq.biUnion (COne'.good.gamma
        (⟨COne'.hierarchy.dividerCount - (1 : ℕ),
    by
                                        have := TreeSequence.positive T
                                        omega
    ⟩ : Fin (COne'.hierarchy.dividerCount + (1 : ℕ))))))) → (
    ∀ {input' : PartialEdgeColoring E k} (old new : PartialEdgeColoring E k) (ett' :
        ExtendedTashkinovTree G k e0 input' T old) (base' : HierarchyBase ett' old) (K :
        TashkinovHierarchy ett' base'), TreeSequenceInitialSegment (HierarchyStarredStage K
        (Fin.last K.dividerCount)) T → HierarchyWeaklyStable K (Fin.last K.dividerCount) new →
        IsProperEdgeColoring G old → IsOneEdgeUncolored old e0 → IsProperEdgeColoring G new →
        IsOneEdgeUncolored new e0 →
    ∀ (t : Fin T.length), (↑t : ℕ) < (HierarchyStarredStage K (Fin.last K.dividerCount)).length →
        new (T.edge t) = old (T.edge t)) →
    ∀ (t : Fin T.length), (↑t : ℕ) < A.length → muTwo (T.edge t) = rho (T.edge t) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A hAT z POne sameStar rho ettOne
      baseOne' COne' ctxOne HOne muTwo hstableTwo weakEdges
  have h := weakEdges rho muTwo ettOne baseOne' HOne
    (by rw [sameStar POne]; exact hAT) hstableTwo.1 ctxOne.proper ctxOne.oneEdgeUncolored
    hstableTwo.2.1.1 hstableTwo.2.1.2.1
  change ∀ t : Fin T.length, t.val < (HierarchyStarredStage POne.counterexample.hierarchy
    (Fin.last POne.counterexample.hierarchy.dividerCount)).length → _ at h
  rw [sameStar POne] at h
  exact h

private theorem helper_hstoredTwo_1050.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoCaseOneTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
        D.gammaOne ≠ D.theta →
    let z : V ⊕ E := Sum.inl (T.vertex D.terminalVertexIndex); (
    ∀ (rho sigma : PartialEdgeColoring E k) (c : Fin k), (
    ∀ v ∈ TreeSequenceVertexSet B, MissingColors G sigma v = MissingColors G rho v) → c ∈
        TreeMissingColors rho B → HierarchyFirstMissingPosition sigma T c =
        HierarchyFirstMissingPosition rho T c) → (
    ∀ (rho : PartialEdgeColoring E k) (a b c : Fin k), a ≠ b → IsProperEdgeColoring G rho → c ≠ a
        → c ≠ b → HierarchyFirstMissingPosition (TwoColorComponentSwap G rho a b z) T c =
        HierarchyFirstMissingPosition rho T c) →
    ∀ (POne : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), (
    ∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage P.counterexample.hierarchy (Fin.last
        P.counterexample.hierarchy.dividerCount) = A) →
    let rho : PartialEdgeColoring E k := POne.coloring;
    let COne' : HierarchyCounterexample POne.replacementBase := POne.counterexample;
    let _ : HierarchyMinimumCounterexampleContext G k e0 POne.corresponding.replacementInput T
        POne.coloring POne.corresponding.replacementETT POne.replacementBase POne.counterexample
        := POne.minimumContext;
    let HOne : TashkinovHierarchy POne.corresponding.replacementETT POne.replacementBase :=
        COne'.hierarchy;
    let qOne : Fin (HOne.dividerCount + (1 : ℕ)) := Fin.last HOne.dividerCount; D.gammaOne ∈
        TreeMissingColors rho A → D.gammaOne ∈ TreeMissingColors rho B ∧ D.theta ∈
        TreeMissingColors rho B →
    let muTwo : PartialEdgeColoring E k := TwoColorComponentSwap G rho D.gammaOne D.theta z; (
    ∀ w ∈ TreeSequenceVertexSet B, MissingColors G (TwoColorComponentSwap G rho D.gammaOne D.theta
        z) w = MissingColors G rho w) →
    ∀ c ∈ HierarchyStoredColorsAt HOne qOne, HierarchyFirstMissingPosition muTwo T c =
        HierarchyFirstMissingPosition rho T c := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B hgammaTheta z firstPreserved
      firstUnaffected POne sameStar rho COne' ctxOne HOne qOne hgammaAOne hmissingPairOne muTwo
      hmissingTwo c hc
  have hcg : c ≠ D.gammaOne := by
    intro he
    apply (Finset.mem_sdiff.mp hc).2
    rw [sameStar POne]
    exact he ▸ hgammaAOne
  by_cases hct : c = D.theta
  · subst c
    exact firstPreserved rho muTwo D.theta hmissingTwo hmissingPairOne.2
  · exact firstUnaffected rho D.gammaOne D.theta c hgammaTheta ctxOne.proper hcg hct

private theorem helper_commonPrefix_1062.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
        {X Y F : TreeSequence G e0}, TreeSequenceInitialSegment X F → TreeSequenceInitialSegment Y
        F → X.length ≤ Y.length → TreeSequenceInitialSegment X Y := by
  classical
  intro V E G e0 X Y F hXF hYF hXY
  refine ⟨hXY, ?_, ?_⟩
  · intro i
    rw [← hYF.2.1 (Fin.castLE (Nat.succ_le_succ hXY) i)]
    exact hXF.2.1 i
  · intro i
    rw [← hYF.2.2 (Fin.castLE hXY i)]
    exact hXF.2.2 i

private theorem helper_hcoreLength_1080.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (_ :
        HierarchySituationTwoCaseOneTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    ∀ (POne : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), (
    ∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage P.counterexample.hierarchy (Fin.last
        P.counterexample.hierarchy.dividerCount) = A) →
    let baseOne' : HierarchyBase POne.corresponding.replacementETT POne.coloring :=
        POne.replacementBase;
    let COne' : HierarchyCounterexample POne.replacementBase := POne.counterexample;
    let HOne : TashkinovHierarchy POne.corresponding.replacementETT POne.replacementBase :=
        COne'.hierarchy;
    let _ : Fin (HOne.dividerCount + (1 : ℕ)) := Fin.last HOne.dividerCount; baseOne'.core.length
        ≤ A.length := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A POne sameStar baseOne' COne' HOne qOne
  by_cases hz : HOne.dividerCount = 0
  · have hi : qOne = 0 := by apply Fin.ext; simp [qOne, hz]
    have he := sameStar POne
    change HierarchyStarredStage HOne qOne = A at he
    rw [hi] at he
    change baseOne'.core = A at he
    exact le_of_eq (congrArg TreeSequence.length he)
  · have hmono : Monotone (fun i : Fin (HOne.dividerCount + 2) => (HOne.stage i).length) :=
      Fin.monotone_iff_le_succ.mpr fun i => (HOne.nested i).1
    have hi : qOne = (⟨HOne.dividerCount - 1, by omega⟩ : Fin HOne.dividerCount).succ := by
      apply Fin.ext
      simp [qOne]
      omega
    have he := sameStar POne
    change HierarchyStarredStage HOne qOne = A at he
    rw [hi] at he
    simp only [HierarchyStarredStage, Fin.cases_succ] at he
    have hle := hmono (show (⟨1, by omega⟩ : Fin (HOne.dividerCount + 2)) ≤
        (⟨HOne.dividerCount - 1, by omega⟩ : Fin HOne.dividerCount).succ.castSucc by
      change 1 ≤ HOne.dividerCount - 1 + 1
      omega)
    dsimp only at hle
    rw [he] at hle
    exact HOne.coreInsideFirst.1.trans hle

private theorem helper_hrouteTwo_1126.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoCaseOneTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
        (2 : ℕ) ≤ T.length - A.length → B.length + (1 : ℕ) = T.length → TreeSequenceInitialSegment
        B T →
    let z : V ⊕ E := Sum.inl (T.vertex D.terminalVertexIndex);
    ∀ (POne : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let rho : PartialEdgeColoring E k := POne.coloring;
    let ettOne : ExtendedTashkinovTree G k e0 POne.corresponding.replacementInput T POne.coloring
        := POne.corresponding.replacementETT;
    let baseOne' : HierarchyBase POne.corresponding.replacementETT POne.coloring :=
        POne.replacementBase;
    let muTwo : PartialEdgeColoring E k := TwoColorComponentSwap G rho D.gammaOne D.theta z; (
    ∀ {X Y F : TreeSequence G e0}, TreeSequenceInitialSegment X F → TreeSequenceInitialSegment Y F
        → X.length ≤ Y.length → TreeSequenceInitialSegment X Y) → (
    ∀ {X Y F : TreeSequence G e0}, TreeSequenceInitialSegment X Y → TreeSequenceInitialSegment Y F
        → TreeSequenceInitialSegment X F) → baseOne'.core.length ≤ A.length → (
    ∀ (S : TreeSequence G e0), TashkinovAugmentationSequence rho S B →
        TashkinovAugmentationSequence muTwo S B) → ettOne.series.data.kind (Fin.last
        ettOne.rounds) = some TashkinovExtensionKind.PE ∧ TashkinovAugmentationSequence muTwo
        (ettOne.series.data.tree (Fin.last ettOne.rounds).castSucc) B ∨ (ettOne.series.data.kind
        (Fin.last ettOne.rounds) = some TashkinovExtensionKind.SE ∨ ettOne.series.data.kind
        (Fin.last ettOne.rounds) = some TashkinovExtensionKind.RE) ∧
    ∃ (f : E) (seed : TreeSequence G e0), ettOne.series.data.connectingEdges (Fin.last
        ettOne.rounds) = ({ f } : Finset E) ∧ TreeSequenceAdjoinEdge (ettOne.series.data.tree
        (Fin.last ettOne.rounds).castSucc) f seed ∧ TashkinovAugmentationSequence muTwo seed B := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B htail hBlen hBT z POne rho ettOne
      baseOne' muTwo commonPrefix segmentTrans hcoreLength transportRoute
  let n : Fin (ettOne.rounds + 1) := Fin.last ettOne.rounds
  let Tn := ettOne.series.data.tree n.castSucc
  let F := ettOne.series.data.tree (Fin.last (ettOne.rounds + 1))
  have hBF : TreeSequenceInitialSegment B F := segmentTrans hBT ettOne.belowFinal
  have hn : n.succ = Fin.last (ettOne.rounds + 1) := Fin.ext rfl
  have hTnT : TreeSequenceInitialSegment Tn T := ettOne.abovePenultimate
  have hTnB : TreeSequenceInitialSegment Tn B := commonPrefix hTnT hBT (by
    have hs := ettOne.strictAbovePenultimate
    change Tn.length < T.length at hs
    omega)
  have nonparallel (hkind : ettOne.series.data.kind n = some TashkinovExtensionKind.SE ∨
      ettOne.series.data.kind n = some TashkinovExtensionKind.RE)
      (f : E) (seed : TreeSequence G e0)
      (hedges : ettOne.series.data.connectingEdges n = {f})
      (hadjoin : TreeSequenceAdjoinEdge Tn f seed)
      (hclosure : TashkinovClosure rho seed F) :
      ∃ f seed, ettOne.series.data.connectingEdges (Fin.last ettOne.rounds) = {f} ∧
        TreeSequenceAdjoinEdge (ettOne.series.data.tree (Fin.last ettOne.rounds).castSucc) f seed ∧
        TashkinovAugmentationSequence muTwo seed B := by
    have hnotPE : ettOne.series.data.kind n ≠ some TashkinovExtensionKind.PE := by
      intro he
      rcases hkind with hs | hr
      · rw [hs] at he
        simp at he
      · rw [hr] at he
        simp at he
    have hc : baseOne'.core = Tn := baseOne'.nonparallel hnotPE
    have hseedF := TashkinovAugmentationSequenceInitialSegment rho seed F hclosure.1
    have hsBound : seed.length ≤ B.length := by
      have hlen : Tn.length ≤ A.length := hc ▸ hcoreLength
      have hab : A.length + 1 ≤ B.length := by
        clear * - htail hBlen
        omega
      exact hadjoin.1.le.trans ((Nat.add_le_add_right hlen 1).trans hab)
    have hseedB : TreeSequenceInitialSegment seed B := commonPrefix hseedF hBF hsBound
    exact ⟨f, seed, hedges, hadjoin,
      transportRoute seed (TashkinovAugmentationSequenceRestrict rho seed B F
        hclosure.1 hseedB hBF)⟩
  have cert := ettOne.series.certified n
  generalize hindex : n = j at cert
  cases cert with
  | initial triple seedLength initialColoring initialStored initialEdges initialKind
      initialVertex initialOutside initialDelta initialGamma initialClosure =>
      have hnzero : n = 0 := by simpa using hindex
      have hv := congrArg Fin.val hnzero
      have hp := ettOne.roundsPositive
      simp [n] at hv
      omega
  | SE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
      have hk : ettOne.series.data.kind n = some TashkinovExtensionKind.SE := by
        rw [hindex]
        exact currentKind
      refine Or.inr ⟨Or.inl hk, ?_⟩
      apply nonparallel (Or.inl hk) choice.edge adjoined
      · rw [hindex]; exact currentEdges
      · simpa [Tn, hindex] using adjoinedExactly
      · rw [← hindex, hn, ← ettOne.generatingColoring] at closedExtension
        exact closedExtension
  | PE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper secondStableOneUncolored
      secondStableRelation exitWitness currentColoring currentProper
      currentOneUncolored currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma closedExtension orderedExtension
      strictExtension =>
      have hk : ettOne.series.data.kind n = some TashkinovExtensionKind.PE := by
        rw [hindex]
        exact currentKind
      refine Or.inl ⟨hk, transportRoute Tn ?_⟩
      rw [← hindex, hn, ← ettOne.generatingColoring] at closedExtension
      exact TashkinovAugmentationSequenceRestrict rho Tn B F closedExtension.1 hTnB hBF
  | RE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored currentEdges
      currentKind currentVertex currentOutside currentDelta currentGamma adjoined
      adjoinedExactly closedExtension orderedExtension strictExtension =>
      have hk : ettOne.series.data.kind n = some TashkinovExtensionKind.RE := by
        rw [hindex]
        exact currentKind
      refine Or.inr ⟨Or.inr hk, ?_⟩
      apply nonparallel (Or.inr hk) available.edge adjoined
      · rw [hindex]; exact currentEdges
      · simpa [Tn, hindex] using adjoinedExactly
      · rw [← hindex, hn, ← ettOne.generatingColoring] at closedExtension
        exact closedExtension

private theorem helper_hthetaLastOne_1217.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoCaseOneTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q; (2 : ℕ) ≤ T.length - A.length →
    let z : V ⊕ E := Sum.inl (T.vertex D.terminalVertexIndex);
    let muOne : PartialEdgeColoring E k := TwoColorComponentSwap G phi D.gammaOne D.alpha z; (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → muOne (T.edge t) = phi (T.edge t)) →
    ∀ (POne : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), POne.coloring =
        muOne →
    let rho : PartialEdgeColoring E k := POne.coloring; rho (T.edge D.lastEdgeIndex) = some
        D.theta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A htail z muOne hfixedOne POne hPOne rho
  rw [show rho = muOne from hPOne, hfixedOne D.lastEdgeIndex (by
    have hl := D.lastEdgePosition
    clear * - hl htail
    omega)]
  exact D.thetaOnLastEdge

private theorem helper_hgammaCutoff_1234.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoCaseOneTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
        B.length + (1 : ℕ) = T.length → TreeSequenceInitialSegment A B → (
    ∀ {c : Fin k}, c ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex) → c ∉
        TreeMissingColors phi A) →
    ∀ (POne : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), (
    ∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage P.counterexample.hierarchy (Fin.last
        P.counterexample.hierarchy.dividerCount) = A) →
    let rho : PartialEdgeColoring E k := POne.coloring;
    let COne' : HierarchyCounterexample POne.replacementBase := POne.counterexample;
    let HOne : TashkinovHierarchy POne.corresponding.replacementETT POne.replacementBase :=
        COne'.hierarchy;
    let qOne : Fin (HOne.dividerCount + (1 : ℕ)) := Fin.last HOne.dividerCount; (
    ∀ v ∈ TreeSequenceVertexSet B, MissingColors G rho v = MissingColors G phi v) →
        HierarchyFirstMissingPosition rho T D.alpha = D.penultimateVertexIndex → D.alpha ∈
        HierarchyStoredColorsAt HOne qOne ∧ POne.counterexample.good.gamma qOne D.alpha = (insert
        D.gammaOne ({ D.gammaTwo } : Finset (Fin k)) : Finset (Fin k)) →
    ∀ c ∈ HierarchyStoredColorsAt HOne qOne, D.gammaOne ∈ POne.counterexample.good.gamma qOne c ∨
        D.theta ∈ POne.counterexample.good.gamma qOne c → (↑(HierarchyFirstMissingPosition rho T
        c) : ℕ) ≤ B.length := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B hBlen hAB hnotA POne sameStar rho
      COne' HOne qOne hmissingOne' hfirstAlphaOne hpairDataOne c hc hpair
  rcases hpair with hgamma | htheta
  · have hca : c = D.alpha := by
      by_contra hne
      have hdis := POne.counterexample.good.disjointPairs qOne c D.alpha hc hpairDataOne.1 hne
      exact Finset.disjoint_left.mp hdis hgamma (by rw [hpairDataOne.2]; simp)
    subst c
    rw [hfirstAlphaOne]
    have hp := D.penultimateVertexPosition
    clear * - hBlen hp
    omega
  · have htA := (GoodHierarchyReservedDisjoint POne.counterexample.good qOne).1 c hc htheta
    rw [sameStar POne] at htA
    have htB : D.theta ∈ TreeMissingColors phi A := by
      rcases Finset.mem_biUnion.mp htA with ⟨v, hv, hm⟩
      refine Finset.mem_biUnion.mpr ⟨v, hv, ?_⟩
      rw [hmissingOne' _ (TreeSequenceInitialSegmentVertexSetSubset hAB hv)] at hm
      exact hm
    exact (hnotA D.thetaMissingPenultimate htB).elim

private theorem helper_hlastComponent_1277.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoCaseOneTwoData G k e0 input T phi ett base C ctx),
    let z : V ⊕ E := Sum.inl (T.vertex D.terminalVertexIndex); Incident G (T.vertex
        D.terminalVertexIndex) (T.edge D.lastEdgeIndex) →
    ∀ (POne : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let rho : PartialEdgeColoring E k := POne.coloring; rho (T.edge D.lastEdgeIndex) = some
        D.theta → Sum.inr (T.edge D.lastEdgeIndex) ∈ TwoColorComponent G rho D.gammaOne D.theta z
  := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D z terminalIncident POne rho hthetaLastOne
  have hadj : (TwoColorIncidenceGraph G rho D.gammaOne D.theta).Adj
      (Sum.inr (T.edge D.lastEdgeIndex)) z := by
    exact ⟨terminalIncident, Or.inr hthetaLastOne⟩
  change (TwoColorIncidenceGraph G rho D.gammaOne D.theta).connectedComponentMk
    (Sum.inr (T.edge D.lastEdgeIndex)) = _
  exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj

private noncomputable abbrev helperTailTwo2292.{u_1, u_2} :
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
                                      (D :
                                          HierarchySituationTwoCaseOneTwoData G k e0 input T phi ett
                                            base C ctx) →
                                        let H : TashkinovHierarchy ett base := C.hierarchy;
                                        let q : Fin (H.dividerCount + (1 : ℕ)) :=
                                          Fin.last H.dividerCount;
                                        let A : TreeSequence G e0 := HierarchyStarredStage H q;
                                        (2 : ℕ) ≤ T.length - A.length →
                                          let z : V ⊕ E := Sum.inl (T.vertex D.terminalVertexIndex);
                                          (POne :
                                              HierarchyReplacementPresentation G k e0 input T phi
                                                ett base C ctx) →
                                            (∀
                                                (P :
                                                  HierarchyReplacementPresentation G k e0 input T
                                                    phi ett base C ctx),
                                                HierarchyStarredStage P.counterexample.hierarchy
                                                    (Fin.last
                                                      P.counterexample.hierarchy.dividerCount) =
                                                  A) →
                                              let rho : PartialEdgeColoring E k := POne.coloring;
                                              let muTwo : PartialEdgeColoring E k :=
                                                TwoColorComponentSwap G rho D.gammaOne D.theta z;
                                              muTwo (T.edge D.lastEdgeIndex) = some D.gammaOne →
                                                D.gammaOne ∉
                                                    MissingColors G muTwo
                                                      (T.vertex D.penultimateVertexIndex) →
                                                  (PTwo :
                                                      HierarchyReplacementPresentation G k e0 input
                                                        T phi ett base C ctx) →
                                                    PTwo.coloring = muTwo →
                                                      HierarchySituationTwoTailData G k e0
                                                        PTwo.corresponding.replacementInput T
                                                        PTwo.coloring
                                                        PTwo.corresponding.replacementETT
                                                        PTwo.replacementBase PTwo.counterexample
                                                        PTwo.minimumContext := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A htail z POne sameStar rho muTwo
      hlastTwo hgammaPenTwo PTwo hPTwo
  exact {
    tailAtLeastTwo := by
      change 2 ≤ T.length - (HierarchyStarredStage PTwo.counterexample.hierarchy
        (Fin.last PTwo.counterexample.hierarchy.dividerCount)).length
      rw [sameStar PTwo]
      exact htail
    pathNumberFull := by
      have hp := D.pathNumberFull
      unfold HierarchyPathNumber HierarchyFullTailLength at hp ⊢
      dsimp only at hp ⊢
      rw [sameStar PTwo]
      exact hp
    lastEdgeIndex := D.lastEdgeIndex
    penultimateVertexIndex := D.penultimateVertexIndex
    terminalVertexIndex := D.terminalVertexIndex
    lastEdgePosition := D.lastEdgePosition
    penultimateVertexPosition := D.penultimateVertexPosition
    terminalVertexPosition := D.terminalVertexPosition
    lastEdgeNotIncidentPenultimate := D.lastEdgeNotIncidentPenultimate
    theta := D.gammaOne
    thetaOnLastEdge := hPTwo.symm ▸ hlastTwo
    thetaPresentPenultimate := hPTwo.symm ▸ hgammaPenTwo }

private theorem helper_branch_2476.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoCaseOneTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    ∀ (htail : (2 : ℕ) ≤ T.length - A.length),
    let z : V ⊕ E := Sum.inl (T.vertex D.terminalVertexIndex);
    ∀ (POne : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (sameStar :
    ∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage P.counterexample.hierarchy (Fin.last
        P.counterexample.hierarchy.dividerCount) = A),
    let rho : PartialEdgeColoring E k := POne.coloring;
    let muTwo : PartialEdgeColoring E k := TwoColorComponentSwap G rho D.gammaOne D.theta z;
    ∀ (hlastTwo : muTwo (T.edge D.lastEdgeIndex) = some D.gammaOne), D.theta ∈ MissingColors G
        muTwo (T.vertex D.terminalVertexIndex) → D.theta ∈ MissingColors G muTwo (T.vertex
        D.penultimateVertexIndex) →
    ∀ (hgammaPenTwo : D.gammaOne ∉ MissingColors G muTwo (T.vertex D.penultimateVertexIndex))
        (PTwo : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (hPTwo :
        PTwo.coloring = muTwo),
    let _ : HierarchySituationTwoTailData G k e0 PTwo.corresponding.replacementInput T
        PTwo.coloring PTwo.corresponding.replacementETT PTwo.replacementBase PTwo.counterexample
        PTwo.minimumContext := helperTailTwo2292 G k e0 input T phi ett base C ctx D htail POne
        sameStar hlastTwo hgammaPenTwo PTwo hPTwo; D.theta ∈ HierarchyStoredColorsAt
        PTwo.counterexample.hierarchy (Fin.last PTwo.counterexample.hierarchy.dividerCount) →
        False := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A htail z POne sameStar rho muTwo
      hlastTwo hthetaTermTwo hthetaPenTwo hgammaPenTwo PTwo hPTwo tailTwo hstored
  obtain ⟨g1, g2, hne, hpair⟩ := Finset.card_eq_two.mp
    (PTwo.counterexample.good.twoColors _ D.theta hstored)
  let finalData : HierarchySituationTwoCaseOneData G k e0 PTwo.corresponding.replacementInput T
      PTwo.coloring PTwo.corresponding.replacementETT PTwo.replacementBase
      PTwo.counterexample PTwo.minimumContext :=
    { toHierarchySituationTwoTailData := tailTwo
      alpha := D.theta
      gammaOne := g1
      gammaTwo := g2
      alphaMissingPenultimate := by
        change D.theta ∈ MissingColors G PTwo.coloring (T.vertex D.penultimateVertexIndex)
        rw [hPTwo]
        exact hthetaPenTwo
      alphaMissingTerminal := by
        change D.theta ∈ MissingColors G PTwo.coloring (T.vertex D.terminalVertexIndex)
        rw [hPTwo]
        exact hthetaTermTwo
      alphaStored := hstored
      gammaPair := hpair
      gammaDistinct := hne }
  exact HierarchySituationTwoSubcaseOneOne G k e0 PTwo.corresponding.replacementInput T
    PTwo.coloring PTwo.corresponding.replacementETT PTwo.replacementBase
    PTwo.counterexample PTwo.minimumContext finalData

private theorem helper_branch_2499.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoCaseOneTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    ∀ (htail : (2 : ℕ) ≤ T.length - A.length),
    let z : V ⊕ E := Sum.inl (T.vertex D.terminalVertexIndex);
    ∀ (POne : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (sameStar :
    ∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage P.counterexample.hierarchy (Fin.last
        P.counterexample.hierarchy.dividerCount) = A),
    let rho : PartialEdgeColoring E k := POne.coloring;
    let muTwo : PartialEdgeColoring E k := TwoColorComponentSwap G rho D.gammaOne D.theta z;
    ∀ (hlastTwo : muTwo (T.edge D.lastEdgeIndex) = some D.gammaOne), D.theta ∈ MissingColors G
        muTwo (T.vertex D.terminalVertexIndex) → D.theta ∈ MissingColors G muTwo (T.vertex
        D.penultimateVertexIndex) →
    ∀ (hgammaPenTwo : D.gammaOne ∉ MissingColors G muTwo (T.vertex D.penultimateVertexIndex))
        (PTwo : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (hPTwo :
        PTwo.coloring = muTwo),
    let _ : HierarchySituationTwoTailData G k e0 PTwo.corresponding.replacementInput T
        PTwo.coloring PTwo.corresponding.replacementETT PTwo.replacementBase PTwo.counterexample
        PTwo.minimumContext := helperTailTwo2292 G k e0 input T phi ett base C ctx D htail POne
        sameStar hlastTwo hgammaPenTwo PTwo hPTwo; D.theta ∉ HierarchyStoredColorsAt
        PTwo.counterexample.hierarchy (Fin.last PTwo.counterexample.hierarchy.dividerCount) →
        False := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A htail z POne sameStar rho muTwo
      hlastTwo hthetaTermTwo hthetaPenTwo hgammaPenTwo PTwo hPTwo tailTwo hstored
  let finalData : HierarchySituationTwoCaseTwoData G k e0 PTwo.corresponding.replacementInput T
      PTwo.coloring PTwo.corresponding.replacementETT PTwo.replacementBase
      PTwo.counterexample PTwo.minimumContext :=
    { toHierarchySituationTwoTailData := tailTwo
      alpha := D.theta
      alphaMissingPenultimate := by
        change D.theta ∈ MissingColors G PTwo.coloring (T.vertex D.penultimateVertexIndex)
        rw [hPTwo]
        exact hthetaPenTwo
      alphaMissingTerminal := by
        change D.theta ∈ MissingColors G PTwo.coloring (T.vertex D.terminalVertexIndex)
        rw [hPTwo]
        exact hthetaTermTwo
      alphaOutsideStored := hstored }
  exact HierarchySituationTwoSubcaseTwoOne G k e0 PTwo.corresponding.replacementInput T
    PTwo.coloring PTwo.corresponding.replacementETT PTwo.replacementBase
    PTwo.counterexample PTwo.minimumContext finalData

private theorem helper_hfixedOne_2200.{u_1, u_2} :
    helperHfixedOne2200Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B hBlen hBT hAzero hAT hgammaUnused
      halphaExclusion z muOne hstableOne predecessorIncident terminalIncident missingNotColored
      seedStable t ht
  have hng := hgammaUnused t ht
  by_cases ha : phi (T.edge t) = some D.alpha
  · have hnotlast : t ≠ D.lastEdgeIndex := by
      intro he
      exact missingNotColored phi D.alpha _ D.alphaMissingTerminal _ terminalIncident (he ▸ ha)
    have hbound : t.val < B.length := by
      have hlast := D.lastEdgePosition
      have hb := t.isLt
      have hn : t.val ≠ D.lastEdgeIndex.val := fun he => hnotlast (Fin.ext he)
      omega
    let tB : Fin B.length := ⟨t.val, hbound⟩
    have hcast : Fin.castLE hBT.1 tB = t := Fin.ext rfl
    have heB : phi (B.edge tB) = some D.alpha := by rw [← hBT.2.2 tB, hcast]; exact ha
    obtain ⟨hqzero, hcore, hpos, f, hstep, hkind, hedges, heq, hcolor, hstored⟩ :=
      halphaExclusion tB ht (by
        change tB.val < A.length + (T.length - A.length - 1)
        have hb := tB.isLt
        omega) heB
    have hAX : A = ett.series.data.tree (Fin.last ett.rounds).castSucc :=
      (hAzero hqzero).trans hcore
    have hinc : TreeIncidentEdge (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (T.edge t) := by
      rw [← hAX]
      exact predecessorIncident A hAT t hpos
    exact (seedStable phi muOne ett base H hstableOne.1 hqzero).1 _ hinc
      ⟨D.alpha, Finset.mem_union_right _ hstored, ha⟩
  · simp [muOne, TwoColorComponentSwap, hng, ha]

private theorem helper_hfixedTailTwo_2433.{u_1, u_2} :
    helperHfixedTailTwo2433Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B hBlen hBT hAzero hAT hnotA
      hthetaExclusion z muOne predecessorIncident seedStable hfixedOne POne hPOne rho ettOne
      baseOne' COne' HOne qOne hgammaUnusedOne muTwo hstableTwo t ht hb
  have hng := hgammaUnusedOne t ht
  by_cases htheta : rho (T.edge t) = some D.theta
  · let tB : Fin B.length := ⟨t.val, hb⟩
    have hcast : Fin.castLE hBT.1 tB = t := Fin.ext rfl
    have heOld : phi (T.edge t) = some D.theta := by
      rw [show rho = muOne from hPOne, hfixedOne t ht] at htheta
      exact htheta
    have heB : phi (B.edge tB) = some D.theta := by
      rw [← hBT.2.2 tB, hcast]
      exact heOld
    obtain ⟨hzero, hcore, hpos, f, hstep, hkind, hedges, heq, hcolor, hstored⟩ :=
      hthetaExclusion tB ht (by
        change tB.val < A.length + (T.length - A.length - 1)
        have hb := tB.isLt
        omega) heB
    rcases POne.sameGood.1 with ⟨hcoreSame, hcount, hstages, hpositions, hpe, hclosure⟩
    have hzeroOne : HOne.dividerCount = 0 := hcount.symm.trans hzero
    have hnotPE : ett.series.data.kind (Fin.last ett.rounds) ≠
        some TashkinovExtensionKind.PE := by
      intro he
      rcases hkind with hs | hr
      · rw [hs] at he
        simp at he
      · rw [hr] at he
        simp at he
    have hnotPEOne : ettOne.series.data.kind (Fin.last ettOne.rounds) ≠
        some TashkinovExtensionKind.PE := fun hp => hnotPE (hpe.mpr hp)
    have hAX : A = ettOne.series.data.tree (Fin.last ettOne.rounds).castSucc :=
      (hAzero hzero).trans (hcoreSame.trans (baseOne'.nonparallel hnotPEOne))
    have hinc : TreeIncidentEdge (ettOne.series.data.tree (Fin.last ettOne.rounds).castSucc)
        (T.edge t) := by
      rw [← hAX]
      exact predecessorIncident A hAT t hpos
    have hthetaStored : D.theta ∈ HierarchyStoredColorsAt H q :=
      Finset.mem_sdiff.mpr ⟨hstored, hnotA D.thetaMissingPenultimate⟩
    rcases POne.sameGood.2 with ⟨hcount', hdata⟩
    have hi : Fin.cast (congrArg (fun n => n + 1) hcount') q = qOne := by
      apply Fin.ext
      simp [q, qOne, H, HOne, COne']
    have hd := (hdata q).1
    rw [hi] at hd
    have hs : D.theta ∈ HierarchyStoredColorsAt HOne qOne := hd ▸ hthetaStored
    have hs' := (Finset.mem_sdiff.mp hs).1
    exact (seedStable rho muTwo ettOne baseOne' HOne hstableTwo.1 hzeroOne).1 _ hinc
      ⟨D.theta, Finset.mem_union_right _ hs', htheta⟩
  · simp [muTwo, TwoColorComponentSwap, hng, htheta]

private abbrev helperContinuation3192Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoCaseOneTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
        (2 : ℕ) ≤ T.length - A.length → B.length + (1 : ℕ) = T.length → TreeSequenceInitialSegment
        B T → TreeSequenceInitialSegment A B → T.vertex D.penultimateVertexIndex ∈
        TreeSequenceVertexSet B → (
    ∀ {c : Fin k}, c ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex) → c ∉
        TreeMissingColors phi A) → D.gammaOne ≠ D.theta →
    let ig : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T D.gammaOne; T.vertex
        ig ∈ TreeSequenceVertexSet B → (
    ∀ (rho : PartialEdgeColoring E k) (a b : Fin k) (v : V), Sum.inl v ∈ TwoColorComponent G rho a
        b (Sum.inl v)) → T.vertex D.penultimateVertexIndex ≠ T.vertex D.terminalVertexIndex →
    let z : V ⊕ E := Sum.inl (T.vertex D.terminalVertexIndex);
    let muOne : PartialEdgeColoring E k := TwoColorComponentSwap G phi D.gammaOne D.alpha z;
        Incident G (T.vertex D.terminalVertexIndex) (T.edge D.lastEdgeIndex) → (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → muOne (T.edge t) = phi (T.edge t)) →
    ∀ (POne : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), POne.coloring =
        muOne → (
    ∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage P.counterexample.hierarchy (Fin.last
        P.counterexample.hierarchy.dividerCount) = A) → (
    ∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyFullTailPrefix P.counterexample (HierarchyFullTailLength P.counterexample - (1 :
        ℕ)) = B) →
    let rho : PartialEdgeColoring E k := POne.coloring;
    let ettOne : ExtendedTashkinovTree G k e0 POne.corresponding.replacementInput T POne.coloring
        := POne.corresponding.replacementETT;
    let _ : HierarchyBase POne.corresponding.replacementETT POne.coloring := POne.replacementBase;
    let COne' : HierarchyCounterexample POne.replacementBase := POne.counterexample;
    let _ : HierarchyMinimumCounterexampleContext G k e0 POne.corresponding.replacementInput T
        POne.coloring POne.corresponding.replacementETT POne.replacementBase POne.counterexample
        := POne.minimumContext;
    let HOne : TashkinovHierarchy POne.corresponding.replacementETT POne.replacementBase :=
        COne'.hierarchy;
    let qOne : Fin (HOne.dividerCount + (1 : ℕ)) := Fin.last HOne.dividerCount; (
    ∀ v ∈ TreeSequenceVertexSet B, MissingColors G rho v = MissingColors G phi v) → D.theta ∈
        MissingColors G rho (T.vertex D.penultimateVertexIndex) → D.gammaOne ∉ MissingColors G rho
        (T.vertex D.penultimateVertexIndex) → D.gammaOne ∈ MissingColors G rho (T.vertex
        D.terminalVertexIndex) → D.gammaOne ∈ MissingColors G rho (T.vertex ig) →
        HierarchyFirstMissingPosition rho T D.gammaOne = ig → HierarchyFirstMissingPosition rho T
        D.alpha = D.penultimateVertexIndex → D.alpha ∈ HierarchyStoredColorsAt HOne qOne ∧
        POne.counterexample.good.gamma qOne D.alpha = (insert D.gammaOne ({ D.gammaTwo } : Finset
        (Fin k)) : Finset (Fin k)) → (0 : ℕ) < HOne.dividerCount ∧ D.gammaOne ∈ TreeMissingColors
        rho (HOne.stage (⟨HOne.dividerCount,
    by omega
    ⟩ : Fin (HOne.dividerCount + (2 : ℕ)))) ∨ HOne.dividerCount = (0 : ℕ) ∧ D.gammaOne ∈
        TreeMissingColors rho (ettOne.series.data.tree (Fin.last ettOne.rounds).castSucc) →
        D.gammaOne ∈ TreeMissingColors rho B ∧ D.theta ∈ TreeMissingColors rho B → Disjoint
        (TwoColorComponent G rho D.gammaOne D.theta (Sum.inl (T.vertex D.terminalVertexIndex)))
        (TwoColorComponent G rho D.gammaOne D.theta (Sum.inl (T.vertex ig))) →
    let muTwo : PartialEdgeColoring E k := TwoColorComponentSwap G rho D.gammaOne D.theta z;
        TwoColorPathComponent G rho D.gammaOne D.theta z → (
    ∀ w ∈ TreeSequenceVertexSet B, MissingColors G (TwoColorComponentSwap G rho D.gammaOne D.theta
        z) w = MissingColors G rho w) → (
    ∀ (t : Fin T.length), (↑t : ℕ) < B.length → muTwo (T.edge t) = rho (T.edge t)) → (
    ∀ c ∈ HierarchyStoredColorsAt HOne qOne, HierarchyFirstMissingPosition muTwo T c =
        HierarchyFirstMissingPosition rho T c) → (
    ∀ {X Y F : TreeSequence G e0}, TreeSequenceInitialSegment X F → TreeSequenceInitialSegment Y F
        → X.length ≤ Y.length → TreeSequenceInitialSegment X Y) → False

private theorem helper_continuation_3192.{u_1, u_2} :
    helperContinuation3192Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B htail hBlen hBT hAB hyB hnotA
      hgammaTheta ig higB self hyt z muOne terminalIncident hfixedOne POne hPOne sameStar
      samePrefix rho ettOne baseOne' COne' ctxOne HOne qOne hmissingOne' hthetaPenOne
      hgammaPenOne hgammaTermOne hgammaWitnessOne' hfirstGammaOne hfirstAlphaOne hpairDataOne
      hcaseOne hmissingPairOne hdisjointTwo muTwo hpathTwo hmissingTwo hfixedPrefixTwo hstoredTwo
      commonPrefix
  have segmentTrans {X Y F : TreeSequence G e0}
      (hXY : TreeSequenceInitialSegment X Y) (hYF : TreeSequenceInitialSegment Y F) :
      TreeSequenceInitialSegment X F := by
    exact @TreeSequenceInitialSegment.trans V E G e0 (@X) (@Y) (@F) (@hXY) (@hYF)
  have hcoreLength : baseOne'.core.length ≤ A.length := by
    exact @helper_hcoreLength_1080 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@POne) (@sameStar)
  have transportRoute (S : TreeSequence G e0) (hs : TashkinovAugmentationSequence rho S B) :
      TashkinovAugmentationSequence muTwo S B := by
    have fixedEdges (index : Fin B.length) :
        muTwo (B.edge index) = rho (B.edge index) := by
      have fixed := hfixedPrefixTwo (Fin.castLE hBT.1 index) index.isLt
      rwa [hBT.2.2 index] at fixed
    apply TashkinovAugmentationSequence.transport_of_fixed fixedEdges ?_ hs
    intro initial segment _ vertex member
    exact hmissingTwo vertex (TreeSequenceInitialSegmentVertexSetSubset segment member)
  have hrouteTwo :
      (ettOne.series.data.kind (Fin.last ettOne.rounds) = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence muTwo
          (ettOne.series.data.tree (Fin.last ettOne.rounds).castSucc) B) ∨
      ((ettOne.series.data.kind (Fin.last ettOne.rounds) = some TashkinovExtensionKind.SE ∨
          ettOne.series.data.kind (Fin.last ettOne.rounds) = some TashkinovExtensionKind.RE) ∧
        ∃ f seed, ettOne.series.data.connectingEdges (Fin.last ettOne.rounds) = {f} ∧
          TreeSequenceAdjoinEdge (ettOne.series.data.tree (Fin.last ettOne.rounds).castSucc) f
              seed ∧
          TashkinovAugmentationSequence muTwo seed B) := by
    exact @helper_hrouteTwo_1126 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@htail) (@hBlen) (@hBT) (@POne) (@commonPrefix) (@segmentTrans) (@hcoreLength)
        (@transportRoute)
  have hthetaLastOne : rho (T.edge D.lastEdgeIndex) = some D.theta := by
    exact @helper_hthetaLastOne_1217 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@htail) (@hfixedOne) (@POne) (@hPOne)
  have hsuffix : TashkinovAugmentationSequence rho B T := by
    exact TashkinovAugmentationSequence.singleLastEdge hBlen hBT D.lastEdgeIndex
      D.lastEdgePosition hthetaLastOne hmissingPairOne.2
  have hgammaCutoff : ∀ c ∈ HierarchyStoredColorsAt HOne qOne,
      (D.gammaOne ∈ POne.counterexample.good.gamma qOne c ∨
        D.theta ∈ POne.counterexample.good.gamma qOne c) →
      (HierarchyFirstMissingPosition rho T c).val ≤ B.length := by
    exact @helper_hgammaCutoff_1234 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@hBlen) (@hAB) (@hnotA) (@POne) (@sameStar) (@hmissingOne') (@hfirstAlphaOne)
        (@hpairDataOne)
  obtain ⟨corrTwo, hmaxTwo, baseTwo, KTwo, goodTwo, hsameGoodTwo⟩ :=
    (StableChangeCasesOneTwoSplitTail G k e0 POne.corresponding.replacementInput T rho ettOne
      baseOne' COne' ctxOne D.gammaOne D.theta hgammaTheta
      (by rw [samePrefix POne]; exact hmissingPairOne)
      z hpathTwo muTwo rfl
      (by dsimp only; rcases hcaseOne with hpos | ⟨hzero, hm⟩
          · exact Or.inl hpos
          · exact Or.inr ⟨hzero, Or.inl hm⟩)
      (by dsimp only; rw [hfirstGammaOne]; exact hdisjointTwo)
      B (by dsimp only; rw [sameStar POne]; exact hAB)
      (by dsimp only; rw [sameStar POne]; clear * - htail hBlen; omega)
      (by rw [samePrefix POne]; exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩)
      (by dsimp only; intro t _ ht; exact hfixedPrefixTwo t ht)
      hrouteTwo hsuffix
      (by
        constructor
        · exact Finset.mem_biUnion.mpr ⟨_, higB, (hmissingTwo _ higB).symm ▸ hgammaWitnessOne'⟩
        · exact Finset.mem_biUnion.mpr ⟨_, hyB, (hmissingTwo _ hyB).symm ▸ hthetaPenOne⟩)
      (by rw [samePrefix POne]; exact hmissingTwo)
      hstoredTwo hgammaCutoff).2.2
  have hlastComponent : Sum.inr (T.edge D.lastEdgeIndex) ∈ TwoColorComponent G rho D.gammaOne
      D.theta z := by
    exact @helper_hlastComponent_1277 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@terminalIncident) (@POne) (@hthetaLastOne)
  have hlastTwo : muTwo (T.edge D.lastEdgeIndex) = some D.gammaOne := by
    simp [muTwo, TwoColorComponentSwap, hlastComponent, hthetaLastOne, hgammaTheta.symm]
  have hthetaTermTwo : D.theta ∈ MissingColors G muTwo (T.vertex D.terminalVertexIndex) :=
    (TwoColorComponentSwapMissingBehavior G rho D.gammaOne D.theta hgammaTheta ctxOne.proper z).2.1
      _ (self rho D.gammaOne D.theta _) hgammaTermOne
  have hthetaPenTwo : D.theta ∈ MissingColors G muTwo (T.vertex D.penultimateVertexIndex) := by
    rw [hmissingTwo _ hyB]
    exact hthetaPenOne
  have hgammaPenTwo : D.gammaOne ∉ MissingColors G muTwo (T.vertex D.penultimateVertexIndex) := by
    rw [hmissingTwo _ hyB]
    exact hgammaPenOne
  let CTwo : HierarchyCounterexample baseTwo :=
    { positive := by rw [corrTwo.rungAgreement]; exact COne'.positive
      hierarchy := KTwo
      good := goodTwo
      maximum := hmaxTwo
      notElementary := by
        intro he
        have hy : T.vertex D.penultimateVertexIndex ∈ TreeSequenceVertexSet T := by simp
            [TreeSequenceVertexSet]
        have ht : T.vertex D.terminalVertexIndex ∈ TreeSequenceVertexSet T := by simp
            [TreeSequenceVertexSet]
        exact Finset.disjoint_left.mp (he hy ht hyt) hthetaPenTwo hthetaTermTwo }
  obtain ⟨PTwo, hPTwo⟩ := HierarchyReplacementPresentationTrans G k e0 input T phi
    ett base C ctx POne muTwo corrTwo baseTwo CTwo hsameGoodTwo
  let tailTwo : HierarchySituationTwoTailData G k e0 PTwo.corresponding.replacementInput T
      PTwo.coloring PTwo.corresponding.replacementETT PTwo.replacementBase
      PTwo.counterexample PTwo.minimumContext := by
    exact @helperTailTwo2292 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@htail) (@POne)
        (@sameStar) (@hlastTwo) (@hgammaPenTwo) (@PTwo) (@hPTwo)
  by_cases hstored : D.theta ∈ HierarchyStoredColorsAt PTwo.counterexample.hierarchy
      (Fin.last PTwo.counterexample.hierarchy.dividerCount)
  · exact @helper_branch_2476 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@htail) (@POne)
      (@sameStar) (@hlastTwo) (@hthetaTermTwo) (@hthetaPenTwo) (@hgammaPenTwo) (@PTwo) (@hPTwo)
      (@hstored)
  · exact @helper_branch_2499 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@htail) (@POne)
      (@sameStar) (@hlastTwo) (@hthetaTermTwo) (@hthetaPenTwo) (@hgammaPenTwo) (@PTwo) (@hPTwo)
      (@hstored)

private theorem helper_continuation_2860.{u_1, u_2} :
    helperContinuation2860Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B htail hBlen hBT hAzero hAT hAB
      hyB hElementary hfirstAlpha hfirstTheta hnotA hgammaA hgammaTheta hthetaExclusion
      hgammaUnused ig hfirstGamma higB hmissing self leaf separate hgy hgt hyt z muOne
      prefixMissing predecessorIncident terminalIncident seedStable hfixedOne firstPreserved
      firstUnaffected hgammaTerminalOne POne hPOne sameStar samePrefix rho ettOne baseOne' COne'
      ctxOne HOne qOne hmissingOne'
  have hElementaryOne : ColoredVertexSetElementary G rho (TreeSequenceVertexSet B) := by
    intro u hu v hv huv
    rw [hmissingOne' u hu, hmissingOne' v hv]
    exact hElementary hu hv huv
  have hthetaPenOne : D.theta ∈ MissingColors G rho (T.vertex D.penultimateVertexIndex) := by
    rw [hmissingOne' _ hyB]
    exact D.thetaMissingPenultimate
  have hgammaPenOne : D.gammaOne ∉ MissingColors G rho (T.vertex D.penultimateVertexIndex) := by
    rw [hmissingOne' _ hyB]
    intro hm
    exact Finset.disjoint_left.mp (hElementary higB hyB hgy) hfirstGamma.1 hm
  have hgammaTermOne : D.gammaOne ∈ MissingColors G rho (T.vertex D.terminalVertexIndex) := by
    rw [show rho = muOne from hPOne]
    exact hgammaTerminalOne
  have hgammaWitnessOne' : D.gammaOne ∈ MissingColors G rho (T.vertex ig) := by
    rw [hmissingOne' _ higB]
    exact hfirstGamma.1
  have hgammaAOne : D.gammaOne ∈ TreeMissingColors rho A := by
    rcases Finset.mem_biUnion.mp hgammaA with ⟨v, hv, hm⟩
    refine Finset.mem_biUnion.mpr ⟨v, hv, ?_⟩
    rw [hmissingOne' _ (TreeSequenceInitialSegmentVertexSetSubset hAB hv)]
    exact hm
  have hfirstGammaOne : HierarchyFirstMissingPosition rho T D.gammaOne = ig :=
    firstPreserved phi rho D.gammaOne hmissingOne' hmissing.1
  have hfirstThetaOne : HierarchyFirstMissingPosition rho T D.theta = D.penultimateVertexIndex :=
    (firstPreserved phi rho D.theta hmissingOne'
      (Finset.mem_biUnion.mpr ⟨_, hyB, D.thetaMissingPenultimate⟩)).trans hfirstTheta
  have hfirstAlphaOne : HierarchyFirstMissingPosition rho T D.alpha = D.penultimateVertexIndex :=
    (firstPreserved phi rho D.alpha hmissingOne' hmissing.2).trans hfirstAlpha
  have hgammaUnusedOne : ∀ t : Fin T.length, A.length ≤ t.val →
      rho (T.edge t) ≠ some D.gammaOne := by
    intro t ht
    rw [show rho = muOne from hPOne, hfixedOne t ht]
    exact hgammaUnused t ht
  have hpairDataOne : D.alpha ∈ HierarchyStoredColorsAt HOne qOne ∧
      POne.counterexample.good.gamma qOne D.alpha = {D.gammaOne, D.gammaTwo} := by
    exact @helper_hpairDataOne_800 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@POne)
  have hgammaStageOne : D.gammaOne ∈ HierarchyStageMissingColors HOne qOne := by
    apply (Finset.mem_sdiff.mp
      (POne.counterexample.good.avoidance qOne D.alpha hpairDataOne.1 ?_)).1
    rw [hpairDataOne.2]
    simp
  have hcaseOne :
      (0 < HOne.dividerCount ∧ D.gammaOne ∈ TreeMissingColors rho
        (HOne.stage ⟨HOne.dividerCount, by omega⟩)) ∨
      (HOne.dividerCount = 0 ∧ D.gammaOne ∈ TreeMissingColors rho
        (ettOne.series.data.tree (Fin.last ettOne.rounds).castSucc)) := by
    exact @helper_hcaseOne_816 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@POne)
        (@hgammaStageOne)
  have hmissingPairOne : D.gammaOne ∈ TreeMissingColors rho B ∧
      D.theta ∈ TreeMissingColors rho B := by
    exact ⟨Finset.mem_biUnion.mpr ⟨_, higB, hgammaWitnessOne'⟩,
      Finset.mem_biUnion.mpr ⟨_, hyB, hthetaPenOne⟩⟩
  have hchangeOne := ChangeLemma G k e0 POne.corresponding.replacementInput T rho ettOne
    baseOne' COne' ctxOne.proper ctxOne.oneEdgeUncolored ctxOne.lowerRung
    ctxOne.fewerDividers ctxOne.lexicographicMinimality
    (by change ColoredVertexSetElementary G rho (TreeSequenceVertexSet
        (HierarchyFullTailPrefix COne' (HierarchyFullTailLength COne' - 1)))
        rw [samePrefix POne]; exact hElementaryOne)
    ctxOne.largeMissingSet D.gammaOne D.theta hgammaTheta
    (by change D.gammaOne ∈ TreeMissingColors rho (HierarchyFullTailPrefix COne'
          (HierarchyFullTailLength COne' - 1)) ∧ D.theta ∈ TreeMissingColors rho
            (HierarchyFullTailPrefix COne' (HierarchyFullTailLength COne' - 1))
        rw [samePrefix POne]; exact hmissingPairOne)
    (by
      dsimp only
      rw [sameStar POne, hfirstGammaOne, hfirstThetaOne]
      intro _
      refine ⟨⟨ig, D.penultimateVertexIndex, rfl, rfl, ?_⟩, ?_⟩
      · have hp := D.penultimateVertexPosition
        have hg : ig.val ≤ A.length := hfirstGamma.2
        clear * - hp hg htail
        omega
      · intro hc
        rcases (Finset.mem_filter.mp hc).2 with ⟨t, ht, _, he⟩
        exact hgammaUnusedOne t ht he)
  have hsameTwo : TwoColorComponent G rho D.gammaOne D.theta (Sum.inl (T.vertex ig)) =
      TwoColorComponent G rho D.gammaOne D.theta
        (Sum.inl (T.vertex D.penultimateVertexIndex)) := by
    rw [← hfirstGammaOne, ← hfirstThetaOne]
    rcases hcaseOne with ⟨hq, hm⟩ | ⟨hq, hm⟩
    · exact hchangeOne.1 ⟨hq, Or.inl hm⟩
    · exact hchangeOne.2.1 ⟨hq, Or.inl hm⟩
  have hdisjointTwo := separate rho D.gammaOne D.theta hgammaTheta ctxOne.proper
    (T.vertex ig) (T.vertex D.penultimateVertexIndex) (T.vertex D.terminalVertexIndex)
    hgy hgt hyt hgammaWitnessOne' hthetaPenOne (Or.inl hgammaTermOne) hsameTwo
  let muTwo := TwoColorComponentSwap G rho D.gammaOne D.theta z
  have hpathTwo : TwoColorPathComponent G rho D.gammaOne D.theta z :=
    ⟨hgammaTheta, _, self rho D.gammaOne D.theta _,
      leaf rho D.gammaOne D.theta hgammaTheta ctxOne.proper _ (Or.inl hgammaTermOne)⟩
  have hstableTwo := StableChangeCasesOneTwo G k e0 POne.corresponding.replacementInput T rho
    ettOne baseOne' COne' ctxOne.proper ctxOne.oneEdgeUncolored ctxOne.lowerRung
    ctxOne.fewerDividers ctxOne.lexicographicMinimality
    (by change ColoredVertexSetElementary G rho (TreeSequenceVertexSet
        (HierarchyFullTailPrefix COne' (HierarchyFullTailLength COne' - 1)))
        rw [samePrefix POne]; exact hElementaryOne)
    ctxOne.largeMissingSet D.gammaOne D.theta hgammaTheta
    (by change D.gammaOne ∈ TreeMissingColors rho (HierarchyFullTailPrefix COne'
          (HierarchyFullTailLength COne' - 1)) ∧ D.theta ∈ TreeMissingColors rho
            (HierarchyFullTailPrefix COne' (HierarchyFullTailLength COne' - 1))
        rw [samePrefix POne]; exact hmissingPairOne)
    z hpathTwo muTwo rfl
    (by dsimp only; rcases hcaseOne with hpos | ⟨hzero, hm⟩
        · exact Or.inl hpos
        · exact Or.inr ⟨hzero, Or.inl hm⟩)
    (by dsimp only; rw [hfirstGammaOne]; exact hdisjointTwo)
  have houtsideGammaTwo : Sum.inl (T.vertex ig) ∉ TwoColorComponent G rho D.gammaOne D.theta z := by
    intro hm
    exact Set.disjoint_left.mp hdisjointTwo hm (self rho D.gammaOne D.theta _)
  have houtsideThetaTwo : Sum.inl (T.vertex D.penultimateVertexIndex) ∉
      TwoColorComponent G rho D.gammaOne D.theta z := by
    intro hm
    apply Set.disjoint_left.mp hdisjointTwo hm
    rw [hsameTwo]
    exact self rho D.gammaOne D.theta _
  have hmissingTwo := prefixMissing rho D.gammaOne D.theta hgammaTheta ctxOne.proper
    hElementaryOne _ _ higB hyB hgammaWitnessOne' hthetaPenOne
    houtsideGammaTwo houtsideThetaTwo
  have hfixedTailTwo : ∀ t : Fin T.length, A.length ≤ t.val → t.val < B.length →
      muTwo (T.edge t) = rho (T.edge t) := by
    exact @helper_hfixedTailTwo_2433 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@hBlen) (@hBT) (@hAzero) (@hAT) (@hnotA) (@hthetaExclusion) (@predecessorIncident)
        (@seedStable) (@hfixedOne) (@POne) (@hPOne) (@hgammaUnusedOne) (@hstableTwo)
  have edgeCast (X Y : TreeSequence G e0) (h : X = Y) (i : Fin X.length) :
      X.edge i = Y.edge (Fin.cast (congrArg TreeSequence.length h) i) := by
    subst Y
    rfl
  have weakEdges {input' : PartialEdgeColoring E k}
      (old new : PartialEdgeColoring E k)
      (ett' : ExtendedTashkinovTree G k e0 input' T old)
      (base' : HierarchyBase ett' old) (K : TashkinovHierarchy ett' base')
      (hST : TreeSequenceInitialSegment (HierarchyStarredStage K (Fin.last K.dividerCount)) T)
      (hw : HierarchyWeaklyStable K (Fin.last K.dividerCount) new)
      (hp : IsProperEdgeColoring G old) (ho : IsOneEdgeUncolored old e0)
      (hnp : IsProperEdgeColoring G new) (hno : IsOneEdgeUncolored new e0) :
      ∀ t : Fin T.length, t.val < (HierarchyStarredStage K (Fin.last K.dividerCount)).length →
        new (T.edge t) = old (T.edge t) := by
    exact @helper_weakEdges_959 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@T) (@edgeCast) (@input') (@old) (@new) (@ett') (@base') (@K) (@hST)
        (@hw) (@hp) (@ho) (@hnp) (@hno)
  have hfixedCoreTwo : ∀ t : Fin T.length, t.val < A.length → muTwo (T.edge t) = rho (T.edge t)
     := by
    exact @helper_hfixedCoreTwo_1036 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@hAT)
        (@POne) (@sameStar) (@hstableTwo) (@weakEdges)
  have hfixedPrefixTwo : ∀ t : Fin T.length, t.val < B.length →
      muTwo (T.edge t) = rho (T.edge t) := by
    intro t ht
    by_cases ha : t.val < A.length
    · exact hfixedCoreTwo t ha
    · exact hfixedTailTwo t (by omega) ht
  have hstoredTwo : ∀ c ∈ HierarchyStoredColorsAt HOne qOne,
      HierarchyFirstMissingPosition muTwo T c = HierarchyFirstMissingPosition rho T c := by
    exact @helper_hstoredTwo_1050 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@hgammaTheta) (@firstPreserved) (@firstUnaffected) (@POne) (@sameStar) (@hgammaAOne)
        (@hmissingPairOne) (@hmissingTwo)
  have commonPrefix {X Y F : TreeSequence G e0}
      (hXF : TreeSequenceInitialSegment X F) (hYF : TreeSequenceInitialSegment Y F)
      (hXY : X.length ≤ Y.length) : TreeSequenceInitialSegment X Y := by
    exact @helper_commonPrefix_1062 (@V) (@E) (@G) (@e0) (@X) (@Y) (@F) (@hXF) (@hYF) (@hXY)
  exact @helper_continuation_3192 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@htail)
      (@hBlen) (@hBT) (@hAB) (@hyB) (@hnotA) (@hgammaTheta) (@higB) (@self) (@hyt)
      (@terminalIncident) (@hfixedOne) (@POne) (@hPOne) (@sameStar) (@samePrefix) (@hmissingOne')
      (@hthetaPenOne) (@hgammaPenOne) (@hgammaTermOne) (@hgammaWitnessOne') (@hfirstGammaOne)
      (@hfirstAlphaOne) (@hpairDataOne) (@hcaseOne) (@hmissingPairOne) (@hdisjointTwo)
      (@hpathTwo) (@hmissingTwo) (@hfixedPrefixTwo) (@hstoredTwo) (@commonPrefix)
private theorem helper_continuation_1912.{u_1, u_2} :
    helperContinuation1912Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B htail hBlen hBT hAzero hAT hAB
      hyB hElementary hfirstAlpha hfirstTheta hnotA hgammaA hgammaTheta hgammaAlpha
      hthetaExclusion hgammaUnused halphaExclusion firstWitness ig hfirstGamma higB hcase
      hmissing hsame self leaf separate hgy hgt
  have hyt : T.vertex D.penultimateVertexIndex ≠ T.vertex D.terminalVertexIndex := by
    exact @helper_hyt_415 (@V) (@E) inferInstance inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@hfirstTheta)
  have hdisjoint := separate phi D.gammaOne D.alpha hgammaAlpha ctx.proper
    (T.vertex ig) (T.vertex D.penultimateVertexIndex) (T.vertex D.terminalVertexIndex)
    hgy hgt hyt hfirstGamma.1 D.alphaMissingPenultimate (Or.inr D.alphaMissingTerminal) hsame
  let z : Sum V E := Sum.inl (T.vertex D.terminalVertexIndex)
  let muOne := TwoColorComponentSwap G phi D.gammaOne D.alpha z
  have hpath : TwoColorPathComponent G phi D.gammaOne D.alpha z :=
    ⟨hgammaAlpha, _, self phi D.gammaOne D.alpha _,
      leaf phi D.gammaOne D.alpha hgammaAlpha ctx.proper _ (Or.inr D.alphaMissingTerminal)⟩
  have hstableOne := StableChangeCasesOneTwo G k e0 input T phi ett base C
    ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
    ctx.lexicographicMinimality hElementary ctx.largeMissingSet
    D.gammaOne D.alpha hgammaAlpha hmissing z hpath muOne rfl
    (by
      dsimp only
      rcases hcase with hpos | ⟨hzero, hm⟩
      · exact Or.inl hpos
      · exact Or.inr ⟨hzero, Or.inl hm⟩)
    hdisjoint
  have prefixMissing (rho : PartialEdgeColoring E k) (a b : Fin k) (hne : a ≠ b)
      (hp : IsProperEdgeColoring G rho)
      (helem : ColoredVertexSetElementary G rho (TreeSequenceVertexSet B))
      (u v : V) (huB : u ∈ TreeSequenceVertexSet B) (hvB : v ∈ TreeSequenceVertexSet B)
      (hu : a ∈ MissingColors G rho u) (hv : b ∈ MissingColors G rho v)
      (hdu : Sum.inl u ∉ TwoColorComponent G rho a b z)
      (hdv : Sum.inl v ∉ TwoColorComponent G rho a b z) :
      ∀ w ∈ TreeSequenceVertexSet B,
        MissingColors G (TwoColorComponentSwap G rho a b z) w = MissingColors G rho w := by
    exact TwoColorComponentSwapMissingOnElementarySet (TreeSequenceVertexSet B) rho a b
      hne hp helem z u v huB hvB hu hv hdu hdv
  have houtsideGamma : Sum.inl (T.vertex ig) ∉ TwoColorComponent G phi D.gammaOne D.alpha z := by
    intro hm
    exact Set.disjoint_left.mp hdisjoint hm (self phi D.gammaOne D.alpha _)
  have houtsideAlpha : Sum.inl (T.vertex D.penultimateVertexIndex) ∉
      TwoColorComponent G phi D.gammaOne D.alpha z := by
    intro hm
    apply Set.disjoint_left.mp hdisjoint hm
    rw [hsame]
    exact self phi D.gammaOne D.alpha _
  have hmissingOne := prefixMissing phi D.gammaOne D.alpha hgammaAlpha ctx.proper
    hElementary _ _ higB hyB hfirstGamma.1 D.alphaMissingPenultimate
    houtsideGamma houtsideAlpha
  have predecessorIncident (X : TreeSequence G e0)
      (hXT : TreeSequenceInitialSegment X T) (t : Fin T.length)
      (ht : t.val = X.length) : TreeIncidentEdge X (T.edge t) := by
    exact @helper_predecessorIncident_507 (@V) (@E) inferInstance inferInstance (@G) (@e0) (@T)
        (@X) (@hXT) (@t) (@ht)
  have terminalIncident : Incident G (T.vertex D.terminalVertexIndex) (T.edge D.lastEdgeIndex) := by
    exact @helper_terminalIncident_524 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
  have missingNotColored (rho : PartialEdgeColoring E k) (c : Fin k) (v : V)
      (hm : c ∈ MissingColors G rho v) (e : E) (hi : Incident G v e) :
      rho e ≠ some c := by
    exact @helper_missingNotColored_535 (@V) (@E) inferInstance inferInstance (@G) (@k) (@rho)
        (@c) (@v) (@hm) (@e) (@hi)
  have seedStable {input' : PartialEdgeColoring E k}
      (rho sigma : PartialEdgeColoring E k)
      (ett' : ExtendedTashkinovTree G k e0 input' T rho)
      (base' : HierarchyBase ett' rho) (K : TashkinovHierarchy ett' base')
      (hw : HierarchyWeaklyStable K (Fin.last K.dividerCount) sigma)
      (hq : K.dividerCount = 0) :
      StableColoring (ett'.series.data.tree (Fin.last ett'.rounds).castSucc)
        (TashkinovStoredColors ett'.series.data (Fin.last ett'.rounds)) rho sigma := by
    exact @helper_seedStable_543 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@T) (@input') (@rho) (@sigma) (@ett') (@base') (@K) (@hw)
        (@hq)
  have hfixedOne : ∀ t : Fin T.length, A.length ≤ t.val →
      muOne (T.edge t) = phi (T.edge t) := by
    exact @helper_hfixedOne_2200 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@hBlen) (@hBT) (@hAzero) (@hAT) (@hgammaUnused) (@halphaExclusion) (@hstableOne)
        (@predecessorIncident) (@terminalIncident) (@missingNotColored) (@seedStable)
  have firstPreserved (rho sigma : PartialEdgeColoring E k) (c : Fin k)
      (hmiss : ∀ v ∈ TreeSequenceVertexSet B, MissingColors G sigma v = MissingColors G rho v)
      (hc : c ∈ TreeMissingColors rho B) :
      HierarchyFirstMissingPosition sigma T c = HierarchyFirstMissingPosition rho T c := by
    exact TreeSequenceFirstMissingPositionCongrOfPrefix hBT hmiss hc
  have firstUnaffected (rho : PartialEdgeColoring E k) (a b c : Fin k)
      (hne : a ≠ b) (hp : IsProperEdgeColoring G rho) (hca : c ≠ a) (hcb : c ≠ b) :
      HierarchyFirstMissingPosition (TwoColorComponentSwap G rho a b z) T c =
        HierarchyFirstMissingPosition rho T c := by
    apply TreeSequenceFirstMissingPositionMembershipCongr
    intro index
    exact (TwoColorComponentSwapMissingBehavior G rho a b hne hp z).2.2.2
      (T.vertex index) c hca hcb
  have hstoredOne : ∀ c ∈ HierarchyStoredColorsAt H q,
      HierarchyFirstMissingPosition muOne T c = HierarchyFirstMissingPosition phi T c := by
    exact @helper_hstoredOne_643 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@hgammaA) (@hgammaAlpha) (@hmissing) (@hmissingOne) (@firstPreserved) (@firstUnaffected)
  obtain ⟨corrOne, hmaxOne, baseOne, KOne, goodOne, hsameOne⟩ :=
    (StableChangeCasesOneTwoFullTail G k e0 input T phi ett base C ctx
      D.gammaOne D.alpha hgammaAlpha hmissing z hpath muOne rfl
      (by
        dsimp only
        rcases hcase with hpos | ⟨hzero, hm⟩
        · exact Or.inl hpos
        · exact Or.inr ⟨hzero, Or.inl hm⟩)
      hdisjoint hfixedOne hmissingOne hstoredOne).2.2.2.2
  have hgammaTerminalOne : D.gammaOne ∈ MissingColors G muOne (T.vertex D.terminalVertexIndex) :=
    (TwoColorComponentSwapMissingBehavior G phi D.gammaOne D.alpha hgammaAlpha ctx.proper z).2.2.1
      _ (self phi D.gammaOne D.alpha _) D.alphaMissingTerminal
  have hgammaWitnessOne : D.gammaOne ∈ MissingColors G muOne (T.vertex ig) := by
    rw [hmissingOne _ higB]
    exact hfirstGamma.1
  let COne : HierarchyCounterexample baseOne :=
    { positive := by rw [corrOne.rungAgreement]; exact C.positive
      hierarchy := KOne
      good := goodOne
      maximum := hmaxOne
      notElementary := by
        intro he
        have hg : T.vertex ig ∈ TreeSequenceVertexSet T := by simp [TreeSequenceVertexSet]
        have ht : T.vertex D.terminalVertexIndex ∈ TreeSequenceVertexSet T := by simp
            [TreeSequenceVertexSet]
        exact Finset.disjoint_left.mp (he hg ht hgt) hgammaWitnessOne hgammaTerminalOne }
  have seriesFacts : ∀ j : Fin (ett.rounds + 1),
      IsProperEdgeColoring G (ett.series.data.coloring j) ∧
        IsOneEdgeUncolored (ett.series.data.coloring j) e0 := by
    exact ett.series.coloringProperties
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
  obtain ⟨POne, hPOne⟩ := HierarchyReplacementPresentationTrans G k e0 input T phi
    ett base C ctx PRefl muOne corrOne baseOne COne hsameOne
  have sameStar (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) :
      HierarchyStarredStage P.counterexample.hierarchy
        (Fin.last P.counterexample.hierarchy.dividerCount) = A := by
    exact @SharedFacts.FirstSubcaseTransport.sameStar (@V) (@E) inferInstance inferInstance
        inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
  have samePrefix (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) :
      HierarchyFullTailPrefix P.counterexample (HierarchyFullTailLength P.counterexample - 1) = B
         := by
    simp only [HierarchyFullTailPrefix, HierarchyFullTailLength, sameStar P]
    rfl
  let rho := POne.coloring
  let ettOne := POne.corresponding.replacementETT
  let baseOne' := POne.replacementBase
  let COne' := POne.counterexample
  let ctxOne := POne.minimumContext
  let HOne := COne'.hierarchy
  let qOne : Fin (HOne.dividerCount + 1) := Fin.last HOne.dividerCount
  have hmissingOne' : ∀ v ∈ TreeSequenceVertexSet B,
      MissingColors G rho v = MissingColors G phi v := by
    rw [show rho = muOne from hPOne]
    exact hmissingOne
  exact @helper_continuation_2860 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@htail)
      (@hBlen) (@hBT) (@hAzero) (@hAT) (@hAB) (@hyB) (@hElementary) (@hfirstAlpha) (@hfirstTheta)
      (@hnotA) (@hgammaA) (@hgammaTheta) (@hthetaExclusion) (@hgammaUnused) (@hfirstGamma)
      (@higB) (@hmissing) (@self) (@leaf) (@separate) (@hgy) (@hgt) (@hyt) (@prefixMissing)
      (@predecessorIncident) (@terminalIncident) (@seedStable) (@hfixedOne) (@firstPreserved)
      (@firstUnaffected) (@hgammaTerminalOne) (@POne) (@hPOne) (@sameStar) (@samePrefix)
      (@hmissingOne')
theorem HierarchySituationTwoSubcaseOneTwo {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (D : HierarchySituationTwoCaseOneTwoData
      G k e0 input T phi ett base C ctx) :
    False := by
  classical
  let H := C.hierarchy
  let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
  let A := HierarchyStarredStage H q
  let B := HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1)
  have htail : 2 ≤ T.length - A.length := D.tailAtLeastTwo
  have hBlen : B.length + 1 = T.length := by
    simp only [B, HierarchyFullTailPrefix, HierarchyFullTailLength,
      TreeSequencePrefix]
    change min (A.length + (T.length - A.length - 1)) T.length + 1 = T.length
    omega
  have hBT : TreeSequenceInitialSegment B T := by
    exact @SharedFacts.FirstSubcaseTransport.bT (@V) (@E) inferInstance inferInstance
        inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hBlen)
  have hApositive (hq : 0 < H.dividerCount) :
      A = H.stage ⟨H.dividerCount, by omega⟩ := by
    exact @helper_hApositive_116 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hq)
  have hAzero (hq : H.dividerCount = 0) : A = base.core := by
    have hi : q = 0 := by apply Fin.ext; simp [q, hq]
    change HierarchyStarredStage H q = _
    rw [hi]
    rfl
  have hAT : TreeSequenceInitialSegment A T := by
    exact H.lastStarredInitialSegment
  have hAB : TreeSequenceInitialSegment A B := by
    exact @helper_hAB_146 (@V) (@E) inferInstance inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@htail) (@hBlen) (@hApositive)
        (@hAzero) (@hAT)
  have hBterminal : B.vertex (Fin.last B.length) = T.vertex D.penultimateVertexIndex := by
    exact @helper_hBterminal_152 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@hBlen) (@hBT)
  have hyB : T.vertex D.penultimateVertexIndex ∈ TreeSequenceVertexSet B := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨Fin.last B.length, hBterminal⟩
  have hElementary : ColoredVertexSetElementary G phi (TreeSequenceVertexSet B) :=
    HierarchyCounterexamplePenultimateElementary G k e0 input T phi ett base C
      ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
      ctx.lexicographicMinimality ctx.largeMissingSet
  have firstAt {c : Fin k}
      (hc : c ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex)) :
      HierarchyFirstMissingPosition phi T c = D.penultimateVertexIndex := by
    exact TreeSequenceFirstMissingPositionEq hBT hElementary (by
      have := D.penultimateVertexPosition
      omega) hc
  have hfirstAlpha := firstAt D.alphaMissingPenultimate
  have hfirstTheta := firstAt D.thetaMissingPenultimate
  have hnotA {c : Fin k}
      (hc : c ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex)) :
      c ∉ TreeMissingColors phi A := by
    exact hAB.missingColorNotInPrefix hAT hElementary hyB (by
      have position := D.penultimateVertexPosition
      clear * - position htail
      omega) hc
  have hthetaGamma : D.theta ∉ (HierarchyStoredColorsAt H q).biUnion (C.good.gamma q) := by
    intro hc
    rcases Finset.mem_biUnion.mp hc with ⟨eta, heta, hpair⟩
    exact hnotA D.thetaMissingPenultimate
      ((GoodHierarchyReservedDisjoint C.good q).1 eta heta hpair)
  have hgammaPair : D.gammaOne ∈ C.good.gamma q D.alpha := by
    rw [D.gammaPair]
    simp
  have hgammaA : D.gammaOne ∈ TreeMissingColors phi A :=
    (GoodHierarchyReservedDisjoint C.good q).1 D.alpha D.alphaStored hgammaPair
  have hgammaTheta : D.gammaOne ≠ D.theta := by
    intro he
    exact hnotA D.thetaMissingPenultimate (he ▸ hgammaA)
  have hgammaAlpha : D.gammaOne ≠ D.alpha := by
    intro he
    exact hnotA D.alphaMissingPenultimate (he ▸ hgammaA)
  have hthetaExclusion := HierarchyTailMissingColorExclusion G k e0 input T phi
    ett base H hElementary (HierarchyFullTailLength C - 1)
    (by change 1 ≤ T.length - A.length - 1; omega)
    (by change T.length - A.length - 1 < T.length - A.length; omega)
    D.theta (by
      change D.theta ∈ MissingColors G phi (B.vertex (Fin.last B.length))
      rw [hBterminal]
      exact D.thetaMissingPenultimate)
  have hgammaUnused : ∀ t : Fin T.length, A.length ≤ t.val →
      phi (T.edge t) ≠ some D.gammaOne := by
    exact @helper_hgammaUnused_232 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@hfirstAlpha) (@hfirstTheta) (@hgammaPair) (@hgammaTheta)
  have halphaExclusion := HierarchyTailMissingColorExclusion G k e0 input T phi
    ett base H hElementary (HierarchyFullTailLength C - 1)
    (by change 1 ≤ T.length - A.length - 1; omega)
    (by change T.length - A.length - 1 < T.length - A.length; omega)
    D.alpha (by
      change D.alpha ∈ MissingColors G phi (B.vertex (Fin.last B.length))
      rw [hBterminal]
      exact D.alphaMissingPenultimate)
  have firstWitness (rho : PartialEdgeColoring E k) (X : TreeSequence G e0)
      (hXT : TreeSequenceInitialSegment X T) (c : Fin k)
      (hc : c ∈ TreeMissingColors rho X) :
      c ∈ MissingColors G rho (T.vertex (HierarchyFirstMissingPosition rho T c)) ∧
      (HierarchyFirstMissingPosition rho T c).val ≤ X.length := by
    exact TreeSequenceFirstMissingPositionPrefixWitness hXT hc
  let ig := HierarchyFirstMissingPosition phi T D.gammaOne
  have hfirstGamma := firstWitness phi A hAT D.gammaOne hgammaA
  have higB : T.vertex ig ∈ TreeSequenceVertexSet B := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    have hg : ig.val ≤ A.length := hfirstGamma.2
    refine ⟨⟨ig.val, by omega⟩, ?_⟩
    rfl
  have hgammaStage : D.gammaOne ∈ HierarchyStageMissingColors H q :=
    (Finset.mem_sdiff.mp (C.good.avoidance q D.alpha D.alphaStored hgammaPair)).1
  have hcase :
      (0 < H.dividerCount ∧ D.gammaOne ∈ TreeMissingColors phi
        (H.stage ⟨H.dividerCount, by omega⟩)) ∨
      (H.dividerCount = 0 ∧ D.gammaOne ∈ TreeMissingColors phi
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)) := by
    exact @helper_hcase_297 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@hgammaStage)
  have hmissing : D.gammaOne ∈ TreeMissingColors phi B ∧
      D.alpha ∈ TreeMissingColors phi B := by
    refine ⟨?_, Finset.mem_biUnion.mpr ⟨_, hyB, D.alphaMissingPenultimate⟩⟩
    rcases Finset.mem_biUnion.mp hgammaA with ⟨v, hv, hm⟩
    exact Finset.mem_biUnion.mpr ⟨v, TreeSequenceInitialSegmentVertexSetSubset hAB hv, hm⟩
  have hchange := ChangeLemma G k e0 input T phi ett base C ctx.proper
    ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers ctx.lexicographicMinimality
    hElementary ctx.largeMissingSet D.gammaOne D.alpha hgammaAlpha hmissing
    (by
      dsimp only
      intro _
      rw [hfirstAlpha]
      refine ⟨⟨ig, D.penultimateVertexIndex, rfl, rfl, ?_⟩, ?_⟩
      · have hp := D.penultimateVertexPosition
        have hg : ig.val ≤ A.length := hfirstGamma.2
        clear * - hp hg htail
        omega
      · intro hc
        rcases (Finset.mem_filter.mp hc).2 with ⟨t, ht, _, he⟩
        exact hgammaUnused t ht he)
  have hsame : TwoColorComponent G phi D.gammaOne D.alpha (Sum.inl (T.vertex ig)) =
      TwoColorComponent G phi D.gammaOne D.alpha
        (Sum.inl (T.vertex D.penultimateVertexIndex)) := by
    rw [← hfirstAlpha]
    rcases hcase with ⟨hq, hm⟩ | ⟨hq, hm⟩
    · exact hchange.1 ⟨hq, Or.inl hm⟩
    · exact hchange.2.1 ⟨hq, Or.inl hm⟩
  have self (rho : PartialEdgeColoring E k) (a b : Fin k) (v : V) :
      Sum.inl v ∈ TwoColorComponent G rho a b (Sum.inl v) := by
    change (TwoColorIncidenceGraph G rho a b).connectedComponentMk (Sum.inl v) = _
    rfl
  have leaf := TwoColorMissingVertexLeaf G k
  have separate (rho : PartialEdgeColoring E k) (a b : Fin k) (hne : a ≠ b)
      (hp : IsProperEdgeColoring G rho) (u v w : V)
      (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
      (hu : a ∈ MissingColors G rho u) (hv : b ∈ MissingColors G rho v)
      (hw : a ∈ MissingColors G rho w ∨ b ∈ MissingColors G rho w)
      (hsame : TwoColorComponent G rho a b (Sum.inl u) =
        TwoColorComponent G rho a b (Sum.inl v)) :
      Disjoint (TwoColorComponent G rho a b (Sum.inl w))
        (TwoColorComponent G rho a b (Sum.inl u)) := by
    exact TwoColorMissingVerticesDisjoint G k rho a b hne hp u v w huv huw hvw hu hv hw hsame
  have prefixGap : A.length + 2 ≤ T.length := by
    simpa only [Nat.add_comm] using Nat.add_le_of_le_sub hAT.1 htail
  have beforePenultimate : A.length < D.penultimateVertexIndex.val := by
    apply Nat.lt_of_add_lt_add_right (n := 1)
    rw [D.penultimateVertexPosition]
    exact Nat.lt_of_succ_le prefixGap
  have vertexAfterPrefixDistinct (j : Fin (T.length + 1)) (hposition : A.length < j.val) :
      T.vertex ig ≠ T.vertex j :=
    T.vertex_injective.ne (Fin.ne_of_val_ne
      (Nat.ne_of_lt (hfirstGamma.2.trans_lt hposition)))
  have hgy := vertexAfterPrefixDistinct D.penultimateVertexIndex beforePenultimate
  have hgt := vertexAfterPrefixDistinct D.terminalVertexIndex (by
    rw [D.terminalVertexPosition]
    exact Nat.sub_pos_iff_lt.mp ((by decide : 0 < 2).trans_le htail))
  exact @helper_continuation_1912 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@htail)
      (@hBlen) (@hBT) (@hAzero) (@hAT) (@hAB) (@hyB) (@hElementary) (@hfirstAlpha) (@hfirstTheta)
      (@hnotA) (@hgammaA) (@hgammaTheta) (@hgammaAlpha) (@hthetaExclusion) (@hgammaUnused)
      (@halphaExclusion) (@firstWitness) (@hfirstGamma) (@higB) (@hcase) (@hmissing) (@hsame)
      (@self) (@leaf) (@separate) (@hgy) (@hgt)
end GoldbergSeymour

end
