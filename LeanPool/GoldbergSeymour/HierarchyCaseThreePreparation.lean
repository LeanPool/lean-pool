/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ChangeLemma
public import LeanPool.GoldbergSeymour.BoundaryEdges
public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary
public import LeanPool.GoldbergSeymour.ColoredVertexSetClosed
public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTree
public import LeanPool.GoldbergSeymour.ExtendedTashkinovTree
public import LeanPool.GoldbergSeymour.GoodHierarchy
public import LeanPool.GoldbergSeymour.GoodHierarchyReservedDisjoint
public import LeanPool.GoldbergSeymour.HierarchyBase
public import LeanPool.GoldbergSeymour.HierarchyCounterexample
public import LeanPool.GoldbergSeymour.HierarchyCounterexampleLess
public import LeanPool.GoldbergSeymour.HierarchyCounterexamplePenultimateElementary
public import LeanPool.GoldbergSeymour.HierarchyCounterexampleMeasure
public import LeanPool.GoldbergSeymour.HierarchyFirstMissingPosition
public import LeanPool.GoldbergSeymour.HierarchyFullTailLength
public import LeanPool.GoldbergSeymour.HierarchyFullTailPrefix
public import LeanPool.GoldbergSeymour.HierarchyLEMStable
public import LeanPool.GoldbergSeymour.HierarchyMinimumCounterexampleContext
public import LeanPool.GoldbergSeymour.HierarchyNonparallelFirstEdge
public import LeanPool.GoldbergSeymour.HierarchyPathNumber
public import LeanPool.GoldbergSeymour.HierarchyReplacementPresentation
public import LeanPool.GoldbergSeymour.HierarchySegmentColors
public import LeanPool.GoldbergSeymour.HierarchySituationTwoCaseThreeData
public import LeanPool.GoldbergSeymour.HierarchySituationTwoCaseThreeNormalizedData
public import LeanPool.GoldbergSeymour.HierarchySituationTwoCommonTailData
public import LeanPool.GoldbergSeymour.HierarchySituationTwoOutsidePenultimateReconstruction
public import LeanPool.GoldbergSeymour.HierarchyStageMissingColors
public import LeanPool.GoldbergSeymour.HierarchyStarredStage
public import LeanPool.GoldbergSeymour.HierarchyStoredColorsAt
public import LeanPool.GoldbergSeymour.IsProperEdgeColoring
public import LeanPool.GoldbergSeymour.MaximumDefectiveChoice
public import LeanPool.GoldbergSeymour.MaximumPropertyTransport
public import LeanPool.GoldbergSeymour.MissingColors
public import LeanPool.GoldbergSeymour.ModColoring
public import LeanPool.GoldbergSeymour.NineN
public import LeanPool.GoldbergSeymour.RevisitingExtensionCertificate
public import LeanPool.GoldbergSeymour.SameGoodHierarchy
public import LeanPool.GoldbergSeymour.StableColoringIncidentEdgeCriterion
public import LeanPool.GoldbergSeymour.StableColoring
public import LeanPool.GoldbergSeymour.StableChangeCasesOneTwoFullTail
public import LeanPool.GoldbergSeymour.TashkinovAugmentation
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequence
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceRestrict
public import LeanPool.GoldbergSeymour.TashkinovClosure
public import LeanPool.GoldbergSeymour.TashkinovHierarchy
public import LeanPool.GoldbergSeymour.TashkinovSeries
public import LeanPool.GoldbergSeymour.TashkinovSeriesStep
public import LeanPool.GoldbergSeymour.TashkinovStoredColors
public import LeanPool.GoldbergSeymour.Td
public import LeanPool.GoldbergSeymour.TreeSequence
public import LeanPool.GoldbergSeymour.TreeSequenceAdjoinEdge
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegment
public import LeanPool.GoldbergSeymour.TwoColorComponentSpanningPath
public import LeanPool.GoldbergSeymour.TwoColorComponentSwap
public import LeanPool.GoldbergSeymour.TwoColorComponentsDisjoint
public import LeanPool.GoldbergSeymour.TwoColorIncidenceDegreeAtMostTwo
public import LeanPool.GoldbergSeymour.TwoColorIncidenceGraph
public import LeanPool.GoldbergSeymour.NormalizedDatum
public import Mathlib.Data.Finset.Option
public import LeanPool.GoldbergSeymour.TashkinovAlternatingSegmentAppend
public import LeanPool.GoldbergSeymour.TwoColorComponentNearestSegment
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceInitialSegment
public import LeanPool.GoldbergSeymour.HierarchyBaseCorrespondingTransport
public import LeanPool.GoldbergSeymour.HierarchyFirstMissingPositionPrefixCutoff
public import LeanPool.GoldbergSeymour.MinimumContextTransport
public import LeanPool.GoldbergSeymour.TwoColorComponentSwapMissingBehavior
public import LeanPool.GoldbergSeymour.BaseDisplayedEdges

/-!
# Preparatory lemmas for hierarchy case-three normalization

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Dependent contract shared by the hierarchy construction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev HierarchyCaseThreePreparation.helperContinuation547Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoCaseThreeData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := T.length - A.length;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    let Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let Gamma : Finset (Fin k) := Dnq.biUnion (C.good.gamma q);
    let tailUsed : Finset (Fin k) := ({c : Fin k |
    ∃ (t : Fin T.length), A.length ≤ (↑t : ℕ) ∧ phi (T.edge t) = some c} : Finset (Fin k));
    ∀ beta ∈ TreeMissingColors phi B, (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → phi (T.edge t) ≠ some beta) → (0 : ℕ) <
        H.dividerCount ∧ beta ∉ Dnq ∧ beta ∉ Gamma ∨ H.dividerCount = (0 : ℕ) ∧ beta ∉ Dn ∧ beta ∉
        Gamma ∨ beta ∈ Dnq ∧ Disjoint (C.good.gamma q beta) tailUsed →
    let Bplus : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 :
        ℕ));
    let Q : Set (V ⊕ E) := TwoColorComponent G phi D.alpha beta (Sum.inl (T.vertex
        D.terminalVertexIndex)); beta ∉ MissingColors G phi (T.vertex D.terminalVertexIndex) → (
    ∃ v ∈ TreeSequenceVertexSet Bplus, Sum.inl v ∈ Q) → B.length = T.length - (2 : ℕ) →
        Bplus.length = T.length - (1 : ℕ) → TreeSequenceInitialSegment B T →
        TreeSequenceInitialSegment Bplus T → TreeSequenceInitialSegment B Bplus →
        (↑D.earlierVertexIndex : ℕ) < B.length + (1 : ℕ) → beta ∈ TreeMissingColors phi Bplus →
        D.alpha ∈ TreeMissingColors phi Bplus → D.alpha ≠ beta → T.vertex D.terminalVertexIndex ∉
        TreeSequenceVertexSet Bplus → (
    ∀ {S U W : TreeSequence G e0}, TreeSequenceInitialSegment S U → TreeSequenceInitialSegment U W
        → TreeSequenceInitialSegment S W) → (
    ∀ {S U W : TreeSequence G e0}, TreeSequenceInitialSegment S W → TreeSequenceInitialSegment U W
        → S.length ≤ U.length → TreeSequenceInitialSegment S U) → (
    ∀ {S U : TreeSequence G e0}, TreeSequenceInitialSegment S U → S.length = U.length → S = U) → (
    ∀ (a d : ℕ) (hbound : a + d ≤ H.dividerCount + (1 : ℕ)), TreeSequenceInitialSegment (H.stage
        (⟨a,
    by
      have := TreeSequence.positive T
      omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) (H.stage (⟨a + d,
    by
      have := TreeSequence.positive T
      omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ))))) → ( H.dividerCount ≠ (0 : ℕ) → A = H.stage q.castSucc) →
        TreeSequenceInitialSegment A T →
    ∃ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), Nonempty
        (HierarchySituationTwoCaseThreeNormalizedData G k e0 P.corresponding.replacementInput T
        P.coloring P.corresponding.replacementETT P.replacementBase P.counterexample
        P.minimumContext)

/-- Dependent contract shared by the hierarchy construction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev HierarchyCaseThreePreparation.helperContinuation647Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoCaseThreeData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := T.length - A.length;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    let Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let Gamma : Finset (Fin k) := Dnq.biUnion (C.good.gamma q);
    let tailUsed : Finset (Fin k) := ({c : Fin k |
    ∃ (t : Fin T.length), A.length ≤ (↑t : ℕ) ∧ phi (T.edge t) = some c} : Finset (Fin k));
    ∀ beta ∈ TreeMissingColors phi B, (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → phi (T.edge t) ≠ some beta) → (0 : ℕ) <
        H.dividerCount ∧ beta ∉ Dnq ∧ beta ∉ Gamma ∨ H.dividerCount = (0 : ℕ) ∧ beta ∉ Dn ∧ beta ∉
        Gamma ∨ beta ∈ Dnq ∧ Disjoint (C.good.gamma q beta) tailUsed →
    let Bplus : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 :
        ℕ));
    let Q : Set (V ⊕ E) := TwoColorComponent G phi D.alpha beta (Sum.inl (T.vertex
        D.terminalVertexIndex)); beta ∉ MissingColors G phi (T.vertex D.terminalVertexIndex) →
        B.length = T.length - (2 : ℕ) → Bplus.length = T.length - (1 : ℕ) →
        TreeSequenceInitialSegment B T → TreeSequenceInitialSegment Bplus T →
        TreeSequenceInitialSegment B Bplus → (↑D.earlierVertexIndex : ℕ) < B.length + (1 : ℕ) →
        beta ∈ TreeMissingColors phi Bplus → D.alpha ∈ TreeMissingColors phi Bplus → D.alpha ≠
        beta → T.vertex D.terminalVertexIndex ∉ TreeSequenceVertexSet Bplus → (
    ∀ {S U W : TreeSequence G e0}, TreeSequenceInitialSegment S U → TreeSequenceInitialSegment U W
        → TreeSequenceInitialSegment S W) → (
    ∀ {S U : TreeSequence G e0}, TreeSequenceInitialSegment S U → S.length = U.length → S = U) → (
    ∀ (a d : ℕ) (hbound : a + d ≤ H.dividerCount + (1 : ℕ)), TreeSequenceInitialSegment (H.stage
        (⟨a,
    have this : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a_1 : ¬a <
        H.dividerCount + (2 : ℕ)) ↦
    by
   omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) (H.stage (⟨a + d,
    have this : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a_1 : ¬a + d <
        H.dividerCount + (2 : ℕ)) ↦
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ))))) → ( H.dividerCount ≠ (0 : ℕ) → A = H.stage q.castSucc) →
        TreeSequenceInitialSegment A T → TreeSequenceInitialSegment A B →
        TreeSequenceInitialSegment Tn A → D.alpha ∈ TreeMissingColors phi B →
    ∀ (m : ℕ), (1 : ℕ) ≤ m →
    ∀ (pv : Fin (m + (1 : ℕ)) → V),
    let R : TreeSequence G e0 := if pv (0 : Fin (m + (1 : ℕ))) = T.vertex D.penultimateVertexIndex
        then Bplus else B; TreeSequenceInitialSegment B R → TreeSequenceInitialSegment R T →
    ∀ (Utree : TreeSequence G e0), TreeSequenceInitialSegment R Utree → Utree.length = R.length +
        m → R.length < Utree.length → (
    ∀ (r : Fin Utree.length), R.length ≤ (↑r : ℕ) → Utree.vertex r.succ ∉ TreeSequenceVertexSet R
        ∧ Sum.inr (Utree.edge r) ∈ TwoColorComponent G phi D.alpha beta (Sum.inl (T.vertex
        D.terminalVertexIndex)) ∧ Sum.inl (Utree.vertex r.succ) ∈ TwoColorComponent G phi D.alpha
        beta (Sum.inl (T.vertex D.terminalVertexIndex)) ∧ (phi (Utree.edge r) = some D.alpha ∨ phi
        (Utree.edge r) = some beta) ∧ G.ends (Utree.edge r) = if (↑r : ℕ) = R.length then s(pv (0
        : Fin (m + (1 : ℕ))), Utree.vertex r.succ) else s(Utree.vertex r.castSucc, Utree.vertex
        r.succ)) → TreeSequenceInitialSegment B Utree → TreeSequenceInitialSegment A Utree →
        TreeSequenceInitialSegment Tn Utree → Tn.length < Utree.length → Utree.vertex (Fin.last
        Utree.length) = T.vertex D.terminalVertexIndex → ModColoring ett phi →
        (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧ TashkinovAugmentationSequence
        phi Tn Utree ∨ (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
        ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
    ∃ (f : E) (seed : TreeSequence G e0), ett.series.data.connectingEdges n = ({ f } : Finset E) ∧
        TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence phi seed Utree) →
    ∃ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), Nonempty
        (HierarchySituationTwoCaseThreeNormalizedData G k e0 P.corresponding.replacementInput T
        P.coloring P.corresponding.replacementETT P.replacementBase P.counterexample
        P.minimumContext)

/-- Dependent contract shared by the hierarchy construction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev HierarchyCaseThreePreparation.helperCaseContinuation1264Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoCaseThreeData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := T.length - A.length;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    let Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let Gamma : Finset (Fin k) := Dnq.biUnion (C.good.gamma q);
    let tailUsed : Finset (Fin k) := ({c : Fin k |
    ∃ (t : Fin T.length), A.length ≤ (↑t : ℕ) ∧ phi (T.edge t) = some c} : Finset (Fin k));
    ∀ beta ∈ TreeMissingColors phi B, (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → phi (T.edge t) ≠ some beta) → (0 : ℕ) <
        H.dividerCount ∧ beta ∉ Dnq ∧ beta ∉ Gamma ∨ H.dividerCount = (0 : ℕ) ∧ beta ∉ Dn ∧ beta ∉
        Gamma ∨ beta ∈ Dnq ∧ Disjoint (C.good.gamma q beta) tailUsed →
    let Bplus : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 :
        ℕ));
    let Q : Set (V ⊕ E) := TwoColorComponent G phi D.alpha beta (Sum.inl (T.vertex
        D.terminalVertexIndex)); B.length = T.length - (2 : ℕ) → Bplus.length = T.length - (1 : ℕ)
        → TreeSequenceInitialSegment B T → TreeSequenceInitialSegment Bplus T →
        TreeSequenceInitialSegment B Bplus → beta ∈ TreeMissingColors phi Bplus → D.alpha ∈
        TreeMissingColors phi Bplus → D.alpha ≠ beta → T.vertex D.terminalVertexIndex ∉
        TreeSequenceVertexSet Bplus → ( H.dividerCount ≠ (0 : ℕ) → A = H.stage q.castSucc) →
        TreeSequenceInitialSegment A T → D.alpha ∈ Gamma → D.alpha ∉ tailUsed →
        ColoredVertexSetElementary G phi (TreeSequenceVertexSet Bplus) → (0 : ℕ) < H.dividerCount
        ∧ D.alpha ∈ TreeMissingColors phi (H.stage q.castSucc) ∨ H.dividerCount = (0 : ℕ) ∧
        D.alpha ∈ TreeMissingColors phi Tn → (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤
        B.length →
    let ia : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T D.alpha;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let va : V := T.vertex ia;
    let vb : V := T.vertex ib;
    let _ : V := T.vertex D.terminalVertexIndex; D.alpha ∈ MissingColors G phi va → beta ∈
        MissingColors G phi vb → T.vertex (HierarchyFirstMissingPosition phi T D.alpha) ∈
        TreeSequenceVertexSet Bplus → T.vertex (HierarchyFirstMissingPosition phi T beta) ∈
        TreeSequenceVertexSet Bplus → TwoColorComponent G phi D.alpha beta (Sum.inl va) =
        TwoColorComponent G phi D.alpha beta (Sum.inl vb) →
    let graph : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi D.alpha beta; (
    ∀ (v : V), D.alpha ∈ MissingColors G phi v ∨ beta ∈ MissingColors G phi v → (graph.neighborSet
        (Sum.inl v)).Subsingleton) → Disjoint Q (TwoColorComponent G phi D.alpha beta (Sum.inl
        va)) →
    ∃ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), Nonempty
        (HierarchySituationTwoCaseThreeNormalizedData G k e0 P.corresponding.replacementInput T
        P.coloring P.corresponding.replacementETT P.replacementBase P.counterexample
        P.minimumContext)

/-- Dependent contract shared by the hierarchy construction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev HierarchyCaseThreePreparation.helperBranch1551Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoCaseThreeData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := T.length - A.length;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    let Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let Gamma : Finset (Fin k) := Dnq.biUnion (C.good.gamma q);
    let tailUsed : Finset (Fin k) := ({c : Fin k |
    ∃ (t : Fin T.length), A.length ≤ (↑t : ℕ) ∧ phi (T.edge t) = some c} : Finset (Fin k));
    ∀ beta ∈ TreeMissingColors phi B, (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → phi (T.edge t) ≠ some beta) → (0 : ℕ) <
        H.dividerCount ∧ beta ∉ Dnq ∧ beta ∉ Gamma ∨ H.dividerCount = (0 : ℕ) ∧ beta ∉ Dn ∧ beta ∉
        Gamma ∨ beta ∈ Dnq ∧ Disjoint (C.good.gamma q beta) tailUsed →
    let Bplus : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 :
        ℕ));
    let _ : Set (V ⊕ E) := TwoColorComponent G phi D.alpha beta (Sum.inl (T.vertex
        D.terminalVertexIndex)); beta ∉ MissingColors G phi (T.vertex D.terminalVertexIndex) →
        B.length = T.length - (2 : ℕ) → Bplus.length = T.length - (1 : ℕ) →
        TreeSequenceInitialSegment B T → TreeSequenceInitialSegment Bplus T →
        TreeSequenceInitialSegment B Bplus → beta ∈ TreeMissingColors phi Bplus → D.alpha ∈
        TreeMissingColors phi Bplus → D.alpha ≠ beta → T.vertex D.terminalVertexIndex ∉
        TreeSequenceVertexSet Bplus → ( H.dividerCount ≠ (0 : ℕ) → A = H.stage q.castSucc) →
        TreeSequenceInitialSegment A T → TreeSequenceInitialSegment Tn A → D.alpha ∈
        TreeMissingColors phi B →
    ∀ (m : ℕ), (1 : ℕ) ≤ m → (
    ∀ (S : TreeSequence G e0) (c : Fin k) (i : Fin (S.length + (1 : ℕ))), c ∈ MissingColors G phi
        (S.vertex i) → (↑(HierarchyFirstMissingPosition phi S c) : ℕ) ≤ (↑i : ℕ)) → (
    ∀ (c : Fin k), (↑(HierarchyFirstMissingPosition phi T c) : ℕ) < T.length → c ∈ MissingColors G
        phi (T.vertex (HierarchyFirstMissingPosition phi T c))) → D.alpha ∈ Gamma → D.alpha ∉
        tailUsed →
    ∃ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), Nonempty
        (HierarchySituationTwoCaseThreeNormalizedData G k e0 P.corresponding.replacementInput T
        P.coloring P.corresponding.replacementETT P.replacementBase P.counterexample
        P.minimumContext)

/-- The dependent type of the shared hierarchy constructor.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev hierarchyExtensionConstructorType.{u_1, u_2} (V : Type u_1) (E : Type u_2) :=
    open scoped Classical in

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
  HierarchySituationTwoCaseThreeData G k e0 input T phi ett base
      C ctx →
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) :=
    Fin.last H.dividerCount;
  let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
  let Tn : TreeSequence G e0 :=
    ett.series.data.tree n.castSucc;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let ell : ℕ := T.length - A.length;
  let B : TreeSequence G e0 :=
    HierarchyFullTailPrefix C (ell - (2 : ℕ));
  B.length = T.length - (2 : ℕ) →
  TreeSequenceInitialSegment B T →
  (
  ∀ {S U W : TreeSequence G e0},
  TreeSequenceInitialSegment S U →
  TreeSequenceInitialSegment U W →
  TreeSequenceInitialSegment S W) →
  (
  ∀ {S U : TreeSequence G e0},
  TreeSequenceInitialSegment S U →
  S.length = U.length →
  S = U) →
  (m : ℕ) →
  (
  Fin (m + (1 : ℕ)) →
  V) →
  (Utree : TreeSequence G e0) →
  TreeSequenceInitialSegment B Utree →
  TreeSequenceInitialSegment A Utree →
  (corrU :
      CorrespondingExtendedTashkinovTree G k
        e0 ett phi Utree) →
  (baseU :
      HierarchyBase corrU.replacementETT
        phi) →
  baseU.core = base.core →
  corrU.replacementETT.series.data.tree
          (Fin.last
              corrU.replacementETT.rounds).castSucc =
        Tn ∧
      corrU.replacementETT.series.data.kind
          (Fin.last
            corrU.replacementETT.rounds) =
        ett.series.data.kind n →
  (
  ∀
     (j :
       Fin
         (H.dividerCount +
           (1 : ℕ))),
  TreeSequenceInitialSegment
    (H.stage j.castSucc) A) →
  A.length < Utree.length →
  let newStage :
  Fin
      (H.dividerCount +
        (2 : ℕ)) →
  TreeSequence G e0 :=
    fun
      (j :
        Fin
          (H.dividerCount +
            (2 : ℕ))) ↦
    if
        (↑j : ℕ) =
          H.dividerCount +
            (1 : ℕ) then
      Utree
    else H.stage j;
  (
  ∀
     (j :
       Fin
         (H.dividerCount +
           (1 : ℕ))),
  newStage j.castSucc =
    H.stage j.castSucc) →
  newStage
        (Fin.last
          (H.dividerCount +
            (1 : ℕ))) =
      Utree →
  (
  ∀
     (j :
       Fin
         (H.dividerCount +
           (2 : ℕ))),
  (↑j : ℕ) ≤
      H.dividerCount →
  newStage j =
    H.stage j) →
  (
  ∀
     (i :
       Fin
         H.dividerCount),
  (↑(H.dividerPosition
          i) :
      ℕ) ≤
    B.length) →
  TashkinovHierarchy
    corrU.replacementETT
    baseU

/-- Color-choice contract for the case-three hierarchy preparation.

Shared separately from its proof to avoid repeating dependent hypotheses.
-/
abbrev hierarchyCaseThreeColorChoiceStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (_ :
        HierarchySituationTwoCaseThreeData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := T.length - A.length;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
    let M0 : Finset (Fin k) := (TreeSequenceVertexSet base.core \ TreeSequenceVertexSet
        Tn).biUnion fun (v : V) ↦ MissingColors G phi v;
    let U : Finset (Fin k) := {c : Fin k |
    ∃ (r : Fin T.length), A.length ≤ (↑r : ℕ) ∧ (↑r : ℕ) < A.length + (ell - (2 : ℕ)) ∧ phi
        (T.edge r) = some c};
    let _ : Finset (Fin k) := (TreeMissingColors phi B \ M0) \ U;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    let Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let Gamma : Finset (Fin k) := Dnq.biUnion (C.good.gamma q);
    let tailUsed : Finset (Fin k) := {c : Fin k |
    ∃ (t : Fin T.length), A.length ≤ (↑t : ℕ) ∧ phi (T.edge t) = some c};
    ∃ beta ∈ TreeMissingColors phi B, (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → phi (T.edge t) ≠ some beta) ∧ ((0 : ℕ) <
        H.dividerCount ∧ beta ∉ Dnq ∧ beta ∉ Gamma ∨ H.dividerCount = (0 : ℕ) ∧ beta ∉ Dn ∧ beta ∉
        Gamma ∨ beta ∈ Dnq ∧ Disjoint (C.good.gamma q beta) tailUsed)

theorem HierarchyCaseThreePreparation.helper_hchoice_125.{u_1, u_2} :
    hierarchyCaseThreeColorChoiceStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q n Tn A ell B M0 U X Dn Dnq Gamma
      tailUsed
  let Tn := ett.series.data.tree n.castSucc
  let M0 := (TreeSequenceVertexSet base.core \
      TreeSequenceVertexSet Tn).biUnion fun v => MissingColors G phi v
  let U := (Finset.univ : Finset (Fin k)).filter fun c =>
    ∃ r : Fin T.length, A.length ≤ r.val ∧
      r.val < A.length + (ell - 2) ∧ phi (T.edge r) = some c
  let X := (TreeMissingColors phi B \ M0) \ U
  have hell : 2 ≤ ell := D.tailAtLeastTwo
  have hT : 2 ≤ T.length := le_trans hell (Nat.sub_le _ _)
  let t1 : Fin T.length := ⟨T.length - 2, by omega⟩
  let t2 : Fin T.length := ⟨T.length - 1, by omega⟩
  let L := (phi (T.edge t1)).toFinset ∪ (phi (T.edge t2)).toFinset
  have hLcard : L.card ≤ 2 := by
    have h1 : (phi (T.edge t1)).toFinset.card ≤ 1 := by
      cases phi (T.edge t1) <;> simp
    have h2 : (phi (T.edge t2)).toFinset.card ≤ 1 := by
      cases phi (T.edge t2) <;> simp
    have h := Finset.card_union_le (phi (T.edge t1)).toFinset
      (phi (T.edge t2)).toFinset
    change L.card ≤ _ at h
    omega
  have hcut : A.length + (ell - 2) = T.length - 2 := by
    dsimp [ell] at hell ⊢
    omega
  have hused : tailUsed ⊆ U ∪ L := by
    intro c hc
    obtain ⟨t, hAt, ht⟩ := (Finset.mem_filter.mp hc).2
    by_cases hsmall : t.val < T.length - 2
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, hAt,
        hcut ▸ hsmall, ht⟩
    · apply Finset.mem_union_right
      have hindices : t = t1 ∨ t = t2 := by
        have hv : t.val = T.length - 2 ∨ t.val = T.length - 1 := by omega
        rcases hv with hv | hv
        · exact Or.inl (Fin.ext hv)
        · exact Or.inr (Fin.ext hv)
      rcases hindices with rfl | rfl
      · exact Finset.mem_union_left _ (by simp [ht])
      · exact Finset.mem_union_right _ (by simp [ht])
  have hunusedTail (c : Fin k) (hU : c ∉ U) (hL : c ∉ L) :
      ∀ t : Fin T.length, A.length ≤ t.val →
        phi (T.edge t) ≠ some c := by
    intro t hAt ht
    have hc : c ∈ tailUsed := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, t, hAt, ht⟩
    rcases Finset.mem_union.mp (hused hc) with hc | hc
    · exact hU hc
    · exact hL hc
  have hprefix : ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet (HierarchyFullTailPrefix C (ell - 1))) := by
    exact HierarchyCounterexamplePenultimateElementary G k e0 input T phi
      ett base C ctx.proper ctx.oneEdgeUncolored ctx.lowerRung
      ctx.fewerDividers ctx.lexicographicMinimality ctx.largeMissingSet
  have hnine := NineN G k e0 input T phi ett C.positive base H C.good
    hprefix ctx.largeMissingSet (ell - 2)
    (show ell - 2 < ell from by omega)
  change 2 * ett.rounds + 11 ≤ X.card ∧
    ((X \ (Gamma ∪ Dnq)).card ≤ 4 →
      ∃ eta : Fin 7 → Fin k, Function.Injective eta ∧
        ∀ h : Fin 7, eta h ∈ Dnq ∧ eta h ∈ TreeMissingColors phi B ∧
          Disjoint (C.good.gamma q (eta h) ∪ {eta h}) U) at hnine
  by_cases hsmall : (X \ (Gamma ∪ Dnq)).card ≤ 4
  · obtain ⟨eta, hinj, heta⟩ := hnine.2 hsmall
    let block := fun h : Fin 7 => C.good.gamma q (eta h) ∪ {eta h}
    have hreserved : Disjoint Gamma Dnq :=
      (GoodHierarchyReservedDisjoint C.good q).2
    have hblocks : ∀ i j : Fin 7, i ≠ j → Disjoint (block i) (block j) := by
      intro i j hij
      have hne : eta i ≠ eta j := fun he => hij (hinj he)
      rw [Finset.disjoint_left]
      intro c hc hd
      simp only [block, Finset.mem_union, Finset.mem_singleton] at hc hd
      rcases hc with hc | hc <;> rcases hd with hd | hd
      · exact Finset.disjoint_left.mp
          (C.good.disjointPairs q _ _ (heta i).1 (heta j).1 hne) hc hd
      · exact Finset.disjoint_left.mp hreserved
          (Finset.mem_biUnion.mpr ⟨eta i, (heta i).1, hc⟩)
          (hd.symm ▸ (heta j).1)
      · exact Finset.disjoint_left.mp hreserved
          (Finset.mem_biUnion.mpr ⟨eta j, (heta j).1, hd⟩)
          (hc.symm ▸ (heta i).1)
      · exact hne (hc.symm.trans hd)
    let bad := (Finset.univ : Finset (Fin 7)).filter fun h =>
      (block h ∩ L).Nonempty
    have hbad : bad.card ≤ L.card := by
      have chooseColor (h : {h : Fin 7 // h ∈ bad}) :
          ∃ c, c ∈ block h.val ∧ c ∈ L := by
        obtain ⟨c, hc⟩ := (Finset.mem_filter.mp h.property).2
        exact ⟨c, (Finset.mem_inter.mp hc).1, (Finset.mem_inter.mp hc).2⟩
      let color : {h : Fin 7 // h ∈ bad} → {c : Fin k // c ∈ L} :=
        fun h => ⟨Classical.choose (chooseColor h),
          (Classical.choose_spec (chooseColor h)).2⟩
      have hcolor : Function.Injective color := by
        intro i j heq
        apply Subtype.ext
        by_contra hne
        have hc := congrArg Subtype.val heq
        change Classical.choose (chooseColor i) =
          Classical.choose (chooseColor j) at hc
        exact Finset.disjoint_left.mp (hblocks i.val j.val hne)
          (Classical.choose_spec (chooseColor i)).1
          (hc.symm ▸ (Classical.choose_spec (chooseColor j)).1)
      simpa only [Fintype.card_coe] using
        Fintype.card_le_of_injective color hcolor
    have hgood : ((Finset.univ : Finset (Fin 7)) \ bad).Nonempty := by
      apply Finset.card_pos.mp
      have h := Finset.le_card_sdiff bad (Finset.univ : Finset (Fin 7))
      simp only [Finset.card_univ, Fintype.card_fin] at h
      omega
    obtain ⟨h, hh⟩ := hgood
    have hnotBad := (Finset.mem_sdiff.mp hh).2
    have hL : Disjoint (block h) L := by
      rw [Finset.disjoint_left]
      intro c hc hl
      exact hnotBad (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, c, Finset.mem_inter.mpr ⟨hc, hl⟩⟩)
    have hfull : Disjoint (block h) tailUsed := by
      rw [Finset.disjoint_left]
      intro c hc ht
      rcases Finset.mem_union.mp (hused ht) with hu | hl
      · exact Finset.disjoint_left.mp (heta h).2.2 hc hu
      · exact Finset.disjoint_left.mp hL hc hl
    refine ⟨eta h, (heta h).2.1, ?_, Or.inr (Or.inr ⟨(heta h).1, ?_⟩)⟩
    · intro t hAt ht
      exact Finset.disjoint_left.mp hfull
        (Finset.mem_union_right _ (Finset.mem_singleton_self _))
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, hAt, ht⟩)
    · exact hfull.mono_left Finset.subset_union_left
  · have hnonempty : ((X \ (Gamma ∪ Dnq)) \ L).Nonempty := by
      apply Finset.card_pos.mp
      have h := Finset.le_card_sdiff L (X \ (Gamma ∪ Dnq))
      omega
    obtain ⟨beta, hbeta⟩ := hnonempty
    obtain ⟨havailable, hL⟩ := Finset.mem_sdiff.mp hbeta
    obtain ⟨hx, hexcluded⟩ := Finset.mem_sdiff.mp havailable
    obtain ⟨hx, hU⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨hmissing, hM0⟩ := Finset.mem_sdiff.mp hx
    have hGamma : beta ∉ Gamma := fun h =>
      hexcluded (Finset.mem_union_left _ h)
    have hDnq : beta ∉ Dnq := fun h =>
      hexcluded (Finset.mem_union_right _ h)
    refine ⟨beta, hmissing, hunusedTail beta hU hL, ?_⟩
    by_cases hzero : H.dividerCount = 0
    · refine Or.inr (Or.inl ⟨hzero, ?_, hGamma⟩)
      intro hDn
      have hnotMissingTn : beta ∉ TreeMissingColors phi Tn := by
        have hn : n.val ≠ 0 := by dsimp [n]; exact Nat.ne_of_gt C.positive
        have hd := hDn
        dsimp only [Dn, TashkinovStoredColors] at hd
        rw [ite_eq_right hn] at hd
        have habsent := (Finset.mem_sdiff.mp hd).2
        have hcolor : ett.series.data.coloring n = phi :=
          ett.generatingColoring.symm
        rw [hcolor] at habsent
        exact habsent
      have hmissingA : beta ∈ TreeMissingColors phi A := by
        by_contra habsent
        exact hDnq (Finset.mem_sdiff.mpr ⟨hDn, habsent⟩)
      have hA : A = base.core := by
        have hq : q = 0 := by apply Fin.ext; simp [q, hzero]
        simp [A, HierarchyStarredStage, hq]
      obtain ⟨v, hv, hm⟩ := Finset.mem_biUnion.mp hmissingA
      by_cases hvn : v ∈ TreeSequenceVertexSet Tn
      · exact hnotMissingTn (Finset.mem_biUnion.mpr ⟨v, hvn, hm⟩)
      · apply hM0
        exact Finset.mem_biUnion.mpr
          ⟨v, Finset.mem_sdiff.mpr ⟨hA ▸ hv, hvn⟩, hm⟩
    · exact Or.inl ⟨Nat.pos_of_ne_zero hzero, hDnq, hGamma⟩

theorem HierarchyCaseThreePreparation.helper_branch_304.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoCaseThreeData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := T.length - A.length;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    let Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let Gamma : Finset (Fin k) := Dnq.biUnion (C.good.gamma q);
    let tailUsed : Finset (Fin k) := {c : Fin k |
    ∃ (t : Fin T.length), A.length ≤ (↑t : ℕ) ∧ phi (T.edge t) = some c};
    ∀ beta ∈ TreeMissingColors phi B, (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → phi (T.edge t) ≠ some beta) → (0 : ℕ) <
        H.dividerCount ∧ beta ∉ Dnq ∧ beta ∉ Gamma ∨ H.dividerCount = (0 : ℕ) ∧ beta ∉ Dn ∧ beta ∉
        Gamma ∨ beta ∈ Dnq ∧ Disjoint (C.good.gamma q beta) tailUsed → beta ∈ MissingColors G phi
        (T.vertex D.terminalVertexIndex) →
    ∃ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), Nonempty
        (HierarchySituationTwoCaseThreeNormalizedData G k e0 P.corresponding.replacementInput T
        P.coloring P.corresponding.replacementETT P.replacementBase P.counterexample
        P.minimumContext) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q n A ell B Dn Dnq Gamma tailUsed beta
      hmissing hunused halternative hterminal
  have hvalid : ∀ i : Fin (ett.rounds + 1),
      IsProperEdgeColoring G (ett.series.data.coloring i) ∧
        IsOneEdgeUncolored (ett.series.data.coloring i) e0 := by
    intro i
    have hs := ett.series.certified i
    cases hs with
    | initial triple _ hcolor =>
      rw [hcolor]
      exact triple.2.2.2
    | SE i _ _ _ _ _ choice _ hcolor =>
      rw [hcolor]
      exact ⟨choice.selectedProper, choice.selectedOneUncolored⟩
    | PE i _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hp hone =>
      exact ⟨hp, hone⟩
    | RE i hp hone _ _ _ hcolor =>
      rw [hcolor]
      exact ⟨hp, hone⟩
  let corr : CorrespondingExtendedTashkinovTree G k e0 ett phi T := {
    replacementInput := input
    replacementSeries := ett.series
    replacementETT := ett
    rungAgreement := rfl
    seriesPresentation := HEq.rfl
    finalGeneratingColoring := ett.generatingColoring
    ladderTreesAgree := fun _ => rfl
    storedColorsAgree := fun _ => rfl
    connectingEdgesAgree := fun _ => rfl
    extensionKindsAgree := fun _ => rfl
    replacementProper := fun i => (hvalid i).1
    replacementOneUncolored := fun i => (hvalid i).2
    replacementStable := by intro i; simp [StableColoring] }
  let P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx := {
    coloring := phi
    corresponding := corr
    maximum := C.maximum
    replacementBase := base
    counterexample := C
    sameGood := ⟨⟨rfl, rfl, HEq.rfl, HEq.rfl, Iff.rfl, fun _ => rfl⟩,
      rfl, fun j => ⟨rfl, fun eta heta => rfl⟩⟩
    minimumContext := ctx }
  obtain ⟨N, hN⟩ := P2752_T2_NormalizedDatum G k e0 input T phi ett base C ctx D
    beta hmissing hunused halternative P (fun _ => rfl)
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩ hterminal
  exact ⟨P, ⟨N⟩⟩

/-- Typed data construction shared by the hierarchy construction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
noncomputable abbrev HierarchyCaseThreePreparation.helperK553.{u_1, u_2} :
  ∀ {V : Type u_1} {E : Type u_2},
  hierarchyExtensionConstructorType V E := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q n Tn A ell B hlenB hBT segTrans
      equalTrees m pv Utree hBU hAU corrU baseU hcoreU terminalData ordinaryToA hAUstrict
      newStage stageOld stageLast stageAt divBound
  exact {
    dividerCount := H.dividerCount
    stage := newStage
    baseStage := by
      rw [show newStage 0 = H.stage 0 by simp [newStage], H.baseStage]
      exact terminalData.1.symm
    terminalStage := stageLast
    nested := by
      intro j
      rw [stageOld j]
      by_cases hj : j.val = H.dividerCount
      · have he : j = q := Fin.ext (by simpa [q] using hj)
        subst j
        rw [show q.succ = Fin.last (H.dividerCount + 1) from Fin.ext rfl, stageLast]
        exact segTrans (ordinaryToA q) hAU
      · rw [stageAt j.succ (by have := j.isLt; change j.val + 1 ≤ _; omega)]
        exact H.nested j
    strict := by
      intro j
      rw [stageOld j]
      by_cases hj : j.val = H.dividerCount
      · have he : j = q := Fin.ext (by simpa [q] using hj)
        subst j
        rw [show q.succ = Fin.last (H.dividerCount + 1) from Fin.ext rfl, stageLast]
        exact lt_of_le_of_lt (ordinaryToA q).1 hAUstrict
      · rw [stageAt j.succ (by have := j.isLt; change j.val + 1 ≤ _; omega)]
        exact H.strict j
    dividerPosition := fun i => ⟨(H.dividerPosition i).val, by
      have hb := divBound i
      have hbu := hBU.1
      omega⟩
    dividerPositive := H.dividerPositive
    dividerIncreasing := H.dividerIncreasing
    dividerStage := by
      intro i
      clear * - H i stageAt divBound hBU hBT equalTrees
      rw [stageAt ⟨i.val + 1, by omega⟩
        (by change i.val + 1 ≤ H.dividerCount; have := i.isLt; omega), H.dividerStage i]
      have hpref : TreeSequencePrefix Utree (H.dividerPosition i).val (H.dividerPositive i)
          (by have := divBound i; have := hBU.1; omega) =
          TreeSequencePrefix T (H.dividerPosition i).val (H.dividerPositive i)
            (Nat.le_of_lt_succ (H.dividerPosition i).isLt) := by
        apply equalTrees
        · refine ⟨le_rfl, ?_, ?_⟩
          · intro x
            have hu := hBU.2.1 (Fin.castLE (Nat.succ_le_succ (divBound i)) x)
            have ht := hBT.2.1 (Fin.castLE (Nat.succ_le_succ (divBound i)) x)
            exact ht.trans hu.symm
          · intro x
            have hu := hBU.2.2 (Fin.castLE (divBound i) x)
            have ht := hBT.2.2 (Fin.castLE (divBound i) x)
            exact ht.trans hu.symm
        · rfl
      exact hpref.symm
    coreInsideFirst := by
      rw [hcoreU]
      by_cases hz : H.dividerCount = 0
      · have hq : q = 0 := Fin.ext (by simp [q, hz])
        have hA : A = base.core := by simp [A, HierarchyStarredStage, hq]
        rw [show newStage ⟨1, by omega⟩ = Utree by simp [newStage, hz]]
        exact hA ▸ hAU
      · rw [stageAt ⟨1, by omega⟩ (Nat.one_le_iff_ne_zero.mpr hz)]
        exact H.coreInsideFirst }

theorem HierarchyCaseThreePreparation.helper_pathShort_734.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoCaseThreeData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := T.length - A.length;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
    ∀ (beta : Fin k),
    let Bplus : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 :
        ℕ));
    ∀ (hlenB : B.length = T.length - (2 : ℕ)), Bplus.length = T.length - (1 : ℕ) →
    ∀ (hBT : TreeSequenceInitialSegment B T), TreeSequenceInitialSegment Bplus T →
    ∀ (segTrans :
    ∀ {S U W : TreeSequence G e0}, TreeSequenceInitialSegment S U → TreeSequenceInitialSegment U W
        → TreeSequenceInitialSegment S W) (equalTrees :
    ∀ {S U : TreeSequence G e0}, TreeSequenceInitialSegment S U → S.length = U.length → S = U),
        TreeSequenceInitialSegment A T →
    ∀ (m : ℕ), (1 : ℕ) ≤ m →
    ∀ (pv : Fin (m + (1 : ℕ)) → V),
    let R : TreeSequence G e0 := if pv (0 : Fin (m + (1 : ℕ))) = T.vertex D.penultimateVertexIndex
        then Bplus else B; TreeSequenceInitialSegment B R →
    ∀ (Utree : TreeSequence G e0), TreeSequenceInitialSegment R Utree → Utree.length = R.length +
        m → R.length < Utree.length → (
    ∀ (r : Fin Utree.length), R.length ≤ (↑r : ℕ) → Utree.vertex r.succ ∉ TreeSequenceVertexSet R
        ∧ Sum.inr (Utree.edge r) ∈ TwoColorComponent G phi D.alpha beta (Sum.inl (T.vertex
        D.terminalVertexIndex)) ∧ Sum.inl (Utree.vertex r.succ) ∈ TwoColorComponent G phi D.alpha
        beta (Sum.inl (T.vertex D.terminalVertexIndex)) ∧ (phi (Utree.edge r) = some D.alpha ∨ phi
        (Utree.edge r) = some beta) ∧ G.ends (Utree.edge r) = if (↑r : ℕ) = R.length then s(pv (0
        : Fin (m + (1 : ℕ))), Utree.vertex r.succ) else s(Utree.vertex r.castSucc, Utree.vertex
        r.succ)) →
    ∀ (hBU : TreeSequenceInitialSegment B Utree) (hAU : TreeSequenceInitialSegment A Utree) (corrU
        : CorrespondingExtendedTashkinovTree G k e0 ett phi Utree) (baseU : HierarchyBase
        corrU.replacementETT phi) (hcoreU : baseU.core = base.core) (terminalData :
        corrU.replacementETT.series.data.tree (Fin.last corrU.replacementETT.rounds).castSucc = Tn
        ∧ corrU.replacementETT.series.data.kind (Fin.last corrU.replacementETT.rounds) =
        ett.series.data.kind n) (ordinaryToA :
    ∀ (j : Fin (H.dividerCount + (1 : ℕ))), TreeSequenceInitialSegment (H.stage j.castSucc) A)
        (hAUstrict : A.length < Utree.length),
    let newStage : Fin (H.dividerCount + (2 : ℕ)) → TreeSequence G e0 := fun (j : Fin
        (H.dividerCount + (2 : ℕ))) ↦ if (↑j : ℕ) = H.dividerCount + (1 : ℕ) then Utree else
        H.stage j;
    ∀ (stageOld :
    ∀ (j : Fin (H.dividerCount + (1 : ℕ))), newStage j.castSucc = H.stage j.castSucc) (stageLast :
        newStage (Fin.last (H.dividerCount + (1 : ℕ))) = Utree) (stageAt :
    ∀ (j : Fin (H.dividerCount + (2 : ℕ))), (↑j : ℕ) ≤ H.dividerCount → newStage j = H.stage j)
        (divBound :
    ∀ (i : Fin H.dividerCount), (↑(H.dividerPosition i) : ℕ) ≤ B.length),
    let K : TashkinovHierarchy corrU.replacementETT baseU :=
        HierarchyCaseThreePreparation.helperK553 G k e0 input T phi ett base C ctx D hlenB hBT
        (fun {_ _ _ : TreeSequence G e0} ↦ segTrans) (fun {_ _ : TreeSequence G e0} ↦ equalTrees)
        m pv Utree hBU hAU corrU baseU hcoreU terminalData ordinaryToA hAUstrict stageOld
        stageLast stageAt divBound; (
    ∀ (j : Fin (H.dividerCount + (1 : ℕ))), HierarchyStarredStage K j = HierarchyStarredStage H j)
        → HierarchyPathNumber K < HierarchyPathNumber H := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q n Tn A ell B beta Bplus hlenB
      hlenPlus hBT hplusT segTrans equalTrees hAT m hm pv R hBR Utree hRU hUlen hRUstrict hnew
      hBU hAU corrU baseU hcoreU terminalData ordinaryToA hAUstrict newStage stageOld stageLast
      stageAt divBound K starredEq
  have hell : 2 ≤ ell := D.tailAtLeastTwo
  have hsum : A.length + ell = T.length := by dsimp [ell]; have := hAT.1; omega
  let candidates := (Finset.Icc 1 (Utree.length - A.length)).filter fun i =>
    ∀ r : Fin Utree.length, A.length + i ≤ r.val →
      G.ends (Utree.edge r) = s(Utree.vertex r.castSucc, Utree.vertex r.succ)
  have hcand : ell - 1 ∈ candidates := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨by omega, ?_⟩, ?_⟩
    · have hbr := hBR.1
      omega
    · intro r hr
      by_cases hp : pv 0 = T.vertex D.penultimateVertexIndex
      · have hR : R = Bplus := ite_eq_left hp
        have hRlen : R.length = T.length - 1 := hR ▸ hlenPlus
        have hge : R.length ≤ r.val := by omega
        rw [(hnew r hge).2.2.2.2]
        split
        · rename_i he
          have hv : Utree.vertex r.castSucc = pv 0 := by
            have h := hRU.2.1 (Fin.last R.length)
            have hi : Fin.castLE (Nat.succ_le_succ hRU.1) (Fin.last R.length) = r.castSucc :=
              Fin.ext (by change R.length = r.val; omega)
            rw [hi, hR, ← hplusT.2.1 (Fin.last Bplus.length)] at h
            have hj : Fin.castLE (Nat.succ_le_succ hplusT.1) (Fin.last Bplus.length) =
                D.penultimateVertexIndex := Fin.ext (by
              change Bplus.length = D.penultimateVertexIndex.val
              have := D.penultimateVertexPosition
              omega)
            rw [hj] at h
            exact h.trans hp.symm
          rw [hv]
        · rfl
      · have hR : R = B := ite_eq_right hp
        have hRlen : R.length = T.length - 2 := hR ▸ hlenB
        have hge : R.length ≤ r.val := by omega
        rw [(hnew r hge).2.2.2.2, ite_eq_right (by omega : r.val ≠ R.length)]
  have hnonempty : candidates.Nonempty := ⟨ell - 1, hcand⟩
  have hpath : HierarchyPathNumber K = candidates.min' hnonempty := by
    unfold HierarchyPathNumber
    dsimp only
    rw [starredEq q]
    change (if h : candidates.Nonempty then candidates.min' h else _) = _
    rw [dite_eq_left hnonempty]
  rw [hpath, D.pathNumberFull]
  have hle := Finset.min'_le candidates (ell - 1) hcand
  change candidates.min' hnonempty < ell
  omega

private theorem helper_continuation_1119.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoCaseThreeData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := T.length - A.length;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    let Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let Gamma : Finset (Fin k) := Dnq.biUnion (C.good.gamma q);
    let tailUsed : Finset (Fin k) := ({c : Fin k |
    ∃ (t : Fin T.length), A.length ≤ (↑t : ℕ) ∧ phi (T.edge t) = some c} : Finset (Fin k));
    ∀ (beta : Fin k) (_ : beta ∈ TreeMissingColors phi B) (_ :
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → phi (T.edge t) ≠ some beta) (_ : (0 : ℕ) <
        H.dividerCount ∧ beta ∉ Dnq ∧ beta ∉ Gamma ∨ H.dividerCount = (0 : ℕ) ∧ beta ∉ Dn ∧ beta ∉
        Gamma ∨ beta ∈ Dnq ∧ Disjoint (C.good.gamma q beta) tailUsed),
    let Bplus : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 :
        ℕ));
    let _ : Set (V ⊕ E) := TwoColorComponent G phi D.alpha beta (Sum.inl (T.vertex
        D.terminalVertexIndex));
    ∀ (_ : TreeSequenceInitialSegment B T) (_ : TreeSequenceInitialSegment Bplus T) (_ :
        TreeSequenceInitialSegment B Bplus) (_ : D.alpha ≠ beta) (_ : T.vertex
        D.terminalVertexIndex ∉ TreeSequenceVertexSet Bplus) (_ : TreeSequenceInitialSegment A T),
    let yp : V := T.vertex D.terminalVertexIndex;
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G phi D.alpha beta (Sum.inl yp);
    ∀ (_ :
    have C_1 : Set (V ⊕ E) := TwoColorComponent G phi D.alpha beta (Sum.inl yp);
    have phi' : PartialEdgeColoring E k := TwoColorComponentSwap G phi D.alpha beta (Sum.inl yp);
        (
    ∀ (v : V), Sum.inl v ∉ C_1 → MissingColors G phi' v = MissingColors G phi v) ∧ (
    ∀ (v : V), Sum.inl v ∈ C_1 → D.alpha ∈ MissingColors G phi v → beta ∈ MissingColors G phi' v)
        ∧ (
    ∀ (v : V), Sum.inl v ∈ C_1 → beta ∈ MissingColors G phi v → D.alpha ∈ MissingColors G phi' v)
        ∧
    ∀ (v : V) (c : Fin k), c ≠ D.alpha → c ≠ beta → (c ∈ MissingColors G phi' v ↔ c ∈
        MissingColors G phi v)) (_ :
    ∀ v ∈ TreeSequenceVertexSet Bplus, MissingColors G sigma v = MissingColors G phi v) (_ :
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → sigma (T.edge t) = phi (T.edge t)) (corrT :
        CorrespondingExtendedTashkinovTree G k e0 ett sigma T) (_ : MaximumProperty
        corrT.replacementETT) (baseT : HierarchyBase corrT.replacementETT sigma) (KT :
        TashkinovHierarchy corrT.replacementETT baseT) (goodT : GoodHierarchy KT) (_ :
        SameGoodHierarchy C.good goodT) (_ :
    ∀ (t : Fin A.length), sigma (A.edge t) = phi (A.edge t)),
    ∃ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), Nonempty
        (HierarchySituationTwoCaseThreeNormalizedData G k e0 P.corresponding.replacementInput T
        P.coloring P.corresponding.replacementETT P.replacementBase P.counterexample
        P.minimumContext) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q n A ell B Dn Dnq Gamma tailUsed beta
      hmissing hunused halternative Bplus Q hBT hplusT hBBplus hne hterminalOutside hAT yp sigma
      behavior missingPenultimate tailFixed corrT maximumT baseT KT goodT sameT fixedA
  have fixedT : ∀ t : Fin T.length, sigma (T.edge t) = phi (T.edge t) := by
    intro t
    by_cases ht : t.val < A.length
    · let tA : Fin A.length := ⟨t.val, ht⟩
      have he : Fin.castLE hAT.1 tA = t := Fin.ext rfl
      rw [← he, hAT.2.2 tA]
      exact fixedA tA
    · exact tailFixed t (by omega)
  have hterminalNew : beta ∈ MissingColors G sigma yp :=
    behavior.2.1 yp (show Sum.inl yp ∈ Q from rfl) D.alphaMissingTerminal
  have notElementary : ¬ ColoredVertexSetElementary G sigma (TreeSequenceVertexSet T) := by
    obtain ⟨v, hv, hm⟩ := Finset.mem_biUnion.mp hmissing
    have hvPlus := TreeSequenceInitialSegmentVertexSetSubset hBBplus hv
    have hmissingNew : beta ∈ MissingColors G sigma v := by
      rw [missingPenultimate v hvPlus]
      exact hm
    have hvT := TreeSequenceInitialSegmentVertexSetSubset hBT hv
    have hyT : yp ∈ TreeSequenceVertexSet T := by simp [yp, TreeSequenceVertexSet]
    have hne : v ≠ yp := by
      intro he
      apply hterminalOutside
      change yp ∈ TreeSequenceVertexSet Bplus
      rw [← he]
      exact hvPlus
    intro he
    exact Finset.disjoint_left.mp (he hvT hyT hne) hmissingNew hterminalNew
  let CT : HierarchyCounterexample baseT := {
    positive := by rw [corrT.rungAgreement]; exact C.positive
    hierarchy := KT
    good := goodT
    maximum := maximumT
    notElementary := notElementary }
  obtain ⟨contextT⟩ := P2752_T2_MinimumContextTransport G k e0 input T phi sigma
    ett base C ctx corrT baseT CT sameT
  let P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx := {
    coloring := sigma
    corresponding := corrT
    maximum := maximumT
    replacementBase := baseT
    counterexample := CT
    sameGood := sameT
    minimumContext := contextT }
  obtain ⟨N, hN⟩ := P2752_T2_NormalizedDatum G k e0 input T phi ett base C ctx D
    beta hmissing hunused halternative P fixedT
    ⟨(fun t _ => by rw [← hplusT.2.2 t]; exact fixedT _), missingPenultimate⟩ hterminalNew
  exact ⟨P, ⟨N⟩⟩

theorem HierarchyCaseThreePreparation.helper_caseContinuation_1264.{u_1, u_2} :
    HierarchyCaseThreePreparation.helperCaseContinuation1264Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q n Tn A ell B Dn Dnq Gamma tailUsed
      beta hmissing hunused halternative Bplus Q hlenB hlenPlus hBT hplusT hBBplus
      hbetaMissingPlus halphaMissingPlus hne hterminalOutside lastPositive hAT haGamma haUsed
      hprefixElementary hcase hbFirstB ia ib va vb yp hma hmb hva hvb hsameComponent graph leaf
      disjointFirst
  let sigma := TwoColorComponentSwap G phi D.alpha beta (Sum.inl yp)
  have behavior := TwoColorComponentSwapMissingBehavior G phi D.alpha beta hne ctx.proper
      (Sum.inl yp)
  have haOutsideQ : Sum.inl va ∉ Q := fun ha =>
    Set.disjoint_left.mp disjointFirst ha (show Sum.inl va ∈
      TwoColorComponent G phi D.alpha beta (Sum.inl va) from rfl)
  have hbOutsideQ : Sum.inl vb ∉ Q := by
    intro hb
    apply Set.disjoint_left.mp disjointFirst hb
    rw [hsameComponent]
    rfl
  have missingPenultimate : ∀ v, v ∈ TreeSequenceVertexSet Bplus →
      MissingColors G sigma v = MissingColors G phi v := by
    intro v hv
    by_cases hvQ : Sum.inl v ∈ Q
    · have hna : D.alpha ∉ MissingColors G phi v := by
        intro hm
        have he : v = va := by
          by_contra hne
          exact Finset.disjoint_left.mp (hprefixElementary hv hva hne) hm hma
        exact haOutsideQ (he ▸ hvQ)
      have hnb : beta ∉ MissingColors G phi v := by
        intro hm
        have he : v = vb := by
          by_contra hne
          exact Finset.disjoint_left.mp (hprefixElementary hv hvb hne) hm hmb
        exact hbOutsideQ (he ▸ hvQ)
      have edgeInQ (f : E) (hf : Incident G v f)
          (hc : phi f = some D.alpha ∨ phi f = some beta) : Sum.inr f ∈ Q := by
        have hadj : graph.Adj (Sum.inr f) (Sum.inl v) := ⟨hf, hc⟩
        exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans hvQ
      have hnewA : D.alpha ∉ MissingColors G sigma v := by
        have hpresent : beta ∈ PresentColors G phi v := by simpa [MissingColors] using hnb
        obtain ⟨f, hf, hc⟩ := (Finset.mem_filter.mp hpresent).2
        have hfQ := edgeInQ f hf (Or.inr hc)
        have hfA : phi f ≠ some D.alpha := fun h => hne (Option.some.inj (h.symm.trans hc))
        have hnew : sigma f = some D.alpha := by
          change (if Sum.inr f ∈ Q then
            if phi f = some D.alpha then some beta else
              if phi f = some beta then some D.alpha else phi f
            else phi f) = _
          rw [ite_eq_left hfQ, ite_eq_right hfA, ite_eq_left hc]
        intro hm
        exact (Finset.mem_sdiff.mp hm).2
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, f, hf, hnew⟩)
      have hnewB : beta ∉ MissingColors G sigma v := by
        have hpresent : D.alpha ∈ PresentColors G phi v := by simpa [MissingColors] using hna
        obtain ⟨f, hf, hc⟩ := (Finset.mem_filter.mp hpresent).2
        have hfQ := edgeInQ f hf (Or.inl hc)
        have hnew : sigma f = some beta := by
          change (if Sum.inr f ∈ Q then
            if phi f = some D.alpha then some beta else
              if phi f = some beta then some D.alpha else phi f
            else phi f) = _
          rw [ite_eq_left hfQ, ite_eq_left hc]
        intro hm
        exact (Finset.mem_sdiff.mp hm).2
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, f, hf, hnew⟩)
      apply Finset.ext
      intro c
      by_cases hca : c = D.alpha
      · subst c
        exact ⟨fun h => (hnewA h).elim, fun h => (hna h).elim⟩
      · by_cases hcb : c = beta
        · subst c
          exact ⟨fun h => (hnewB h).elim, fun h => (hnb h).elim⟩
        · exact behavior.2.2.2 v c hca hcb
    · exact behavior.1 v hvQ
  have storedFirst : ∀ eta, eta ∈ Dnq →
      HierarchyFirstMissingPosition sigma T eta = HierarchyFirstMissingPosition phi T eta := by
    intro eta heta
    have hneA : eta ≠ D.alpha := by
      intro he
      exact Finset.disjoint_left.mp (GoodHierarchyReservedDisjoint C.good q).2 haGamma (he ▸ heta)
    by_cases hneB : eta = beta
    · subst eta
      have hfirstPrefix : HierarchyFirstMissingPosition sigma Bplus beta =
          HierarchyFirstMissingPosition phi Bplus beta := by
        have hfilters :
            ((Finset.univ : Finset (Fin (Bplus.length + 1))).filter fun i =>
              beta ∈ MissingColors G sigma (Bplus.vertex i)) =
            ((Finset.univ : Finset (Fin (Bplus.length + 1))).filter fun i =>
              beta ∈ MissingColors G phi (Bplus.vertex i)) := by
          apply Finset.filter_congr
          intro i _
          rw [missingPenultimate (Bplus.vertex i) (by simp [TreeSequenceVertexSet])]
        unfold HierarchyFirstMissingPosition
        rw [hfilters]
      have hcutS := HierarchyFirstMissingPositionPrefixCutoff sigma Bplus T hplusT beta
          Bplus.length le_rfl
      have hcutP := HierarchyFirstMissingPositionPrefixCutoff phi Bplus T hplusT beta
          Bplus.length le_rfl
      rw [hfirstPrefix] at hcutS
      have hbLt : ib.val < Bplus.length := by
        have hlength : B.length < Bplus.length := by
          rw [hlenB, hlenPlus]
          have hp : 2 ≤ T.length := le_trans D.tailAtLeastTwo (Nat.sub_le _ _)
          clear * - hp
          omega
        exact lt_of_le_of_lt hbFirstB hlength
      apply Fin.ext
      change (HierarchyFirstMissingPosition sigma T beta).val = ib.val
      change min (HierarchyFirstMissingPosition phi Bplus beta).val Bplus.length =
        min ib.val Bplus.length at hcutP
      clear * - hcutS hcutP hbLt
      omega
    · have hfilters :
          ((Finset.univ : Finset (Fin (T.length + 1))).filter fun i =>
            eta ∈ MissingColors G sigma (T.vertex i)) =
          ((Finset.univ : Finset (Fin (T.length + 1))).filter fun i =>
            eta ∈ MissingColors G phi (T.vertex i)) := by
        apply Finset.filter_congr
        intro i _
        exact behavior.2.2.2 _ eta hneA hneB
      unfold HierarchyFirstMissingPosition
      rw [hfilters]
  have tailFixed : ∀ t : Fin T.length, A.length ≤ t.val →
      sigma (T.edge t) = phi (T.edge t) := by
    intro t ht
    have hna : phi (T.edge t) ≠ some D.alpha := fun hc =>
      haUsed (Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, ht, hc⟩)
    have hnb := hunused t ht
    unfold sigma TwoColorComponentSwap
    split <;> simp only []
  have pathQ : TwoColorPathComponent G phi D.alpha beta (Sum.inl yp) := by
    exact ⟨hne, Sum.inl yp, show Sum.inl yp ∈ Q from rfl,
      leaf yp (Or.inl D.alphaMissingTerminal)⟩
  obtain ⟨weak, modSigma, _, _, corrT, maximumT, baseT, KT, goodT, sameT⟩ :=
    StableChangeCasesOneTwoFullTail G k e0 input T phi ett base C ctx D.alpha beta hne
      ⟨halphaMissingPlus, hbetaMissingPlus⟩ (Sum.inl yp) pathQ sigma rfl
      (by rcases hcase with h | h
          · exact Or.inl h
          · exact Or.inr ⟨h.1, Or.inl h.2⟩)
      disjointFirst tailFixed missingPenultimate storedFirst
  have fixedA : ∀ t : Fin A.length, sigma (A.edge t) = phi (A.edge t) := by
    change HierarchyWeaklyStable H q sigma at weak
    by_cases hz : H.dividerCount = 0
    · have hq : q = 0 := Fin.ext (by simp [q, hz])
      have hA : A = base.core := by simp [A, HierarchyStarredStage, hq]
      rw [hA]
      apply P2813_T1_BaseDisplayedEdges G k e0 input T phi ett base sigma
        ctx.oneEdgeUncolored modSigma.2.1
      rw [hq] at weak
      exact weak
    · let i : Fin H.dividerCount := ⟨H.dividerCount - 1, by omega⟩
      have hq : q = i.succ := Fin.ext (by dsimp [q, i]; omega)
      have hinv : TreeColoringInvariant (H.stage q.castSucc) phi sigma := by
        rw [hq] at weak ⊢
        exact weak.2
      rw [lastPositive hz]
      intro t
      by_cases ht : t.val = 0
      · have he : t = ⟨0, (H.stage q.castSucc).positive⟩ := Fin.ext ht
        rw [he, (H.stage q.castSucc).first_edge, modSigma.2.1.1, ctx.oneEdgeUncolored.1]
      · exact hinv.1 t (by omega)
  exact @helper_continuation_1119 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@beta)
      (@hmissing) (@hunused) (@halternative) (@hBT) (@hplusT) (@hBBplus) (@hne)
      (@hterminalOutside) (@hAT) (@behavior) (@missingPenultimate) (@tailFixed) (@corrT)
      (@maximumT) (@baseT) (@KT) (@goodT) (@sameT) (@fixedA)
theorem HierarchyCaseThreePreparation.helper_branch_1316.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoCaseThreeData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := T.length - A.length;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
    let Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let tailUsed : Finset (Fin k) := ({c : Fin k |
    ∃ (t : Fin T.length), A.length ≤ (↑t : ℕ) ∧ phi (T.edge t) = some c} : Finset (Fin k));
    ∀ (beta : Fin k),
    let Bplus : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 :
        ℕ)); B.length = T.length - (2 : ℕ) → Bplus.length = T.length - (1 : ℕ) →
        TreeSequenceInitialSegment B T → D.alpha ≠ beta → (
    ∀ {S U W : TreeSequence G e0}, TreeSequenceInitialSegment S U → TreeSequenceInitialSegment U W
        → TreeSequenceInitialSegment S W) → (
    ∀ {S U : TreeSequence G e0}, TreeSequenceInitialSegment S U → S.length = U.length → S = U) → (
        H.dividerCount ≠ (0 : ℕ) → A = H.stage q.castSucc) →
    ∀ (m : ℕ) (_ : Fin (m + (1 : ℕ)) → V) (Utree : TreeSequence G e0), TreeSequenceInitialSegment
        B Utree → TreeSequenceInitialSegment A Utree →
    ∀ (corrU : CorrespondingExtendedTashkinovTree G k e0 ett phi Utree) (baseU : HierarchyBase
        corrU.replacementETT phi), baseU.core = base.core → corrU.replacementETT.series.data.tree
        (Fin.last corrU.replacementETT.rounds).castSucc = Tn ∧
        corrU.replacementETT.series.data.kind (Fin.last corrU.replacementETT.rounds) =
        ett.series.data.kind n → (
    ∀ (j : Fin (H.dividerCount + (1 : ℕ))), TreeSequenceInitialSegment (H.stage j.castSucc) A) →
        A.length < Utree.length →
    let newStage : Fin (H.dividerCount + (2 : ℕ)) → TreeSequence G e0 := fun (j : Fin
        (H.dividerCount + (2 : ℕ))) ↦ if (↑j : ℕ) = H.dividerCount + (1 : ℕ) then Utree else
        H.stage j; (
    ∀ (j : Fin (H.dividerCount + (1 : ℕ))), newStage j.castSucc = H.stage j.castSucc) → newStage
        (Fin.last (H.dividerCount + (1 : ℕ))) = Utree → (
    ∀ (j : Fin (H.dividerCount + (2 : ℕ))), (↑j : ℕ) ≤ H.dividerCount → newStage j = H.stage j) →
        (
    ∀ (i : Fin H.dividerCount), (↑(H.dividerPosition i) : ℕ) ≤ B.length) → ( (
    ∀ eta ∈ Dnq, D.alpha ∈ C.good.gamma q eta → (↑(HierarchyFirstMissingPosition phi T eta) : ℕ) ≤
        B.length) → False) → D.alpha ∈ tailUsed →
    ∃ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), Nonempty
        (HierarchySituationTwoCaseThreeNormalizedData G k e0 P.corresponding.replacementInput T
        P.coloring P.corresponding.replacementETT P.replacementBase P.counterexample
        P.minimumContext) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q n Tn A ell B Dnq tailUsed beta Bplus
      hlenB hlenPlus hBT hne segTrans equalTrees lastPositive m pv Utree hBU hAU corrU baseU
      hcoreU terminalData ordinaryToA hAUstrict newStage stageOld stageLast stageAt divBound
      shorteningContradiction haUsed
  have alphaNotLast : phi (T.edge D.lastEdgeIndex) ≠ some D.alpha := by
    intro hc
    have hnotPresent : D.alpha ∉ PresentColors G phi (T.vertex D.terminalVertexIndex) :=
      (Finset.mem_sdiff.mp D.alphaMissingTerminal).2
    apply hnotPresent
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨T.edge D.lastEdgeIndex, ?_, hc⟩
    obtain ⟨i, he⟩ := T.attaches D.lastEdgeIndex
    have hi : D.lastEdgeIndex.succ = D.terminalVertexIndex := Fin.ext (by
      change D.lastEdgeIndex.val + 1 = D.terminalVertexIndex.val
      have := D.lastEdgePosition
      have := D.terminalVertexPosition
      omega)
    change T.vertex D.terminalVertexIndex ∈ G.ends (T.edge D.lastEdgeIndex)
    rw [he, hi]
    exact Sym2.mem_mk_left _ _
  obtain ⟨t, htA, htcolor⟩ := (Finset.mem_filter.mp haUsed).2
  have htB : t.val ≤ B.length := by
    by_contra hn
    have htlast : t = D.lastEdgeIndex := Fin.ext (by
      have := t.isLt
      have := D.lastEdgePosition
      rw [hlenB] at hn
      omega)
    exact alphaNotLast (htlast ▸ htcolor)
  apply False.elim
  apply shorteningContradiction
  intro eta heta hgamma
  have hfirst : (HierarchyFirstMissingPosition phi T eta).val ≤ t.val := by
    by_contra hn
    have hseg : D.alpha ∈ HierarchySegmentColors H q eta := by
      unfold HierarchySegmentColors
      dsimp only
      rw [show q.succ = Fin.last (H.dividerCount + 1) from Fin.ext rfl, H.terminalStage]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, htA,
        by have := t.isLt; omega, htcolor⟩
    exact (Finset.mem_sdiff.mp (C.good.avoidance q eta heta hgamma)).2 hseg
  exact hfirst.trans htB

theorem HierarchyCaseThreePreparation.helper_terminalAvoid_1779.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoCaseThreeData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := T.length - A.length;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
    let Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let Gamma : Finset (Fin k) := Dnq.biUnion (C.good.gamma q);
    ∀ (beta : Fin k),
    let Bplus : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 :
        ℕ));
    ∀ (hlenB : B.length = T.length - (2 : ℕ)) (hBT : TreeSequenceInitialSegment B T) (segTrans :
    ∀ {S U W : TreeSequence G e0}, TreeSequenceInitialSegment S U → TreeSequenceInitialSegment U W
        → TreeSequenceInitialSegment S W) (equalTrees :
    ∀ {S U : TreeSequence G e0}, TreeSequenceInitialSegment S U → S.length = U.length → S = U) (m
        : ℕ) (pv : Fin (m + (1 : ℕ)) → V),
    let R : TreeSequence G e0 := if pv (0 : Fin (m + (1 : ℕ))) = T.vertex D.penultimateVertexIndex
        then Bplus else B; TreeSequenceInitialSegment B R → TreeSequenceInitialSegment R T →
    ∀ (Utree : TreeSequence G e0), TreeSequenceInitialSegment R Utree → (
    ∀ (r : Fin Utree.length), R.length ≤ (↑r : ℕ) → Utree.vertex r.succ ∉ TreeSequenceVertexSet R
        ∧ Sum.inr (Utree.edge r) ∈ TwoColorComponent G phi D.alpha beta (Sum.inl (T.vertex
        D.terminalVertexIndex)) ∧ Sum.inl (Utree.vertex r.succ) ∈ TwoColorComponent G phi D.alpha
        beta (Sum.inl (T.vertex D.terminalVertexIndex)) ∧ (phi (Utree.edge r) = some D.alpha ∨ phi
        (Utree.edge r) = some beta) ∧ G.ends (Utree.edge r) = if (↑r : ℕ) = R.length then s(pv (0
        : Fin (m + (1 : ℕ))), Utree.vertex r.succ) else s(Utree.vertex r.castSucc, Utree.vertex
        r.succ)) →
    ∀ (hBU : TreeSequenceInitialSegment B Utree) (hAU : TreeSequenceInitialSegment A Utree) (corrU
        : CorrespondingExtendedTashkinovTree G k e0 ett phi Utree) (baseU : HierarchyBase
        corrU.replacementETT phi) (hcoreU : baseU.core = base.core) (terminalData :
        corrU.replacementETT.series.data.tree (Fin.last corrU.replacementETT.rounds).castSucc = Tn
        ∧ corrU.replacementETT.series.data.kind (Fin.last corrU.replacementETT.rounds) =
        ett.series.data.kind n) (ordinaryToA :
    ∀ (j : Fin (H.dividerCount + (1 : ℕ))), TreeSequenceInitialSegment (H.stage j.castSucc) A)
        (hAUstrict : A.length < Utree.length),
    let newStage : Fin (H.dividerCount + (2 : ℕ)) → TreeSequence G e0 := fun (j : Fin
        (H.dividerCount + (2 : ℕ))) ↦ if (↑j : ℕ) = H.dividerCount + (1 : ℕ) then Utree else
        H.stage j;
    ∀ (stageOld :
    ∀ (j : Fin (H.dividerCount + (1 : ℕ))), newStage j.castSucc = H.stage j.castSucc) (stageLast :
        newStage (Fin.last (H.dividerCount + (1 : ℕ))) = Utree) (stageAt :
    ∀ (j : Fin (H.dividerCount + (2 : ℕ))), (↑j : ℕ) ≤ H.dividerCount → newStage j = H.stage j)
        (divBound :
    ∀ (i : Fin H.dividerCount), (↑(H.dividerPosition i) : ℕ) ≤ B.length),
    let K : TashkinovHierarchy corrU.replacementETT baseU :=
        HierarchyCaseThreePreparation.helperK553 G k e0 input T phi ett base C ctx D hlenB hBT
        (fun {_ _ _ : TreeSequence G e0} ↦ segTrans) (fun {_ _ : TreeSequence G e0} ↦ equalTrees)
        m pv Utree hBU hAU corrU baseU hcoreU terminalData ordinaryToA hAUstrict stageOld
        stageLast stageAt divBound; (
    ∀ (j : Fin (H.dividerCount + (1 : ℕ))), HierarchyStarredStage K j = HierarchyStarredStage H j)
        → beta ∉ Gamma → (
    ∀ (S : TreeSequence G e0) (c : Fin k) (i : Fin (S.length + (1 : ℕ))), c ∈ MissingColors G phi
        (S.vertex i) → (↑(HierarchyFirstMissingPosition phi S c) : ℕ) ≤ (↑i : ℕ)) → (
    ∀ (c : Fin k), (↑(HierarchyFirstMissingPosition phi T c) : ℕ) < T.length → c ∈ MissingColors G
        phi (T.vertex (HierarchyFirstMissingPosition phi T c))) → (
    ∀ eta ∈ Dnq, D.alpha ∈ C.good.gamma q eta → (↑(HierarchyFirstMissingPosition phi T eta) : ℕ) ≤
        B.length) →
    ∀ eta ∈ Dnq, Disjoint (C.good.gamma q eta) (HierarchySegmentColors K q eta) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q n Tn A ell B Dnq Gamma beta Bplus
      hlenB hBT segTrans equalTrees m pv R hBR hRT Utree hRU hnew hBU hAU corrU baseU hcoreU
      terminalData ordinaryToA hAUstrict newStage stageOld stageLast stageAt divBound K starredEq
      betaOutsideGamma firstBound firstWitness control eta heta
  apply Finset.disjoint_left.mpr
  intro c hc hu
  unfold HierarchySegmentColors at hu
  dsimp only at hu
  rw [show q.succ = Fin.last (K.dividerCount + 1) from Fin.ext rfl,
    K.terminalStage, starredEq q] at hu
  obtain ⟨_, r, hrA, hrfirst, hrcolor⟩ := Finset.mem_filter.mp hu
  change A.length ≤ r.val at hrA
  by_cases hr : r.val < R.length
  · let rR : Fin R.length := ⟨r.val, hr⟩
    let rT : Fin T.length := Fin.castLE hRT.1 rR
    have hedge : phi (T.edge rT) = some c := by
      rw [hRT.2.2 rR, ← hRU.2.2 rR]
      simpa only [show Fin.castLE hRU.1 rR = r from Fin.ext rfl] using hrcolor
    have hcutU := HierarchyFirstMissingPositionPrefixCutoff phi R Utree hRU eta R.length le_rfl
    have hcutT := HierarchyFirstMissingPositionPrefixCutoff phi R T hRT eta R.length le_rfl
    have hsmall : r.val < min (HierarchyFirstMissingPosition phi T eta).val R.length := by
      rw [← hcutT, hcutU]
      omega
    have hseg : c ∈ HierarchySegmentColors H q eta := by
      unfold HierarchySegmentColors
      dsimp only
      rw [show q.succ = Fin.last (H.dividerCount + 1) from Fin.ext rfl, H.terminalStage]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rT, hrA,
        by have := rT.isLt; change r.val < min _ _; omega, hedge⟩
    exact (Finset.mem_sdiff.mp (C.good.avoidance q eta heta hc)).2 hseg
  · rcases (hnew r (by omega)).2.2.2.1 with ha | hb
    · have hca : c = D.alpha := Option.some.inj (hrcolor.symm.trans ha)
      subst c
      have hearly := control eta heta hc
      have hBlt : B.length < T.length := by rw [hlenB]; have := T.positive; omega
      have hm := firstWitness eta (lt_of_le_of_lt hearly hBlt)
      let iB : Fin (B.length + 1) :=
        ⟨(HierarchyFirstMissingPosition phi T eta).val, by omega⟩
      have hmissingB : eta ∈ MissingColors G phi (B.vertex iB) := by
        rw [← hBT.2.1 iB]
        have hi : Fin.castLE (Nat.succ_le_succ hBT.1) iB =
            HierarchyFirstMissingPosition phi T eta := Fin.ext rfl
        rw [hi]
        exact hm
      have hmissingU : eta ∈ MissingColors G phi
          (Utree.vertex (Fin.castLE (Nat.succ_le_succ hBU.1) iB)) := by
        rw [hBU.2.1 iB]
        exact hmissingB
      have hfirstU := firstBound Utree eta _ hmissingU
      change (HierarchyFirstMissingPosition phi Utree eta).val ≤
        (HierarchyFirstMissingPosition phi T eta).val at hfirstU
      have hBRlen := hBR.1
      omega
    · have hcb : c = beta := Option.some.inj (hrcolor.symm.trans hb)
      subst c
      exact betaOutsideGamma (Finset.mem_biUnion.mpr ⟨eta, heta, hc⟩)

theorem HierarchyCaseThreePreparation.helper_branch_1551.{u_1, u_2} :
    HierarchyCaseThreePreparation.helperBranch1551Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q n Tn A ell B Dn Dnq Gamma tailUsed
      beta hmissing hunused halternative Bplus Q hbetaPresent hlenB hlenPlus hBT hplusT hBBplus
      hbetaMissingPlus halphaMissingPlus hne hterminalOutside lastPositive hAT hTnA
      halphaMissingB m hm firstBound firstWitness haGamma haUsed
  clear * - G k e0 input T phi ett base C ctx D H q n Tn A ell B Bplus Q
    Dnq Gamma tailUsed beta hmissing hunused halternative hne hbetaPresent
    hlenB hlenPlus hBT hplusT hBBplus halphaMissingB halphaMissingPlus
    hbetaMissingPlus hterminalOutside hAT hTnA lastPositive firstBound firstWitness haGamma haUsed
  have hprefixElementary : ColoredVertexSetElementary G phi (TreeSequenceVertexSet Bplus) :=
    HierarchyCounterexamplePenultimateElementary G k e0 input T phi ett base C
      ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
      ctx.lexicographicMinimality ctx.largeMissingSet
  have prefixFirst (S : TreeSequence G e0) (hST : TreeSequenceInitialSegment S T)
      (c : Fin k) (hc : c ∈ TreeMissingColors phi S) :
      (HierarchyFirstMissingPosition phi T c).val ≤ S.length := by
    clear * - S hST c hc firstBound phi T
    obtain ⟨v, hv, hm⟩ := Finset.mem_biUnion.mp hc
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hv
    obtain ⟨i, hi⟩ := hv
    have hmissing : c ∈ MissingColors G phi
        (T.vertex (Fin.castLE (Nat.succ_le_succ hST.1) i)) := by
      rw [hST.2.1 i, hi]
      exact hm
    have hbound := firstBound T c _ hmissing
    change (HierarchyFirstMissingPosition phi T c).val ≤ i.val at hbound
    exact hbound.trans (Nat.le_of_lt_succ i.isLt)
  have haStage : D.alpha ∈ HierarchyStageMissingColors H q := by
    obtain ⟨eta, heta, hga⟩ := Finset.mem_biUnion.mp haGamma
    exact (Finset.mem_sdiff.mp (C.good.avoidance q eta heta hga)).1
  have hcase :
      (0 < H.dividerCount ∧ D.alpha ∈ TreeMissingColors phi (H.stage q.castSucc)) ∨
      (H.dividerCount = 0 ∧ D.alpha ∈ TreeMissingColors phi Tn) := by
    by_cases hz : H.dividerCount = 0
    · have hq : q = 0 := Fin.ext (by simp [q, hz])
      exact Or.inr ⟨hz, by simpa only [hq, HierarchyStageMissingColors, Fin.cases_zero] using
          haStage⟩
    · let i : Fin H.dividerCount := ⟨H.dividerCount - 1, by omega⟩
      have hq : q = i.succ := Fin.ext (by dsimp [q, i]; omega)
      refine Or.inl ⟨Nat.pos_of_ne_zero hz, ?_⟩
      simpa only [hq, HierarchyStageMissingColors, Fin.cases_succ] using haStage
  have haMissingA : D.alpha ∈ TreeMissingColors phi A := by
    rcases hcase with h | h
    · rw [lastPositive (Nat.ne_of_gt h.1)]
      exact h.2
    · obtain ⟨v, hv, hm⟩ := Finset.mem_biUnion.mp h.2
      exact Finset.mem_biUnion.mpr ⟨v, TreeSequenceInitialSegmentVertexSetSubset hTnA hv, hm⟩
  have haFirstA := prefixFirst A hAT D.alpha haMissingA
  have haFirstB := prefixFirst B hBT D.alpha halphaMissingB
  have hbFirstB := prefixFirst B hBT beta hmissing
  let ia := HierarchyFirstMissingPosition phi T D.alpha
  let ib := HierarchyFirstMissingPosition phi T beta
  let va := T.vertex ia
  let vb := T.vertex ib
  let yp := T.vertex D.terminalVertexIndex
  have hBlt : B.length < T.length := by rw [hlenB]; have := T.positive; omega
  have hma : D.alpha ∈ MissingColors G phi va :=
    firstWitness _ (lt_of_le_of_lt haFirstB hBlt)
  have hmb : beta ∈ MissingColors G phi vb :=
    firstWitness _ (lt_of_le_of_lt hbFirstB hBlt)
  have firstInB (c : Fin k) (hc : (HierarchyFirstMissingPosition phi T c).val ≤ B.length) :
      T.vertex (HierarchyFirstMissingPosition phi T c) ∈ TreeSequenceVertexSet Bplus := by
    let i : Fin (B.length + 1) := ⟨(HierarchyFirstMissingPosition phi T c).val, by omega⟩
    have hv : T.vertex (HierarchyFirstMissingPosition phi T c) = B.vertex i := by
      exact hBT.2.1 i
    apply TreeSequenceInitialSegmentVertexSetSubset hBBplus
    rw [hv]
    simp [TreeSequenceVertexSet]
  have hva := firstInB D.alpha haFirstB
  have hvb := firstInB beta hbFirstB
  have hsame := ChangeLemma G k e0 input T phi ett base C ctx.proper ctx.oneEdgeUncolored
    ctx.lowerRung ctx.fewerDividers ctx.lexicographicMinimality hprefixElementary
        ctx.largeMissingSet
    D.alpha beta hne ⟨halphaMissingPlus, hbetaMissingPlus⟩ (by
      dsimp only
      intro hn
      change D.alpha ∉ TreeMissingColors phi A ∨ beta ∉ TreeMissingColors phi A at hn
      have hbAbsent : beta ∉ TreeMissingColors phi A := hn.resolve_left (by
        intro hna; exact hna haMissingA)
      have hbAfter : A.length < ib.val := by
        by_contra hno
        have hle : ib.val ≤ A.length := by omega
        let i : Fin (A.length + 1) := ⟨ib.val, by omega⟩
        apply hbAbsent
        refine Finset.mem_biUnion.mpr ⟨A.vertex i, by simp [TreeSequenceVertexSet], ?_⟩
        rw [← hAT.2.1 i]
        have hi : Fin.castLE (Nat.succ_le_succ hAT.1) i = ib := Fin.ext rfl
        rw [hi]
        exact hmb
      refine ⟨⟨ia, ib, rfl, rfl, lt_of_le_of_lt haFirstA hbAfter⟩, ?_⟩
      intro hcolor
      obtain ⟨t, htA, _, htc⟩ := (Finset.mem_filter.mp hcolor).2
      exact haUsed (Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, htA, htc⟩))
  have hsameComponent : TwoColorComponent G phi D.alpha beta (Sum.inl va) =
      TwoColorComponent G phi D.alpha beta (Sum.inl vb) := by
    rcases hcase with h | h
    · exact hsame.1 ⟨h.1, Or.inl h.2⟩
    · exact hsame.2.1 ⟨h.1, Or.inl h.2⟩
  let graph := TwoColorIncidenceGraph G phi D.alpha beta
  have absent (v : V) (c : Fin k) (hc : c ∈ MissingColors G phi v)
      (f : E) (hf : Incident G v f) : phi f ≠ some c := by
    intro hfc
    exact (Finset.mem_sdiff.mp hc).2 (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, f, hf, hfc⟩)
  have leaf (v : V) (hm : D.alpha ∈ MissingColors G phi v ∨ beta ∈ MissingColors G phi v) :
      (graph.neighborSet (Sum.inl v)).Subsingleton := by
    clear * - G phi D beta graph hm v ctx absent
    intro x hx y hy
    cases x with
    | inl x => exact (show False by simp [graph, TwoColorIncidenceGraph] at hx).elim
    | inr f =>
      cases y with
      | inl y => exact (show False by simp [graph, TwoColorIncidenceGraph] at hy).elim
      | inr g =>
        have hxf : Incident G v f ∧ (phi f = some D.alpha ∨ phi f = some beta) := hx
        have hyg : Incident G v g ∧ (phi g = some D.alpha ∨ phi g = some beta) := hy
        by_cases hfg : f = g
        · exact congrArg Sum.inr hfg
        · exfalso
          rcases hm with hm | hm
          · have hf := hxf.2.resolve_left (absent v D.alpha hm f hxf.1)
            have hg := hyg.2.resolve_left (absent v D.alpha hm g hyg.1)
            exact ctx.proper hfg ⟨v, hxf.1, hyg.1⟩ hf hg
          · have hf := hxf.2.resolve_right (absent v beta hm f hxf.1)
            have hg := hyg.2.resolve_right (absent v beta hm g hyg.1)
            exact ctx.proper hfg ⟨v, hxf.1, hyg.1⟩ hf hg
  have disjointFirst : Disjoint Q (TwoColorComponent G phi D.alpha beta (Sum.inl va)) := by
    rcases TwoColorComponentsDisjoint G phi D.alpha beta (Sum.inl yp) (Sum.inl va) with he | hd
    · exfalso
      have haQ : Sum.inl va ∈ Q := by
        change Sum.inl va ∈ TwoColorComponent G phi D.alpha beta (Sum.inl yp)
        rw [he]
        rfl
      have hbQ : Sum.inl vb ∈ Q := by
        change Sum.inl vb ∈ TwoColorComponent G phi D.alpha beta (Sum.inl yp)
        rw [he, hsameComponent]
        rfl
      have hyQ : Sum.inl yp ∈ Q := rfl
      have hay : va ≠ yp := by
        intro heq
        apply hterminalOutside
        change yp ∈ TreeSequenceVertexSet Bplus
        rw [← heq]
        exact hva
      have hby : vb ≠ yp := by
        intro heq
        apply hterminalOutside
        change yp ∈ TreeSequenceVertexSet Bplus
        rw [← heq]
        exact hvb
      have hab : va ≠ vb := by
        intro heq
        have hmbA : beta ∈ MissingColors G phi va := heq ▸ hmb
        have hempty : graph.neighborSet (Sum.inl va) = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro x hx
          cases x with
          | inl x => simp [graph, TwoColorIncidenceGraph] at hx
          | inr f =>
            have hf : Incident G va f ∧ (phi f = some D.alpha ∨ phi f = some beta) := hx
            exact hf.2.elim (absent va D.alpha hma f hf.1) (absent va beta hmbA f hf.1)
        have hreach : graph.Reachable (Sum.inl va) (Sum.inl yp) :=
          SimpleGraph.ConnectedComponent.eq.mp haQ
        exact SimpleGraph.not_reachable_of_neighborSet_left_eq_empty
          (by intro h; exact hay (Sum.inl.inj h)) hempty hreach
      obtain ⟨u, v, p, hp, hsupp⟩ :=
        TwoColorComponentSpanningPath G phi D.alpha beta ctx.proper (Sum.inl yp)
      have endpoints (x : Sum V E) (hx : x ∈ Q) (hleaf : (graph.neighborSet x).Subsingleton) :
          x = u ∨ x = v := by
        have hxP : x ∈ p.support := by
          change x ∈ {x | x ∈ p.support}
          rw [hsupp]
          exact hx
        by_cases hxu : x = u
        · exact Or.inl hxu
        · by_cases hxv : x = v
          · exact Or.inr hxv
          · exact (hp.isTrail.notMem_support_of_subsingleton_neighborSet hxu hxv hleaf hxP).elim
      have hea := endpoints _ haQ (leaf va (Or.inl hma))
      have heb := endpoints _ hbQ (leaf vb (Or.inr hmb))
      have hey := endpoints _ hyQ (leaf yp (Or.inl D.alphaMissingTerminal))
      have hab' : (Sum.inl va : Sum V E) ≠ Sum.inl vb := fun h => hab (Sum.inl.inj h)
      have hay' : (Sum.inl va : Sum V E) ≠ Sum.inl yp := fun h => hay (Sum.inl.inj h)
      have hby' : (Sum.inl vb : Sum V E) ≠ Sum.inl yp := fun h => hby (Sum.inl.inj h)
      rcases hea with hea | hea <;> rcases heb with heb | heb <;> rcases hey with hey | hey
      all_goals first
        | exact hab' (hea.trans heb.symm)
        | exact hay' (hea.trans hey.symm)
        | exact hby' (heb.trans hey.symm)
    · exact hd
  exact @HierarchyCaseThreePreparation.helper_caseContinuation_1264 (@V) (@E) inferInstance
      inferInstance inferInstance inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett)
      (@base) (@C) (@ctx) (@D) (@beta) (@hmissing) (@hunused) (@halternative) (@hlenB)
      (@hlenPlus) (@hBT) (@hplusT) (@hBBplus) (@hbetaMissingPlus) (@halphaMissingPlus) (@hne)
      (@hterminalOutside) (@lastPositive) (@hAT) (@haGamma) (@haUsed) (@hprefixElementary)
      (@hcase) (@hbFirstB) (@hma) (@hmb) (@hva) (@hvb) (@hsameComponent) (@leaf) (@disjointFirst)

end GoldbergSeymour

end
