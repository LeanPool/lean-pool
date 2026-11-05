/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.StableChangeCaseThree.Preparation4
public import LeanPool.GoldbergSeymour.ChangeLemmaBothOutside

/-!
# StableChangeCaseThree: supporting constructions, part 5

Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
This module separates dependent data constructors from their supporting proofs.
-/

@[expose] public section

namespace GoldbergSeymour.StableChangeCaseThreePreparation

/-- Dependent contract shared by the hierarchy construction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperContinuation3662Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (hproper :
        IsProperEdgeColoring G phi) (hone : IsOneEdgeUncolored phi e0) (hlower :
        LowerRoundInductionHypothesis G k e0 ett.rounds) (hfewer :
    ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k} (other : ExtendedTashkinovTree G k e0 input' T'
        generating'), other.rounds = ett.rounds → MaximumProperty other →
    ∀ (base' : HierarchyBase other generating') (K : TashkinovHierarchy other base') (a :
        GoodHierarchy K), K.dividerCount < C.hierarchy.dividerCount → ColoredVertexSetElementary G
        generating' (TreeSequenceVertexSet T')) (hminimal :
    ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k}
        {other : ExtendedTashkinovTree G k e0 input' T' generating'}
        {base' : HierarchyBase other generating'} (C' : HierarchyCounterexample base'),
        other.rounds = ett.rounds → C'.hierarchy.dividerCount = C.hierarchy.dividerCount →
        ¬HierarchyCounterexampleLess (HierarchyCounterexampleMeasure C')
        (HierarchyCounterexampleMeasure C)) (hprefixElementary :
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
    let ell : ℕ := T.length - A.length;
    let Ty : TreeSequence G e0 := TreeSequencePrefix T (min (A.length + (ell - (1 : ℕ))) T.length)
        (le_min (le_trans A.positive (Nat.le_add_right _ _)) T.positive) (Nat.min_le_right
        (A.length + (ell - (1 : ℕ))) T.length); ColoredVertexSetElementary G phi
        (TreeSequenceVertexSet Ty)) (hlarge :
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc; (2 : ℕ) * ett.rounds + (11 : ℕ)
        ≤ (TreeMissingColors phi Tn).card) (alpha beta : Fin k) (hne : alpha ≠ beta)
        (hmissingPrefix :
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
    let ell : ℕ := T.length - A.length;
    let Ty : TreeSequence G e0 := TreeSequencePrefix T (min (A.length + (ell - (1 : ℕ))) T.length)
        (le_min (le_trans A.positive (Nat.le_add_right _ _)) T.positive) (Nat.min_le_right
        (A.length + (ell - (1 : ℕ))) T.length); alpha ∈ TreeMissingColors phi Ty ∧ beta ∈
        TreeMissingColors phi Ty) (z : V ⊕ E) (sigma : PartialEdgeColoring E k) (hsigma : sigma =
        TwoColorComponentSwap G phi alpha beta z) (hAprecedes :
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let va : V := T.vertex (HierarchyFirstMissingPosition phi T alpha);
    ∀ u ∈ TreeSequenceVertexSet A, TreeVertexOrder T u va) (hordered :
    let va : V := T.vertex (HierarchyFirstMissingPosition phi T alpha);
    let vb : V := T.vertex (HierarchyFirstMissingPosition phi T beta); TreeVertexOrder T va vb)
        (hnotStored :
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q; alpha ∉ Dnq ∧ beta ∉ Dnq) (hunused :
    let ia : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T alpha;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta; alpha ∉ ({c :
        Fin k |
    ∃ (t : Fin T.length), (↑ia : ℕ) ≤ (↑t : ℕ) ∧ (↑t : ℕ) < (↑ib : ℕ) ∧ phi (T.edge t) = some c} :
        Finset (Fin k))),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    let ia : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T alpha;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let va : V := T.vertex ia;
    let vb : V := T.vertex ib;
    let ell : ℕ := T.length - A.length;
    let Y : TreeSequence G e0 := TreeSequencePrefix T (min (A.length + (ell - (1 : ℕ))) T.length)
        (
    have this : (1 : ℕ) ≤ A.length := A.positive;
    have this_1 : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤
        min (A.length + (ell - (1 : ℕ))) T.length) ↦
    by
      omega
    ) (Nat.min_le_right (A.length + (ell - (1 : ℕ))) T.length);
    ∀ (segTrans :
    ∀ {S U W : TreeSequence G e0} (hSU : TreeSequenceInitialSegment S U) (hUW :
        TreeSequenceInitialSegment U W), TreeSequenceInitialSegment S W) (commonPrefix :
    ∀ {S U W : TreeSequence G e0} (hSW : TreeSequenceInitialSegment S W) (hUW :
        TreeSequenceInitialSegment U W) (hlen : S.length ≤ U.length), TreeSequenceInitialSegment S
        U) (equalTrees :
    ∀ {S U : TreeSequence G e0} (hSU : TreeSequenceInitialSegment S U) (hlen : S.length =
        U.length), S = U) (lastPositive :
    ∀ (hz : H.dividerCount ≠ (0 : ℕ)), A = H.stage (⟨H.dividerCount,
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) (coreToA : TreeSequenceInitialSegment base.core A) (TnToA
        : TreeSequenceInitialSegment Tn A) (AToT : TreeSequenceInitialSegment A T) (ordinaryToA :
    ∀ (j : Fin (H.dividerCount + (1 : ℕ))), TreeSequenceInitialSegment (H.stage j.castSucc) A)
        (starredToA :
    ∀ (j : Fin (H.dividerCount + (1 : ℕ))), TreeSequenceInitialSegment (HierarchyStarredStage H j)
        A) (hmissingY : alpha ∈ TreeMissingColors phi Y ∧ beta ∈ TreeMissingColors phi Y) (ha :
        alpha ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T alpha)) ∧
        (↑(HierarchyFirstMissingPosition phi T alpha) : ℕ) ≤ Y.length) (hb : beta ∈ MissingColors
        G phi (T.vertex (HierarchyFirstMissingPosition phi T beta)) ∧
        (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ Y.length) (habIndex : (↑ia : ℕ) < (↑ib
        : ℕ)) (hout : va ∉ TreeSequenceVertexSet A ∧ vb ∉ TreeSequenceVertexSet A) (hAia :
        A.length < (↑ia : ℕ)) (hAib : A.length < (↑ib : ℕ)) (haY : va ∈ TreeSequenceVertexSet Y)
        (halphaA : alpha ∉ TreeMissingColors phi A) (hbetaA : beta ∉ TreeMissingColors phi A)
        (missingSubset :
    ∀ {S U : TreeSequence G e0} (hSU : TreeSequenceInitialSegment S U), TreeMissingColors phi S ⊆
        TreeMissingColors phi U) (hDn : alpha ∉ Dn ∧ beta ∉ Dn) (notControlled :
    ∀ (c : Fin k) (hc : c = alpha ∨ c = beta), c ∉ TreeMissingColors phi Tn ∪ Dn) (terminalRoute :
        ett.series.data.kind n = some TashkinovExtensionKind.PE ∧ TashkinovAugmentationSequence
        phi Tn T ∨ (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨ ett.series.data.kind
        n = some TashkinovExtensionKind.RE) ∧
    ∃ (f : E) (seed : TreeSequence G e0), ett.series.data.connectingEdges n = ({ f } : Finset E) ∧
        TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence phi seed T ∧ phi f ≠ some
        alpha ∧ phi f ≠ some beta) (treeControlled :
    ∀ (t : Fin Tn.length), phi (Tn.edge t) ≠ some alpha ∧ phi (Tn.edge t) ≠ some beta)
        (augmentationControlled :
    ∀ (S : TreeSequence G e0) (hseq : TashkinovAugmentationSequence phi S T) (t : Fin T.length)
        (ht : S.length ≤ (↑t : ℕ)) (htb : (↑t : ℕ) < (↑ib : ℕ)), phi (T.edge t) ≠ some alpha ∧ phi
        (T.edge t) ≠ some beta) (prefixControlled :
    ∀ (t : Fin T.length) (htb : (↑t : ℕ) < (↑ib : ℕ)), phi (T.edge t) ≠ some alpha ∧ phi (T.edge
        t) ≠ some beta) (horderedUnused : alpha ∉ TreeMissingColors phi A ∨ beta ∉
        TreeMissingColors phi A → TreeVertexOrder T va vb ∧ alpha ∉ ({c : Fin k |
    ∃ (t : Fin T.length), A.length ≤ (↑t : ℕ) ∧ (↑t : ℕ) < (↑ib : ℕ) ∧ phi (T.edge t) = some c} :
        Finset (Fin k))),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let Tnq : TreeSequence G e0 := H.stage (⟨H.dividerCount,
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)));
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q; HierarchyWeaklyStable H q sigma ∧
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
    let jH : Fin (H.dividerCount + (1 : ℕ)) := (⟨(↑j : ℕ),
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
        corrT.replacementETT baseT) (goodT : GoodHierarchy K), SameGoodHierarchy C.good goodT

private abbrev helperContinuation370Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (alpha beta
        : Fin k) (hne : alpha ≠ beta) (sigma : PartialEdgeColoring E k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    ∀ (commonPrefix :
    ∀ {S U W : TreeSequence G e0} (hSW : TreeSequenceInitialSegment S W) (hUW :
        TreeSequenceInitialSegment U W) (hlen : S.length ≤ U.length), TreeSequenceInitialSegment S
        U) (equalTrees :
    ∀ {S U : TreeSequence G e0} (hSU : TreeSequenceInitialSegment S U) (hlen : S.length =
        U.length), S = U) (lastPositive :
    ∀ (hz : H.dividerCount ≠ (0 : ℕ)), A = H.stage (⟨H.dividerCount,
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) (coreToA : TreeSequenceInitialSegment base.core A) (TnToA
        : TreeSequenceInitialSegment Tn A) (AToT : TreeSequenceInitialSegment A T) (ordinaryToA :
    ∀ (j : Fin (H.dividerCount + (1 : ℕ))), TreeSequenceInitialSegment (H.stage j.castSucc) A)
        (starredToA :
    ∀ (j : Fin (H.dividerCount + (1 : ℕ))), TreeSequenceInitialSegment (HierarchyStarredStage H j)
        A) (hAib : A.length < (↑ib : ℕ)) (halphaA : alpha ∉ TreeMissingColors phi A) (hbetaA :
        beta ∉ TreeMissingColors phi A) (missingSubset :
    ∀ {S U : TreeSequence G e0} (hSU : TreeSequenceInitialSegment S U), TreeMissingColors phi S ⊆
        TreeMissingColors phi U) (hDn : alpha ∉ Dn ∧ beta ∉ Dn) (terminalRoute :
        ett.series.data.kind n = some TashkinovExtensionKind.PE ∧ TashkinovAugmentationSequence
        phi Tn T ∨ (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨ ett.series.data.kind
        n = some TashkinovExtensionKind.RE) ∧
    ∃ (f : E) (seed : TreeSequence G e0), ett.series.data.connectingEdges n = ({ f } : Finset E) ∧
        TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence phi seed T ∧ phi f ≠ some
        alpha ∧ phi f ≠ some beta) (unaffected :
    ∀ (f : E) (c : Fin k) (hca : c ≠ alpha) (hcb : c ≠ beta), sigma f = some c ↔ phi f = some c)
        (missingUnaffected :
    ∀ (v : V) (c : Fin k) (hca : c ≠ alpha) (hcb : c ≠ beta), c ∈ MissingColors G sigma v ↔ c ∈
        MissingColors G phi v) (missingA :
    ∀ (v : V) (hv : v ∈ TreeSequenceVertexSet A), MissingColors G sigma v = MissingColors G phi v)
        (treeMissingEq :
    ∀ (S : TreeSequence G e0) (hS : TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A),
        TreeMissingColors sigma S = TreeMissingColors phi S) (closureInsideA :
    ∀ (hPE : ett.series.data.kind n = some TashkinovExtensionKind.PE), TreeSequenceVertexSet
        base.closure ⊆ TreeSequenceVertexSet A) (weak : HierarchyWeaklyStable H q sigma) (hmod :
        ModColoring ett sigma) (transportBefore :
    ∀ (S U : TreeSequence G e0) (hseq : TashkinovAugmentationSequence phi S U) (hUT :
        TreeSequenceInitialSegment U T) (hU : U.length ≤ (↑ib : ℕ)), TashkinovAugmentationSequence
        sigma S U) (corrData :
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma T),
        corr.replacementETT.series.data.tree (Fin.last corr.replacementETT.rounds).castSucc = Tn ∧
        corr.replacementETT.series.data.kind (Fin.last corr.replacementETT.rounds) =
        ett.series.data.kind n ∧ TashkinovStoredColors corr.replacementETT.series.data (Fin.last
        corr.replacementETT.rounds) = Dn) (fullBase :
    ∃ (corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma T), MaximumProperty
        corr.replacementETT ∧
    ∃ (baseT : HierarchyBase corr.replacementETT sigma), baseT.core = base.core ∧ baseT.closure =
        base.closure),
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
        corrT.replacementETT baseT) (goodT : GoodHierarchy K), SameGoodHierarchy C.good goodT

private theorem helper_continuation_370.{u_1, u_2} :
    helperContinuation370Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta hne sigma H q A n Tn Dn ib
      commonPrefix equalTrees lastPositive coreToA TnToA AToT ordinaryToA starredToA hAib halphaA
      hbetaA missingSubset hDn terminalRoute unaffected missingUnaffected missingA treeMissingEq
      closureInsideA weak hmod transportBefore corrData fullBase
  obtain ⟨corrT, hmaximumT, baseT, hcoreT, hclosureT⟩ := fullBase
  have terminalData := corrData corrT
  let K : TashkinovHierarchy corrT.replacementETT baseT := {
    dividerCount := H.dividerCount
    stage := H.stage
    baseStage := H.baseStage.trans terminalData.1.symm
    terminalStage := H.terminalStage
    nested := H.nested
    strict := H.strict
    dividerPosition := H.dividerPosition
    dividerPositive := H.dividerPositive
    dividerIncreasing := H.dividerIncreasing
    dividerStage := H.dividerStage
    coreInsideFirst := by rw [hcoreT]; exact H.coreInsideFirst }
  have starredEq (j : Fin (H.dividerCount + 1)) :
      HierarchyStarredStage K j = HierarchyStarredStage H j := by
    exact Fin.cases hcoreT (fun _ => rfl) j
  have storedEq (j : Fin (H.dividerCount + 1)) :
      HierarchyStoredColorsAt K j = HierarchyStoredColorsAt H j := by
    unfold HierarchyStoredColorsAt
    dsimp only
    rw [terminalData.2.2, starredEq j,
      treeMissingEq _ (TreeSequenceInitialSegmentVertexSetSubset (starredToA j))]
  have stageMissingEq (j : Fin (H.dividerCount + 1)) :
      HierarchyStageMissingColors K j = HierarchyStageMissingColors H j := by
    exact @helper_stageMissingEq_1044 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@sigma) (@TnToA)
        (@ordinaryToA) (@treeMissingEq) (@corrT) (@baseT) (@hcoreT) (@terminalData) (@j)
  have stageMissingInside (j : Fin (H.dividerCount + 1)) :
      HierarchyStageMissingColors H j ⊆ TreeMissingColors phi A := by
    exact Fin.cases (missingSubset TnToA) (fun a => missingSubset (ordinaryToA a.succ)) j
  have ownerNot (j : Fin (H.dividerCount + 1)) (eta : Fin k)
      (heta : eta ∈ HierarchyStoredColorsAt H j) : eta ≠ alpha ∧ eta ≠ beta := by
    have hd : eta ∈ Dn := (Finset.mem_sdiff.mp heta).1
    exact ⟨fun he => hDn.1 (he ▸ hd), fun he => hDn.2 (he ▸ hd)⟩
  have gammaNot (j : Fin (H.dividerCount + 1)) (eta : Fin k)
      (heta : eta ∈ HierarchyStoredColorsAt H j) (c : Fin k)
      (hc : c ∈ C.good.gamma j eta) : c ≠ alpha ∧ c ≠ beta := by
    have hm := stageMissingInside j (Finset.mem_sdiff.mp (C.good.avoidance j eta heta hc)).1
    exact ⟨fun he => halphaA (he ▸ hm), fun he => hbetaA (he ▸ hm)⟩
  have firstEq (c : Fin k) (hca : c ≠ alpha) (hcb : c ≠ beta) :
      HierarchyFirstMissingPosition sigma T c = HierarchyFirstMissingPosition phi T c := by
    exact @helper_firstEq_1065 (@V) (@E) inferInstance inferInstance (@G) (@k) (@e0) (@T) (@phi)
        (@alpha) (@beta) (@sigma) (@missingUnaffected) (@c) (@hca) (@hcb)
  have segmentTransfer (j : Fin (H.dividerCount + 1)) (eta : Fin k)
      (heta : eta ∈ HierarchyStoredColorsAt H j) (c : Fin k)
      (hca : c ≠ alpha) (hcb : c ≠ beta)
      (hc : c ∈ HierarchySegmentColors K j eta) :
      c ∈ HierarchySegmentColors H j eta := by
    exact @helper_segmentTransfer_1077 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
        (@sigma) (@unaffected) (@corrT) (@baseT) (@hcoreT) (@terminalData) (@starredEq)
        (@ownerNot) (@firstEq) (@j) (@eta) (@heta) (@c) (@hca) (@hcb) (@hc)
  have boundaryEq (S : TreeSequence G e0) (c : Fin k) (hca : c ≠ alpha) (hcb : c ≠ beta) :
      BoundaryColorEdges G sigma (TreeSequenceVertexSet S) c =
        BoundaryColorEdges G phi (TreeSequenceVertexSet S) c := by
    ext f
    simp only [BoundaryColorEdges, Finset.mem_filter]
    rw [unaffected f c hca hcb]
  have minusEq (S : TreeSequence G e0)
      (hS : TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A) (R : Finset (Fin k)) :
      TreeColorSetMinusClosed G sigma S R ↔ TreeColorSetMinusClosed G phi S R := by
    exact @helper_minusEq_1094 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta) (@sigma)
        (@halphaA) (@hbetaA) (@treeMissingEq) (@boundaryEq) (@S) (@hS) (@R)
  let goodT : GoodHierarchy K := by
    exact @helperGoodT2426 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta) (@hne) (@sigma)
        (@coreToA) (@TnToA) (@ordinaryToA) (@missingA) (@treeMissingEq) (@closureInsideA)
        (@corrT) (@baseT) (@hcoreT) (@hclosureT) (@terminalData) (@starredEq) (@storedEq)
        (@stageMissingEq) (@gammaNot) (@segmentTransfer) (@minusEq)
  have same : SameGoodHierarchy C.good goodT := by
    exact @helper_same_2713 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta) (@hne) (@sigma)
        (@coreToA) (@TnToA) (@ordinaryToA) (@missingA) (@treeMissingEq) (@closureInsideA)
        (@corrT) (@baseT) (@hcoreT) (@hclosureT) (@terminalData) (@starredEq) (@storedEq)
        (@stageMissingEq) (@gammaNot) (@segmentTransfer) (@minusEq)
  have prefixMaximum : A = Tn ∨
      ∃ inputA : PartialEdgeColoring E k,
        ∃ ettA : ExtendedTashkinovTree G k e0 inputA A sigma, MaximumProperty ettA := by
    exact @helper_prefixMaximum_1187 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
        (@sigma) (@commonPrefix) (@equalTrees) (@TnToA) (@AToT) (@hAib) (@terminalRoute) (@hmod)
        (@transportBefore)
  refine ⟨weak, hmod, prefixMaximum, ?_, corrT, hmaximumT, baseT, K, goodT, same⟩
  intro hq
  have hqK : 1 ≤ q.val := by change 0 < H.dividerCount at hq; dsimp [q]; omega
  have hqpos : H.dividerCount ≠ 0 := by change 0 < H.dividerCount at hq; omega
  have hA : A = H.stage q.castSucc := by
    rw [lastPositive hqpos]
    rfl
  exact @helper_positivePackage_2874 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
      (@hne) (@sigma) (@coreToA) (@TnToA) (@ordinaryToA) (@missingA) (@treeMissingEq)
      (@closureInsideA) (@corrT) (@hmaximumT) (@baseT) (@hcoreT) (@hclosureT) (@terminalData)
      (@starredEq) (@storedEq) (@stageMissingEq) (@gammaNot) (@segmentTransfer) (@minusEq) (@hq)
      (@hqK) (@A) (@hA)

theorem helper_continuation_3662.{u_1, u_2} :
    helperContinuation3662Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hproper hone hlower hfewer hminimal
      hprefixElementary hlarge alpha beta hne hmissingPrefix z sigma hsigma hAprecedes hordered
      hnotStored hunused H q A n Tn Dn ia ib va vb ell Y segTrans commonPrefix equalTrees
      lastPositive coreToA TnToA AToT ordinaryToA starredToA hmissingY ha hb habIndex hout hAia
      hAib haY halphaA hbetaA missingSubset hDn notControlled terminalRoute treeControlled
      augmentationControlled prefixControlled horderedUnused
  have hchange := ChangeLemmaBothOutside G k e0 input T phi ett base C hproper hone
    hlower hfewer hminimal hprefixElementary hlarge alpha beta hne hmissingPrefix
    horderedUnused hout
  have sameComponent : TwoColorComponent G phi alpha beta (Sum.inl va) =
      TwoColorComponent G phi alpha beta (Sum.inl vb) := by
    exact @helper_sameComponent_3526 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
        (@hne) (@hmissingPrefix) (@z) (@sigma) (@hsigma) (@hAprecedes) (@hordered) (@hnotStored)
        (@hunused) (@hmissingY) (@ha) (@habIndex) (@hout) (@hAia) (@haY) (@halphaA) (@hDn)
        (@notControlled) (@terminalRoute) (@treeControlled) (@augmentationControlled)
        (@prefixControlled) (@horderedUnused) (@hchange)
  have behavior := TwoColorComponentSwapMissingBehavior G phi alpha beta hne hproper z
  have fixedValue (f : E) (ha : phi f ≠ some alpha) (hb : phi f ≠ some beta) :
      sigma f = phi f := by
    rw [hsigma]
    simp [TwoColorComponentSwap, ha, hb]
  have unaffected (f : E) (c : Fin k) (hca : c ≠ alpha) (hcb : c ≠ beta) :
      sigma f = some c ↔ phi f = some c := by
    exact @helper_unaffected_835 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
        (@hne) (@z) (@sigma) (@hsigma) (@ha) (@hb) (@f) (@c) (@hca) (@hcb)
  have missingUnaffected (v : V) (c : Fin k) (hca : c ≠ alpha) (hcb : c ≠ beta) :
      c ∈ MissingColors G sigma v ↔ c ∈ MissingColors G phi v := by
    rw [hsigma]
    exact behavior.2.2.2 v c hca hcb
  have sigmaProper : IsProperEdgeColoring G sigma := by
    rw [hsigma]
    exact TwoColorComponentSwapProper G phi alpha beta hne hproper z
  have sigmaOne : IsOneEdgeUncolored sigma e0 := by
    exact @helper_sigmaOne_852 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hone) (@alpha) (@beta) (@hne)
        (@z) (@sigma) (@hsigma) (@ha) (@hb) (@unaffected)
  have missingA (v : V) (hv : v ∈ TreeSequenceVertexSet A) :
      MissingColors G sigma v = MissingColors G phi v := by
    exact @helper_missingA_629 V E inferInstance inferInstance inferInstance inferInstance G k e0
        input T phi ett base C alpha beta hne z sigma hsigma halphaA hbetaA behavior
        missingUnaffected v hv
  have treeMissingEq (S : TreeSequence G e0)
      (hS : TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A) :
      TreeMissingColors sigma S = TreeMissingColors phi S := by
    unfold TreeMissingColors
    exact Finset.biUnion_congr rfl (fun v hv => missingA v (hS hv))
  have stable (S : TreeSequence G e0)
      (hS : TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A)
      (D : Finset (Fin k)) (hD : alpha ∉ D ∧ beta ∉ D) :
      StableColoring S D phi sigma := by
    exact @helper_stable_876 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta) (@sigma)
        (@halphaA) (@hbetaA) (@unaffected) (@missingA) (@S) (@hS) (@D) (@hD)
  have stableTn : StableColoring Tn Dn phi sigma :=
    stable Tn (TreeSequenceInitialSegmentVertexSetSubset TnToA) Dn hDn
  have closureInsideA (hPE : ett.series.data.kind n = some TashkinovExtensionKind.PE) :
      TreeSequenceVertexSet base.closure ⊆ TreeSequenceVertexSet A := by
    exact @helper_closureInsideA_893 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@coreToA) (@hPE)
  have combined (hPE : ett.series.data.kind n = some TashkinovExtensionKind.PE) :
      CombinedStableColoring Tn base.closure Dn phi sigma :=
    ⟨stableTn, stable base.closure (closureInsideA hPE) ∅ (by simp)⟩
  have invariant (S : TreeSequence G e0) (hSA : TreeSequenceInitialSegment S A) :
      TreeColoringInvariant S phi sigma := by
    exact @helper_invariant_903 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta) (@sigma)
        (@segTrans) (@AToT) (@habIndex) (@hAia) (@prefixControlled) (@fixedValue) (@missingA)
        (@S) (@hSA)
  have weak : HierarchyWeaklyStable H q sigma := by
    exact @helper_weak_912 (@V) (@E) inferInstance inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@sigma) (@ordinaryToA) (@stableTn)
        (@combined) (@invariant)
  have stableLadder : StableColoring Tn Dn (ett.series.data.coloring n) sigma := by
    rw [show ett.series.data.coloring n = phi from ett.generatingColoring.symm]
    exact stableTn
  have hmod : ModColoring ett sigma := Td G k e0 input T phi ett C.maximum
    C.positive hlower sigma sigmaProper sigmaOne stableLadder
  -- Before b every augmentation color is unaffected. Beyond b both colors remain missing.
  let B := TreeSequencePrefix T ib.val (by have := A.positive; omega)
    (Nat.le_of_lt_succ ib.isLt)
  have BToT : TreeSequenceInitialSegment B T :=
    ⟨Nat.le_of_lt_succ ib.isLt, (by intro i; rfl), (by intro i; rfl)⟩
  have AToB : TreeSequenceInitialSegment A B := commonPrefix AToT BToT (le_of_lt hAib)
  have vertexB (i : Fin (T.length + 1)) (hi : i.val ≤ B.length) :
      T.vertex i ∈ TreeSequenceVertexSet B := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨i.val, by omega⟩, rfl⟩
  have haB : va ∈ TreeSequenceVertexSet B := vertexB ia (le_of_lt habIndex)
  have hbB : vb ∈ TreeSequenceVertexSet B := vertexB ib le_rfl
  have together : (Sum.inl va ∈ TwoColorComponent G phi alpha beta z) ↔
      (Sum.inl vb ∈ TwoColorComponent G phi alpha beta z) := by
    exact @helper_together_938 (@V) (@E) inferInstance inferInstance (@G) (@k) (@e0) (@T) (@phi)
        (@alpha) (@beta) (@z) (@sameComponent)
  have bothMissingB : alpha ∈ TreeMissingColors sigma B ∧ beta ∈ TreeMissingColors sigma B := by
    exact @helper_bothMissingB_946 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
        (@z) (@sigma) (@hsigma) (@ha) (@hb) (@hAib) (@behavior) (@haB) (@hbB) (@together)
  have transportBefore (S U : TreeSequence G e0)
      (hseq : TashkinovAugmentationSequence phi S U)
      (hUT : TreeSequenceInitialSegment U T) (hU : U.length ≤ ib.val) :
      TashkinovAugmentationSequence sigma S U := by
    exact @helper_transportBefore_958 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
        (@sigma) (@segTrans) (@prefixControlled) (@unaffected) (@missingUnaffected) (@S) (@U)
        (@hseq) (@hUT) (@hU)
  have transportRoute (S : TreeSequence G e0)
      (hseq : TashkinovAugmentationSequence phi S T)
      (hSB : TreeSequenceInitialSegment S B) :
      TashkinovAugmentationSequence sigma S T := by
    exact @helper_transportRoute_981 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
        (@hne) (@z) (@sigma) (@hsigma) (@hAib) (@BToT) (@bothMissingB) (@transportBefore) (@S)
        (@hseq) (@hSB)
  have sigmaRoute :
      (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence sigma Tn T) ∨
      ((ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
          ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
        ∃ (f : E) (seed : TreeSequence G e0),
          ett.series.data.connectingEdges n = {f} ∧ TreeSequenceAdjoinEdge Tn f seed ∧
          TashkinovAugmentationSequence sigma seed T) := by
    exact @helper_sigmaRoute_993 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
        (@sigma) (@segTrans) (@commonPrefix) (@TnToA) (@habIndex) (@hAia) (@hAib)
        (@terminalRoute) (@BToT) (@AToB) (@transportRoute)
  have corrData (corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma T) :
      corr.replacementETT.series.data.tree
          (Fin.last corr.replacementETT.rounds).castSucc = Tn ∧
      corr.replacementETT.series.data.kind (Fin.last corr.replacementETT.rounds) =
          ett.series.data.kind n ∧
      TashkinovStoredColors corr.replacementETT.series.data
          (Fin.last corr.replacementETT.rounds) = Dn := by
    exact @helper_corrData_806 V E inferInstance inferInstance inferInstance inferInstance G k e0
        input T phi ett base C alpha beta sigma TnToA ha treeMissingEq corr
  have fullBase :
      ∃ corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma T,
        MaximumProperty corr.replacementETT ∧
        ∃ baseT : HierarchyBase corr.replacementETT sigma,
          baseT.core = base.core ∧ baseT.closure = base.closure := by
    exact @helper_fullBase_847 V E inferInstance inferInstance inferInstance inferInstance G k e0
        input T phi ett base C hproper hone hlower beta sigma hb sigmaProper sigmaOne combined
        hmod sigmaRoute corrData
  exact @helper_continuation_370 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
      (@hne) (@sigma) (@commonPrefix) (@equalTrees) (@lastPositive) (@coreToA) (@TnToA) (@AToT)
      (@ordinaryToA) (@starredToA) (@hAib) (@halphaA) (@hbetaA) (@missingSubset) (@hDn)
      (@terminalRoute) (@unaffected) (@missingUnaffected) (@missingA) (@treeMissingEq)
      (@closureInsideA) (@weak) (@hmod) (@transportBefore) (@corrData) (@fullBase)
end GoldbergSeymour.StableChangeCaseThreePreparation

end
