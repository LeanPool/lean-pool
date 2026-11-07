/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyNonparallelFirstEdge
public import LeanPool.GoldbergSeymour.HierarchySituationTwoReorderedTrees
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceRestrict
public import LeanPool.GoldbergSeymour.StableColoringIncidentEdgeCriterion
public import LeanPool.GoldbergSeymour.HierarchyBaseCorrespondingTransport
public import LeanPool.GoldbergSeymour.TreeSequenceAdjoinEdgeUnique
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentVertexSetSubset
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceInitialSegment
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceSuffix

/-!
# HierarchySituationTwoReorderedTreesCertified: supporting constructions, part 1

Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
This module separates dependent data constructors from their supporting proofs.
-/

@[expose] public section

namespace GoldbergSeymour.HierarchySituationTwoReorderedTreesCertifiedPreparation

/-- Dependent contract shared by the hierarchy construction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperContinuation891Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoTailData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
    let ell : ℕ := HierarchyFullTailLength C;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
    let P : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let _ : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    ∀ (_ : (
    ∀ (X : TreeSequence G e0), TreeSequenceInitialSegment X X)) (_ : (
    ∀ {X Y Z : TreeSequence G e0} (_ : TreeSequenceInitialSegment X Y) (_ :
        TreeSequenceInitialSegment Y Z), TreeSequenceInitialSegment X Z)) (_ : (
    ∀ {X Y Z : TreeSequence G e0} (_ : TreeSequenceInitialSegment X Z) (_ :
        TreeSequenceInitialSegment Y Z) (_ : X.length ≤ Y.length), TreeSequenceInitialSegment X
        Y)) (_ : (
    ∀ {X Y : TreeSequence G e0} (_ : TreeSequenceInitialSegment X Y) (_ : X.length = Y.length), X
        = Y)) (_ : (
    ∀ (X : TreeSequence G e0) (r : ℕ) (hr : (1 : ℕ) ≤ r) (hx : r ≤ X.length),
        TreeSequenceInitialSegment (TreeSequencePrefix X r hr hx) X)) (_ : (
    ∀ {X Y : TreeSequence G e0} (hXY : TreeSequenceInitialSegment X Y), X = TreeSequencePrefix Y
        X.length X.positive hXY.1)) (_ : (
    ∀ (a d : ℕ) (hbound : a + d ≤ H.dividerCount + (1 : ℕ)), TreeSequenceInitialSegment (H.stage
        (⟨a, Decidable.byContradiction fun (a_1 : ¬a < H.dividerCount + (2 : ℕ)) ↦
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) (H.stage (⟨a + d, Decidable.byContradiction fun (a_1 : ¬a
        + d < H.dividerCount + (2 : ℕ)) ↦
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))))) (_ : (
    ∀ (i : Fin (H.dividerCount + (2 : ℕ))), TreeSequenceInitialSegment (H.stage i) T)) (_ : (
    ∀ (_ : (0 : ℕ) < H.dividerCount), A = H.stage (⟨H.dividerCount, Decidable.byContradiction fun
        (a : ¬H.dividerCount < H.dividerCount + (2 : ℕ)) ↦
    by
          omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ))))) (_ : TreeSequenceInitialSegment A T) (_ :
        TreeSequenceInitialSegment base.core A) (_ : ell = T.length - A.length) (_ : (2 : ℕ) ≤
        ell) (_ : A.length ≤ T.length) (_ : B.length = T.length - (2 : ℕ)) (_ : P.length =
        T.length - (1 : ℕ)) (_ : (3 : ℕ) ≤ T.length) (_ : TreeSequenceInitialSegment B T),
    ∃ (R : HierarchySituationTwoReorderedTrees G k e0 input T phi ett base C ctx D),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ));
        (B = Tn → ett.series.data.kind n = some TashkinovExtensionKind.PE) ∧ (ett.series.data.kind
        n = some TashkinovExtensionKind.PE ∧ TashkinovAugmentationSequence phi Tn R.minus ∨
        (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨ ett.series.data.kind n = some
        TashkinovExtensionKind.RE) ∧
    ∃ (f : E) (seed : TreeSequence G e0), ett.series.data.connectingEdges n = { f } ∧
        TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence phi seed R.minus) ∧
        (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧ TashkinovAugmentationSequence
        phi Tn R.star ∨ (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
        ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
    ∃ (f : E) (seed : TreeSequence G e0), ett.series.data.connectingEdges n = { f } ∧
        TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence phi seed R.star) ∧
    ∃ (corrMinus : CorrespondingExtendedTashkinovTree G k e0 ett phi R.minus), MaximumProperty
        corrMinus.replacementETT ∧
    ∃ (baseMinus : HierarchyBase corrMinus.replacementETT phi), baseMinus.core = base.core ∧
        baseMinus.closure = base.closure ∧ (↑baseMinus.supportPosition : ℕ) =
        (↑base.supportPosition : ℕ) ∧
    ∃ (HMinus : TashkinovHierarchy corrMinus.replacementETT baseMinus) (hMinusCount :
        HMinus.dividerCount = C.hierarchy.dividerCount), (
    ∀ (j : Fin (HMinus.dividerCount + (1 : ℕ))), HMinus.stage j.castSucc = C.hierarchy.stage
        (Fin.cast (congrArg (fun (d : ℕ) ↦ d + (1 : ℕ)) hMinusCount) j).castSucc) ∧ (
    ∀ (j : Fin HMinus.dividerCount), (↑(HMinus.dividerPosition j) : ℕ) =
        (↑(C.hierarchy.dividerPosition (Fin.cast hMinusCount j)) : ℕ)) ∧
    ∃ (corrStar : CorrespondingExtendedTashkinovTree G k e0 ett phi R.star), MaximumProperty
        corrStar.replacementETT ∧
    ∃ (baseStar : HierarchyBase corrStar.replacementETT phi), baseStar.core = base.core ∧
        baseStar.closure = base.closure ∧ (↑baseStar.supportPosition : ℕ) = (↑base.supportPosition
        : ℕ) ∧
    ∃ (HStar : TashkinovHierarchy corrStar.replacementETT baseStar) (hStarCount :
        HStar.dividerCount = C.hierarchy.dividerCount), (
    ∀ (j : Fin (HStar.dividerCount + (1 : ℕ))), HStar.stage j.castSucc = C.hierarchy.stage
        (Fin.cast (congrArg (fun (d : ℕ) ↦ d + (1 : ℕ)) hStarCount) j).castSucc) ∧
    ∀ (j : Fin HStar.dividerCount), (↑(HStar.dividerPosition j) : ℕ) =
        (↑(C.hierarchy.dividerPosition (Fin.cast hStarCount j)) : ℕ)

/-- Dependent contract shared by the hierarchy construction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperContinuation941Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoTailData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
    let ell : ℕ := HierarchyFullTailLength C;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
    let P : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    ∀ (_ : (
    ∀ {X Y Z : TreeSequence G e0} (_ : TreeSequenceInitialSegment X Y) (_ :
        TreeSequenceInitialSegment Y Z), TreeSequenceInitialSegment X Z)) (_ : (
    ∀ {X Y Z : TreeSequence G e0} (_ : TreeSequenceInitialSegment X Z) (_ :
        TreeSequenceInitialSegment Y Z) (_ : X.length ≤ Y.length), TreeSequenceInitialSegment X
        Y)) (_ : (
    ∀ {X Y : TreeSequence G e0} (_ : TreeSequenceInitialSegment X Y) (_ : X.length = Y.length), X
        = Y)) (_ : (
    ∀ (X : TreeSequence G e0) (r : ℕ) (hr : (1 : ℕ) ≤ r) (hx : r ≤ X.length),
        TreeSequenceInitialSegment (TreeSequencePrefix X r hr hx) X)) (_ : (
    ∀ {X Y : TreeSequence G e0} (hXY : TreeSequenceInitialSegment X Y), X = TreeSequencePrefix Y
        X.length X.positive hXY.1)) (_ : (
    ∀ (a d : ℕ) (hbound : a + d ≤ H.dividerCount + (1 : ℕ)), TreeSequenceInitialSegment (H.stage
        (⟨a, Decidable.byContradiction fun (a_1 : ¬a < H.dividerCount + (2 : ℕ)) ↦
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) (H.stage (⟨a + d, Decidable.byContradiction fun (a_1 : ¬a
        + d < H.dividerCount + (2 : ℕ)) ↦
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))))) (_ : (
    ∀ (i : Fin (H.dividerCount + (2 : ℕ))), TreeSequenceInitialSegment (H.stage i) T)) (_ : (
    ∀ (_ : (0 : ℕ) < H.dividerCount), A = H.stage (⟨H.dividerCount, Decidable.byContradiction fun
        (a : ¬H.dividerCount < H.dividerCount + (2 : ℕ)) ↦
    by
          omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ))))) (_ : TreeSequenceInitialSegment base.core A) (_ :
        B.length = T.length - (2 : ℕ)) (_ : P.length = T.length - (1 : ℕ)) (hm : (3 : ℕ) ≤
        T.length) (_ : TreeSequenceInitialSegment B T) (_ : TreeSequenceInitialSegment P T) (_ :
        TreeSequenceInitialSegment B P) (_ : TreeSequenceInitialSegment A B) (_ :
        TreeSequenceInitialSegment Tn B),
    let r : Fin T.length := (⟨T.length - (2 : ℕ), Decidable.byContradiction fun (a : ¬T.length -
        (2 : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length);
    let f : E := T.edge r;
    let g : E := T.edge D.lastEdgeIndex;
    let y : V := T.vertex D.penultimateVertexIndex;
    let z : V := T.vertex D.terminalVertexIndex;
    ∀ (_ : (↑r : ℕ) + (2 : ℕ) = T.length) (_ : (↑D.lastEdgeIndex : ℕ) + (1 : ℕ) = T.length) (_ :
        (↑D.penultimateVertexIndex : ℕ) + (1 : ℕ) = T.length) (_ : (↑D.terminalVertexIndex : ℕ) =
        T.length) (_ : TreeSequenceAdjoinEdge B f P) (_ : TreeSequenceAdjoinEdge P g T) (_ :
        P.vertex (Fin.last P.length) = y) (_ : T.vertex (Fin.last T.length) = z) (_ : (
    ∀ (X : TreeSequence G e0) (i : Fin (X.length + (1 : ℕ))), X.vertex i ∈ TreeSequenceVertexSet
        X)) (_ : (
    ∀ {X U : TreeSequence G e0} {e : E} (_ : TreeSequenceAdjoinEdge X e U), TreeSequenceVertexSet
        U = insert (U.vertex (Fin.last U.length)) (TreeSequenceVertexSet X) ∧ TreeSequenceEdgeSet
        U = insert e (TreeSequenceEdgeSet X))) (_ : (
    ∀ {X U : TreeSequence G e0} {e : E} {v w : V} (_ : TreeSequenceAdjoinEdge X e U) (_ : v ∉
        TreeSequenceVertexSet X) (_ : w ∈ TreeSequenceVertexSet X) (_ : G.ends e = s(v, w)),
        U.vertex (Fin.last U.length) = v)) (_ : z ∉ TreeSequenceVertexSet B) (_ : y ∉
        TreeSequenceVertexSet B) (_ : y ≠ z) (ig : Fin ((↑D.lastEdgeIndex : ℕ) + (1 : ℕ))) (_ :
        G.ends (T.edge D.lastEdgeIndex) = s(T.vertex D.lastEdgeIndex.succ, T.vertex (ig.castLT
        (Nat.lt_trans ig.isLt (Nat.succ_lt_succ D.lastEdgeIndex.isLt))))) (_ : (↑ig : ℕ) <
        B.length + (1 : ℕ)),
    ∃ (R : HierarchySituationTwoReorderedTrees G k e0 input T phi ett base C ctx D),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ));
        (B = Tn → ett.series.data.kind n = some TashkinovExtensionKind.PE) ∧ (ett.series.data.kind
        n = some TashkinovExtensionKind.PE ∧ TashkinovAugmentationSequence phi Tn R.minus ∨
        (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨ ett.series.data.kind n = some
        TashkinovExtensionKind.RE) ∧
    ∃ (f : E) (seed : TreeSequence G e0), ett.series.data.connectingEdges n = { f } ∧
        TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence phi seed R.minus) ∧
        (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧ TashkinovAugmentationSequence
        phi Tn R.star ∨ (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
        ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
    ∃ (f : E) (seed : TreeSequence G e0), ett.series.data.connectingEdges n = { f } ∧
        TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence phi seed R.star) ∧
    ∃ (corrMinus : CorrespondingExtendedTashkinovTree G k e0 ett phi R.minus), MaximumProperty
        corrMinus.replacementETT ∧
    ∃ (baseMinus : HierarchyBase corrMinus.replacementETT phi), baseMinus.core = base.core ∧
        baseMinus.closure = base.closure ∧ (↑baseMinus.supportPosition : ℕ) =
        (↑base.supportPosition : ℕ) ∧
    ∃ (HMinus : TashkinovHierarchy corrMinus.replacementETT baseMinus) (hMinusCount :
        HMinus.dividerCount = C.hierarchy.dividerCount), (
    ∀ (j : Fin (HMinus.dividerCount + (1 : ℕ))), HMinus.stage j.castSucc = C.hierarchy.stage
        (Fin.cast (congrArg (fun (d : ℕ) ↦ d + (1 : ℕ)) hMinusCount) j).castSucc) ∧ (
    ∀ (j : Fin HMinus.dividerCount), (↑(HMinus.dividerPosition j) : ℕ) =
        (↑(C.hierarchy.dividerPosition (Fin.cast hMinusCount j)) : ℕ)) ∧
    ∃ (corrStar : CorrespondingExtendedTashkinovTree G k e0 ett phi R.star), MaximumProperty
        corrStar.replacementETT ∧
    ∃ (baseStar : HierarchyBase corrStar.replacementETT phi), baseStar.core = base.core ∧
        baseStar.closure = base.closure ∧ (↑baseStar.supportPosition : ℕ) = (↑base.supportPosition
        : ℕ) ∧
    ∃ (HStar : TashkinovHierarchy corrStar.replacementETT baseStar) (hStarCount :
        HStar.dividerCount = C.hierarchy.dividerCount), (
    ∀ (j : Fin (HStar.dividerCount + (1 : ℕ))), HStar.stage j.castSucc = C.hierarchy.stage
        (Fin.cast (congrArg (fun (d : ℕ) ↦ d + (1 : ℕ)) hStarCount) j).castSucc) ∧
    ∀ (j : Fin HStar.dividerCount), (↑(HStar.dividerPosition j) : ℕ) =
        (↑(C.hierarchy.dividerPosition (Fin.cast hStarCount j)) : ℕ)

theorem helper_adjoinSets_322.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (_ :
        HierarchySituationTwoTailData G k e0 input T phi ett base C ctx), (3 : ℕ) ≤ T.length →
    ∀ {X U : TreeSequence G e0} {e : E}, TreeSequenceAdjoinEdge X e U → TreeSequenceVertexSet U =
        insert (U.vertex (Fin.last U.length)) (TreeSequenceVertexSet X) ∧ TreeSequenceEdgeSet U =
        insert e (TreeSequenceEdgeSet X) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D hm X U e ha
  rcases ha with ⟨hl, hs, he⟩
  constructor
  · ext v
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and, Finset.mem_insert]
    constructor
    · rintro ⟨i, rfl⟩
      by_cases hi : i.val < X.length + 1
      · right
        exact ⟨⟨i.val, hi⟩, (hs.2.1 ⟨i.val, hi⟩).symm⟩
      · left
        congr 1
        apply Fin.ext
        simp
        omega
    · rintro (hv | ⟨i, rfl⟩)
      · exact ⟨Fin.last U.length, hv.symm⟩
      · exact ⟨Fin.castLE (Nat.succ_le_succ hs.1) i, hs.2.1 i⟩
  · ext e'
    simp only [TreeSequenceEdgeSet, Finset.mem_image, Finset.mem_univ,
      true_and, Finset.mem_insert]
    constructor
    · rintro ⟨i, rfl⟩
      by_cases hi : i.val < X.length
      · right
        exact ⟨⟨i.val, hi⟩, (hs.2.2 ⟨i.val, hi⟩).symm⟩
      · left
        have hi' : i = Fin.cast hl.symm (Fin.last X.length) := by
          apply Fin.ext
          simp
          omega
        exact hi' ▸ he
    · rintro (hv | ⟨i, rfl⟩)
      · exact ⟨Fin.cast hl.symm (Fin.last X.length), he.trans hv.symm⟩
      · exact ⟨Fin.castLE hs.1 i, hs.2.2 i⟩

theorem helper_stepRoute_542.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi), (
    ∀ (X : TreeSequence G e0) (colors : Finset (Fin k)) (old new : PartialEdgeColoring E k),
        IsProperEdgeColoring G old → IsOneEdgeUncolored old e0 → IsProperEdgeColoring G new →
        IsOneEdgeUncolored new e0 → StableColoring X colors old new → ColoredVertexSetClosed G old
        (TreeSequenceVertexSet X) → ColoredVertexSetClosed G new (TreeSequenceVertexSet X)) →
    ∀ (j : Fin (ett.rounds + (1 : ℕ))), j ≠ (0 : Fin (ett.rounds + (1 : ℕ))) →
        ett.series.data.kind j = some TashkinovExtensionKind.PE ∧ TashkinovAugmentationSequence
        (ett.series.data.coloring j) (ett.series.data.tree j.castSucc) (ett.series.data.tree
        j.succ) ∨ (ett.series.data.kind j = some TashkinovExtensionKind.SE ∨ ett.series.data.kind
        j = some TashkinovExtensionKind.RE) ∧ ColoredVertexSetClosed G (ett.series.data.coloring
        j) (TreeSequenceVertexSet (ett.series.data.tree j.castSucc)) ∧
    ∃ (e : E) (seed : TreeSequence G e0), ett.series.data.connectingEdges j = { e } ∧
        TreeSequenceAdjoinEdge (ett.series.data.tree j.castSucc) e seed ∧
        TashkinovAugmentationSequence (ett.series.data.coloring j) seed (ett.series.data.tree
        j.succ) := by
  classical
  intro V E _ _ _ G k e0 input T phi ett stableClosed j hj
  cases ett.series.certified j with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure => exact False.elim (hj rfl)
  | SE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    refine Or.inr ⟨Or.inl currentKind, ?_, choice.edge, adjoined,
      currentEdges, adjoinedExactly, closedExtension.1⟩
    rw [currentColoring]
    exact stableClosed _ _ _ _ previousProper previousOneUncolored
      choice.selectedProper choice.selectedOneUncolored
      choice.selectedStable previousClosed
  | PE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper
      secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma closedExtension orderedExtension strictExtension =>
    exact Or.inl ⟨currentKind, closedExtension.1⟩
  | RE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    refine Or.inr ⟨Or.inr currentKind, ?_, available.edge, adjoined,
      currentEdges, adjoinedExactly, closedExtension.1⟩
    rw [currentColoring]
    exact previousClosed

theorem helper_routes_692.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoTailData G k e0 input T phi ett base C ctx),
    let ell : ℕ := HierarchyFullTailLength C;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
    let P : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    ∀ (_ : (
    ∀ {X Y Z : TreeSequence G e0} (_ : TreeSequenceInitialSegment X Y) (_ :
        TreeSequenceInitialSegment Y Z), TreeSequenceInitialSegment X Z)) (_ : (
    ∀ {X Y Z : TreeSequence G e0} (_ : TreeSequenceInitialSegment X Z) (_ :
        TreeSequenceInitialSegment Y Z) (_ : X.length ≤ Y.length), TreeSequenceInitialSegment X
        Y)) (_ : (
    ∀ {X Y : TreeSequence G e0} (_ : TreeSequenceInitialSegment X Y) (_ : X.length = Y.length), X
        = Y)) (_ : B.length = T.length - (2 : ℕ)) (_ : P.length = T.length - (1 : ℕ)) (hm : (3 :
        ℕ) ≤ T.length) (_ : TreeSequenceInitialSegment B T) (_ : TreeSequenceInitialSegment P T)
        (_ : TreeSequenceInitialSegment B P) (_ : TreeSequenceInitialSegment Tn B),
    let r : Fin T.length := (⟨T.length - (2 : ℕ), Decidable.byContradiction fun (a : ¬T.length -
        (2 : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length);
    let f : E := T.edge r;
    let g : E := T.edge D.lastEdgeIndex;
    ∀ (_ : (↑r : ℕ) + (2 : ℕ) = T.length) (_ : (↑D.lastEdgeIndex : ℕ) + (1 : ℕ) = T.length) (_ :
        (↑D.penultimateVertexIndex : ℕ) + (1 : ℕ) = T.length) (_ : (↑D.terminalVertexIndex : ℕ) =
        T.length) (_ : TreeSequenceAdjoinEdge B f P) (_ : Fin ((↑D.lastEdgeIndex : ℕ) + (1 : ℕ)))
        (M : TreeSequence G e0) (_ : TreeSequenceAdjoinEdge B g M) (_ : Fin ((↑r : ℕ) + (1 : ℕ)))
        (S : TreeSequence G e0) (_ : TreeSequenceAdjoinEdge M f S) (_ : TreeSequenceEdgeSet P =
        insert f (TreeSequenceEdgeSet B)),
    let Z : TreeSequence G e0 := ett.series.data.tree n.succ;
    ∀ (_ : TreeSequenceInitialSegment T Z) (_ : n ≠ (0 : Fin (ett.rounds + (1 : ℕ)))) (_ :
        (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧ TashkinovAugmentationSequence
        phi Tn Z ∨ (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨ ett.series.data.kind
        n = some TashkinovExtensionKind.RE) ∧ ColoredVertexSetClosed G phi (TreeSequenceVertexSet
        Tn) ∧
    ∃ (e : E) (seed : TreeSequence G e0), ett.series.data.connectingEdges n = { e } ∧
        TreeSequenceAdjoinEdge Tn e seed ∧ TashkinovAugmentationSequence phi seed Z)) (_ : (
    ∀ (e : E) (seed : TreeSequence G e0) (_ : ett.series.data.kind n = some
        TashkinovExtensionKind.SE ∨ ett.series.data.kind n = some TashkinovExtensionKind.RE) (_ :
        ett.series.data.connectingEdges n = { e }) (_ : TreeSequenceAdjoinEdge Tn e seed),
        TreeSequenceInitialSegment seed T)) (_ : (
    ∀ {X Y : TreeSequence G e0} (_ : TashkinovAugmentationSequence phi X Y) (_ : Y.length =
        X.length + (1 : ℕ)), TashkinovAugmentation phi X Y)) (_ : (
    ∀ (_ : B = Tn), ett.series.data.kind n = some TashkinovExtensionKind.PE)) (_ : (
    ∀ {X U : TreeSequence G e0} {e : E} {c : Fin k} (_ : TreeSequenceAdjoinEdge X e U) (_ : phi e
        = some c) (_ : c ∈ TreeMissingColors phi X), TashkinovAugmentation phi X U)) (_ :
        TashkinovAugmentation phi B M), (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence phi Tn M ∨ (ett.series.data.kind n = some
        TashkinovExtensionKind.SE ∨ ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
    ∃ (e : E) (seed : TreeSequence G e0), ett.series.data.connectingEdges n = { e } ∧
        TreeSequenceAdjoinEdge Tn e seed ∧ TashkinovAugmentationSequence phi seed M) ∧
        (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧ TashkinovAugmentationSequence
        phi Tn S ∨ (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨ ett.series.data.kind
        n = some TashkinovExtensionKind.RE) ∧
    ∃ (e : E) (seed : TreeSequence G e0), ett.series.data.connectingEdges n = { e } ∧
        TreeSequenceAdjoinEdge Tn e seed ∧ TashkinovAugmentationSequence phi seed S) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D ell B P n Tn segmentTrans commonPrefix
      equalTrees hBlen hPlen hm hBT hPT hBP hTnB r f g hr hgpos hypos hzpos hOrigP ig M hBM if_ S
      hMS hPE Z hTZ hnzero terminalRoute seedToT oneStep hboundaryPE augmentOfAdjoin hBMaug
  have extendRoute (source : TreeSequence G e0)
      (hsourceB : TreeSequenceInitialSegment source B)
      (hseqT : TashkinovAugmentationSequence phi source T) :
      TashkinovAugmentationSequence phi source M ∧
        TashkinovAugmentationSequence phi source S := by
    have hseqB := TashkinovAugmentationSequenceRestrict phi source B T hseqT hsourceB hBT
    have hseqBT := TashkinovAugmentationSequenceSuffix phi source B T hseqT hsourceB hBT
    have hseqBP := TashkinovAugmentationSequenceRestrict phi B P T hseqBT hBP hPT
    have hBPaug := oneStep hseqBP (by omega)
    rcases hBPaug with ⟨hl, hs, c, he, hc⟩
    have hef : P.edge (Fin.cast hl.symm (Fin.last B.length)) = f := hOrigP.choose_spec.2
    have hcM : c ∈ TreeMissingColors phi M := by
      obtain ⟨v, hv, hmissing⟩ := Finset.mem_biUnion.mp hc
      exact Finset.mem_biUnion.mpr
        ⟨v, TreeSequenceInitialSegmentVertexSetSubset hBM.choose_spec.1 hv, hmissing⟩
    have hMSaug := augmentOfAdjoin hMS (hef ▸ he) hcM
    have hseqM : TashkinovAugmentationSequence phi source M :=
      Relation.ReflTransGen.tail hseqB hBMaug
    exact ⟨hseqM, Relation.ReflTransGen.tail hseqM hMSaug⟩
  rcases terminalRoute with ⟨hp, hseq⟩ | ⟨hk, hc, e, seed, he, ha, hseq⟩
  · have hseqT := TashkinovAugmentationSequenceRestrict phi Tn T Z hseq
      (segmentTrans hTnB hBT) hTZ
    obtain ⟨hm, hs⟩ := extendRoute Tn hTnB hseqT
    exact ⟨Or.inl ⟨hp, hm⟩, Or.inl ⟨hp, hs⟩⟩
  · have hBN : B ≠ Tn := by
      intro hBN
      have hPE := hboundaryPE hBN
      rcases hk with hk | hk <;> rw [hk] at hPE <;> cases hPE
    have hstrict : Tn.length < B.length := by
      have hle := hTnB.1
      by_contra hn
      exact hBN (equalTrees hTnB (by omega)).symm
    have hseedT := seedToT e seed hk he ha
    have hseedB := commonPrefix hseedT hBT (by have := ha.1; omega)
    have hseqT := TashkinovAugmentationSequenceRestrict phi seed T Z hseq hseedT hTZ
    obtain ⟨hm, hs⟩ := extendRoute seed hseedB hseqT
    exact ⟨Or.inr ⟨hk, e, seed, he, ha, hm⟩, Or.inr ⟨hk, e, seed, he, ha, hs⟩⟩

theorem helper_copyHierarchy_812.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoTailData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
    let ell : ℕ := HierarchyFullTailLength C;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    ∀ (_ : (
    ∀ {X Y Z : TreeSequence G e0} (_ : TreeSequenceInitialSegment X Y) (_ :
        TreeSequenceInitialSegment Y Z), TreeSequenceInitialSegment X Z)) (_ : (
    ∀ {X Y : TreeSequence G e0} (hXY : TreeSequenceInitialSegment X Y), X = TreeSequencePrefix Y
        X.length X.positive hXY.1)) (_ : TreeSequenceInitialSegment base.core A) (_ : B.length =
        T.length - (2 : ℕ)) (hm : (3 : ℕ) ≤ T.length) (_ : TreeSequenceInitialSegment A B),
    let r : Fin T.length := (⟨T.length - (2 : ℕ), Decidable.byContradiction fun (a : ¬T.length -
        (2 : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length);
    ∀ (_ : Fin ((↑D.lastEdgeIndex : ℕ) + (1 : ℕ))) (M : TreeSequence G e0) (_ : Fin ((↑r : ℕ) + (1
        : ℕ))) (S : TreeSequence G e0) (_ : M.length = B.length + (1 : ℕ)) (_ : S.length =
        M.length + (1 : ℕ)) (_ : TreeSequenceInitialSegment (H.stage (Fin.last
        H.dividerCount).castSucc) B) (_ : (
    ∀ (i : Fin (H.dividerCount + (1 : ℕ))), TreeSequenceInitialSegment (H.stage i.castSucc) B)) (_
        : (
    ∀ (X : TreeSequence G e0) (corr : CorrespondingExtendedTashkinovTree G k e0 ett phi X),
        corr.replacementETT.series.data.tree (Fin.last corr.replacementETT.rounds).castSucc = Tn))
        (X : TreeSequence G e0) (corr : CorrespondingExtendedTashkinovTree G k e0 ett phi X) (_ :
        TreeSequenceInitialSegment B X) (_ : B.length < X.length),
    ∃ (bx : HierarchyBase corr.replacementETT phi), bx.core = base.core ∧ bx.closure =
        base.closure ∧ (↑bx.supportPosition : ℕ) = (↑base.supportPosition : ℕ) ∧
    ∃ (K : TashkinovHierarchy corr.replacementETT bx) (hcount : K.dividerCount = H.dividerCount),
        (
    ∀ (j : Fin (K.dividerCount + (1 : ℕ))), K.stage j.castSucc = H.stage (Fin.cast (congrArg (fun
        (d : ℕ) ↦ d + (1 : ℕ)) hcount) j).castSucc) ∧
    ∀ (j : Fin K.dividerCount), (↑(K.dividerPosition j) : ℕ) = (↑(H.dividerPosition (Fin.cast
        hcount j)) : ℕ) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H A ell B n Tn segmentTrans prefixEq
      hcoreA hBlen hm hAB r ig M if_ S hMlen hSlen hlastB hstageB terminalTree X corr hBX hstrictBX
  -- Transport the base, then retain every stage and divider before the new terminal tree.
  obtain ⟨bx, hcore, hclosure, hsupport⟩ :=
    HierarchyBaseCorrespondingTransport G k e0 input T X phi ett corr base
  let stages : Fin (H.dividerCount + 2) → TreeSequence G e0 :=
    fun i => if hi : i.val < H.dividerCount + 1 then H.stage ⟨i.val, by omega⟩ else X
  have stagesOld (i : Fin (H.dividerCount + 1)) :
      stages i.castSucc = H.stage i.castSucc := by
    simp only [stages, Fin.val_castSucc, dite_eq_left i.isLt]
    congr 1
  have stagesLast : stages (Fin.last (H.dividerCount + 1)) = X := by
    simp [stages]
  have oldStageLength (i : Fin H.dividerCount) :
      (H.stage i.succ.castSucc).length = (H.dividerPosition i).val := by
    have hd := H.dividerStage i
    have hi : (⟨i.val + 1, by omega⟩ : Fin (H.dividerCount + 2)) = i.succ.castSucc := by
      apply Fin.ext
      rfl
    rw [hi] at hd
    exact congrArg TreeSequence.length hd
  have positionB (i : Fin H.dividerCount) : (H.dividerPosition i).val ≤ B.length := by
    rw [← oldStageLength i]
    exact (hstageB i.succ).1
  let positions : Fin H.dividerCount → Fin (X.length + 1) :=
    fun i => ⟨(H.dividerPosition i).val, by have := positionB i; omega⟩
  let K : TashkinovHierarchy corr.replacementETT bx := by
    exact {
      dividerCount := H.dividerCount
      stage := stages
      baseStage := by
        have h0 := stagesOld (0 : Fin (H.dividerCount + 1))
        have hi : (0 : Fin (H.dividerCount + 1)).castSucc =
            (0 : Fin (H.dividerCount + 2)) := by apply Fin.ext; rfl
        rw [hi] at h0
        rw [h0, H.baseStage, terminalTree X corr]
      terminalStage := stagesLast
      nested := by
        intro j
        by_cases hj : j.val < H.dividerCount
        · let i : Fin (H.dividerCount + 1) := ⟨j.val + 1, by omega⟩
          have hi : i.castSucc = j.succ := by apply Fin.ext; rfl
          rw [stagesOld j, ← hi, stagesOld i]
          exact H.nested j
        · have hjlast : j = Fin.last H.dividerCount := by
            apply Fin.ext
            simp
            omega
          have hnext : j.succ = Fin.last (H.dividerCount + 1) := by
            apply Fin.ext
            simp
            omega
          rw [stagesOld j, hnext, stagesLast, hjlast]
          exact segmentTrans hlastB hBX
      strict := by
        intro j
        by_cases hj : j.val < H.dividerCount
        · let i : Fin (H.dividerCount + 1) := ⟨j.val + 1, by omega⟩
          have hi : i.castSucc = j.succ := by apply Fin.ext; rfl
          rw [stagesOld j, ← hi, stagesOld i]
          exact H.strict j
        · have hjlast : j = Fin.last H.dividerCount := by
            apply Fin.ext
            simp
            omega
          have hnext : j.succ = Fin.last (H.dividerCount + 1) := by
            apply Fin.ext
            simp
            omega
          rw [stagesOld j, hnext, stagesLast, hjlast]
          exact lt_of_le_of_lt hlastB.1 hstrictBX
      dividerPosition := positions
      dividerPositive := H.dividerPositive
      dividerIncreasing := H.dividerIncreasing
      dividerStage := by
        intro i
        have hi : (⟨i.val + 1, by omega⟩ : Fin (H.dividerCount + 2)) = i.succ.castSucc := by
          apply Fin.ext
          rfl
        rw [hi, stagesOld i.succ]
        have hstageX := segmentTrans (hstageB i.succ) hBX
        have hp := prefixEq hstageX
        simpa only [oldStageLength i] using hp
      coreInsideFirst := by
        rw [hcore]
        by_cases hq : H.dividerCount = 0
        · have hi : (⟨1, by omega⟩ : Fin (H.dividerCount + 2)) =
              Fin.last (H.dividerCount + 1) := by apply Fin.ext; simp [hq]
          rw [hi, stagesLast]
          exact segmentTrans hcoreA (segmentTrans hAB hBX)
        · let i : Fin (H.dividerCount + 1) := ⟨1, by omega⟩
          have hi : i.castSucc = (⟨1, by omega⟩ : Fin (H.dividerCount + 2)) := by
            apply Fin.ext
            rfl
          rw [← hi, stagesOld i]
          exact H.coreInsideFirst }
  refine ⟨bx, hcore, hclosure, hsupport, K, rfl, ?_, ?_⟩
  · intro j
    exact stagesOld j
  · intro j
    rfl

theorem helper_seedToT_936.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoTailData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let ell : ℕ := HierarchyFullTailLength C;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    ∀ (_ : (
    ∀ {X Y Z : TreeSequence G e0} (_ : TreeSequenceInitialSegment X Y) (_ :
        TreeSequenceInitialSegment Y Z), TreeSequenceInitialSegment X Z)) (_ : (
    ∀ {X Y Z : TreeSequence G e0} (_ : TreeSequenceInitialSegment X Z) (_ :
        TreeSequenceInitialSegment Y Z) (_ : X.length ≤ Y.length), TreeSequenceInitialSegment X
        Y)) (_ : (
    ∀ (X : TreeSequence G e0) (r : ℕ) (hr : (1 : ℕ) ≤ r) (hx : r ≤ X.length),
        TreeSequenceInitialSegment (TreeSequencePrefix X r hr hx) X)) (_ : (
    ∀ (i : Fin (H.dividerCount + (2 : ℕ))), TreeSequenceInitialSegment (H.stage i) T)) (hm : (3 :
        ℕ) ≤ T.length) (_ : TreeSequenceInitialSegment B T) (_ : TreeSequenceInitialSegment Tn B),
    let r : Fin T.length := (⟨T.length - (2 : ℕ), Decidable.byContradiction fun (a : ¬T.length -
        (2 : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length);
    ∀ (_ : (↑r : ℕ) + (2 : ℕ) = T.length) (_ : (↑D.lastEdgeIndex : ℕ) + (1 : ℕ) = T.length) (_ :
        (↑D.penultimateVertexIndex : ℕ) + (1 : ℕ) = T.length) (_ : (↑D.terminalVertexIndex : ℕ) =
        T.length) (_ : Fin ((↑D.lastEdgeIndex : ℕ) + (1 : ℕ))) (_ : Fin ((↑r : ℕ) + (1 : ℕ))) (e :
        E) (seed : TreeSequence G e0) (_ : ett.series.data.kind n = some TashkinovExtensionKind.SE
        ∨ ett.series.data.kind n = some TashkinovExtensionKind.RE) (_ :
        ett.series.data.connectingEdges n = { e }) (_ : TreeSequenceAdjoinEdge Tn e seed),
        TreeSequenceInitialSegment seed T := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H ell B n Tn segmentTrans commonPrefix
      prefixSegment stageToT hm hBT hTnB r hr hgpos hypos hzpos ig if_ e seed hkind he ha
  obtain ⟨ie, hie, hentry⟩ := HierarchyNonparallelFirstEdge H e hkind he
  change ie.val = Tn.length at hie
  have ht := stageToT (⟨1, by omega⟩ : Fin (H.dividerCount + 2))
  have hentryT : T.edge (Fin.castLE ht.1 ie) = e :=
    (ht.2.2 ie).trans hentry
  have hN : Tn.length < T.length := by
    have hlt := ie.isLt
    have hle := ht.1
    omega
  let Q := TreeSequencePrefix T (Tn.length + 1) (by omega) (by omega)
  have hQT : TreeSequenceInitialSegment Q T := prefixSegment _ _ _ _
  have hNQ : TreeSequenceInitialSegment Tn Q :=
    commonPrefix (segmentTrans hTnB hBT) hQT (by change Tn.length ≤ Tn.length + 1; omega)
  have hQ : TreeSequenceAdjoinEdge Tn e Q := by
    refine ⟨rfl, hNQ, ?_⟩
    change T.edge _ = e
    convert hentryT using 1
    congr 1
    apply Fin.ext
    exact hie.symm
  have hseed : seed = Q := TreeSequenceAdjoinEdgeUnique Tn e seed Q ha hQ
  rw [hseed]
  exact hQT

theorem helper_equalTrees_631.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
        {X Y : TreeSequence G e0}, TreeSequenceInitialSegment X Y → X.length = Y.length → X = Y
  := by
  classical
  intro V E G e0 X Y hXY hlen
  cases X with
  | mk lx px vx ex vix eix fx ax =>
    cases Y with
    | mk ly py vy ey viy eiy fy ay =>
      simp only at hlen
      subst ly
      rw [TreeSequence.mk.injEq]
      refine ⟨rfl, ?_, ?_⟩
      · apply heq_of_eq
        funext i
        simpa only [Fin.castLE] using (hXY.2.1 i).symm
      · apply heq_of_eq
        funext i
        simpa only [Fin.castLE] using (hXY.2.2 i).symm

theorem helper_hAstage_679.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
    ∀ (_ : (0 : ℕ) < H.dividerCount), A = H.stage (⟨H.dividerCount, Decidable.byContradiction fun
        (a : ¬H.dividerCount < H.dividerCount + (2 : ℕ)) ↦
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ))) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H A hq
  have hi : (Fin.last H.dividerCount : Fin (H.dividerCount + 1)) =
      (⟨H.dividerCount - 1, by omega⟩ : Fin H.dividerCount).succ := by
    apply Fin.ext
    simp
    omega
  dsimp [A, HierarchyStarredStage]
  rw [hi]
  simp only [Fin.cases]
  apply congrArg H.stage
  apply Fin.ext
  simp
  omega

theorem helper_stableClosed_938.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (X : TreeSequence G e0) (colors : Finset (Fin k)) (old new : PartialEdgeColoring
        E k), IsProperEdgeColoring G old → IsOneEdgeUncolored old e0 → IsProperEdgeColoring G new
        → IsOneEdgeUncolored new e0 → StableColoring X colors old new → ColoredVertexSetClosed G
        old (TreeSequenceVertexSet X) → ColoredVertexSetClosed G new (TreeSequenceVertexSet X) := by
  classical
  intro V E _ _ G k e0 X colors old new ho huo hn hun hstable hclosed e c v he hv hc hmissing
  have hmold : c ∈ MissingColors G old v := by
    rw [← hstable.2 v hv]
    exact hmissing
  have hmTree : c ∈ TreeMissingColors old X := by
    simp only [TreeMissingColors, Finset.mem_biUnion]
    exact ⟨v, hv, hmold⟩
  obtain ⟨u, hu, w, hw, hends⟩ := by
    simpa only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
      true_and] using he
  have hinc : TreeIncidentEdge X e := by
    refine ⟨u, hu, ?_⟩
    change u ∈ G.ends e
    rw [hends]
    exact Sym2.mem_iff.mpr (Or.inl rfl)
  have heq := (sc1 G e0 X colors old new ho huo hn hun).mp hstable e hinc
    (Or.inr ⟨c, Finset.mem_union_left _ hmTree, hc⟩)
  exact hclosed he hv (heq.symm.trans hc) hmold

theorem helper_hfinalAug_1019.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoTailData G k e0 input T phi ett base C ctx),
    let ell : ℕ := HierarchyFullTailLength C;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
    let P : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    ∀ (_ : (
    ∀ {X Y Z : TreeSequence G e0} (_ : TreeSequenceInitialSegment X Y) (_ :
        TreeSequenceInitialSegment Y Z), TreeSequenceInitialSegment X Z)) (_ : (
    ∀ {X Y Z : TreeSequence G e0} (_ : TreeSequenceInitialSegment X Z) (_ :
        TreeSequenceInitialSegment Y Z) (_ : X.length ≤ Y.length), TreeSequenceInitialSegment X
        Y)) (_ : B.length = T.length - (2 : ℕ)) (_ : P.length = T.length - (1 : ℕ)) (hm : (3 : ℕ)
        ≤ T.length) (_ : TreeSequenceInitialSegment B T) (_ : TreeSequenceInitialSegment P T) (_ :
        TreeSequenceInitialSegment B P) (_ : TreeSequenceInitialSegment Tn B),
    let r : Fin T.length := (⟨T.length - (2 : ℕ), Decidable.byContradiction fun (a : ¬T.length -
        (2 : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length);
    ∀ (_ : (↑r : ℕ) + (2 : ℕ) = T.length) (_ : (↑D.lastEdgeIndex : ℕ) + (1 : ℕ) = T.length) (_ :
        (↑D.penultimateVertexIndex : ℕ) + (1 : ℕ) = T.length) (_ : (↑D.terminalVertexIndex : ℕ) =
        T.length) (_ : Fin ((↑D.lastEdgeIndex : ℕ) + (1 : ℕ))) (_ : Fin ((↑r : ℕ) + (1 : ℕ))),
    let Z : TreeSequence G e0 := ett.series.data.tree n.succ;
    ∀ (_ : TreeSequenceInitialSegment T Z) (_ : n ≠ (0 : Fin (ett.rounds + (1 : ℕ)))) (_ :
        (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧ TashkinovAugmentationSequence
        phi Tn Z ∨ (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨ ett.series.data.kind
        n = some TashkinovExtensionKind.RE) ∧ ColoredVertexSetClosed G phi (TreeSequenceVertexSet
        Tn) ∧
    ∃ (e : E) (seed : TreeSequence G e0), ett.series.data.connectingEdges n = { e } ∧
        TreeSequenceAdjoinEdge Tn e seed ∧ TashkinovAugmentationSequence phi seed Z)) (_ : (
    ∀ (e : E) (seed : TreeSequence G e0) (_ : ett.series.data.kind n = some
        TashkinovExtensionKind.SE ∨ ett.series.data.kind n = some TashkinovExtensionKind.RE) (_ :
        ett.series.data.connectingEdges n = { e }) (_ : TreeSequenceAdjoinEdge Tn e seed),
        TreeSequenceInitialSegment seed T)) (_ : (
    ∀ {X Y : TreeSequence G e0} (_ : TashkinovAugmentationSequence phi X Y) (_ : Y.length =
        X.length + (1 : ℕ)), TashkinovAugmentation phi X Y)), TashkinovAugmentation phi P T := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D ell B P n Tn segmentTrans commonPrefix
      hBlen hPlen hm hBT hPT hBP hTnB r hr hgpos hypos hzpos ig if_ Z hTZ hnzero terminalRoute
      seedToT oneStep
  rcases terminalRoute with ⟨hp, hseq⟩ | ⟨hk, hc, e, seed, he, ha, hseq⟩
  · have hNT := segmentTrans hTnB hBT
    have hseqT := TashkinovAugmentationSequenceRestrict phi Tn T Z hseq hNT hTZ
    have hseqP := TashkinovAugmentationSequenceSuffix phi Tn P T hseqT
      (segmentTrans hTnB hBP) hPT
    exact oneStep hseqP (by omega)
  · have hseedT := seedToT e seed hk he ha
    have hseqT := TashkinovAugmentationSequenceRestrict phi seed T Z hseq hseedT hTZ
    have hseedP : TreeSequenceInitialSegment seed P :=
      commonPrefix hseedT hPT (by have := ha.1; have := hTnB.1; omega)
    have hseqP := TashkinovAugmentationSequenceSuffix phi seed P T hseqT hseedP hPT
    exact oneStep hseqP (by omega)

theorem helper_hgends_1058.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoTailData G k e0 input T phi ett base C ctx),
    let ell : ℕ := HierarchyFullTailLength C;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
    ∀ (hm : (3 : ℕ) ≤ T.length), TreeSequenceInitialSegment B T →
    let r : Fin T.length := (⟨T.length - (2 : ℕ),
    by
        have := GoldbergSeymour.TreeSequence.positive T
        omega
    ⟩ : Fin T.length);
    let g : E := T.edge D.lastEdgeIndex;
    let z : V := T.vertex D.terminalVertexIndex; (↑r : ℕ) + (2 : ℕ) = T.length → (↑D.lastEdgeIndex
        : ℕ) + (1 : ℕ) = T.length → (↑D.penultimateVertexIndex : ℕ) + (1 : ℕ) = T.length →
        (↑D.terminalVertexIndex : ℕ) = T.length →
    ∀ (ig : Fin ((↑D.lastEdgeIndex : ℕ) + (1 : ℕ))), G.ends (T.edge D.lastEdgeIndex) = s(T.vertex
        D.lastEdgeIndex.succ, T.vertex (ig.castLT (
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ))) →
    ∀ (higbound : (↑ig : ℕ) < B.length + (1 : ℕ)),
    let igB : Fin (B.length + (1 : ℕ)) := (⟨(↑ig : ℕ), higbound⟩ : Fin (B.length + (1 : ℕ)));
        G.ends g = s(z, B.vertex igB) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D ell B hm hBT r g z hr hgpos hypos hzpos
      ig hig higbound igB
  have hnew : D.lastEdgeIndex.succ = D.terminalVertexIndex := by
    apply Fin.ext
    simp
    omega
  rw [← hBT.2.1 igB]
  convert hig using 1
  · exact congrArg (fun i =>
      s(T.vertex i, T.vertex (Fin.castLE (Nat.succ_le_succ hBT.1) igB))) hnew.symm

theorem helper_hfends_1083.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoTailData G k e0 input T phi ett base C ctx),
    let ell : ℕ := HierarchyFullTailLength C;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
    ∀ (hm : (3 : ℕ) ≤ T.length), TreeSequenceInitialSegment B T →
    let r : Fin T.length := (⟨T.length - (2 : ℕ),
    by
        have := GoldbergSeymour.TreeSequence.positive T
        omega
    ⟩ : Fin T.length);
    let f : E := T.edge r;
    let y : V := T.vertex D.penultimateVertexIndex; (↑r : ℕ) + (2 : ℕ) = T.length →
        (↑D.lastEdgeIndex : ℕ) + (1 : ℕ) = T.length → (↑D.penultimateVertexIndex : ℕ) + (1 : ℕ) =
        T.length →
    ∀ (_ : Fin ((↑D.lastEdgeIndex : ℕ) + (1 : ℕ))) (if_ : Fin ((↑r : ℕ) + (1 : ℕ))), G.ends
        (T.edge r) = s(T.vertex r.succ, T.vertex (if_.castLT (
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ))) →
    ∀ (hifbound : (↑if_ : ℕ) < B.length + (1 : ℕ)),
    let ifB : Fin (B.length + (1 : ℕ)) := (⟨(↑if_ : ℕ), hifbound⟩ : Fin (B.length + (1 : ℕ)));
        G.ends f = s(y, B.vertex ifB) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D ell B hm hBT r f y hr hgpos hypos ig if_
      hif hifbound ifB
  have hnew : r.succ = D.penultimateVertexIndex := by
    apply Fin.ext
    simp
    omega
  rw [← hBT.2.1 ifB]
  convert hif using 1
  · exact congrArg (fun i =>
      s(T.vertex i, T.vertex (Fin.castLE (Nat.succ_le_succ hBT.1) ifB))) hnew.symm

theorem helper_hfB_1110.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoTailData G k e0 input T phi ett base C ctx),
    let ell : ℕ := HierarchyFullTailLength C;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ)); B.length = T.length -
        (2 : ℕ) →
    ∀ (hm : (3 : ℕ) ≤ T.length), TreeSequenceInitialSegment B T →
    let r : Fin T.length := (⟨T.length - (2 : ℕ),
    by
        have := GoldbergSeymour.TreeSequence.positive T
        omega
    ⟩ : Fin T.length);
    let f : E := T.edge r; (↑r : ℕ) + (2 : ℕ) = T.length → (↑D.lastEdgeIndex : ℕ) + (1 : ℕ) =
        T.length → (↑D.penultimateVertexIndex : ℕ) + (1 : ℕ) = T.length → (↑D.terminalVertexIndex
        : ℕ) = T.length →
    ∀ (_ : Fin ((↑D.lastEdgeIndex : ℕ) + (1 : ℕ))) (_ : Fin ((↑r : ℕ) + (1 : ℕ))), f ∉
        TreeSequenceEdgeSet B := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D ell B hBlen hm hBT r f hr hgpos hypos
      hzpos ig if_ hf
  obtain ⟨i, hi⟩ := by simpa [TreeSequenceEdgeSet] using hf
  have hidx := congrArg Fin.val (T.edge_injective ((hBT.2.2 i).trans hi))
  simp only [Fin.val_castLE] at hidx
  omega

theorem helper_branch_1137.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoTailData G k e0 input T phi ett base C ctx),
    let ell : ℕ := HierarchyFullTailLength C;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
    let y : V := T.vertex D.penultimateVertexIndex;
    let z : V := T.vertex D.terminalVertexIndex; y ∉ TreeSequenceVertexSet B → y ≠ z →
    ∀ (v : V), v = z ∨ v ∈ TreeSequenceVertexSet B → (v = z ∨ v = y ∨ v ∈ TreeSequenceVertexSet B)
        ∧ ¬v = T.vertex D.penultimateVertexIndex := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D ell B y z hyB hyz v hv
  refine ⟨hv.elim Or.inl (fun h => Or.inr (Or.inr h)), ?_⟩
  intro hh
  change v = y at hh
  rcases hv with hv | hv
  · exact hyz (hh.symm.trans hv)
  · exact hyB (hh ▸ hv)

theorem helper_branch_1144.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoTailData G k e0 input T phi ett base C ctx),
    let ell : ℕ := HierarchyFullTailLength C;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
    let y : V := T.vertex D.penultimateVertexIndex;
    let z : V := T.vertex D.terminalVertexIndex;
    ∀ (v : V), (v = z ∨ v = y ∨ v ∈ TreeSequenceVertexSet B) ∧ ¬v = T.vertex
        D.penultimateVertexIndex → v = z ∨ v ∈ TreeSequenceVertexSet B := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D ell B y z v
  rintro ⟨hv, hn⟩
  rcases hv with hv | hv | hv
  · exact Or.inl hv
  · exact False.elim (hn hv)
  · exact Or.inr hv

theorem helper_branch_1154.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoTailData G k e0 input T phi ett base C ctx),
    let ell : ℕ := HierarchyFullTailLength C;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
    ∀ (hm : (3 : ℕ) ≤ T.length),
    let r : Fin T.length := (⟨T.length - (2 : ℕ),
    by
        have := GoldbergSeymour.TreeSequence.positive T
        omega
    ⟩ : Fin T.length);
    let f : E := T.edge r;
    let g : E := T.edge D.lastEdgeIndex; f ∉ TreeSequenceEdgeSet B → f ≠ g →
    ∀ (e : E), e = g ∨ e ∈ TreeSequenceEdgeSet B → (e = g ∨ e = f ∨ e ∈ TreeSequenceEdgeSet B) ∧
        ¬e = T.edge r := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D ell B hm r f g hfB hfg e he
  refine ⟨he.elim Or.inl (fun h => Or.inr (Or.inr h)), ?_⟩
  intro hh
  change e = f at hh
  rcases he with he | he
  · exact hfg (hh.symm.trans he)
  · exact hfB (hh ▸ he)

theorem helper_branch_1161.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoTailData G k e0 input T phi ett base C ctx),
    let ell : ℕ := HierarchyFullTailLength C;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
    ∀ (hm : (3 : ℕ) ≤ T.length),
    let r : Fin T.length := (⟨T.length - (2 : ℕ),
    by
        have := GoldbergSeymour.TreeSequence.positive T
        omega
    ⟩ : Fin T.length);
    let f : E := T.edge r;
    let g : E := T.edge D.lastEdgeIndex;
    ∀ (e : E), (e = g ∨ e = f ∨ e ∈ TreeSequenceEdgeSet B) ∧ ¬e = T.edge r → e = g ∨ e ∈
        TreeSequenceEdgeSet B := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D ell B hm r f g e
  rintro ⟨he, hn⟩
  rcases he with he | he | he
  · exact Or.inl he
  · exact False.elim (hn he)
  · exact Or.inr he

theorem helper_hnzero_1202.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoTailData G k e0 input T phi ett base C ctx),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    ∀ (hm : (3 : ℕ) ≤ T.length),
    let r : Fin T.length := (⟨T.length - (2 : ℕ),
    by
        have := GoldbergSeymour.TreeSequence.positive T
        omega
    ⟩ : Fin T.length);
    ∀ (_ : Fin ((↑D.lastEdgeIndex : ℕ) + (1 : ℕ))) (_ : Fin ((↑r : ℕ) + (1 : ℕ))), n ≠ (0 : Fin
        (ett.rounds + (1 : ℕ))) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D n hm r ig if_ hn
  have hv := congrArg Fin.val hn
  have hp := C.positive
  simp [n] at hv
  omega

theorem helper_oneStep_1228.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoTailData G k e0 input T phi ett base C ctx), (
    ∀ {X Y : TreeSequence G e0}, TreeSequenceInitialSegment X Y → X.length = Y.length → X = Y) →
    ∀ (hm : (3 : ℕ) ≤ T.length),
    let r : Fin T.length := (⟨T.length - (2 : ℕ),
    by
        have := GoldbergSeymour.TreeSequence.positive T
        omega
    ⟩ : Fin T.length);
    ∀ (_ : Fin ((↑D.lastEdgeIndex : ℕ) + (1 : ℕ))) (_ : Fin ((↑r : ℕ) + (1 : ℕ)))
        {X Y : TreeSequence G e0}, TashkinovAugmentationSequence phi X Y → Y.length = X.length +
        (1 : ℕ) → TashkinovAugmentation phi X Y := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D equalTrees hm r ig if_ X Y hseq hlen
  unfold TashkinovAugmentationSequence at hseq
  induction hseq with
  | refl => omega
  | @tail W Y hXW hWY ih =>
    have hp := TashkinovAugmentationSequenceInitialSegment phi X W hXW
    have hwlen : X.length = W.length := by have := hWY.1; have := hp.1; omega
    have heq := equalTrees hp hwlen
    subst W
    exact hWY

theorem helper_hthetaP_1244.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoTailData G k e0 input T phi ett base C ctx),
    let ell : ℕ := HierarchyFullTailLength C;
    let P : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
    let g : E := T.edge D.lastEdgeIndex; TreeSequenceAdjoinEdge P g T → TashkinovAugmentation phi
        P T → D.theta ∈ TreeMissingColors phi P := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D ell P g hOrigT hfinalAug
  rcases hfinalAug with ⟨hl, hs, c, he, hc⟩
  have heg : T.edge (Fin.cast hl.symm (Fin.last P.length)) = g := hOrigT.choose_spec.2
  rw [heg, D.thetaOnLastEdge] at he
  have hct : D.theta = c := Option.some.inj he
  exact hct.symm ▸ hc

theorem helper_hthetaB_1250.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoTailData G k e0 input T phi ett base C ctx),
    let ell : ℕ := HierarchyFullTailLength C;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
    let P : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
    let y : V := T.vertex D.penultimateVertexIndex; TreeSequenceVertexSet P = (insert y
        (TreeSequenceVertexSet B) : Finset V) → D.theta ∈ TreeMissingColors phi P → D.theta ∈
        TreeMissingColors phi B := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D ell B P y hPV hthetaP
  obtain ⟨v, hv, hc⟩ := Finset.mem_biUnion.mp hthetaP
  rw [hPV] at hv
  rcases Finset.mem_insert.mp hv with hv | hv
  · subst v
    exact False.elim (D.thetaPresentPenultimate hc)
  · exact Finset.mem_biUnion.mpr ⟨v, hv, hc⟩

theorem helper_hboundaryPE_1258.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoTailData G k e0 input T phi ett base C ctx),
    let ell : ℕ := HierarchyFullTailLength C;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let g : E := T.edge D.lastEdgeIndex; g ∈ BoundaryEdges G (TreeSequenceVertexSet B) →
    let Z : TreeSequence G e0 := ett.series.data.tree n.succ; (ett.series.data.kind n = some
        TashkinovExtensionKind.PE ∧ TashkinovAugmentationSequence phi Tn Z ∨ (ett.series.data.kind
        n = some TashkinovExtensionKind.SE ∨ ett.series.data.kind n = some
        TashkinovExtensionKind.RE) ∧ ColoredVertexSetClosed G phi (TreeSequenceVertexSet Tn) ∧
    ∃ (e : E) (seed : TreeSequence G e0), ett.series.data.connectingEdges n = ({ e } : Finset E) ∧
        TreeSequenceAdjoinEdge Tn e seed ∧ TashkinovAugmentationSequence phi seed Z) → D.theta ∈
        TreeMissingColors phi B → B = Tn → ett.series.data.kind n = some TashkinovExtensionKind.PE
  := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D ell B n Tn g hgBoundary Z terminalRoute
      hthetaB hBN
  rcases terminalRoute with ⟨hp, hseq⟩ | ⟨hk, hc, e, seed, he, ha, hseq⟩
  · exact hp
  · obtain ⟨v, hv, hmissing⟩ := Finset.mem_biUnion.mp hthetaB
    rw [← hBN] at hc
    exact False.elim (hc hgBoundary hv D.thetaOnLastEdge hmissing)

theorem helper_hlastB_1310.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoTailData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
    let ell : ℕ := HierarchyFullTailLength C;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc; ((0 : ℕ) < H.dividerCount → A =
        H.stage (⟨H.dividerCount,
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) →
    ∀ (hm : (3 : ℕ) ≤ T.length), TreeSequenceInitialSegment A B → TreeSequenceInitialSegment Tn B
        →
    let r : Fin T.length := (⟨T.length - (2 : ℕ),
    by
        have := GoldbergSeymour.TreeSequence.positive T
        omega
    ⟩ : Fin T.length);
    ∀ (_ : Fin ((↑D.lastEdgeIndex : ℕ) + (1 : ℕ))) (_ : TreeSequence G e0) (_ : Fin ((↑r : ℕ) + (1
        : ℕ))) (_ : TreeSequence G e0), TreeSequenceInitialSegment (H.stage (Fin.last
        H.dividerCount).castSucc) B := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H A ell B n Tn hAstage hm hAB hTnB r ig M
      if_ S
  by_cases hq : H.dividerCount = 0
  · have hi : (Fin.last H.dividerCount).castSucc =
        (0 : Fin (H.dividerCount + 2)) := by
      apply Fin.ext
      simp [hq]
    rw [hi, H.baseStage]
    exact hTnB
  · have hi : (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + 2)) =
        (Fin.last H.dividerCount).castSucc := by apply Fin.ext; rfl
    rw [← hi, ← hAstage (by omega)]
    exact hAB

theorem helper_hstageB_1323.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoTailData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let ell : ℕ := HierarchyFullTailLength C;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ)); (
    ∀ {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Y → TreeSequenceInitialSegment Y Z
        → TreeSequenceInitialSegment X Z) → (
    ∀ (a d : ℕ) (hbound : a + d ≤ H.dividerCount + (1 : ℕ)), TreeSequenceInitialSegment (H.stage
        (⟨a,
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) (H.stage (⟨a + d,
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ))))) →
    ∀ (hm : (3 : ℕ) ≤ T.length),
    let r : Fin T.length := (⟨T.length - (2 : ℕ),
    by
        have := GoldbergSeymour.TreeSequence.positive T
        omega
    ⟩ : Fin T.length);
    ∀ (_ : Fin ((↑D.lastEdgeIndex : ℕ) + (1 : ℕ))) (_ : TreeSequence G e0) (_ : Fin ((↑r : ℕ) + (1
        : ℕ))) (_ : TreeSequence G e0), TreeSequenceInitialSegment (H.stage (Fin.last
        H.dividerCount).castSucc) B →
    ∀ (i : Fin (H.dividerCount + (1 : ℕ))), TreeSequenceInitialSegment (H.stage i.castSucc) B := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H ell B segmentTrans stageSegment hm r ig
      M if_ S hlastB i
  have hs := stageSegment i.val (H.dividerCount - i.val) (by omega)
  have hfirst : (⟨i.val, by omega⟩ : Fin (H.dividerCount + 2)) = i.castSucc := by
    apply Fin.ext
    rfl
  have hlast : (⟨i.val + (H.dividerCount - i.val), by omega⟩ :
      Fin (H.dividerCount + 2)) = (Fin.last H.dividerCount).castSucc := by
    apply Fin.ext
    simp
    omega
  rw [hfirst, hlast] at hs
  exact segmentTrans hs hlastB

/-- Typed data construction shared by the hierarchy construction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
noncomputable abbrev helperR1556.{u_1, u_2} :
    open scoped Classical in
      {V : Type u_1} →
  {E : Type u_2} →
  [ Fintype V] →
  [ Fintype E] →
  [ DecidableEq V] →
  [ DecidableEq E] →
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
      HierarchySituationTwoTailData G k e0 input T phi ett base
        C ctx) →
  let ell : ℕ := HierarchyFullTailLength C;
  let B : TreeSequence G e0 :=
    HierarchyFullTailPrefix C (ell - (2 : ℕ));
  let P : TreeSequence G e0 :=
    HierarchyFullTailPrefix C (ell - (1 : ℕ));
  (hm : (3 : ℕ) ≤ T.length) →
  let r : Fin T.length :=
    (⟨T.length - (2 : ℕ),
        by
        have := GoldbergSeymour.TreeSequence.positive T
        have := GoldbergSeymour.TreeSequence.positive T
        omega⟩ :
      Fin T.length);
  let f : E := T.edge r;
  let g : E := T.edge D.lastEdgeIndex;
  let y : V := T.vertex D.penultimateVertexIndex;
  let z : V := T.vertex D.terminalVertexIndex;
  (↑r : ℕ) + (2 : ℕ) = T.length →
  TreeSequenceAdjoinEdge B f P →
  TreeSequenceAdjoinEdge P g T →
  (∀ {X U : TreeSequence G e0} {e : E},
      TreeSequenceAdjoinEdge X e U →
        TreeSequenceVertexSet U =
            (insert (U.vertex (Fin.last U.length))
                (TreeSequenceVertexSet X) :
              Finset V) ∧
          TreeSequenceEdgeSet U =
            (insert e (TreeSequenceEdgeSet X) :
              Finset E)) →
  y ∉ TreeSequenceVertexSet B →
  y ≠ z →
  (M : TreeSequence G e0) →
  TreeSequenceAdjoinEdge B g M →
  M.vertex (Fin.last M.length) = z →
  TreeSequenceVertexSet M =
      (insert z
          (TreeSequenceVertexSet B) :
        Finset V) →
  TreeSequenceEdgeSet M =
      (insert g
          (TreeSequenceEdgeSet B) :
        Finset E) →
  (S : TreeSequence G e0) →
  TreeSequenceAdjoinEdge M f S →
  S.vertex (Fin.last S.length) =
      y →
  TreeSequenceVertexSet T =
      (insert z
          (insert y
              (TreeSequenceVertexSet
                B) :
            Finset V) :
        Finset V) →
  TreeSequenceEdgeSet T =
      (insert g
          (insert f
              (TreeSequenceEdgeSet
                B) :
            Finset E) :
        Finset E) →
  f ∉
      TreeSequenceEdgeSet
        B →
  f ≠ g →
  HierarchySituationTwoReorderedTrees
    G k e0 input T phi
    ett base C ctx D := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D ell B P hm r f g y z hr hOrigP hOrigT
      adjoinSets hyB hyz M hBM hMz hMV hME S hMS hSy hTV hTE hfB hfg
  exact {
    penultimateEdgeIndex := r
    penultimateEdgePosition := hr
    minus := M
    star := S
    originalPenultimate := hOrigP
    originalFinal := hOrigT
    minusFinal := hBM
    minusTerminalVertex := hMz
    starFinal := hMS
    starPenultimateVertex := hSy
    minusVertexSet := by
      rw [hMV, hTV]
      ext v
      simp only [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_insert]
      constructor
      · exact helper_branch_1137 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
          (@D)
          (@hyB) (@hyz) (@v)
      · exact helper_branch_1144 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
          (@D) (@v)
    minusEdgeSet := by
      rw [hME, hTE]
      ext e
      simp only [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_insert]
      constructor
      · exact helper_branch_1154 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
          (@D)
          (@hm) (@hfB) (@hfg) (@e)
      · exact helper_branch_1161 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
          (@D)
          (@hm) (@e)
    starVertexSet := by
      rw [(adjoinSets hMS).1, hSy, hMV, hTV]
      exact Finset.insert_comm _ _ _
    starEdgeSet := by
      rw [(adjoinSets hMS).2, hME, hTE]
      exact Finset.insert_comm _ _ _ }

end GoldbergSeymour.HierarchySituationTwoReorderedTreesCertifiedPreparation

end
