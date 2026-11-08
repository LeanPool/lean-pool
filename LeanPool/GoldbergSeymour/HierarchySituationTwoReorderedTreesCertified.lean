/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyTreeFacts

public import LeanPool.GoldbergSeymour.HierarchySituationTwoReorderedTreesCertified.Preparation2
public import LeanPool.GoldbergSeymour.HierarchySituationTwoReorderedTrees
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentFacts

/-!
# Hierarchy Situation Two Reordered Trees Certified

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open HierarchySituationTwoReorderedTreesCertifiedPreparation

theorem HierarchySituationTwoReorderedTreesCertified {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (D : HierarchySituationTwoTailData
      G k e0 input T phi ett base C ctx) :
    ∃ R : HierarchySituationTwoReorderedTrees
        G k e0 input T phi ett base C ctx D,
      let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
      let Tn := ett.series.data.tree n.castSucc
      let B := HierarchyFullTailPrefix C (HierarchyFullTailLength C - 2)
      (B = Tn →
          ett.series.data.kind n = some TashkinovExtensionKind.PE) ∧
        ((ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
            TashkinovAugmentationSequence phi Tn R.minus) ∨
          ((ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
              ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
            ∃ (f : E) (seed : TreeSequence G e0),
              ett.series.data.connectingEdges n = {f} ∧
                TreeSequenceAdjoinEdge Tn f seed ∧
                TashkinovAugmentationSequence phi seed R.minus)) ∧
        ((ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
            TashkinovAugmentationSequence phi Tn R.star) ∨
          ((ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
              ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
            ∃ (f : E) (seed : TreeSequence G e0),
              ett.series.data.connectingEdges n = {f} ∧
                TreeSequenceAdjoinEdge Tn f seed ∧
                TashkinovAugmentationSequence phi seed R.star)) ∧
        ∃ corrMinus : CorrespondingExtendedTashkinovTree
            G k e0 ett phi R.minus,
          MaximumProperty corrMinus.replacementETT ∧
            ∃ baseMinus : HierarchyBase corrMinus.replacementETT phi,
              baseMinus.core = base.core ∧
                baseMinus.closure = base.closure ∧
                baseMinus.supportPosition.val = base.supportPosition.val ∧
                ∃ HMinus : TashkinovHierarchy
                    corrMinus.replacementETT baseMinus,
                  ∃ hMinusCount :
                      HMinus.dividerCount = C.hierarchy.dividerCount,
                    (∀ j : Fin (HMinus.dividerCount + 1),
                        HMinus.stage j.castSucc =
                          C.hierarchy.stage
                            (Fin.cast
                              (congrArg (fun d => d + 1) hMinusCount) j).castSucc) ∧
                      (∀ j : Fin HMinus.dividerCount,
                        (HMinus.dividerPosition j).val =
                          (C.hierarchy.dividerPosition
                            (Fin.cast hMinusCount j)).val) ∧
                      ∃ corrStar : CorrespondingExtendedTashkinovTree
                          G k e0 ett phi R.star,
                        MaximumProperty corrStar.replacementETT ∧
                          ∃ baseStar : HierarchyBase
                              corrStar.replacementETT phi,
                            baseStar.core = base.core ∧
                              baseStar.closure = base.closure ∧
                              baseStar.supportPosition.val =
                                base.supportPosition.val ∧
                              ∃ HStar : TashkinovHierarchy
                                  corrStar.replacementETT baseStar,
                                ∃ hStarCount :
                                    HStar.dividerCount =
                                      C.hierarchy.dividerCount,
                                  (∀ j : Fin (HStar.dividerCount + 1),
                                      HStar.stage j.castSucc =
                                        C.hierarchy.stage
                                          (Fin.cast
                                            (congrArg (fun d => d + 1)
                                              hStarCount) j).castSucc) ∧
                                    ∀ j : Fin HStar.dividerCount,
                                      (HStar.dividerPosition j).val =
                                        (C.hierarchy.dividerPosition
                                          (Fin.cast hStarCount j)).val := by
  classical
  let H := C.hierarchy
  let A := HierarchyStarredStage H (Fin.last H.dividerCount)
  let ell := HierarchyFullTailLength C
  let B := HierarchyFullTailPrefix C (ell - 2)
  let P := HierarchyFullTailPrefix C (ell - 1)
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn := ett.series.data.tree n.castSucc
  -- Exact ordered prefixes will be used for both route restriction and hierarchy copying.
  have segmentRefl (X : TreeSequence G e0) : TreeSequenceInitialSegment X X :=
    ⟨le_rfl, (fun _ => rfl), (fun _ => rfl)⟩
  have segmentTrans {X Y Z : TreeSequence G e0}
      (hXY : TreeSequenceInitialSegment X Y)
      (hYZ : TreeSequenceInitialSegment Y Z) :
      TreeSequenceInitialSegment X Z := by
    exact hXY.trans hYZ
  have commonPrefix {X Y Z : TreeSequence G e0}
      (hXZ : TreeSequenceInitialSegment X Z)
      (hYZ : TreeSequenceInitialSegment Y Z) (hXY : X.length ≤ Y.length) :
      TreeSequenceInitialSegment X Y := by
    refine ⟨hXY, ?_, ?_⟩
    · intro i
      have hv := hYZ.2.1 (Fin.castLE (Nat.succ_le_succ hXY) i)
      exact hv.symm.trans (by simpa using hXZ.2.1 i)
    · intro i
      have he := hYZ.2.2 (Fin.castLE hXY i)
      exact he.symm.trans (by simpa using hXZ.2.2 i)
  have equalTrees {X Y : TreeSequence G e0}
      (hXY : TreeSequenceInitialSegment X Y) (hlen : X.length = Y.length) :
      X = Y := by
    exact helper_equalTrees_631 G e0 hXY hlen
  have prefixSegment (X : TreeSequence G e0) (r : ℕ)
      (hr : 1 ≤ r) (hx : r ≤ X.length) :
      TreeSequenceInitialSegment (TreeSequencePrefix X r hr hx) X :=
    ⟨hx, (fun _ => rfl), (fun _ => rfl)⟩
  have prefixEq {X Y : TreeSequence G e0}
      (hXY : TreeSequenceInitialSegment X Y) :
      X = TreeSequencePrefix Y X.length X.positive hXY.1 := by
    apply equalTrees
      (commonPrefix hXY (prefixSegment Y X.length X.positive hXY.1) le_rfl)
    rfl
  have stageSegment : ∀ (a d : ℕ) (hbound : a + d ≤ H.dividerCount + 1),
      TreeSequenceInitialSegment (H.stage ⟨a, by omega⟩)
        (H.stage ⟨a + d, by omega⟩) := by
    intro a d bound
    exact H.stageInitialSegmentOfLE _ _ (by change a ≤ a + d; exact Nat.le_add_right _ _)
  have stageToT (i : Fin (H.dividerCount + 2)) :
      TreeSequenceInitialSegment (H.stage i) T := by
    have hs := stageSegment i.val (H.dividerCount + 1 - i.val) (by omega)
    have hi : (⟨i.val + (H.dividerCount + 1 - i.val), by omega⟩ :
        Fin (H.dividerCount + 2)) = Fin.last (H.dividerCount + 1) := by
      apply Fin.ext
      simp
      omega
    simpa [hi, H.terminalStage] using hs
  have hAstage (hq : 0 < H.dividerCount) :
      A = H.stage ⟨H.dividerCount, by omega⟩ := by
    exact helper_hAstage_679 G k e0 input T phi ett base C hq
  have hAcore (hq : H.dividerCount = 0) : A = base.core := by
    simp [A, HierarchyStarredStage, Fin.last, hq]
  have hAT : TreeSequenceInitialSegment A T := by
    by_cases hq : H.dividerCount = 0
    · rw [hAcore hq]
      exact segmentTrans H.coreInsideFirst (stageToT _)
    · rw [hAstage (by omega)]
      exact stageToT _
  have hcoreA : TreeSequenceInitialSegment base.core A := by
    by_cases hq : H.dividerCount = 0
    · rw [hAcore hq]; exact segmentRefl _
    · rw [hAstage (by omega)]
      exact segmentTrans H.coreInsideFirst
        (by
          convert stageSegment 1 (H.dividerCount - 1) (by omega) using 1
          congr 1
          apply Fin.ext
          simp
          omega)
  have hell : ell = T.length - A.length := rfl
  have htwo : 2 ≤ ell := D.tailAtLeastTwo
  have hAlen : A.length ≤ T.length := hAT.1
  have hBlen : B.length = T.length - 2 := by
    change min (A.length + (ell - 2)) T.length = T.length - 2
    omega
  have hPlen : P.length = T.length - 1 := by
    change min (A.length + (ell - 1)) T.length = T.length - 1
    omega
  have hm : 3 ≤ T.length := by have := A.positive; omega
  have hBT : TreeSequenceInitialSegment B T := prefixSegment _ _ _ _
  apply helper_continuation_891 <;> assumption
end GoldbergSeymour

end
