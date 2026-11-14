/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceInitialSegment
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceRestrict
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceSuffix
public import LeanPool.GoldbergSeymour.TreeSequencePrefix

/-!
# Tashkinov Augmentation Sequence Position

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem TashkinovAugmentationSequencePosition
    {V E : Type*} [Fintype E]
    {G : LooplessMultigraph V E} {k : Nat} {e0 : E}
    (phi : PartialEdgeColoring E k) (A B : TreeSequence G e0)
    (hAB : TashkinovAugmentationSequence phi A B)
    (t : Fin B.length) (hAt : A.length ≤ t.val) :
    let Bt := TreeSequencePrefix B t.val
      (le_trans A.positive hAt) (Nat.le_of_lt t.isLt)
    let Bt1 := TreeSequencePrefix B (t.val + 1)
      (by omega) (Nat.succ_le_of_lt t.isLt)
    TashkinovAugmentation phi Bt Bt1 ∧
      Bt1.edge (Fin.last t.val) = B.edge t := by
  classical
  dsimp only
  let Bt := TreeSequencePrefix B t.val
    (le_trans A.positive hAt) (Nat.le_of_lt t.isLt)
  let Bt1 := TreeSequencePrefix B (t.val + 1)
    (by omega) (Nat.succ_le_of_lt t.isLt)
  have hAinitialB := TashkinovAugmentationSequenceInitialSegment phi A B hAB
  have hBtB : TreeSequenceInitialSegment Bt B :=
    TreeSequenceInitialSegment.prefix_segment B t.val
      (le_trans A.positive hAt) (Nat.le_of_lt t.isLt)
  have hBt1B : TreeSequenceInitialSegment Bt1 B :=
    TreeSequenceInitialSegment.prefix_segment B (t.val + 1)
      (by omega) (Nat.succ_le_of_lt t.isLt)
  have hABt : TreeSequenceInitialSegment A Bt :=
    hBtB.of_common_extension hAinitialB (by simpa [Bt, TreeSequencePrefix] using hAt)
  have hBtBt1 : TreeSequenceInitialSegment Bt Bt1 :=
    hBt1B.of_common_extension hBtB (by simp [Bt, Bt1, TreeSequencePrefix])
  have hABt1 : TreeSequenceInitialSegment A Bt1 :=
    hABt.trans hBtBt1
  have hseqABt1 : TashkinovAugmentationSequence phi A Bt1 :=
    TashkinovAugmentationSequenceRestrict phi A Bt1 B hAB hABt1 hBt1B
  have hseq : TashkinovAugmentationSequence phi Bt Bt1 :=
    TashkinovAugmentationSequenceSuffix phi A Bt Bt1 hseqABt1 hABt hBtBt1
  have oneStepOfLength {X Y : TreeSequence G e0}
      (hseqXY : TashkinovAugmentationSequence phi X Y)
      (hlenXY : Y.length = X.length + 1) :
      TashkinovAugmentation phi X Y := by
    unfold TashkinovAugmentationSequence at hseqXY
    induction hseqXY with
    | refl => omega
    | @tail Z Y hXZ hZY ih =>
        have hprefix :=
          TashkinovAugmentationSequenceInitialSegment phi X Z hXZ
        have hZlen : Z.length = X.length := by
          rcases hZY with ⟨hlen, hsegment, hcolor⟩
          have hle := hprefix.1
          omega
        have hXZeq : X = Z := hprefix.eq_of_length_eq hZlen.symm
        subst Z
        exact hZY
  have hstep : TashkinovAugmentation phi Bt Bt1 :=
    oneStepOfLength hseq (by simp [Bt, Bt1, TreeSequencePrefix])
  refine ⟨hstep, ?_⟩
  change B.edge _ = B.edge t
  congr 1

end GoldbergSeymour

end
