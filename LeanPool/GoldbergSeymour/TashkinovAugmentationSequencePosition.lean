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
    {V E : Type*} [Finite V] [Fintype E]
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
  let _ := Fintype.ofFinite V
  dsimp only
  let Bt := TreeSequencePrefix B t.val
    (le_trans A.positive hAt) (Nat.le_of_lt t.isLt)
  let Bt1 := TreeSequencePrefix B (t.val + 1)
    (by omega) (Nat.succ_le_of_lt t.isLt)
  have segmentRefl (X : TreeSequence G e0) :
      TreeSequenceInitialSegment X X :=
    ⟨le_rfl, (by intro i; rfl), (by intro i; rfl)⟩
  have segmentTrans {X Y Z : TreeSequence G e0}
      (hXY : TreeSequenceInitialSegment X Y)
      (hYZ : TreeSequenceInitialSegment Y Z) :
      TreeSequenceInitialSegment X Z := by
    rcases hXY with ⟨hxy, hvxy, hexy⟩
    rcases hYZ with ⟨hyz, hvyz, heyz⟩
    refine ⟨le_trans hxy hyz, ?_, ?_⟩
    · intro i
      have hmid := hvyz (Fin.castLE (Nat.succ_le_succ hxy) i)
      simpa using hmid.trans (hvxy i)
    · intro i
      have hmid := heyz (Fin.castLE hxy i)
      simpa using hmid.trans (hexy i)
  have commonPrefix {X Y Z : TreeSequence G e0}
      (hXZ : TreeSequenceInitialSegment X Z)
      (hYZ : TreeSequenceInitialSegment Y Z)
      (hXY : X.length ≤ Y.length) :
      TreeSequenceInitialSegment X Y := by
    rcases hXZ with ⟨hxz, hvxz, hexz⟩
    rcases hYZ with ⟨hyz, hvyz, heyz⟩
    refine ⟨hXY, ?_, ?_⟩
    · intro i
      calc
        Y.vertex (Fin.castLE (Nat.succ_le_succ hXY) i) =
            Z.vertex (Fin.castLE (Nat.succ_le_succ hyz)
              (Fin.castLE (Nat.succ_le_succ hXY) i)) :=
          (hvyz _).symm
        _ = Z.vertex (Fin.castLE (Nat.succ_le_succ hxz) i) := by
          congr 1
        _ = X.vertex i := hvxz i
    · intro i
      calc
        Y.edge (Fin.castLE hXY i) =
            Z.edge (Fin.castLE hyz (Fin.castLE hXY i)) :=
          (heyz _).symm
        _ = Z.edge (Fin.castLE hxz i) := by
          congr 1
        _ = X.edge i := hexz i
  have equalTrees {X Y : TreeSequence G e0}
      (hXY : TreeSequenceInitialSegment X Y)
      (hlen : X.length = Y.length) : X = Y := by
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
  have hAinitialB := TashkinovAugmentationSequenceInitialSegment phi A B hAB
  have hBtB : TreeSequenceInitialSegment Bt B := by
    refine ⟨Nat.le_of_lt t.isLt, ?_, ?_⟩
    · intro i
      simp [Bt, TreeSequencePrefix]
    · intro i
      simp [Bt, TreeSequencePrefix]
  have hBt1B : TreeSequenceInitialSegment Bt1 B := by
    refine ⟨Nat.succ_le_of_lt t.isLt, ?_, ?_⟩
    · intro i
      simp [Bt1, TreeSequencePrefix]
    · intro i
      simp [Bt1, TreeSequencePrefix]
  have hABt : TreeSequenceInitialSegment A Bt :=
    commonPrefix hAinitialB hBtB (by simpa [Bt, TreeSequencePrefix] using hAt)
  have hBtBt1 : TreeSequenceInitialSegment Bt Bt1 :=
    commonPrefix hBtB hBt1B (by simp [Bt, Bt1, TreeSequencePrefix])
  have hABt1 : TreeSequenceInitialSegment A Bt1 :=
    segmentTrans hABt hBtBt1
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
        have hXZeq : X = Z := equalTrees hprefix hZlen.symm
        subst Z
        exact hZY
  have hstep : TashkinovAugmentation phi Bt Bt1 :=
    oneStepOfLength hseq (by simp [Bt, Bt1, TreeSequencePrefix])
  refine ⟨hstep, ?_⟩
  change B.edge _ = B.edge t
  congr 1

end GoldbergSeymour

end
