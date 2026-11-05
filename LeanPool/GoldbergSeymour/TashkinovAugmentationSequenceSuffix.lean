/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequence
public import Mathlib.Data.Fintype.EquivFin

/-!
# Tashkinov Augmentation Sequence Suffix

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem TashkinovAugmentationSequenceSuffix
    {V E : Type*} [Finite V] [Fintype E]
    {G : LooplessMultigraph V E} {k : Nat} {e0 : E}
    (phi : PartialEdgeColoring E k) (S B C : TreeSequence G e0)
    (hSC : TashkinovAugmentationSequence phi S C)
    (hSB : TreeSequenceInitialSegment S B)
    (hBC : TreeSequenceInitialSegment B C) :
    TashkinovAugmentationSequence phi B C := by
  classical
  let _ := Fintype.ofFinite V
  have equalTrees {X Y : TreeSequence G e0}
      (hXY : TreeSequenceInitialSegment X Y)
      (hlen : X.length = Y.length) : X = Y := by
    rcases hXY with ⟨hle, hv, he⟩
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
          simpa only [Fin.castLE] using (hv i).symm
        · apply heq_of_eq
          funext i
          simpa only [Fin.castLE] using (he i).symm
  have commonPrefix {X Y Z : TreeSequence G e0}
      (hXZ : TreeSequenceInitialSegment X Z)
      (hYZ : TreeSequenceInitialSegment Y Z)
      (hXY : X.length ≤ Y.length) :
      TreeSequenceInitialSegment X Y := by
    rcases hXZ with ⟨hxz, hvx, hex⟩
    rcases hYZ with ⟨hyz, hvy, hey⟩
    refine ⟨hXY, ?_, ?_⟩
    · intro i
      calc
        Y.vertex (Fin.castLE (Nat.succ_le_succ hXY) i) =
            Z.vertex (Fin.castLE (Nat.succ_le_succ hyz)
              (Fin.castLE (Nat.succ_le_succ hXY) i)) := (hvy _).symm
        _ = Z.vertex (Fin.castLE (Nat.succ_le_succ hxz) i) := by congr 1
        _ = X.vertex i := hvx i
    · intro i
      calc
        Y.edge (Fin.castLE hXY i) =
            Z.edge (Fin.castLE hyz (Fin.castLE hXY i)) := (hey _).symm
        _ = Z.edge (Fin.castLE hxz i) := by congr 1
        _ = X.edge i := hex i
  unfold TashkinovAugmentationSequence at hSC ⊢
  induction hSC generalizing B with
  | refl =>
      have hlen : B.length = S.length := Nat.le_antisymm hBC.1 hSB.1
      have hBS : B = S := equalTrees hBC hlen
      subst B
      exact Relation.ReflTransGen.refl
  | @tail A C hSA hAC ih =>
      rcases hAC with ⟨hlen, hinitAC, hcolor⟩
      by_cases hBA : B.length ≤ A.length
      · have hBC' : TreeSequenceInitialSegment B A :=
          commonPrefix hBC hinitAC hBA
        exact Relation.ReflTransGen.tail
          (ih B hSB hBC') ⟨hlen, hinitAC, hcolor⟩
      · have hBlen : B.length = C.length := by
          rcases hBC with ⟨hBCle, _, _⟩
          omega
        have hBCeq : B = C := equalTrees hBC hBlen
        subst B
        exact Relation.ReflTransGen.refl

end GoldbergSeymour

end
