/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequence
public import Mathlib.Data.Fintype.EquivFin

/-!
# Tashkinov Augmentation Sequence Initial Segment

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem TashkinovAugmentationSequenceInitialSegment
    {V E : Type*} [Finite V] [Fintype E]
    {G : LooplessMultigraph V E} {k : Nat} {e0 : E}
    (phi : PartialEdgeColoring E k) (A B : TreeSequence G e0)
    (hAB : TashkinovAugmentationSequence phi A B) :
    TreeSequenceInitialSegment A B := by
  classical
  let _ := Fintype.ofFinite V
  unfold TashkinovAugmentationSequence at hAB
  induction hAB with
  | refl =>
      exact ⟨le_rfl, (fun _ => rfl), (fun _ => rfl)⟩
  | @tail B C hAB hBC ih =>
      rcases hBC with ⟨hlenEq, hsegBC, _⟩
      rcases ih with ⟨hlenAB, hvertexAB, hedgeAB⟩
      rcases hsegBC with ⟨hlenBC, hvertexBC, hedgeBC⟩
      refine ⟨Nat.le_trans hlenAB hlenBC, ?_, ?_⟩
      · intro i
        calc
          C.vertex (Fin.castLE
              (Nat.succ_le_succ (Nat.le_trans hlenAB hlenBC)) i) =
              C.vertex (Fin.castLE (Nat.succ_le_succ hlenBC)
                (Fin.castLE (Nat.succ_le_succ hlenAB) i)) := by congr 1
          _ = B.vertex (Fin.castLE (Nat.succ_le_succ hlenAB) i) :=
            hvertexBC _
          _ = A.vertex i := hvertexAB i
      · intro i
        calc
          C.edge (Fin.castLE (Nat.le_trans hlenAB hlenBC) i) =
              C.edge (Fin.castLE hlenBC (Fin.castLE hlenAB i)) := by congr 1
          _ = B.edge (Fin.castLE hlenAB i) := hedgeBC _
          _ = A.edge i := hedgeAB i

end GoldbergSeymour

end
