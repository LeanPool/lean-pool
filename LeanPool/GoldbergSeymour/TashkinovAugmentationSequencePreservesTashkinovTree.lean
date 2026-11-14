/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequence
public import LeanPool.GoldbergSeymour.TashkinovTree
public import Mathlib.Data.Fintype.EquivFin

/-!
# Tashkinov Augmentation Sequence Preserves Tashkinov Tree

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem TashkinovAugmentationSequencePreservesTashkinovTree
    {V E : Type*} [Finite V] [Fintype E]
    (G : LooplessMultigraph V E) {k : ℕ} (e0 : E)
    (phi : PartialEdgeColoring E k) (T T' : TreeSequence G e0)
    (hT : TashkinovTree G e0 phi T)
    (hseq : TashkinovAugmentationSequence phi T T') :
    TashkinovTree G e0 phi T' := by
  classical
  let _ := Fintype.ofFinite V
  unfold TashkinovAugmentationSequence at hseq
  induction hseq using Relation.ReflTransGen.head_induction_on with
  | refl => exact hT
  | @head A B hstep hreach ih =>
      apply ih
      rcases hstep with ⟨hlen, hinit, c, hedge, hc⟩
      rcases hinit with ⟨hle, hvertices, hedges⟩
      intro j hj
      by_cases hold : j.val < A.length
      · let jA : Fin A.length := ⟨j.val, hold⟩
        rcases hT jA hj with ⟨i, d, hcolor, hmissing⟩
        refine ⟨i, d, ?_, ?_⟩
        · have hjeq : Fin.castLE hle jA = j := Fin.ext rfl
          rw [← hjeq, hedges]
          exact hcolor
        · let qA : Fin (A.length + 1) :=
            Fin.castLT i (Nat.lt_trans i.isLt (Nat.succ_lt_succ jA.isLt))
          have hqeq : Fin.castLE (Nat.succ_le_succ hle) qA =
              Fin.castLT i
                (Nat.lt_trans i.isLt (Nat.succ_lt_succ j.isLt)) := Fin.ext rfl
          rw [← hqeq, hvertices]
          exact hmissing
      · have hjval : j.val = A.length := by omega
        rw [TreeMissingColors] at hc
        rcases Finset.mem_biUnion.mp hc with ⟨v, hv, hcv⟩
        rw [TreeSequenceVertexSet] at hv
        rcases Finset.mem_image.mp hv with ⟨q, _, hq⟩
        let i : Fin (j.val + 1) := ⟨q.val, by omega⟩
        refine ⟨i, c, ?_, ?_⟩
        · have hjlast :
              j = Fin.cast hlen.symm (Fin.last A.length) := Fin.ext hjval
          rw [hjlast]
          exact hedge
        · have hqeq : Fin.castLE (Nat.succ_le_succ hle) q =
              Fin.castLT i
                (Nat.lt_trans i.isLt (Nat.succ_lt_succ j.isLt)) := Fin.ext rfl
          rw [← hqeq, hvertices]
          simpa only [hq] using hcv

end GoldbergSeymour

end
