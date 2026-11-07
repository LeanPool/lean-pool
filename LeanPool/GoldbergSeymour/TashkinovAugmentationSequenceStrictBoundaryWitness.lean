/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.BoundaryColorEdges
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequence

/-!
# Tashkinov Augmentation Sequence Strict Boundary Witness

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem TashkinovAugmentationSequenceStrictBoundaryWitness
    {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {k : Nat} {e0 : E}
    (phi : PartialEdgeColoring E k) (A B : TreeSequence G e0)
    (hAB : TashkinovAugmentationSequence phi A B)
    (hstrict : A.length < B.length) :
    ∃ c : Fin k, c ∈ TreeMissingColors phi A ∧
      (BoundaryColorEdges G phi (TreeSequenceVertexSet A) c).Nonempty := by
  classical
  unfold TashkinovAugmentationSequence at hAB
  induction hAB using Relation.ReflTransGen.head_induction_on with
  | refl => omega
  | @head A C hAC hCB ih =>
      rcases hAC with ⟨hlen, hsegment, c, hcolor, hmissing⟩
      refine ⟨c, hmissing, ?_⟩
      let j : Fin C.length := Fin.cast hlen.symm (Fin.last A.length)
      refine ⟨C.edge j, ?_⟩
      simp only [BoundaryColorEdges, Finset.mem_filter]
      refine ⟨?_, hcolor⟩
      simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      obtain ⟨i, hi⟩ := C.attaches j
      let oldIndex : Fin (A.length + 1) := ⟨i.val, by
        have hiLt := i.isLt
        simp [j] at hiLt
        omega⟩
      let cIndex : Fin (C.length + 1) :=
        Fin.castLE (Nat.succ_le_succ hsegment.1) oldIndex
      have hOldVertex : C.vertex cIndex = A.vertex oldIndex :=
        hsegment.2.1 oldIndex
      have hNewOutside : C.vertex j.succ ∉ TreeSequenceVertexSet A := by
        intro hmem
        rw [TreeSequenceVertexSet] at hmem
        obtain ⟨a, -, ha⟩ := Finset.mem_image.mp hmem
        have heq : C.vertex j.succ =
            C.vertex (Fin.castLE (Nat.succ_le_succ hsegment.1) a) :=
          ha.symm.trans (hsegment.2.1 a).symm
        have hindex := congrArg Fin.val (C.vertex_injective heq)
        simp [j] at hindex
        omega
      refine ⟨C.vertex cIndex, ?_, C.vertex j.succ, hNewOutside, ?_⟩
      · rw [TreeSequenceVertexSet]
        exact Finset.mem_image.mpr ⟨oldIndex, Finset.mem_univ _, hOldVertex.symm⟩
      · have hicast :
            Fin.castLT i (Nat.lt_trans i.isLt (Nat.succ_lt_succ j.isLt)) = cIndex := by
          apply Fin.ext
          rfl
        calc
          G.ends (C.edge j) =
              s(C.vertex j.succ,
                C.vertex (Fin.castLT i
                  (Nat.lt_trans i.isLt (Nat.succ_lt_succ j.isLt)))) := hi
          _ = s(C.vertex j.succ, C.vertex cIndex) := by rw [hicast]
          _ = s(C.vertex cIndex, C.vertex j.succ) := Sym2.eq_swap

end GoldbergSeymour

end
