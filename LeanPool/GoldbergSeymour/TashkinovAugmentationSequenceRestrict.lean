/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequence
public import Mathlib.Data.Fintype.EquivFin

/-!
# Tashkinov Augmentation Sequence Restrict

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem TashkinovAugmentationSequenceRestrict
    {V E : Type*} [Finite V] [Fintype E]
    {G : LooplessMultigraph V E} {k : Nat} {e0 : E}
    (phi : PartialEdgeColoring E k) (S B C : TreeSequence G e0)
    (hSC : TashkinovAugmentationSequence phi S C)
    (hSB : TreeSequenceInitialSegment S B)
    (hBC : TreeSequenceInitialSegment B C) :
    TashkinovAugmentationSequence phi S B := by
  classical
  let _ := Fintype.ofFinite V
  have initialSegment_antisymm_length
      {A D : TreeSequence G e0}
      (hAD : TreeSequenceInitialSegment A D)
      (hlen : A.length = D.length) : A = D := by
    rcases hAD with ⟨hle, hvertex, hedge⟩
    cases A with
    | mk la pa va ea via eia fea aa =>
      cases D with
      | mk ld pd vd ed vid eid fed ad =>
        simp only at hlen
        subst ld
        rw [TreeSequence.mk.injEq]
        refine ⟨rfl, ?_, ?_⟩
        · apply heq_of_eq
          funext i
          simpa only [Fin.castLE] using (hvertex i).symm
        · apply heq_of_eq
          funext i
          simpa only [Fin.castLE] using (hedge i).symm
  have initialSegment_of_common_extension
      {A D F : TreeSequence G e0}
      (hAF : TreeSequenceInitialSegment A F)
      (hDF : TreeSequenceInitialSegment D F)
      (hDA : D.length ≤ A.length) :
      TreeSequenceInitialSegment D A := by
    rcases hAF with ⟨hAlen, hAvertex, hAedge⟩
    rcases hDF with ⟨hDlen, hDvertex, hDedge⟩
    refine ⟨hDA, ?_, ?_⟩
    · intro i
      calc
        A.vertex (Fin.castLE (Nat.succ_le_succ hDA) i) =
            F.vertex (Fin.castLE (Nat.succ_le_succ hAlen)
              (Fin.castLE (Nat.succ_le_succ hDA) i)) :=
          (hAvertex (Fin.castLE (Nat.succ_le_succ hDA) i)).symm
        _ = F.vertex (Fin.castLE (Nat.succ_le_succ hDlen) i) := by
          congr 1
        _ = D.vertex i := hDvertex i
    · intro i
      calc
        A.edge (Fin.castLE hDA i) =
            F.edge (Fin.castLE hAlen (Fin.castLE hDA i)) :=
          (hAedge (Fin.castLE hDA i)).symm
        _ = F.edge (Fin.castLE hDlen i) := by
          congr 1
        _ = D.edge i := hDedge i
  unfold TashkinovAugmentationSequence at hSC ⊢
  induction hSC generalizing B with
  | refl =>
      have hlen : B.length = S.length :=
        Nat.le_antisymm hBC.1 hSB.1
      have hBS : B = S :=
        initialSegment_antisymm_length hBC hlen
      subst B
      exact Relation.ReflTransGen.refl
  | @tail A C hSA hAC ih =>
      rcases hAC with ⟨hlen, hinitAC, hcolor⟩
      by_cases hBA : B.length ≤ A.length
      · exact ih B hSB
          (initialSegment_of_common_extension hinitAC hBC hBA)
      · have hBlen : B.length = C.length := by
          rcases hBC with ⟨hBCle, _, _⟩
          omega
        have hBCeq : B = C :=
          initialSegment_antisymm_length hBC hBlen
        subst B
        exact Relation.ReflTransGen.tail hSA ⟨hlen, hinitAC, hcolor⟩

end GoldbergSeymour

end
