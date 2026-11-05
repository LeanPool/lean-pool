/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequence

/-!
# Tashkinov Augmentation Sequence Coloring Transport

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem TashkinovAugmentationSequenceColoringTransport
    {V E : Type*} [Finite V] [Fintype E]
    {G : LooplessMultigraph V E} {k : Nat} {e0 : E}
    (phi sigma : PartialEdgeColoring E k)
    (S B X : TreeSequence G e0)
    (hsequence : TashkinovAugmentationSequence phi S X)
    (hBX : TreeSequenceInitialSegment B X)
    (hpenultimate : X.length = B.length + 1)
    (hfixed : forall t : Fin X.length, S.length <= t.val ->
      sigma (X.edge t) = phi (X.edge t))
    (hmissing : forall v, v ∈ TreeSequenceVertexSet B ->
      MissingColors G sigma v = MissingColors G phi v) :
    TashkinovAugmentationSequence sigma S X := by
  classical
  let _ := Fintype.ofFinite V
  have initialSegmentRefl (A : TreeSequence G e0) :
      TreeSequenceInitialSegment A A := by
    refine ⟨Nat.le_refl _, ?_, ?_⟩
    · intro i
      rfl
    · intro i
      rfl
  have initialSegmentTrans {A C D : TreeSequence G e0}
      (hAC : TreeSequenceInitialSegment A C)
      (hCD : TreeSequenceInitialSegment C D) :
      TreeSequenceInitialSegment A D := by
    rcases hAC with ⟨hACLen, hACVertex, hACEdge⟩
    rcases hCD with ⟨hCDLen, hCDVertex, hCDEdge⟩
    refine ⟨Nat.le_trans hACLen hCDLen, ?_, ?_⟩
    · intro i
      calc
        D.vertex (Fin.castLE (Nat.succ_le_succ (Nat.le_trans hACLen hCDLen)) i) =
            D.vertex (Fin.castLE (Nat.succ_le_succ hCDLen)
              (Fin.castLE (Nat.succ_le_succ hACLen) i)) := by
                congr 1
        _ = C.vertex (Fin.castLE (Nat.succ_le_succ hACLen) i) :=
          hCDVertex _
        _ = A.vertex i := hACVertex i
    · intro i
      calc
        D.edge (Fin.castLE (Nat.le_trans hACLen hCDLen) i) =
            D.edge (Fin.castLE hCDLen (Fin.castLE hACLen i)) := by
              congr 1
        _ = C.edge (Fin.castLE hACLen i) := hCDEdge _
        _ = A.edge i := hACEdge i
  have routeInitialSegment {A C : TreeSequence G e0}
      (hroute : TashkinovAugmentationSequence phi A C) :
      TreeSequenceInitialSegment A C := by
    unfold TashkinovAugmentationSequence at hroute
    induction hroute with
    | refl => exact initialSegmentRefl A
    | @tail C D hAC hCD ih =>
        exact initialSegmentTrans ih hCD.2.1
  have commonExtensionPrefix {A : TreeSequence G e0}
      (hAX : TreeSequenceInitialSegment A X)
      (hlen : A.length < X.length) :
      TreeSequenceInitialSegment A B := by
    rcases hAX with ⟨hAXLen, hAXVertex, hAXEdge⟩
    rcases hBX with ⟨hBXLen, hBXVertex, hBXEdge⟩
    have hABLen : A.length ≤ B.length := by omega
    refine ⟨hABLen, ?_, ?_⟩
    · intro i
      calc
        B.vertex (Fin.castLE (Nat.succ_le_succ hABLen) i) =
            X.vertex (Fin.castLE (Nat.succ_le_succ hBXLen)
              (Fin.castLE (Nat.succ_le_succ hABLen) i)) :=
          (hBXVertex _).symm
        _ = X.vertex (Fin.castLE (Nat.succ_le_succ hAXLen) i) := by
          congr 1
        _ = A.vertex i := hAXVertex i
    · intro i
      calc
        B.edge (Fin.castLE hABLen i) =
            X.edge (Fin.castLE hBXLen (Fin.castLE hABLen i)) :=
          (hBXEdge _).symm
        _ = X.edge (Fin.castLE hAXLen i) := by
          congr 1
        _ = A.edge i := hAXEdge i
  have transport (A : TreeSequence G e0) (hsource : S.length ≤ A.length)
      (hroute : TashkinovAugmentationSequence phi A X) :
      TashkinovAugmentationSequence sigma A X := by
    unfold TashkinovAugmentationSequence at hroute ⊢
    revert hsource
    refine Relation.ReflTransGen.head_induction_on hroute ?_ ?_
    · intro hsource
      exact Relation.ReflTransGen.refl
    · intro A C hstep htail ih hsource
      rcases hstep with ⟨hlen, hAC, c, hcolor, hc⟩
      have hCX : TreeSequenceInitialSegment C X := by
        exact routeInitialSegment htail
      have hAX : TreeSequenceInitialSegment A X :=
        initialSegmentTrans hAC hCX
      have hAlen : A.length < X.length := by
        have hCXLen := hCX.1
        omega
      have hAB : TreeSequenceInitialSegment A B :=
        commonExtensionPrefix hAX hAlen
      have hcSigma : c ∈ TreeMissingColors sigma A := by
        rw [TreeMissingColors] at hc ⊢
        rcases Finset.mem_biUnion.mp hc with ⟨v, hvA, hcv⟩
        have hvB : v ∈ TreeSequenceVertexSet B := by
          rw [TreeSequenceVertexSet] at hvA ⊢
          rcases Finset.mem_image.mp hvA with ⟨j, _, hj⟩
          refine Finset.mem_image.mpr ⟨Fin.castLE (Nat.succ_le_succ hAB.1) j,
            Finset.mem_univ _, ?_⟩
          rw [hAB.2.1 j]
          exact hj
        refine Finset.mem_biUnion.mpr ⟨v, hvA, ?_⟩
        rw [hmissing v hvB]
        exact hcv
      have haddedFixed :
          sigma (C.edge (Fin.cast hlen.symm (Fin.last A.length))) =
            phi (C.edge (Fin.cast hlen.symm (Fin.last A.length))) := by
        let tC : Fin C.length := Fin.cast hlen.symm (Fin.last A.length)
        let tX : Fin X.length := Fin.castLE hCX.1 tC
        have htval : tX.val = A.length := rfl
        have hfix := hfixed tX (by simpa [htval] using hsource)
        have hedge : X.edge tX = C.edge tC := hCX.2.2 tC
        simpa [tC, tX, hedge] using hfix
      have hsourceC : S.length ≤ C.length := by omega
      exact Relation.ReflTransGen.head
        ⟨hlen, hAC, c, haddedFixed.trans hcolor, hcSigma⟩
        (ih hsourceC)
  exact transport S (Nat.le_refl _) hsequence

end GoldbergSeymour

end
