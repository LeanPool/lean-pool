/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.OrderedTreeUnion
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceInitialSegment
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceSuffix
public import LeanPool.GoldbergSeymour.TreeSequencePrefix
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentFacts

/-!
# Ordered Tree Union Augmentation Sequence

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_replay_113.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [ Finite V] [ Fintype E] {G : LooplessMultigraph V E} {k : ℕ}
        {e0 : E} (phi : PartialEdgeColoring E k) (P L R U : TreeSequence G e0),
        TashkinovAugmentationSequence phi P R → TreeSequenceInitialSegment P L →
    ∀ (hleftSegment : TreeSequenceInitialSegment L U), (
    ∀ (j : Fin U.length), L.length ≤ (↑j : ℕ) →
    ∃ (i : Fin R.length), U.edge j = R.edge i ∧ U.vertex j.succ = R.vertex i.succ) → (
    ∀ (i : Fin R.length), R.vertex i.succ ∉ TreeSequenceVertexSet L →
    ∃ (j : Fin U.length), L.length ≤ (↑j : ℕ) ∧ U.edge j = R.edge i ∧ U.vertex j.succ = R.vertex
        i.succ) → (
    ∀ (i j : Fin R.length), R.vertex i.succ ∉ TreeSequenceVertexSet L → R.vertex j.succ ∉
        TreeSequenceVertexSet L → (↑i : ℕ) < (↑j : ℕ) →
    ∀ (p q : Fin U.length), U.vertex p.succ = R.vertex i.succ → U.vertex q.succ = R.vertex j.succ
        → (↑p : ℕ) < (↑q : ℕ)) → (
    ∀ (T : TreeSequence G e0) (q : ℕ) (hq : (1 : ℕ) ≤ q) (hqT : q ≤ T.length),
        TreeSequenceInitialSegment (TreeSequencePrefix T q hq hqT) T) → (
    ∀ (T : TreeSequence G e0) (q : ℕ) (hq : (1 : ℕ) ≤ q) (hqT : q + (1 : ℕ) ≤ T.length),
        TreeSequenceInitialSegment (TreeSequencePrefix T q hq (Nat.le_trans (Nat.le_succ q) hqT))
        (TreeSequencePrefix T (q + (1 : ℕ)) (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ q + (1
        : ℕ)) =>
    by
                                omega
    ) hqT)) → TreeSequencePrefix U L.length L.positive hleftSegment.1 = L →
        TreeSequenceInitialSegment P R → (
    ∀ {A B : TreeSequence G e0}, TashkinovAugmentationSequence phi A B → A.length < B.length →
    ∃ (C : TreeSequence G e0), TashkinovAugmentation phi A C ∧ TashkinovAugmentationSequence phi C
        B) →
    ∀ (n : ℕ) (hnL : L.length ≤ n) (hnU : n ≤ U.length), TashkinovAugmentationSequence phi L
        (TreeSequencePrefix U n (Nat.le_trans L.positive hnL) hnU) := by
  classical
  intro V E _ _ G k e0 phi P L R U hPR hPL hleftSegment hnewEntryFromRight heveryNewRightEntry
      hrightOrder prefixSegment prefixPrefix prefixAtLeft hPRSegment firstStep n hnL hnU
  let _ := Fintype.ofFinite V
  induction n, hnL using Nat.le_induction with
  | base =>
      simpa [prefixAtLeft] using
        (show TashkinovAugmentationSequence phi L L from
          Relation.ReflTransGen.refl)
  | @succ n hnL ih =>
      by_cases hnEq : n = U.length
      · omega
      have hnSuccU : n + 1 ≤ U.length := by omega
      have hnU' : n ≤ U.length := Nat.le_trans (Nat.le_succ n) hnSuccU
      have ih' := ih hnU'
      let X := TreeSequencePrefix U n (Nat.le_trans L.positive hnL) hnU'
      let Y := TreeSequencePrefix U (n + 1)
        (Nat.le_trans L.positive (Nat.le_trans hnL (Nat.le_succ n))) hnSuccU
      let j : Fin U.length := ⟨n, by omega⟩
      obtain ⟨i, hedgeUR, hvertexUR⟩ := hnewEntryFromRight j hnL
      have hrightOutside : R.vertex i.succ ∉ TreeSequenceVertexSet L := by
        intro hmem
        rw [TreeSequenceVertexSet] at hmem
        obtain ⟨a, -, ha⟩ :=
          (@Finset.mem_image _ _ (Classical.decEq V)).mp hmem
        have huvertex : U.vertex
              (Fin.castLE (Nat.succ_le_succ hleftSegment.1) a) =
            L.vertex a := hleftSegment.2.1 a
        have heq : U.vertex j.succ =
            U.vertex (Fin.castLE (Nat.succ_le_succ hleftSegment.1) a) :=
          hvertexUR.trans (ha.symm.trans huvertex.symm)
        have hindex := congrArg Fin.val (U.vertex_injective heq)
        simp [j] at hindex
        omega
      have hiP : P.length ≤ i.val := by
        by_contra hnot
        have hi : i.val < P.length := Nat.lt_of_not_ge hnot
        let a : Fin (P.length + 1) := ⟨i.val + 1, by omega⟩
        have hRPa : R.vertex
              (Fin.castLE (Nat.succ_le_succ hPRSegment.1) a) = P.vertex a :=
          hPRSegment.2.1 a
        apply hrightOutside
        rw [TreeSequenceVertexSet]
        apply (@Finset.mem_image _ _ (Classical.decEq V)).mpr
        refine ⟨Fin.castLE (Nat.succ_le_succ hPL.1) a, Finset.mem_univ _, ?_⟩
        have hia : Fin.castLE (Nat.succ_le_succ hPRSegment.1) a = i.succ :=
          Fin.ext (by simp [a])
        rw [hia] at hRPa
        exact (hPL.2.1 a).trans hRPa.symm
      have hiR : i.val < R.length := i.isLt
      let RX := TreeSequencePrefix R i.val
        (Nat.le_trans P.positive hiP) (Nat.le_of_lt hiR)
      have hPRX : TreeSequenceInitialSegment P RX := by
        refine ⟨hiP, ?_, ?_⟩
        · intro a
          change R.vertex _ = P.vertex a
          calc
            R.vertex _ = R.vertex
                (Fin.castLE (Nat.succ_le_succ hPRSegment.1) a) := by congr 1
            _ = P.vertex a := hPRSegment.2.1 a
        · intro a
          change R.edge _ = P.edge a
          calc
            R.edge _ = R.edge (Fin.castLE hPRSegment.1 a) := by congr 1
            _ = P.edge a := hPRSegment.2.2 a
      have hRXR : TreeSequenceInitialSegment RX R :=
        prefixSegment R i.val (Nat.le_trans P.positive hiP) (Nat.le_of_lt hiR)
      have hsuffix : TashkinovAugmentationSequence phi RX R :=
        TashkinovAugmentationSequenceSuffix phi P RX R hPR hPRX hRXR
      have hRXlen : RX.length = i.val := rfl
      obtain ⟨C, hRXC, hCR⟩ := firstStep hsuffix (by omega)
      rcases hRXC with ⟨hlenC, hRXCsegment, c, hcolorC, hmissingRX⟩
      have hCRSegment : TreeSequenceInitialSegment C R :=
        TashkinovAugmentationSequenceInitialSegment phi C R hCR
      have hCi : C.length = i.val + 1 := by omega
      let ci : Fin C.length := ⟨i.val, by omega⟩
      have hcolorR : phi (R.edge i) = some c := by
        have hciLast : ci = Fin.cast hlenC.symm (Fin.last RX.length) := by
          apply Fin.ext
          simp [ci, hRXlen]
        have hRci : R.edge (Fin.castLE hCRSegment.1 ci) = C.edge ci :=
          hCRSegment.2.2 ci
        have hcast : Fin.castLE hCRSegment.1 ci = i := by
          apply Fin.ext
          simp [ci]
        rw [← hcast, hRci, hciLast]
        exact hcolorC
      have hmissingX : c ∈ TreeMissingColors phi X := by
        rw [TreeMissingColors] at hmissingRX ⊢
        obtain ⟨v, hvRX, hcMissing⟩ := Finset.mem_biUnion.mp hmissingRX
        rw [TreeSequenceVertexSet] at hvRX
        obtain ⟨a, -, ha⟩ :=
          (@Finset.mem_image _ _ (Classical.decEq V)).mp hvRX
        apply Finset.mem_biUnion.mpr
        refine ⟨v, ?_, hcMissing⟩
        by_cases hvL : v ∈ TreeSequenceVertexSet L
        · rw [TreeSequenceVertexSet] at hvL ⊢
          obtain ⟨b, -, hb⟩ :=
            (@Finset.mem_image _ _ (Classical.decEq V)).mp hvL
          apply (@Finset.mem_image _ _ (Classical.decEq V)).mpr
          refine ⟨Fin.castLE (Nat.succ_le_succ hnL) b, Finset.mem_univ _, ?_⟩
          change U.vertex _ = v
          calc
            U.vertex _ = U.vertex
                (Fin.castLE (Nat.succ_le_succ hleftSegment.1) b) := by congr 1
            _ = L.vertex b := hleftSegment.2.1 b
            _ = v := hb
        · have haPos : 1 ≤ a.val := by
            by_contra hzero
            have haZero : a.val = 0 := by omega
            let p0 : Fin (P.length + 1) := ⟨0, by omega⟩
            have hRp0 := hPRSegment.2.1 p0
            have hLp0 := hPL.2.1 p0
            apply hvL
            rw [TreeSequenceVertexSet]
            refine (@Finset.mem_image _ _ (Classical.decEq V)).mpr
              ⟨Fin.castLE (Nat.succ_le_succ hPL.1) p0, Finset.mem_univ _, ?_⟩
            have haR : R.vertex (Fin.castLE
                  (Nat.succ_le_succ (Nat.le_of_lt hiR)) a) = v := by
              simpa [RX, TreeSequencePrefix] using ha
            have ha0 : Fin.castLE
                  (Nat.succ_le_succ (Nat.le_of_lt hiR)) a =
                Fin.castLE (Nat.succ_le_succ hPRSegment.1) p0 := by
              apply Fin.ext
              exact haZero
            rw [ha0, hRp0] at haR
            exact hLp0.trans haR
          let r : Fin R.length := ⟨a.val - 1, by
            have haLt : a.val < RX.length + 1 := a.isLt
            simp [RX] at haLt
            omega⟩
          have hrSucc : r.succ =
              Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt hiR)) a := by
            apply Fin.ext
            exact Nat.sub_add_cancel haPos
          have hrv : R.vertex r.succ = v := by
            rw [hrSucc]
            simpa [RX, TreeSequencePrefix] using ha
          have hrOutside : R.vertex r.succ ∉ TreeSequenceVertexSet L := by
            simpa [hrv] using hvL
          have hri : r.val < i.val := by
            have haLt : a.val < RX.length + 1 := a.isLt
            simp [RX, r] at haLt ⊢
            omega
          obtain ⟨q, hqL, hedgeq, hvertexq⟩ :=
            heveryNewRightEntry r hrOutside
          have hqn : q.val < n :=
            hrightOrder r i hrOutside hrightOutside hri q j
              hvertexq hvertexUR
          rw [TreeSequenceVertexSet]
          apply (@Finset.mem_image _ _ (Classical.decEq V)).mpr
          have hXlen : X.length = n := rfl
          let qX : Fin (X.length + 1) := ⟨q.val + 1, by omega⟩
          refine ⟨qX, Finset.mem_univ _, ?_⟩
          rw [← hrv, ← hvertexq]
          change U.vertex _ = U.vertex q.succ
          congr 1
      have hXY : TashkinovAugmentation phi X Y := by
        have hlenXY : Y.length = X.length + 1 := by
          change n + 1 = n + 1
          rfl
        refine ⟨hlenXY, ?_, c, ?_, hmissingX⟩
        · simpa [X, Y] using prefixPrefix U n
            (Nat.le_trans L.positive hnL) hnSuccU
        · have hcolorU : phi (U.edge j) = some c := by
            rw [hedgeUR]
            exact hcolorR
          change phi (U.edge _) = some c
          convert hcolorU using 1
          apply congrArg phi
          apply congrArg U.edge
          apply Fin.ext
          rfl
      change TashkinovAugmentationSequence phi L Y
      exact Relation.ReflTransGen.tail ih' hXY

theorem OrderedTreeUnionAugmentationSequence
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    {G : LooplessMultigraph V E} {k : Nat} {e0 : E}
    (phi : PartialEdgeColoring E k) (P L R U : TreeSequence G e0)
    (hPR : TashkinovAugmentationSequence phi P R)
    (hPL : TreeSequenceInitialSegment P L)
    (hunion : OrderedTreeUnion L R U) :
    TashkinovAugmentationSequence phi L U := by
  rcases hunion with
    ⟨hleftSegment, hunionVertices, hnewEntryFromRight,
      heveryNewRightEntry, hrightOrder⟩
  classical
  have prefixSegment (T : TreeSequence G e0) (q : Nat)
      (hq : 1 ≤ q) (hqT : q ≤ T.length) :
      TreeSequenceInitialSegment (TreeSequencePrefix T q hq hqT) T := by
    exact TreeSequenceInitialSegment.prefix_segment T q hq hqT
  have prefixPrefix (T : TreeSequence G e0) (q : Nat)
      (hq : 1 ≤ q) (hqT : q + 1 ≤ T.length) :
      TreeSequenceInitialSegment
        (TreeSequencePrefix T q hq (Nat.le_trans (Nat.le_succ q) hqT))
        (TreeSequencePrefix T (q + 1) (by omega) hqT) := by
    exact TreeSequenceInitialSegment.prefix_prefix T q (q + 1) hq (by omega)
      (Nat.le_trans (Nat.le_succ q) hqT) hqT (Nat.le_succ q)
  have prefixSelf (T : TreeSequence G e0) :
      TreeSequencePrefix T T.length T.positive le_rfl = T := by
    exact TreeSequenceInitialSegment.prefix_self T
  have prefixAtLeft :
      TreeSequencePrefix U L.length L.positive hleftSegment.1 = L := by
    exact hleftSegment.eq_prefix.symm
  have hPRSegment : TreeSequenceInitialSegment P R :=
    TashkinovAugmentationSequenceInitialSegment phi P R hPR
  have firstStep {A B : TreeSequence G e0}
      (hAB : TashkinovAugmentationSequence phi A B)
      (hlt : A.length < B.length) :
      ∃ C, TashkinovAugmentation phi A C ∧
        TashkinovAugmentationSequence phi C B := by
    unfold TashkinovAugmentationSequence at hAB ⊢
    induction hAB using Relation.ReflTransGen.head_induction_on with
    | refl => omega
    | @head A C hAC hCB ih => exact ⟨C, hAC, hCB⟩
  have replay := @helper_replay_113 V E inferInstance inferInstance G k e0 phi P L R U hPR hPL
      hleftSegment hnewEntryFromRight heveryNewRightEntry hrightOrder prefixSegment prefixPrefix
      prefixAtLeft hPRSegment firstStep
  have hfull := replay U.length hleftSegment.1 le_rfl
  simpa [prefixSelf] using hfull

end GoldbergSeymour

end
