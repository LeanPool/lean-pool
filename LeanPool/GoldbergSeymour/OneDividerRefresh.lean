/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTreeTerminalData

public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTree
public import LeanPool.GoldbergSeymour.GoodHierarchy
public import LeanPool.GoldbergSeymour.GoodHierarchyReservedDisjoint
public import LeanPool.GoldbergSeymour.HierarchyFirstMissingPositionPrefixCutoff
public import LeanPool.GoldbergSeymour.HierarchyTerminalStoredColorsSubsetLast
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentVertexSetSubset
public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary

/-!
# P2940_T1_One Divider Refresh

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private noncomputable abbrev helperHW360.{u_1, u_2} :
    open scoped Classical in
      {V : Type u_1} →
  {E : Type u_2} →
  [ Fintype V] →
  [ Fintype E] →
  [ DecidableEq V] →
  [ DecidableEq E] →
  (G : LooplessMultigraph V E) →
  (k : ℕ) →
  (e0 : E) →
  (input : PartialEdgeColoring E k) →
  (T : TreeSequence G e0) →
  (phi : PartialEdgeColoring E k) →
  (ett : ExtendedTashkinovTree G k e0 input T phi) →
  (U W : TreeSequence G e0) →
  (corrU : CorrespondingExtendedTashkinovTree G k e0 ett phi U) →
  (corrW : CorrespondingExtendedTashkinovTree G k e0 ett phi W) →
  (baseU : HierarchyBase corrU.replacementETT phi) →
  (baseW : HierarchyBase corrW.replacementETT phi) →
  baseW.core = baseU.core →
  (H : TashkinovHierarchy corrU.replacementETT baseU) →
  let d : ℕ := H.dividerCount;
  let N : ℕ := d + (1 : ℕ);
  (∀ (X : TreeSequence G e0)
      (corr :
        CorrespondingExtendedTashkinovTree G k e0 ett
          phi X),
      corr.replacementETT.series.data.tree
            (Fin.last
                corr.replacementETT.rounds).castSucc =
          ett.series.data.tree
            (Fin.last ett.rounds).castSucc ∧
        corr.replacementETT.series.data.kind
              (Fin.last corr.replacementETT.rounds) =
            ett.series.data.kind (Fin.last ett.rounds) ∧
          TashkinovStoredColors
              corr.replacementETT.series.data
              (Fin.last corr.replacementETT.rounds) =
            TashkinovStoredColors ett.series.data
              (Fin.last ett.rounds)) →
  let stageW :
    Fin (N + (2 : ℕ)) → TreeSequence G e0 :=
    fun (j : Fin (N + (2 : ℕ))) ↦
    if hj : (↑j : ℕ) = d + (2 : ℕ) then W
    else
      H.stage
        (⟨(↑j : ℕ),
            (by
              have := corrU.rungAgreement;
              have := T.positive; have := U.positive;
              omega)⟩ :
          Fin (H.dividerCount + (2 : ℕ)));
  (hsize : W.length = U.length + (1 : ℕ)) →
  TreeSequenceInitialSegment U W →
  (∀ {A B : TreeSequence G e0}
      (hAB : TreeSequenceInitialSegment A B),
      A =
        TreeSequencePrefix B A.length A.positive
          hAB.1) →
  (∀ (p : ℕ) (hp : (1 : ℕ) ≤ p)
      (hpU : p ≤ U.length),
      TreeSequencePrefix U p hp hpU =
        TreeSequencePrefix W p hp
          ((by have := W.positive; omega))) →
  (∀ (j : Fin (N + (2 : ℕ)))
      (hj : (↑j : ℕ) ≤ d + (1 : ℕ)),
      stageW j =
        H.stage
          (⟨(↑j : ℕ),
              (by
                have := corrU.rungAgreement;
                have := T.positive;
                have := U.positive; omega)⟩ :
            Fin (H.dividerCount + (2 : ℕ)))) →
  (∀ (j : Fin (d + (2 : ℕ))),
      stageW
          (⟨(↑j : ℕ),
              (by
                have := corrU.rungAgreement;
                have := T.positive;
                have := U.positive;
                omega)⟩ :
            Fin (N + (2 : ℕ))) =
        H.stage j) →
  stageW
        (⟨d + (2 : ℕ),
            (by
              have := corrU.rungAgreement;
              have := T.positive;
              have := U.positive;
              omega)⟩ :
          Fin (N + (2 : ℕ))) =
      W →
  let _ :
    Fin N → Fin (W.length + (1 : ℕ)) :=
    fun (i : Fin N) ↦
    if hi : (↑i : ℕ) < d then
      (⟨(↑(H.dividerPosition
                (⟨(↑i : ℕ), hi⟩ :
                  Fin H.dividerCount)) :
            ℕ),
          have hpos :
            (↑(H.dividerPosition
                    (⟨(↑i : ℕ), hi⟩ :
                      Fin
                        H.dividerCount)) :
                ℕ) <
              U.length + (1 : ℕ) :=
            (by
              have :=
                corrU.rungAgreement;
              have := T.positive;
              have := U.positive;
              omega);
          have _ :
            W.length =
              U.length + (1 : ℕ) :=
            hsize;
          Decidable.byContradiction
            fun
              (a :
                ¬(↑(H.dividerPosition
                          (⟨(↑i : ℕ),
                              hi⟩ :
                            Fin
                              H.dividerCount)) :
                      ℕ) <
                    W.length +
                      (1 : ℕ)) ↦
            (by omega)⟩ :
        Fin (W.length + (1 : ℕ)))
    else
      (⟨U.length,
          (by
            have := U.positive;
            have := W.positive;
            omega)⟩ :
        Fin (W.length + (1 : ℕ)));
  (∀ (i : Fin d),
      (↑(H.dividerPosition i) : ℕ) <
        U.length) →
  TashkinovHierarchy
    corrW.replacementETT baseW := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett U W corrU corrW baseU baseW hcore H d N corrTerminal
      stageW hsize hUW prefixEqOfSegment prefixTransfer stageAtOld stageOld stageNew divW
      dividerBeforeTerminal
  exact {
    dividerCount := N
    stage := stageW
    baseStage := by
      calc
        stageW 0 = H.stage 0 := by
          simpa using stageOld (0 : Fin (d + 2))
        _ = corrU.replacementETT.series.data.tree
              (Fin.last corrU.replacementETT.rounds).castSucc := H.baseStage
        _ = ett.series.data.tree (Fin.last ett.rounds).castSucc :=
          (corrTerminal U corrU).1
        _ = corrW.replacementETT.series.data.tree
              (Fin.last corrW.replacementETT.rounds).castSucc :=
          (corrTerminal W corrW).1.symm
    terminalStage := by
      have hidx : Fin.last (N + 1) = (⟨d + 2, by omega⟩ : Fin (N + 2)) := by
        apply Fin.ext
        simp [N]
      rw [hidx]
      exact stageNew
    nested := by
      intro j
      by_cases hj : j.val = d + 1
      · have hleft : stageW j.castSucc = U := by
          rw [stageAtOld j.castSucc (by simp [hj])]
          have hi : (⟨j.castSucc.val, by simp [hj]⟩ : Fin (d + 2)) =
              Fin.last (d + 1) := by apply Fin.ext; simp [hj]
          rw [hi, H.terminalStage]
        have hright : stageW j.succ = W := by
          have hi : j.succ = (⟨d + 2, by omega⟩ : Fin (N + 2)) := by
            apply Fin.ext
            simp [hj, N]
          rw [hi, stageNew]
        rw [hleft, hright]
        exact hUW
      · have hjlt : j.val < d + 1 := by have := j.isLt; omega
        have hleft := stageAtOld j.castSucc (by
          change j.val ≤ d + 1
          exact Nat.le_of_lt hjlt)
        have hright := stageAtOld j.succ (by
          change j.val + 1 ≤ d + 1
          omega)
        rw [hleft, hright]
        let io : Fin (d + 1) := ⟨j.val, by omega⟩
        have hleftIdx : (⟨j.castSucc.val, by exact j.isLt⟩ : Fin (d + 2)) = io.castSucc :=
          Fin.ext rfl
        have hrightIdx : (⟨j.succ.val, by change j.val + 1 < d + 2; omega⟩ : Fin (d + 2)) =
            io.succ :=
          Fin.ext rfl
        rw [hleftIdx, hrightIdx]
        exact H.nested io
    strict := by
      intro j
      by_cases hj : j.val < d + 1
      · have hleft := stageAtOld j.castSucc (by
          change j.val ≤ d + 1
          exact Nat.le_of_lt hj)
        have hright := stageAtOld j.succ (by
          change j.val + 1 ≤ d + 1
          omega)
        rw [hleft, hright]
        let io : Fin (d + 1) := ⟨j.val, by omega⟩
        have hleftIdx : (⟨j.castSucc.val, by exact j.isLt⟩ : Fin (d + 2)) = io.castSucc :=
          Fin.ext rfl
        have hrightIdx : (⟨j.succ.val, by change j.val + 1 < d + 2; omega⟩ : Fin (d + 2)) =
            io.succ :=
          Fin.ext rfl
        rw [hleftIdx, hrightIdx]
        exact H.strict io
      · have hjlast : j.val = d + 1 := by have := j.isLt; omega
        have hleft : stageW j.castSucc = U := by
          rw [stageAtOld j.castSucc (by simp [hjlast])]
          have hi : (⟨j.castSucc.val, by simp [hjlast]⟩ : Fin (d + 2)) =
              Fin.last (d + 1) := by apply Fin.ext; simp [hjlast]
          rw [hi, H.terminalStage]
        have hright : stageW j.succ = W := by
          have hi : j.succ = (⟨d + 2, by omega⟩ : Fin (N + 2)) := by
            apply Fin.ext
            simp [hjlast, N]
          rw [hi, stageNew]
        rw [hleft, hright]
        omega
    dividerPosition := divW
    dividerPositive := by
      intro i
      by_cases hi : i.val < d
      · simpa [divW, hi] using H.dividerPositive ⟨i.val, hi⟩
      · simpa [divW, hi] using U.positive
    dividerIncreasing := by
      intro i j hij
      by_cases hi : i.val < d <;> by_cases hj : j.val < d
      · simpa [divW, hi, hj] using
          H.dividerIncreasing ⟨i.val, hi⟩ ⟨j.val, hj⟩ hij
      · have hpos := dividerBeforeTerminal ⟨i.val, hi⟩
        simp only [hi, ↓reduceDIte, hj, gt_iff_lt, divW]
        exact hpos
      · omega
      · omega
    dividerStage := by
      intro i
      by_cases hi : i.val < d
      · let j : Fin (N + 2) := ⟨i.val + 1, by change i.val + 1 < d + 3; omega⟩
        have hstage := stageAtOld j (by
          change i.val + 1 ≤ d + 1
          omega)
        rw [hstage]
        let oldI : Fin d := ⟨i.val, hi⟩
        have hidx : (⟨j.val, by change i.val + 1 < d + 2; omega⟩ : Fin (d + 2)) =
            oldI.succ.castSucc := by
          apply Fin.ext
          simp [j, oldI]
        rw [hidx]
        have hidx2 : oldI.succ.castSucc =
            (⟨oldI.val + 1, by omega⟩ : Fin (d + 2)) := Fin.ext rfl
        rw [hidx2, H.dividerStage oldI]
        have hp : (H.dividerPosition oldI).val ≤ U.length :=
          Nat.le_of_lt_succ (H.dividerPosition oldI).isLt
        rw [prefixTransfer (H.dividerPosition oldI).val
          (H.dividerPositive oldI) hp]
        simp [oldI, divW, hi]
      · have hlast : i.val = d := by have := i.isLt; omega
        have hidx : (⟨i.val + 1, by omega⟩ : Fin (N + 2)) =
            (⟨d + 1, by omega⟩ : Fin (N + 2)) := by
          apply Fin.ext
          simp [hlast]
        rw [hidx]
        have hstage : stageW ⟨d + 1, by omega⟩ = U := by
          let jOld : Fin (N + 2) := ⟨d + 1, by simp [N]⟩
          have hjOld : jOld.val ≤ d + 1 := by change d + 1 ≤ d + 1; omega
          have hold := stageAtOld jOld hjOld
          have hindex : jOld = (⟨d + 1, by simp [N]⟩ : Fin (N + 2)) :=
            Fin.ext rfl
          change stageW (⟨d + 1, by simp [N]⟩ : Fin (N + 2)) = U
          rw [← hindex, hold]
          have heq : (⟨d + 1, by omega⟩ : Fin (d + 2)) = Fin.last (d + 1) :=
            Fin.ext rfl
          rw [heq, H.terminalStage]
        rw [hstage]
        simpa [divW, hi] using (prefixEqOfSegment hUW)
    coreInsideFirst := by
      by_cases hd : d = 0
      · have hfirst : stageW ⟨1, by omega⟩ = U := by
          let jOld : Fin (N + 2) := ⟨1, by simp [N, hd]⟩
          have hbound : jOld.val ≤ d + 1 := by change 1 ≤ d + 1; omega
          have hOld := stageAtOld jOld hbound
          have hindex : jOld = (⟨1, by omega⟩ : Fin (N + 2)) := Fin.ext rfl
          change stageW (⟨1, by omega⟩ : Fin (N + 2)) = U
          rw [← hindex, hOld]
          have hi : (⟨1, by omega⟩ : Fin (d + 2)) = Fin.last (d + 1) := by
            apply Fin.ext
            simp [hd]
          rw [hi, H.terminalStage]
        rw [hfirst, hcore]
        have hcoreU := H.coreInsideFirst
        have hterminal : H.stage ⟨1, by omega⟩ = U := by
          have hi : (⟨1, by omega⟩ : Fin (d + 2)) = Fin.last (d + 1) := by
            apply Fin.ext
            simp [hd]
          rw [hi]
          exact H.terminalStage
        rw [hterminal] at hcoreU
        exact hcoreU
      · have hfirst : stageW ⟨1, by omega⟩ = H.stage ⟨1, by omega⟩ := by
          simp [stageW, d]
        rw [hfirst, hcore]
        exact H.coreInsideFirst
  }

private noncomputable abbrev helperGoodW888.{u_1, u_2} :
    open scoped Classical in
      {V : Type u_1} →
  {E : Type u_2} →
  [ Fintype V] →
  [ Fintype E] →
  [ DecidableEq V] →
  [ DecidableEq E] →
  (G : LooplessMultigraph V E) →
  (k : ℕ) →
  (e0 : E) →
  (input : PartialEdgeColoring E k) →
  (T : TreeSequence G e0) →
  (phi : PartialEdgeColoring E k) →
  (ett : ExtendedTashkinovTree G k e0 input T phi) →
  (U W : TreeSequence G e0) →
  (corrU : CorrespondingExtendedTashkinovTree G k e0 ett phi U) →
  (corrW : CorrespondingExtendedTashkinovTree G k e0 ett phi W) →
  (baseU : HierarchyBase corrU.replacementETT phi) →
  (baseW : HierarchyBase corrW.replacementETT phi) →
  (hcore : baseW.core = baseU.core) →
  baseW.closure = baseU.closure →
  (H : TashkinovHierarchy corrU.replacementETT baseU) →
  (good : GoodHierarchy H) →
  ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet U) →
  (eta beta gammaOne gammaTwo : Fin k) →
  (f : E) →
  eta ∈ HierarchyTerminalStoredColors H →
  beta ∈
      good.gamma (Fin.last H.dividerCount)
        eta →
  phi f = some beta →
  gammaOne ≠ gammaTwo →
  gammaOne ∈
      (TreeSequenceVertexSet U \
            TreeSequenceVertexSet
              (HierarchyStarredStage H
                (Fin.last
                  H.dividerCount))).biUnion
        (MissingColors G phi) →
  gammaTwo ∈
      (TreeSequenceVertexSet U \
            TreeSequenceVertexSet
              (HierarchyStarredStage
                H
                (Fin.last
                  H.dividerCount))).biUnion
        (MissingColors G phi) →
  Disjoint
      (insert gammaOne
          ({ gammaTwo } :
            Finset (Fin k)) :
        Finset (Fin k))
      ((HierarchyTerminalStoredColors
            H).biUnion
        (good.gamma
          (Fin.last
            H.dividerCount))) →
  TreeColorSetMinusClosed G phi
      U
      ((HierarchyTerminalStoredColors
            H).biUnion
        (good.gamma
          (Fin.last
            H.dividerCount))) →
  let d : ℕ := H.dividerCount;
  let N : ℕ := d + (1 : ℕ);
  (corrTerminal :
      ∀
        (X :
          TreeSequence G e0)
        (corr :
          CorrespondingExtendedTashkinovTree
            G k e0 ett phi X),
        corr.replacementETT.series.data.tree
              (Fin.last
                  corr.replacementETT.rounds).castSucc =
            ett.series.data.tree
              (Fin.last
                  ett.rounds).castSucc ∧
          corr.replacementETT.series.data.kind
                (Fin.last
                  corr.replacementETT.rounds) =
              ett.series.data.kind
                (Fin.last
                  ett.rounds) ∧
            TashkinovStoredColors
                corr.replacementETT.series.data
                (Fin.last
                  corr.replacementETT.rounds) =
              TashkinovStoredColors
                ett.series.data
                (Fin.last
                  ett.rounds)) →
  let stageW :
    Fin (N + (2 : ℕ)) →
      TreeSequence G e0 :=
    fun
      (j :
        Fin (N + (2 : ℕ))) ↦
    if hj :
        (↑j : ℕ) =
          d + (2 : ℕ) then
      W
    else
      H.stage
        (⟨(↑j : ℕ),
            have _ :
              corrU.replacementETT.rounds =
                ett.rounds :=
              corrU.rungAgreement;
            have _ :
              (1 : ℕ) ≤
                T.length :=
              T.positive;
            have _ :
              (1 : ℕ) ≤
                U.length :=
              U.positive;
            Decidable.byContradiction
              fun
                (a :
                  ¬(↑j :
                        ℕ) <
                      H.dividerCount +
                        (2 :
                          ℕ)) ↦
              (by omega)⟩ :
          Fin
            (H.dividerCount +
              (2 : ℕ)));
  (hsize :
      W.length =
        U.length +
          (1 : ℕ)) →
  (hUW :
      TreeSequenceInitialSegment
        U W) →
  W.edge
        (Fin.cast
          (have _ :
            (1 : ℕ) ≤
              U.length :=
            U.positive;
          have _ :
            (1 : ℕ) ≤
              W.length :=
            W.positive;
          Decidable.byContradiction
            fun
              (a :
                ¬U.length +
                      (1 :
                        ℕ) =
                    W.length) ↦
            (by omega))
          (Fin.last
            U.length)) =
      f →
  (prefixEqOfSegment :
      ∀
        {A B :
          TreeSequence
            G e0}
        (hAB :
          TreeSequenceInitialSegment
            A B),
        A =
          TreeSequencePrefix
            B A.length
            A.positive
            hAB.1) →
  (prefixTransfer :
      ∀ (p : ℕ)
        (hp :
          (1 : ℕ) ≤
            p)
        (hpU :
          p ≤
            U.length),
        TreeSequencePrefix
            U p hp
            hpU =
          TreeSequencePrefix
            W p hp
            (have
              _ :
              (1 :
                  ℕ) ≤
                W.length :=
              W.positive;
            Decidable.byContradiction
              fun
                (a :
                  ¬p ≤
                      W.length) ↦
              (by
                omega))) →
  (stageAtOld :
      ∀
        (j :
          Fin
            (N +
              (2 :
                ℕ)))
        (hj :
          (↑j :
              ℕ) ≤
            d +
              (1 :
                ℕ)),
        stageW j =
          H.stage
            (⟨(↑j :
                  ℕ),
                have
                  _ :
                  corrU.replacementETT.rounds =
                    ett.rounds :=
                  corrU.rungAgreement;
                have
                  _ :
                  (1 :
                      ℕ) ≤
                    T.length :=
                  T.positive;
                have
                  _ :
                  (1 :
                      ℕ) ≤
                    U.length :=
                  U.positive;
                Decidable.byContradiction
                  fun
                    (a :
                      ¬(↑j :
                            ℕ) <
                          H.dividerCount +
                            (2 :
                              ℕ)) ↦
                  (by
                    omega)⟩ :
              Fin
                (H.dividerCount +
                  (2 :
                    ℕ)))) →
  (stageOld :
      ∀
        (j :
          Fin
            (d +
              (2 :
                ℕ))),
        stageW
            (⟨(↑j :
                  ℕ),
                have
                  _ :
                  corrU.replacementETT.rounds =
                    ett.rounds :=
                  corrU.rungAgreement;
                have
                  _ :
                  (1 :
                      ℕ) ≤
                    T.length :=
                  T.positive;
                have
                  _ :
                  (1 :
                      ℕ) ≤
                    U.length :=
                  U.positive;
                Decidable.byContradiction
                  fun
                    (a :
                      ¬(↑j :
                            ℕ) <
                          N +
                            (2 :
                              ℕ)) ↦
                  (by
                    omega)⟩ :
              Fin
                (N +
                  (2 :
                    ℕ))) =
          H.stage
            j) →
  (stageNew :
      stageW
          (⟨d +
                (2 :
                  ℕ),
              have
                _ :
                corrU.replacementETT.rounds =
                  ett.rounds :=
                corrU.rungAgreement;
              have
                _ :
                (1 :
                    ℕ) ≤
                  T.length :=
                T.positive;
              have
                _ :
                (1 :
                    ℕ) ≤
                  U.length :=
                U.positive;
              Decidable.byContradiction
                fun
                  (a :
                    ¬d +
                          (2 :
                            ℕ) <
                        N +
                          (2 :
                            ℕ)) ↦
                (by
                  omega)⟩ :
            Fin
              (N +
                (2 :
                  ℕ))) =
        W) →
  (dividerBeforeTerminal :
      ∀
        (i :
          Fin
            d),
        (↑(H.dividerPosition
                i) :
            ℕ) <
          U.length) →
  let HW :
    TashkinovHierarchy
      corrW.replacementETT
      baseW :=
    helperHW360
      G k
      e0
      input
      T
      phi
      ett
      U W
      corrU
      corrW
      baseU
      baseW
      hcore
      H
      corrTerminal
      hsize
      hUW
      (fun
          {A
            B :
            TreeSequence
              G
              e0} ↦
        prefixEqOfSegment)
      prefixTransfer
      stageAtOld
      stageOld
      stageNew
      dividerBeforeTerminal;
  (hcountW :
      HW.dividerCount =
        H.dividerCount +
          (1 :
            ℕ)) →
  (∀
      (j :
        Fin
          (d +
            (2 :
              ℕ))),
      HW.stage
          (Fin.castLE
            (have
              _ :
              corrU.replacementETT.rounds =
                ett.rounds :=
              corrU.rungAgreement;
            have
              _ :
              corrW.replacementETT.rounds =
                ett.rounds :=
              corrW.rungAgreement;
            have
              _ :
              (1 :
                  ℕ) ≤
                T.length :=
              T.positive;
            have
              _ :
              (1 :
                  ℕ) ≤
                U.length :=
              U.positive;
            have
              _ :
              (1 :
                  ℕ) ≤
                W.length :=
              W.positive;
            Decidable.byContradiction
              fun
                (a :
                  ¬d +
                        (2 :
                          ℕ) ≤
                      HW.dividerCount +
                        (2 :
                          ℕ)) ↦
              (by
                omega))
            j) =
        H.stage
          j) →
  let
    oldIndex :
    Fin
        (d +
          (1 :
            ℕ)) →
      Fin
        (N +
          (1 :
            ℕ)) :=
    fun
      (j :
        Fin
          (d +
            (1 :
              ℕ))) ↦
    (⟨(↑j :
          ℕ),
        have
          _ :
          corrU.replacementETT.rounds =
            ett.rounds :=
          corrU.rungAgreement;
        have
          _ :
          (1 :
              ℕ) ≤
            T.length :=
          T.positive;
        have
          _ :
          (1 :
              ℕ) ≤
            U.length :=
          U.positive;
        Decidable.byContradiction
          fun
            (a :
              ¬(↑j :
                    ℕ) <
                  N +
                    (1 :
                      ℕ)) ↦
          (by
            omega)⟩ :
      Fin
        (N +
          (1 :
            ℕ)));
  (∀
      (j :
        Fin
          (d +
            (1 :
              ℕ))),
      HierarchyStarredStage
          HW
          (oldIndex
            j) =
        HierarchyStarredStage
          H
          j) →
  (∀
      (j :
        Fin
          (d +
            (1 :
              ℕ))),
      HierarchyStageMissingColors
          HW
          (oldIndex
            j) =
        HierarchyStageMissingColors
          H
          j) →
  (∀
      (j :
        Fin
          (d +
            (1 :
              ℕ))),
      HierarchyStoredColorsAt
          HW
          (oldIndex
            j) =
        HierarchyStoredColorsAt
          H
          j) →
  HierarchyStarredStage
        HW
        (Fin.last
          HW.dividerCount) =
      U →
  HierarchyStoredColorsAt
        HW
        (Fin.last
          HW.dividerCount) =
      HierarchyTerminalStoredColors
        H →
  HW.stage
        (Fin.last
            HW.dividerCount).castSucc =
      U →
  (∀
      (j :
        Fin
          (d +
            (1 :
              ℕ)))
      (theta :
        Fin
          k),
      HierarchySegmentColors
          HW
          (oldIndex
            j)
          theta =
        HierarchySegmentColors
          H
          j
          theta) →
  TreeSequenceInitialSegment
      (HierarchyStarredStage
        H
        (Fin.last
          d))
      U →
  let
    newIndex :
    Fin
      (N +
        (1 :
          ℕ)) :=
    Fin.last
      N;
  let
    gammaW :
    Fin
        (N +
          (1 :
            ℕ)) →
      Fin
          k →
        Finset
          (Fin
            k) :=
    fun
      (j :
        Fin
          (N +
            (1 :
              ℕ)))
      (theta :
        Fin
          k) ↦
    if
        hj :
        (↑j :
            ℕ) ≤
          d then
      good.gamma
        (⟨(↑j :
              ℕ),
            (by
              have :=
                corrU.rungAgreement;
              have :=
                T.positive;
              have :=
                U.positive;
              omega)⟩ :
          Fin
            (H.dividerCount +
              (1 :
                ℕ)))
        theta
    else
      if
          theta =
            eta then
        (insert
            gammaOne
            ({
                gammaTwo } :
              Finset
                (Fin
                  k)) :
          Finset
            (Fin
              k))
      else
        good.gamma
          (Fin.last
            d)
          theta;
  (∀
      (j :
        Fin
          (d +
            (1 :
              ℕ)))
      (theta :
        Fin
          k),
      gammaW
          (oldIndex
            j)
          theta =
        good.gamma
          j
          theta) →
  (∀
      (S :
        Finset
          (Fin
            k))
      (j :
        Fin
          (d +
            (1 :
              ℕ))),
      S.biUnion
          (gammaW
            (oldIndex
              j)) =
        S.biUnion
          (good.gamma
            j)) →
  gammaW
        newIndex
        eta =
      (insert
          gammaOne
          ({
              gammaTwo } :
            Finset
              (Fin
                k)) :
        Finset
          (Fin
            k)) →
  (∀
      (theta :
        Fin
          k),
      theta ≠
          eta →
        gammaW
            newIndex
            theta =
          good.gamma
            (Fin.last
              d)
            theta) →
  GoodHierarchy
    HW := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett U W corrU corrW baseU baseW hcore hclosure H good
      helem eta beta gammaOne gammaTwo f heta hbeta hfc hne hg1 hg2 hfresh hminus d N
      corrTerminal stageW hsize hUW hedge prefixEqOfSegment prefixTransfer stageAtOld stageOld
      stageNew dividerBeforeTerminal HW hcountW stageCopy oldIndex starredCopy missingCopy
      storedCopy lastStar newStored hstageU segmentCopy starToU newIndex gammaW gammaCopy
      gammaSetCopy gammaNewEta gammaNewOther
  exact {
    gamma := gammaW
    twoColors := by
      intro j theta htheta
      by_cases hj : j.val ≤ d
      · let jo : Fin (d + 1) := ⟨j.val, by omega⟩
        have hjEq : j = oldIndex jo := Fin.ext (by simp [oldIndex, jo])
        have hmem : theta ∈ HierarchyStoredColorsAt H jo := by
          rw [← storedCopy jo, ← hjEq]
          exact htheta
        rw [hjEq, gammaCopy jo theta]
        exact good.twoColors jo theta hmem
      · have hjlast : j = newIndex := Fin.ext (by
          apply le_antisymm
          · have := j.isLt; simp [newIndex, N, d] at this ⊢; omega
          · have := j.isLt; simp [newIndex, N, d] at this ⊢; omega)
        subst j
        rw [newStored] at htheta
        by_cases hte : theta = eta
        · subst theta
          simp [gammaNewEta, hne]
        · have hmem : theta ∈ HierarchyStoredColorsAt H (Fin.last d) :=
            (HierarchyTerminalStoredColorsSubsetLast H).1 htheta
          rw [gammaNewOther theta hte]
          exact good.twoColors (Fin.last d) theta hmem
    avoidance := by
      intro j theta htheta c hc
      by_cases hj : j.val ≤ d
      · let jo : Fin (d + 1) := ⟨j.val, by omega⟩
        have hjEq : j = oldIndex jo := Fin.ext (by simp [oldIndex, jo])
        have holdMem : theta ∈ HierarchyStoredColorsAt H jo := by
          rw [← storedCopy jo, ← hjEq]
          exact htheta
        have hcOld : c ∈ good.gamma jo theta := by
          rw [← gammaCopy jo theta, ← hjEq]
          exact hc
        have hold := good.avoidance jo theta holdMem hcOld
        rw [hjEq]
        exact Finset.mem_sdiff.mpr ⟨
          (by simpa [missingCopy jo] using (Finset.mem_sdiff.mp hold).1),
          (by simpa [segmentCopy jo theta] using (Finset.mem_sdiff.mp hold).2)⟩
      · have hjlast : j = newIndex := Fin.ext (by
          apply le_antisymm
          · have := j.isLt; simp [newIndex, N, d] at this ⊢; omega
          · have := j.isLt; simp [newIndex, N, d] at this ⊢; omega)
        subst j
        rw [newStored] at htheta
        have hmissingU : c ∈ TreeMissingColors phi U := by
          by_cases hte : theta = eta
          · subst theta
            have hcP : c ∈ ({gammaOne, gammaTwo} : Finset (Fin k)) := by
              simpa [gammaNewEta] using hc
            have hcCases : c = gammaOne ∨ c = gammaTwo := by
              simpa [Finset.mem_insert, Finset.mem_singleton] using hcP
            rcases hcCases with rfl | rfl
            · rcases Finset.mem_biUnion.mp hg1 with ⟨v, hv, hmiss⟩
              exact Finset.mem_biUnion.mpr ⟨v, (Finset.mem_sdiff.mp hv).1, hmiss⟩
            · rcases Finset.mem_biUnion.mp hg2 with ⟨v, hv, hmiss⟩
              exact Finset.mem_biUnion.mpr ⟨v, (Finset.mem_sdiff.mp hv).1, hmiss⟩
          · have hmem : theta ∈ HierarchyStoredColorsAt H (Fin.last d) :=
              (HierarchyTerminalStoredColorsSubsetLast H).1 htheta
            have hold := (good.avoidance (Fin.last d) theta hmem)
            have hcOld : c ∈ good.gamma (Fin.last d) theta := by
              simpa [gammaNewOther theta hte] using hc
            have hmiss := (Finset.mem_sdiff.mp (hold hcOld)).1
            have hmissStar : c ∈ TreeMissingColors phi
                (HierarchyStarredStage H (Fin.last d)) := by
              have hreserved :=
                (GoodHierarchyReservedDisjoint good (Fin.last d)).1 theta hmem
              exact hreserved hcOld
            have hmissTree : c ∈ TreeMissingColors phi U := by
              rcases Finset.mem_biUnion.mp hmissStar with ⟨v, hv, hmissV⟩
              exact Finset.mem_biUnion.mpr ⟨v,
                TreeSequenceInitialSegmentVertexSetSubset starToU hv, hmissV⟩
            exact hmissTree
        have hstageMissing : HierarchyStageMissingColors HW newIndex =
            TreeMissingColors phi U := by
          change TreeMissingColors phi (HierarchyStarredStage HW newIndex) = _
          rw [lastStar]
        rw [hstageMissing]
        refine Finset.mem_sdiff.mpr ⟨hmissingU, ?_⟩
        intro hseg
        have hseg' : ∃ r : Fin (HW.stage newIndex.succ).length,
            U.length ≤ r.val ∧
            r.val < min (HierarchyFirstMissingPosition phi W theta).val
              (HW.stage newIndex.succ).length ∧
            phi ((HW.stage newIndex.succ).edge r) = some c := by
          change c ∈ HierarchySegmentColors HW newIndex theta at hseg
          dsimp [HierarchySegmentColors] at hseg
          have hnewIndex : newIndex = Fin.last HW.dividerCount := by
            apply Fin.ext
            simp [newIndex, HW, N, d]
          rw [hnewIndex, lastStar] at hseg
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hseg
          have hstageNext : HW.stage (Fin.last HW.dividerCount).succ =
              HW.stage newIndex.succ := congrArg (fun j => HW.stage j.succ) hnewIndex.symm
          rw [hstageNext] at hseg
          exact hseg
        have hWstage : HW.stage newIndex.succ = W := by
          have hi : newIndex.succ = Fin.last (HW.dividerCount + 1) := by
            apply Fin.ext
            simp [newIndex, HW, N, d]
          rw [hi, HW.terminalStage]
        rw [hWstage] at hseg'
        rcases hseg' with ⟨r, hlo, hhi, hcolor⟩
        have hrval : r.val = U.length := by
          have hrlt : r.val < U.length + 1 := by simpa [hsize] using r.isLt
          omega
        have hrEq : r = Fin.cast (by omega : U.length + 1 = W.length)
            (Fin.last U.length) := by
          apply Fin.ext
          simp [hrval]
        have hrEdge : W.edge r = f := by
          rw [hrEq]
          simpa using hedge
        have hcbeta : c = beta := by
          rw [hrEdge, hfc] at hcolor
          injection hcolor with heq
          exact heq.symm
        subst c
        by_cases hte : theta = eta
        · subst theta
          have hbUnion : beta ∈
              (HierarchyTerminalStoredColors H).biUnion (good.gamma (Fin.last d)) :=
            Finset.mem_biUnion.mpr ⟨eta, heta, hbeta⟩
          have hcPair : beta ∈ ({gammaOne, gammaTwo} : Finset (Fin k)) := by
            simpa [gammaNewEta] using hc
          exact (Finset.disjoint_left.mp hfresh) hcPair hbUnion
        · have hthetaLast : theta ∈ HierarchyStoredColorsAt H (Fin.last d) :=
            (HierarchyTerminalStoredColorsSubsetLast H).1 htheta
          have hetaLast : eta ∈ HierarchyStoredColorsAt H (Fin.last d) :=
            (HierarchyTerminalStoredColorsSubsetLast H).1 heta
          have hne' : eta ≠ theta := Ne.symm hte
          have hdis := good.disjointPairs (Fin.last d) eta theta hetaLast hthetaLast hne'
          have hbOld : beta ∈ good.gamma (Fin.last d) theta := by
            simpa [gammaNewOther theta hte] using hc
          exact (Finset.disjoint_left.mp hdis) hbeta hbOld
    disjointPairs := by
      intro j theta rho ht hr hne'
      by_cases hj : j.val ≤ d
      · let jo : Fin (d + 1) := ⟨j.val, by omega⟩
        have hjEq : j = oldIndex jo := Fin.ext (by simp [oldIndex, jo])
        have htOld : theta ∈ HierarchyStoredColorsAt H jo := by
          rw [← storedCopy jo, ← hjEq]
          exact ht
        have hrOld : rho ∈ HierarchyStoredColorsAt H jo := by
          rw [← storedCopy jo, ← hjEq]
          exact hr
        rw [hjEq]
        rw [gammaCopy jo theta, gammaCopy jo rho]
        exact good.disjointPairs jo theta rho htOld hrOld hne'
      · have hjlast : j = newIndex := Fin.ext (by
          apply le_antisymm
          · have := j.isLt; simp [newIndex, N, d] at this ⊢; omega
          · have := j.isLt; simp [newIndex, N, d] at this ⊢; omega)
        subst j
        rw [newStored] at ht hr
        by_cases hte : theta = eta
        · subst theta
          have hrD : rho ∈ HierarchyTerminalStoredColors H := hr
          have hneR : rho ≠ eta := by
            intro heq
            exact hne' heq.symm
          exact Finset.disjoint_left.mpr (by
            intro c hcP hcR
            have hcPair : c ∈ ({gammaOne, gammaTwo} : Finset (Fin k)) := by
              simpa [gammaNewEta] using hcP
            have hcOld : c ∈ good.gamma (Fin.last d) rho := by
              simpa [gammaNewOther rho hneR] using hcR
            exact (Finset.disjoint_left.mp hfresh) hcPair
              (Finset.mem_biUnion.mpr ⟨rho, hrD, hcOld⟩))
        · by_cases hre : rho = eta
          · subst rho
            exact Finset.disjoint_left.mpr (by
              intro c hcOther hcP
              have hcPair : c ∈ ({gammaOne, gammaTwo} : Finset (Fin k)) := by
                simpa [gammaNewEta] using hcP
              have hcOld : c ∈ good.gamma (Fin.last d) theta := by
                simpa [gammaNewOther theta hte] using hcOther
              exact (Finset.disjoint_left.mp hfresh) hcPair
                (Finset.mem_biUnion.mpr ⟨theta, ht, hcOld⟩))
          · have hOld := good.disjointPairs (Fin.last d) theta rho
              ((HierarchyTerminalStoredColorsSubsetLast H).1 ht)
              ((HierarchyTerminalStoredColorsSubsetLast H).1 hr) hne'
            rw [gammaNewOther theta hte, gammaNewOther rho hre]
            exact hOld
    uniqueRefresh := by
      intro i
      by_cases hi : i.val < d
      · let io : Fin d := ⟨i.val, hi⟩
        have hOld := good.uniqueRefresh io
        rcases hOld with ⟨chosen, hchosen, huniq⟩
        have hprev : i.castSucc = oldIndex io.castSucc := by
          apply Fin.ext
          simp [oldIndex, io]
        have hnext : i.succ = oldIndex io.succ := by
          apply Fin.ext
          simp [oldIndex, io]
        have hstageNext : (oldIndex io.succ).castSucc =
            Fin.castLE (by omega) io.succ.castSucc := by
          apply Fin.ext
          simp [oldIndex, io]
        refine ⟨chosen, ?_, ?_⟩
        · rcases hchosen with ⟨hmem, hloc, hrest⟩
          refine ⟨?_, ?_, ?_⟩
          · rw [hnext, storedCopy io.succ]
            exact hmem
          · simpa only [hnext, hprev, hstageNext, stageCopy io.succ.castSucc,
              starredCopy io.castSucc, gammaCopy io.succ] using hloc
          · intro theta htheta hne'
            have hthetaOld : theta ∈ HierarchyStoredColorsAt H io.succ := by
              rw [← storedCopy io.succ, ← hnext]
              exact htheta
            simpa only [hnext, hprev, gammaCopy io.succ, gammaCopy io.castSucc] using
              hrest theta hthetaOld hne'
        · intro theta htheta
          have hthetaOld : theta ∈ HierarchyStoredColorsAt H io.succ := by
            rw [← storedCopy io.succ, ← hnext]
            exact htheta.1
          apply huniq theta
          refine ⟨hthetaOld, ?_, ?_⟩
          · simpa only [hnext, hprev, hstageNext, stageCopy io.succ.castSucc,
              starredCopy io.castSucc, gammaCopy io.succ] using htheta.2.1
          · intro rho hrho hne'
            have hrhoNew : rho ∈ HierarchyStoredColorsAt HW i.succ := by
              rw [hnext, storedCopy io.succ]
              exact hrho
            simpa only [hnext, hprev, gammaCopy io.succ, gammaCopy io.castSucc] using
              htheta.2.2 rho hrhoNew hne'
      · have hlast : i.val = d := by have := i.isLt; omega
        have hidx : i = Fin.last d := Fin.ext (by simp [hlast])
        rw [hidx]
        have hlastIndex : (Fin.last d).succ = Fin.last HW.dividerCount := by
          apply Fin.ext
          change d + 1 = HW.dividerCount
          simpa [d] using hcountW.symm
        have hindexNew : Fin.last HW.dividerCount = newIndex := by
          apply Fin.ext
          simp [newIndex, HW, N, d]
        let P : Finset (Fin k) := {gammaOne, gammaTwo}
        refine ⟨eta, ?_, ?_⟩
        · refine ⟨?_, ?_, ?_⟩
          · rw [hlastIndex, newStored]
            exact heta
          · rw [hlastIndex, hindexNew, gammaNewEta]
            intro c hc
            have hcP : c = gammaOne ∨ c = gammaTwo := by
              simpa [Finset.mem_insert, Finset.mem_singleton] using hc
            rcases hcP with rfl | rfl
            · have hstarIndex : (Fin.last d).castSucc = oldIndex (Fin.last d) := Fin.ext rfl
              rw [hstageU, hstarIndex, starredCopy (Fin.last d)]
              simpa [d] using (Finset.mem_biUnion.mp hg1)
            · have hstarIndex : (Fin.last d).castSucc = oldIndex (Fin.last d) := Fin.ext rfl
              rw [hstageU, hstarIndex, starredCopy (Fin.last d)]
              simpa [d] using (Finset.mem_biUnion.mp hg2)
          · intro theta htheta hne'
            rw [hlastIndex, hindexNew]
            have hstarIndex : (Fin.last d).castSucc = oldIndex (Fin.last d) := Fin.ext rfl
            calc
              gammaW newIndex theta = good.gamma (Fin.last d) theta :=
                gammaNewOther theta hne'
              _ = gammaW (oldIndex (Fin.last d)) theta :=
                (gammaCopy (Fin.last d) theta).symm
              _ = gammaW ((Fin.last d).castSucc) theta := by rw [hstarIndex]
        · intro theta htheta
          by_cases hte : theta = eta
          · exact hte
          · have hthetaOld : theta ∈ HierarchyStoredColorsAt H (Fin.last d) := by
              have hterm : theta ∈ HierarchyTerminalStoredColors H := by
                rw [← newStored, ← hlastIndex]
                exact htheta.1
              exact (HierarchyTerminalStoredColorsSubsetLast H).1 hterm
            have hpair : (good.gamma (Fin.last d) theta).card = 2 :=
              good.twoColors (Fin.last d) theta hthetaOld
            obtain ⟨c, hc⟩ := Finset.card_pos.mp (by omega : 0 < (good.gamma (Fin.last d)
                theta).card)
            have hreservedSubset :=
              (GoodHierarchyReservedDisjoint good (Fin.last d)).1 theta hthetaOld
            have hreserved : c ∈ TreeMissingColors phi
                (HierarchyStarredStage H (Fin.last d)) := hreservedSubset hc
            have hlocal := htheta.2.1
            have hcOld : c ∈ good.gamma (Fin.last d) theta := by
              simpa only [hlastIndex, hindexNew, gammaNewOther theta hte] using hc
            have hcNew : c ∈ gammaW (Fin.last d).succ theta := by
              rw [hlastIndex, hindexNew, gammaNewOther theta hte]
              exact hcOld
            have hcLocal := hlocal hcNew
            have hstarIndex : (Fin.last d).castSucc = oldIndex (Fin.last d) := Fin.ext rfl
            have hUStage : HW.stage (Fin.last d).succ.castSucc = U := by
              have hidx : (Fin.last d).succ.castSucc =
                  (Fin.last HW.dividerCount).castSucc := congrArg Fin.castSucc hlastIndex
              rw [hidx]
              exact hstageU
            have hstarStage : HierarchyStarredStage HW (Fin.last d).castSucc =
                HierarchyStarredStage H (Fin.last d) := by
              rw [hstarIndex, starredCopy (Fin.last d)]
            rcases Finset.mem_biUnion.mp hcLocal with ⟨u, hu, hmiss⟩
            simp only [TreeMissingColors, Finset.mem_biUnion] at hreserved
            rcases hreserved with ⟨a, ha, hmissA⟩
            have haU : a ∈ TreeSequenceVertexSet U :=
              TreeSequenceInitialSegmentVertexSetSubset starToU ha
            have huU : u ∈ TreeSequenceVertexSet U := by
              rw [hUStage] at hu
              exact (Finset.mem_sdiff.mp hu).1
            have hau : a ≠ u := by
              intro heq
              subst u
              have haStarHW : a ∈ TreeSequenceVertexSet
                  (HierarchyStarredStage HW (Fin.last d).castSucc) := by
                rw [hstarStage]
                exact ha
              exact (Finset.mem_sdiff.mp hu).2 haStarHW
            have hdis := helem haU huU hau
            exact False.elim ((Finset.disjoint_left.mp hdis) hmissA hmiss)
    parallelBase := by
      dsimp
      intro hpe
      have hkind : corrW.replacementETT.series.data.kind
          (Fin.last corrW.replacementETT.rounds) =
        corrU.replacementETT.series.data.kind
          (Fin.last corrU.replacementETT.rounds) :=
        (corrTerminal W corrW).2.1.trans (corrTerminal U corrU).2.1.symm
      have hpeU : corrU.replacementETT.series.data.kind
          (Fin.last corrU.replacementETT.rounds) = some TashkinovExtensionKind.PE := by
        rw [← hkind]
        exact hpe
      have hzero : (HierarchyStoredColorsAt HW 0).biUnion (gammaW 0) =
          (HierarchyStoredColorsAt H 0).biUnion (good.gamma 0) := by
        have hidx : (0 : Fin (N + 1)) = oldIndex (0 : Fin (d + 1)) := Fin.ext rfl
        rw [hidx, storedCopy (0 : Fin (d + 1))]
        exact gammaSetCopy (HierarchyStoredColorsAt H 0) 0
      have old := good.parallelBase hpeU
      have htree : corrW.replacementETT.series.data.tree
          (Fin.last corrW.replacementETT.rounds).castSucc =
          corrU.replacementETT.series.data.tree
            (Fin.last corrU.replacementETT.rounds).castSucc :=
        (corrTerminal W corrW).1.trans (corrTerminal U corrU).1.symm
      rw [hcore, hclosure, hzero, htree]
      exact old
    minusClosed := by
      intro i
      by_cases hi : i.val < d
      · let io : Fin d := ⟨i.val, hi⟩
        have hnext : i.succ = oldIndex io.succ := by
          apply Fin.ext
          simp [oldIndex, io]
        have hprev : i.castSucc = oldIndex io.castSucc := by
          apply Fin.ext
          simp [oldIndex, io]
        have hstage : i.succ.castSucc =
            Fin.castLE (by omega) io.succ.castSucc := by
          apply Fin.ext
          simp [io]
        rw [hstage, stageCopy io.succ.castSucc, hnext, hprev, storedCopy io.succ,
          gammaSetCopy (HierarchyStoredColorsAt H io.succ) io.castSucc]
        exact good.minusClosed io
      · have hlast : i.val = d := by have := i.isLt; omega
        have hidx : i = Fin.last d := Fin.ext (by simp [hlast])
        rw [hidx]
        have hlastIndex : (Fin.last d).succ = Fin.last HW.dividerCount := by
          apply Fin.ext
          change d + 1 = HW.dividerCount
          simpa [d] using hcountW.symm
        have hstarIndex : (Fin.last d).castSucc = oldIndex (Fin.last d) := Fin.ext rfl
        have hstageIndex : (Fin.last d).succ.castSucc =
            (Fin.last HW.dividerCount).castSucc := congrArg Fin.castSucc hlastIndex
        rw [hstageIndex, hstageU, hlastIndex, newStored, hstarIndex,
          gammaSetCopy (HierarchyTerminalStoredColors H) (Fin.last d)]
        exact hminus
  }

private abbrev helperContinuation694Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (U W : TreeSequence G e0) (corrU : CorrespondingExtendedTashkinovTree G k e0
        ett phi U) (corrW : CorrespondingExtendedTashkinovTree G k e0 ett phi W) (baseU :
        HierarchyBase corrU.replacementETT phi) (baseW : HierarchyBase corrW.replacementETT phi)
        (hcore : baseW.core = baseU.core), baseW.closure = baseU.closure →
    ∀ (H : TashkinovHierarchy corrU.replacementETT baseU) (good : GoodHierarchy H),
        ColoredVertexSetElementary G phi (TreeSequenceVertexSet U) →
    ∀ (eta beta gammaOne gammaTwo : Fin k) (f : E), eta ∈ HierarchyTerminalStoredColors H → beta ∈
        good.gamma (Fin.last H.dividerCount) eta → phi f = some beta → gammaOne ≠ gammaTwo →
        gammaOne ∈ (TreeSequenceVertexSet U \ TreeSequenceVertexSet (HierarchyStarredStage H
        (Fin.last H.dividerCount))).biUnion (MissingColors G phi) → gammaTwo ∈
        (TreeSequenceVertexSet U \ TreeSequenceVertexSet (HierarchyStarredStage H (Fin.last
        H.dividerCount))).biUnion (MissingColors G phi) → Disjoint (insert gammaOne ({ gammaTwo }
        : Finset (Fin k)) : Finset (Fin k)) ((HierarchyTerminalStoredColors H).biUnion (good.gamma
        (Fin.last H.dividerCount))) → TreeColorSetMinusClosed G phi U
        ((HierarchyTerminalStoredColors H).biUnion (good.gamma (Fin.last H.dividerCount))) →
    let d : ℕ := H.dividerCount;
    let N : ℕ := d + (1 : ℕ);
    ∀ (corrTerminal :
    ∀ (X : TreeSequence G e0) (corr : CorrespondingExtendedTashkinovTree G k e0 ett phi X),
        corr.replacementETT.series.data.tree (Fin.last corr.replacementETT.rounds).castSucc =
        ett.series.data.tree (Fin.last ett.rounds).castSucc ∧ corr.replacementETT.series.data.kind
        (Fin.last corr.replacementETT.rounds) = ett.series.data.kind (Fin.last ett.rounds) ∧
        TashkinovStoredColors corr.replacementETT.series.data (Fin.last
        corr.replacementETT.rounds) = TashkinovStoredColors ett.series.data (Fin.last
        ett.rounds)),
    let stageW : Fin (N + (2 : ℕ)) → TreeSequence G e0 := fun (j : Fin (N + (2 : ℕ))) ↦ if hj :
        (↑j : ℕ) = d + (2 : ℕ) then W else H.stage (⟨(↑j : ℕ), (
    by
        have := corrU.rungAgreement; have := T.positive; have := U.positive;
        omega
    )⟩ : Fin (H.dividerCount + (2 : ℕ)));
    ∀ (hsize : W.length = U.length + (1 : ℕ)) (hUW : TreeSequenceInitialSegment U W), W.edge
        (Fin.cast ((
    by have := U.positive; have := W.positive; omega
    )) (Fin.last U.length)) = f → (
    ∀ {A B C : TreeSequence G e0}, TreeSequenceInitialSegment A B → B = C →
        TreeSequenceInitialSegment A C) →
    ∀ (prefixEqOfSegment :
    ∀ {A B : TreeSequence G e0} (hAB : TreeSequenceInitialSegment A B), A = TreeSequencePrefix B
        A.length A.positive hAB.1) (prefixTransfer :
    ∀ (p : ℕ) (hp : (1 : ℕ) ≤ p) (hpU : p ≤ U.length), TreeSequencePrefix U p hp hpU =
        TreeSequencePrefix W p hp ((
    by have := W.positive; omega
    ))), (
    ∀ (j : Fin (d + (2 : ℕ))), (↑j : ℕ) ≤ d + (1 : ℕ) → TreeSequenceInitialSegment (H.stage j) U)
        →
    ∀ (stageAtOld :
    ∀ (j : Fin (N + (2 : ℕ))) (hj : (↑j : ℕ) ≤ d + (1 : ℕ)), stageW j = H.stage (⟨(↑j : ℕ), (
    by
          have := corrU.rungAgreement; have := T.positive; have := U.positive;
          omega
    )⟩ : Fin (H.dividerCount + (2 : ℕ)))) (stageOld :
    ∀ (j : Fin (d + (2 : ℕ))), stageW (⟨(↑j : ℕ), (
    by
          have := corrU.rungAgreement; have := T.positive; have := U.positive;
          omega
    )⟩ : Fin (N + (2 : ℕ))) = H.stage j) (stageNew : stageW (⟨d + (2 : ℕ), (
    by
         have := corrU.rungAgreement; have := T.positive; have := U.positive;
         omega
    )⟩ : Fin (N + (2 : ℕ))) = W),
    let divW : Fin N → Fin (W.length + (1 : ℕ)) := fun (i : Fin N) ↦ if hi : (↑i : ℕ) < d then
        (⟨(↑(H.dividerPosition (⟨(↑i : ℕ), hi⟩ : Fin H.dividerCount)) : ℕ),
    have hpos : (↑(H.dividerPosition (⟨(↑i : ℕ), hi⟩ : Fin H.dividerCount)) : ℕ) < U.length + (1 :
        ℕ) := (
    by
        have := corrU.rungAgreement; have := T.positive; have := U.positive;
        omega
    );
    have hlen : W.length = U.length + (1 : ℕ) := hsize; Decidable.byContradiction fun (a :
        ¬(↑(H.dividerPosition (⟨(↑i : ℕ), hi⟩ : Fin H.dividerCount)) : ℕ) < W.length + (1 : ℕ)) ↦
        (
    by omega
    )⟩ : Fin (W.length + (1 : ℕ))) else (⟨U.length, (
    by have := U.positive; have := W.positive; omega
    )⟩ : Fin (W.length + (1 : ℕ)));
    ∀ (dividerBeforeTerminal :
    ∀ (i : Fin d), (↑(H.dividerPosition i) : ℕ) < U.length),
    let HW : TashkinovHierarchy corrW.replacementETT baseW := helperHW360 G k e0 input T phi ett U
        W corrU corrW baseU baseW hcore H corrTerminal hsize hUW prefixEqOfSegment prefixTransfer
        stageAtOld stageOld stageNew dividerBeforeTerminal;
    ∀ (hcountW : HW.dividerCount = H.dividerCount + (1 : ℕ)), (
    ∀ (j : Fin (d + (2 : ℕ))), HW.stage (Fin.castLE ((
    by
        have := corrU.rungAgreement
        have := corrW.rungAgreement
        have := T.positive
        have := U.positive
        have := W.positive
        omega
    )) j) = H.stage j) →
    let oldIndex : Fin (d + (1 : ℕ)) → Fin (N + (1 : ℕ)) := fun (j : Fin (d + (1 : ℕ))) ↦ (⟨(↑j :
        ℕ), (
    by
      have := corrU.rungAgreement; have := T.positive; have := U.positive;
      omega
    )⟩ : Fin (N + (1 : ℕ))); (
    ∀ (j : Fin (d + (1 : ℕ))), HierarchyStarredStage HW (oldIndex j) = HierarchyStarredStage H j)
        → (
    ∀ (j : Fin (d + (1 : ℕ))), HierarchyStageMissingColors HW (oldIndex j) =
        HierarchyStageMissingColors H j) →
    ∃ (HW : TashkinovHierarchy corrW.replacementETT baseW) (hcountW : HW.dividerCount =
        H.dividerCount + (1 : ℕ)), (
    ∀ (j : Fin (H.dividerCount + (2 : ℕ))), HW.stage (Fin.castLE ((
    by
         have := corrU.rungAgreement
         have := corrW.rungAgreement
         have := T.positive
         have := U.positive
         have := W.positive
         omega
    )) j) = H.stage j) ∧ HW.stage (Fin.last HW.dividerCount).castSucc = U ∧ HierarchyStarredStage
        HW (Fin.last HW.dividerCount) = U ∧ HW.stage (Fin.last HW.dividerCount).succ = W ∧ (
    ∀ (i : Fin H.dividerCount), (↑(HW.dividerPosition (Fin.castLE ((
    by
               have := corrU.rungAgreement
               have := corrW.rungAgreement
               have := T.positive
               have := U.positive
               have := W.positive
               omega
    )) i)) : ℕ) = (↑(H.dividerPosition i) : ℕ)) ∧ (↑(HW.dividerPosition (Fin.cast ((
    by
               have := corrU.rungAgreement
               have := corrW.rungAgreement
               have := T.positive
               have := U.positive
               have := W.positive
               omega
    )) (Fin.last H.dividerCount))) : ℕ) = U.length ∧ (
    ∀ (j : Fin (H.dividerCount + (1 : ℕ))), HierarchyStoredColorsAt HW (Fin.castLE ((
    by
               have := corrU.rungAgreement
               have := corrW.rungAgreement
               have := T.positive
               have := U.positive
               have := W.positive
               omega
    )) j) = HierarchyStoredColorsAt H j) ∧ HierarchyStoredColorsAt HW (Fin.last HW.dividerCount) =
        HierarchyTerminalStoredColors H ∧
    ∃ (goodW : GoodHierarchy HW), (
    ∀ (j : Fin (H.dividerCount + (1 : ℕ))) (theta : Fin k), goodW.gamma (Fin.castLE ((
    by
                  have := corrU.rungAgreement
                  have := corrW.rungAgreement
                  have := T.positive
                  have := U.positive
                  have := W.positive
                  omega
    )) j) theta = good.gamma j theta) ∧ goodW.gamma (Fin.last HW.dividerCount) eta = (insert
        gammaOne ({ gammaTwo } : Finset (Fin k)) : Finset (Fin k)) ∧
    ∀ theta ∈ HierarchyTerminalStoredColors H, theta ≠ eta → goodW.gamma (Fin.last
        HW.dividerCount) theta = good.gamma (Fin.last H.dividerCount) theta

private theorem helper_starToU_526.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (U W : TreeSequence G e0) (corrU : CorrespondingExtendedTashkinovTree G k e0
        ett phi U) (corrW : CorrespondingExtendedTashkinovTree G k e0 ett phi W) (baseU :
        HierarchyBase corrU.replacementETT phi) (baseW : HierarchyBase corrW.replacementETT phi)
        (_ : baseW.core = baseU.core) (H : TashkinovHierarchy corrU.replacementETT baseU),
    let d : ℕ := H.dividerCount;
    let N : ℕ := d + (1 : ℕ);
    ∀ (_ : (
    ∀ (X : TreeSequence G e0) (corr : CorrespondingExtendedTashkinovTree G k e0 ett phi X),
        corr.replacementETT.series.data.tree (Fin.last corr.replacementETT.rounds).castSucc =
        ett.series.data.tree (Fin.last ett.rounds).castSucc ∧ corr.replacementETT.series.data.kind
        (Fin.last corr.replacementETT.rounds) = ett.series.data.kind (Fin.last ett.rounds) ∧
        TashkinovStoredColors corr.replacementETT.series.data (Fin.last
        corr.replacementETT.rounds) = TashkinovStoredColors ett.series.data (Fin.last
        ett.rounds))),
    let stageW : Fin (N + (2 : ℕ)) → TreeSequence G e0 := fun (j : Fin (N + (2 : ℕ))) ↦ if hj :
        (↑j : ℕ) = d + (2 : ℕ) then W else H.stage (⟨(↑j : ℕ), (
    by omega
    )⟩ : Fin (H.dividerCount + (2 : ℕ)));
    ∀ (hsize : W.length = U.length + (1 : ℕ)) (_ : TreeSequenceInitialSegment U W) (_ : (
    ∀ {A B C : TreeSequence G e0} (_ : TreeSequenceInitialSegment A B) (_ : B = C),
        TreeSequenceInitialSegment A C)) (_ : (
    ∀ {A B : TreeSequence G e0} (hAB : TreeSequenceInitialSegment A B), A = TreeSequencePrefix B
        A.length A.positive hAB.1)) (_ : (
    ∀ (p : ℕ) (hp : (1 : ℕ) ≤ p) (hpU : p ≤ U.length), TreeSequencePrefix U p hp hpU =
        TreeSequencePrefix W p hp ((
    by omega
    )))) (_ : (
    ∀ (j : Fin (N + (2 : ℕ))) (hj : (↑j : ℕ) ≤ d + (1 : ℕ)), stageW j = H.stage (⟨(↑j : ℕ), (
    by omega
    )⟩ : Fin (H.dividerCount + (2 : ℕ))))) (_ : (
    ∀ (j : Fin (d + (2 : ℕ))), stageW (⟨(↑j : ℕ), (
    by omega
    )⟩ : Fin (N + (2 : ℕ))) = H.stage j)) (_ : stageW (⟨d + (2 : ℕ), (
    by omega
    )⟩ : Fin (N + (2 : ℕ))) = W) (_ : (
    ∀ (i : Fin d), (↑(H.dividerPosition i) : ℕ) < U.length)), TreeSequenceInitialSegment
        (HierarchyStarredStage H (Fin.last d)) U := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett U W corrU corrW baseU baseW hcore H d N corrTerminal
      stageW hsize hUW segmentEqRight prefixEqOfSegment prefixTransfer stageAtOld stageOld
      stageNew dividerBeforeTerminal
  by_cases hd : d = 0
  · have hstar : HierarchyStarredStage H (Fin.last d) = baseU.core := by
      have hz : Fin.last d = (0 : Fin (d + 1)) := by
        apply Fin.ext
        simp [hd]
      rw [hz]
      simp [HierarchyStarredStage]
    rw [hstar]
    have hidx : (⟨1, by omega⟩ : Fin (d + 2)) = Fin.last (d + 1) := by
      apply Fin.ext
      simp [hd]
    have hstage : H.stage ⟨1, by omega⟩ = U := by
      rw [hidx, H.terminalStage]
    exact segmentEqRight H.coreInsideFirst hstage
  · let ii : Fin d := ⟨d - 1, by omega⟩
    have hlast : ii.succ = Fin.last d := by
      apply Fin.ext
      simp [ii]
      omega
    have hstar : HierarchyStarredStage H (Fin.last d) =
        H.stage ii.succ.castSucc := by
      rw [← hlast]
      simp [HierarchyStarredStage]
    rw [hstar]
    have hterm : H.stage ii.succ.succ = U := by
      have hi : ii.succ.succ = Fin.last (d + 1) := by
        apply Fin.ext
        simp [ii]
        omega
      rw [hi, H.terminalStage]
    exact segmentEqRight (H.nested ii.succ) hterm

private theorem helper_continuation_694.{u_1, u_2} :
    helperContinuation694Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett U W corrU corrW baseU baseW hcore hclosure H good
      helem eta beta gammaOne gammaTwo f heta hbeta hfc hne hg1 hg2 hfresh hminus d N
      corrTerminal stageW hsize hUW hedge segmentEqRight prefixEqOfSegment prefixTransfer
      stageToU stageAtOld stageOld stageNew divW dividerBeforeTerminal HW hcountW stageCopy
      oldIndex starredCopy missingCopy
  have terminalStoredEq :
      TashkinovStoredColors corrW.replacementETT.series.data
          (Fin.last corrW.replacementETT.rounds) =
        TashkinovStoredColors corrU.replacementETT.series.data
          (Fin.last corrU.replacementETT.rounds) := by
    exact (corrTerminal W corrW).2.2.trans (corrTerminal U corrU).2.2.symm
  have storedCopy (j : Fin (d + 1)) :
      HierarchyStoredColorsAt HW (oldIndex j) = HierarchyStoredColorsAt H j := by
    change (TashkinovStoredColors corrW.replacementETT.series.data
        (Fin.last corrW.replacementETT.rounds) \
        TreeMissingColors phi (HierarchyStarredStage HW (oldIndex j))) =
      (TashkinovStoredColors corrU.replacementETT.series.data
        (Fin.last corrU.replacementETT.rounds) \
        TreeMissingColors phi (HierarchyStarredStage H j))
    rw [terminalStoredEq, starredCopy j]
  have lastStar : HierarchyStarredStage HW (Fin.last HW.dividerCount) = U := by
    change HW.stage (Fin.last d).succ.castSucc = U
    let j : Fin (d + 2) := ⟨d + 1, by omega⟩
    have hidx : (Fin.last d).succ.castSucc = Fin.castLE (by omega) j := Fin.ext rfl
    rw [hidx, stageCopy j]
    exact H.terminalStage
  have newStored :
      HierarchyStoredColorsAt HW (Fin.last HW.dividerCount) =
        HierarchyTerminalStoredColors H := by
    change (TashkinovStoredColors corrW.replacementETT.series.data
        (Fin.last corrW.replacementETT.rounds) \
        TreeMissingColors phi (HierarchyStarredStage HW (Fin.last HW.dividerCount))) =
      (TashkinovStoredColors corrU.replacementETT.series.data
        (Fin.last corrU.replacementETT.rounds) \
        TreeMissingColors phi U)
    rw [terminalStoredEq, lastStar]
  have hstageU : HW.stage (Fin.last HW.dividerCount).castSucc = U := by
    let j : Fin (d + 2) := ⟨d + 1, by omega⟩
    have hidx : (Fin.last HW.dividerCount).castSucc = Fin.castLE (by omega) j :=
      Fin.ext (by
        change d + 1 = HW.dividerCount
        simpa [d] using hcountW.symm)
    rw [hidx, stageCopy j]
    have hterm : j = Fin.last (d + 1) := Fin.ext (by simp [j])
    rw [hterm]
    simpa [d] using H.terminalStage
  have stageMissingEq (j : Fin (d + 1)) :
      HierarchyStageMissingColors HW (oldIndex j) =
        HierarchyStageMissingColors H j := missingCopy j
  have segmentCopy (j : Fin (d + 1)) (theta : Fin k) :
      HierarchySegmentColors HW (oldIndex j) theta =
        HierarchySegmentColors H j theta := by
    have hnextU : TreeSequenceInitialSegment (H.stage j.succ) U :=
      stageToU j.succ (by omega)
    have hcut := HierarchyFirstMissingPositionPrefixCutoff phi U W hUW theta
      (H.stage j.succ).length hnextU.1
    unfold HierarchySegmentColors
    dsimp
    have hnextIdx : (oldIndex j).succ =
        (⟨j.val + 1, by omega⟩ : Fin (N + 2)) := Fin.ext rfl
    have hstageNext : HW.stage (oldIndex j).succ = H.stage j.succ := by
      rw [hnextIdx]
      exact stageCopy j.succ
    rw [starredCopy j, hstageNext]
    apply Finset.ext
    intro c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> intro h
    · rcases h with ⟨r, hlo, hhi, hcolor⟩
      refine ⟨r, hlo, ?_, hcolor⟩
      simpa [hcut] using hhi
    · rcases h with ⟨r, hlo, hhi, hcolor⟩
      refine ⟨r, hlo, ?_, hcolor⟩
      simpa [hcut] using hhi
  have starToU : TreeSequenceInitialSegment
      (HierarchyStarredStage H (Fin.last d)) U := by
    apply helper_starToU_526 <;> assumption
  let newIndex : Fin (N + 1) := Fin.last N
  let gammaW : Fin (N + 1) → Fin k → Finset (Fin k) := fun j theta =>
    if hj : j.val ≤ d then good.gamma ⟨j.val, by omega⟩ theta
    else if theta = eta then {gammaOne, gammaTwo}
      else good.gamma (Fin.last d) theta
  have gammaCopy (j : Fin (d + 1)) (theta : Fin k) :
      gammaW (oldIndex j) theta = good.gamma j theta := by
    simp only [gammaW]
    split
    · congr 1
    · rename_i h
      have : (oldIndex j).val ≤ d := by simp [oldIndex]; omega
      contradiction
  have gammaSetCopy (S : Finset (Fin k)) (j : Fin (d + 1)) :
      S.biUnion (gammaW (oldIndex j)) = S.biUnion (good.gamma j) := by
    apply Finset.ext
    intro c
    simp only [Finset.mem_biUnion]
    constructor
    · rintro ⟨theta, htheta, hc⟩
      exact ⟨theta, htheta, (by simpa only [gammaCopy] using hc)⟩
    · rintro ⟨theta, htheta, hc⟩
      exact ⟨theta, htheta, (by simpa only [gammaCopy] using hc)⟩
  have gammaNewEta : gammaW newIndex eta = {gammaOne, gammaTwo} := by
    have hj : newIndex.val = d + 1 := by simp [newIndex, N, d]
    simp [gammaW, newIndex, N, d]
  have gammaNewOther (theta : Fin k) (hneEta : theta ≠ eta) :
      gammaW newIndex theta = good.gamma (Fin.last d) theta := by
    have hj : newIndex.val = d + 1 := by simp [newIndex, N, d]
    simp [gammaW, newIndex, N, d, hneEta]
  let goodW := @helperGoodW888 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@U) (@W) (@corrU) (@corrW) (@baseU) (@baseW)
      (@hcore) (@hclosure) (@H) (@good) (@helem) (@eta) (@beta) (@gammaOne) (@gammaTwo) (@f) (@heta)
      (@hbeta) (@hfc) (@hne) (@hg1) (@hg2) (@hfresh) (@hminus) (@corrTerminal) (@hsize) (@hUW)
      (@hedge) (@prefixEqOfSegment) (@prefixTransfer) (@stageAtOld) (@stageOld) (@stageNew)
      (@dividerBeforeTerminal) (@hcountW) (@stageCopy) (@starredCopy) (@missingCopy) (@storedCopy)
      (@lastStar) (@newStored) (@hstageU) (@segmentCopy) (@starToU) (@gammaCopy) (@gammaSetCopy)
      (@gammaNewEta) (@gammaNewOther)
  have hpreceding : HW.stage (Fin.last HW.dividerCount).castSucc = U := by
    exact hstageU
  have hstarred : HierarchyStarredStage HW (Fin.last HW.dividerCount) = U := lastStar
  have hterminal : HW.stage (Fin.last HW.dividerCount).succ = W := HW.terminalStage
  refine ⟨HW, hcountW, ?_, hpreceding, hstarred, hterminal, ?_, ?_, ?_, newStored,
    goodW, ?_, ?_, ?_⟩
  · intro j
    simpa [hcountW] using stageCopy j
  · intro i
    change (divW (Fin.castLE (by omega) i)).val = (H.dividerPosition i).val
    have hbound : H.dividerCount ≤ HW.dividerCount := by
      rw [hcountW]
      omega
    have hidx : Fin.castLE (by omega) i = Fin.castLE hbound i := Fin.ext rfl
    rw [hidx]
    have hi : i.val < d := by
      change i.val < H.dividerCount
      exact i.isLt
    simp [divW, hi]
  · change (HW.dividerPosition (Fin.last d)).val = U.length
    have hnot : ¬ (Fin.last N).val < d := by simp [N, d]
    simp [HW, d]
  · intro j
    have hidx : Fin.castLE (by omega) j = oldIndex j := Fin.ext rfl
    rw [hidx]
    exact storedCopy j
  · intro j theta
    have hidx : Fin.castLE (by omega) j = oldIndex j := Fin.ext rfl
    rw [hidx]
    exact gammaCopy j theta
  · change gammaW newIndex eta = {gammaOne, gammaTwo}
    exact gammaNewEta
  · intro theta htheta hneEta
    change gammaW newIndex theta = good.gamma (Fin.last d) theta
    exact gammaNewOther theta hneEta

theorem P2940_T1_OneDividerRefresh
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (U W : TreeSequence G e0)
    (corrU : CorrespondingExtendedTashkinovTree G k e0 ett phi U)
    (corrW : CorrespondingExtendedTashkinovTree G k e0 ett phi W)
    (baseU : HierarchyBase corrU.replacementETT phi)
    (baseW : HierarchyBase corrW.replacementETT phi)
    (hcore : baseW.core = baseU.core)
    (hclosure : baseW.closure = baseU.closure)
    (H : TashkinovHierarchy corrU.replacementETT baseU)
    (good : GoodHierarchy H)
    (helem : ColoredVertexSetElementary G phi (TreeSequenceVertexSet U))
    (eta beta gammaOne gammaTwo : Fin k) (f : E)
    (heta : eta ∈ HierarchyTerminalStoredColors H)
    (hbeta : beta ∈ good.gamma (Fin.last H.dividerCount) eta)
    (hfc : phi f = some beta) (hadjoin : TreeSequenceAdjoinEdge U f W)
    (hne : gammaOne ≠ gammaTwo)
    (hg1 : gammaOne ∈ (TreeSequenceVertexSet U \ TreeSequenceVertexSet
      (HierarchyStarredStage H (Fin.last H.dividerCount))).biUnion
        (MissingColors G phi))
    (hg2 : gammaTwo ∈ (TreeSequenceVertexSet U \ TreeSequenceVertexSet
      (HierarchyStarredStage H (Fin.last H.dividerCount))).biUnion
        (MissingColors G phi))
    (hfresh : Disjoint {gammaOne, gammaTwo}
      ((HierarchyTerminalStoredColors H).biUnion
        (good.gamma (Fin.last H.dividerCount))))
    (hminus : TreeColorSetMinusClosed G phi U
      ((HierarchyTerminalStoredColors H).biUnion
        (good.gamma (Fin.last H.dividerCount)))) :
    exists HW : TashkinovHierarchy corrW.replacementETT baseW,
      exists hcountW : HW.dividerCount = H.dividerCount + 1,
        (forall j : Fin (H.dividerCount + 2),
          HW.stage (Fin.castLE (by omega) j) = H.stage j) /\
        HW.stage (Fin.last HW.dividerCount).castSucc = U /\
        HierarchyStarredStage HW (Fin.last HW.dividerCount) = U /\
        HW.stage (Fin.last HW.dividerCount).succ = W /\
        (forall i : Fin H.dividerCount,
          (HW.dividerPosition (Fin.castLE (by omega) i)).val =
            (H.dividerPosition i).val) /\
        (HW.dividerPosition (Fin.cast hcountW.symm
          (Fin.last H.dividerCount))).val = U.length /\
        (forall j : Fin (H.dividerCount + 1),
          HierarchyStoredColorsAt HW (Fin.castLE (by omega) j) =
            HierarchyStoredColorsAt H j) /\
        HierarchyStoredColorsAt HW (Fin.last HW.dividerCount) =
          HierarchyTerminalStoredColors H /\
        exists goodW : GoodHierarchy HW,
          (forall j : Fin (H.dividerCount + 1), forall theta : Fin k,
            goodW.gamma (Fin.castLE (by omega) j) theta = good.gamma j theta) /\
          goodW.gamma (Fin.last HW.dividerCount) eta = {gammaOne, gammaTwo} /\
          (forall theta : Fin k, theta ∈ HierarchyTerminalStoredColors H ->
            theta ≠ eta -> goodW.gamma (Fin.last HW.dividerCount) theta =
              good.gamma (Fin.last H.dividerCount) theta) := by
  classical
  let d := H.dividerCount
  let N := d + 1
  have corrTerminal (X : TreeSequence G e0)
      (corr : CorrespondingExtendedTashkinovTree G k e0 ett phi X) :
      corr.replacementETT.series.data.tree (Fin.last corr.replacementETT.rounds).castSucc =
          ett.series.data.tree (Fin.last ett.rounds).castSucc ∧
        corr.replacementETT.series.data.kind (Fin.last corr.replacementETT.rounds) =
          ett.series.data.kind (Fin.last ett.rounds) ∧
        TashkinovStoredColors corr.replacementETT.series.data
            (Fin.last corr.replacementETT.rounds) =
          TashkinovStoredColors ett.series.data (Fin.last ett.rounds) := by
    exact corr.terminalData
  let stageW : Fin (N + 2) → TreeSequence G e0 := fun j =>
    if hj : j.val = d + 2 then W else H.stage ⟨j.val, by omega⟩
  rcases hadjoin with ⟨hsize, hUW, hedge⟩
  have segmentTrans {A B C : TreeSequence G e0}
      (hAB : TreeSequenceInitialSegment A B)
      (hBC : TreeSequenceInitialSegment B C) :
      TreeSequenceInitialSegment A C := by
    exact hAB.trans hBC
  have segmentRefl (A : TreeSequence G e0) : TreeSequenceInitialSegment A A :=
    ⟨le_rfl, (by intro i; rfl), (by intro i; rfl)⟩
  have segmentEqRight {A B C : TreeSequence G e0}
      (hAB : TreeSequenceInitialSegment A B) (hBC : B = C) :
      TreeSequenceInitialSegment A C := by
    cases hBC
    exact hAB
  have prefixEqOfSegment {A B : TreeSequence G e0}
      (hAB : TreeSequenceInitialSegment A B) :
      A = TreeSequencePrefix B A.length A.positive hAB.1 := by
    cases A with
    | mk la pa va ea via eia fea aa =>
      cases B with
      | mk lb pb vb eb vib eib feb ab =>
        rw [TreeSequence.mk.injEq]
        refine ⟨rfl, ?_, ?_⟩
        · apply heq_of_eq
          funext i
          simpa [TreeSequencePrefix] using (hAB.2.1 i).symm
        · apply heq_of_eq
          funext i
          simpa [TreeSequencePrefix] using (hAB.2.2 i).symm
  have prefixTransfer (p : Nat) (hp : 1 ≤ p) (hpU : p ≤ U.length) :
      TreeSequencePrefix U p hp hpU =
        TreeSequencePrefix W p hp (by omega) := by
    rw [TreeSequencePrefix, TreeSequencePrefix]
    congr 1
    · funext i
      have h := hUW.2.1 (Fin.castLE (Nat.succ_le_succ hpU) i)
      simpa [TreeSequencePrefix] using h.symm
    · funext i
      have h := hUW.2.2 (Fin.castLE hpU i)
      simpa [TreeSequencePrefix] using h.symm
  have stageSegment : ∀ (a r : Nat) (h : a + r ≤ d + 1),
      TreeSequenceInitialSegment
        (H.stage ⟨a, by have := h; omega⟩)
        (H.stage ⟨a + r, by exact Nat.lt_succ_of_le h⟩) := by
    intro a r
    induction r with
    | zero =>
        intro h
        exact segmentRefl _
    | succ r ih =>
        intro h
        have hprev : a + r ≤ d + 1 := by omega
        exact segmentTrans (ih hprev) (H.nested ⟨a + r, by omega⟩)
  have stageToU (j : Fin (d + 2)) (hj : j.val ≤ d + 1) :
      TreeSequenceInitialSegment (H.stage j) U := by
    have hseg := stageSegment j.val (d + 1 - j.val) (by omega)
    have hidx : (⟨j.val + (d + 1 - j.val), by omega⟩ : Fin (d + 2)) =
        Fin.last (d + 1) := by
      apply Fin.ext
      simp
      omega
    rw [hidx, H.terminalStage] at hseg
    have hstart : (⟨j.val, by omega⟩ : Fin (d + 2)) = j := by
      apply Fin.ext
      rfl
    rw [hstart] at hseg
    exact hseg
  have stageAtOld (j : Fin (N + 2)) (hj : j.val ≤ d + 1) :
      stageW j = H.stage ⟨j.val, by omega⟩ := by
    have hneq : j.val ≠ d + 2 := by omega
    simp [stageW, hneq]
  have stageOld (j : Fin (d + 2)) :
      stageW ⟨j.val, by omega⟩ = H.stage j := by
    have hneq : j.val ≠ d + 2 := by have := j.isLt; omega
    simp only [stageW, hneq]
    congr 1
  have stageNew : stageW ⟨d + 2, by omega⟩ = W := by
    simp [stageW]
  let divW : Fin N → Fin (W.length + 1) := fun i =>
    if hi : i.val < d then
      ⟨(H.dividerPosition ⟨i.val, hi⟩).val, by
        have hpos := (H.dividerPosition ⟨i.val, hi⟩).isLt
        have hlen := hsize
        omega⟩
    else ⟨U.length, by omega⟩
  have dividerBeforeTerminal (i : Fin d) :
      (H.dividerPosition i).val < U.length := by
    have hstrict := H.strict i.succ
    let next : Fin (d + 2) := i.succ.succ
    have hnext : next.val ≤ d + 1 := by
      change i.val + 2 ≤ d + 1
      omega
    have htoU := stageToU next hnext
    have hposEq : (H.dividerPosition i).val =
        (H.stage i.succ.castSucc).length := by
      have hidx : (⟨i.val + 1, by omega⟩ : Fin (d + 2)) =
          i.succ.castSucc := Fin.ext rfl
      rw [← hidx, H.dividerStage i]
      rfl
    rw [hposEq]
    exact Nat.lt_of_lt_of_le hstrict htoU.1
  let HW := @helperHW360 (@V) (@E) inferInstance inferInstance inferInstance inferInstance (@G)
      (@k) (@e0) (@input) (@T) (@phi) (@ett) (@U) (@W) (@corrU) (@corrW) (@baseU) (@baseW) (@hcore)
      (@H) (@corrTerminal) (@hsize) (@hUW) (@prefixEqOfSegment) (@prefixTransfer) (@stageAtOld)
      (@stageOld) (@stageNew) (@dividerBeforeTerminal)
  have hcountW : HW.dividerCount = H.dividerCount + 1 := by rfl
  have stageCopy (j : Fin (d + 2)) :
      HW.stage (Fin.castLE (by omega) j) = H.stage j := by
    change stageW (Fin.castLE (by omega) j) = H.stage j
    have hidx : Fin.castLE (by omega) j = (⟨j.val, by omega⟩ : Fin (N + 2)) :=
      Fin.ext rfl
    rw [hidx]
    exact stageOld j
  let oldIndex (j : Fin (d + 1)) : Fin (N + 1) := ⟨j.val, by omega⟩
  have starredCopy (j : Fin (d + 1)) :
      HierarchyStarredStage HW (oldIndex j) = HierarchyStarredStage H j := by
    refine Fin.cases ?_ (fun i => ?_) j
    · simpa [oldIndex, HierarchyStarredStage] using hcore
    · change HW.stage (⟨i.val + 1, by omega⟩ : Fin (N + 2)) =
        H.stage (⟨i.val + 1, by omega⟩ : Fin (d + 2))
      exact stageCopy ⟨i.val + 1, by omega⟩
  have missingCopy (j : Fin (d + 1)) :
      HierarchyStageMissingColors HW (oldIndex j) =
        HierarchyStageMissingColors H j := by
    refine Fin.cases ?_ (fun i => ?_) j
    · change TreeMissingColors phi
          (corrW.replacementETT.series.data.tree
            (Fin.last corrW.replacementETT.rounds).castSucc) =
        TreeMissingColors phi
          (corrU.replacementETT.series.data.tree
            (Fin.last corrU.replacementETT.rounds).castSucc)
      exact congrArg (TreeMissingColors phi)
        ((corrTerminal W corrW).1.trans (corrTerminal U corrU).1.symm)
    · change TreeMissingColors phi (HW.stage (⟨i.val + 1, by omega⟩ : Fin (N + 2))) =
        TreeMissingColors phi (H.stage (⟨i.val + 1, by omega⟩ : Fin (d + 2)))
      exact congrArg (TreeMissingColors phi) (stageCopy ⟨i.val + 1, by omega⟩)
  apply helper_continuation_694 <;> assumption
end GoldbergSeymour

end
