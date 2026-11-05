/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.StarredPrefixPreparation
public import LeanPool.GoldbergSeymour.NestedOddMissingPair
public import LeanPool.GoldbergSeymour.OneDividerRefresh

/-!
# Algorithm Five Six Fixed Root Refresh

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_hTnW_292.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (J W : TreeSequence G e0),
    let Tn : TreeSequence G e0 := ett.series.data.tree (Fin.last ett.rounds).castSucc;
    ∀ (_ : TreeSequenceInitialSegment Tn J) (_ : TreeSequenceInitialSegment J W),
    TreeSequenceInitialSegment Tn W := by
  classical
  intro V E _ _ _ G k e0 input T phi ett J W Tn hTnJ hJWsegment
  refine ⟨hTnJ.1.trans hJWsegment.1, ?_, ?_⟩
  · intro i
    exact (hJWsegment.2.1 (Fin.castLE (Nat.succ_le_succ hTnJ.1) i)).trans
      (hTnJ.2.1 i)
  · intro i
    exact (hJWsegment.2.2 (Fin.castLE hTnJ.1 i)).trans (hTnJ.2.2 i)

private theorem helper_hcarry_334.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (_ : HierarchyBase ett phi) (U : TreeSequence G e0) (corrU :
        CorrespondingExtendedTashkinovTree G k e0 ett phi U) (baseU : HierarchyBase
        corrU.replacementETT phi) (H : TashkinovHierarchy corrU.replacementETT baseU) (_ :
        GoodHierarchy H) (W : TreeSequence G e0) (corrW : CorrespondingExtendedTashkinovTree G k
        e0 ett phi W) (baseW : HierarchyBase corrW.replacementETT phi) (HW : TashkinovHierarchy
        corrW.replacementETT baseW) (hcountW : HW.dividerCount = H.dividerCount + (1 : ℕ)) (V' :
        TreeSequence G e0) (corrV : CorrespondingExtendedTashkinovTree G k e0 ett phi V') (baseV :
        HierarchyBase corrV.replacementETT phi) (K : TashkinovHierarchy corrV.replacementETT
        baseV) (hcount : K.dividerCount = HW.dividerCount) (_ : (
    ∀ (j : Fin (K.dividerCount + (1 : ℕ))),
    have jo : Fin (HW.dividerCount + (1 : ℕ)) := Fin.cast (
    by omega
    ) j; K.stage j.castSucc = HW.stage jo.castSucc ∧ HierarchyStarredStage K j =
        HierarchyStarredStage HW jo ∧ HierarchyStoredColorsAt K j = HierarchyStoredColorsAt HW jo
        ∧ HierarchyStageMissingColors K j = HierarchyStageMissingColors HW jo)) (j : Fin
        (HW.dividerCount + (1 : ℕ))), K.stage (⟨(↑j : ℕ),
    by omega
    ⟩ : Fin (K.dividerCount + (2 : ℕ))) = HW.stage j.castSucc ∧ HierarchyStarredStage K (⟨(↑j :
        ℕ),
    by omega
    ⟩ : Fin (K.dividerCount + (1 : ℕ))) = HierarchyStarredStage HW j ∧ HierarchyStoredColorsAt K
        (⟨(↑j : ℕ),
    by omega
    ⟩ : Fin (K.dividerCount + (1 : ℕ))) = HierarchyStoredColorsAt HW j := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base U corrU baseU H good W corrW baseW HW hcountW V'
      corrV baseV K hcount hstagesV j
  have hh := hstagesV (⟨j.val, by omega⟩ : Fin (K.dividerCount + 1))
  dsimp only at hh
  have hi : Fin.cast (congrArg (fun n : Nat => n + 1) hcount)
      (⟨j.val, by omega⟩ : Fin (K.dividerCount + 1)) = j := Fin.ext rfl
  rw [hi] at hh
  exact ⟨hh.1, hh.2.1, hh.2.2.1⟩

private theorem helper_hprecedingV_354.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (_ : HierarchyBase ett phi) (U : TreeSequence G e0) (corrU :
        CorrespondingExtendedTashkinovTree G k e0 ett phi U) (baseU : HierarchyBase
        corrU.replacementETT phi) (H : TashkinovHierarchy corrU.replacementETT baseU) (_ :
        GoodHierarchy H) (W : TreeSequence G e0) (corrW : CorrespondingExtendedTashkinovTree G k
        e0 ett phi W) (baseW : HierarchyBase corrW.replacementETT phi) (HW : TashkinovHierarchy
        corrW.replacementETT baseW) (hcountW : HW.dividerCount = H.dividerCount + (1 : ℕ)) (_ :
        HW.stage (Fin.last HW.dividerCount).castSucc = U) (V' : TreeSequence G e0) (corrV :
        CorrespondingExtendedTashkinovTree G k e0 ett phi V') (baseV : HierarchyBase
        corrV.replacementETT phi) (K : TashkinovHierarchy corrV.replacementETT baseV) (hcount :
        K.dividerCount = HW.dividerCount) (_ : (
    ∀ (j : Fin (HW.dividerCount + (1 : ℕ))), K.stage (⟨(↑j : ℕ),
    by omega
    ⟩ : Fin (K.dividerCount + (2 : ℕ))) = HW.stage j.castSucc ∧ HierarchyStarredStage K (⟨(↑j :
        ℕ),
    by omega
    ⟩ : Fin (K.dividerCount + (1 : ℕ))) = HierarchyStarredStage HW j ∧ HierarchyStoredColorsAt K
        (⟨(↑j : ℕ),
    by omega
    ⟩ : Fin (K.dividerCount + (1 : ℕ))) = HierarchyStoredColorsAt HW j)) (_ : (⟨HW.dividerCount,
    by omega
    ⟩ : Fin (K.dividerCount + (2 : ℕ))) = (Fin.last K.dividerCount).castSucc), K.stage (Fin.last
        K.dividerCount).castSucc = U := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base U corrU baseU H good W corrW baseW HW hcountW
      hprecedingW V' corrV baseV K hcount hcarry hlastStageIndex
  have hh := (hcarry (Fin.last HW.dividerCount)).1
  change K.stage ⟨HW.dividerCount, by omega⟩ =
    HW.stage (Fin.last HW.dividerCount).castSucc at hh
  rw [hlastStageIndex] at hh
  exact hh.trans hprecedingW

private theorem helper_hstarV_360.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (_ : HierarchyBase ett phi) (U : TreeSequence G e0) (corrU :
        CorrespondingExtendedTashkinovTree G k e0 ett phi U) (baseU : HierarchyBase
        corrU.replacementETT phi) (H : TashkinovHierarchy corrU.replacementETT baseU) (_ :
        GoodHierarchy H) (W : TreeSequence G e0) (corrW : CorrespondingExtendedTashkinovTree G k
        e0 ett phi W) (baseW : HierarchyBase corrW.replacementETT phi) (HW : TashkinovHierarchy
        corrW.replacementETT baseW) (hcountW : HW.dividerCount = H.dividerCount + (1 : ℕ)) (_ :
        HierarchyStarredStage HW (Fin.last HW.dividerCount) = U) (V' : TreeSequence G e0) (corrV :
        CorrespondingExtendedTashkinovTree G k e0 ett phi V') (baseV : HierarchyBase
        corrV.replacementETT phi) (K : TashkinovHierarchy corrV.replacementETT baseV) (hcount :
        K.dividerCount = HW.dividerCount) (_ : (
    ∀ (j : Fin (HW.dividerCount + (1 : ℕ))), K.stage (⟨(↑j : ℕ),
    by omega
    ⟩ : Fin (K.dividerCount + (2 : ℕ))) = HW.stage j.castSucc ∧ HierarchyStarredStage K (⟨(↑j :
        ℕ),
    by omega
    ⟩ : Fin (K.dividerCount + (1 : ℕ))) = HierarchyStarredStage HW j ∧ HierarchyStoredColorsAt K
        (⟨(↑j : ℕ),
    by omega
    ⟩ : Fin (K.dividerCount + (1 : ℕ))) = HierarchyStoredColorsAt HW j)) (_ : (⟨HW.dividerCount,
    by omega
    ⟩ : Fin (K.dividerCount + (1 : ℕ))) = Fin.last K.dividerCount), HierarchyStarredStage K
        (Fin.last K.dividerCount) = U := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base U corrU baseU H good W corrW baseW HW hcountW
      hstarW V' corrV baseV K hcount hcarry hlastIndex
  have hh := (hcarry (Fin.last HW.dividerCount)).2.1
  change HierarchyStarredStage K ⟨HW.dividerCount, by omega⟩ =
    HierarchyStarredStage HW (Fin.last HW.dividerCount) at hh
  rw [hlastIndex] at hh
  exact hh.trans hstarW

private theorem helper_hnewStoredV_366.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (_ : HierarchyBase ett phi) (U : TreeSequence G e0) (corrU :
        CorrespondingExtendedTashkinovTree G k e0 ett phi U) (baseU : HierarchyBase
        corrU.replacementETT phi) (H : TashkinovHierarchy corrU.replacementETT baseU) (_ :
        GoodHierarchy H) (W : TreeSequence G e0) (corrW : CorrespondingExtendedTashkinovTree G k
        e0 ett phi W) (baseW : HierarchyBase corrW.replacementETT phi) (HW : TashkinovHierarchy
        corrW.replacementETT baseW) (hcountW : HW.dividerCount = H.dividerCount + (1 : ℕ)) (_ :
        HierarchyStoredColorsAt HW (Fin.last HW.dividerCount) = HierarchyTerminalStoredColors H)
        (V' : TreeSequence G e0) (corrV : CorrespondingExtendedTashkinovTree G k e0 ett phi V')
        (baseV : HierarchyBase corrV.replacementETT phi) (K : TashkinovHierarchy
        corrV.replacementETT baseV) (hcount : K.dividerCount = HW.dividerCount) (_ : (
    ∀ (j : Fin (HW.dividerCount + (1 : ℕ))), K.stage (⟨(↑j : ℕ),
    by omega
    ⟩ : Fin (K.dividerCount + (2 : ℕ))) = HW.stage j.castSucc ∧ HierarchyStarredStage K (⟨(↑j :
        ℕ),
    by omega
    ⟩ : Fin (K.dividerCount + (1 : ℕ))) = HierarchyStarredStage HW j ∧ HierarchyStoredColorsAt K
        (⟨(↑j : ℕ),
    by omega
    ⟩ : Fin (K.dividerCount + (1 : ℕ))) = HierarchyStoredColorsAt HW j)) (_ : (⟨HW.dividerCount,
    by omega
    ⟩ : Fin (K.dividerCount + (1 : ℕ))) = Fin.last K.dividerCount), HierarchyStoredColorsAt K
        (Fin.last K.dividerCount) = HierarchyTerminalStoredColors H := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base U corrU baseU H good W corrW baseW HW hcountW
      hnewStoredW V' corrV baseV K hcount hcarry hlastIndex
  have hh := (hcarry (Fin.last HW.dividerCount)).2.2
  change HierarchyStoredColorsAt K ⟨HW.dividerCount, by omega⟩ =
    HierarchyStoredColorsAt HW (Fin.last HW.dividerCount) at hh
  rw [hlastIndex] at hh
  exact hh.trans hnewStoredW

private theorem helper_branch_397.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (_ : HierarchyBase ett phi) (U : TreeSequence G e0) (corrU :
        CorrespondingExtendedTashkinovTree G k e0 ett phi U) (baseU : HierarchyBase
        corrU.replacementETT phi) (H : TashkinovHierarchy corrU.replacementETT baseU) (_ :
        GoodHierarchy H) (W : TreeSequence G e0) (corrW : CorrespondingExtendedTashkinovTree G k
        e0 ett phi W) (baseW : HierarchyBase corrW.replacementETT phi) (HW : TashkinovHierarchy
        corrW.replacementETT baseW) (hcountW : HW.dividerCount = H.dividerCount + (1 : ℕ)) (_ : (
    ∀ (j : Fin (H.dividerCount + (2 : ℕ))), HW.stage (Fin.castLE (
    by omega
    ) j) = H.stage j)) (V' : TreeSequence G e0) (corrV : CorrespondingExtendedTashkinovTree G k e0
        ett phi V') (baseV : HierarchyBase corrV.replacementETT phi) (K : TashkinovHierarchy
        corrV.replacementETT baseV) (hcount : K.dividerCount = HW.dividerCount) (_ :
        K.dividerCount = H.dividerCount + (1 : ℕ)) (_ : (
    ∀ (j : Fin (HW.dividerCount + (1 : ℕ))), K.stage (⟨(↑j : ℕ),
    by omega
    ⟩ : Fin (K.dividerCount + (2 : ℕ))) = HW.stage j.castSucc ∧ HierarchyStarredStage K (⟨(↑j :
        ℕ),
    by omega
    ⟩ : Fin (K.dividerCount + (1 : ℕ))) = HierarchyStarredStage HW j ∧ HierarchyStoredColorsAt K
        (⟨(↑j : ℕ),
    by omega
    ⟩ : Fin (K.dividerCount + (1 : ℕ))) = HierarchyStoredColorsAt HW j)) (j : Fin (H.dividerCount
        + (2 : ℕ))), K.stage (Fin.castLE (
    by omega
    ) j) = H.stage j := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base U corrU baseU H good W corrW baseW HW hcountW
      hstagesW V' corrV baseV K hcount hcountV hcarry j
  have hh := (hcarry (⟨j.val, by omega⟩ : Fin (HW.dividerCount + 1))).1
  calc
    K.stage (Fin.castLE (by omega) j) =
        HW.stage (Fin.castLE (by omega) j) := by
      convert hh using 1 <;> congr 1
    _ = H.stage j := hstagesW j

private theorem helper_branch_404.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (_ : HierarchyBase ett phi) (U : TreeSequence G e0) (corrU :
        CorrespondingExtendedTashkinovTree G k e0 ett phi U) (baseU : HierarchyBase
        corrU.replacementETT phi) (H : TashkinovHierarchy corrU.replacementETT baseU) (_ :
        GoodHierarchy H) (W : TreeSequence G e0) (corrW : CorrespondingExtendedTashkinovTree G k
        e0 ett phi W) (baseW : HierarchyBase corrW.replacementETT phi) (HW : TashkinovHierarchy
        corrW.replacementETT baseW) (hcountW : HW.dividerCount = H.dividerCount + (1 : ℕ)) (_ : (
    ∀ (i : Fin H.dividerCount), (↑(HW.dividerPosition (Fin.castLE (
    by omega
    ) i)) : ℕ) = (↑(H.dividerPosition i) : ℕ))) (V' : TreeSequence G e0) (corrV :
        CorrespondingExtendedTashkinovTree G k e0 ett phi V') (baseV : HierarchyBase
        corrV.replacementETT phi) (K : TashkinovHierarchy corrV.replacementETT baseV) (hcount :
        K.dividerCount = HW.dividerCount) (_ : (
    ∀ (i : Fin K.dividerCount), (↑(K.dividerPosition i) : ℕ) = (↑(HW.dividerPosition (Fin.cast
        hcount i)) : ℕ))) (_ : K.dividerCount = H.dividerCount + (1 : ℕ)) (i : Fin
        H.dividerCount), (↑(K.dividerPosition (Fin.castLE (
    by omega
    ) i)) : ℕ) = (↑(H.dividerPosition i) : ℕ) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base U corrU baseU H good W corrW baseW HW hcountW
      hdividersW V' corrV baseV K hcount hdividersV hcountV i
  have hh := hdividersV (Fin.castLE (by omega) i)
  have hi : Fin.cast hcount (Fin.castLE (by omega) i) =
      Fin.castLE (by omega) i := Fin.ext rfl
  rw [hi] at hh
  exact hh.trans (hdividersW i)

private theorem helper_branch_410.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (U : TreeSequence G e0) (corrU : CorrespondingExtendedTashkinovTree G k e0
        ett phi U) (baseU : HierarchyBase corrU.replacementETT phi) (H : TashkinovHierarchy
        corrU.replacementETT baseU) (W : TreeSequence G e0) (corrW :
        CorrespondingExtendedTashkinovTree G k e0 ett phi W) (baseW : HierarchyBase
        corrW.replacementETT phi) (HW : TashkinovHierarchy corrW.replacementETT baseW) (hcountW :
        HW.dividerCount = H.dividerCount + (1 : ℕ)) (_ : (↑(HW.dividerPosition (Fin.cast (
    by omega
    ) (Fin.last H.dividerCount))) : ℕ) = U.length) (V' : TreeSequence G e0) (corrV :
        CorrespondingExtendedTashkinovTree G k e0 ett phi V') (baseV : HierarchyBase
        corrV.replacementETT phi) (K : TashkinovHierarchy corrV.replacementETT baseV) (hcount :
        K.dividerCount = HW.dividerCount) (_ : (
    ∀ (i : Fin K.dividerCount), (↑(K.dividerPosition i) : ℕ) = (↑(HW.dividerPosition (Fin.cast
        hcount i)) : ℕ))) (_ : K.dividerCount = H.dividerCount + (1 : ℕ)), (↑(K.dividerPosition
        (Fin.cast (
    by omega
    ) (Fin.last H.dividerCount))) : ℕ) = U.length := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett U corrU baseU H W corrW baseW HW hcountW hnewDividerW
      V' corrV baseV K hcount hdividersV hcountV
  have hh := hdividersV (Fin.cast hcountV.symm (Fin.last H.dividerCount))
  have hi : Fin.cast hcount (Fin.cast hcountV.symm (Fin.last H.dividerCount)) =
      Fin.cast hcountW.symm (Fin.last H.dividerCount) := Fin.ext rfl
  rw [hi] at hh
  exact hh.trans hnewDividerW

theorem AlgorithmFiveSixFixedRootRefresh
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (ctx : TechnicalInductionContext G k e0 ett.rounds)
    (hMP : MaximumProperty ett)
    (base : HierarchyBase ett phi)
    (hdegree : MaximumDegree G + 1 <= k)
    (hlargeOrder : 11 <= TashkinovOrder G)
    (hmissingBound : forall {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      (current : ExtendedTashkinovTree G k e0 input' T' generating'),
      current.rounds = ett.rounds -> MaximumProperty current ->
      forall (base' : HierarchyBase current generating')
        (K : TashkinovHierarchy current base'),
        GoodHierarchy K ->
        2 * current.rounds + 11 ≤
      (TreeMissingColors generating'
          (current.series.data.tree
            ((Fin.last current.rounds : Fin (current.rounds + 1))).castSucc)).card)
    (U : TreeSequence G e0)
    (corrU : CorrespondingExtendedTashkinovTree G k e0 ett phi U)
    (hMPU : MaximumProperty corrU.replacementETT)
    (baseU : HierarchyBase corrU.replacementETT phi)
    (hbaseCore : baseU.core = base.core)
    (hbaseClosure : baseU.closure = base.closure)
    (_ : baseU.supportPosition.val = base.supportPosition.val)
    (H : TashkinovHierarchy corrU.replacementETT baseU)
    (good : GoodHierarchy H)
    (hminus : TreeColorSetMinusClosed G phi U
      ((HierarchyTerminalStoredColors H).biUnion
        (good.gamma (Fin.last H.dividerCount))))
    (hnotClosed : ¬ TreeColorSetClosed G phi U (TreeMissingColors phi U))
    (J : TreeSequence G e0)
    (hanchor :
      (ett.series.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.PE /\ J = base.core /\
        TashkinovAugmentationSequence phi
          (ett.series.data.tree (Fin.last ett.rounds).castSucc) J) \/
      ((ett.series.data.kind (Fin.last ett.rounds) =
            some TashkinovExtensionKind.SE \/
          ett.series.data.kind (Fin.last ett.rounds) =
            some TashkinovExtensionKind.RE) /\
        exists f0 : E,
          ett.series.data.connectingEdges (Fin.last ett.rounds) = {f0} /\
          TreeSequenceAdjoinEdge
            (ett.series.data.tree (Fin.last ett.rounds).castSucc) f0 J))
    (hanchorStrict :
      (ett.series.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.PE -> base.core.length < U.length) /\
      (ett.series.data.kind (Fin.last ett.rounds) !=
          some TashkinovExtensionKind.PE ->
        (ett.series.data.tree
          (Fin.last ett.rounds).castSucc).length < U.length))
    (hroute : TashkinovAugmentationSequence phi J U) :
    exists (alpha beta eta gammaOne gammaTwo : Fin k) (f : E) (W : TreeSequence G e0),
    ColoredVertexSetElementary G phi
        (TreeSequenceVertexSet
          (HierarchyStarredStage H (Fin.last H.dividerCount : Fin (H.dividerCount + 1)) :
            TreeSequence G e0)) ∧
    ColoredVertexSetElementary G phi (TreeSequenceVertexSet U) ∧
    ((HierarchyStarredStage H (Fin.last H.dividerCount : Fin (H.dividerCount + 1)) :
            TreeSequence G e0)).length <
        U.length ∧
    Odd
        (TreeSequenceVertexSet
            (HierarchyStarredStage H (Fin.last H.dividerCount : Fin (H.dividerCount + 1)) :
              TreeSequence G e0)).card ∧
    Odd (TreeSequenceVertexSet U).card ∧
    alpha ∈
        TreeMissingColors phi U \
          ((HierarchyTerminalStoredColors H).biUnion
              (good.gamma (Fin.last H.dividerCount : Fin (H.dividerCount + 1))) :
            Finset (Fin k)) ∧
    TreeColorSetClosed G phi U { alpha } ∧
    beta ∈ TreeMissingColors phi U ∧
    beta ∈
        ((HierarchyTerminalStoredColors H).biUnion
            (good.gamma (Fin.last H.dividerCount : Fin (H.dividerCount + 1))) :
          Finset (Fin k)) ∧
    eta ∈ HierarchyTerminalStoredColors H ∧
    beta ∈ good.gamma (Fin.last H.dividerCount : Fin (H.dividerCount + 1)) eta ∧
    (∀ theta : Fin k,
        theta ∈ HierarchyTerminalStoredColors H →
          beta ∈ good.gamma (Fin.last H.dividerCount : Fin (H.dividerCount + 1)) theta →
            theta = eta) ∧
    f ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet U) beta ∧
    phi f = some beta ∧
    TreeSequenceAdjoinEdge U f W ∧
    TashkinovAugmentation phi U W ∧
    gammaOne != gammaTwo ∧
    gammaOne ∈
        (TreeSequenceVertexSet U \
              TreeSequenceVertexSet
                (HierarchyStarredStage H
                    (Fin.last H.dividerCount : Fin (H.dividerCount + 1)) :
                  TreeSequence G e0)).biUnion
          (MissingColors G phi) ∧
    gammaTwo ∈
        (TreeSequenceVertexSet U \
              TreeSequenceVertexSet
                (HierarchyStarredStage H
                    (Fin.last H.dividerCount : Fin (H.dividerCount + 1)) :
                  TreeSequence G e0)).biUnion
          (MissingColors G phi) ∧
    Disjoint { gammaOne, gammaTwo }
        ((HierarchyTerminalStoredColors H).biUnion
            (good.gamma (Fin.last H.dividerCount : Fin (H.dividerCount + 1))) :
          Finset (Fin k)) ∧
    beta ∉ ({ gammaOne, gammaTwo } : Finset (Fin k)) ∧
    exists (corrW : CorrespondingExtendedTashkinovTree G k e0 ett phi W),
    MaximumProperty corrW.replacementETT ∧
    TashkinovAugmentationSequence phi J W ∧
    exists baseW : HierarchyBase corrW.replacementETT phi,
    baseW.core = base.core ∧
    baseW.closure = base.closure ∧
    baseW.supportPosition.val = base.supportPosition.val ∧
    exists HW : TashkinovHierarchy corrW.replacementETT baseW,
    exists hcountW : HW.dividerCount = H.dividerCount + 1,
    (∀ j : Fin (H.dividerCount + 2), HW.stage (Fin.castLE (by omega) j) = H.stage j) ∧
    HW.stage (Fin.last HW.dividerCount).castSucc = U ∧
    HierarchyStarredStage HW (Fin.last HW.dividerCount) = U ∧
    HW.stage (Fin.last HW.dividerCount).succ = W ∧
    (∀ i : Fin H.dividerCount,
        (HW.dividerPosition (Fin.castLE (by omega) i)).val = (H.dividerPosition i).val) ∧
    (HW.dividerPosition (Fin.cast hcountW.symm (Fin.last H.dividerCount))).val = U.length ∧
    (∀ j : Fin (H.dividerCount + 1),
        HierarchyStoredColorsAt HW (Fin.castLE (by omega) j) =
          HierarchyStoredColorsAt H j) ∧
    HierarchyStoredColorsAt HW (Fin.last HW.dividerCount) =
        HierarchyTerminalStoredColors H ∧
    exists goodW : GoodHierarchy HW,
    (∀ j : Fin (H.dividerCount + 1),
        ∀ theta : Fin k, goodW.gamma (Fin.castLE (by omega) j) theta = good.gamma j theta) ∧
    goodW.gamma (Fin.last HW.dividerCount) eta = { gammaOne, gammaTwo } ∧
    (∀ theta : Fin k,
        theta ∈ HierarchyTerminalStoredColors H →
          theta != eta →
            goodW.gamma (Fin.last HW.dividerCount) theta =
              good.gamma (Fin.last H.dividerCount : Fin (H.dividerCount + 1)) theta) ∧
    exists (V' : TreeSequence G e0) (corrV :
      CorrespondingExtendedTashkinovTree G k e0 ett phi V'),
    MaximumProperty corrV.replacementETT ∧
    U.length < V'.length ∧
    TashkinovAugmentationSequence phi J V' ∧
    exists baseV : HierarchyBase corrV.replacementETT phi,
    baseV.core = base.core ∧
    baseV.closure = base.closure ∧
    baseV.supportPosition.val = base.supportPosition.val ∧
    exists K : TashkinovHierarchy corrV.replacementETT baseV,
    exists hcountV : K.dividerCount = H.dividerCount + 1,
    (∀ j : Fin (H.dividerCount + 2), K.stage (Fin.castLE (by omega) j) = H.stage j) ∧
    K.stage (Fin.last K.dividerCount).castSucc = U ∧
    HierarchyStarredStage K (Fin.last K.dividerCount) = U ∧
    K.stage (Fin.last K.dividerCount).succ = V' ∧
    (∀ i : Fin H.dividerCount,
        (K.dividerPosition (Fin.castLE (by omega) i)).val = (H.dividerPosition i).val) ∧
    (K.dividerPosition (Fin.cast hcountV.symm (Fin.last H.dividerCount))).val = U.length ∧
    (∀ j : Fin (H.dividerCount + 1),
        HierarchyStoredColorsAt K (Fin.castLE (by omega) j) = HierarchyStoredColorsAt H j) ∧
    HierarchyStoredColorsAt K (Fin.last K.dividerCount) = HierarchyTerminalStoredColors H ∧
    exists goodV : GoodHierarchy K,
    (∀ j : Fin (H.dividerCount + 1),
        ∀ theta : Fin k, goodV.gamma (Fin.castLE (by omega) j) theta = good.gamma j theta) ∧
    goodV.gamma (Fin.last K.dividerCount) eta = { gammaOne, gammaTwo } ∧
    (∀ theta : Fin k,
        theta ∈ HierarchyTerminalStoredColors H →
          theta != eta →
            goodV.gamma (Fin.last K.dividerCount) theta =
              good.gamma (Fin.last H.dividerCount : Fin (H.dividerCount + 1)) theta) ∧
    TreeColorSetMinusClosed G phi V'
      ((HierarchyTerminalStoredColors K).biUnion (goodV.gamma (Fin.last K.dividerCount))) := by
  classical
  let lastH : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
  let A := HierarchyStarredStage H lastH
  let Dplus := HierarchyTerminalStoredColors H
  have hstrict :
      (ett.series.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.PE -> base.core.length < U.length) ∧
      (ett.series.data.kind (Fin.last ett.rounds) ≠
          some TashkinovExtensionKind.PE ->
        (ett.series.data.tree (Fin.last ett.rounds).castSucc).length < U.length) := by
    simpa only [bne_iff_ne] using hanchorStrict
  obtain ⟨hproper, hone, helemA, helemU, hAU, hAUstrict, hoddA, hgap⟩ :=
    P2940_T1_StarredPrefixPreparation G k e0 input T phi ett ctx hMP base
      hdegree hlargeOrder hmissingBound U corrU hMPU baseU hbaseCore H good hstrict
  have hDsub : Dplus ⊆ HierarchyStoredColorsAt H lastH :=
    (HierarchyTerminalStoredColorsSubsetLast H).1
  have hreserved : forall eta, eta ∈ Dplus ->
      good.gamma lastH eta ⊆ TreeMissingColors phi A := by
    intro eta heta
    exact (GoodHierarchyReservedDisjoint good lastH).1 eta (hDsub heta)
  obtain ⟨alpha, beta, eta, gammaOne, gammaTwo, f, W, hoddU, halpha,
      halphaClosed, hbeta, hbetaReserved, heta, hbetaEta, howner, hf,
      hfc, hadjoin, haug, hne, hg1, hg2, hfresh, hbetaPair⟩ :=
    P2940_T1_NestedOddMissingPair G k e0 phi A U hproper helemU hAU hAUstrict
      hoddA hdegree Dplus (good.gamma lastH) hreserved
      (fun a b ha hb hab => good.disjointPairs lastH a b
        (hDsub ha) (hDsub hb) hab) hgap hminus hnotClosed
  have hstable : StableColoring
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
      (ett.series.data.coloring (Fin.last ett.rounds)) phi := by
    rw [← ett.generatingColoring]
    exact (sc2 G e0 _ _).refl ⟨phi, hproper, hone⟩
  have hmod : ModColoring ett phi :=
    ctx.currentSix ett rfl hMP phi hproper hone hstable
  have hUW : TashkinovAugmentationSequence phi U W :=
    Relation.ReflTransGen.single haug
  have hJW : TashkinovAugmentationSequence phi J W := hroute.trans hUW
  let Tn := ett.series.data.tree (Fin.last ett.rounds).castSucc
  have hTnJ : TreeSequenceInitialSegment Tn J := by
    rcases hanchor with hPE | hnonPE
    · exact TashkinovAugmentationSequenceInitialSegment phi Tn J hPE.2.2
    · obtain ⟨_, f0, _, hadjoinJ⟩ := hnonPE
      exact hadjoinJ.2.1
  have hJWsegment := TashkinovAugmentationSequenceInitialSegment phi J W hJW
  have hTnW :=
    @helper_hTnW_292 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0) (@input)
        (@T) (@phi) (@ett) (@J) (@W) (@hTnJ) (@hJWsegment)
  have hTnStrictW : Tn.length < W.length := by
    have hTnLeJ := hTnJ.1
    have hJLeU := (TashkinovAugmentationSequenceInitialSegment phi J U hroute).1
    have hlengthW := hadjoin.1
    omega
  have heligibleW :
      (ett.series.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.PE ∧ TashkinovAugmentationSequence phi Tn W) ∨
      ((ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.SE ∨
          ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.RE) ∧
        exists (f0 : E) (seed : TreeSequence G e0),
          ett.series.data.connectingEdges (Fin.last ett.rounds) = {f0} ∧
          TreeSequenceAdjoinEdge Tn f0 seed ∧ TashkinovAugmentationSequence phi seed W) := by
    rcases hanchor with hPE | hnonPE
    · exact Or.inl ⟨hPE.1, hPE.2.2.trans hJW⟩
    · obtain ⟨hkind, f0, hedges, hadjoinJ⟩ := hnonPE
      exact Or.inr ⟨hkind, f0, J, hedges, hadjoinJ, hJW⟩
  obtain ⟨corrW⟩ := hmod.2.2 W hTnW hTnStrictW heligibleW
  have hMPW := MaximumPropertyTransport G k e0 ett phi hmod W corrW hMP
  obtain ⟨baseW, hcoreW, hclosureW, hsupportW⟩ :=
    HierarchyBaseCorrespondingTransport G k e0 input T W phi ett corrW base
  obtain ⟨HW, hcountW, hstagesW, hprecedingW, hstarW, hterminalW,
      hdividersW, hnewDividerW, hstoredW, hnewStoredW, goodW,
      hgammaW, hrefreshW, hcopiedW⟩ :=
    P2940_T1_OneDividerRefresh G k e0 input T phi ett U W corrU corrW baseU baseW
      (hcoreW.trans hbaseCore.symm) (hclosureW.trans hbaseClosure.symm) H good
      helemU eta beta gammaOne gammaTwo f heta hbetaEta hfc hadjoin hne hg1 hg2
      hfresh hminus
  obtain ⟨m, chain, V', hfirst, hlast, hsteps, hlengths, hsegments,
      hvertices, hWV, havoid, hmaximal, corrV, hMPV, baseV, hcoreV,
      hclosureV, hsupportV, K, hcount, hstagesV, hdividersV, goodV,
      hgammaV, hterminalStoredV, hminusV⟩ :=
    GoodHierarchyRestrictedAugmentation G k e0 input T phi phi ett hmod hMP
      W corrW baseW HW goodW
  have hcountV : K.dividerCount = H.dividerCount + 1 := hcount.trans hcountW
  have hcarry := @helper_hcarry_334 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@U) (@corrU) (@baseU) (@H)
      (@good) (@W) (@corrW) (@baseW) (@HW) (@hcountW) (@V') (@corrV) (@baseV) (@K) (@hcount)
      (@hstagesV)
  have hcarryGamma (j : Fin (HW.dividerCount + 1)) (theta : Fin k) :
      goodV.gamma ⟨j.val, by omega⟩ theta = goodW.gamma j theta := by
    have hh := hgammaV (⟨j.val, by omega⟩ : Fin (K.dividerCount + 1)) theta
    have hi : Fin.cast (congrArg (fun n : Nat => n + 1) hcount)
        (⟨j.val, by omega⟩ : Fin (K.dividerCount + 1)) = j := Fin.ext rfl
    rwa [hi] at hh
  have hlastIndex : (⟨HW.dividerCount, by omega⟩ : Fin (K.dividerCount + 1)) =
      Fin.last K.dividerCount := Fin.ext (by simpa using hcount.symm)
  have hlastStageIndex : (⟨HW.dividerCount, by omega⟩ : Fin (K.dividerCount + 2)) =
      (Fin.last K.dividerCount).castSucc := Fin.ext (by simpa using hcount.symm)
  have hprecedingV :=
    @helper_hprecedingV_354 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@U) (@corrU) (@baseU) (@H) (@good)
        (@W) (@corrW) (@baseW) (@HW) (@hcountW) (@hprecedingW) (@V') (@corrV) (@baseV) (@K)
        (@hcount) (@hcarry) (@hlastStageIndex)
  have hstarV :=
    @helper_hstarV_360 (@V) (@E) inferInstance inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@U) (@corrU) (@baseU) (@H) (@good) (@W)
        (@corrW) (@baseW) (@HW) (@hcountW) (@hstarW) (@V') (@corrV) (@baseV) (@K) (@hcount)
        (@hcarry) (@hlastIndex)
  have hnewStoredV :=
    @helper_hnewStoredV_366 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@U) (@corrU) (@baseU) (@H) (@good)
        (@W) (@corrW) (@baseW) (@HW) (@hcountW) (@hnewStoredW) (@V') (@corrV) (@baseV) (@K)
        (@hcount) (@hcarry) (@hlastIndex)
  have hlastGamma (theta : Fin k) : goodV.gamma (Fin.last K.dividerCount) theta =
      goodW.gamma (Fin.last HW.dividerCount) theta := by
    have hh := hcarryGamma (Fin.last HW.dividerCount) theta
    change goodV.gamma ⟨HW.dividerCount, by omega⟩ theta =
      goodW.gamma (Fin.last HW.dividerCount) theta at hh
    rwa [hlastIndex] at hh
  have hstrictV : U.length < V'.length := by
    have hlen := hadjoin.1
    have hinit := TashkinovAugmentationSequenceInitialSegment phi W V' hWV
    have hle := hinit.1
    omega
  refine ⟨alpha, beta, eta, gammaOne, gammaTwo, f, W, helemA, helemU,
    hAUstrict, hoddA, hoddU, halpha, halphaClosed, hbeta, hbetaReserved,
    heta, hbetaEta, howner, hf, hfc, hadjoin, haug, ?_, hg1, hg2, hfresh,
    hbetaPair, corrW, hMPW, hJW, baseW, hcoreW, hclosureW, hsupportW,
    HW, hcountW, hstagesW, hprecedingW, hstarW, hterminalW, hdividersW,
    hnewDividerW, hstoredW, hnewStoredW, goodW, hgammaW, hrefreshW, ?_,
    V', corrV, hMPV, hstrictV, hJW.trans hWV, baseV, hcoreV.trans hcoreW,
    hclosureV.trans hclosureW, hsupportV.trans hsupportW, K, hcountV,
    ?_, hprecedingV, hstarV, K.terminalStage, ?_, ?_, ?_, hnewStoredV,
    goodV, ?_, (hlastGamma eta).trans hrefreshW, ?_, hminusV⟩
  · simpa only [bne_iff_ne] using hne
  · intro theta htheta hthetaNe
    exact hcopiedW theta htheta (by simpa only [bne_iff_ne] using hthetaNe)
  · exact @helper_branch_397 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@U) (@corrU) (@baseU) (@H) (@good)
      (@W) (@corrW) (@baseW) (@HW) (@hcountW) (@hstagesW) (@V') (@corrV) (@baseV) (@K) (@hcount)
      (@hcountV) (@hcarry)
  · exact @helper_branch_404 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@U) (@corrU) (@baseU) (@H) (@good)
      (@W) (@corrW) (@baseW) (@HW) (@hcountW) (@hdividersW) (@V') (@corrV) (@baseV) (@K)
      (@hcount) (@hdividersV) (@hcountV)
  · exact @helper_branch_410 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@U) (@corrU) (@baseU) (@H) (@W) (@corrW)
      (@baseW) (@HW) (@hcountW) (@hnewDividerW) (@V') (@corrV) (@baseV) (@K) (@hcount)
      (@hdividersV) (@hcountV)
  · intro j
    have hh := (hcarry (Fin.castLE (by omega) j)).2.2
    exact hh.trans (hstoredW j)
  · intro j theta
    exact (hcarryGamma (Fin.castLE (by omega) j) theta).trans (hgammaW j theta)
  · intro theta htheta hthetaNe
    exact (hlastGamma theta).trans
      (hcopiedW theta htheta (by simpa only [bne_iff_ne] using hthetaNe))

end GoldbergSeymour

end
