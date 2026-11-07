/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyTreeFacts

public import LeanPool.GoldbergSeymour.HierarchyFirstMissingPositionPrefixCutoff

public import LeanPool.GoldbergSeymour.TerminalHierarchyPrefixConstruction
public import LeanPool.GoldbergSeymour.GoodHierarchy
public import LeanPool.GoldbergSeymour.MaximumProperty
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentFacts

/-!
# Good Hierarchy Terminal Prefix Repackage

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open TerminalHierarchyPrefixPreparation

private theorem helper_continuation_904.{u_1, u_2} :
    helperContinuation904Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T generating phi ett base H good B hAB hBT segmentRefl
      segmentTrans stageSegment lastStage lastZero lastPositive lastToB firstToB strictFirst ettB
      mpB baseB hbStage hbStageOld hbStageAt hbNested hbStrict HB stageOrdNext starredEq storedEq
      beforeFirstMissing missingEq
  have segmentSubset (j : Fin (H.dividerCount + 1)) (eta : Fin k) :
      HierarchySegmentColors HB j eta ⊆ HierarchySegmentColors H j eta := by
    intro c hc
    unfold HierarchySegmentColors at hc ⊢
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    rcases hc with ⟨x, hafter, hbefore, hcolor⟩
    have hnext : TreeSequenceInitialSegment
        (HB.stage j.succ) (H.stage j.succ) := by
      by_cases hj : j.val = H.dividerCount
      · have hlast : j = Fin.last H.dividerCount := by
          apply Fin.ext
          simpa using hj
        rw [hlast]
        have hjs : (Fin.last H.dividerCount).succ =
            Fin.last (H.dividerCount + 1) := by rfl
        rw [hjs, HB.terminalStage, H.terminalStage]
        exact hBT
      · have hjlt : j.val < H.dividerCount := by omega
        change TreeSequenceInitialSegment (hbStage j.succ) (H.stage j.succ)
        rw [hbStageAt j.succ (Nat.succ_le_of_lt hjlt)]
        exact segmentRefl _
    have hstageB : TreeSequenceInitialSegment (HB.stage j.succ) B := by
      by_cases hj : j.val = H.dividerCount
      · have hlast : j = Fin.last H.dividerCount := by
          apply Fin.ext
          simpa using hj
        rw [hlast]
        have hjs : (Fin.last H.dividerCount).succ =
            Fin.last (H.dividerCount + 1) := by rfl
        rw [hjs, HB.terminalStage]
        exact segmentRefl _
      · have hjlt : j.val < H.dividerCount := by omega
        change TreeSequenceInitialSegment (hbStage j.succ) B
        rw [hbStageAt j.succ (Nat.succ_le_of_lt hjlt)]
        have hs := stageSegment (j.val + 1)
          (H.dividerCount - (j.val + 1)) (by omega)
        rw [show (⟨j.val + 1 + (H.dividerCount - (j.val + 1)), by omega⟩ :
          Fin (H.dividerCount + 2)) = ⟨H.dividerCount, by omega⟩ by
            apply Fin.ext
            simpa using Nat.add_sub_of_le (Nat.succ_le_of_lt hjlt)] at hs
        have hs' : TreeSequenceInitialSegment
            (H.stage ⟨j.val + 1, by omega⟩)
            (H.stage ⟨H.dividerCount, by omega⟩) := by
          exact hs
        have hab : TreeSequenceInitialSegment
            (H.stage ⟨H.dividerCount, by omega⟩) B := by
          rw [← lastPositive (by omega)]
          exact hAB
        exact segmentTrans hs' hab
    let xold : Fin (H.stage j.succ).length :=
      Fin.castLE hnext.1 x
    let xB : Fin (B.length + 1) := Fin.castLE
      (Nat.succ_le_succ hstageB.1) ⟨x.val, by omega⟩
    refine ⟨xold, ?_, ?_, ?_⟩
    · rw [← starredEq j]
      simpa [xold] using hafter
    · apply lt_min
      · have hm := beforeFirstMissing hBT eta xB (by dsimp [xB]; omega)
          (by simpa [xB] using (lt_min_iff.mp hbefore).1)
        simpa [xold, xB] using hm
      · exact lt_of_lt_of_le (lt_min_iff.mp hbefore).2 hnext.1
    · change phi ((H.stage j.succ).edge (Fin.castLE hnext.1 x)) = some c
      rw [hnext.2.2 x]
      exact hcolor
  let goodB : GoodHierarchy HB := by
    exact {
      gamma := good.gamma
      twoColors := by
        intro j eta hmem
        apply good.twoColors j eta
        rw [← storedEq j]
        exact hmem
      avoidance := by
        intro j eta hmem c hc
        have ho := good.avoidance j eta (by rw [← storedEq j]; exact hmem) hc
        exact Finset.mem_sdiff.mpr ⟨by rw [missingEq j]; exact (Finset.mem_sdiff.mp ho).1,
          fun hn => (Finset.mem_sdiff.mp ho).2 (segmentSubset j eta hn)⟩
      disjointPairs := by
        intro j eta theta h₁ h₂ hne
        apply good.disjointPairs j eta theta
        · rw [← storedEq j]; exact h₁
        · rw [← storedEq j]; exact h₂
        · exact hne
      uniqueRefresh := by
        intro i
        rw [stageOrdNext i]
        simpa [storedEq, starredEq] using good.uniqueRefresh i
      parallelBase := by
        simpa [ettB, baseB, HierarchyStoredColorsAt, HierarchyStarredStage] using good.parallelBase
      minusClosed := by
        intro i
        rw [stageOrdNext i]
        simpa [storedEq] using good.minusClosed i }
  refine ⟨ettB, mpB, rfl, HEq.rfl, baseB, rfl, rfl, rfl, HB, rfl, ?_, ?_, goodB, ?_⟩
  · intro j
    exact ⟨by simpa using hbStageOld j, starredEq j⟩
  · intro i
    rfl
  · intro j
    exact ⟨storedEq j, missingEq j, fun eta => ⟨rfl, segmentSubset j eta⟩⟩

theorem GoodHierarchyTerminalPrefixRepackage {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hMP : MaximumProperty ett)
    (base : HierarchyBase ett phi)
    (H : TashkinovHierarchy ett base)
    (good : GoodHierarchy H)
    (B : TreeSequence G e0)
    (hAB : TreeSequenceInitialSegment
      (HierarchyStarredStage H (Fin.last H.dividerCount)) B)
    (hABstrict :
      (HierarchyStarredStage H (Fin.last H.dividerCount)).length < B.length)
    (hBT : TreeSequenceInitialSegment B T) :
    ∃ ettB : ExtendedTashkinovTree G k e0 input B generating,
    MaximumProperty ettB ∧
    ettB.rounds = ett.rounds ∧
    HEq ettB.series ett.series ∧
    ∃ baseB : HierarchyBase ettB phi,
    baseB.core = base.core ∧
    baseB.closure = base.closure ∧
    baseB.supportPosition.val = base.supportPosition.val ∧
    ∃ HB : TashkinovHierarchy ettB baseB,
    ∃ hcount : HB.dividerCount = H.dividerCount,
    (∀ j : Fin (HB.dividerCount + 1),
      HB.stage j.castSucc =
          H.stage
            ((Fin.cast (congrArg (fun n : ℕ => n + 1) hcount) j :
                Fin (H.dividerCount + 1))).castSucc ∧
        HierarchyStarredStage HB j =
          HierarchyStarredStage H
            (Fin.cast (congrArg (fun n : ℕ => n + 1) hcount) j : Fin (H.dividerCount + 1))) ∧
    (∀ i : Fin HB.dividerCount,
      (HB.dividerPosition i).val = (H.dividerPosition (Fin.cast hcount i)).val) ∧
    ∃ goodB : GoodHierarchy HB,
    ∀ j : Fin (HB.dividerCount + 1),
    HierarchyStoredColorsAt HB j =
      HierarchyStoredColorsAt H
        (Fin.cast (congrArg (fun n : ℕ => n + 1) hcount) j : Fin (H.dividerCount + 1)) ∧
    HierarchyStageMissingColors HB j =
      HierarchyStageMissingColors H
        (Fin.cast (congrArg (fun n : ℕ => n + 1) hcount) j : Fin (H.dividerCount + 1)) ∧
    ∀ eta : Fin k,
    goodB.gamma j eta =
      good.gamma
        (Fin.cast (congrArg (fun n : ℕ => n + 1) hcount) j : Fin (H.dividerCount + 1)) eta ∧
    HierarchySegmentColors HB j eta ⊆
      HierarchySegmentColors H
        (Fin.cast (congrArg (fun n : ℕ => n + 1) hcount) j : Fin (H.dividerCount + 1)) eta := by
  classical
  have segmentRefl (A : TreeSequence G e0) :
      TreeSequenceInitialSegment A A :=
    ⟨le_rfl, (by intro i; rfl), (by intro i; rfl)⟩
  have segmentTrans {A B C : TreeSequence G e0}
      (hAB : TreeSequenceInitialSegment A B)
      (hBC : TreeSequenceInitialSegment B C) :
      TreeSequenceInitialSegment A C := by
    apply TreeSequenceInitialSegment.trans <;> assumption
  have stageSegment :=
    @helper_stageSegment_94 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@generating) (@phi) (@ett) (@base) (@H) (@B)
        (@segmentRefl) (@segmentTrans)
  let lastStage : TreeSequence G e0 :=
    HierarchyStarredStage H (Fin.last H.dividerCount)
  have lastZero : H.dividerCount = 0 →
      lastStage = base.core := by
    intro h
    simp [lastStage, HierarchyStarredStage, h, Fin.last]
  have lastPositive :=
    @helper_lastPositive_115 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@generating) (@phi) (@ett) (@base) (@H) (@B)
  have stageLastPositive :=
    @helper_stageLastPositive_128 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@phi) (@ett) (@base) (@H) (@B)
        (@lastPositive)
  have stageToLast := by
    exact base.lastRoundInitialSegmentCore.trans
      (H.coreInitialSegmentOfStarredStage (Fin.last _))
  have lastToB : TreeSequenceInitialSegment lastStage B := hAB
  have firstToB := segmentTrans stageToLast lastToB
  have strictFirst :
      (ett.series.data.tree (Fin.last ett.rounds).castSucc).length < B.length := by
    have hlt : (ett.series.data.tree (Fin.last ett.rounds).castSucc).length ≤
        lastStage.length := stageToLast.1
    exact lt_of_le_of_lt hlt (by exact hABstrict)
  let ettB : ExtendedTashkinovTree G k e0 input B generating :=
    { rounds := ett.rounds
      roundsPositive := ett.roundsPositive
      series := ett.series
      abovePenultimate := firstToB
      strictAbovePenultimate := strictFirst
      belowFinal := segmentTrans hBT ett.belowFinal
      generatingColoring := ett.generatingColoring }
  have mpB : MaximumProperty ettB := by
    simpa [MaximumProperty, ettB] using hMP
  let baseB : HierarchyBase ettB phi :=
    { core := base.core
      closure := base.closure
      supportPosition := base.supportPosition
      supportPositive := base.supportPositive
      terminalMissingColors := by simpa [ettB] using base.terminalMissingColors
      parallel := by simpa [ettB] using base.parallel
      nonparallel := by simpa [ettB] using base.nonparallel }
  let hbStage : Fin (H.dividerCount + 2) → TreeSequence G e0 :=
    fun j => if j.val = H.dividerCount + 1 then B
      else H.stage ⟨j.val, by omega⟩
  have hbStageOld (j : Fin (H.dividerCount + 1)) :
      hbStage j.castSucc = H.stage j.castSucc := by
    by_cases hh : j.castSucc.val = H.dividerCount + 1
    · have hj : j.val = H.dividerCount + 1 := by simpa using hh
      omega
    · simp only [hbStage, ite_eq_right hh]
  have hbStageLast : hbStage (Fin.last (H.dividerCount + 1)) = B := by
    have he : (Fin.last (H.dividerCount + 1)).val = H.dividerCount + 1 := by simp
    simp only [hbStage, ite_eq_left he]
  have hbStageAt (j : Fin (H.dividerCount + 2)) (hj : j.val ≤ H.dividerCount) :
      hbStage j = H.stage ⟨j.val, by omega⟩ := by
    simp only [hbStage]
    split <;> rename_i hs
    · omega
    · rfl
  have hbNested :=
    @helper_hbNested_194 (@V) (@E) inferInstance inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@phi) (@ett) (@base) (@H) (@B) (@hAB)
        (@segmentTrans) (@stageLastPositive) (@stageToLast) (@hbStageOld) (@hbStageLast)
        (@hbStageAt)
  have hbStrict :=
    @helper_hbStrict_225 (@V) (@E) inferInstance inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@phi) (@ett) (@base) (@H) (@B) (@hABstrict)
        (@stageLastPositive) (@stageToLast) (@hbStageOld) (@hbStageLast) (@hbStageAt)
  let HB := @helperHB477 (@V) (@E) inferInstance inferInstance inferInstance inferInstance (@G)
      (@k) (@e0) (@input) (@T) (@generating) (@phi) (@ett) (@base) (@H) (@B) (@hAB) (@hBT)
      (@segmentTrans) (@stageSegment) (@lastZero) (@lastPositive) (@lastToB) (@firstToB)
      (@strictFirst) (@hbStageAt) (@hbNested) (@hbStrict)
  have stageOrd (i : Fin H.dividerCount) :
      HB.stage i.castSucc.succ = H.stage i.castSucc.succ := by
    change hbStage i.castSucc.succ = H.stage i.castSucc.succ
    exact hbStageAt i.castSucc.succ (Nat.succ_le_of_lt i.isLt)
  have stageOrdNext (i : Fin H.dividerCount) :
      HB.stage i.succ.castSucc = H.stage i.succ.castSucc := by
    have hindex : i.succ.castSucc = i.castSucc.succ := by
      apply Fin.ext
      rfl
    rw [hindex]
    exact stageOrd i
  have stageEq (j : Fin (H.dividerCount + 2)) :
      HB.stage j = if j.val = H.dividerCount + 1 then B
        else H.stage ⟨j.val, by omega⟩ := rfl
  have starredEq (j : Fin (H.dividerCount + 1)) :
      HierarchyStarredStage HB j = HierarchyStarredStage H j := by
    refine Fin.cases ?_ (fun i => ?_) j
    · simp [HierarchyStarredStage]
    · change HB.stage i.succ.castSucc = H.stage i.succ.castSucc
      exact stageOrd i
  have storedEq (j : Fin (H.dividerCount + 1)) :
      HierarchyStoredColorsAt HB j = HierarchyStoredColorsAt H j := by
    unfold HierarchyStoredColorsAt
    rw [starredEq]
  have beforeFirstMissing {A B : TreeSequence G e0}
      (segment : TreeSequenceInitialSegment A B) (eta : Fin k)
      (index : Fin (A.length + 1)) (beforeEnd : index.val < A.length)
      (before : index.val < (HierarchyFirstMissingPosition phi A eta).val) :
      index.val < (HierarchyFirstMissingPosition phi B eta).val := by
    exact TreeSequenceFirstMissingPositionBeforeInExtension segment beforeEnd before
  have missingEq (j : Fin (H.dividerCount + 1)) :
      HierarchyStageMissingColors HB j = HierarchyStageMissingColors H j := by
    refine Fin.cases ?_ (fun i => ?_) j
    · simp [HierarchyStageMissingColors]
    · change TreeMissingColors phi (HB.stage i.succ.castSucc) =
        TreeMissingColors phi (H.stage i.succ.castSucc)
      rw [stageOrdNext i]
  exact @helper_continuation_904 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@phi) (@ett) (@base) (@H)
      (@good) (@B) (@hAB) (@hBT) (@segmentRefl) (@segmentTrans) (@stageSegment) (@lastZero)
      (@lastPositive) (@lastToB) (@firstToB) (@strictFirst) (@mpB) (@hbStageOld) (@hbStageAt)
      (@hbNested) (@hbStrict) (@stageOrdNext) (@starredEq) (@storedEq) (@beforeFirstMissing)
      (@missingEq)
end GoldbergSeymour

end
