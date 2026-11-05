/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.GoodHierarchyPrefixConstruction

/-!
# Good Hierarchy Prefix Repackage

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open GoodHierarchyPrefix

private abbrev helperContinuation626Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree
        G k e0 input T generating) (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett
        base) (good : GoodHierarchy H) (r : Fin (H.dividerCount + (1 : ℕ))) (hr : (1 : ℕ) ≤ (↑r :
        ℕ)),
    let prefixData : (P : ExtendedTashkinovTree G k e0 input (H.stage r.castSucc) generating) × (B
        : HierarchyBase P phi) × TashkinovHierarchy P B := prefixHierarchyData G k e0 input T
        generating phi ett base H r hr;
    let ettPrefix : ExtendedTashkinovTree G k e0 input (H.stage r.castSucc) generating :=
        prefixData.fst;
    ∀ (mpPrefix : MaximumProperty ettPrefix),
    let basePrefix : HierarchyBase prefixData.fst phi := prefixData.snd.fst;
    ∀ (oldDividerValue :
    ∀ (i : Fin H.dividerCount), (↑(H.dividerPosition i) : ℕ) = (H.stage (⟨(↑i : ℕ) + (1 : ℕ),
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))).length),
    let HP : TashkinovHierarchy prefixData.fst prefixData.snd.fst := prefixData.snd.snd;
    ∀ (stageEqRaw :
    ∀ (j : Fin (HP.dividerCount + (2 : ℕ))), HP.stage j = H.stage (⟨(↑j : ℕ),
    have hj : (↑j : ℕ) < HP.dividerCount + (2 : ℕ) := j.isLt; id (fun (hj : (↑j : ℕ) < (↑r : ℕ) -
        (1 : ℕ) + (2 : ℕ)) ↦ Decidable.byContradiction fun (a : ¬(↑j : ℕ) < H.dividerCount + (2 :
        ℕ)) ↦
    by omega
    ) hj⟩ : Fin (H.dividerCount + (2 : ℕ)))) (starredEqRaw :
    ∀ (j : Fin (HP.dividerCount + (1 : ℕ))), HierarchyStarredStage HP j = HierarchyStarredStage H
        (⟨(↑j : ℕ),
    have hj : (↑j : ℕ) < HP.dividerCount + (1 : ℕ) := j.isLt; id (fun (hj : (↑j : ℕ) < (↑r : ℕ) -
        (1 : ℕ) + (1 : ℕ)) ↦ Decidable.byContradiction fun (a : ¬(↑j : ℕ) < H.dividerCount + (1 :
        ℕ)) ↦
    by omega
    ) hj⟩ : Fin (H.dividerCount + (1 : ℕ)))) (storedEqRaw :
    ∀ (j : Fin (HP.dividerCount + (1 : ℕ))), HierarchyStoredColorsAt HP j =
        HierarchyStoredColorsAt H (⟨(↑j : ℕ),
    have hj : (↑j : ℕ) < HP.dividerCount + (1 : ℕ) := j.isLt; id (fun (hj : (↑j : ℕ) < (↑r : ℕ) -
        (1 : ℕ) + (1 : ℕ)) ↦ Decidable.byContradiction fun (a : ¬(↑j : ℕ) < H.dividerCount + (1 :
        ℕ)) ↦
    by omega
    ) hj⟩ : Fin (H.dividerCount + (1 : ℕ)))) (stageMissingEqRaw :
    ∀ (j : Fin (HP.dividerCount + (1 : ℕ))), HierarchyStageMissingColors HP j =
        HierarchyStageMissingColors H (⟨(↑j : ℕ),
    have hj : (↑j : ℕ) < HP.dividerCount + (1 : ℕ) := j.isLt; id (fun (hj : (↑j : ℕ) < (↑r : ℕ) -
        (1 : ℕ) + (1 : ℕ)) ↦ Decidable.byContradiction fun (a : ¬(↑j : ℕ) < H.dividerCount + (1 :
        ℕ)) ↦
    by omega
    ) hj⟩ : Fin (H.dividerCount + (1 : ℕ)))) (segmentSubsetRaw :
    ∀ (j : Fin (HP.dividerCount + (1 : ℕ))) (eta : Fin k), HierarchySegmentColors HP j eta ⊆
        HierarchySegmentColors H (⟨(↑j : ℕ),
    have hj : (↑j : ℕ) < HP.dividerCount + (1 : ℕ) := j.isLt; id (fun (hj : (↑j : ℕ) < (↑r : ℕ) -
        (1 : ℕ) + (1 : ℕ)) ↦ Decidable.byContradiction fun (a : ¬(↑j : ℕ) < H.dividerCount + (1 :
        ℕ)) ↦
    by omega
    ) hj⟩ : Fin (H.dividerCount + (1 : ℕ))) eta),
    ∃ (ettPrefix : ExtendedTashkinovTree G k e0 input (H.stage r.castSucc) generating),
        MaximumProperty ettPrefix ∧ ettPrefix.rounds = ett.rounds ∧ ettPrefix.series ≍ ett.series
        ∧
    ∃ (basePrefix : HierarchyBase ettPrefix phi), basePrefix.core = base.core ∧ basePrefix.closure
        = base.closure ∧ (↑basePrefix.supportPosition : ℕ) = (↑base.supportPosition : ℕ) ∧
    ∃ (HP : TashkinovHierarchy ettPrefix basePrefix) (hcount : HP.dividerCount = (↑r : ℕ) - (1 :
        ℕ)), (
    ∀ (j : Fin ((↑r : ℕ) + (1 : ℕ))), HP.stage (Fin.cast (
    by omega
    ) j) = H.stage (⟨(↑j : ℕ),
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) ∧ (
    ∀ (i : Fin ((↑r : ℕ) - (1 : ℕ))), (↑(HP.dividerPosition (Fin.cast (
    by omega
    ) i)) : ℕ) = (↑(H.dividerPosition (⟨(↑i : ℕ),
    by omega
    ⟩ : Fin H.dividerCount)) : ℕ)) ∧
    ∃ (goodPrefix : GoodHierarchy HP), (
    ∀ (j : Fin (↑r : ℕ)), HierarchyStoredColorsAt HP (Fin.cast (
    by omega
    ) j) = HierarchyStoredColorsAt H (⟨(↑j : ℕ),
    by omega
    ⟩ : Fin (H.dividerCount + (1 : ℕ))) ∧
    ∀ (eta : Fin k), goodPrefix.gamma (Fin.cast (
    by omega
    ) j) eta = good.gamma (⟨(↑j : ℕ),
    by omega
    ⟩ : Fin (H.dividerCount + (1 : ℕ))) eta) ∧ TreeColorSetMinusClosed G phi (H.stage r.castSucc)
        ((HierarchyStoredColorsAt H r).biUnion (good.gamma (⟨(↑r : ℕ) - (1 : ℕ),
    by omega
    ⟩ : Fin (H.dividerCount + (1 : ℕ)))))

private theorem helper_continuation_626.{u_1, u_2} :
    helperContinuation626Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T generating phi ett base H good r hr prefixData ettPrefix
      mpPrefix basePrefix oldDividerValue HP stageEqRaw starredEqRaw storedEqRaw
      stageMissingEqRaw segmentSubsetRaw
  let oldGammaIndex (j : Fin (HP.dividerCount + 1)) :
      Fin (H.dividerCount + 1) := ⟨j.val, by
        have hj := j.isLt
        change j.val < r.val - 1 + 1 at hj
        omega⟩
  let gammaPrefix : Fin (HP.dividerCount + 1) → Fin k → Finset (Fin k) :=
    fun j eta => good.gamma (oldGammaIndex j) eta
  let goodPrefix : GoodHierarchy HP :=
    { gamma := gammaPrefix
      twoColors := by
        intro j eta heta
        apply good.twoColors (oldGammaIndex j) eta
        rw [← storedEqRaw j]
        exact heta
      avoidance := by
        intro j eta heta c hc
        have hetaOld : eta ∈ HierarchyStoredColorsAt H (oldGammaIndex j) := by
          rw [← storedEqRaw j]
          exact heta
        have hold := good.avoidance (oldGammaIndex j) eta hetaOld hc
        apply Finset.mem_sdiff.mpr
        constructor
        · rw [stageMissingEqRaw j]
          exact (Finset.mem_sdiff.mp hold).1
        · intro hnew
          exact (Finset.mem_sdiff.mp hold).2 (segmentSubsetRaw j eta hnew)
      disjointPairs := by
        intro j eta theta heta htheta hne
        apply good.disjointPairs (oldGammaIndex j) eta theta
        · rw [← storedEqRaw j]
          exact heta
        · rw [← storedEqRaw j]
          exact htheta
        · exact hne
      uniqueRefresh := by
        intro i
        let io : Fin H.dividerCount := ⟨i.val, by
          have hi := i.isLt
          change i.val < r.val - 1 at hi
          omega⟩
        have hold := good.uniqueRefresh io
        rw [storedEqRaw i.succ, stageEqRaw i.succ.castSucc,
          starredEqRaw i.castSucc]
        simpa [gammaPrefix, oldGammaIndex, io] using hold
      parallelBase := by
        simpa [ettPrefix, basePrefix, gammaPrefix, oldGammaIndex, HP,
          HierarchyStoredColorsAt, HierarchyStarredStage] using
            good.parallelBase
      minusClosed := by
        intro i
        let io : Fin H.dividerCount := ⟨i.val, by
          have hi := i.isLt
          change i.val < r.val - 1 at hi
          omega⟩
        have hold := good.minusClosed io
        rw [stageEqRaw i.succ.castSucc, storedEqRaw i.succ]
        simpa [gammaPrefix, oldGammaIndex, io] using hold }
  let lastInternal : Fin H.dividerCount := ⟨r.val - 1, by omega⟩
  have terminalClosed := helper_terminalClosed_412 (@G) (@k) (@e0) (@input) (@T) (@generating)
      (@phi) (@ett) (@base) (@H) (@good) (@r) (@hr)
  refine ⟨ettPrefix, mpPrefix, rfl, HEq.rfl, basePrefix, rfl, rfl, rfl,
    HP, rfl, ?_, ?_, goodPrefix, ?_, terminalClosed⟩
  · intro j
    rfl
  · intro i
    change (H.stage ⟨i.val + 1, by omega⟩).length =
      (H.dividerPosition ⟨i.val, by omega⟩).val
    exact (oldDividerValue ⟨i.val, by omega⟩).symm
  · intro j
    constructor
    · let jp : Fin (HP.dividerCount + 1) :=
        Fin.cast (by dsimp [HP, prefixData, prefixHierarchyData]; omega) j
      have hs := storedEqRaw jp
      convert hs using 1; congr 2
    · intro eta
      rfl

theorem GoodHierarchyPrefixRepackage {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hMP : MaximumProperty ett)
    (base : HierarchyBase ett phi)
    (H : TashkinovHierarchy ett base)
    (good : GoodHierarchy H)
    (r : Fin (H.dividerCount + 1)) (hr : 1 ≤ r.val) :
    ∃ ettPrefix : ExtendedTashkinovTree G k e0 input (H.stage r.castSucc) generating,
    MaximumProperty ettPrefix ∧
    ettPrefix.rounds = ett.rounds ∧
    HEq ettPrefix.series ett.series ∧
    ∃ basePrefix : HierarchyBase ettPrefix phi,
    basePrefix.core = base.core ∧
    basePrefix.closure = base.closure ∧
    basePrefix.supportPosition.val = base.supportPosition.val ∧
    ∃ HP : TashkinovHierarchy ettPrefix basePrefix,
    ∃ hcount : HP.dividerCount = r.val - 1,
    (∀ j : Fin (r.val + 1), HP.stage (Fin.cast (by omega) j) = H.stage ⟨j.val, by omega⟩) ∧
    (∀ i : Fin (r.val - 1),
      (HP.dividerPosition (Fin.cast (by omega) i)).val =
        (H.dividerPosition ⟨i.val, by omega⟩).val) ∧
    ∃ goodPrefix : GoodHierarchy HP,
    (∀ j : Fin r.val,
      HierarchyStoredColorsAt HP (Fin.cast (by omega) j) =
          HierarchyStoredColorsAt H ⟨j.val, by omega⟩ ∧
        ∀ eta : Fin k,
          goodPrefix.gamma (Fin.cast (by omega) j) eta = good.gamma ⟨j.val, by omega⟩ eta) ∧
    TreeColorSetMinusClosed G phi (H.stage r.castSucc)
      ((HierarchyStoredColorsAt H r).biUnion (good.gamma ⟨r.val - 1, by omega⟩)) := by
  classical
  have segmentRefl (A : TreeSequence G e0) :
      TreeSequenceInitialSegment A A :=
    ⟨le_rfl, (by intro i; rfl), (by intro i; rfl)⟩
  have segmentTrans {A B C : TreeSequence G e0}
      (hAB : TreeSequenceInitialSegment A B)
      (hBC : TreeSequenceInitialSegment B C) :
      TreeSequenceInitialSegment A C := by
    apply TreeSequenceInitialSegment.trans <;> assumption
  have stageSegment := @helper_stageSegment_77 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@phi) (@ett) (@base) (@H) (@r)
      (@segmentRefl) (@segmentTrans)
  have prefixEqOfSegment {A B : TreeSequence G e0}
      (hAB : TreeSequenceInitialSegment A B) :
      A = TreeSequencePrefix B A.length A.positive hAB.1 := by
    exact helper_prefixEqOfSegment_95 (@G) (@e0) (@hAB)
  let Tp := H.stage r.castSucc
  have firstToPrefix := helper_firstToPrefix_111 (@G) (@k) (@e0) (@input) (@T) (@generating) (@phi)
      (@ett) (@base) (@H) (@r) (@stageSegment)
  have prefixToTerminal := helper_prefixToTerminal_118 (@G) (@k) (@e0) (@input) (@T) (@generating)
      (@phi) (@ett) (@base) (@H) (@r) (@stageSegment)
  let prefixData := prefixHierarchyData G k e0 input T generating phi ett base H r hr
  let ettPrefix := prefixData.1
  have mpPrefix : MaximumProperty ettPrefix := by
    simpa [MaximumProperty, ettPrefix] using hMP
  let basePrefix := prefixData.2.1
  have oldDividerValue (i : Fin H.dividerCount) :
      (H.dividerPosition i).val =
        (H.stage ⟨i.val + 1, by omega⟩).length := by
    have h := congrArg TreeSequence.length (H.dividerStage i)
    simpa [TreeSequencePrefix] using h.symm
  let HP := prefixData.2.2
  have beforeFirstMissing {A B : TreeSequence G e0}
      (hAB : TreeSequenceInitialSegment A B) (eta : Fin k)
      (i : Fin (A.length + 1)) (hiEnd : i.val < A.length)
      (hi : i.val < (HierarchyFirstMissingPosition phi A eta).val) :
      let iB : Fin (B.length + 1) :=
        Fin.castLE (Nat.succ_le_succ hAB.1) i
      iB.val < (HierarchyFirstMissingPosition phi B eta).val := by
    exact helper_beforeFirstMissing_386 (@G) (@k) (@e0) (@input) (@T) (@generating) (@phi) (@ett)
        (@base) (@H) (@r) (@hAB) (@eta) (@i) (@hiEnd) (@hi)
  have stageEqRaw (j : Fin (HP.dividerCount + 2)) :
      HP.stage j = H.stage ⟨j.val, by
        have hj := j.isLt
        change j.val < r.val - 1 + 2 at hj
        omega⟩ := by
    rfl
  have starredEqRaw (j : Fin (HP.dividerCount + 1)) :
      HierarchyStarredStage HP j =
        HierarchyStarredStage H ⟨j.val, by
          have hj := j.isLt
          change j.val < r.val - 1 + 1 at hj
          omega⟩ := by
    refine Fin.cases ?_ (fun i => ?_) j
    · simp [HierarchyStarredStage, prefixData, prefixHierarchyData]
    · change HP.stage i.succ.castSucc =
        H.stage ⟨i.val + 1, by
          have hi := i.isLt
          change i.val < r.val - 1 at hi
          omega⟩
      exact stageEqRaw i.succ.castSucc
  have storedEqRaw (j : Fin (HP.dividerCount + 1)) :
      HierarchyStoredColorsAt HP j =
        HierarchyStoredColorsAt H ⟨j.val, by
          have hj := j.isLt
          change j.val < r.val - 1 + 1 at hj
          omega⟩ := by
    unfold HierarchyStoredColorsAt
    dsimp [ettPrefix]
    rw [starredEqRaw]
  have stageMissingEqRaw (j : Fin (HP.dividerCount + 1)) :
      HierarchyStageMissingColors HP j =
        HierarchyStageMissingColors H ⟨j.val, by
          have hj := j.isLt
          change j.val < r.val - 1 + 1 at hj
          omega⟩ := by
    refine Fin.cases ?_ (fun i => ?_) j
    · simp [HierarchyStageMissingColors, prefixData, prefixHierarchyData]
    · change TreeMissingColors phi (HP.stage i.succ.castSucc) =
        TreeMissingColors phi (H.stage ⟨i.val + 1, by
          have hi := i.isLt
          change i.val < r.val - 1 at hi
          omega⟩)
      rw [stageEqRaw i.succ.castSucc]
      congr 2
  have segmentSubsetRaw (j : Fin (HP.dividerCount + 1)) (eta : Fin k) :
      HierarchySegmentColors HP j eta ⊆
        HierarchySegmentColors H ⟨j.val, by
          have hj := j.isLt
          change j.val < r.val - 1 + 1 at hj
          omega⟩ eta := by
    intro c hc
    unfold HierarchySegmentColors at hc ⊢
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    rcases hc with ⟨x, hafter, hbefore, hcolor⟩
    let jo : Fin (H.dividerCount + 1) := ⟨j.val, by
      have hj := j.isLt
      change j.val < r.val - 1 + 1 at hj
      omega⟩
    have hstage : HP.stage j.succ = H.stage jo.succ := by
      rw [stageEqRaw j.succ]
      apply congrArg H.stage
      apply Fin.ext
      rfl
    let xo : Fin (H.stage jo.succ).length :=
      Fin.cast (congrArg TreeSequence.length hstage) x
    have hsOld := stageSegment (j.val + 1)
      (r.val - (j.val + 1)) (by
        have hj := j.isLt
        change j.val < r.val - 1 + 1 at hj
        omega)
    have hind : j.val + 1 + (r.val - (j.val + 1)) = r.val := by
      have hj := j.isLt
      change j.val < r.val - 1 + 1 at hj
      omega
    have hidx : (⟨j.val + 1 + (r.val - (j.val + 1)), by omega⟩ :
        Fin (H.dividerCount + 2)) = r.castSucc := Fin.ext hind
    rw [hidx] at hsOld
    have hsNew : TreeSequenceInitialSegment (HP.stage j.succ) Tp := by
      rw [hstage]
      exact hsOld
    have hxStage : x.val < (HP.stage j.succ).length :=
      lt_of_lt_of_le hbefore (Nat.min_le_right _ _)
    have hxFirst : x.val <
        (HierarchyFirstMissingPosition phi Tp eta).val :=
      lt_of_lt_of_le hbefore (Nat.min_le_left _ _)
    let ix : Fin (Tp.length + 1) := ⟨x.val, by omega⟩
    have hxOldFirst := beforeFirstMissing prefixToTerminal eta ix
      (by dsimp [ix]; omega) (by simpa [ix] using hxFirst)
    refine ⟨xo, ?_, ?_, ?_⟩
    · rw [← starredEqRaw j]
      simpa [xo] using hafter
    · apply lt_min
      · simpa [xo, ix] using hxOldFirst
      · simp [xo]
    · cases hstage
      exact hcolor
  exact @helper_continuation_626 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@phi) (@ett) (@base) (@H)
      (@good) (@r) (@hr) (@mpPrefix) (@oldDividerValue) (@stageEqRaw) (@starredEqRaw)
      (@storedEqRaw) (@stageMissingEqRaw) (@segmentSubsetRaw)
end GoldbergSeymour

end
