/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.GoodHierarchyPrefixPreparation
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentFacts

/-!
# Good Hierarchy Prefix Repackage

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

namespace GoodHierarchyPrefix

/-- Typed data construction shared by the hierarchy construction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
noncomputable abbrev prefixHierarchyData {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
    (T : TreeSequence G e0) (generating phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating) (base : HierarchyBase ett phi)
    (H : TashkinovHierarchy ett base) (r : Fin (H.dividerCount + 1)) (hr : 1 ≤ r.val) :
    Σ P : ExtendedTashkinovTree G k e0 input (H.stage r.castSucc) generating,
      Σ B : HierarchyBase P phi, TashkinovHierarchy P B := by
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
  let ettPrefix : ExtendedTashkinovTree G k e0 input Tp generating :=
    { rounds := ett.rounds
      roundsPositive := ett.roundsPositive
      series := ett.series
      abovePenultimate := firstToPrefix
      strictAbovePenultimate := by
        exact helper_strictAbovePenultimate_337 (@G) (@k) (@e0) (@input) (@T) (@generating)
            (@phi) (@ett) (@base) (@H) (@r) (@hr) (@stageSegment)
      belowFinal := segmentTrans prefixToTerminal ett.belowFinal
      generatingColoring := ett.generatingColoring }
  let basePrefix : HierarchyBase ettPrefix phi :=
    { core := base.core
      closure := base.closure
      supportPosition := base.supportPosition
      supportPositive := base.supportPositive
      terminalMissingColors := by simpa [ettPrefix] using base.terminalMissingColors
      parallel := by simpa [ettPrefix] using base.parallel
      nonparallel := by simpa [ettPrefix] using base.nonparallel }
  have oldDividerValue (i : Fin H.dividerCount) :
      (H.dividerPosition i).val =
        (H.stage ⟨i.val + 1, by omega⟩).length := by
    have h := congrArg TreeSequence.length (H.dividerStage i)
    simpa [TreeSequencePrefix] using h.symm
  let dividerPositionPrefix (i : Fin (r.val - 1)) : Fin (Tp.length + 1) :=
    ⟨(H.stage ⟨i.val + 1, by omega⟩).length,
      by
        have hs := stageSegment (i.val + 1)
          (r.val - (i.val + 1)) (by omega)
        have hind : i.val + 1 + (r.val - (i.val + 1)) = r.val := by omega
        have hidx : (⟨i.val + 1 + (r.val - (i.val + 1)), by omega⟩ :
            Fin (H.dividerCount + 2)) = r.castSucc := Fin.ext hind
        rw [hidx] at hs
        exact Nat.lt_succ_of_le (by simpa [Tp] using hs.1)⟩
  let HP : TashkinovHierarchy ettPrefix basePrefix :=
    { dividerCount := r.val - 1
      stage := fun j => H.stage ⟨j.val, by omega⟩
      baseStage := by simpa [ettPrefix] using H.baseStage
      terminalStage := by
        exact helper_terminalStage_419 (@G) (@k) (@e0) (@input) (@T) (@generating) (@phi) (@ett)
            (@base) (@H) (@r) (@hr)
      nested := by
        intro j
        have hn := H.nested ⟨j.val, by omega⟩
        convert hn using 1 <;> apply congrArg H.stage <;> apply Fin.ext <;> rfl
      strict := by
        intro j
        have hs := H.strict ⟨j.val, by omega⟩
        convert hs using 1 <;> apply congrArg TreeSequence.length <;>
          apply congrArg H.stage <;> apply Fin.ext <;> rfl
      dividerPosition := dividerPositionPrefix
      dividerPositive := by
        intro i
        exact (H.stage ⟨i.val + 1, by omega⟩).positive
      dividerIncreasing := by
        intro i j hij
        have oldInc := H.dividerIncreasing
          (⟨i.val, by omega⟩ : Fin H.dividerCount)
          (⟨j.val, by omega⟩ : Fin H.dividerCount) hij
        simpa [dividerPositionPrefix, oldDividerValue] using oldInc
      dividerStage := by
        intro i
        have hs := stageSegment (i.val + 1)
          (r.val - (i.val + 1)) (by omega)
        have hind : i.val + 1 + (r.val - (i.val + 1)) = r.val := by omega
        have hidx : (⟨i.val + 1 + (r.val - (i.val + 1)), by omega⟩ :
            Fin (H.dividerCount + 2)) = r.castSucc := Fin.ext hind
        rw [hidx] at hs
        simpa [dividerPositionPrefix, Tp] using prefixEqOfSegment hs
      coreInsideFirst := by simpa [basePrefix] using H.coreInsideFirst }
  exact ⟨ettPrefix, basePrefix, HP⟩

end GoodHierarchyPrefix

end GoldbergSeymour

end
