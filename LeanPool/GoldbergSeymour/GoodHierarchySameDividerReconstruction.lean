/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden, Lean Pool contributors
-/
module

public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTreeTerminalData
public import LeanPool.GoldbergSeymour.HierarchyTreeFacts
public import LeanPool.GoldbergSeymour.HierarchyFieldTransport
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceInitialSegment

/-!
# Good Hierarchy Same Divider Reconstruction

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem GoodHierarchySameDividerReconstruction {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating sigma : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (J U : TreeSequence G e0)
    (corrJ : CorrespondingExtendedTashkinovTree G k e0 ett sigma J)
    (baseJ : HierarchyBase corrJ.replacementETT sigma)
    (KJ : TashkinovHierarchy corrJ.replacementETT baseJ)
    (corrU : CorrespondingExtendedTashkinovTree G k e0 ett sigma U)
    (baseU : HierarchyBase corrU.replacementETT sigma)
    (hcore : baseU.core = baseJ.core)
    (hJU : TashkinovAugmentationSequence sigma J U) :
    ∃ KU : TashkinovHierarchy corrU.replacementETT baseU,
    ∃ hcount : KU.dividerCount = KJ.dividerCount,
    (∀ j : Fin (KU.dividerCount + 1),
        let jo : Fin (KJ.dividerCount + 1) :=
          Fin.cast (congrArg (fun n : ℕ => n + 1) hcount) j
        KU.stage j.castSucc = KJ.stage jo.castSucc ∧
          HierarchyStarredStage KU j = HierarchyStarredStage KJ jo ∧
            HierarchyStoredColorsAt KU j = HierarchyStoredColorsAt KJ jo ∧
              HierarchyStageMissingColors KU j = HierarchyStageMissingColors KJ jo) ∧
      ∀ i : Fin KU.dividerCount,
        (KU.dividerPosition i).val = (KJ.dividerPosition (Fin.cast hcount i)).val := by
  classical
  have segment := TashkinovAugmentationSequenceInitialSegment sigma J U hJU
  have treeEq := corrU.terminalData.1.trans corrJ.terminalData.1.symm
  have storedEq := corrU.terminalData.2.2.trans corrJ.terminalData.2.2.symm
  let stages : Fin (KJ.dividerCount + 2) → TreeSequence G e0 :=
    fun j => if j.val = KJ.dividerCount + 1 then U else KJ.stage j
  have old (j : Fin (KJ.dividerCount + 1)) :
      stages j.castSucc = KJ.stage j.castSucc := by
    exact ite_eq_right (Nat.ne_of_lt j.isLt)
  have terminal : stages (Fin.last (KJ.dividerCount + 1)) = U := ite_eq_left rfl
  have step (j : Fin (KJ.dividerCount + 1)) :
      TreeSequenceInitialSegment (stages j.castSucc) (stages j.succ) ∧
        (stages j.castSucc).length < (stages j.succ).length := by
    rw [old]
    by_cases last : j.val = KJ.dividerCount
    · have index : j = Fin.last KJ.dividerCount := Fin.ext last
      subst j
      rw [show (Fin.last KJ.dividerCount).succ =
        Fin.last (KJ.dividerCount + 1) from rfl, terminal]
      have nested := KJ.nested (Fin.last KJ.dividerCount)
      have strict := KJ.strict (Fin.last KJ.dividerCount)
      rw [show (Fin.last KJ.dividerCount).succ =
        Fin.last (KJ.dividerCount + 1) from rfl, KJ.terminalStage] at nested strict
      exact ⟨nested.trans segment, lt_of_lt_of_le strict segment.1⟩
    · have notLast : j.succ.val ≠ KJ.dividerCount + 1 := by
        have := j.isLt
        simp only [Fin.val_succ]
        omega
      rw [show stages j.succ = KJ.stage j.succ from ite_eq_right notLast]
      exact ⟨KJ.nested j, KJ.strict j⟩
  let KU : TashkinovHierarchy corrU.replacementETT baseU :=
    { dividerCount := KJ.dividerCount
      stage := stages
      baseStage := (old 0).trans (KJ.baseStage.trans treeEq.symm)
      terminalStage := terminal
      nested := fun j => (step j).1
      strict := fun j => (step j).2
      dividerPosition := fun i => Fin.castLE (Nat.succ_le_succ segment.1) (KJ.dividerPosition i)
      dividerPositive := KJ.dividerPositive
      dividerIncreasing := KJ.dividerIncreasing
      dividerStage := by
        intro i
        have index : i.val + 1 ≠ KJ.dividerCount + 1 := by have := i.isLt; omega
        rw [show stages ⟨i.val + 1, by omega⟩ = KJ.stage ⟨i.val + 1, by omega⟩
          from ite_eq_right index, KJ.dividerStage]
        exact ((TreeSequenceInitialSegment.prefix_segment J _ (KJ.dividerPositive i)
          (Nat.le_of_lt_succ (KJ.dividerPosition i).isLt)).trans segment).eq_prefix
      coreInsideFirst := by
        rw [hcore]
        by_cases count : KJ.dividerCount = 0
        · have index : (⟨1, by omega⟩ : Fin (KJ.dividerCount + 2)) =
              Fin.last (KJ.dividerCount + 1) := Fin.ext (by simpa using count)
          rw [index, terminal]
          exact (KJ.coreInsideFirst.trans (KJ.stageInitialSegment _)).trans segment
        · have index : 1 ≠ KJ.dividerCount + 1 := by omega
          rw [show stages ⟨1, by omega⟩ = KJ.stage ⟨1, by omega⟩ from ite_eq_right index]
          exact KJ.coreInsideFirst }
  have stars (j : Fin (KJ.dividerCount + 1)) :
      HierarchyStarredStage KU j = HierarchyStarredStage KJ j := by
    refine Fin.cases ?_ (fun i => ?_) j
    · exact hcore
    · exact old i.succ
  refine ⟨KU, rfl, ?_, fun _ => rfl⟩
  intro j
  exact ⟨old j, stars j,
    KJ.storedColors_eq_of_agreement KU j j storedEq (stars j) rfl,
    KJ.stageMissingColors_eq_of_agreement KU j j (old j) rfl⟩

end GoldbergSeymour

end
