/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyCounterexamplePenultimateElementary
public import LeanPool.GoldbergSeymour.HierarchyCounterexampleOneAdditionPositiveDividerImpossible
public import LeanPool.GoldbergSeymour.HierarchyCounterexampleOneAdditionZeroDividerImpossible

public import LeanPool.GoldbergSeymour.LowerRoundInductionHypothesis
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentFacts

/-!
# Hierarchy Counterexample Tail At Least Two

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem HierarchyCounterexampleTailAtLeastTwo {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (hproper : IsProperEdgeColoring G phi)
    (hone : IsOneEdgeUncolored phi e0)
    (hlower : LowerRoundInductionHypothesis G k e0 ett.rounds)
    (hfewer : ∀ {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      (other : ExtendedTashkinovTree G k e0 input' T' generating'),
      other.rounds = ett.rounds → MaximumProperty other →
      ∀ (base' : HierarchyBase other generating')
        (K : TashkinovHierarchy other base'),
        GoodHierarchy K → K.dividerCount < C.hierarchy.dividerCount →
        ColoredVertexSetElementary G generating'
          (TreeSequenceVertexSet T'))
    (hminimal : ∀ {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      {other : ExtendedTashkinovTree G k e0 input' T' generating'}
      {base' : HierarchyBase other generating'}
      (C' : HierarchyCounterexample base'),
      other.rounds = ett.rounds →
      C'.hierarchy.dividerCount = C.hierarchy.dividerCount →
      ¬ HierarchyCounterexampleLess
        (HierarchyCounterexampleMeasure C')
        (HierarchyCounterexampleMeasure C))
    (hlarge :
      let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
      let Tn := ett.series.data.tree n.castSucc
      2 * ett.rounds + 11 ≤ (TreeMissingColors phi Tn).card) :
    let H := C.hierarchy
    let A := HierarchyStarredStage H (Fin.last H.dividerCount)
    2 ≤ T.length - A.length := by
  have hprefixElementary :
      let H := C.hierarchy
      let A := HierarchyStarredStage H (Fin.last H.dividerCount)
      let ell := T.length - A.length
      let Ty := TreeSequencePrefix T
        (min (A.length + (ell - 1)) T.length)
        (by have hA := A.positive; have hT := T.positive; omega)
        (Nat.min_le_right _ _)
      ColoredVertexSetElementary G phi (TreeSequenceVertexSet Ty) :=
    HierarchyCounterexamplePenultimateElementary G k e0 input T phi ett base C
      hproper hone hlower hfewer hminimal hlarge
  dsimp only
  by_contra hnotTwo
  have hpositiveTail :
      0 < T.length -
        (HierarchyStarredStage C.hierarchy
          (Fin.last C.hierarchy.dividerCount)).length := by
    have lastStage :
    ∀ (d : ℕ) (s : Fin (d + 2) → TreeSequence G e0) (core : TreeSequence G e0), 0 < d → Fin.cases
        core (fun i : Fin d => s i.castSucc.succ) (Fin.last d) = s (Fin.last d).castSucc := by
      intro d s core hd
      cases d with
      | zero => omega
      | succ n =>
        have hi : Fin.last (n + 1) = (Fin.last n).succ := by
          apply Fin.ext
          rfl
        rw [hi]
        rfl
    have zeroStage :
    ∀ (d : ℕ) (s : Fin (d + 2) → TreeSequence G e0) (core : TreeSequence G e0), d = 0 → Fin.cases
        core (fun i : Fin d => s i.castSucc.succ) (Fin.last d) = core := by
      intro d s core hd
      subst d
      rfl
    by_cases hq : 0 < C.hierarchy.dividerCount
    · have hAeq : HierarchyStarredStage C.hierarchy
          (Fin.last C.hierarchy.dividerCount) =
          C.hierarchy.stage (Fin.last C.hierarchy.dividerCount).castSucc := by
        unfold HierarchyStarredStage
        exact lastStage _ _ _ hq
      have hstep := C.hierarchy.strict (Fin.last C.hierarchy.dividerCount)
      have hlenA := congrArg TreeSequence.length hAeq
      have hterm : C.hierarchy.stage (Fin.last C.hierarchy.dividerCount).succ = T := by
        rw [show (Fin.last C.hierarchy.dividerCount).succ =
            Fin.last (C.hierarchy.dividerCount + 1) by
              apply Fin.ext
              rfl]
        exact C.hierarchy.terminalStage
      have hlenT := congrArg TreeSequence.length hterm
      omega
    · have hzero : C.hierarchy.dividerCount = 0 := Nat.eq_zero_of_not_pos hq
      have hAeq : HierarchyStarredStage C.hierarchy
          (Fin.last C.hierarchy.dividerCount) = base.core := by
        unfold HierarchyStarredStage
        exact zeroStage _ _ _ hzero
      have hseg : TreeSequenceInitialSegment
          (HierarchyStarredStage C.hierarchy
            (Fin.last C.hierarchy.dividerCount)) T := by
        have hc := C.hierarchy.coreInsideFirst
        rw [show (⟨1, by omega⟩ : Fin (C.hierarchy.dividerCount + 2)) =
            Fin.last (C.hierarchy.dividerCount + 1) by
              apply Fin.ext
              simp [hzero]] at hc
        rw [hAeq]
        simpa [C.hierarchy.terminalStage, hzero] using hc
      by_contra hnon
      have hle :
          (HierarchyStarredStage C.hierarchy
            (Fin.last C.hierarchy.dividerCount)).length ≤ T.length := hseg.1
      have heq :
          (HierarchyStarredStage C.hierarchy
            (Fin.last C.hierarchy.dividerCount)).length = T.length := by
        omega
      have equalTrees : ∀ {X Y : TreeSequence G e0},
          TreeSequenceInitialSegment X Y → X.length = Y.length → X = Y := by
        intro X Y hXY hlen
        exact hXY.eq_of_length_eq hlen
      have htrees :
          HierarchyStarredStage C.hierarchy
            (Fin.last C.hierarchy.dividerCount) = T := by
        exact equalTrees hseg heq
      have htailzero : T.length -
          (HierarchyStarredStage C.hierarchy
            (Fin.last C.hierarchy.dividerCount)).length = 0 :=
        Nat.eq_zero_of_not_pos hnon
      have prefixFull : ∀ (X : TreeSequence G e0) (hp : 1 ≤ X.length)
          (hq : X.length ≤ X.length),
          TreeSequencePrefix X X.length hp hq = X := by
        intro X hp hq
        exact TreeSequenceInitialSegment.prefix_self X
      have helem : ColoredVertexSetElementary G phi
          (TreeSequenceVertexSet T) := by
        dsimp only at hprefixElementary
        intro u hu v hv huv
        apply hprefixElementary (u := u) (v := v)
        · simpa [htailzero, htrees, prefixFull] using hu
        · simpa [htailzero, htrees, prefixFull] using hv
        · exact huv
      exact C.notElementary helem
  have honeAddition :
      T.length -
        (HierarchyStarredStage C.hierarchy
          (Fin.last C.hierarchy.dividerCount)).length = 1 := by
    omega
  rcases Nat.eq_zero_or_pos C.hierarchy.dividerCount with hzero | hpositive
  · exact HierarchyCounterexampleOneAdditionZeroDividerImpossible
      G k e0 input T phi ett base C hproper hone hlower hfewer hminimal hlarge
      honeAddition hprefixElementary hzero
  · exact HierarchyCounterexampleOneAdditionPositiveDividerImpossible
      G k e0 input T phi ett base C hproper hone hlower hfewer hminimal hlarge
      honeAddition hprefixElementary hpositive

end GoldbergSeymour

end
