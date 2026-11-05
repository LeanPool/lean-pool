/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyEligibleCommonMissingIndices

/-!
# P2905_T2_Empty Common Missing Location

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem P2905_T2_EmptyCommonMissingLocation {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (hpathLower : 2 ≤ HierarchyPathNumber C.hierarchy)
    (hpathUpper : HierarchyPathNumber C.hierarchy < HierarchyFullTailLength C)
    (hempty : ¬ (HierarchyEligibleCommonMissingIndices
      G k e0 input T phi ett base C ctx).Nonempty)
    (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
    (c : Fin k)
    (hc : c ∈ TreeMissingColors P.coloring
      (HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1)))
    (hterm : c ∈ MissingColors G P.coloring (T.vertex (Fin.last T.length))) :
    c ∈ TreeMissingColors P.coloring
      (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)) := by
  classical
  have common {X Y Z : TreeSequence G e0}
      (hXZ : TreeSequenceInitialSegment X Z)
      (hYZ : TreeSequenceInitialSegment Y Z) (hXY : X.length ≤ Y.length) :
      TreeSequenceInitialSegment X Y := by as_aux_lemma =>
    clear * - hXZ hYZ hXY
    refine ⟨hXY, ?_, ?_⟩
    · intro i
      exact (hYZ.2.1 (Fin.castLE (Nat.succ_le_succ hXY) i)).symm.trans (hXZ.2.1 i)
    · intro i
      exact (hYZ.2.2 (Fin.castLE hXY i)).symm.trans (hXZ.2.2 i)
  let j := HierarchyPathNumber C.hierarchy
  let ell := HierarchyFullTailLength C
  let A := HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)
  let B := HierarchyFullTailPrefix C (ell - 1)
  let I := HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx
  have hAT : TreeSequenceInitialSegment A T := by
    have starNext (i : Fin (C.hierarchy.dividerCount + 1)) :
        TreeSequenceInitialSegment (HierarchyStarredStage C.hierarchy i)
          (C.hierarchy.stage i.succ) :=
      Fin.cases C.hierarchy.coreInsideFirst (fun i => C.hierarchy.nested i.succ) i
    simpa only [Fin.succ_last, C.hierarchy.terminalStage] using
      starNext (Fin.last C.hierarchy.dividerCount)
  have htail : 3 ≤ ell := by change j < ell at hpathUpper; change 2 ≤ j at hpathLower; omega
  have hell : ell = T.length - A.length := rfl
  have prefixLen (r : ℕ) (hr : r ≤ ell) :
      (HierarchyFullTailPrefix C r).length = A.length + r := by as_aux_lemma =>
    change min (A.length + r) T.length = A.length + r
    apply Nat.min_eq_left
    omega
  have prefixT (r : ℕ) :
      TreeSequenceInitialSegment (HierarchyFullTailPrefix C r) T :=
    ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
  have hBLen : B.length = T.length - 1 := by
    have := prefixLen (ell - 1) (by omega)
    change B.length = A.length + (ell - 1) at this
    omega
  have hAB : TreeSequenceInitialSegment A B := common hAT (prefixT _) (by omega)
  have vertexMem (U : TreeSequence G e0) (i : Fin (U.length + 1)) :
      U.vertex i ∈ TreeSequenceVertexSet U := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨i, rfl⟩
  have eligible
      (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
      (c : Fin k) (i : ℕ) (hi : 1 ≤ i ∧ i ≤ ell - 1)
      (hc : c ∈ MissingColors G P.coloring
        ((HierarchyFullTailPrefix C i).vertex
          (Fin.last (HierarchyFullTailPrefix C i).length)))
      (hterm : c ∈ MissingColors G P.coloring (T.vertex (Fin.last T.length))) :
      I.Nonempty := by as_aux_lemma =>
    refine ⟨i, ?_⟩
    change i ∈ (Finset.Icc 1 (HierarchyFullTailLength C - 1)).filter _
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr hi, P, c, hc, hterm⟩
  obtain ⟨v, hv, hm⟩ := Finset.mem_biUnion.mp hc
  obtain ⟨x, hx⟩ : ∃ x, B.vertex x = v := by
    simpa only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] using hv
  by_cases hsmall : x.val ≤ A.length
  · let a : Fin (A.length + 1) := ⟨x.val, by omega⟩
    have ha : Fin.castLE (Nat.succ_le_succ hAB.1) a = x := Fin.ext rfl
    have hmA : c ∈ MissingColors G P.coloring (A.vertex a) := by
      rw [← hAB.2.1 a, ha, hx]
      exact hm
    exact Finset.mem_biUnion.mpr ⟨A.vertex a, vertexMem A a, hmA⟩
  · let i := x.val - A.length
    have hi : 1 ≤ i ∧ i ≤ ell - 1 := by
      have := x.isLt
      change B.length = T.length - 1 at hBLen
      dsimp [i]
      omega
    have hp := prefixLen i (by omega)
    have hcI : c ∈ MissingColors G P.coloring
        ((HierarchyFullTailPrefix C i).vertex
          (Fin.last (HierarchyFullTailPrefix C i).length)) := by
      rw [← (prefixT i).2.1]
      have hidx : Fin.castLE (Nat.succ_le_succ (prefixT i).1)
          (Fin.last (HierarchyFullTailPrefix C i).length) =
          Fin.castLE (Nat.succ_le_succ (prefixT (ell - 1)).1) x := by
        apply Fin.ext
        simp only [Fin.val_castLE, Fin.val_last]
        rw [hp]
        dsimp [i]
        omega
      rw [hidx, (prefixT (ell - 1)).2.1, hx]
      exact hm
    exact (hempty (eligible P c i hi hcI hterm)).elim

end GoldbergSeymour

end
