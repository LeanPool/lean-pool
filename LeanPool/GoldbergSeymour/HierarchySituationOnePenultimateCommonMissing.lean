/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyClaimNine

public import LeanPool.GoldbergSeymour.HierarchySituationOneAdvanceInsideStored
public import LeanPool.GoldbergSeymour.HierarchySituationOneAdvanceOutsideStored

/-!
# Hierarchy Situation One Penultimate Common Missing

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem HierarchySituationOnePenultimateCommonMissing {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (hsituation : HierarchyPathNumber C.hierarchy = 1)
    (hvertexMissing : ∀ (mu : PartialEdgeColoring E k),
      IsProperEdgeColoring G mu → IsOneEdgeUncolored mu e0 →
        ∀ v : V, (MissingColors G mu v).Nonempty)
    (hnonempty : (HierarchyEligibleCommonMissingIndices
      G k e0 input T phi ett base C ctx).Nonempty) :
    HierarchyFullTailLength C - 1 ∈
      HierarchyEligibleCommonMissingIndices
        G k e0 input T phi ett base C ctx := by
  classical
  let I := HierarchyEligibleCommonMissingIndices
    G k e0 input T phi ett base C ctx
  have hI : I.Nonempty := hnonempty
  let i := I.max' hI
  have hiI : i ∈ I := Finset.max'_mem I hI
  have hiBounds : 1 ≤ i ∧ i ≤ HierarchyFullTailLength C - 1 := by
    have hiFiltered : i ∈
        (Finset.Icc 1 (HierarchyFullTailLength C - 1)).filter (fun j =>
          ∃ P : HierarchyReplacementPresentation
              G k e0 input T phi ett base C ctx,
            ∃ alpha : Fin k,
              alpha ∈ MissingColors G P.coloring
                  ((HierarchyFullTailPrefix C j).vertex
                    (Fin.last (HierarchyFullTailPrefix C j).length)) ∧
                alpha ∈ MissingColors G P.coloring
                  (T.vertex (Fin.last T.length))) := by
      simpa [I, HierarchyEligibleCommonMissingIndices] using hiI
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hiFiltered).1)
  have hiData : ∃ P : HierarchyReplacementPresentation
        G k e0 input T phi ett base C ctx,
      ∃ alpha : Fin k,
        alpha ∈ MissingColors G P.coloring
            ((HierarchyFullTailPrefix C i).vertex
              (Fin.last (HierarchyFullTailPrefix C i).length)) ∧
          alpha ∈ MissingColors G P.coloring
            (T.vertex (Fin.last T.length)) := by
    have hiFiltered : i ∈
        (Finset.Icc 1 (HierarchyFullTailLength C - 1)).filter (fun j =>
          ∃ P : HierarchyReplacementPresentation
              G k e0 input T phi ett base C ctx,
            ∃ alpha : Fin k,
              alpha ∈ MissingColors G P.coloring
                  ((HierarchyFullTailPrefix C j).vertex
                    (Fin.last (HierarchyFullTailPrefix C j).length)) ∧
                alpha ∈ MissingColors G P.coloring
                  (T.vertex (Fin.last T.length))) := by
      simpa [I, HierarchyEligibleCommonMissingIndices] using hiI
    exact (Finset.mem_filter.mp hiFiltered).2
  obtain ⟨P, alpha, hcommon⟩ := hiData
  have heq : i = HierarchyFullTailLength C - 1 := by
    by_contra hne
    have hlt : i < HierarchyFullTailLength C - 1 :=
      Nat.lt_of_le_of_ne hiBounds.2 hne
    have hnext : i + 1 ∈ I := by
      by_cases hstored :
          alpha ∈ HierarchyStoredColorsAt P.counterexample.hierarchy
            (Fin.last P.counterexample.hierarchy.dividerCount)
      · exact HierarchySituationOneAdvanceInsideStored G k e0 input T phi ett
          base C ctx hsituation hvertexMissing i hiBounds.1 hlt P alpha hcommon
          hstored
      · exact HierarchySituationOneAdvanceOutsideStored G k e0 input T phi ett
          base C ctx hsituation hvertexMissing i hiBounds.1 hlt P alpha hcommon
          hstored
    have hle : i + 1 ≤ i := Finset.le_max' I (i + 1) hnext
    exact (Nat.not_succ_le_self i) hle
  simpa [I, heq] using hiI

end GoldbergSeymour

end
