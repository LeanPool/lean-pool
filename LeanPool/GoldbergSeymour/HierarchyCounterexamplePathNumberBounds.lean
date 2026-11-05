/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyCounterexampleTailAtLeastTwo

/-!
# Hierarchy Counterexample Path Number Bounds

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem HierarchyCounterexamplePathNumberBounds {V E : Type*}
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
    let ell := T.length - A.length
    let r := HierarchyPathNumber H
    1 ≤ r ∧ r ≤ ell := by
  classical
  have htail := HierarchyCounterexampleTailAtLeastTwo G k e0 input T phi ett base C
    hproper hone hlower hfewer hminimal hlarge
  let H := C.hierarchy
  let A := HierarchyStarredStage H (Fin.last H.dividerCount)
  let ell := T.length - A.length
  let candidates := (Finset.Icc 1 ell).filter fun i =>
    ∀ q : Fin T.length, A.length + i ≤ q.val →
      G.ends (T.edge q) = s(T.vertex q.castSucc, T.vertex q.succ)
  have htail' : 2 ≤ ell := by
    dsimp [ell, A, H]
    exact htail
  have hAle : A.length ≤ T.length := by omega
  have hsum : A.length + ell = T.length := Nat.add_sub_of_le hAle
  have hellpos : 1 ≤ ell := by omega
  have hellmem : ell ∈ candidates := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨hellpos, le_rfl⟩, ?_⟩
    intro q hq
    exfalso
    omega
  have hnonempty : candidates.Nonempty := ⟨ell, hellmem⟩
  have hminmem : candidates.min' hnonempty ∈ candidates :=
    Finset.min'_mem candidates hnonempty
  have hminbounds : 1 ≤ candidates.min' hnonempty ∧
      candidates.min' hnonempty ≤ ell := by
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hminmem).1)
  change (1 ≤ (if h : candidates.Nonempty then candidates.min' h else ell) ∧
    (if h : candidates.Nonempty then candidates.min' h else ell) ≤ ell)
  rw [dite_eq_left hnonempty]
  exact hminbounds

end GoldbergSeymour

end
