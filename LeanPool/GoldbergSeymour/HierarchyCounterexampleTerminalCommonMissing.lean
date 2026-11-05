/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyCounterexampleTailAtLeastTwo

/-!
# Hierarchy Counterexample Terminal Common Missing

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem HierarchyCounterexampleTerminalCommonMissing {V E : Type*}
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
    let Ty := TreeSequencePrefix T
      (min (A.length + (ell - 1)) T.length)
      (by have hA := A.positive; have hT := T.positive; omega)
      (Nat.min_le_right _ _)
    ∃ alpha : Fin k,
      alpha ∈ TreeMissingColors phi Ty ∧
        alpha ∈ MissingColors G phi (T.vertex (Fin.last T.length)) := by
  classical
  dsimp only
  let H := C.hierarchy
  let A := HierarchyStarredStage H (Fin.last H.dividerCount)
  let ell := T.length - A.length
  let Ty := TreeSequencePrefix T
      (min (A.length + (ell - 1)) T.length)
      (by have hA := A.positive; have hT := T.positive; omega)
      (Nat.min_le_right _ _)
  have htail : 2 ≤ ell := by
    dsimp [ell]
    exact HierarchyCounterexampleTailAtLeastTwo G k e0 input T phi ett base C
      hproper hone hlower hfewer hminimal hlarge
  have helem : ColoredVertexSetElementary G phi (TreeSequenceVertexSet Ty) := by
    exact HierarchyCounterexamplePenultimateElementary G k e0 input T phi ett base C
      hproper hone hlower hfewer hminimal hlarge
  have hlen : min (A.length + (ell - 1)) T.length = T.length - 1 := by
    dsimp [ell]
    omega
  have hTy : Ty = TreeSequencePrefix T (T.length - 1)
      (by have hT := T.positive; omega) (by omega) := by
    simp [Ty, hlen]
  have hTyLen : Ty.length = T.length - 1 := by
    rw [hTy]
    rfl
  have hlastNot : T.vertex (Fin.last T.length) ∉ TreeSequenceVertexSet Ty := by
    intro hlast
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hlast
    rcases hlast with ⟨i, hi⟩
    have hv := T.vertex_injective hi
    have hvval := congrArg Fin.val hv
    simp only [Nat.succ_eq_add_one, Fin.val_last] at hvval
    change i.val = T.length at hvval
    have hvval' : i.val = T.length := hvval
    have hii := i.isLt
    omega
  by_contra hnone
  have hnone' : ∀ alpha, alpha ∈ TreeMissingColors phi Ty →
      alpha ∉ MissingColors G phi (T.vertex (Fin.last T.length)) := by
    intro alpha ha hb
    apply hnone
    refine ⟨alpha, ?_, hb⟩
    simpa [Ty, H, A, ell, hlen] using ha
  have prefixMem : ∀ {u : V}, u ∈ TreeSequenceVertexSet T →
      u ≠ T.vertex (Fin.last T.length) → u ∈ TreeSequenceVertexSet Ty := by
    intro u hu hne
    rcases (by simpa [TreeSequenceVertexSet] using hu) with ⟨i, hi⟩
    have hival : i.val < T.length := by
      by_contra hival
      have hii := i.isLt
      have hiLast : i = Fin.last T.length := by
        apply Fin.ext
        simp
        omega
      apply hne
      simpa [hiLast] using hi.symm
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    have hbound : i.val < Ty.length + 1 := by omega
    refine ⟨⟨i.val, hbound⟩, ?_⟩
    change T.vertex (Fin.castLE _ ⟨i.val, hbound⟩) = u
    have hidx : Fin.castLE (by omega) (⟨i.val, hbound⟩ : Fin (Ty.length + 1)) = i := by
      apply Fin.ext
      rfl
    rw [hidx]
    exact hi
  have hdisj : ∀ {u v : V}, u ∈ TreeSequenceVertexSet T →
      v ∈ TreeSequenceVertexSet T → u ≠ v →
      Disjoint (MissingColors G phi u) (MissingColors G phi v) := by
    intro u v hu hv huv
    by_cases huFinal : u = T.vertex (Fin.last T.length)
    · have hvNot : v ≠ T.vertex (Fin.last T.length) := by
        intro hvFinal
        exact huv (huFinal.trans hvFinal.symm)
      have hvTy := prefixMem hv hvNot
      apply Finset.disjoint_left.2
      intro alpha hau hav
      have hat : alpha ∈ TreeMissingColors phi Ty := by
        simp only [TreeMissingColors, Finset.mem_biUnion]
        exact ⟨v, hvTy, hav⟩
      exact hnone' alpha hat (huFinal ▸ hau)
    · have huTy := prefixMem hu huFinal
      by_cases hvFinal : v = T.vertex (Fin.last T.length)
      · apply Finset.disjoint_left.2
        intro alpha hau hav
        have hat : alpha ∈ TreeMissingColors phi Ty := by
          simp only [TreeMissingColors, Finset.mem_biUnion]
          exact ⟨u, huTy, hau⟩
        exact hnone' alpha hat (hvFinal ▸ hav)
      · exact helem huTy (prefixMem hv hvFinal) huv
  apply C.notElementary
  intro u hu v hv huv
  exact hdisj hu hv huv

end GoldbergSeymour

end
