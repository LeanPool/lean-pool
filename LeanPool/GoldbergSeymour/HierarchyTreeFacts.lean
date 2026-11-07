/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyStarredStage

public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentFacts

/-!
# Hierarchy stage and closure inclusions

These facts depend only on the hierarchy or base, independently of coloring-change constructions.
-/

@[expose] public section

namespace GoldbergSeymour

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input generating phi : PartialEdgeColoring E k}
    {tree : TreeSequence G e0} {ett : ExtendedTashkinovTree G k e0 input tree generating}
    {base : HierarchyBase ett phi}

/-- Every stage of a hierarchy is an initial segment of its terminal tree. -/
theorem TashkinovHierarchy.stageInitialSegment (hierarchy : TashkinovHierarchy ett base)
    (index : Fin (hierarchy.dividerCount + 2)) :
    TreeSequenceInitialSegment (hierarchy.stage index) tree := by
  exact Fin.reverseInduction
    (motive := fun index => TreeSequenceInitialSegment (hierarchy.stage index) tree)
    (by simpa only [hierarchy.terminalStage] using TreeSequenceInitialSegment.refl tree)
    (fun index next => (hierarchy.nested index).trans next) index

/-- In the parallel case the closure vertices are contained in the base core. -/
theorem HierarchyBase.closure_vertexSet_subset_core (base : HierarchyBase ett phi)
    (parallel : ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE) :
    TreeSequenceVertexSet base.closure ⊆ TreeSequenceVertexSet base.core := by
  obtain ⟨_, _, ⟨union⟩⟩ := base.parallel parallel
  intro vertex member
  rw [union.vertexSet]
  exact Finset.mem_union_right _ member

/-- Earlier ordinary hierarchy stages are initial segments of later stages. -/
theorem TashkinovHierarchy.stageInitialSegmentOfLE (hierarchy : TashkinovHierarchy ett base)
    (first last : Fin (hierarchy.dividerCount + 2)) (ordered : first ≤ last) :
    TreeSequenceInitialSegment (hierarchy.stage first) (hierarchy.stage last) := by
  have nested : ∀ last : Fin (hierarchy.dividerCount + 2),
      ∀ first, first ≤ last →
        TreeSequenceInitialSegment (hierarchy.stage first) (hierarchy.stage last) := by
    intro last
    induction last using Fin.induction with
    | zero =>
      intro first ordered
      change first.val ≤ 0 at ordered
      have equal : first = 0 := by
        apply Fin.ext
        simpa only [Fin.val_zero] using Nat.eq_zero_of_le_zero ordered
      subst first
      exact TreeSequenceInitialSegment.refl _
    | succ index induction =>
      intro first ordered
      by_cases equal : first = index.succ
      · subst first
        exact TreeSequenceInitialSegment.refl _
      · have different : first.val ≠ index.val + 1 := fun same => equal (Fin.ext same)
        change first.val ≤ index.val + 1 at ordered
        exact (induction first (by change first.val ≤ index.val; omega)).trans
          (hierarchy.nested index)
  exact nested last first ordered

/-- Every starred stage is contained in the next ordinary stage. -/
theorem TashkinovHierarchy.starredStageInitialSegmentNext
    (hierarchy : TashkinovHierarchy ett base) (index : Fin (hierarchy.dividerCount + 1)) :
    TreeSequenceInitialSegment
      (HierarchyStarredStage hierarchy index) (hierarchy.stage index.succ) :=
  Fin.cases hierarchy.coreInsideFirst (fun index => hierarchy.nested index.succ) index

/-- The last starred stage is contained in the terminal tree. -/
theorem TashkinovHierarchy.lastStarredInitialSegment (hierarchy : TashkinovHierarchy ett base) :
    TreeSequenceInitialSegment
      (HierarchyStarredStage hierarchy (Fin.last hierarchy.dividerCount)) tree := by
  simpa only [Fin.succ_last, hierarchy.terminalStage] using
    hierarchy.starredStageInitialSegmentNext (Fin.last hierarchy.dividerCount)

/-- The starred hierarchy stages are nested in their index order. -/
theorem TashkinovHierarchy.starredStageInitialSegmentOfLE
    (hierarchy : TashkinovHierarchy ett base) (first last : Fin (hierarchy.dividerCount + 1))
    (ordered : first ≤ last) :
    TreeSequenceInitialSegment
      (HierarchyStarredStage hierarchy first) (HierarchyStarredStage hierarchy last) := by
  by_cases equal : first = last
  · subst last
    exact TreeSequenceInitialSegment.refl _
  · have strict : first.val < last.val := by omega
    have nonzero : last ≠ 0 := by intro zero; subst last; simp at strict
    have lastStage : HierarchyStarredStage hierarchy last = hierarchy.stage last.castSucc := by
      rw [← Fin.succ_pred last nonzero]
      rfl
    rw [lastStage]
    exact (hierarchy.starredStageInitialSegmentNext first).trans
      (hierarchy.stageInitialSegmentOfLE first.succ last.castSucc
        (by change first.val + 1 ≤ last.val; omega))

/-- With no internal divider the first stage is the terminal tree. -/
theorem TashkinovHierarchy.firstStageOfNoDividers (hierarchy : TashkinovHierarchy ett base)
    (count : hierarchy.dividerCount = 0) :
    hierarchy.stage (0 : Fin (hierarchy.dividerCount + 1)).succ = tree := by
  have index : (0 : Fin (hierarchy.dividerCount + 1)).succ =
      Fin.last (hierarchy.dividerCount + 1) := by
    apply Fin.ext
    simp only [Fin.val_succ, Fin.val_zero, Fin.val_last, count]
  rw [index, hierarchy.terminalStage]

end GoldbergSeymour

end
