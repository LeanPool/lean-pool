/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TreeSequenceColoringFacts

/-!
# Invariance of first missing positions

The totalized first missing position depends only on missing-color sets before the final
vertex. Generalized from the credited Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Agreement before the final vertex preserves the totalized first missing position. -/
theorem TreeSequence.firstMissingPosition_eq_of_agreement {V E : Type*} [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} (tree : TreeSequence G e0)
    {phi sigma : PartialEdgeColoring E k}
    (agreement : ∀ index : Fin (tree.length + 1), index.val < tree.length →
      MissingColors G sigma (tree.vertex index) = MissingColors G phi (tree.vertex index))
    (color : Fin k) :
    HierarchyFirstMissingPosition sigma tree color =
      HierarchyFirstMissingPosition phi tree color := by
  apply Fin.ext
  apply Nat.le_antisymm
  · by_cases before : (HierarchyFirstMissingPosition phi tree color).val < tree.length
    · apply TreeSequenceFirstMissingPositionLe
      rw [agreement _ before]
      exact TreeSequenceFirstMissingPositionMem before
    · have := (HierarchyFirstMissingPosition sigma tree color).isLt
      omega
  · by_cases before : (HierarchyFirstMissingPosition sigma tree color).val < tree.length
    · apply TreeSequenceFirstMissingPositionLe
      rw [← agreement _ before]
      exact TreeSequenceFirstMissingPositionMem before
    · have := (HierarchyFirstMissingPosition phi tree color).isLt
      omega

/-- Vertex-wise agreement away from the final vertex preserves every first position. -/
theorem TreeSequence.firstMissingPosition_eq_of_except_last {V E : Type*} [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} (tree : TreeSequence G e0)
    {phi sigma : PartialEdgeColoring E k}
    (agreement : ∀ vertex ∈ TreeSequenceVertexSet tree,
      vertex ≠ tree.vertex (Fin.last tree.length) →
        MissingColors G sigma vertex = MissingColors G phi vertex) (color : Fin k) :
    HierarchyFirstMissingPosition sigma tree color =
      HierarchyFirstMissingPosition phi tree color := by
  classical
  apply tree.firstMissingPosition_eq_of_agreement (color := color)
  intro index before
  apply agreement
  · simp [TreeSequenceVertexSet]
  · intro equal
    have indices := congrArg Fin.val (tree.vertex_injective equal)
    simp only [Fin.val_last] at indices
    omega

end GoldbergSeymour

end
