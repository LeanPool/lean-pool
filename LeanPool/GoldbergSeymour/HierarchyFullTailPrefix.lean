/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden, Lean Pool contributors
-/
module

public import LeanPool.GoldbergSeymour.HierarchyTreeFacts

public import LeanPool.GoldbergSeymour.HierarchyCounterexample

/-!
# Hierarchy Full Tail Prefix

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- The prefix extending the last starred stage by at most the requested number of tail edges. -/
noncomputable def HierarchyFullTailPrefix {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
    {T : TreeSequence G e0} {phi : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input T phi} {base : HierarchyBase ett phi}
    (C : HierarchyCounterexample base) (i : ℕ) : TreeSequence G e0 :=
  let H := C.hierarchy
  let A := HierarchyStarredStage H (Fin.last H.dividerCount)
  TreeSequencePrefix T (min (A.length + i) T.length)
    (by
      have hA := A.positive
      have hT := T.positive
      omega)
    (Nat.min_le_right _ _)

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input phi : PartialEdgeColoring E k}
    {tree : TreeSequence G e0} {ett : ExtendedTashkinovTree G k e0 input tree phi}
    {base : HierarchyBase ett phi}

/-- The full-tail prefix stops at the terminal tree length. -/
theorem HierarchyFullTailPrefix.length (counterexample : HierarchyCounterexample base)
    (index : ℕ) :
    (HierarchyFullTailPrefix counterexample index).length =
      min ((HierarchyStarredStage counterexample.hierarchy
        (Fin.last counterexample.hierarchy.dividerCount)).length + index) tree.length := rfl

/-- Before the terminal cutoff, the full-tail prefix has its requested length. -/
theorem HierarchyFullTailPrefix.length_of_le (counterexample : HierarchyCounterexample base)
    (index : ℕ) (bound : (HierarchyStarredStage counterexample.hierarchy
      (Fin.last counterexample.hierarchy.dividerCount)).length + index ≤ tree.length) :
    (HierarchyFullTailPrefix counterexample index).length =
      (HierarchyStarredStage counterexample.hierarchy
        (Fin.last counterexample.hierarchy.dividerCount)).length + index := by
  rw [HierarchyFullTailPrefix.length, min_eq_left bound]

/-- Every full-tail prefix is an initial segment of its terminal tree. -/
theorem HierarchyFullTailPrefix.initialSegment (counterexample : HierarchyCounterexample base)
    (index : ℕ) :
    TreeSequenceInitialSegment (HierarchyFullTailPrefix counterexample index) tree := by
  unfold HierarchyFullTailPrefix
  exact TreeSequenceInitialSegment.prefix_segment _ _ _ _

/-- Full-tail prefixes are nested in their requested index order. -/
theorem HierarchyFullTailPrefix.initialSegmentOfLE
    (counterexample : HierarchyCounterexample base) (first last : ℕ) (ordered : first ≤ last) :
    TreeSequenceInitialSegment (HierarchyFullTailPrefix counterexample first)
      (HierarchyFullTailPrefix counterexample last) := by
  apply (HierarchyFullTailPrefix.initialSegment counterexample last).of_common_extension
    (HierarchyFullTailPrefix.initialSegment counterexample first)
  rw [HierarchyFullTailPrefix.length, HierarchyFullTailPrefix.length]
  exact min_le_min_right _ (Nat.add_le_add_left ordered _)

/-- Every full-tail prefix contains the last starred hierarchy stage. -/
theorem HierarchyFullTailPrefix.starredStageInitialSegment
    (counterexample : HierarchyCounterexample base) (index : ℕ) :
    TreeSequenceInitialSegment
      (HierarchyStarredStage counterexample.hierarchy
        (Fin.last counterexample.hierarchy.dividerCount))
      (HierarchyFullTailPrefix counterexample index) := by
  apply (HierarchyFullTailPrefix.initialSegment counterexample index).of_common_extension
    counterexample.hierarchy.lastStarredInitialSegment
  rw [HierarchyFullTailPrefix.length]
  exact le_min (Nat.le_add_right _ _) counterexample.hierarchy.lastStarredInitialSegment.1

end GoldbergSeymour

end
