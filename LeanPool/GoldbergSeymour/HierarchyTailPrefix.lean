/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyStarredStage

/-!
# Prefixes of a hierarchy's terminal tail

Adapted from Wesley Pegden's Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12. This construction applies to any
hierarchy, independently of the counterexample data used in the main proof.
-/

@[expose] public section

namespace GoldbergSeymour

/-- The prefix ending `i` edges after the last starred stage, capped by the full tree. -/
noncomputable def HierarchyTailPrefix {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
    {T : TreeSequence G e0} {phi : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input T phi} {base : HierarchyBase ett phi}
    (H : TashkinovHierarchy ett base) (i : ℕ) : TreeSequence G e0 :=
  let A := HierarchyStarredStage H (Fin.last H.dividerCount)
  TreeSequencePrefix T (min (A.length + i) T.length)
    (le_min (le_trans A.positive (Nat.le_add_right _ _)) T.positive) (Nat.min_le_right _ _)

end GoldbergSeymour

end
