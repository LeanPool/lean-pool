/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

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

end GoldbergSeymour

end
