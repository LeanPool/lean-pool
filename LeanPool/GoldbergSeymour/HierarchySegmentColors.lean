/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyFirstMissingPosition
public import LeanPool.GoldbergSeymour.HierarchyStarredStage

/-!
# Hierarchy Segment Colors

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Colors on the stage segment before the first occurrence of a missing specified color. -/
noncomputable def HierarchySegmentColors {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
    {T : TreeSequence G e0} {generating phi : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input T generating} {base : HierarchyBase ett phi}
    (H : TashkinovHierarchy ett base) (j : Fin (H.dividerCount + 1)) (eta : Fin k) :
    Finset (Fin k) := by
  classical
  let A := HierarchyStarredStage H j
  let B := H.stage j.succ
  let p := HierarchyFirstMissingPosition phi T eta
  exact Finset.univ.filter fun c =>
    ∃ r : Fin B.length, A.length ≤ r.val ∧
      r.val < min p.val B.length ∧ phi (B.edge r) = some c

end GoldbergSeymour

end
