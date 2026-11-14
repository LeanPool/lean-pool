/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyCounterexample
public import LeanPool.GoldbergSeymour.HierarchyPathNumber

/-!
# Hierarchy Counterexample Measure

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- The path number and length beyond the last ordinary hierarchy stage. -/
noncomputable def HierarchyCounterexampleMeasure {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input T generating} {base : HierarchyBase ett generating}
    (C : HierarchyCounterexample base) : ℕ × ℕ :=
  (HierarchyPathNumber C.hierarchy,
    T.length - (C.hierarchy.stage ⟨C.hierarchy.dividerCount, by omega⟩).length)

end GoldbergSeymour

end
