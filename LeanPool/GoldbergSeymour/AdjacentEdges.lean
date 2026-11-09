/-
Copyright (c) 2026 Wesley Pegden and Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden, Lean Pool contributors
-/
module

public import LeanPool.GoldbergSeymour.Incident

/-!
# Adjacent Edges

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open scoped Sym2

/-- Two edges are adjacent when they have a common incident vertex. -/
def AdjacentEdges {V E : Type*} (G : LooplessMultigraph V E) (e f : E) : Prop :=
 ∃ v, Incident G v e ∧ Incident G v f

/-- Consecutive endpoint pairs give adjacent edges. -/
theorem AdjacentEdges.of_endpoint_pairs {V E : Type*} {G : LooplessMultigraph V E}
    {first second : E} {left middle right : V}
    (first_endpoints : G.ends first = s(left, middle))
    (second_endpoints : G.ends second = s(middle, right)) : AdjacentEdges G first second := by
  refine ⟨middle, ?_, ?_⟩
  · rw [Incident, first_endpoints]
    exact Sym2.mem_mk_right _ _
  · rw [Incident, second_endpoints]
    exact Sym2.mem_mk_left _ _

end GoldbergSeymour

end
