/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.MissingColors
public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet
public import LeanPool.GoldbergSeymour.TwoColorIncidenceGraph

/-!
# Tree Exit Path

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A simple two-color path of length at least two meeting the tree only at its inside endpoint,
with a missing color outside.
-/
def TreeExitPath {V E : Type*} [Fintype E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (T : TreeSequence G e0) (phi : PartialEdgeColoring E k) (alpha beta : Fin k) (u v : V)
    (p : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl u) (Sum.inl v)) : Prop :=
  p.IsPath ∧
    2 ≤ p.length ∧
      u ∉ TreeSequenceVertexSet T ∧
        v ∈ TreeSequenceVertexSet T ∧
          (alpha ∈ MissingColors G phi u ∨ beta ∈ MissingColors G phi u) ∧
            ∀ w ∈ TreeSequenceVertexSet T, (Sum.inl w ∈ p.support ↔ w = v)

end GoldbergSeymour

end
