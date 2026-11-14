/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Paths
public import LeanPool.GoldbergSeymour.TwoColorIncidenceGraph

/-!
# Two Color Cycle

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A closed walk certified to be a simple cycle in the two-color incidence graph. -/
structure TwoColorCycle {V E : Type*} (G : LooplessMultigraph V E) {k : ℕ}
    (phi : PartialEdgeColoring E k) (alpha beta : Fin k) where
  /-- The incidence-graph node at which the cycle starts and ends. -/
  base : Sum V E
  /-- The closed two-color walk certified to be a simple cycle. -/
  walk : (TwoColorIncidenceGraph G phi alpha beta).Walk base base
  isCycle : walk.IsCycle

end GoldbergSeymour

end
