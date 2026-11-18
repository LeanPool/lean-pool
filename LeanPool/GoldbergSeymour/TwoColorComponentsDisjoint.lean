/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TwoColorComponent

/-!
# Two Color Components Disjoint

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem TwoColorComponentsDisjoint {V E : Type*} (G : LooplessMultigraph V E)
    {k : ℕ} (phi : PartialEdgeColoring E k) (alpha beta : Fin k)
    (z w : Sum V E) :
    TwoColorComponent G phi alpha beta z = TwoColorComponent G phi alpha beta w ∨
      Disjoint (TwoColorComponent G phi alpha beta z)
        (TwoColorComponent G phi alpha beta w) := by
  classical
  let H := TwoColorIncidenceGraph G phi alpha beta
  by_cases h : H.connectedComponentMk z = H.connectedComponentMk w
  · left
    simp [TwoColorComponent, H, h]
  · right
    exact SimpleGraph.pairwise_disjoint_supp_connectedComponent H h

end GoldbergSeymour

end
