/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TwoColorPathComponent

/-!
# Two Color Nontrivial Path Component

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A two-color path component containing at least one edge node. -/
def TwoColorNontrivialPathComponent {V E : Type*} (G : LooplessMultigraph V E) {k : ℕ}
  (phi : PartialEdgeColoring E k) (alpha beta : Fin k) (z : Sum V E) : Prop :=
 TwoColorPathComponent G phi alpha beta z ∧
  ∃ f : E, Sum.inr f ∈ TwoColorComponent G phi alpha beta z

end GoldbergSeymour

end
