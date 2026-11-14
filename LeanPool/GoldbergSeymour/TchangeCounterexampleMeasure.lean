/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TchangeCounterexample

/-!
# Tchange Counterexample Measure

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- The sum of the three exit-path lengths in a color-change counterexample. -/
def TchangeCounterexampleMeasure {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    [DecidableEq E] {G : LooplessMultigraph V E} {k : Nat} {e0 : E}
    (C : TchangeCounterexample G k e0) : Nat :=
  C.P1.length + C.P2.length + C.P3.length

end GoldbergSeymour

end
