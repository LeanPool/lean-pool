/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.RutgersCounterexample

/-!
# Rutgers Counterexample Measure

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- The sum of the lengths of the three exit walks in a Rutgers counterexample. -/
def RutgersCounterexampleMeasure {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    [DecidableEq E] {G : LooplessMultigraph V E} {k : Nat} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
    {original : ExtendedTashkinovTree G k e0 input T generating}
    {presentation : RutgersClosedPresentation G k e0 original}
    (counterexample : RutgersCounterexample G k e0 original presentation) : Nat :=
  counterexample.Q1.length + counterexample.Q2.length + counterexample.Q3.length

end GoldbergSeymour

end
