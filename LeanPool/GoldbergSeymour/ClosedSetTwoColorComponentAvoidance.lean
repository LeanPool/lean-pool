/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ColoredVertexSetClosed

public import LeanPool.GoldbergSeymour.TwoColorComponentClosedColors

/-!
# Closed Set Two Color Component Avoidance

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ClosedSetTwoColorComponentAvoidance {V E : Type*}
    [Fintype V] [Fintype E] (G : LooplessMultigraph V E) {k : ℕ} (phi : PartialEdgeColoring E k)
    (alpha beta : Fin k) (X : Finset V) (u a b : V)
    (hclosed : ColoredVertexSetClosed G phi X)
    (hu : u ∉ X) (haX : a ∈ X) (hbX : b ∈ X)
    (ha : alpha ∈ MissingColors G phi a)
    (hb : beta ∈ MissingColors G phi b) :
    (∀ v ∈ X, Sum.inl v ∉
        TwoColorComponent G phi alpha beta (Sum.inl u)) ∧
      (∀ e : E, (∃ v ∈ X, Incident G v e) → Sum.inr e ∉
        TwoColorComponent G phi alpha beta (Sum.inl u)) := by
  exact TwoColorComponent.avoidsBoundaryColors G phi alpha beta X u
    (by
      intro e boundary
      exact ⟨fun colored => hclosed boundary haX colored ha,
        fun colored => hclosed boundary hbX colored hb⟩) hu

end GoldbergSeymour

end
