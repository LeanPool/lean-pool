/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Data.Rat.Cast.Order
public import LeanPool.GoldbergSeymour.InternalEdges

/-!
# Density Value

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- The rational density `2 * |E(U)| / (|U| - 1)` of a vertex set. -/
noncomputable def DensityValue {V E : Type*} [Fintype V] [Fintype E] (G : LooplessMultigraph V E)
    (U : Finset V) : ℚ :=
  (2 * (InternalEdges G U).card : ℚ) / (U.card - 1)

end GoldbergSeymour

end
