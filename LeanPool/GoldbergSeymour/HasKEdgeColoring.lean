/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.IsFullEdgeColoring
public import LeanPool.GoldbergSeymour.IsProperEdgeColoring

/-!
# Has KEdge Coloring

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A proper full edge coloring using colors in `Fin k`. -/
def HasKEdgeColoring {V E : Type*} (G : LooplessMultigraph V E) (k : ℕ) : Prop :=
 ∃ φ : PartialEdgeColoring E k, IsProperEdgeColoring G φ ∧ IsFullEdgeColoring φ

end GoldbergSeymour

end
