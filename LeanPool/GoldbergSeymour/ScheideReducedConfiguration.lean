/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ScheideStructuralConfiguration

/-!
# Scheide Reduced Configuration

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- The exact exit-vertex count and block-color coverage required for a reduced structural
configuration.
-/
structure ScheideReducedConfiguration {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k)
    (T : TreeSequence G e0) extends ScheideStructuralConfiguration G k e0 phi T where
  exit_card_eq : (ScheideExitVertices T phi).card = s
  exit_exactly_one : ∀ v ∈ ScheideExitVertices T phi, ∃! i : Fin s, gamma i ∈ MissingColors G phi v
  every_block_color_at_exit :
    ∀ i : Fin s, ∃ v ∈ ScheideExitVertices T phi, gamma i ∈ MissingColors G phi v

end GoldbergSeymour

end
