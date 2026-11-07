/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.AbsorbingVertex

/-!
# Absorbing Vertices

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Outside vertices satisfying the absorbing-vertex condition for the given coloring and tree. -/
noncomputable def AbsorbingVertices {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) : Finset V := by
  classical
  exact Finset.univ.filter fun v => AbsorbingVertex T phi v

end GoldbergSeymour

end
