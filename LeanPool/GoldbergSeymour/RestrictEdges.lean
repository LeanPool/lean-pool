/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.LooplessMultigraph

/-!
# Restrict Edges

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- The multigraph retaining precisely the edges of the specified finite set. -/
noncomputable def RestrictEdges {V E : Type*} (G : LooplessMultigraph V E) (F : Finset E) :
    LooplessMultigraph V { e // e ∈ F } := by
  classical
  exact { ends := fun e => G.ends e.1
          loopless := fun e v => G.loopless e.1 v }

end GoldbergSeymour

end
