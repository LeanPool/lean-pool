/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.Incident

/-!
# Boundary Edges

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open scoped Sym2

/-- Edges with one endpoint in the vertex set and one endpoint outside it. -/
noncomputable def BoundaryEdges {V E : Type*} [Fintype V] [Fintype E] (G : LooplessMultigraph V E)
    (U : Finset V) : Finset E := by
  classical
  exact Finset.univ.filter fun e => ∃ u ∈ U, ∃ v ∉ U, G.ends e = s(u, v)

end GoldbergSeymour

end
