/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.Critical
public import LeanPool.GoldbergSeymour.IsOneEdgeUncolored

public import LeanPool.GoldbergSeymour.MaximumDegree

/-!
# KTriple

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A critical graph with chromatic index `k + 1`, sufficiently many colors and one distinguished
uncolored edge.
-/
def KTriple {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E] (G : LooplessMultigraph V E)
  (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) : Prop :=
 Critical G ∧
  ChromaticIndex G = k + 1 ∧
   MaximumDegree G + 1 ≤ k ∧ IsProperEdgeColoring G phi ∧ IsOneEdgeUncolored phi e0

end GoldbergSeymour

end
