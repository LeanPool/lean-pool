/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet
public import LeanPool.GoldbergSeymour.TwoColorComponent

/-!
# Scheide Defective Chain Path

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A simple two-color path spanning its component from a tree vertex to an outside vertex. -/
def ScheideDefectiveChainPath {V E : Type*} {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k) (alpha gamma : Fin k) (u z : V)
  (p : (TwoColorIncidenceGraph G phi alpha gamma).Walk (Sum.inl u) (Sum.inl z)) : Prop :=
 u ∈ TreeSequenceVertexSet T ∧
  p.IsPath ∧
   z ∉ TreeSequenceVertexSet T ∧
    {x | x ∈ p.support} = TwoColorComponent G phi alpha gamma (Sum.inl u)

end GoldbergSeymour

end
