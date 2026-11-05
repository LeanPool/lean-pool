/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TreeFreeColors
public import LeanPool.GoldbergSeymour.TwoColorComponent

/-!
# Absorbing Vertex

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/--
An outside vertex whose two-color components select unique missing-color witnesses in the tree. -/
def AbsorbingVertex {V E : Type*} [Fintype E] {G : LooplessMultigraph V E} {k : ℕ}
  {e0 : E} (T : TreeSequence G e0) (phi : PartialEdgeColoring E k) (v : V) : Prop :=
 v ∉ TreeSequenceVertexSet T ∧
  ∀ delta ∈ MissingColors G phi v,
   ∀ gamma ∈ TreeFreeColors phi T,
    gamma ≠ delta →
     ∃ u : V,
      u ∈ TreeSequenceVertexSet T ∧
       gamma ∈ MissingColors G phi u ∧
        Sum.inl u ∈ TwoColorComponent G phi gamma delta (Sum.inl v) ∧
         ∀ w ∈ TreeSequenceVertexSet T, gamma ∈ MissingColors G phi w → w = u

end GoldbergSeymour

end
