/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.DefectiveColors
public import LeanPool.GoldbergSeymour.MissingColors
public import LeanPool.GoldbergSeymour.ScheideDefectiveChainPath

/-!
# Scheide Exit Vertex

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A tree vertex that is the last tree vertex on an appropriate defective-color component path. -/
def ScheideExitVertex {V E : Type*} [Fintype V] [Fintype E] {G : LooplessMultigraph V E} {k : ℕ}
  {e0 : E} (T : TreeSequence G e0) (phi : PartialEdgeColoring E k) (v : V) : Prop :=
 ∃ (u : V) (gamma delta : Fin k),
  u ∈ TreeSequenceVertexSet T ∧
   gamma ∈ MissingColors G phi u ∧
    delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T) ∧
     ∃ (z : V) (p : (TwoColorIncidenceGraph G phi delta gamma).Walk (Sum.inl u) (Sum.inl z)),
      ScheideDefectiveChainPath T phi delta gamma u z p ∧
       ∃ i : Fin (p.length + 1),
        p.getVert i.val = Sum.inl v ∧
         v ∈ TreeSequenceVertexSet T ∧
          ∀ r : Fin (p.length + 1),
           i.val < r.val → ∀ w : V, p.getVert r.val = Sum.inl w → w ∉ TreeSequenceVertexSet T

end GoldbergSeymour

end
