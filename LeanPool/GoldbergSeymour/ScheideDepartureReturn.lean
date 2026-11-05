/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Walk.Traversal
public import LeanPool.GoldbergSeymour.ScheideDefectiveChainPath

/-!
# Scheide Departure Return

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A defective chain's first outside vertex and later last return to the tree. -/
def ScheideDepartureReturn {V E : Type*} {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
  (T : TreeSequence G e0) {phi : PartialEdgeColoring E k} {alpha gamma : Fin k} {u z : V}
  {p : (TwoColorIncidenceGraph G phi alpha gamma).Walk (Sum.inl u) (Sum.inl z)}
  (i1 i2 : Fin (p.length + 1)) (v1 v2 : V) : Prop :=
 ScheideDefectiveChainPath T phi alpha gamma u z p ∧
  p.getVert i1.val = Sum.inl v1 ∧
   v1 ∉ TreeSequenceVertexSet T ∧
    (∀ r : Fin (p.length + 1),
      r.val < i1.val → ∀ w : V, p.getVert r.val = Sum.inl w → w ∈ TreeSequenceVertexSet T) ∧
     i1.val < i2.val ∧
      p.getVert i2.val = Sum.inl v2 ∧
       v2 ∈ TreeSequenceVertexSet T ∧
        ∀ r : Fin (p.length + 1),
         i2.val < r.val → ∀ w : V, p.getVert r.val = Sum.inl w → w ∉ TreeSequenceVertexSet T

end GoldbergSeymour

end
