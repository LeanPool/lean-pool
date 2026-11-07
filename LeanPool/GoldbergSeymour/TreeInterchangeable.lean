/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet
public import LeanPool.GoldbergSeymour.TwoColorPathComponent

/-!
# Tree Interchangeable

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Every two-color path component meeting the tree is the same component. -/
def TreeInterchangeable {V E : Type*} (G : LooplessMultigraph V E) {k : ℕ} {e0 : E}
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k) (alpha beta : Fin k) : Prop :=
 ∀ z w : Sum V E,
  TwoColorPathComponent G phi alpha beta z →
   TwoColorPathComponent G phi alpha beta w →
    (∃ v ∈ TreeSequenceVertexSet T, Sum.inl v ∈ TwoColorComponent G phi alpha beta z) →
     (∃ v ∈ TreeSequenceVertexSet T, Sum.inl v ∈ TwoColorComponent G phi alpha beta w) →
      TwoColorComponent G phi alpha beta z = TwoColorComponent G phi alpha beta w

end GoldbergSeymour

end
