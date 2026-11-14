/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovTree
public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet

/-!
# Fixed Pair Maximal Tashkinov Tree

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A Tashkinov tree maximal by vertex-set inclusion for the fixed uncolored edge and coloring. -/
def FixedPairMaximalTashkinovTree {V E : Type*} [Fintype E] (G : LooplessMultigraph V E)
  {k : ℕ} (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0) : Prop :=
 TashkinovTree G e0 phi T ∧
  ∀ S : TreeSequence G e0,
   TashkinovTree G e0 phi S →
    TreeSequenceVertexSet T ⊆ TreeSequenceVertexSet S →
     TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet T

end GoldbergSeymour

end
