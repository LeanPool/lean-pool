/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet
public import LeanPool.GoldbergSeymour.TreeVertexOrder

/-!
# Tree Vertices Before

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- The tree vertices occurring strictly before the specified vertex. -/
noncomputable def TreeVerticesBefore {V E : Type*} {G : LooplessMultigraph V E} {e0 : E}
    (T : TreeSequence G e0) (v : V) (_hv : v ∈ TreeSequenceVertexSet T) : Finset V := by
  classical
  exact (TreeSequenceVertexSet T).filter fun w => TreeVertexOrder T w v

end GoldbergSeymour

end
