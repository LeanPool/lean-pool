/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Data.Fintype.Fin

public import LeanPool.GoldbergSeymour.TreeSequence

/-!
# Tree Sequence Vertex Set

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- The finite set of vertices occurring in the tree sequence. -/
noncomputable def TreeSequenceVertexSet {V E : Type*} {G : LooplessMultigraph V E} {e0 : E}
    (T : TreeSequence G e0) : Finset V := by classical exact Finset.univ.image T.vertex

end GoldbergSeymour

end
