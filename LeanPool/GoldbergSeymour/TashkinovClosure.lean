/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ColoredVertexSetClosed
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequence

/-!
# Tashkinov Closure

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A tree reachable by augmentations whose vertex set is closed under the coloring. -/
def TashkinovClosure {V E : Type*} [Fintype V] [Fintype E] {G : LooplessMultigraph V E} {k : ℕ}
  {e0 : E} (phi : PartialEdgeColoring E k) (T T' : TreeSequence G e0) : Prop :=
 TashkinovAugmentationSequence phi T T' ∧ ColoredVertexSetClosed G phi (TreeSequenceVertexSet T')

end GoldbergSeymour

end
