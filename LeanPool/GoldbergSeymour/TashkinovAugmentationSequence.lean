/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovAugmentation

/-!
# Tashkinov Augmentation Sequence

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- The reflexive transitive closure of one-edge Tashkinov augmentations. -/
def TashkinovAugmentationSequence {V E : Type*} [Fintype E] {G : LooplessMultigraph V E}
  {k : ℕ} {e0 : E} (phi : PartialEdgeColoring E k) (T T' : TreeSequence G e0) : Prop :=
 Relation.ReflTransGen (TashkinovAugmentation phi) T T'

end GoldbergSeymour

end
