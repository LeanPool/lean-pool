/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.StableColoring

/-!
# Combined Stable Coloring

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Simultaneous stability on the ladder tree with stored colors and on the auxiliary closure. -/
def CombinedStableColoring {V E : Type*} [Fintype E] {G : LooplessMultigraph V E}
  {k : ℕ} {e0 : E} (Tn R : TreeSequence G e0) (D : Finset (Fin k))
  (phi sigma : PartialEdgeColoring E k) : Prop :=
 StableColoring Tn D phi sigma ∧ StableColoring R ∅ phi sigma

end GoldbergSeymour

end
