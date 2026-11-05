/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TreeIncidentEdge
public import LeanPool.GoldbergSeymour.PartialEdgeColoring

/-!
# Outside Tree Color Swap

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Swap two colors only on edges incident to no vertex of the tree. -/
noncomputable def OutsideTreeColorSwap {V E : Type*} {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (T : TreeSequence G e0) (phi : PartialEdgeColoring E k) (alpha beta : Fin k) :
    PartialEdgeColoring E k := by
  classical
  exact fun e =>
    if TreeIncidentEdge T e then phi e
    else if phi e = some alpha then some beta
    else if phi e = some beta then some alpha
    else phi e

end GoldbergSeymour

end
