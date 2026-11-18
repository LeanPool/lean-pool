/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TreeExitPath

/-!
# Tree Exit

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- An outside-to-inside two-color path ending at the given tree vertex and meeting the tree only
there.
-/
def TreeExit {V E : Type*} [Fintype E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k) (alpha beta : Fin k) (v : V) : Prop :=
 ∃ (u : V) (p : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl u) (Sum.inl v)),
  TreeExitPath T phi alpha beta u v p

end GoldbergSeymour

end
