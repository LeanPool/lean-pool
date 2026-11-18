/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.MissingColors
public import LeanPool.GoldbergSeymour.TreeSequence

/-!
# Tashkinov Tree

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A tree sequence whose later edges have colors missing at an earlier tree vertex. -/
def TashkinovTree {V E : Type*} [Fintype E] (G : LooplessMultigraph V E) {k : ℕ}
  (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0) : Prop :=
    ∀ j : Fin T.length, 1 ≤ j.val →
    ∃ i : Fin (j.val + 1),
    ∃ c : Fin k, phi (T.edge j) = some c ∧ c ∈ MissingColors G phi (T.vertex (Fin.castLT i
        (Nat.lt_trans i.isLt (Nat.succ_lt_succ j.isLt))))

end GoldbergSeymour

end
