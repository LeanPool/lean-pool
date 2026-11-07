/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TreeSequence

/-!
# Tash Tree Suffix Path

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open scoped Sym2

/-- After the specified positive position, each edge joins consecutive tree vertices. -/
def TashTreeSuffixPath {V E : Type*} (G : LooplessMultigraph V E) {e0 : E} (T : TreeSequence G e0)
  (q : ℕ) : Prop :=
 1 ≤ q ∧
  q ≤ T.length ∧
   ∀ i : Fin T.length, q ≤ i.val → G.ends (T.edge i) = s(T.vertex i.castSucc, T.vertex i.succ)

end GoldbergSeymour

end
