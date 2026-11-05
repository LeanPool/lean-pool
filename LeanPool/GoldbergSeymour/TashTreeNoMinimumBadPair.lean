/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashTreeCaseNoRepeatedOnPath
public import LeanPool.GoldbergSeymour.TashTreeCasePathIndexLast

/-!
# Tash Tree No Minimum Bad Pair

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem TashTreeNoMinimumBadPair {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T) : False := by
  classical
  have hq := TashTreeMinimumBadPathIndex G k e0 phi T hmin
  have hspec : TashTreeSuffixPath G T (TashTreePathIndex G T) := by
    unfold TashTreePathIndex
    exact Nat.find_spec _
  by_cases hlast : TashTreePathIndex G T = T.length
  · exact TashTreeCasePathIndexLast G k e0 phi T hmin hq hlast
  · have hbefore : TashTreePathIndex G T < T.length :=
      Nat.lt_of_le_of_ne hspec.2.1 hlast
    by_cases hrepeat : ∃ alpha : Fin k, ∃ i : Fin (T.length + 1),
        TashTreePathIndex G T ≤ i.val ∧ i.val < T.length ∧
        alpha ∈ MissingColors G phi (T.vertex i) ∧
        alpha ∈ MissingColors G phi (T.vertex (Fin.last T.length))
    · exact TashTreeCaseRepeatedOnPath G k e0 phi T hmin hq hbefore hrepeat
    · exact TashTreeCaseNoRepeatedOnPath G k e0 phi T hmin hq hbefore hrepeat

end GoldbergSeymour

end
