/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashTreeSuffixAdvance

/-!
# Tash Tree Rho One Advance

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem TashTreeRhoOneAdvance {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T)
    (hq : TashTreePathIndex G T = 1) (beta : Fin k)
    (i : Fin T.length) (hiNext : i.val + 1 < T.length)
    (hi : beta ∈ MissingColors G phi (T.vertex i.castSucc))
    (hlast : beta ∈ MissingColors G phi
      (T.vertex (Fin.last T.length))) :
    ∃ phi' : PartialEdgeColoring E k,
      TashTreeMinimumBadPair G k e0 phi' T ∧
      beta ∈ MissingColors G phi' (T.vertex i.succ) ∧
      beta ∈ MissingColors G phi'
        (T.vertex (Fin.last T.length)) := by
  apply TashTreeSuffixAdvance G k e0 phi T hmin beta i
  · by_cases hiZero : i.val = 0
    · exact Or.inl hiZero
    · exact Or.inr (by omega)
  · exact hiNext
  · exact hi
  · exact hlast

end GoldbergSeymour

end
