/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashTreeSuffixTerminalReplacement

/-!
# Tash Tree Rho One Terminal Replacement

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem TashTreeRhoOneTerminalReplacement {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T)
    (hlen : 2 ≤ T.length) (hq : TashTreePathIndex G T = 1)
    (beta : Fin k) (p : Fin T.length) (hp : p.val + 1 = T.length)
    (hprev : beta ∈ MissingColors G phi (T.vertex p.castSucc))
    (hlast : beta ∈ MissingColors G phi
      (T.vertex (Fin.last T.length))) :
    ∃ (hpos : 1 ≤ p.val) (hle : p.val ≤ T.length)
      (delta : Fin k) (j : Fin (p.val + 1))
      (phiStar : PartialEdgeColoring E k),
      phi (T.edge p) = some delta ∧
      j.val < p.val ∧
      delta ∈ MissingColors G phi
        (T.vertex (Fin.castLT j (by omega))) ∧
      phiStar = (fun e => if e = T.edge p then some beta else phi e) ∧
      TashTreeBadPair G k e0 phiStar
        (TreeSequencePrefix T p.val hpos hle) ∧
      TashTreeRankLess G (TreeSequencePrefix T p.val hpos hle) T := by
  have hbound : TashTreePathIndex G T ≤ p.val := by
    omega
  exact TashTreeSuffixTerminalReplacement G k e0 phi T hmin hlen beta p
    hbound hp hprev hlast

end GoldbergSeymour

end
