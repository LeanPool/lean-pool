/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashTreeRhoOneAdvance

/-!
# Tash Tree Rho One Iterate

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem TashTreeRhoOneIterate {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T)
    (hq : TashTreePathIndex G T = 1) (beta : Fin k)
    (i : Fin T.length)
    (hi : beta ∈ MissingColors G phi (T.vertex i.castSucc))
    (hlast : beta ∈ MissingColors G phi
      (T.vertex (Fin.last T.length))) :
    ∃ (psi : PartialEdgeColoring E k) (p : Fin T.length),
      p.val + 1 = T.length ∧
      TashTreeMinimumBadPair G k e0 psi T ∧
      beta ∈ MissingColors G psi (T.vertex p.castSucc) ∧
      beta ∈ MissingColors G psi
        (T.vertex (Fin.last T.length)) := by
  have iterate :
    ∀ (d : ℕ) (coloring : _) (j : Fin T.length), T.length - (j.val + 1) = d →
        TashTreeMinimumBadPair G k e0 coloring T → beta ∈ MissingColors G coloring (T.vertex
        j.castSucc) → beta ∈ MissingColors G coloring (T.vertex (Fin.last T.length)) →
    ∃ (nextColoring : _) (p : Fin T.length), p.val + 1 = T.length ∧ TashTreeMinimumBadPair G k e0
        nextColoring T ∧ beta ∈ MissingColors G nextColoring (T.vertex p.castSucc) ∧ beta ∈
        MissingColors G nextColoring (T.vertex (Fin.last T.length)) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d smaller =>
        intro coloring j hd hbad hj hlast'
        by_cases hnext : j.val + 1 < T.length
        · let nextIndex : Fin T.length := ⟨j.val + 1, hnext⟩
          obtain ⟨coloring', hbad', hj', hlast''⟩ :=
            TashTreeRhoOneAdvance G k e0 coloring T hbad hq beta j hnext hj hlast'
          have hnextval : nextIndex.val = j.val + 1 := by
            rfl
          have hsmaller : T.length - (nextIndex.val + 1) < d := by
            omega
          have htransport : beta ∈ MissingColors G coloring'
              (T.vertex nextIndex.castSucc) := by
            simpa [nextIndex, Fin.succ] using hj'
          exact smaller (T.length - (nextIndex.val + 1)) hsmaller coloring' nextIndex
            rfl hbad' htransport hlast''
        · have hterminal : j.val + 1 = T.length := by
            omega
          refine ⟨coloring, j, hterminal, hbad, hj, hlast'⟩
  exact iterate (T.length - (i.val + 1)) phi i rfl hmin hi hlast

end GoldbergSeymour

end
