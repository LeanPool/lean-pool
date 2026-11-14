/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashTreeSuffixAdvance

/-!
# Tash Tree Suffix Iterate

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem TashTreeSuffixIterate {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T)
    (beta : Fin k) (i : Fin T.length)
    (hiSuffix : TashTreePathIndex G T ≤ i.val)
    (hi : beta ∈ MissingColors G phi (T.vertex i.castSucc))
    (hlast : beta ∈ MissingColors G phi
      (T.vertex (Fin.last T.length))) :
    ∃ (psi : PartialEdgeColoring E k) (p : Fin T.length),
      p.val + 1 = T.length ∧
      TashTreePathIndex G T ≤ p.val ∧
      TashTreeMinimumBadPair G k e0 psi T ∧
      beta ∈ MissingColors G psi (T.vertex p.castSucc) ∧
      beta ∈ MissingColors G psi
        (T.vertex (Fin.last T.length)) := by
  have iterate :
    ∀ (d : ℕ) (coloring : _) (j : Fin T.length), T.length - (j.val + 1) = d → TashTreePathIndex G
        T ≤ j.val → TashTreeMinimumBadPair G k e0 coloring T → beta ∈ MissingColors G coloring
        (T.vertex j.castSucc) → beta ∈ MissingColors G coloring (T.vertex (Fin.last T.length)) →
    ∃ (nextColoring : _) (p : Fin T.length), p.val + 1 = T.length ∧ TashTreePathIndex G T ≤ p.val
        ∧ TashTreeMinimumBadPair G k e0 nextColoring T ∧ beta ∈ MissingColors G nextColoring
        (T.vertex p.castSucc) ∧ beta ∈ MissingColors G nextColoring (T.vertex (Fin.last T.length))
  := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d smaller =>
        intro coloring j hd hjSuffix hbad hj hlast'
        by_cases hnext : j.val + 1 < T.length
        · let nextIndex : Fin T.length := ⟨j.val + 1, hnext⟩
          obtain ⟨coloring', hbad', hj', hlast''⟩ :=
            TashTreeSuffixAdvance G k e0 coloring T hbad beta j
              (Or.inr hjSuffix) hnext hj hlast'
          have hnextval : nextIndex.val = j.val + 1 := by
            rfl
          have hsmaller : T.length - (nextIndex.val + 1) < d := by
            omega
          have hnextSuffix : TashTreePathIndex G T ≤ nextIndex.val := by
            rw [hnextval]
            omega
          have htransport : beta ∈ MissingColors G coloring'
              (T.vertex nextIndex.castSucc) := by
            simpa [nextIndex, Fin.succ] using hj'
          exact smaller (T.length - (nextIndex.val + 1)) hsmaller
            coloring' nextIndex rfl hnextSuffix hbad' htransport hlast''
        · have hterminal : j.val + 1 = T.length := by
            omega
          refine ⟨coloring, j, hterminal, hjSuffix, hbad, hj, hlast'⟩
  exact iterate (T.length - (i.val + 1)) phi i rfl hiSuffix hmin hi hlast

end GoldbergSeymour

end
