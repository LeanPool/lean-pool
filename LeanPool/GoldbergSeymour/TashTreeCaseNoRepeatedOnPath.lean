/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashTreeEarlyBetaNormalization
public import LeanPool.GoldbergSeymour.TashTreeGammaEpsilonSetup
public import LeanPool.GoldbergSeymour.TashTreeNoRepeatedDisjointReduction
public import LeanPool.GoldbergSeymour.TashTreeNoRepeatedIntersectionShortening

/-!
# Tash Tree Case No Repeated On Path

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem TashTreeCaseNoRepeatedOnPath {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T)
    (hq : 2 < TashTreePathIndex G T)
    (hbefore : TashTreePathIndex G T < T.length)
    (hnone : ¬ ∃ alpha : Fin k, ∃ i : Fin (T.length + 1),
      TashTreePathIndex G T ≤ i.val ∧ i.val < T.length ∧
      alpha ∈ MissingColors G phi (T.vertex i) ∧
      alpha ∈ MissingColors G phi (T.vertex (Fin.last T.length))) : False := by
  rcases TashTreeEarlyBetaNormalization G k e0 phi T hmin hq hbefore hnone with
    ⟨phi', beta, i, hmin', hi, hbeta, hbetaLast, hnone'⟩
  let q : Fin (T.length + 1) :=
    ⟨TashTreePathIndex G T, Nat.lt_succ_of_lt hbefore⟩
  have hsetup :
      ∃ (gamma epsilon : Fin k) (m : Fin (T.length + 1)),
        gamma ≠ beta ∧ epsilon ≠ gamma ∧
        gamma ∈ MissingColors G phi' (T.vertex q) ∧
        epsilon ∈ MissingColors G phi' (T.vertex m) ∧
        TreeColorUnusedThrough phi' T gamma q ∧
        TreeColorUnusedThrough phi' T epsilon q ∧
        m.val + 2 ≤ TashTreePathIndex G T := by
    simpa [q] using
      (TashTreeGammaEpsilonSetup G k e0 phi' T hmin' hq hbefore
        hnone' beta hbetaLast)
  rcases hsetup with
    ⟨gamma, epsilon, m, hgb, heg, hgamma, hepsilon,
      hgammaUnused, hepsilonUnused, hm⟩
  by_cases hepsilonLast : epsilon ∈
      MissingColors G phi' (T.vertex (Fin.last T.length))
  · exact TashTreeControlledRepeatedSuffixContradiction
      G k e0 phi' T hmin' hq hbefore m q
      (by change m.val < TashTreePathIndex G T; omega)
      (by change TashTreePathIndex G T < T.length; exact hbefore)
      (by change TashTreePathIndex G T ≤ TashTreePathIndex G T; exact le_rfl)
      epsilon gamma heg hepsilon hgamma
      hepsilonUnused hgammaUnused hepsilonLast
  · have heb : epsilon ≠ beta := by
      intro h
      apply hepsilonLast
      simpa [h] using hbetaLast
    by_cases hmeets : ∃ s : Fin (T.length + 1),
        s.val + 1 ≤ TashTreePathIndex G T ∧
        Sum.inl (T.vertex s) ∈
          TwoColorComponent G phi' epsilon beta
            (Sum.inl (T.vertex (Fin.last T.length)))
    · exact TashTreeNoRepeatedIntersectionShortening
        G k e0 phi' T hmin' hq hbefore beta epsilon heb i m hi hm
        hbeta hbetaLast hepsilon hmeets
    · exact TashTreeNoRepeatedDisjointReduction
        G k e0 phi' T hmin' hq hbefore beta gamma epsilon hgb heg heb
        i m hi hm hbeta hbetaLast hepsilon hgamma hgammaUnused
        hepsilonUnused (by
          intro s hs hmem
          exact hmeets ⟨s, hs, hmem⟩)

end GoldbergSeymour

end
