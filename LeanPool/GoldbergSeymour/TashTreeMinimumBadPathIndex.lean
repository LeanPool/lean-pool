/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashTreeMinimumBadLengthAtLeastTwo

public import LeanPool.GoldbergSeymour.TashTreePathIndexTwoReplacement
public import LeanPool.GoldbergSeymour.TashTreeRhoOneIterate
public import LeanPool.GoldbergSeymour.TashTreeRhoOneRepeatedColor
public import LeanPool.GoldbergSeymour.TashTreeRhoOneTerminalReplacement

/-!
# Tash Tree Minimum Bad Path Index

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem TashTreeMinimumBadPathIndex {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T) :
    2 < TashTreePathIndex G T := by
  classical
  have hlen : 2 ≤ T.length :=
    TashTreeMinimumBadLengthAtLeastTwo G k e0 phi T hmin
  have hpath : TashTreeSuffixPath G T (TashTreePathIndex G T) := by
    unfold TashTreePathIndex
    exact Nat.find_spec _
  have hpos : 1 ≤ TashTreePathIndex G T := hpath.1
  by_contra hnot
  have hle : TashTreePathIndex G T ≤ 2 := by omega
  have hcases : TashTreePathIndex G T = 1 ∨
      TashTreePathIndex G T = 2 := by
    omega
  rcases hcases with hq | hq
  · obtain ⟨beta, i, hi, hlast⟩ :=
      TashTreeRhoOneRepeatedColor G k e0 phi T hmin hlen hq
    obtain ⟨psi, p, hp, hminPsi, hprev, hlastPsi⟩ :=
      TashTreeRhoOneIterate G k e0 phi T hmin hq beta i hi hlast
    obtain ⟨hpos, hprefix, delta, j, phiStar, hdelta, hj,
        hjMissing, hphiStar, hbad, hrank⟩ :=
      TashTreeRhoOneTerminalReplacement G k e0 psi T hminPsi hlen hq
        beta p hp hprev hlastPsi
    exact (hminPsi.2 hbad) hrank
  · obtain ⟨S, hdisplay, hbad, hrank⟩ :=
      TashTreePathIndexTwoReplacement G k e0 phi T hmin hlen hq
    exact (hmin.2 hbad) hrank

end GoldbergSeymour

end
