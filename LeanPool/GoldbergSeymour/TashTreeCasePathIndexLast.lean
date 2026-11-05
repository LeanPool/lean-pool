/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashTreeMinimumBadPathIndex

public import LeanPool.GoldbergSeymour.TashTreeLastIndexDeletion
public import LeanPool.GoldbergSeymour.TashTreeLastIndexFirstNormalForm
public import LeanPool.GoldbergSeymour.TashTreeLastIndexSecondNormalForm
public import LeanPool.GoldbergSeymour.TashTreeLastIndexThirdNormalForm

/-!
# Tash Tree Case Path Index Last

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem TashTreeCasePathIndexLast {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T)
    (hq : 2 < TashTreePathIndex G T)
    (hlast : TashTreePathIndex G T = T.length) : False := by
  obtain ⟨phi₁, beta₁, j₁, hmin₁, hj₁, hbeta₁j, hbeta₁last,
    hbeta₁unused⟩ :=
    TashTreeLastIndexFirstNormalForm G k e0 phi T hmin hq hlast
  obtain ⟨phi₂, gamma, r, p, hr, hp, hmin₂, hrgamma, hpgamma⟩ :=
    TashTreeLastIndexSecondNormalForm G k e0 phi₁ T hmin₁ hq hlast
      beta₁ j₁ hj₁ hbeta₁j hbeta₁last hbeta₁unused
  obtain ⟨phi₃, beta₃, j₃, hmin₃, hrgamma₃, hpgamma₃, hj₃,
    hbeta₃j, hbeta₃last⟩ :=
    TashTreeLastIndexThirdNormalForm G k e0 phi₂ T hmin₂ hq hlast
      gamma r p hr hp hrgamma hpgamma
  obtain ⟨P, S, s, hPlength, hPT, hSlength, hPS, hs, hsedge,
    hsvertex, hbadS, hrankS⟩ :=
    TashTreeLastIndexDeletion G k e0 phi₃ T hmin₃ hq hlast
      gamma beta₃ r p j₃ hr hp hj₃ hrgamma₃ hpgamma₃
      hbeta₃j hbeta₃last
  exact (hmin₃.2 hbadS) hrankS

end GoldbergSeymour

end
