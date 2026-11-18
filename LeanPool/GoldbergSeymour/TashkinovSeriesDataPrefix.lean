/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovSeriesData

/-!
# Tashkinov Series Data Prefix

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Restrict every component of the series data to the specified initial number of rounds. -/
def TashkinovSeriesDataPrefix {V E : Type*} {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E}
    (m : ℕ) (hm : m ≤ rounds) (data : TashkinovSeriesData G k rounds e0) :
    TashkinovSeriesData G k m e0 :=
  { tree := fun i => data.tree (Fin.castLE (by omega) i)
    coloring := fun i => data.coloring (Fin.castLE (by omega) i)
    stored := fun i => data.stored (Fin.castLE (by omega) i)
    connectingEdges := fun i => data.connectingEdges (Fin.castLE (by omega) i)
    kind := fun i => data.kind (Fin.castLE (by omega) i)
    chosenVertex := fun i => data.chosenVertex (Fin.castLE (by omega) i)
    outsideVertex := fun i => data.outsideVertex (Fin.castLE (by omega) i)
    delta := fun i => data.delta (Fin.castLE (by omega) i)
    gamma := fun i => data.gamma (Fin.castLE (by omega) i) }

end GoldbergSeymour

end
