/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovSeriesStep

/-!
# Tashkinov Series

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Extension-series data certified at every step by the initial or extension rules. -/
structure TashkinovSeries {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k) where
  /-- The indexed data certified by the extension rules. -/
  data : TashkinovSeriesData G k rounds e0
  certified : ∀ i : Fin (rounds + 1), TashkinovSeriesStep G k rounds e0 input data i

end GoldbergSeymour

end
