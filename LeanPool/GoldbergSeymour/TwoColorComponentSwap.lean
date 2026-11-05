/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TwoColorComponent

/-!
# Two Color Component Swap

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Interchange two colors on the selected incidence-graph component and preserve every other edge
color.
-/
noncomputable def TwoColorComponentSwap {V E : Type*} (G : LooplessMultigraph V E) {k : ℕ}
    (phi : PartialEdgeColoring E k) (alpha beta : Fin k) (z : Sum V E) : PartialEdgeColoring E k
        := by
  classical
  exact fun e =>
    if Sum.inr e ∈ TwoColorComponent G phi alpha beta z then
      if phi e = some alpha then some beta
      else if phi e = some beta then some alpha
      else phi e
    else phi e

/-- Completeness survives a component swap, including coincident swap colors. -/
theorem TwoColorComponentSwapColored {V E : Type*} {G : LooplessMultigraph V E} {k : ℕ}
    {phi : PartialEdgeColoring E k} {alpha beta : Fin k} {vertex : Sum V E} {edge : E}
    {color : Fin k} (colored : phi edge = some color) :
    ∃ newColor, TwoColorComponentSwap G phi alpha beta vertex edge = some newColor := by
  classical
  unfold TwoColorComponentSwap
  split
  · split
    · exact ⟨beta, rfl⟩
    · split
      · exact ⟨alpha, rfl⟩
      · exact ⟨color, colored⟩
  · exact ⟨color, colored⟩

end GoldbergSeymour

end
