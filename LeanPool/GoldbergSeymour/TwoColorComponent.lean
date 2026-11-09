/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TwoColorIncidenceGraph
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Two Color Component

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- The connected component in the incidence graph restricted to the two specified colors. -/
def TwoColorComponent {V E : Type*} (G : LooplessMultigraph V E) {k : ℕ}
    (phi : PartialEdgeColoring E k) (alpha beta : Fin k) (z : Sum V E) : Set (Sum V E) :=
  (TwoColorIncidenceGraph G phi alpha beta).connectedComponentMk z

/-- Every edge in a vertex-rooted component has one of the two selected colors. -/
theorem TwoColorComponent.edge_colors {V E : Type*} {G : LooplessMultigraph V E} {k : ℕ}
    {phi : PartialEdgeColoring E k} {alpha beta : Fin k} {vertex : V} {edge : E}
    (member : Sum.inr edge ∈ TwoColorComponent G phi alpha beta (Sum.inl vertex)) :
    phi edge = some alpha ∨ phi edge = some beta := by
  have support : Sum.inr edge ∈ (TwoColorIncidenceGraph G phi alpha beta).support :=
    SimpleGraph.mem_support_of_reachable (by simp)
      (SimpleGraph.ConnectedComponent.eq.mp member)
  obtain ⟨neighbor, adjacent⟩ :=
    (TwoColorIncidenceGraph G phi alpha beta).mem_support.mp support
  exact TwoColorIncidenceEdgeColors adjacent

end GoldbergSeymour

end
