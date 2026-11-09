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

/-- An edge different from the root of its component has one of the selected colors. -/
theorem TwoColorComponent.edge_colors_of_ne {V E : Type*} {G : LooplessMultigraph V E} {k : ℕ}
    {phi : PartialEdgeColoring E k} {alpha beta : Fin k} {root : Sum V E} {edge : E}
    (member : Sum.inr edge ∈ TwoColorComponent G phi alpha beta root)
    (different : Sum.inr edge ≠ root) :
    phi edge = some alpha ∨ phi edge = some beta := by
  have support : Sum.inr edge ∈ (TwoColorIncidenceGraph G phi alpha beta).support :=
    SimpleGraph.mem_support_of_reachable different (SimpleGraph.ConnectedComponent.eq.mp member)
  obtain ⟨neighbor, adjacent⟩ :=
    (TwoColorIncidenceGraph G phi alpha beta).mem_support.mp support
  exact TwoColorIncidenceEdgeColors adjacent

/-- Every edge in a vertex-rooted component has one of the two selected colors. -/
theorem TwoColorComponent.edge_colors {V E : Type*} {G : LooplessMultigraph V E} {k : ℕ}
    {phi : PartialEdgeColoring E k} {alpha beta : Fin k} {vertex : V} {edge : E}
    (member : Sum.inr edge ∈ TwoColorComponent G phi alpha beta (Sum.inl vertex)) :
    phi edge = some alpha ∨ phi edge = some beta := by
  exact TwoColorComponent.edge_colors_of_ne member (by simp)

/-- Each vertex incident to a component edge belongs to the same vertex-rooted component. -/
theorem TwoColorComponent.vertex_mem_of_incident {V E : Type*}
    {G : LooplessMultigraph V E} {k : ℕ} {phi : PartialEdgeColoring E k}
    {alpha beta : Fin k} {root vertex : V} {edge : E}
    (member : Sum.inr edge ∈ TwoColorComponent G phi alpha beta (Sum.inl root))
    (incident : Incident G vertex edge) :
    Sum.inl vertex ∈ TwoColorComponent G phi alpha beta (Sum.inl root) := by
  exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    (show (TwoColorIncidenceGraph G phi alpha beta).Adj (Sum.inl vertex) (Sum.inr edge) from
      ⟨incident, TwoColorComponent.edge_colors member⟩)).trans member

/-- A vertex-rooted component containing an edge has a colored edge incident to its root. -/
theorem TwoColorComponent.exists_colored_incident {V E : Type*}
    {G : LooplessMultigraph V E} {k : ℕ} {phi : PartialEdgeColoring E k}
    {alpha beta : Fin k} {root : V} {edge : E}
    (member : Sum.inr edge ∈ TwoColorComponent G phi alpha beta (Sum.inl root)) :
    ∃ candidate : E, Incident G root candidate ∧
      (phi candidate = some alpha ∨ phi candidate = some beta) := by
  have support : Sum.inl root ∈ (TwoColorIncidenceGraph G phi alpha beta).support :=
    SimpleGraph.mem_support_of_reachable (by simp)
      (SimpleGraph.ConnectedComponent.eq.mp member).symm
  obtain ⟨node, adjacent⟩ := (TwoColorIncidenceGraph G phi alpha beta).mem_support.mp support
  cases node with
  | inl _ => exact False.elim adjacent
  | inr candidate => exact ⟨candidate, adjacent⟩

end GoldbergSeymour

end
