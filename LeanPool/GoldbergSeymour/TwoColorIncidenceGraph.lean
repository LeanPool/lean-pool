/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.Incident
public import LeanPool.GoldbergSeymour.PartialEdgeColoring
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Tactic.Bound.Init

/-!
# Two Color Incidence Graph

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- The bipartite incidence graph on vertices and edges whose assigned color is one of the specified
pair.
-/
def TwoColorIncidenceGraph {V E : Type*} (G : LooplessMultigraph V E) {k : ℕ}
    (phi : PartialEdgeColoring E k) (alpha beta : Fin k) : SimpleGraph (Sum V E)
    where
  Adj x
    y :=
    match x, y with
    | Sum.inl v, Sum.inr e => Incident G v e ∧ (phi e = some alpha ∨ phi e = some beta)
    | Sum.inr e, Sum.inl v => Incident G v e ∧ (phi e = some alpha ∨ phi e = some beta)
    | _, _ => False
  symm.symm := by
    intro x y
    cases x <;> cases y <;> simp_all
  loopless.irrefl := by
    intro x
    cases x <;> simp

/-- Read colors directly from incidence adjacency when constructing paths. -/
theorem TwoColorIncidenceEdgeColors {V E : Type*} {G : LooplessMultigraph V E} {k : ℕ}
    {phi : PartialEdgeColoring E k} {alpha beta : Fin k} {edge : E} {vertex : Sum V E}
    (adjacent : (TwoColorIncidenceGraph G phi alpha beta).Adj (Sum.inr edge) vertex) :
    phi edge = some alpha ∨ phi edge = some beta := by
  cases vertex with
  | inl _ => exact adjacent.2
  | inr _ => exact False.elim adjacent

end GoldbergSeymour

end
