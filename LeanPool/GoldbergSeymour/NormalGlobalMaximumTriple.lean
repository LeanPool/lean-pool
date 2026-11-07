/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.GlobalMaximumTriple
public import LeanPool.GoldbergSeymour.TwoColorIncidenceGraph
public import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Normal Global Maximum Triple

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open scoped Sym2

/-- A maximum triple with a specified alternating trunk, missing colors and a closing path. -/
structure NormalGlobalMaximumTriple {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k)
    (T : TreeSequence G e0) where
  global : GlobalMaximumTriple G k e0 phi T
  /-- The number of vertices in the distinguished normal trunk. -/
  height : ℕ
  height_lower : 2 ≤ height
  height_upper : height ≤ T.length + 1
  /-- The distinguished color constrained by the accompanying missing-color conditions. -/
  alpha : Fin k
  /-- The second distinguished color in the alternating configuration. -/
  beta : Fin k
  alpha_missing : alpha ∈ MissingColors G phi (T.vertex ⟨0, Nat.zero_lt_succ T.length⟩)
  beta_missing : beta ∈ MissingColors G phi (T.vertex ⟨1, Nat.succ_lt_succ T.positive⟩)
  /-- The edge closing the alternating trunk. -/
  closingEdge : E
  /-- The index of the distinguished final trunk or departure vertex. -/
  lastIndex : Fin (T.length + 1)
  lastIndex_height : lastIndex.val + 1 = height
  closing_ends : G.ends closingEdge = s(T.vertex lastIndex, T.vertex ⟨0, Nat.zero_lt_succ T.length⟩)
  /-- The alternating path joining the trunk endpoints. -/
  closingPath :
    (TwoColorIncidenceGraph G phi alpha beta).Walk
      (Sum.inl (T.vertex ⟨1, Nat.succ_lt_succ T.positive⟩))
      (Sum.inl (T.vertex ⟨0, Nat.zero_lt_succ T.length⟩))
  closingPath_isPath : closingPath.IsPath
  closingPath_length : closingPath.length = 2 * (height - 1)
  closingPath_vertices :
    ∀ v : V,
      Sum.inl v ∈ closingPath.support ↔ ∃ i : Fin height, v = T.vertex (Fin.castLE height_upper i)
  closingPath_edges :
    ∀ f : E,
      Sum.inr f ∈ closingPath.support ↔
        f = closingEdge ∨ ∃ j : Fin T.length, 1 ≤ j.val ∧ j.val + 2 ≤ height ∧ f = T.edge j
  trunk_edge_ends :
    ∀ j : Fin T.length, 1 ≤ j.val → j.val + 2 ≤ height → G.ends (T.edge j) = s(T.vertex ⟨j.val,
        Nat.lt_succ_of_lt j.isLt⟩, T.vertex j.succ)

end GoldbergSeymour

end
