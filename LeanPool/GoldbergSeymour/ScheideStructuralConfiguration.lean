/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.GlobalMaximumTriple

public import LeanPool.GoldbergSeymour.ScheideExitVertices

/-!
# Scheide Structural Configuration

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open scoped Sym2

/-- The base and paired blocks of a global maximum tree, with their colors, positions and exit
coverage.
-/
structure ScheideStructuralConfiguration {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k)
    (T : TreeSequence G e0) where
  /-- The number of base vertices in the structural decomposition. -/
  p : ℕ
  /-- The number of paired structural blocks. -/
  s : ℕ
  p_ge_two : 2 ≤ p
  /-- The auxiliary color or color family used by this configuration. -/
  gamma : Fin s → Fin k
  gamma_injective : Function.Injective gamma
  /-- The ordered base vertices. -/
  y : Fin p → V
  /-- The ordered edges between the base vertices. -/
  baseEdge : Fin (p - 1) → E
  /-- The two vertices in each structural block. -/
  blockVertex : Fin s → Fin 2 → V
  /-- The two edges in each structural block. -/
  blockEdge : Fin s → Fin 2 → E
  length_eq : T.length + 1 = p + 2 * s
  base_vertex_position : ∀ i : Fin p, T.vertex ⟨i.val, by omega⟩ = y i
  block_vertex_position :
    ∀ (i : Fin s) (j : Fin 2), T.vertex ⟨p + 2 * i.val + j.val, by omega⟩ = blockVertex i j
  base_edge_position : ∀ i : Fin (p - 1), T.edge ⟨i.val, by omega⟩ = baseEdge i
  block_edge_position :
    ∀ (i : Fin s) (j : Fin 2), T.edge ⟨p - 1 + 2 * i.val + j.val, by omega⟩ = blockEdge i j
  block_attaches_to_base :
    ∀ (i : Fin s) (j : Fin 2), ∃ q : Fin p, G.ends (blockEdge i j) = s(y q, blockVertex i j)
  block_color : ∀ (i : Fin s) (j : Fin 2), phi (blockEdge i j) = some (gamma i)
  block_color_missing_on_base : ∀ i : Fin s, ∃ q : Fin p, gamma i ∈ MissingColors G phi (y q)
  initial_nonfirst_avoids_blocks :
    ∀ i : Fin (p - 1), 1 ≤ i.val → ∀ c : Fin k, phi (baseEdge i) = some c → ∀ r : Fin s, c ≠ gamma r
  exit_covered : ∀ v ∈ ScheideExitVertices T phi, ∃ i : Fin s, gamma i ∈ MissingColors G phi v
  no_isolated : ∀ v : V, ∃ e : E, Incident G v e
  globally_maximum : GlobalMaximumTriple G k e0 phi T

end GoldbergSeymour

end
