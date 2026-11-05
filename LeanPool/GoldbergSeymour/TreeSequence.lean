/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.LooplessMultigraph

/-!
# Tree Sequence

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open scoped Sym2

/-- An ordered tree with distinct vertices and edges, a distinguished first edge and an earlier
attachment for each edge.
-/
structure TreeSequence {V E : Type*} (G : LooplessMultigraph V E) (e0 : E) where
  /-- The positive number of edges in the tree sequence. -/
  length : ℕ
  positive : 1 ≤ length
  /-- The selected vertex, or ordered vertices when the field is indexed. -/
  vertex : Fin (length + 1) → V
  /-- The selected edge, or ordered edges when the field is indexed. -/
  edge : Fin length → E
  vertex_injective : Function.Injective vertex
  edge_injective : Function.Injective edge
  first_edge : edge ⟨0, positive⟩ = e0
  attaches :
    ∀ j : Fin length,
      ∃ i : Fin (j.val + 1),
        G.ends (edge j) =
          s(vertex j.succ, vertex (Fin.castLT i (Nat.lt_trans i.isLt (Nat.succ_lt_succ j.isLt))))

end GoldbergSeymour

end
