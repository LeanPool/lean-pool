/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Basic.Finite.Sum
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import LeanPool.GoldbergSeymour.TwoColorMissingVertexNeighbors

/-!
# Missing Color Incidence Endpoint

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem MissingColorIncidenceEndpoint {V E : Type*}
     [Finite V] [Fintype E] (G : LooplessMultigraph V E) {k : ℕ} (phi : PartialEdgeColoring E k)
    (alpha beta : Fin k) (_ : alpha ≠ beta)
    (hproper : IsProperEdgeColoring G phi) (v : V)
    (hmissing : alpha ∈ MissingColors G phi v) :
    @SimpleGraph.degree _ (TwoColorIncidenceGraph G phi alpha beta) (Sum.inl v)
      (Fintype.ofFinite _) ≤ 1 := by
  classical
  let _ := Fintype.ofFinite V
  have neighbors := TwoColorMissingVertexNeighborsSubsingleton G phi hproper alpha beta v
    (Or.inl hmissing)
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_le_one.mpr
  intro first firstMember second secondMember
  exact neighbors
    (by simpa only [SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborSet] using firstMember)
    (by simpa only [SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborSet] using secondMember)

end GoldbergSeymour

end
