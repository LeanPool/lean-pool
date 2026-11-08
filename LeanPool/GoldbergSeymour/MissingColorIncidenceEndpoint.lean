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

/-- A missing color bounds the incidence degree, for any enumeration of the neighbors. -/
theorem TwoColorMissingVertexDegreeAtMostOne {V E : Type*} [Fintype E]
    (G : LooplessMultigraph V E) {k : ℕ} (phi : PartialEdgeColoring E k)
    (hproper : IsProperEdgeColoring G phi) (alpha beta : Fin k) (v : V)
    [neighborEnumeration :
      Fintype ((TwoColorIncidenceGraph G phi alpha beta).neighborSet (Sum.inl v))]
    (hmissing : alpha ∈ MissingColors G phi v ∨ beta ∈ MissingColors G phi v) :
    (TwoColorIncidenceGraph G phi alpha beta).degree (Sum.inl v) ≤ 1 := by
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  apply Fintype.card_le_one_iff.mpr
  intro first second
  exact Subtype.ext (TwoColorMissingVertexNeighborsSubsingleton G phi hproper alpha beta v
    hmissing first.property second.property)

theorem MissingColorIncidenceEndpoint {V E : Type*}
     [Finite V] [Fintype E] (G : LooplessMultigraph V E) {k : ℕ} (phi : PartialEdgeColoring E k)
    (alpha beta : Fin k) (_ : alpha ≠ beta)
    (hproper : IsProperEdgeColoring G phi) (v : V)
    (hmissing : alpha ∈ MissingColors G phi v) :
    @SimpleGraph.degree _ (TwoColorIncidenceGraph G phi alpha beta) (Sum.inl v)
      (Fintype.ofFinite _) ≤ 1 := by
  classical
  exact TwoColorMissingVertexDegreeAtMostOne G phi hproper alpha beta v
    (neighborEnumeration := Fintype.ofFinite _) (Or.inl hmissing)

end GoldbergSeymour

end
