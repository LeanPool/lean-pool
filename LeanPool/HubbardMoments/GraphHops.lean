/-
Copyright (c) 2026 Daniel Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Souza
-/
module

-- Adapted for Lean Pool.

public import Mathlib.Combinatorics.SimpleGraph.Density

/-! # Directed edges and available hops on a finite graph -/

@[expose] public section

namespace HubbardMoments

open Finset

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The directed edges of `G`: ordered pairs of adjacent vertices. -/
def arcs : Finset (V × V) := G.interedges univ univ

@[simp]
theorem mem_arcs {p : V × V} : p ∈ arcs G ↔ G.Adj p.1 p.2 := by
  simp [arcs, G.mem_interedges_iff]

/-- Reversing the orientation of every arc leaves the sum unchanged. -/
theorem sum_arcs_swap {R : Type*} [AddCommMonoid R] (weight : V × V → R) :
    ∑ p ∈ arcs G, weight p.swap = ∑ p ∈ arcs G, weight p :=
  sum_equiv (Equiv.prodComm V V) (fun p ↦ by simp [G.adj_comm]) fun _ _ ↦ rfl

/-- The hops out of a configuration `S` (the set of occupied sites): directed edges from
an occupied site to an empty one. Their number is the `M(S)` of the paper, and the
diagonal element of `H∞²` at `S` is `λ² M(S)`. -/
def hops [DecidableEq V] (S : Finset V) : Finset (V × V) :=
  G.interedges S Sᶜ

theorem mem_hops [DecidableEq V] {S : Finset V} {p : V × V} :
    p ∈ hops G S ↔ G.Adj p.1 p.2 ∧ p.1 ∈ S ∧ p.2 ∉ S := by
  simp [hops, G.mem_interedges_iff, and_comm, and_assoc]

theorem hops_eq_filter [DecidableEq V] (S : Finset V) :
    hops G S = (arcs G).filter (fun p => p.1 ∈ S ∧ p.2 ∉ S) := by
  ext p
  simp [mem_hops]

end HubbardMoments
