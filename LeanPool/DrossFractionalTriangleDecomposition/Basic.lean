/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Fractional triangle decompositions

The edge weights in the decomposition equation are exactly one. This is the public
statement model for the Dross threshold; auxiliary flow and cut structures remain internal.
-/

namespace LeanPool.DrossFractionalTriangleDecomposition

open SimpleGraph Finset

variable {V : Type*} [DecidableEq V]

/-- The non-loop edges spanned by a finite set of vertices. -/
@[expose] public def triEdges (t : Finset V) : Finset (Sym2 V) :=
  t.sym2.filter (fun e => ¬ e.IsDiag)

/-- A triangle has three edges. -/
public theorem triEdges_card_of_isNClique (G : SimpleGraph V)
    {t : Finset V} (ht : G.IsNClique 3 t) : (triEdges t).card = 3 := by
  rw [triEdges, Finset.sym2_eq_image, Sym2.filter_image_mk_not_isDiag,
    Sym2.card_image_offDiag]
  simp [SimpleGraph.IsNClique.card_eq ht]

variable [Fintype V]

/-- Every edge of a graph triangle belongs to the graph. -/
public theorem triEdges_subset_edgeFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    {t : Finset V} (ht : t ∈ G.cliqueFinset 3) : triEdges t ⊆ G.edgeFinset := by
  rw [mem_cliqueFinset_iff] at ht
  intro e he
  unfold triEdges at he
  rw [Finset.mem_filter] at he
  obtain ⟨hmem, hdiag⟩ := he
  induction e using Sym2.ind with
  | _ a b =>
    rw [Finset.mk_mem_sym2_iff] at hmem
    rw [Sym2.mk_isDiag_iff] at hdiag
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact ht.1 hmem.1 hmem.2 hdiag

/-- Nonnegative weights on triangles which give every graph edge total weight one. -/
@[expose] public def FractionalTriangleDecomp (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ w : Finset V → ℝ, (∀ t, 0 ≤ w t) ∧
    ∀ e ∈ G.edgeFinset,
      (∑ t ∈ G.cliqueFinset 3, if e ∈ triEdges t then w t else 0) = 1

end LeanPool.DrossFractionalTriangleDecomposition
