/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.DrossFractionalTriangleDecomposition.Internal.NoHeavyTriangle
import Aesop

/-!
# Geometry of a peeled high-degree triangle

The three deleted pairs are genuine graph edges, are pairwise distinct, and
deleting them lowers every degree by at most two.
-/

namespace LeanPool.DrossFractionalTriangleDecomposition

open SimpleGraph Finset

variable {V : Type*}

public theorem heavy_triangle_vertices_distinct (G : SimpleGraph V) {u v w : V}
    (huv : G.Adj u v) (huw : G.Adj u w) (hvw : G.Adj v w) :
    u ≠ v ∧ u ≠ w ∧ v ≠ w :=
  ⟨huv.ne, huw.ne, hvw.ne⟩

public theorem triEdges_heavy_triangle_subset (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {u v w : V} (huv : G.Adj u v) (huw : G.Adj u w) (hvw : G.Adj v w) :
    triEdges {u, v, w} ⊆ G.edgeFinset := by
  simp only [subset_iff, Sym2.forall, triEdges, mem_filter, mem_sym2_iff,
    mem_insert, mem_singleton, mem_edgeFinset]
  rintro a b ⟨hab, hdiag⟩
  have ha : a = u ∨ a = v ∨ a = w := hab a (by simp)
  have hb : b = u ∨ b = v ∨ b = w := hab b (by simp)
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    simp_all [SimpleGraph.mem_edgeSet, G.adj_comm]

public theorem triEdges_heavy_triangle_card (G : SimpleGraph V) [DecidableEq V] {u v w : V}
    (huv : G.Adj u v) (huw : G.Adj u w) (hvw : G.Adj v w) :
    #(triEdges {u, v, w}) = 3 := by
  have hne := heavy_triangle_vertices_distinct G huv huw hvw
  have heq : triEdges {u, v, w} = {s(u, v), s(u, w), s(v, w)} := by
    ext e
    induction e using Sym2.inductionOn with
    | _ a b =>
      simp only [triEdges, mem_filter, mem_sym2_iff, mem_insert, mem_singleton,
        Sym2.mk_isDiag_iff, Sym2.eq_iff]
      aesop
  rw [heq]
  simp [hne.1, hne.2.1, hne.2.2]

end LeanPool.DrossFractionalTriangleDecomposition
