/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.DrossFractionalTriangleDecomposition.Internal.ExactFlow
import Mathlib.Tactic.Positivity

/-!
# Elementary dense-graph cases

Uniform triangle counts yield a fractional decomposition by constant weights.
The minimum-degree assumption also ensures every edge belongs to a triangle.
-/

namespace LeanPool.DrossFractionalTriangleDecomposition

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- If all edges lie in exactly the same positive number of triangles,
the constant reciprocal weight is a fractional triangle decomposition. -/
public theorem fractional_of_constant_triThrough (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : ℕ) (hT : 0 < T) (hconst : ∀ e ∈ G.edgeFinset, triThrough G e = T) :
    FractionalTriangleDecomp G := by
  refine ⟨fun _ => 1 / (T : ℝ), fun _ => by positivity, ?_⟩
  intro e he
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  change (triThrough G e : ℝ) * (1 / (T : ℝ)) = 1
  rw [hconst e he]
  have : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  field_simp

/-- Under the nine-tenths minimum-degree hypothesis, every nonempty graph
contains a triangle. -/
public theorem exists_triangle_of_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : 9 * Fintype.card V ≤ 10 * G.minDegree) (hm : G.edgeFinset.Nonempty) :
    0 < (G.cliqueFinset 3).card := by
  rw [Finset.card_pos]
  obtain ⟨e, he⟩ := hm
  rw [SimpleGraph.mem_edgeFinset] at he
  induction e using Sym2.inductionOn with
  | hf u v =>
    have huv : G.Adj u v := he
    have hcardV : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨u⟩
    have hdu : 9 * Fintype.card V ≤ 10 * G.degree u :=
      le_trans h (by simpa using Nat.mul_le_mul_left 10 (G.minDegree_le_degree u))
    have hdv : 9 * Fintype.card V ≤ 10 * G.degree v :=
      le_trans h (by simpa using Nat.mul_le_mul_left 10 (G.minDegree_le_degree v))
    have hinter : (G.neighborFinset u ∩ G.neighborFinset v).Nonempty := by
      rw [← Finset.card_pos]
      have hun : (G.neighborFinset u ∪ G.neighborFinset v).card ≤ Fintype.card V :=
        le_trans (Finset.card_le_univ _) (le_of_eq Finset.card_univ)
      have hsum := Finset.card_union_add_card_inter (G.neighborFinset u) (G.neighborFinset v)
      rw [G.card_neighborFinset_eq_degree, G.card_neighborFinset_eq_degree] at hsum
      omega
    obtain ⟨w, hw⟩ := hinter
    rw [Finset.mem_inter, mem_neighborFinset, mem_neighborFinset] at hw
    exact ⟨{u, v, w}, SimpleGraph.mem_cliqueFinset_iff.mpr
      (SimpleGraph.is3Clique_iff.mpr ⟨u, v, w, huv, hw.1, hw.2, rfl⟩)⟩

end LeanPool.DrossFractionalTriangleDecomposition
