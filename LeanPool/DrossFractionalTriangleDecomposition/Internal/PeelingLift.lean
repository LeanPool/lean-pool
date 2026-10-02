/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.DrossFractionalTriangleDecomposition.Internal.PeelingDegree
import Mathlib.Tactic.NormNum

/-!
# Lifting a decomposition after triangle peeling

The peeled graph has fewer edges. Its fractional triangle weights extend by
zero, and weight one on the removed triangle restores exact edge coverage.
-/

namespace LeanPool.DrossFractionalTriangleDecomposition

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

public theorem peeled_heavy_triangle_fewer_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v w : V} (huv : G.Adj u v) (huw : G.Adj u w) (hvw : G.Adj v w) :
    (G.deleteEdges (triEdges {u, v, w})).edgeFinset.card < G.edgeFinset.card := by
  have hsub := triEdges_heavy_triangle_subset G huv huw hvw
  have hcard := triEdges_heavy_triangle_card G huv huw hvw
  rw [edgeFinset_deleteEdges, card_sdiff_of_subset hsub]
  apply Nat.sub_lt
  · have hc := card_le_card hsub
    omega
  · omega

public theorem cliqueFinset_deleteEdges_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Sym2 V)) (n : ℕ) :
    (G.deleteEdges S).cliqueFinset n ⊆ G.cliqueFinset n := by
  intro t ht
  rw [mem_cliqueFinset_iff] at ht ⊢
  exact ht.mono (deleteEdges_le _)

public theorem sum_truncated_cliques (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Sym2 V)) (n : ℕ) (a : Finset V → ℝ) (e : Sym2 V) :
    (∑ t ∈ G.cliqueFinset n,
      if e ∈ triEdges t then (if t ∈ (G.deleteEdges S).cliqueFinset n then a t else 0) else 0) =
    ∑ t ∈ (G.deleteEdges S).cliqueFinset n, if e ∈ triEdges t then a t else 0 := by
  rw [← sum_subset (cliqueFinset_deleteEdges_subset G S n)]
  · apply sum_congr rfl
    intro t ht
    simp [ht]
  · intro t htG htG'
    simp [htG']

public theorem deleted_edge_not_in_clique (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Sym2 V)) {e : Sym2 V} (heS : e ∈ S) {n : ℕ} {t : Finset V}
    (ht : t ∈ (G.deleteEdges S).cliqueFinset n) : e ∉ triEdges t := by
  intro het
  induction e using Sym2.inductionOn with
  | _ x y =>
    have hmem := mem_filter.mp het
    have hxt := mem_sym2_iff.mp hmem.1 x (by simp)
    have hyt := mem_sym2_iff.mp hmem.1 y (by simp)
    have hxy : x ≠ y := by simpa using hmem.2
    have hc := (mem_cliqueFinset_iff.mp ht).isClique hxt hyt hxy
    exact (deleteEdges_adj.mp hc).2 heS

public theorem triangle_indicator_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v w : V} (huv : G.Adj u v) (huw : G.Adj u w) (hvw : G.Adj v w)
    (e : Sym2 V) :
    (∑ t ∈ G.cliqueFinset 3,
      if e ∈ triEdges t then (if t = {u, v, w} then (1 : ℝ) else 0) else 0) =
      if e ∈ triEdges {u, v, w} then 1 else 0 := by
  have hT : {u, v, w} ∈ G.cliqueFinset 3 :=
    mem_cliqueFinset_iff.mpr (is3Clique_iff.mpr ⟨u, v, w, huv, huw, hvw, rfl⟩)
  rw [sum_eq_single {u, v, w}]
  · simp
  · intro t ht hne
    simp [hne]
  · intro hnot
    exact (hnot hT).elim

public theorem lift_fractional_decomp_triangle (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v w : V} (huv : G.Adj u v) (huw : G.Adj u w) (hvw : G.Adj v w)
    (hdec : FractionalTriangleDecomp (G.deleteEdges (triEdges {u, v, w}))) :
    FractionalTriangleDecomp G := by
  classical
  let T : Finset V := {u, v, w}
  let G' := G.deleteEdges (triEdges T)
  rcases hdec with ⟨a, ha, hcov⟩
  refine ⟨fun t => (if t ∈ G'.cliqueFinset 3 then a t else 0) +
      (if t = T then 1 else 0), ?_, ?_⟩
  · intro t
    exact add_nonneg (by split <;> simp_all) (by split <;> norm_num)
  · intro e he
    have hsplit :
        (∑ t ∈ G.cliqueFinset 3,
          if e ∈ triEdges t then
            ((if t ∈ G'.cliqueFinset 3 then a t else 0) + (if t = T then 1 else 0)) else 0) =
        (∑ t ∈ G.cliqueFinset 3,
          if e ∈ triEdges t then (if t ∈ G'.cliqueFinset 3 then a t else 0) else 0) +
        (∑ t ∈ G.cliqueFinset 3,
          if e ∈ triEdges t then (if t = T then 1 else 0) else 0) := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro t ht
      by_cases het : e ∈ triEdges t <;> simp [het]
    rw [hsplit, sum_truncated_cliques G (triEdges T) 3 a e,
      triangle_indicator_sum G huv huw hvw e]
    by_cases heT : e ∈ triEdges T
    · have hz : (∑ t ∈ G'.cliqueFinset 3, if e ∈ triEdges t then a t else 0) = 0 := by
        apply sum_eq_zero
        intro t ht
        simp [deleted_edge_not_in_clique G (triEdges T) heT ht]
      change (∑ t ∈ G'.cliqueFinset 3, if e ∈ triEdges t then a t else 0) +
        (if e ∈ triEdges T then 1 else 0) = 1
      simp [hz, heT]
    · have heG' : e ∈ G'.edgeFinset := by
        rw [edgeFinset_deleteEdges]
        exact mem_sdiff.mpr ⟨he, heT⟩
      simpa [G', T, heT] using hcov e heG'

end LeanPool.DrossFractionalTriangleDecomposition
