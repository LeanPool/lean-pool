/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.DrossFractionalTriangleDecomposition.Internal.DenseBase

/-!
# The complete-graph case

Maximum possible minimum degree makes the graph complete. Each edge then
has exactly `n - 2` common neighbours, so constant triangle weights suffice.
-/

namespace LeanPool.DrossFractionalTriangleDecomposition

open SimpleGraph Finset

variable {V : Type*} [Fintype V]

/-- Every vertex degree is at most one less than the order of the graph. -/
public theorem degree_le_card_sub_one (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) :
    G.degree u ≤ Fintype.card V - 1 := by
  classical
  rw [SimpleGraph.degree]
  calc
    (G.neighborFinset u).card ≤ (Finset.univ \ {u}).card := by
      apply Finset.card_le_card
      intro v hv
      simp only [Finset.mem_sdiff, Finset.mem_singleton]
      refine ⟨Finset.mem_univ _, ?_⟩
      intro h
      rw [h] at hv
      simp only [SimpleGraph.mem_neighborFinset] at hv
      exact G.loopless.irrefl u hv
    _ = Fintype.card V - 1 := by rw [card_sdiff]; simp

/-- Maximum minimum degree forces all distinct vertices to be adjacent. -/
public theorem adj_of_minDegree_eq_card_sub_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : G.minDegree = Fintype.card V - 1) {u v : V} (huv : u ≠ v) :
    G.Adj u v := by
  classical
  have hdeg_u : G.degree u = Fintype.card V - 1 :=
    Nat.le_antisymm (degree_le_card_sub_one G u) (hmin ▸ G.minDegree_le_degree u)
  have hsub : G.neighborFinset u ⊆ Finset.univ \ {u} := by
    intro w hw
    simp only [Finset.mem_sdiff, Finset.mem_singleton]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro h
    rw [h] at hw
    simp only [SimpleGraph.mem_neighborFinset] at hw
    exact G.loopless.irrefl u hw
  have hcard : (G.neighborFinset u).card = (Finset.univ \ {u}).card := by
    rw [SimpleGraph.degree] at hdeg_u
    rw [hdeg_u, card_sdiff]; simp
  have hneigh : G.neighborFinset u = Finset.univ \ {u} :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard])
  have hv : v ∈ G.neighborFinset u := by
    rw [hneigh]
    simp [Ne.symm huv]
  exact (G.mem_neighborFinset u v).mp hv

/-- In the complete case, an edge belongs to precisely `n - 2` triangles. -/
public theorem triThrough_of_minDegree_eq_card_sub_one (G : SimpleGraph V)
    [DecidableEq V] [DecidableRel G.Adj]
    (hmin : G.minDegree = Fintype.card V - 1)
    {e : Sym2 V} (he : e ∈ G.edgeFinset) :
    triThrough G e = Fintype.card V - 2 := by
  rw [SimpleGraph.mem_edgeFinset] at he
  induction e using Sym2.inductionOn with
  | hf u v =>
    have huv : G.Adj u v := he
    rw [triThrough_edge G huv, codeg]
    have hnei (x : V) : G.neighborFinset x = Finset.univ \ {x} := by
      ext w
      simp only [mem_neighborFinset, mem_sdiff, mem_univ, true_and, mem_singleton]
      exact ⟨fun h => h.ne.symm,
        fun h => adj_of_minDegree_eq_card_sub_one G hmin (Ne.symm h)⟩
    rw [hnei u, hnei v]
    have hset : (Finset.univ \ {u}) ∩ (Finset.univ \ {v}) =
        Finset.univ \ ({u, v} : Finset V) := by
      ext w
      simp only [mem_inter, mem_sdiff, mem_univ, true_and,
        mem_singleton, mem_insert]
      tauto
    rw [hset, card_sdiff]
    simp [Finset.card_pair huv.ne]

/-- A graph with the maximum possible minimum degree has a fractional
triangle decomposition once it has at least three vertices. -/
public theorem complete_fractional (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj]
    (hmin : G.minDegree = Fintype.card V - 1) (hcard : 3 ≤ Fintype.card V) :
    FractionalTriangleDecomp G := by
  have hT : 0 < Fintype.card V - 2 := by omega
  exact fractional_of_constant_triThrough G (Fintype.card V - 2) hT
    (fun e he => triThrough_of_minDegree_eq_card_sub_one G hmin he)

end LeanPool.DrossFractionalTriangleDecomposition
