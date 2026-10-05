/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.StructuralGraphClasses.SplitObstructions
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
# Native induced embeddings of chordless cycles

The vertices of a chordless cycle, indexed before the repeated endpoint,
give an induced embedding of Mathlib's cycle graph. A cycle of length at
least six then contains an induced pair of disjoint edges.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {v : V} {p : G.Walk v v}

/-- Adjacency along a chordless cycle is precisely consecutive or wraparound adjacency. -/
theorem Walk.IsCycle.adj_getVert_iff_of_isChordless (hc : p.IsCycle) (hh : p.IsChordless)
    {i j : ℕ} (hi : i < p.length) (hj : j < p.length) :
    G.Adj (p.getVert i) (p.getVert j) ↔
      i + 1 = j ∨ j + 1 = i ∨ (i = 0 ∧ j + 1 = p.length) ∨
        (j = 0 ∧ i + 1 = p.length) := by
  have hn := hc.three_le_length
  have heq {a b : ℕ} (ha : a < p.length) (hb : b < p.length) :
      p.getVert a = p.getVert b ↔ a = b :=
    ⟨hc.getVert_injOn' (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega), congrArg p.getVert⟩
  have hsub : G.Adj (p.getVert i) (p.getVert j) ↔
      p.toSubgraph.Adj (p.getVert i) (p.getVert j) :=
    ⟨fun h => Walk.adj_toSubgraph_iff_mem_edges.mpr
      (hh.mem_edges (p.getVert_mem_support i) (p.getVert_mem_support j) h),
      p.toSubgraph.adj_sub⟩
  rw [hsub]
  change p.getVert j ∈ p.toSubgraph.neighborSet (p.getVert i) ↔ _
  by_cases hi0 : i = 0
  · subst i
    rw [Walk.getVert_zero, hc.neighborSet_toSubgraph_endpoint,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    change (p.getVert j = p.getVert 1 ∨ p.getVert j = p.getVert (p.length - 1)) ↔ _
    rw [heq hj (by omega), heq hj (by omega)]
    omega
  · rw [hc.neighborSet_toSubgraph_internal hi0 hi,
      Set.mem_insert_iff, Set.mem_singleton_iff, heq hj (by omega)]
    by_cases hlast : i + 1 = p.length
    · have hwrap : p.getVert (i + 1) = p.getVert 0 := by
        simp only [hlast, Walk.getVert_length, Walk.getVert_zero]
      rw [hwrap, heq hj (by omega)]
      omega
    · rw [heq hj (by omega)]
      omega

private theorem cycleGraph_adj_iff_consecutive {n : ℕ} (hn : 3 ≤ n) (i j : Fin n) :
    (cycleGraph n).Adj i j ↔
      i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
        (i.val = 0 ∧ j.val + 1 = n) ∨ (j.val = 0 ∧ i.val + 1 = n) := by
  rw [cycleGraph_adj']
  by_cases hij : i = j
  · subst j
    rw [Fin.sub_val_of_le (le_refl i)]
    have := i.isLt
    omega
  · by_cases hle : i ≤ j
    · have hlt : i < j := lt_of_le_of_ne hle hij
      rw [Fin.coe_sub_iff_lt.mpr hlt, Fin.sub_val_of_le hle]
      have := i.isLt
      have := j.isLt
      change i.val < j.val at hlt
      omega
    · have hlt : j < i := lt_of_not_ge hle
      rw [Fin.sub_val_of_le hlt.le, Fin.coe_sub_iff_lt.mpr hlt]
      have := i.isLt
      have := j.isLt
      change j.val < i.val at hlt
      omega

/-- A chordless cycle supplies a native induced embedding of the cycle graph. -/
theorem Walk.IsCycle.cycleGraph_isIndContained_of_isChordless
    (hc : p.IsCycle) (hh : p.IsChordless) : (cycleGraph p.length).IsIndContained G := by
  refine ⟨⟨⟨fun i => p.getVert i.val, ?_⟩, ?_⟩⟩
  · intro i j hij
    apply Fin.ext
    exact hc.getVert_injOn' (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega) hij
  · intro i j
    exact (hc.adj_getVert_iff_of_isChordless hh i.isLt j.isLt).trans
      (cycleGraph_adj_iff_consecutive hc.three_le_length i j).symm

/-- A chordless cycle of length at least six has an induced disjoint pair of edges. -/
theorem Walk.IsCycle.twoK2_isIndContained_of_isChordless (hc : p.IsCycle)
    (hh : p.IsChordless) (hlen : 6 ≤ p.length) :
    ((⊤ : SimpleGraph (Fin 2)) ⊕g (⊤ : SimpleGraph (Fin 2))).IsIndContained G := by
  have hne {i j : ℕ} (hi : i < p.length) (hj : j < p.length) (hij : i ≠ j) :
      p.getVert i ≠ p.getVert j := fun h => hij
        (hc.getVert_injOn' (by simp only [Set.mem_ofPred_eq]; omega)
          (by simp only [Set.mem_ofPred_eq]; omega) h)
  apply twoK2_isIndContained_of_adj (a := p.getVert 0) (b := p.getVert 1)
    (c := p.getVert 3) (d := p.getVert 4)
  · exact p.adj_getVert_succ (by omega)
  · exact p.adj_getVert_succ (by omega)
  · exact hne (by omega) (by omega) (by omega)
  · exact hne (by omega) (by omega) (by omega)
  · exact hne (by omega) (by omega) (by omega)
  · exact hne (by omega) (by omega) (by omega)
  all_goals rw [hc.adj_getVert_iff_of_isChordless hh (by omega) (by omega)]; omega

end SimpleGraph
