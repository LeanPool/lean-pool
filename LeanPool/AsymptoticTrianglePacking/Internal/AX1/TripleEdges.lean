/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — counting the edges of a tripartite sub-triple

The bridge `Nibble.AX1.hasNearRegularFamily_of_subTripleDesign` needs, for each sub-triple
`(A, B, C)`, a lower bound `Elo` for the number of edges of `tripleGraph G A B C`.  The edges
between two of the three parts already give one: the `A`–`B` interedges of `G` inject into the
`2`-cliques of the tripartite graph, so

`Elo := d(A,B)·|A|·|B| ≤ #((tripleGraph G A B C).cliqueFinset 2)`.

* `Nibble.AX1.interedges_card_le_tripleGraph_edges` — the injection.
* `Nibble.AX1.edgeDensity_mul_le_tripleGraph_edges` — its density form.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapDesign

/-! # TripleEdges -/

@[expose] public section

open Finset SimpleGraph

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **The `A`–`B` edges of `G` are edges of the tripartite graph of `(A, B, C)`.**  They inject
into its `2`-cliques (injectively, because `A` and `B` are disjoint, so an unordered pair
determines which endpoint lies in `A`). -/
theorem interedges_card_le_tripleGraph_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B C : Finset V) (hAB : Disjoint A B) :
    (#(G.interedges A B) : ℝ) ≤ (#((tripleGraph G A B C).cliqueFinset 2) : ℝ) := by
  classical
  have hcard : #(G.interedges A B) ≤ #((tripleGraph G A B C).cliqueFinset 2) := by
    refine Finset.card_le_card_of_injOn (fun p => ({p.1, p.2} : Finset V)) ?_ ?_
    · rintro ⟨x, y⟩ hp
      simp only [Finset.mem_coe, SimpleGraph.mk_mem_interedges_iff] at hp
      obtain ⟨hx, hy, hadj⟩ := hp
      have hne : x ≠ y := hadj.ne
      have hadj' : (tripleGraph G A B C).Adj x y := ⟨hadj, Or.inl ⟨hx, hy⟩⟩
      simpa only [Finset.mem_coe] using
        (pair_mem_cliqueFinset_two (tripleGraph G A B C) hne).mpr hadj'
    · rintro ⟨x, y⟩ hp ⟨x', y'⟩ hp' heq
      simp only [Finset.mem_coe, SimpleGraph.mk_mem_interedges_iff] at hp hp'
      obtain ⟨hx, hy, -⟩ := hp
      obtain ⟨hx', hy', -⟩ := hp'
      have hxy : x ≠ y := fun h => (Finset.disjoint_left.mp hAB hx) (h ▸ hy)
      have hpairs : ({x, y} : Finset V) = ({x', y'} : Finset V) := heq
      have hxmem : x ∈ ({x', y'} : Finset V) := by
        rw [← hpairs]; simp
      have hymem : y ∈ ({x', y'} : Finset V) := by
        rw [← hpairs]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxmem hymem
      rcases hxmem with rfl | rfl
      · rcases hymem with rfl | rfl
        · exact absurd rfl hxy
        · rfl
      · exact absurd hy' (Finset.disjoint_left.mp hAB hx)
  exact_mod_cast hcard

/-- **Density form of `Nibble.AX1.interedges_card_le_tripleGraph_edges`.** -/
theorem edgeDensity_mul_le_tripleGraph_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B C : Finset V) (hAB : Disjoint A B) :
    (G.edgeDensity A B : ℝ) * (#A : ℝ) * (#B : ℝ)
      ≤ (#((tripleGraph G A B C).cliqueFinset 2) : ℝ) := by
  classical
  have hdef : (G.edgeDensity A B : ℝ) = (#(G.interedges A B) : ℝ) / ((#A : ℝ) * (#B : ℝ)) := by
    rw [SimpleGraph.edgeDensity_def]; push_cast; ring
  rcases Nat.eq_zero_or_pos #A with hA | hA
  · have : (#A : ℝ) = 0 := by exact_mod_cast hA
    rw [this]
    simp
  rcases Nat.eq_zero_or_pos #B with hB | hB
  · have : (#B : ℝ) = 0 := by exact_mod_cast hB
    rw [this]
    simp
  have hA' : (0 : ℝ) < (#A : ℝ) := by exact_mod_cast hA
  have hB' : (0 : ℝ) < (#B : ℝ) := by exact_mod_cast hB
  have hmul : (G.edgeDensity A B : ℝ) * (#A : ℝ) * (#B : ℝ) = (#(G.interedges A B) : ℝ) := by
    rw [hdef]; field_simp
  rw [hmul]
  exact interedges_card_le_tripleGraph_edges G A B C hAB

end Nibble.AX1
