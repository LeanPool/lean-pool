/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.ClassicalMatchingFactors.Matching.Berge
public import LeanPool.ClassicalMatchingFactors.Bipartite.MatchingCover

/-!
# Optimality certificates for finite graph matchings

An odd-component barrier certifies a maximum matching by the weak Tutte–Berge inequality.
In a bipartite graph, a vertex cover of the same size certifies both sides of the minimax theorem.
These interfaces consume the actual matching and vertex-cover predicates of Mathlib.
-/

@[expose] public section

namespace ClassicalMatchingFactors

open SimpleGraph

/-- Equality in the Tutte–Berge bound certifies that the matching is maximum. -/
theorem isMaximum_of_barrier {V : Type*} [Finite V] {G : SimpleGraph V}
    {M : G.Subgraph} (hM : M.IsMatching) (U : Set V)
    (heq : 2 * M.edgeSet.ncard + BergeMatching.oddCount G U = Nat.card V + U.ncard) :
    M.IsMatching ∧
      ∀ M' : G.Subgraph, M'.IsMatching → M'.edgeSet.ncard ≤ M.edgeSet.ncard := by
  refine ⟨hM, ?_⟩
  intro M' hM'
  have hbound := BergeMatching.two_mul_card_add_le hM' U
  omega

/-- A maximum matching has both an odd-component barrier and no augmenting path. -/
theorem exists_matching_with_barrier_and_no_augmenting {V : Type*} [Finite V]
    (G : SimpleGraph V) :
    ∃ (M : G.Subgraph) (U : Set V), M.IsMatching ∧
      (¬ ∃ (u v : V) (p : G.Walk u v), BergeMatching.IsAugmentingPath M p) ∧
      2 * M.edgeSet.ncard + BergeMatching.oddCount G U = Nat.card V + U.ncard := by
  obtain ⟨M, U, hM, heq⟩ := BergeMatching.exists_tutte_berge G
  exact ⟨M, U, hM, (BergeMatching.isMaximum_iff_not_exists_augmenting hM).mp
    (isMaximum_of_barrier hM U heq).2, heq⟩

/-- A bipartite graph admits a matching-cover pair certifying both optima. -/
theorem exists_optimal_matching_cover_pair {V : Type*} [Finite V] (G : SimpleGraph V)
    (hG : G.Colorable 2) :
    ∃ (M : G.Subgraph) (C : Set V), M.IsMatching ∧ G.IsVertexCover C ∧
      M.edgeSet.ncard = C.ncard ∧
      (∀ M' : G.Subgraph, M'.IsMatching → M'.edgeSet.ncard ≤ M.edgeSet.ncard) ∧
      ∀ C' : Set V, G.IsVertexCover C' → C.ncard ≤ C'.ncard := by
  obtain ⟨M, C, hM, hC, heq⟩ := Konig.Egervary.exists_matching_card_eq_vertexCover G hG
  refine ⟨M, C, hM, hC, heq, ?_, ?_⟩
  · intro M' hM'
    exact (Konig.Egervary.card_matching_le_card_vertexCover hM' hC).trans heq.ge
  · intro C' hC'
    exact heq.ge.trans (Konig.Egervary.card_matching_le_card_vertexCover hM hC')

end ClassicalMatchingFactors
