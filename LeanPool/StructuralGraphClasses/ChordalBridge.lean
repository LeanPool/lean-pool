/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.StructuralGraphClasses.Split
public import LeanPool.PaperIVCliqueTree.Characterization

/-!
# Split partitions and chordal interfaces

Independent vertices are simplicial in a split graph. Every induced subgraph
either contains such a vertex or is a clique. The existing elimination-order
constructor therefore produces a perfect elimination order without a new graph
representation or a duplicate proof of the chordal characterization.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- A split partition supplies a simplicial vertex in every nonempty finite set. -/
theorem SplitPartition.exists_simplicial_in_finset (P : SplitPartition G) (S : Finset V)
    (hS : S.Nonempty) :
    ∃ z ∈ S, ∀ a ∈ S, ∀ b ∈ S, G.Adj z a → G.Adj z b → a ≠ b → G.Adj a b := by
  classical
  by_cases hi : ∃ z ∈ S, z ∈ P.independent
  · obtain ⟨z, hzS, hzI⟩ := hi
    refine ⟨z, hzS, ?_⟩
    intro a ha b hb hza hzb hab
    have haC : a ∈ P.clique := by
      rcases P.mem_clique_or_mem_independent a with h | h
      · exact h
      · exact False.elim (P.isIndepSet hzI h hza.ne hza)
    have hbC : b ∈ P.clique := by
      rcases P.mem_clique_or_mem_independent b with h | h
      · exact h
      · exact False.elim (P.isIndepSet hzI h hzb.ne hzb)
    exact P.isClique haC hbC hab
  · obtain ⟨z, hzS⟩ := hS
    refine ⟨z, hzS, ?_⟩
    intro a ha b hb hza hzb hab
    have haC : a ∈ P.clique := by
      rcases P.mem_clique_or_mem_independent a with h | h
      · exact h
      · exact False.elim (hi ⟨a, ha, h⟩)
    have hbC : b ∈ P.clique := by
      rcases P.mem_clique_or_mem_independent b with h | h
      · exact h
      · exact False.elim (hi ⟨b, hb, h⟩)
    exact P.isClique haC hbC hab

/-- A finite split graph has a perfect elimination order. -/
theorem IsSplit.exists_isPEO [Finite V] (h : G.IsSplit) : ∃ ord : V → ℕ, G.IsPEO ord := by
  obtain ⟨P⟩ := h
  exact exists_isPEO_of_simplicial_in_finset P.exists_simplicial_in_finset

/-- Every finite split graph is chordal. -/
theorem IsSplit.isChordal [Finite V] (h : G.IsSplit) : G.IsChordal := by
  obtain ⟨ord, ho⟩ := h.exists_isPEO
  exact ho.isChordal

/-- A finite split graph and its complement are both chordal. -/
theorem IsSplit.isChordal_and_compl [Finite V] (h : G.IsSplit) :
    G.IsChordal ∧ Gᶜ.IsChordal :=
  ⟨h.isChordal, h.compl.isChordal⟩

end SimpleGraph
