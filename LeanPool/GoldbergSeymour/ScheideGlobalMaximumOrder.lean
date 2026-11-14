/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.GlobalMaximumTriple

public import LeanPool.GoldbergSeymour.ScheideMaximalOddOrder

public import LeanPool.GoldbergSeymour.TashkinovOrderBound

/-!
# Scheide Global Maximum Order

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ScheideGlobalMaximumOrder {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hglobal : GlobalMaximumTriple G k e0 phi T) :
    TashkinovOrder G = (TreeSequenceVertexSet T).card ∧
      3 ≤ (TreeSequenceVertexSet T).card ∧
      Odd (TreeSequenceVertexSet T).card ∧
      ColoredVertexSetElementary G phi (TreeSequenceVertexSet T) ∧
      ColoredVertexSetClosed G phi (TreeSequenceVertexSet T) := by
  classical
  rcases hglobal with ⟨htriple, htree, hcard⟩
  have hmax : FixedPairMaximalTashkinovTree G e0 phi T := by
    refine ⟨htree, ?_⟩
    intro S hS hsubset
    have hle : (TreeSequenceVertexSet S).card ≤
        (TreeSequenceVertexSet T).card := by
      exact (treeCard_le_tashkinovOrder G k e0 phi S htriple hS).trans_eq hcard.symm
    have heq : TreeSequenceVertexSet S = TreeSequenceVertexSet T := by
      exact (Finset.eq_of_subset_of_card_le hsubset hle).symm
    rw [heq]
  have hodd := ScheideMaximalOddOrder G k e0 phi T htriple hmax
  have hec := ScheideMaximalElementaryClosed G k e0 phi T htriple hmax
  have htwo : 2 ≤ (TreeSequenceVertexSet T).card := by
    let v₀ : V := T.vertex ⟨0, Nat.zero_lt_succ _⟩
    have hp := T.positive
    let v₁ : V := T.vertex ⟨1, by omega⟩
    have hne : v₀ ≠ v₁ := by
      intro hv
      have hi := T.vertex_injective hv
      simp [] at hi
    have hpair : ({v₀, v₁} : Finset V).card = 2 := by
      simp [hne]
    have hsub : ({v₀, v₁} : Finset V) ⊆ TreeSequenceVertexSet T := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · simp [TreeSequenceVertexSet, v₀]
      · simp [TreeSequenceVertexSet, v₁]
    rw [← hpair]
    exact Finset.card_le_card hsub
  have hthree : 3 ≤ (TreeSequenceVertexSet T).card := by
    rcases hodd with ⟨n, hn⟩
    omega
  exact ⟨hcard.symm, hthree, hodd, hec.1, hec.2⟩

end GoldbergSeymour

end
