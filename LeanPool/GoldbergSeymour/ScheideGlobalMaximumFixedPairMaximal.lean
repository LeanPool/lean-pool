/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.FixedPairMaximalTashkinovTree
public import LeanPool.GoldbergSeymour.GlobalMaximumTriple

/-!
# Scheide Global Maximum Fixed Pair Maximal

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ScheideGlobalMaximumFixedPairMaximal {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hglobal : GlobalMaximumTriple G k e0 phi T) :
    FixedPairMaximalTashkinovTree G e0 phi T := by
  classical
  refine ⟨hglobal.2.1, ?_⟩
  intro S hS hsub
  have hk : ChromaticIndex G - 1 = k := by
    have hchrom := hglobal.1.2.1
    omega
  have hScard : (TreeSequenceVertexSet S).card ≤ TashkinovOrder G := by
    unfold TashkinovOrder
    dsimp only
    apply Finset.le_max'
    apply Finset.mem_insert_of_mem
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_le_univ _))
    · rw [hk]
      exact ⟨e0, phi, S, hglobal.1, hS, rfl⟩
  have hcard : (TreeSequenceVertexSet S).card ≤
      (TreeSequenceVertexSet T).card := by
    rw [hglobal.2.2]
    exact hScard
  have heq : TreeSequenceVertexSet T = TreeSequenceVertexSet S :=
    Finset.eq_of_subset_of_card_le hsub hcard
  exact heq.symm.subset

end GoldbergSeymour

end
