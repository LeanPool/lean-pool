/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovOrder

/-!
# Bounding a Tashkinov tree by the global order

Extracted from the repeated maximum-membership arguments in the Trellis formalization.
-/

public section

namespace GoldbergSeymour

/-- Every Tashkinov tree for a critical colouring is bounded by the global Tashkinov order. -/
theorem treeCard_le_tashkinovOrder {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (htriple : KTriple G k e0 phi) (htree : TashkinovTree G e0 phi T) :
    (TreeSequenceVertexSet T).card ≤ TashkinovOrder G := by
  classical
  have hk : ChromaticIndex G - 1 = k := by
    have hchi := htriple.2.1
    omega
  subst k
  unfold TashkinovOrder
  dsimp only
  refine Finset.le_max' _ _ (Finset.mem_insert_of_mem ?_)
  refine Finset.mem_filter.mpr ⟨?_, e0, phi, T, htriple, htree, rfl⟩
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_le_univ _))

end GoldbergSeymour

end
