/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.BalancedGlobalMaximumTriple

public import LeanPool.GoldbergSeymour.ScheideGlobalMaximumOrder

public import LeanPool.GoldbergSeymour.ScheideBalancedCandidateMaximumExists
public import LeanPool.GoldbergSeymour.ScheideBalancedCandidateMaximumOrder
public import LeanPool.GoldbergSeymour.ScheideBalancedCandidateNormalTransport

/-!
# Scheide Balanced From Max Normal

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ScheideBalancedFromMaxNormal {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (N : NormalGlobalMaximumTriple G k e0 phi T)
    (hheight : N.height = ScheideGraphHeight G) :
    ∃ (T' : TreeSequence G e0)
      (N' : NormalGlobalMaximumTriple G k e0 phi T'),
      BalancedGlobalMaximumTriple N' ∧
        TreeSequenceVertexSet T' = TreeSequenceVertexSet T ∧
        TreeUsedColors phi T' ⊆ TreeUsedColors phi T := by
  classical
  obtain ⟨S, hS, hmax⟩ :=
    ScheideBalancedCandidateMaximumExists G k e0 phi T N hheight
  have horder : (TreeSequenceVertexSet S).card = TashkinovOrder G :=
    ScheideBalancedCandidateMaximumOrder G k e0 phi T S N hS hmax
  have hfixed : FixedPairMaximalTashkinovTree G e0 phi T :=
    ScheideGlobalMaximumFixedPairMaximal G k e0 phi T N.global
  have hsubset : TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet T :=
    ScheideMaximalContainsEveryTree G k e0 phi T S N.global.1 hfixed
      hS.tashkinov
  have hcard : (TreeSequenceVertexSet T).card ≤
      (TreeSequenceVertexSet S).card := by
    rw [N.global.2.2, horder]
  have hvertices : TreeSequenceVertexSet S = TreeSequenceVertexSet T :=
    Finset.eq_of_subset_of_card_le hsubset hcard
  obtain ⟨N', hN'⟩ :=
    ScheideBalancedCandidateNormalTransport G k e0 phi T S N hS hvertices
  refine ⟨S, N', ?_, hvertices, hS.usedColors⟩
  constructor
  · exact hN'.trans hheight
  · intro j hlow hupp
    exact hS.paired j (by simpa [hN'] using hlow) hupp

end GoldbergSeymour

end
