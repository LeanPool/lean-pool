/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashTreeMinimumBadPair

public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegment

/-!
# Tash Tree Proper Prefix Elementary

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem TashTreeProperPrefixElementary {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T S : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T)
    (hprefix : TreeSequenceInitialSegment S T) (hproper : S.length < T.length) :
    ColoredVertexSetElementary G phi (TreeSequenceVertexSet S) := by
  classical
  rcases hmin with ⟨hbadT, hminimal⟩
  rcases hprefix with ⟨hlen, hvertex, hedge⟩
  rcases hbadT with ⟨htriple, hTashT, hnotElementaryT⟩
  have hTashS : TashkinovTree G e0 phi S := by
    intro j hj
    rcases hTashT (Fin.castLE hlen j) hj with ⟨i, c, hcolor, hmissing⟩
    refine ⟨i, c, ?_, ?_⟩
    · rw [← hedge j]
      exact hcolor
    · rw [← hvertex (Fin.castLT i
          (Nat.lt_trans i.isLt (Nat.succ_lt_succ j.isLt)))]
      exact hmissing
  have hspecS : TashTreeSuffixPath G S (TashTreePathIndex G S) := by
    unfold TashTreePathIndex
    exact Nat.find_spec _
  have hspecT : TashTreeSuffixPath G T (TashTreePathIndex G T) := by
    unfold TashTreePathIndex
    exact Nat.find_spec _
  have hrank : TashTreeRankLess G S T := by
    let q := TashTreePathIndex G T
    have hpathSBound : TashTreePathIndex G S ≤ S.length := hspecS.2.1
    by_cases hshort : S.length < q
    · left
      exact hpathSBound.trans_lt hshort
    · have hqS : q ≤ S.length := Nat.le_of_not_gt hshort
      have hsuffixS : TashTreeSuffixPath G S q := by
        refine ⟨hspecT.1, hqS, ?_⟩
        intro i hi
        rw [← hedge i, ← hvertex i.castSucc, ← hvertex i.succ]
        exact hspecT.2.2 (Fin.castLE hlen i) hi
      have hindexLe : TashTreePathIndex G S ≤ q := by
        unfold TashTreePathIndex
        exact Nat.find_min' _ hsuffixS
      rcases hindexLe.eq_or_lt with heq | hlt
      · right
        exact ⟨heq, hproper⟩
      · left
        exact hlt
  by_contra hnotElementaryS
  have hbadS : TashTreeBadPair G k e0 phi S :=
    ⟨htriple, hTashS, hnotElementaryS⟩
  exact (hminimal hbadS) hrank

end GoldbergSeymour

end
