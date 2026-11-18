/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashTreeRankLess

public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegment

/-!
# Tash Tree Proper Initial Segment Rank Less

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem TashTreeProperInitialSegmentRankLess {V E : Type*}
    (G : LooplessMultigraph V E) {e0 : E} (S T : TreeSequence G e0)
    (hprefix : TreeSequenceInitialSegment S T)
    (hproper : S.length < T.length) : TashTreeRankLess G S T := by
  classical
  rcases hprefix with ⟨hlen, hvertex, hedge⟩
  have hspecS : TashTreeSuffixPath G S (TashTreePathIndex G S) := by
    unfold TashTreePathIndex
    exact Nat.find_spec _
  have hspecT : TashTreeSuffixPath G T (TashTreePathIndex G T) := by
    unfold TashTreePathIndex
    exact Nat.find_spec _
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

end GoldbergSeymour

end
