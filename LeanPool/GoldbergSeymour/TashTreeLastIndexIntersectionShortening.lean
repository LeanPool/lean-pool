/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashTreeMinimumBadPair

public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequencePreservesTashkinovTree

public import LeanPool.GoldbergSeymour.TwoColorComponentTashkinovSplice

/-!
# Tash Tree Last Index Intersection Shortening

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem TashTreeLastIndexIntersectionShortening {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T S : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T)
    (hlast : TashTreePathIndex G T = T.length)
    (hST : TreeSequenceInitialSegment S T)
    (hlen : S.length + 2 = T.length)
    (alpha beta : Fin k) (hne : alpha ≠ beta)
    (halpha : alpha ∈ TreeMissingColors phi S)
    (hbeta : beta ∈ TreeMissingColors phi S)
    (hlastbeta : beta ∈
      MissingColors G phi (T.vertex (Fin.last T.length)))
    (hlastOutside : T.vertex (Fin.last T.length) ∉ TreeSequenceVertexSet S)
    (hmeets : ∃ u ∈ TreeSequenceVertexSet S,
      Sum.inl u ∈ TwoColorComponent G phi alpha beta
        (Sum.inl (T.vertex (Fin.last T.length)))) : False := by
  classical
  have hSTdata := hST
  rcases hSTdata with ⟨hSTlen, hSTvertices, hSTedges⟩
  have hTashS : TashkinovTree G e0 phi S := by
    intro j hj
    rcases hmin.1.2.1 (Fin.castLE hSTlen j) hj with
      ⟨i, c, hcolor, hmissing⟩
    refine ⟨i, c, ?_, ?_⟩
    · rw [hSTedges j] at hcolor
      exact hcolor
    · have hindex :
          Fin.castLE (Nat.succ_le_succ hSTlen)
              (Fin.castLT i
                (Nat.lt_trans i.isLt (Nat.succ_lt_succ j.isLt))) =
            Fin.castLT i
              (Nat.lt_trans i.isLt
                (Nat.succ_lt_succ (Fin.castLE hSTlen j).isLt)) := by
        apply Fin.ext
        rfl
      rw [← hSTvertices, hindex]
      exact hmissing
  have hproper : IsProperEdgeColoring G phi := hmin.1.1.2.2.2.1
  obtain ⟨u, S', hu, _huComponent, hSS', hlength, haugment,
      hlastVertex, hsplice⟩ :=
    TwoColorComponentTashkinovSplice G phi S alpha beta
      (T.vertex (Fin.last T.length)) hproper hne halpha hbeta
      hlastOutside hmeets
  have hTashS' : TashkinovTree G e0 phi S' :=
    TashkinovAugmentationSequencePreservesTashkinovTree G e0 phi S S'
      hTashS haugment
  have hSS'data := hSS'
  rcases hSS'data with ⟨hSSlen, hSSvertices, hSSedges⟩
  have hnotElementary :
      ¬ ColoredVertexSetElementary G phi (TreeSequenceVertexSet S') := by
    intro helementary
    rw [TreeMissingColors] at hbeta
    rcases Finset.mem_biUnion.mp hbeta with ⟨v, hvS, hvbeta⟩
    have hvS' : v ∈ TreeSequenceVertexSet S' := by
      rw [TreeSequenceVertexSet] at hvS ⊢
      rcases Finset.mem_image.mp hvS with ⟨j, hj, rfl⟩
      refine Finset.mem_image.mpr
        ⟨Fin.castLE (Nat.succ_le_succ hSSlen) j, Finset.mem_univ _, ?_⟩
      exact hSSvertices j
    have hyS' : T.vertex (Fin.last T.length) ∈
        TreeSequenceVertexSet S' := by
      rw [← hlastVertex, TreeSequenceVertexSet]
      exact Finset.mem_image.mpr
        ⟨Fin.last S'.length, Finset.mem_univ _, rfl⟩
    have hvne : v ≠ T.vertex (Fin.last T.length) := by
      intro hv
      apply hlastOutside
      rwa [← hv]
    have hdisjoint := helementary hvS' hyS' hvne
    exact (Finset.disjoint_left.mp hdisjoint) hvbeta hlastbeta
  have hbadS' : TashTreeBadPair G k e0 phi S' :=
    ⟨hmin.1.1, hTashS', hnotElementary⟩
  have hsuffix : TashTreeSuffixPath G S' (S.length + 1) := by
    refine ⟨by omega, by omega, ?_⟩
    intro r hr
    have hrbase : S.length ≤ r.val := by omega
    have hrne : r.val ≠ S.length := by omega
    simpa [hrne] using (hsplice r hrbase).2.2.2.2
  have hindexLe : TashTreePathIndex G S' ≤ S.length + 1 := by
    unfold TashTreePathIndex
    exact Nat.find_min' _ hsuffix
  have hrank : TashTreeRankLess G S' T := by
    left
    rw [hlast]
    omega
  exact (hmin.2 hbadS') hrank

end GoldbergSeymour

end
