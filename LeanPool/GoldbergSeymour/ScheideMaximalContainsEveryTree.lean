/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ScheideMaximalElementaryClosed

/-!
# Scheide Maximal Contains Every Tree

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ScheideMaximalContainsEveryTree {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T S : TreeSequence G e0)
    (htriple : KTriple G k e0 phi)
    (hmax : FixedPairMaximalTashkinovTree G e0 phi T)
    (hS : TashkinovTree G e0 phi S) :
    TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet T := by
  classical
  let X := TreeSequenceVertexSet T
  have hclosed : ColoredVertexSetClosed G phi X := by
    exact (ScheideMaximalElementaryClosed G k e0 phi T htriple hmax).2
  have first_mem : ∀ j : Fin 2,
      S.vertex (Fin.castLE (Nat.succ_le_succ S.positive) j) ∈ X := by
    intro j
    obtain ⟨is, hsatt⟩ := S.attaches ⟨0, S.positive⟩
    obtain ⟨it, htatt⟩ := T.attaches ⟨0, T.positive⟩
    have iszero : is = 0 := Fin.eq_zero is
    have itzero : it = 0 := Fin.eq_zero it
    subst is
    subst it
    have hse := hsatt
    rw [S.first_edge] at hse
    have hte := htatt
    rw [T.first_edge] at hte
    have hm : S.vertex (Fin.castLE (Nat.succ_le_succ S.positive) j) ∈ G.ends e0 := by
      have cases : j.val = 0 ∨ j.val = 1 := by omega
      rcases cases with hzero | hone
      · have hj : j = 0 := Fin.ext hzero
        subst j
        rw [hse]
        apply Sym2.mem_iff.mpr
        right
        congr 1
      · have hj : j = 1 := Fin.ext hone
        subst j
        rw [hse]
        apply Sym2.mem_iff.mpr
        left
        congr 1
    rw [hte] at hm
    have cases : j.val = 0 ∨ j.val = 1 := by omega
    rcases cases with hzero | hone
    · have hj : j = 0 := Fin.ext hzero
      subst j
      rcases Sym2.mem_iff.mp hm with h | h
      · change S.vertex (Fin.castLE (Nat.succ_le_succ S.positive) 0) ∈
          Finset.image T.vertex Finset.univ
        exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, h.symm⟩
      · change S.vertex (Fin.castLE (Nat.succ_le_succ S.positive) 0) ∈
          Finset.image T.vertex Finset.univ
        exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, h.symm⟩
    · have hj : j = 1 := Fin.ext hone
      subst j
      rcases Sym2.mem_iff.mp hm with h | h
      · change S.vertex (Fin.castLE (Nat.succ_le_succ S.positive) 1) ∈
          Finset.image T.vertex Finset.univ
        exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, h.symm⟩
      · change S.vertex (Fin.castLE (Nat.succ_le_succ S.positive) 1) ∈
          Finset.image T.vertex Finset.univ
        exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, h.symm⟩
  have all_mem : ∀ n : ℕ, ∀ hn : n < S.length + 1,
      S.vertex ⟨n, hn⟩ ∈ X := by
    intro n hn
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hj : n < 2
      · exact first_mem ⟨n, by omega⟩
      · by_contra hout
        have hjpos : 1 ≤ n - 1 := by omega
        obtain ⟨i, c, hcolor, hmiss⟩ := hS ⟨n - 1, by omega⟩ hjpos
        have hi0 := i.isLt
        have hi : i.val < n := by
          have hi1 : i.val < (n - 1) + 1 := i.isLt
          have hnrel : (n - 1) + 1 = n := Nat.sub_add_cancel (by omega)
          simpa only [hnrel] using hi1
        have hiS : i.val < S.length + 1 := lt_of_lt_of_le hi (Nat.le_of_lt hn)
        have hbefore : S.vertex (Fin.castLT i hiS) ∈ X := by
          exact ih i.val hi (by omega)
        obtain ⟨q, hatt⟩ := S.attaches ⟨n - 1, by omega⟩
        have hq0 := q.isLt
        have hq : q.val < n := by
          have hq1 : q.val < (n - 1) + 1 := q.isLt
          have hnrel : (n - 1) + 1 = n := Nat.sub_add_cancel (by omega)
          simpa only [hnrel] using hq1
        have hqS : q.val < S.length + 1 := lt_of_lt_of_le hq (Nat.le_of_lt hn)
        have hqbefore : S.vertex (Fin.castLT q hqS) ∈ X := by
          exact ih q.val hq (by omega)
        have hnedge : n - 1 < S.length := by omega
        have hcurr : S.vertex ⟨n, hn⟩ =
            S.vertex (⟨n - 1, by omega⟩ : Fin S.length).succ := by
          congr 1
          apply Fin.ext
          dsimp
          exact (Nat.sub_add_cancel (by omega)).symm
        have hedge : G.ends (S.edge ⟨n - 1, by omega⟩) =
            Sym2.mk (S.vertex ⟨n, hn⟩)
              (S.vertex (Fin.castLT q hqS)) := by
          rw [hcurr]
          exact hatt
        have hb : S.edge ⟨n - 1, by omega⟩ ∈ BoundaryEdges G X := by
          unfold BoundaryEdges
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          exact ⟨S.vertex (Fin.castLT q hqS), hqbefore,
            S.vertex ⟨n, hn⟩, hout, by
              exact hedge.trans Sym2.eq_swap⟩
        exact hclosed hb hbefore hcolor hmiss
  intro v hv
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hv
  simpa [X] using all_mem j.val j.isLt

end GoldbergSeymour

end
