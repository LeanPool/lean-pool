/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ScheideBalancedCandidate
public import LeanPool.GoldbergSeymour.ScheideGraphHeightOdd

/-!
# Scheide Balanced Candidate Maximum Exists

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ScheideBalancedCandidateMaximumExists {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (N : NormalGlobalMaximumTriple G k e0 phi T)
    (hheight : N.height = ScheideGraphHeight G) :
    ∃ S : TreeSequence G e0,
      ScheideBalancedCandidate N S ∧
        ∀ R : TreeSequence G e0, ScheideBalancedCandidate N R →
          (TreeSequenceVertexSet R).card ≤
            (TreeSequenceVertexSet S).card := by
  classical
  let Q : TreeSequence G e0 := NormalTripleTrunk N
  have qLength : Q.length + 1 = N.height := by
    dsimp [Q, NormalTripleTrunk, TreeSequencePrefix]
    have := N.height_lower
    omega
  have qBound : Q.length ≤ T.length := by
    have := N.height_upper
    omega
  have qTashkinov : TashkinovTree G e0 phi Q := by
    intro j hj
    let jT : Fin T.length := Fin.castLE qBound j
    obtain ⟨i, c, hedge, hmissing⟩ := N.global.2.1 jT hj
    refine ⟨i, c, ?_, ?_⟩
    · change phi (T.edge _) = some c
      convert hedge using 1
      apply congrArg phi
      apply congrArg T.edge
      apply Fin.ext
      rfl
    · change c ∈ MissingColors G phi (T.vertex _)
      convert hmissing using 1
      apply congrArg (MissingColors G phi)
      apply congrArg T.vertex
      apply Fin.ext
      rfl
  have qCard : (TreeSequenceVertexSet Q).card = Q.length + 1 := by
    simp [TreeSequenceVertexSet, Finset.card_image_of_injective,
      Q.vertex_injective]
  have qOdd : Odd (TreeSequenceVertexSet Q).card := by
    rw [qCard, qLength, hheight]
    exact (ScheideGraphHeightOdd G k e0 phi T N.global).2
  have qInitial : TreeSequenceInitialSegment (NormalTripleTrunk N) Q := by
    change TreeSequenceInitialSegment Q Q
    refine ⟨le_rfl, ?_, ?_⟩
    · intro i
      rfl
    · intro j
      rfl
  have qColors : TreeUsedColors phi Q ⊆ TreeUsedColors phi T := by
    intro c hc
    simp only [TreeUsedColors, Finset.mem_filter, Finset.mem_univ,
      true_and] at hc ⊢
    obtain ⟨j, hj, hcolor⟩ := hc
    refine ⟨Fin.castLE qBound j, hj, ?_⟩
    simpa [Q, NormalTripleTrunk, TreeSequencePrefix] using hcolor
  have qCandidate : ScheideBalancedCandidate N Q := by
    refine
      { tashkinov := qTashkinov
        oddOrder := qOdd
        exactTrunk := qInitial
        usedColors := qColors
        paired := ?_ }
    intro j hlow hupp
    omega
  have cardBound : ∀ R : TreeSequence G e0,
      (TreeSequenceVertexSet R).card ≤ Fintype.card V := by
    intro R
    exact Finset.card_le_card (Finset.subset_univ _)
  let sizes : Finset ℕ :=
    (Finset.range (Fintype.card V + 1)).filter (fun n =>
      ∃ S : TreeSequence G e0,
        ScheideBalancedCandidate N S ∧
          (TreeSequenceVertexSet S).card = n)
  have sizesNonempty : sizes.Nonempty := by
    refine ⟨(TreeSequenceVertexSet Q).card, ?_⟩
    simp only [sizes, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (cardBound Q), Q, qCandidate, rfl⟩
  let largest : ℕ := sizes.max' sizesNonempty
  have largestMem : largest ∈ sizes := Finset.max'_mem sizes sizesNonempty
  obtain ⟨S, hS, hcard⟩ := (Finset.mem_filter.mp largestMem).2
  refine ⟨S, hS, ?_⟩
  intro R hR
  have hRmem : (TreeSequenceVertexSet R).card ∈ sizes := by
    simp only [sizes, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (cardBound R), R, hR, rfl⟩
  rw [hcard]
  exact Finset.le_max' sizes _ hRmem

end GoldbergSeymour

end
