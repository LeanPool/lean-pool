/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.ListInversionPairs
public import LeanPool.ShellsortMean.GapInversions
public import LeanPool.ShellsortMean.GapPairCount
public import LeanPool.ShellsortMean.ChainCoordinates

/-! Exact insertion cost identities for the lists of ranks in each gap chain. -/

@[expose] public noncomputable section
namespace Shellsort
open scoped BigOperators

/-- The actual key ranks encountered along one physical gap chain. -/
def chainKeys {n : ℕ} (p : RankPlacement n) (k : ℕ) (hk : 0 < k) (s : Fin k) :
    Fin (sourceTrialLength (n / k) (n % k) s.val) → Fin n :=
  fun v => p.symm ((positionChainEquiv n k hk).symm ⟨s, v⟩)

/-- Execute the defined insertion routine independently on every actual chain,
and add its successful-right-shift counters. -/
def gapInsertionCost {n : ℕ} (p : RankPlacement n) (k : ℕ) (hk : 0 < k) : ℕ :=
  ∑ s : Fin k, (insertionExecution (List.ofFn (chainKeys p k hk s))).2

theorem chainPosition_lt_iff (n k : ℕ) (hk : 0 < k) (s : Fin k)
    (v w : Fin (sourceTrialLength (n / k) (n % k) s.val)) :
    (positionChainEquiv n k hk).symm ⟨s, v⟩ <
      (positionChainEquiv n k hk).symm ⟨s, w⟩ ↔ v < w := by
  change s.val + k * v.val < s.val + k * w.val ↔ v.val < w.val
  rw [Nat.add_lt_add_iff_left, Nat.mul_lt_mul_left hk]

theorem sum_positions_by_chains {β : Type*} [AddCommMonoid β]
    (n k : ℕ) (hk : 0 < k) (f : Fin n → β) :
    (∑ i : Fin n, f i) =
      ∑ s : Fin k, ∑ v : Fin (sourceTrialLength (n / k) (n % k) s.val),
        f ((positionChainEquiv n k hk).symm ⟨s, v⟩) := by
  rw [← (positionChainEquiv n k hk).symm.sum_comp]
  exact Fintype.sum_sigma _

theorem gapInversions_nat_pair_sum {n : ℕ} (p : RankPlacement n) (k : ℕ) :
    gapInversions p k = ∑ j : Fin n, ∑ i : Fin n,
      if (i < j ∧ i.val % k = j.val % k) ∧ p.symm j < p.symm i then 1 else 0 := by
  unfold gapInversions gapPositionPairs
  rw [Finset.filter_filter, Finset.card_eq_sum_ones, Finset.sum_filter,
    Fintype.sum_prod_type, Finset.sum_comm]

/-- The independently executed insertion counters equal the existing actual
gap inversion statistic, for every input placement and every positive gap. -/
theorem gapInsertionCost_eq_gapInversions {n : ℕ} (p : RankPlacement n)
    (k : ℕ) (hk : 0 < k) :
    gapInsertionCost p k hk = gapInversions p k := by
  unfold gapInsertionCost
  simp_rw [insertionExecution_ofFn_count]
  rw [gapInversions_nat_pair_sum, sum_positions_by_chains n k hk]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro v _
  rw [sum_positions_by_chains n k hk]
  simp only [positionChainEquiv_symm_residue]
  rw [Finset.sum_eq_single s]
  · apply Finset.sum_congr rfl
    intro w _
    simp only [and_true, chainPosition_lt_iff, chainKeys]
    rfl
  · intro t _ hts
    apply Finset.sum_eq_zero
    intro w _
    have hval : t.val ≠ s.val := fun he => hts (Fin.ext he)
    simp only [hval, and_false, false_and, ite_false]
  · intro hs
    exact False.elim (hs (Finset.mem_univ s))

/-- Consequently the exact uniform first-pass expectation is now an execution
counter theorem, not only an inversion-statistic theorem. -/
theorem uniform_gapInsertionCost_half_pairs (n k : ℕ) (hk : 0 < k) :
    uniformAverage (fun p : RankPlacement n => (gapInsertionCost p k hk : ℝ)) =
      ((gapPositionPairs n k).card : ℝ) / 2 := by
  simp only [gapInsertionCost_eq_gapInversions]
  exact uniform_gapInversions_half_pairs n k

theorem uniform_gapInsertionCost_chain_lengths (n k : ℕ) (hk : 0 < k) :
    uniformAverage (fun p : RankPlacement n => (gapInsertionCost p k hk : ℝ)) =
      ∑ s : Fin k,
        (sourceTrialLength (n / k) (n % k) s.val : ℝ) *
          ((sourceTrialLength (n / k) (n % k) s.val : ℝ) - 1) / 4 := by
  simp only [gapInsertionCost_eq_gapInversions]
  exact uniform_gapInversions_chain_lengths n k hk

end Shellsort
end
