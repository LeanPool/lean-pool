/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.GapInversions
public import LeanPool.ShellsortMean.ChainCoordinates

/-! Counts of slot pairs within chains and their role in uniform mean inversion counts. -/

@[expose] public noncomputable section
namespace Shellsort
open scoped BigOperators

theorem gapPositionPairs_card_ordinal (n k : ℕ) :
    (gapPositionPairs n k).card = ∑ j : Fin n, chainOrdinal k j := by
  unfold gapPositionPairs
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type,
    Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [chainOrdinal, chainPositions, Finset.filter_filter,
    Finset.card_eq_sum_ones, Finset.sum_filter, and_comm]

theorem gapPositionPairs_card_div (n k : ℕ) (hk : 0 < k) :
    (gapPositionPairs n k).card = ∑ j : Fin n, j.val / k := by
  rw [gapPositionPairs_card_ordinal]
  apply Finset.sum_congr rfl
  intro j _
  exact chainOrdinal_eq_div k hk j

theorem sum_fin_values_real (L : ℕ) :
    (∑ v : Fin L, (v.val : ℝ)) = (L : ℝ) * ((L : ℝ) - 1) / 2 := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ih, Nat.cast_add, Nat.cast_one]
    ring

/-- Exact pair count, with every actual long/short boundary chain included. -/
theorem gapPositionPairs_card_chain_lengths (n k : ℕ) (hk : 0 < k) :
    ((gapPositionPairs n k).card : ℝ) =
      ∑ s : Fin k,
        (sourceTrialLength (n / k) (n % k) s.val : ℝ) *
          ((sourceTrialLength (n / k) (n % k) s.val : ℝ) - 1) / 2 := by
  rw [gapPositionPairs_card_div n k hk, Nat.cast_sum]
  rw [← (positionChainEquiv n k hk).symm.sum_comp]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro s _
  simp only [positionChainEquiv_symm_val]
  simp_rw [Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt s.isLt, Nat.zero_add]
  exact sum_fin_values_real (sourceTrialLength (n / k) (n % k) s.val)

/-- Actual first-pass inversion expectation: one quarter of sum L_s(L_s-1).
No equality with implementation-level shifts is asserted by this theorem. -/
theorem uniform_gapInversions_chain_lengths (n k : ℕ) (hk : 0 < k) :
    uniformAverage (fun p : RankPlacement n => (gapInversions p k : ℝ)) =
      ∑ s : Fin k,
        (sourceTrialLength (n / k) (n % k) s.val : ℝ) *
          ((sourceTrialLength (n / k) (n % k) s.val : ℝ) - 1) / 4 := by
  rw [uniform_gapInversions_half_pairs, gapPositionPairs_card_chain_lengths n k hk,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s _
  ring

end Shellsort
end
