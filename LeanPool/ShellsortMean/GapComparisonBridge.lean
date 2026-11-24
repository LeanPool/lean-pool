/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.InsertionComparisons
public import LeanPool.ShellsortMean.GapInsertionOutput

/-! The executed comparison count and its relationship to shifts inside gap chains. -/

@[expose] public noncomputable section
namespace Shellsort
open scoped BigOperators

/-- Actual key-comparison counter of the linear insertion execution on each chain. -/
def gapComparisonCost {n : ℕ} (p : RankPlacement n) (k : ℕ) (hk : 0 < k) : ℕ :=
  ∑ s : Fin k, (insertionComparedExecution (List.ofFn (chainKeys p k hk s))).comparisons

theorem gapCompared_chain_eq_gapSort {n : ℕ} (p : RankPlacement n) (k : ℕ)
    (hk : 0 < k) (s : Fin k) :
    (insertionComparedExecution (List.ofFn (chainKeys p k hk s))).output =
      List.ofFn (chainKeys (gapSort p k) k hk s) := by
  rw [insertionComparedExecution_output, insertionExecution_chain_eq_gapSort]

theorem sum_actual_chain_lengths (n k : ℕ) (hk : 0 < k) :
    (∑ s : Fin k, sourceTrialLength (n / k) (n % k) s.val) = n := by
  have hc := Fintype.card_congr (positionChainEquiv n k hk)
  simpa only [Fintype.card_fin, Fintype.card_sigma] using hc.symm

theorem gapComparisonCost_lower {n : ℕ} (p : RankPlacement n) (k : ℕ) (hk : 0 < k) :
    gapInsertionCost p k hk ≤ gapComparisonCost p k hk := by
  apply Finset.sum_le_sum
  intro s _
  exact (insertionComparedExecution_bounds (List.ofFn (chainKeys p k hk s))).1

/-- The sharper finite overhead is the sum of L_s-1 over nonempty chains. -/
theorem gapComparisonCost_upper_chains {n : ℕ} (p : RankPlacement n) (k : ℕ) (hk : 0 < k) :
    gapComparisonCost p k hk ≤ gapInsertionCost p k hk +
      ∑ s : Fin k, (sourceTrialLength (n / k) (n % k) s.val - 1) := by
  unfold gapComparisonCost gapInsertionCost
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro s _
  simpa only [List.length_ofFn] using
    (insertionComparedExecution_bounds (List.ofFn (chainKeys p k hk s))).2

/-- Uniform over all inputs and all positive gaps, including empty physical chains. -/
theorem gapComparisonCost_upper {n : ℕ} (p : RankPlacement n) (k : ℕ) (hk : 0 < k) :
    gapComparisonCost p k hk ≤ gapInsertionCost p k hk + n := by
  apply (gapComparisonCost_upper_chains p k hk).trans
  apply Nat.add_le_add_left
  calc
    _ ≤ ∑ s : Fin k, sourceTrialLength (n / k) (n % k) s.val :=
      Finset.sum_le_sum (fun _ _ => Nat.sub_le _ _)
    _ = n := sum_actual_chain_lengths n k hk

end Shellsort
end
