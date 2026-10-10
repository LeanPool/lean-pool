/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Arithmetic.ResonanceLoss
public import Mathlib.Analysis.PSeries
public import Mathlib.Algebra.BigOperators.Intervals

/-!
Summation of new lattice shells along monotone real cutoffs, with the strict cutoff
boundaries expressed through ceiling and half-open integer intervals.
-/

@[expose] public section
noncomputable section
open scoped NNReal ENNReal
namespace KamProject.Arnold1963.Iteration

theorem shell_sum_telescope (N : ℕ → ℝ) (hN : Monotone N) (s : ℕ) :
    (∑ j ∈ Finset.range s, newShellBudget (N j) (N (j + 1))) =
      newShellBudget (N 0) (N s) := by
  induction s with
  | zero => simp [newShellBudget, newShells]
  | succ s ih =>
    rw [Finset.sum_range_succ, ih]
    exact Finset.sum_Ico_consecutive _ (Nat.ceil_mono (hN (Nat.zero_le s)))
      (Nat.ceil_mono (hN (Nat.le_succ s)))

theorem shell_budget_one_le_two (N : ℝ) : newShellBudget 1 N ≤ 2 := by
  have he : newShells 1 N = Finset.Ioo 0 ⌈N⌉₊ := by
    ext m
    simp only [newShells, Nat.ceil_one, Finset.mem_Ico, Finset.mem_Ioo]
    omega
  rw [newShellBudget, he]
  simpa only [one_div, Nat.cast_zero, zero_add, div_one] using
    (sum_Ioo_inv_sq_le (α := ℝ) 0 ⌈N⌉₊)

theorem shell_summable (N : ℕ → ℝ) (hN : Monotone N) (h0 : N 0 = 1) :
    Summable (fun s => newShellBudget (N s) (N (s + 1))) := by
  apply summable_of_sum_range_le (fun s => newShellBudget_nonneg _ _) (c := 2)
  intro s
  rw [shell_sum_telescope N hN s, h0]
  exact shell_budget_one_le_two _

theorem shell_tsum_le_two (N : ℕ → ℝ) (hN : Monotone N) (h0 : N 0 = 1) :
    (∑' s, newShellBudget (N s) (N (s + 1))) ≤ 2 := by
  apply Real.tsum_le_of_sum_range_le (fun s => newShellBudget_nonneg _ _)
  intro s
  rw [shell_sum_telescope N hN s, h0]
  exact shell_budget_one_le_two _

end KamProject.Arnold1963.Iteration
