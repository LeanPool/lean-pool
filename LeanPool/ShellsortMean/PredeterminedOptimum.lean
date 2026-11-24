/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.HarvestFullSchedule

/-! Exact minimization for the uniform input law. Clearing its common n!
denominator turns the search over *all* legal words into minimization of a
nonempty set of natural numbers. The choice is made solely as a function of n. -/
@[expose] public noncomputable section
namespace Shellsort.PredeterminedOptimum
open HarvestBlockIteration

def Legal (n : ℕ) (w : PositiveWord) : Prop :=
  (w.map Subtype.val).Pairwise (· > ·) ∧ (∀ k ∈ w, k.val < n) ∧
    (w.map Subtype.val).getLast? = some 1

def total (n : ℕ) (w : PositiveWord) : ℕ :=
  ∑ p : RankPlacement n, ordinaryWordComparisons p w

def mean (n : ℕ) (w : PositiveWord) : ℝ :=
  uniformAverage fun p : RankPlacement n => (ordinaryWordComparisons p w : ℝ)

theorem mean_eq {n : ℕ} (w : PositiveWord) :
    mean n w = (total n w : ℝ) / n.factorial := by
  simp [mean, uniformAverage, total, Nat.cast_sum]

private theorem nonempty_prices (n : ℕ) (hn : 2 ≤ n) :
    ∃ m : ℕ, ∃ w : PositiveWord, Legal n w ∧ total n w = m := by
  let one : PositiveWord := [⟨1, by decide⟩]
  refine ⟨total n one, one, ?_, rfl⟩
  refine ⟨List.pairwise_singleton _ _, ?_, rfl⟩
  intro h hh
  have e : h = (⟨1, by decide⟩ : {k : ℕ // 0 < k}) := List.mem_singleton.mp hh
  rw [e]
  exact hn

theorem exists_exact_minimizer (n : ℕ) (hn : 2 ≤ n) :
    ∃ w, Legal n w ∧ ∀ v, Legal n v → mean n w ≤ mean n v := by
  classical
  let prices := nonempty_prices n hn
  obtain ⟨w, hw, eq⟩ := Nat.find_spec prices
  refine ⟨w, hw, fun v hv => ?_⟩
  have ble : Nat.find prices ≤ total n v := Nat.find_min' prices ⟨v, hv, rfl⟩
  rw [mean_eq, mean_eq, eq]
  exact div_le_div_of_nonneg_right (by exact_mod_cast ble) (by positivity)

end Shellsort.PredeterminedOptimum
