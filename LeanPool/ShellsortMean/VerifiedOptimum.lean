/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.PredeterminedOptimum
public import LeanPool.ShellsortMean.ComparisonWordLower

/-! The same, preselected, exactly optimal word is used on every physical
array of a given size. The objective charges the executed key comparisons. -/
@[expose] public noncomputable section
namespace Shellsort.PredeterminedOptimum
open HarvestBlockIteration HarvestOperationalAudit

/-- The uniform mean of the actual array execution's key comparison count. -/
def arrayMean (n : ℕ) (w : PositiveWord) : ℝ :=
  uniformAverage fun p : RankPlacement n => ((runWord (slots p) w).2 : ℝ)

theorem arrayMean_eq (n : ℕ) (w : PositiveWord) : arrayMean n w = mean n w := by
  simp only [arrayMean, mean, runWord_slots]

private theorem bounds_for_minimizer {n : ℕ} (hn : 2 ≤ n) (w : PositiveWord)
    (hw : Legal n w) (best : ∀ v, Legal n v → mean n w ≤ mean n v) :
    Real.logb 2 (n.factorial : ℝ) ≤ arrayMean n w ∧
      arrayMean n w ≤ (1 + (2 : ℝ) ^ 165) * (n : ℝ) * Real.logb 2 n := by
  obtain ⟨v, sorted, cap, last, _, _, up⟩ :=
    HarvestFullSchedule.exists_ordinary_shellsort_word n hn
  rw [arrayMean_eq]
  exact ⟨ComparisonAudit.word_mean_lower w hw.2.2, (best v ⟨sorted, cap, last⟩).trans up⟩

/-- One family of exact minimizers over *all* legal words, with a certified
uniform two-sided cost bound. No cost bound for computing this family. -/
theorem exists_optimal_executed_family :
    ∃ W : ℕ → PositiveWord, ∀ n, 2 ≤ n →
      Legal n (W n) ∧
      (∀ p : RankPlacement n, (runWord (slots p) (W n)).1 = Vector.ofFn id) ∧
      (∀ v, Legal n v → arrayMean n (W n) ≤ arrayMean n v) ∧
      (n : ℝ) * Real.logb 2 n / 2 ≤ Real.logb 2 (n.factorial : ℝ) ∧
      Real.logb 2 (n.factorial : ℝ) ≤ arrayMean n (W n) ∧
      arrayMean n (W n) ≤ (1 + (2 : ℝ) ^ 165) * (n : ℝ) * Real.logb 2 n := by
  classical
  let W (n : ℕ) : PositiveWord :=
    if h : 2 ≤ n then Classical.choose (exists_exact_minimizer n h) else []
  refine ⟨W, fun n hn => ?_⟩
  have spec : Legal n (W n) ∧ ∀ v, Legal n v → mean n (W n) ≤ mean n v := by
    simpa only [W, dite_eq_left hn] using Classical.choose_spec (exists_exact_minimizer n hn)
  refine ⟨spec.1, ?_, ?_, ComparisonTranscriptBound.half_nlog_le_log_factorial (by omega),
    bounds_for_minimizer hn _ spec.1 spec.2⟩
  · intro p
    rw [runWord_slots, ComparisonAudit.sorted_last p _ spec.1.2.2]
    rfl
  · intro v hv
    simpa only [arrayMean_eq] using spec.2 v hv

end Shellsort.PredeterminedOptimum
