/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.OrdinaryWordComparisons
public import LeanPool.ShellsortMean.RoughGapPredeterminedSelection
public import LeanPool.ShellsortMean.GapMonotone

/-! Convert a group-entry potential into a budget for the literal recursive
linear-insertion comparison counter of a supplied positive gap word. -/
@[expose] public noncomputable section
namespace Shellsort.HarvestWordCost

theorem actual_word_from_footrule {n H : ℕ} (hp : 0 < H) (p : RankPlacement n)
    (w : List {h : ℕ // 0 < h}) (lower : ∀ k ∈ w, H ≤ k.val) :
    (ordinaryWordComparisons p w : ℝ) ≤ w.length * ((n : ℝ) + 2 * footrule p / H) := by
  induction w generalizing p with
  | nil => simp [ordinaryWordComparisons]
  | cons k ks ih =>
    have hH : (0 : ℝ) < H := by exact_mod_cast hp
    have h1 : (H : ℝ) ≤ k.val := by exact_mod_cast lower k (by simp)
    have old : 0 ≤ footrule p := by unfold footrule transport; positivity
    have one : (gapComparisonCost p k.val k.property : ℝ) ≤ (n : ℝ) + 2 * footrule p / H := by
      have steps := gapInsertionCost_le_two_footrule_div p k.val k.property
      have cmp : (gapComparisonCost p k.val k.property : ℝ) ≤ (gapInsertionCost p k.val
        k.property : ℝ) + n :=
        by exact_mod_cast gapComparisonCost_upper p k.val k.property
      have small : 2 * footrule p / (k.val : ℝ) ≤ 2 * footrule p / H :=
        div_le_div_of_nonneg_left (by positivity) hH h1
      linarith only [steps, cmp, small]
    have tail := ih (gapSort p k.val) (fun i hi => lower i (List.mem_cons_of_mem _ hi))
    have fm := gapSort_footrule_le p k.val
    have tail' : (ordinaryWordComparisons (gapSort p k.val) ks : ℝ) ≤
        ks.length * ((n : ℝ) + 2 * footrule p / H) := by
      apply tail.trans
      gcongr
    simp only [ordinaryWordComparisons, Nat.cast_add, List.length_cons, Nat.cast_one, add_mul,
      one_mul]
    linarith only [one, tail']

/-- For any input-independent preprocessing P, E[Q(P)/n] ≤ (L H)^2
implies at most (1+2L)n comparisons per pass in this entire word. -/
theorem actual_word_from_square {n H : ℕ} (hn : 0 < n) (hp : 0 < H)
    (P : RankPlacement n → RankPlacement n) (w : List {h : ℕ // 0 < h})
    (lower : ∀ k ∈ w, H ≤ k.val) (L : ℝ) (lp : 0 ≤ L)
    (bound : uniformAverage (fun p => RoughGapSelection.energy (P p)) ≤ (L * H) ^ 2) :
    uniformAverage (fun p => (ordinaryWordComparisons (P p) w : ℝ)) ≤
      w.length * ((1 + 2 * L) * n) := by
  have npos : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < H := by exact_mod_cast hp
  have mass := (RoughGapSelection.prefix_mean_mass_le_root_energy hn P).trans
    ((Real.sqrt_le_sqrt bound).trans_eq (Real.sqrt_sq (by positivity)))
  have expF : uniformAverage (fun p => footrule (P p)) ≤ (L * H) * n := by
    unfold RoughGapSelection.mass at mass
    unfold uniformAverage at mass ⊢
    rw [←Finset.sum_div] at mass
    rw [div_right_comm] at mass
    exact (div_le_iff₀ npos).mp mass
  have payment (p : RankPlacement n) : (ordinaryWordComparisons (P p) w : ℝ) ≤
      w.length * ((n : ℝ) + (2 / (H : ℝ)) * footrule (P p)) := by
    apply (actual_word_from_footrule hp (P p) w lower).trans_eq
    ring
  have compare := uniformAverage_mono _ _ payment
  rw [uniformAverage_const_mul, uniformAverage_add, uniformAverage_const,
    uniformAverage_const_mul] at compare
  apply compare.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have budget := mul_le_mul_of_nonneg_left expF (show 0 ≤ 2 / (H : ℝ) by positivity)
  calc
    _ ≤ (n : ℝ) + (2 / (H : ℝ)) * (L * H * n) := add_le_add le_rfl budget
    _ = _ := by field_simp


end Shellsort.HarvestWordCost
