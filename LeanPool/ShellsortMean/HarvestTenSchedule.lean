/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.HarvestBlockIteration
public import LeanPool.ShellsortMean.HarvestStageArithmetic

/-! The actual center truncation and the ten-center grouping in descending
execution order. Count is the number of retained zero-based centers. -/
@[expose] public section

namespace Shellsort.HarvestTenSchedule
open Actual214 HarvestBlockIteration HarvestStageArithmetic

def top (n : ℕ) := Nat.findGreatest (fun i => 2 * gap i ≤ n) n
def count (n : ℕ) := top n + 1

theorem count_positive (n : ℕ) : 0 < count n := Nat.succ_pos _

theorem top_kept {n : ℕ} (hn : 2 ≤ n) : 2 * gap (top n) ≤ n :=
  Nat.findGreatest_spec (P := fun i => 2 * gap i ≤ n) (m := 0) (Nat.zero_le n) (by simpa [gap]
    using hn)

theorem next_excluded {n : ℕ} (hn : 2 ≤ n) : n < 2 * gap (count n) := by
  have keep := top_kept hn
  have large := ((top n).lt_two_pow_self).trans_le (lower_pow (top n))
  have bounded : count n ≤ n := by unfold count; omega
  exact Nat.lt_of_not_ge (Nat.findGreatest_is_greatest
    (P := fun i => 2 * gap i ≤ n) (show top n < count n from Nat.lt_succ_self _) bounded)

theorem count_le_log {n : ℕ} (hn : 2 ≤ n) : count n ≤ Nat.log 2 n :=
  retained_count (top_kept hn)

def eligible (k : ℕ) : Prop := 10 ≤ k ∧ 18800 ≤ gap (k - 10)
instance (k : ℕ) : Decidable (eligible k) := inferInstanceAs (Decidable (_ ∧ _))

def chunk (k : ℕ) : Stage :=
  ⟨k - 3, (List.range 7).reverse.map (fun t => gap (k - 10 + t))⟩

def stages (k : ℕ) : List Stage :=
  if e : eligible k then chunk k :: stages (k - 10) else []
termination_by k
decreasing_by have := e.1; omega

def tailCount (k : ℕ) : ℕ :=
  if e : eligible k then tailCount (k - 10) else k
termination_by k
decreasing_by have := e.1; omega

theorem stages_eq (k : ℕ) : stages k =
    if eligible k then chunk k :: stages (k - 10) else [] := by
  conv_lhs => rw [stages]
  split <;> simp [*]

theorem tailCount_eq (k : ℕ) : tailCount k =
    if eligible k then tailCount (k - 10) else k := by
  conv_lhs => rw [tailCount]
  split <;> simp [*]

def tailWord (k : ℕ) := (List.range (tailCount k)).reverse.map gap

theorem counts (k : ℕ) : 10 * (stages k).length + tailCount k = k := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    rw [stages_eq, tailCount_eq]
    by_cases e : eligible k
    · have sz := e.1
      have smaller := ih (k - 10) (by omega)
      simp [e]
      omega
    · simp [e]

theorem tail_positive {k : ℕ} (hk : 0 < k) : 0 < tailCount k := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    rw [tailCount_eq]
    by_cases e : eligible k
    · have sz := e.1
      have nz : k ≠ 10 := by
        rintro rfl
        have b := e.2
        norm_num [gap] at b
      simpa [e] using ih (k - 10) (by omega) (by omega)
    · simpa [e] using hk

theorem chunk_threshold {k : ℕ} (e : eligible k) : 9400 ≤ gap (k - 3) := by
  have bound := (bottom_to_center (k - 10) e.2).1
  rw [show k - 10 + 7 = k - 3 by have := e.1; omega] at bound
  exact bound

theorem child_ratio {k : ℕ} (child : eligible (k - 10)) :
    gap (k - 3) ≤ 2 ^ 16 * gap (k - 10 - 3) := by
  have b := ten_ratio (k - 10 - 3) (chunk_threshold child)
  have sz := child.1
  rwa [show k - 10 - 3 + 10 = k - 3 by omega] at b

theorem centers_aux (k prev : ℕ) (ratio : eligible k → prev ≤ 2 ^ 16 * gap (k - 3)) :
    Centers prev (stages k) := by
  induction k using Nat.strong_induction_on generalizing prev with
  | ind k ih =>
    rw [stages_eq]
    split
    · rename_i e
      have sz := e.1
      exact ⟨chunk_threshold e, ratio e, ih (k - 10) (by omega) _ child_ratio⟩
    · trivial

theorem centers_from_size {n : ℕ} (hn : 2 ≤ n) : Centers n (stages (count n)) := by
  apply centers_aux
  intro e
  apply top_ratio
  rw [show count n - 3 + 3 = count n by have := e.1; omega]
  exact next_excluded hn

private theorem stop_count {k : ℕ} (stop : ¬eligible k) : k ≤ 33 := by
  by_cases h : 10 ≤ k
  · have low : gap (k - 10) < 18800 := Nat.lt_of_not_ge (fun large => stop ⟨h, large⟩)
    have maxgap := (complete_small_bounds _ low).1
    have bound := tail_count maxgap
    omega
  · omega

theorem tail_count_bound (k : ℕ) : tailCount k ≤ 33 := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    rw [tailCount_eq]
    split
    · rename_i e
      exact ih (k - 10) (by have := e.1; omega)
    · rename_i stop; exact stop_count stop

/-- Last chosen third center before a stopped child. -/
theorem prior_to_tail {k : ℕ} (_ : eligible k) (stop : ¬eligible (k - 10)) :
    gap (k - 3) ≤ 2 ^ 49 := by
  by_cases whole : 10 ≤ k - 10
  · have low : gap (k - 10 - 10) < 18800 := Nat.lt_of_not_ge (fun e => stop ⟨whole, e⟩)
    have b := (complete_small_bounds _ low).2.1
    rw [show k - 10 - 10 + 17 = k - 3 by omega] at b
    exact b.le
  · have small : k - 3 ≤ 17 := by omega
    have b := (short_bounds (top := 0) (by decide) small).2.1
    exact b.trans (by decide)

theorem end_aux (k prev : ℕ) (stop : ¬eligible k → prev ≤ 2 ^ 49) :
    endCenter prev (stages k) ≤ 2 ^ 49 := by
  induction k using Nat.strong_induction_on generalizing prev with
  | ind k ih =>
    rw [stages_eq]
    split
    · rename_i e
      exact ih (k - 10) (by have := e.1; omega) _ (prior_to_tail e)
    · rename_i e; exact stop e

theorem small_size {n : ℕ} (hn : 2 ≤ n) (stop : ¬eligible (count n)) : n < 2 ^ 36 := by
  have nx := next_excluded hn
  by_cases enough : 10 ≤ count n
  · have low : gap (count n - 10) < 18800 := Nat.lt_of_not_ge (fun l => stop ⟨enough, l⟩)
    have b := (complete_small_bounds _ low).2.2
    rw [show count n - 10 + 10 = count n by omega] at b
    exact nx.trans b
  · have mono := gap_strict.monotone (show count n ≤ 9 by omega)
    have ub : gap 9 ≤ 4 ^ 9 := by simpa [gap] using four_growth 0 9
    norm_num at ub ⊢
    omega

theorem end_center_bound {n : ℕ} (hn : 2 ≤ n) : endCenter n (stages (count n)) ≤ 2 ^ 49 := by
  apply end_aux
  intro stop
  exact (small_size hn stop).le.trans (by decide)







end Shellsort.HarvestTenSchedule
