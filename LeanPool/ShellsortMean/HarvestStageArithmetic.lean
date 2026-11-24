/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module
public import Mathlib.Data.Nat.Log
public import LeanPool.ShellsortMean.Actual214Window

/-! Arithmetic for descending blocks of ten centers from the 107/50 recurrence.
Indices start at 0 for the final gap 1. -/
@[expose] public section

namespace Shellsort.HarvestStageArithmetic
open Actual214

theorem step (j : ℕ) :
    2 * gap j < gap (j + 1) ∧ gap (j + 1) ≤ 4 * gap j := by
  have b := scaled_next_bounds (gap j)
  have p := gap_pos j
  change 2 * gap j < nextGap (gap j) ∧ nextGap (gap j) ≤ _
  omega

theorem gap_strict : StrictMono gap := strictMono_nat_of_lt_succ fun i => by
  have := (step i).1
  omega

theorem lower_pow (j : ℕ) : 2 ^ j ≤ gap j := by
  induction j with
  | zero => decide
  | succ j ih => rw [pow_succ]; have := (step j).1; omega

theorem four_growth (j d : ℕ) : gap (j + d) ≤ 4 ^ d * gap j := by
  induction d with
  | zero => simp
  | succ d ih =>
    have b := (step (j + d)).2
    change gap (j + d + 1) ≤ _
    rw [pow_succ, Nat.mul_right_comm (4 ^ d) 4 (gap j)]
    omega

theorem three_growth (j d : ℕ) (large : 3 ≤ gap j) : gap (j + d) ≤ 3 ^ d * gap j := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hc := large.trans (gap_strict.monotone (Nat.le_add_right j d))
    have b := (scaled_next_bounds (gap (j + d))).2
    change nextGap (gap (j + d)) ≤ _
    rw [pow_succ, Nat.mul_right_comm (3 ^ d) 3 (gap j)]
    omega

/-- Consecutive randomized third-center indices are separated by ten. -/
theorem ten_ratio (j : ℕ) (hc : 9400 ≤ gap j) : gap (j + 10) ≤ 2 ^ 16 * gap j := by
  exact (three_growth j 10 (by omega)).trans (Nat.mul_le_mul_right _ (by decide))

/-- When the top retained gap is gap(j+2), truncation excludes gap(j+3). -/
theorem top_ratio {n j : ℕ} (last : n < 2 * gap (j + 3)) : n ≤ 2 ^ 16 * gap j := by
  have b := four_growth j 3
  norm_num at b ⊢
  omega

/-- From the unperturbed bottom i of a complete large group to its third center. -/
theorem bottom_to_center (i : ℕ) (large : 18800 ≤ gap i) :
    9400 ≤ gap (i + 7) ∧ gap (i + 7) ≤ 2 ^ 12 * gap i := by
  constructor
  · have g := gap_strict.monotone (Nat.le_add_right i 7)
    omega
  · exact (three_growth i 7 (by omega)).trans (Nat.mul_le_mul_right _ (by decide))

/-- Upper bounds on the maximum tail center and previous big-group center
when the next complete group has a small bottom center. -/
theorem complete_small_bounds (i : ℕ) (low : gap i < 18800) :
    gap (i + 9) < 2 ^ 33 ∧ gap (i + 17) < 2 ^ 49 ∧ 2 * gap (i + 10) < 2 ^ 36 := by
  have a := four_growth i 9
  have b := four_growth i 17
  have c := four_growth i 10
  norm_num at a b c ⊢
  omega

/-- With at most nine centers left, the highest has index at most eight;
the previous complete group's third center has index at most sixteen. The
weaker upper index 17 also works for merging endpoint conventions. -/
theorem short_bounds {top prev : ℕ} (short : top < 9) (prior : prev ≤ 17) :
    gap top ≤ 4 ^ 8 ∧ gap prev ≤ 4 ^ 17 ∧ 2 * gap (top + 1) ≤ 2 * 4 ^ 9 := by
  have unit (k : ℕ) : gap k ≤ 4 ^ k := by simpa [gap] using four_growth 0 k
  have a := gap_strict.monotone (show top ≤ 8 by omega)
  have b := gap_strict.monotone prior
  have c := gap_strict.monotone (show top + 1 ≤ 9 by omega)
  exact ⟨a.trans (unit 8), b.trans (unit 17), Nat.mul_le_mul_left _ (c.trans (unit 9))⟩

/-- If the tail spans indices 0 through top, it contains top+1 passes. -/
theorem tail_count {top : ℕ} (size : gap top < 2 ^ 33) : top + 1 ≤ 33 := by
  by_contra! no
  have h : 33 ≤ top := by omega
  have b : 2 ^ 33 ≤ 2 ^ top := Nat.pow_le_pow_right (by decide) h
  exact (not_lt_of_ge (b.trans (lower_pow top))) size

theorem retained_count {n top : ℕ} (kept : 2 * gap top ≤ n) : top + 1 ≤ Nat.log 2 n := by
  apply Nat.le_log_of_pow_le (by decide)
  rw [pow_succ, Nat.mul_comm]
  exact (Nat.mul_le_mul_left 2 (lower_pow top)).trans kept







end Shellsort.HarvestStageArithmetic
