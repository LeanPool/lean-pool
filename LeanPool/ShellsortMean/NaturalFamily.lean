/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
Explicit finite constants for the natural three-pass family.

This module certifies the arithmetic interface in reconstruction R7.
The parameters m₁,m₂,m₃ are real numbers satisfying the displayed cost
estimates. The actual Shellsort estimates must still be proved and instantiated.
No claim of an end-to-end average-case sorting theorem is made here.
-/

@[expose] public section

namespace Shellsort

/-- An exact, executable fourth root, avoiding floating-point gap selection. -/
def fourthRoot (n : ℕ) : ℕ := Nat.sqrt (Nat.sqrt n)

theorem fourthRoot_spec (n : ℕ) :
    (fourthRoot n) ^ 4 ≤ n ∧ n < (fourthRoot n + 1) ^ 4 := by
  have h₁ : fourthRoot n ^ 2 ≤ Nat.sqrt n := Nat.sqrt_le' (Nat.sqrt n)
  have h₂ : Nat.sqrt n < (fourthRoot n + 1) ^ 2 :=
    Nat.lt_succ_sqrt' (Nat.sqrt n)
  constructor
  · calc
      fourthRoot n ^ 4 = (fourthRoot n ^ 2) ^ 2 := by ring
      _ ≤ (Nat.sqrt n) ^ 2 := by gcongr
      _ ≤ n := Nat.sqrt_le' n
  · calc
      n < (Nat.sqrt n + 1) ^ 2 := Nat.lt_succ_sqrt' n
      _ ≤ ((fourthRoot n + 1) ^ 2) ^ 2 := by
        gcongr
        omega
      _ = (fourthRoot n + 1) ^ 4 := by ring

theorem fourthRoot_ge_two (n : ℕ) (hn : 16 ≤ n) : 2 ≤ fourthRoot n := by
  unfold fourthRoot
  apply Nat.le_sqrt'.2
  apply Nat.le_sqrt'.2
  norm_num
  exact hn

theorem natural_gap_coprime (q : ℕ) : Nat.Coprime (q ^ 2 + 1) q := by
  simpa only [pow_two] using
    (Nat.coprime_mul_left_add_left 1 q q).2 (Nat.coprime_one_left q)

theorem natural_gap_legal (n : ℕ) (hn : 16 ≤ n) :
    2 ≤ fourthRoot n ∧ fourthRoot n < fourthRoot n ^ 2 + 1 ∧
      fourthRoot n ^ 2 + 1 < n := by
  have hq := fourthRoot_ge_two n hn
  have hlo := (fourthRoot_spec n).1
  have hq2 : 4 ≤ fourthRoot n ^ 2 := by nlinarith
  refine ⟨hq, ?_, ?_⟩
  · nlinarith
  · nlinarith [sq_nonneg ((fourthRoot n : ℤ) ^ 2 - 2)]

theorem natural_family_finite_bounds
    (q s m₁ m₂ m₃ : ℝ)
    (hq : 2 ≤ q) (hqs : q ^ 2 ≤ s) (hsq : s ≤ 4 * q ^ 2)
    (hm₂_nonneg : 0 ≤ m₂) (hm₃_nonneg : 0 ≤ m₃)
    (hm₁_low : s ^ 4 / (4 * (q ^ 2 + 1)) - s ^ 2 / 4 ≤ m₁)
    (hm₁_up : m₁ ≤ s ^ 4 / (4 * (q ^ 2 + 1)))
    (hm₂_up : m₂ ≤ 2 * s ^ 2 * q + s ^ 3 * Real.sqrt (q ^ 2 + 1) / q)
    (hm₃_up : m₃ ≤ s ^ 2 * (q - 1) / 2 * Real.sqrt (q ^ 2 + 4)) :
    s ^ 3 / 8 ≤ m₁ + m₂ + m₃ ∧ m₁ + m₂ + m₃ ≤ 4 * s ^ 3 := by
  have hqpos : 0 < q := by linarith only [hq]
  have hs4 : 4 ≤ s := by nlinarith only [hq, hqs, sq_nonneg (q - 2)]
  have hspos : 0 < s := by linarith only [hs4]
  have hden : 0 < 4 * (q ^ 2 + 1) := by positivity
  have h2q : 2 * q ≤ s := by nlinarith only [hq, hqs, sq_nonneg (q - 2)]
  have hh : q ^ 2 + 1 ≤ (5 / 4 : ℝ) * s := by linarith only [hs4, hqs]
  have hsqrt1 : Real.sqrt (q ^ 2 + 1) ≤ 5 * q / 4 := by
    apply (Real.sqrt_le_left (by positivity)).2
    nlinarith only [hq, sq_nonneg (q - 2)]
  have hsqrt4 : Real.sqrt (q ^ 2 + 4) ≤ 3 * q / 2 := by
    apply (Real.sqrt_le_left (by positivity)).2
    nlinarith only [hq, sq_nonneg (q - 2)]
  have hfirst_up : s ^ 4 / (4 * (q ^ 2 + 1)) ≤ s ^ 3 := by
    apply (div_le_iff₀ hden).2
    have hle : s ≤ 4 * (q ^ 2 + 1) := by linarith only [hsq]
    have hm := mul_le_mul_of_nonneg_right hle (show 0 ≤ s ^ 3 by positivity)
    nlinarith only [hm]
  have hfirst_low : s ^ 3 / 5 ≤ s ^ 4 / (4 * (q ^ 2 + 1)) := by
    apply (le_div_iff₀ hden).2
    have hm := mul_le_mul_of_nonneg_left hh
      (show 0 ≤ 4 * s ^ 3 / 5 by positivity)
    nlinarith only [hm]
  have hsecond_a : 2 * s ^ 2 * q ≤ s ^ 3 := by
    have hm := mul_le_mul_of_nonneg_left h2q (sq_nonneg s)
    nlinarith only [hm]
  have hsecond_b : s ^ 3 * Real.sqrt (q ^ 2 + 1) / q ≤ (5 / 4 : ℝ) * s ^ 3 := by
    apply (div_le_iff₀ hqpos).2
    have hm := mul_le_mul_of_nonneg_left hsqrt1 (show 0 ≤ s ^ 3 by positivity)
    nlinarith only [hm]
  have hthird : m₃ ≤ (3 / 4 : ℝ) * s ^ 3 := by
    calc
      m₃ ≤ s ^ 2 * (q - 1) / 2 * Real.sqrt (q ^ 2 + 4) := hm₃_up
      _ ≤ s ^ 2 * q / 2 * (3 * q / 2) := by
        gcongr
        · linarith only [hq]
      _ = (3 / 4 : ℝ) * s ^ 2 * q ^ 2 := by ring
      _ ≤ (3 / 4 : ℝ) * s ^ 2 * s := by
        exact mul_le_mul_of_nonneg_left hqs (by positivity)
      _ = (3 / 4 : ℝ) * s ^ 3 := by ring
  constructor
  · have hm := mul_nonneg (sq_nonneg s) (show 0 ≤ s - 4 by linarith only [hs4])
    nlinarith only [hm, hm₁_low, hfirst_low, hm₂_nonneg, hm₃_nonneg]
  · linarith only [hm₁_up, hm₂_up, hm₃_up, hfirst_up, hsecond_a, hsecond_b, hthird]

/-- The integer root interval supplies the numerical hypotheses above.
This is a real arithmetic implication, independent of cost assumptions. -/
theorem natural_family_scale
    (q n : ℝ) (hq : 2 ≤ q) (hn_low : q ^ 4 ≤ n)
    (hn_high : n < (q + 1) ^ 4) :
    q ^ 2 ≤ Real.sqrt n ∧ Real.sqrt n ≤ 4 * q ^ 2 := by
  have hn : 0 ≤ n := le_trans (by positivity : 0 ≤ q ^ 4) hn_low
  have hlo : q ^ 2 ≤ Real.sqrt n := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hhi : Real.sqrt n ≤ (q + 1) ^ 2 := by
    apply (Real.sqrt_le_left (sq_nonneg (q + 1))).2
    nlinarith
  constructor
  · exact hlo
  · nlinarith [sq_nonneg (q - 2)]

end Shellsort
