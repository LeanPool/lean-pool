/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Polynomial.ComplexCoefficientBounds

/-! # Quantitative complex selector bounds at both components -/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation

open Polynomial

theorem complexSelector_factor (N : ℕ) (z : ℂ) :
    complexPolynomialEval (selector N) z =
      (1 - z) ^ N * ∑ k ∈ Finset.range N,
        (((N + k - 1).choose k : ℕ) : ℂ) * z ^ k := by
  simp [complexPolynomialEval, selector, eval₂_finsetSum]

theorem norm_complexSelector_truncated_series (N : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 2) :
    ‖∑ k ∈ Finset.range N, (((N + k - 1).choose k : ℕ) : ℂ) * z ^ k‖ ≤ 8 ^ N := by
  calc
    _ ≤ ∑ k ∈ Finset.range N, ‖(((N + k - 1).choose k : ℕ) : ℂ) * z ^ k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range N, ((N + k - 1).choose k : ℝ) * 2 ^ N := by
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_mul, Complex.norm_natCast, norm_pow]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact (pow_le_pow_left₀ (norm_nonneg z) hz k).trans
        (pow_le_pow_right₀ (by norm_num) (Nat.le_of_lt (Finset.mem_range.mp hk)))
    _ = (∑ k ∈ Finset.range N, ((N + k - 1).choose k : ℝ)) * 2 ^ N :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ 4 ^ N * 2 ^ N := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast sum_choose_le_four_pow N
    _ = 8 ^ N := by rw [← mul_pow]; norm_num

theorem norm_complexSelector_near_one (N : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 2) :
    ‖complexPolynomialEval (selector N) z‖ ≤ 8 ^ N * ‖1 - z‖ ^ N := by
  rw [complexSelector_factor, norm_mul, norm_pow]
  exact (mul_le_mul_of_nonneg_left (norm_complexSelector_truncated_series N hz)
    (by positivity)).trans_eq (mul_comm _ _)

theorem norm_complexSelector_on_two_ball (N : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 2) :
    ‖complexPolynomialEval (selector N) z‖ ≤ 32 ^ N := by
  apply (norm_complexSelector_global N z).trans
  have hmax : max 1 ‖z‖ ≤ (2 : ℝ) := max_le (by norm_num) hz
  have hs := pow_le_pow_left₀ (le_trans zero_le_one (le_max_left 1 ‖z‖)) hmax 2
  have hbase : 8 * max 1 ‖z‖ ^ 2 ≤ (32 : ℝ) := by norm_num at hs; nlinarith
  exact pow_le_pow_left₀ (by positivity) hbase N

theorem norm_complexSelector_near_zero_geometric (N : ℕ) {z : ℂ} {δ : ℝ}
    (hz : ‖z‖ ≤ δ) (hδ : δ ≤ 1) :
    ‖complexPolynomialEval (selector N) z - 1‖ ≤ 2 * (8 * δ) ^ N := by
  have hδ₀ : 0 ≤ δ := (norm_nonneg z).trans hz
  have hpow : (1 : ℝ) ≤ 8 ^ N := one_le_pow₀ (by norm_num)
  calc
    _ ≤ (8 ^ N + 1) * ‖z‖ ^ N := norm_complexSelector_near_zero N (hz.trans hδ)
    _ ≤ (2 * 8 ^ N) * δ ^ N := mul_le_mul (by linarith)
      (pow_le_pow_left₀ (norm_nonneg z) hz N) (by positivity) (by positivity)
    _ = _ := by rw [mul_pow]; ring

theorem norm_complexSelector_product_wrong_component (N : ℕ) {u v : ℂ} {δ : ℝ}
    (hu : ‖u‖ ≤ 2) (hv : ‖v‖ ≤ 2) (hzero : ‖1 - u‖ ≤ δ) :
    ‖complexPolynomialEval (selector N) u * complexPolynomialEval (selector N) v‖ ≤
      (256 * δ) ^ N := by
  rw [norm_mul]
  have hδ : 0 ≤ δ := (norm_nonneg (1 - u)).trans hzero
  calc
    _ ≤ (8 ^ N * ‖1 - u‖ ^ N) * 32 ^ N :=
      mul_le_mul (norm_complexSelector_near_one N hu) (norm_complexSelector_on_two_ball N hv)
        (norm_nonneg _) (by positivity)
    _ ≤ (8 ^ N * δ ^ N) * 32 ^ N := by gcongr
    _ = _ := by simp only [← mul_pow]; congr 1; ring

end VacuumBellSeparation
