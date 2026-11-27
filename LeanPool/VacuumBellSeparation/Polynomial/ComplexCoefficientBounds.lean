/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Polynomial.Selector
import Mathlib.Tactic.Positivity
public import Mathlib.Analysis.Complex.Basic

/-!
# Complex evaluation bounds from the actual real coefficient sum

These are the quantitative tools for the disconnected-support selectors
in manuscript Section 7. The same real polynomials are evaluated at
complex points; no alternative selector is introduced.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation

open Polynomial

/-- Complex polynomial eval obtained from `p.eval₂`. -/
def complexPolynomialEval (p : ℝ[X]) (z : ℂ) : ℂ := p.eval₂ (algebraMap ℝ ℂ) z

theorem complexPolynomialEval_sum (p : ℝ[X]) (z : ℂ) :
    complexPolynomialEval p z =
      ∑ i ∈ Finset.range (p.natDegree + 1), (p.coeff i : ℂ) * z ^ i := by
  exact Polynomial.eval₂_eq_sum_range (algebraMap ℝ ℂ) z

theorem norm_complexPolynomialEval_le (p : ℝ[X]) (z : ℂ) :
    ‖complexPolynomialEval p z‖ ≤ coeffAbsSum p * max 1 ‖z‖ ^ p.natDegree := by
  rw [complexPolynomialEval_sum, coeffAbsSum, Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact (pow_le_pow_left₀ (norm_nonneg z) (le_max_right _ _) i).trans
    (pow_le_pow_right₀ (le_max_left _ _) (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))

theorem norm_complexPolynomialEval_zero_order_le (p : ℝ[X]) (N : ℕ)
    (hcoeff : ∀ i < N, p.coeff i = 0) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖complexPolynomialEval p z‖ ≤ coeffAbsSum p * ‖z‖ ^ N := by
  rw [complexPolynomialEval_sum, coeffAbsSum, Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  by_cases hin : i < N
  · simp only [hcoeff i hin, Complex.ofReal_zero, zero_mul, norm_zero, abs_zero, le_refl]
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one (norm_nonneg z) hz (Nat.le_of_not_gt hin)) (abs_nonneg _)

theorem coeffAbsSum_sub_one_le (p : ℝ[X]) : coeffAbsSum (p - 1) ≤ coeffAbsSum p + 1 := by
  have h := coeffAbsSum_add_le p (C (-1))
  rw [coeffAbsSum_C] at h
  simpa only [map_neg, map_one, ← sub_eq_add_neg, abs_neg, abs_one] using h

theorem norm_complexSelector_near_zero (N : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖complexPolynomialEval (selector N) z - 1‖ ≤ (8 ^ N + 1) * ‖z‖ ^ N := by
  have hzero : ∀ i < N, (selector N - 1).coeff i = 0 := by
    intro i hi
    rw [coeff_sub, coeff_selector_of_lt hi, coeff_one]
    split_ifs <;> simp
  have hb := norm_complexPolynomialEval_zero_order_le (selector N - 1) N hzero hz
  have he : complexPolynomialEval (selector N - 1) z = complexPolynomialEval
    (selector N) z - 1 := by
    simp [complexPolynomialEval]
  rw [he] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right
    ((coeffAbsSum_sub_one_le _).trans (by linarith [coeffAbsSum_selector_le N]))
    (pow_nonneg (norm_nonneg z) N))

theorem norm_complexSelector_global (N : ℕ) (z : ℂ) :
    ‖complexPolynomialEval (selector N) z‖ ≤ (8 * max 1 ‖z‖ ^ 2) ^ N := by
  apply (norm_complexPolynomialEval_le _ _).trans
  calc
    _ ≤ 8 ^ N * max 1 ‖z‖ ^ (2 * N) :=
      mul_le_mul (coeffAbsSum_selector_le N)
        (pow_le_pow_right₀ (le_max_left _ _)
          ((selector_natDegree_le N).trans (Nat.sub_le _ _)))
        (by positivity) (by positivity)
    _ = _ := by rw [mul_pow, ← pow_mul]

end VacuumBellSeparation
