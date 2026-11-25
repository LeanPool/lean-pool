/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ExponentialListBounds

import LeanPool.SuzukiCancellation.RingTheory.PowerSeries.Noncommutative.ExponentialProduct

/-!
# Exponential product series and truncation bounds

The coefficient identity for `[a, b]` specializes the finite-list estimates to `exp a * exp b`.

## Main results

* `FQFP.norm_expMulTerm_le`.
* `FQFP.hasSum_expMulTerm`.
* `FQFP.norm_exp_mul_exp_sub_sum_le`.
* `FQFP.norm_exp_mul_exp_sub_quadratic_le`.
* `FQFP.norm_exp_mul_exp_sub_one_pow_sub_positivePowerTrunc_le`.
* `FQFP.norm_logPartialSum_sub_sum_positivePowerTrunc_le`.
* `FQFP.norm_logPartialSum_sub_sum_positivePowerTrunc_le_weighted`.
-/

@[expose] public noncomputable section
open Finset NormedSpace
namespace FQFP

private lemma sum_norm_pair_lt_quarter {B : Type*} [Norm B] {a b : B}
    (hab : ‖a‖ + ‖b‖ < 1 / 10) : ([a, b].map norm).sum < 1 / 4 := by
  simpa using hab.trans (by norm_num : (1 : ℝ) / 10 < 1 / 4)

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [NormOneClass A]

/-- A homogeneous exponential product term is bounded by the corresponding scalar term. -/
lemma norm_expMulTerm_le (a b : A) (n : ℕ) :
    ‖expMulTerm a b n‖ ≤ (‖a‖ + ‖b‖) ^ n / Nat.factorial n := by
  simpa [expListTerm_pair] using norm_expListTerm_le [a, b] n

/-- Dropping the factorial gives a convenient homogeneous power bound. -/
lemma norm_expMulTerm_le_pow (a b : A) (n : ℕ) :
    ‖expMulTerm a b n‖ ≤ (‖a‖ + ‖b‖) ^ n := by
  simpa [expListTerm_pair] using norm_expListTerm_le_pow [a, b] n

variable [CompleteSpace A]

/-- The homogeneous factorial convolution sums to the ordered exponential product. -/
lemma hasSum_expMulTerm (a b : A) : HasSum (expMulTerm a b) (exp a * exp b) := by
  simpa [funext (expListTerm_pair a b)] using hasSum_expListTerm [a, b]

/-- Every exponential product truncation is bounded by the real exponential tail. -/
lemma norm_exp_mul_exp_sub_sum_le (a b : A) (n : ℕ) :
    ‖exp a * exp b - ∑ i ∈ range n, expMulTerm a b i‖ ≤
      Real.exp (‖a‖ + ‖b‖) - ∑ i ∈ range n,
        (‖a‖ + ‖b‖) ^ i / Nat.factorial i := by
  simpa [expListTerm_pair] using norm_prod_exp_sub_sum_le [a, b] n

/-- The error after the quadratic part of an exponential product is bounded by the real tail. -/
lemma norm_exp_mul_exp_sub_quadratic_le (a b : A) :
    ‖exp a * exp b - 1 - (a + b) -
      (a * b + (2 : ℚ)⁻¹ • a ^ 2 + (2 : ℚ)⁻¹ • b ^ 2)‖ ≤
      Real.exp (‖a‖ + ‖b‖) - 1 - (‖a‖ + ‖b‖) - (‖a‖ + ‖b‖) ^ 2 / 2 := by
  simpa [sum_range_succ, expMulTerm_two, Nat.factorial, sub_eq_add_neg,
    div_eq_mul_inv, add_comm, add_left_comm, add_assoc] using
      norm_exp_mul_exp_sub_sum_le a b 3

/-- In the small-norm region, every tail of order at least two is bounded by its power. -/
lemma norm_exp_mul_exp_sub_sum_le_pow (a b : A) (n : ℕ) (hn : 2 ≤ n)
    (hab : ‖a‖ + ‖b‖ < 1 / 10) :
    ‖exp a * exp b - ∑ i ∈ range n, expMulTerm a b i‖ ≤ (‖a‖ + ‖b‖) ^ n := by
  simpa [expListTerm_pair] using
    norm_prod_exp_sub_sum_le_pow [a, b] n hn (sum_norm_pair_lt_quarter hab)

/-- Every power of the positive exponential product has a uniform homogeneous tail bound. -/
lemma norm_exp_mul_exp_sub_one_pow_sub_positivePowerTrunc_le (a b : A)
    (hab : ‖a‖ + ‖b‖ < 1 / 10) (k n : ℕ) (hkn : k < n) :
    ‖(exp a * exp b - 1) ^ k - positivePowerTrunc (expMulTerm a b) k n‖ ≤
      (2 : ℝ) ^ (n - 1) * (‖a‖ + ‖b‖) ^ n := by
  simpa [funext (expListTerm_pair a b)] using
    norm_prod_exp_sub_one_pow_sub_positivePowerTrunc_le [a, b]
      (sum_norm_pair_lt_quarter hab) k n hkn

/-- Retaining coefficient norms gives a weighted bound for the finite logarithm error. -/
lemma norm_logPartialSum_sub_sum_positivePowerTrunc_le_weighted (a b : A)
    (hab : ‖a‖ + ‖b‖ < 1 / 10) (n : ℕ) :
    ‖logPartialSum A n (exp a * exp b - 1) -
      ∑ k ∈ range n, logCoeff k • positivePowerTrunc (expMulTerm a b) k n‖ ≤
      (∑ k ∈ range n, ‖logCoeff k‖) * 2 ^ (n - 1) * (‖a‖ + ‖b‖) ^ n := by
  simpa [funext (expListTerm_pair a b)] using
    norm_logPartialSum_prod_exp_sub_sum_le_weighted [a, b] (sum_norm_pair_lt_quarter hab) n

/-- The finite logarithm error is controlled uniformly by homogeneous power tails. -/
lemma norm_logPartialSum_sub_sum_positivePowerTrunc_le (a b : A)
    (hab : ‖a‖ + ‖b‖ < 1 / 10) (n : ℕ) :
    ‖logPartialSum A n (exp a * exp b - 1) -
      ∑ k ∈ range n, logCoeff k • positivePowerTrunc (expMulTerm a b) k n‖ ≤
      (n : ℝ) * 2 ^ (n - 1) * (‖a‖ + ‖b‖) ^ n := by
  simpa [funext (expListTerm_pair a b)] using
    norm_logPartialSum_prod_exp_sub_sum_le [a, b] (sum_norm_pair_lt_quarter hab) n

end FQFP
