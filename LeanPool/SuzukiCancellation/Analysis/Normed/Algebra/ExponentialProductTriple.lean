/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.RingTheory.PowerSeries.Noncommutative.Coefficients
public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ExponentialProduct

import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ExponentialListSeries
import LeanPool.SuzukiCancellation.RingTheory.PowerSeries.Noncommutative.ExponentialProduct

/-!
# Ordered products of three exponentials

The identity `expListTerm_triple` identifies the coefficients of the ordered list `[a, b, c]`
with those of the left-associated product. The finite-list estimates then bound its
coefficients, its tails, and the logarithm truncation error on the ball of radius `1/4`.

## Main results

* `norm_expMulMulTerm_le`, `hasSum_expMulMulTerm`: factorial coefficient bounds and summation.
* `norm_exp_mul_exp_mul_exp_sub_sum_le`: analytic tails of the product.
* `norm_log_exp_mul_exp_mul_exp_sub_sum_le`: finite homogeneous logarithm approximation.
-/

@[expose] public noncomputable section

open Finset NormedSpace

namespace FQFP

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [NormOneClass A]

/-- Each homogeneous term of a three-factor product has the scalar factorial bound. -/
lemma norm_expMulMulTerm_le (a b c : A) (n : ℕ) :
    ‖expMulMulTerm a b c n‖ ≤ (‖a‖ + ‖b‖ + ‖c‖) ^ n / Nat.factorial n := by
  simpa [expListTerm_triple, add_assoc] using norm_expListTerm_le [a, b, c] n

/-- Dropping the factorial gives a homogeneous power majorant. -/
lemma norm_expMulMulTerm_le_pow (a b c : A) (n : ℕ) :
    ‖expMulMulTerm a b c n‖ ≤ (‖a‖ + ‖b‖ + ‖c‖) ^ n := by
  simpa [expListTerm_triple, add_assoc] using norm_expListTerm_le_pow [a, b, c] n

variable [CompleteSpace A]

/-- The convolution sums to the ordered product of three exponentials. -/
lemma hasSum_expMulMulTerm (a b c : A) :
    HasSum (expMulMulTerm a b c) (exp a * exp b * exp c) := by
  simpa [funext (expListTerm_triple a b c), mul_assoc] using hasSum_expListTerm [a, b, c]

/-- Every truncation tail is bounded by the corresponding real exponential tail. -/
lemma norm_exp_mul_exp_mul_exp_sub_sum_le (a b c : A) (n : ℕ) :
    ‖exp a * exp b * exp c - ∑ i ∈ range n, expMulMulTerm a b c i‖ ≤
      Real.exp (‖a‖ + ‖b‖ + ‖c‖) -
        ∑ i ∈ range n, (‖a‖ + ‖b‖ + ‖c‖) ^ i / Nat.factorial i := by
  simpa [expListTerm_triple, mul_assoc, add_assoc] using norm_prod_exp_sub_sum_le [a, b, c] n

/-- The distance of the three-factor product from one is controlled by the scalar exponential. -/
lemma norm_exp_mul_exp_mul_exp_sub_one_le (a b c : A) :
    ‖exp a * exp b * exp c - 1‖ ≤ Real.exp (‖a‖ + ‖b‖ + ‖c‖) - 1 := by
  simpa [mul_assoc, add_assoc] using norm_prod_exp_sub_one_le [a, b, c]

/-- On the quarter-radius ball, every product tail of degree at least two is bounded by a power. -/
lemma norm_exp_mul_exp_mul_exp_sub_sum_le_pow (a b c : A) (n : ℕ) (hn : 2 ≤ n)
    (habc : ‖a‖ + ‖b‖ + ‖c‖ < 1 / 4) :
    ‖exp a * exp b * exp c - ∑ i ∈ range n, expMulMulTerm a b c i‖ ≤
      (‖a‖ + ‖b‖ + ‖c‖) ^ n := by
  simpa [expListTerm_triple, mul_assoc, add_assoc] using
    norm_prod_exp_sub_sum_le_pow [a, b, c] n hn (by simpa [add_assoc] using habc)

/-- The positive part of a small exponential product has norm at most twice the input scale. -/
lemma norm_exp_mul_exp_mul_exp_sub_one_le_two_mul (a b c : A)
    (habc : ‖a‖ + ‖b‖ + ‖c‖ < 1 / 4) :
    ‖exp a * exp b * exp c - 1‖ ≤ 2 * (‖a‖ + ‖b‖ + ‖c‖) := by
  simpa [mul_assoc, add_assoc] using
    norm_prod_exp_sub_one_le_two_mul [a, b, c] (by simpa [add_assoc] using habc)

/-- Every power of the positive product has the common homogeneous truncation bound. -/
lemma norm_exp_mul_exp_mul_exp_sub_one_pow_sub_positivePowerTrunc_le (a b c : A)
    (habc : ‖a‖ + ‖b‖ + ‖c‖ < 1 / 4) (k n : ℕ) (hkn : k < n) :
    ‖(exp a * exp b * exp c - 1) ^ k - positivePowerTrunc (expMulMulTerm a b c) k n‖ ≤
      (2 : ℝ) ^ (n - 1) * (‖a‖ + ‖b‖ + ‖c‖) ^ n := by
  simpa [funext (expListTerm_triple a b c), mul_assoc, add_assoc] using
    norm_prod_exp_sub_one_pow_sub_positivePowerTrunc_le [a, b, c]
      (by simpa [add_assoc] using habc) k n hkn

/-- The finite logarithm of the product is approximated by its homogeneous power truncations. -/
lemma norm_logPartialSum_exp_mul_exp_mul_exp_sub_sum_le (a b c : A)
    (habc : ‖a‖ + ‖b‖ + ‖c‖ < 1 / 4) (n : ℕ) :
    ‖logPartialSum A n (exp a * exp b * exp c - 1) -
      ∑ k ∈ range n, logCoeff k • positivePowerTrunc (expMulMulTerm a b c) k n‖ ≤
      (n : ℝ) * 2 ^ (n - 1) * (‖a‖ + ‖b‖ + ‖c‖) ^ n := by
  simpa [funext (expListTerm_triple a b c), mul_assoc, add_assoc] using
    norm_logPartialSum_prod_exp_sub_sum_le [a, b, c] (by simpa [add_assoc] using habc) n

/-- The logarithm of a small three-factor product has a uniform finite homogeneous approximation. -/
theorem norm_log_exp_mul_exp_mul_exp_sub_sum_le (a b c : A)
    (habc : ‖a‖ + ‖b‖ + ‖c‖ < 1 / 4) (n : ℕ) :
    ‖log (exp a * exp b * exp c) -
      ∑ k ∈ range n, logCoeff k • positivePowerTrunc (expMulMulTerm a b c) k n‖ ≤
      ((n : ℝ) * 2 ^ (n - 1) + 2 ^ (n + 1)) * (‖a‖ + ‖b‖ + ‖c‖) ^ n := by
  simpa [sum_expListLogCoeff, funext (expListTerm_triple a b c), mul_assoc, add_assoc] using
    norm_log_prod_exp_sub_sum_le [a, b, c] (by simpa [add_assoc] using habc) n

end FQFP
