/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Arithmetic.MultiplicativeCompletion
public import Mathlib.Algebra.Order.Ring.Star

/-! # Exponential bounds for local coefficients of a Dirichlet inverse -/

@[expose] public section

namespace NairTenenbaum

open Finset ArithmeticFunction

theorem arithmeticFunction_mul_prime_pow (f g : ArithmeticFunction ℝ)
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (f * g) (p ^ k) = ∑ j ∈ range (k + 1), f (p ^ j) * g (p ^ (k - j)) := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun d e => f d * g e), Nat.sum_divisors_prime_pow hp]
  apply sum_congr rfl
  intro j hj
  rw [Nat.pow_div (by have := mem_range.mp hj; omega) hp.pos]

theorem inverse_prime_pow_exponential_bound {f g : ArithmeticFunction ℝ}
    (hf1 : f 1 = 1) (hfg : f * g = 1) {p : ℕ} (hp : p.Prime) {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ k : ℕ, |f (p ^ k)| ≤ C ^ k) (k : ℕ) :
    |g (p ^ k)| ≤ (2 * C) ^ k := by
  have hg1 : g 1 = 1 := by
    have H := congrArg (fun a : ArithmeticFunction ℝ => a 1) hfg
    simpa only [mul_apply_one, hf1, one_mul, one_one] using H
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk : k = 0
    · simp [hk, hg1]
    have hpk : p ^ k ≠ 1 := by
      exact (one_lt_pow₀ hp.one_lt hk).ne'
    have H := congrArg (fun a : ArithmeticFunction ℝ => a (p ^ k)) hfg
    rw [mul_comm f g, arithmeticFunction_mul_prime_pow _ _ hp,
      sum_range_succ, Nat.sub_self, pow_zero, hf1, mul_one,
      one_apply_ne hpk] at H
    have hg : g (p ^ k) = -(∑ j ∈ range k, g (p ^ j) * f (p ^ (k - j))) := by linarith
    rw [hg, abs_neg]
    calc
      _ ≤ ∑ j ∈ range k, |g (p ^ j) * f (p ^ (k - j))| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ range k, (2 * C) ^ j * C ^ (k - j) := by
        apply sum_le_sum
        intro j hj
        rw [abs_mul]
        exact mul_le_mul (ih j (mem_range.mp hj)) (hf (k - j))
          (abs_nonneg _) (pow_nonneg (mul_nonneg (by norm_num) hC) _)
      _ = C ^ k * ∑ j ∈ range k, (2 : ℝ) ^ j := by
        rw [mul_sum]
        apply sum_congr rfl
        intro j hj
        rw [mul_pow]
        have Hpow := pow_sub_mul_pow C (mem_range.mp hj).le
        calc
          _ = (C ^ (k - j) * C ^ j) * 2 ^ j := by ring
          _ = _ := by rw [Hpow]
      _ ≤ C ^ k * (2 : ℝ) ^ k := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hC _)
        have Hsum := geom_sum_mul (2 : ℝ) k
        linarith
      _ = (2 * C) ^ k := by rw [mul_pow]; ring

theorem convolution_prime_pow_exponential_bound {f g : ArithmeticFunction ℝ}
    {p : ℕ} (hp : p.Prime) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ k : ℕ, |f (p ^ k)| ≤ C ^ k)
    (hg : ∀ k : ℕ, |g (p ^ k)| ≤ C ^ k) (k : ℕ) :
    |(f * g) (p ^ k)| ≤ (2 * C) ^ k := by
  rw [arithmeticFunction_mul_prime_pow _ _ hp]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ j ∈ range (k + 1), C ^ k := by
      apply sum_le_sum
      intro j hj
      rw [abs_mul]
      have H := mul_le_mul (hf j) (hg (k - j)) (abs_nonneg _) (pow_nonneg hC _)
      have hjk : j ≤ k := by have := mem_range.mp hj; omega
      simpa only [mul_comm (C ^ j), pow_sub_mul_pow C hjk] using H
    _ = (k + 1 : ℕ) * C ^ k := by simp
    _ ≤ (2 : ℝ) ^ k * C ^ k := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hC _)
      exact_mod_cast (show k + 1 ≤ 2 ^ k from Nat.lt_two_pow_self)
    _ = (2 * C) ^ k := by rw [mul_pow]

end NairTenenbaum
