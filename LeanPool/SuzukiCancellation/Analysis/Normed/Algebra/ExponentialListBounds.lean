/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Nat.Choose.Cast
public import LeanPool.SuzukiCancellation.RingTheory.PowerSeries.Noncommutative.ExponentialListCoefficients
public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ExponentialList
public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.Logarithm
public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.PowerTruncation

/-!
# Coefficient and truncation bounds for ordered exponential products

The sum of the argument norms bounds the Cauchy coefficients and tails of any finite
ordered product of exponentials. On the quarter-radius ball these estimates also bound
the error from truncating the homogeneous powers in a finite logarithm polynomial.
-/

@[expose] public noncomputable section

open Finset Finset.Nat NormedSpace

namespace FQFP

/-- The scalar factorial convolution is the coefficient of the exponential at a sum. -/
lemma factorial_convolution (x y : ℝ) (n : ℕ) :
    (∑ ij ∈ antidiagonal n, (x ^ ij.1 / Nat.factorial ij.1) *
      (y ^ ij.2 / Nat.factorial ij.2)) = (x + y) ^ n / Nat.factorial n := by
  rw [(Commute.all x y).add_pow' n, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ij hij
  have h := mem_antidiagonal.mp hij
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_eq_mul, ← h, Nat.cast_add_choose]
  field_simp

/-- Uniform power-truncation errors control the corresponding finite logarithm. -/
lemma norm_logPartialSum_sub_sum_positivePowerTrunc_le_of_pow
    {B : Type*} [NormedRing B] [NormedAlgebra ℚ B]
    (y : B) (u : ℕ → B) (n : ℕ) {M : ℝ}
    (h : ∀ k < n, ‖y ^ k - positivePowerTrunc u k n‖ ≤ M) :
    ‖logPartialSum B n y - ∑ k ∈ range n, logCoeff k • positivePowerTrunc u k n‖ ≤
      (∑ k ∈ range n, ‖logCoeff k‖) * M := by
  rw [logPartialSum, ← sum_sub_distrib]
  simp only [← smul_sub]
  calc
    _ ≤ ∑ k ∈ range n, ‖logCoeff k • (y ^ k - positivePowerTrunc u k n)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ k ∈ range n, ‖logCoeff k‖ * M := by
      apply sum_le_sum
      intro k hk
      exact (norm_smul_le _ _).trans
        (mul_le_mul_of_nonneg_left (h k (mem_range.mp hk)) (norm_nonneg _))
    _ = _ := (sum_mul ..).symm

/-- The absolute coefficient sum of a finite logarithm is at most its cutoff. -/
lemma sum_norm_logCoeff_le (n : ℕ) : (∑ k ∈ range n, ‖logCoeff k‖) ≤ (n : ℝ) := by
  calc
    _ ≤ ∑ _k ∈ range n, (1 : ℝ) := sum_le_sum fun k _ ↦ norm_logCoeff_le_one k
    _ = _ := by simp

/-- A finite sum of norms is nonnegative. -/
lemma list_sum_norm_nonneg {B : Type*} [SeminormedAddGroup B] (l : List B) :
    0 ≤ (l.map norm).sum := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
  exact norm_nonneg a

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [NormOneClass A]

/-- Every list coefficient is bounded by the corresponding scalar exponential coefficient. -/
lemma norm_expListTerm_le (l : List A) (n : ℕ) :
    ‖expListTerm l n‖ ≤ (l.map norm).sum ^ n / Nat.factorial n := by
  induction l generalizing n with
  | nil => by_cases hn : n = 0 <;> simp [expListTerm, hn]
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, expListTerm]
      refine (norm_sum_le _ _).trans ?_
      rw [← factorial_convolution]
      exact sum_le_sum fun ij _ ↦ norm_mul_le_of_le (norm_exp_term_le a ij.1) (ih ij.2)

/-- Dropping the factorial gives a homogeneous power bound. -/
lemma norm_expListTerm_le_pow (l : List A) (n : ℕ) :
    ‖expListTerm l n‖ ≤ (l.map norm).sum ^ n := by
  have hf : (1 : ℝ) ≤ Nat.factorial n := by exact_mod_cast Nat.factorial_pos n
  exact (norm_expListTerm_le l n).trans (div_le_self (pow_nonneg (list_sum_norm_nonneg l) n) hf)

variable [CompleteSpace A]

/-- The factorial convolution coefficients sum to the ordered exponential product. -/
lemma hasSum_expListTerm (l : List A) :
    HasSum (expListTerm l) (l.map exp).prod := by
  induction l with
  | nil =>
      simpa only [expListTerm, List.map_nil, List.prod_nil] using
        (hasSum_ite_eq (0 : ℕ) (1 : A))
  | cons a l ih =>
      have ha : Summable fun i : ℕ ↦ ‖(Nat.factorial i : ℚ)⁻¹ • a ^ i‖ :=
        (Real.summable_pow_div_factorial ‖a‖).of_nonneg_of_le
          (fun _ ↦ norm_nonneg _) (norm_exp_term_le a)
      have hl : Summable fun i : ℕ ↦ ‖expListTerm l i‖ :=
        (Real.summable_pow_div_factorial ((l.map norm).sum)).of_nonneg_of_le
          (fun _ ↦ norm_nonneg _) (norm_expListTerm_le l)
      have hs := summable_norm_sum_mul_antidiagonal_of_summable_norm ha hl
      simp only [List.map_cons, List.prod_cons]
      change HasSum (fun n ↦ ∑ ij ∈ antidiagonal n,
        ((Nat.factorial ij.1 : ℚ)⁻¹ • a ^ ij.1) * expListTerm l ij.2) _
      rw [hs.of_norm.hasSum_iff]
      exact (tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm ha hl).symm.trans
        (by
          rw [ih.tsum_eq]
          simp only [exp_eq_tsum_rat])

/-- Every product tail is bounded by the corresponding real exponential tail. -/
lemma norm_prod_exp_sub_sum_le (l : List A) (n : ℕ) :
    ‖(l.map exp).prod - ∑ i ∈ range n, expListTerm l i‖ ≤
      Real.exp ((l.map norm).sum) -
        ∑ i ∈ range n, (l.map norm).sum ^ i / Nat.factorial i :=
  norm_sub_sum_le_real_exp_tail _ _ _ (hasSum_expListTerm l) (norm_expListTerm_le l) n

/-- Every tail of degree at least two is bounded by its scale power on the quarter ball. -/
lemma norm_prod_exp_sub_sum_le_pow (l : List A) (n : ℕ) (hn : 2 ≤ n)
    (hl : (l.map norm).sum < 1 / 4) :
    ‖(l.map exp).prod - ∑ i ∈ range n, expListTerm l i‖ ≤ (l.map norm).sum ^ n := by
  exact (norm_prod_exp_sub_sum_le l n).trans
    (real_exp_sub_sum_le_pow (list_sum_norm_nonneg l) (by linarith only [hl]) n hn)

/-- The positive product part has norm at most twice the total argument norm. -/
lemma norm_prod_exp_sub_one_le_two_mul (l : List A)
    (hl : (l.map norm).sum < 1 / 4) :
    ‖(l.map exp).prod - 1‖ ≤ 2 * (l.map norm).sum :=
  (norm_prod_exp_sub_one_le l).trans
    (real_exp_sub_one_le_two_mul (list_sum_norm_nonneg l) (by linarith only [hl]))

/-- Every power of the positive product has the common homogeneous tail bound. -/
lemma norm_prod_exp_sub_one_pow_sub_positivePowerTrunc_le (l : List A)
    (hl : (l.map norm).sum < 1 / 4) (k n : ℕ) (hkn : k < n) :
    ‖((l.map exp).prod - 1) ^ k - positivePowerTrunc (expListTerm l) k n‖ ≤
      (2 : ℝ) ^ (n - 1) * (l.map norm).sum ^ n := by
  apply norm_pow_sub_positivePowerTrunc_le _ _ (list_sum_norm_nonneg l)
    (norm_prod_exp_sub_one_le_two_mul l hl) k n hkn
    (fun i _ _ ↦ norm_expListTerm_le_pow l i)
  intro j hj _
  have hsum : (∑ i ∈ range j, expListTerm l i) =
      1 + ∑ i ∈ range (j - 1), expListTerm l (i + 1) := by
    conv_lhs => rw [show j = (j - 1) + 1 by lia]
    rw [sum_range_succ', expListTerm_zero, add_comm]
  have h := norm_prod_exp_sub_sum_le_pow l j hj hl
  simpa only [hsum, sub_add_eq_sub_sub] using h

/-- The finite logarithm error retains the norms of the logarithm coefficients. -/
lemma norm_logPartialSum_prod_exp_sub_sum_le_weighted (l : List A)
    (hl : (l.map norm).sum < 1 / 4) (n : ℕ) :
    ‖logPartialSum A n ((l.map exp).prod - 1) -
      ∑ k ∈ range n, logCoeff k • positivePowerTrunc (expListTerm l) k n‖ ≤
      (∑ k ∈ range n, ‖logCoeff k‖) * 2 ^ (n - 1) * (l.map norm).sum ^ n := by
  simpa only [mul_assoc] using
    norm_logPartialSum_sub_sum_positivePowerTrunc_le_of_pow ((l.map exp).prod - 1) (expListTerm l) n
      (fun k hk ↦ norm_prod_exp_sub_one_pow_sub_positivePowerTrunc_le l hl k n hk)

/-- Bounding each logarithm coefficient by one gives a bound in terms of the cutoff. -/
lemma norm_logPartialSum_prod_exp_sub_sum_le (l : List A)
    (hl : (l.map norm).sum < 1 / 4) (n : ℕ) :
    ‖logPartialSum A n ((l.map exp).prod - 1) -
      ∑ k ∈ range n, logCoeff k • positivePowerTrunc (expListTerm l) k n‖ ≤
      (n : ℝ) * 2 ^ (n - 1) * (l.map norm).sum ^ n :=
  (norm_logPartialSum_prod_exp_sub_sum_le_weighted l hl n).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (sum_norm_logCoeff_le n) (by positivity))
      (pow_nonneg (list_sum_norm_nonneg l) n))

end FQFP
