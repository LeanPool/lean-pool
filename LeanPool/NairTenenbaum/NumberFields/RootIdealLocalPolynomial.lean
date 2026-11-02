/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.NumberFields.IdealLocalEulerPolynomial

/-! # Every local root correction is a polynomial with positive value at `1/p` -/

@[expose] public section

namespace NairTenenbaum

open Finset NumberField Polynomial ArithmeticFunction

theorem squarefreeRootArithmetic_series (Q : ℤ[X]) {p : ℕ} (hp : p.Prime) :
    arithmeticPrimeSeries (squarefreeRootArithmetic Q) p =
      ((1 + C (rootCount Q p : ℝ) * X : ℝ[X]) : PowerSeries ℝ) := by
  ext k
  rw [arithmeticPrimeSeries_coeff, Polynomial.coeff_coe]
  by_cases hk0 : k = 0
  · simp [hk0, (squarefreeRootArithmetic_isMultiplicative Q).1]
  by_cases hk1 : k = 1
  · simp [hk1, squarefreeRootArithmetic_prime Q hp, Polynomial.coeff_one]
  have H : ¬ Squarefree (p ^ k) := by simp [Nat.squarefree_pow_iff hp.ne_one hk0, hk1]
  simp [squarefreeRootArithmetic, H, coeff_add, coeff_X, Polynomial.coeff_one, hk0, Ne.symm hk1]

variable (K : Type*) [Field K] [NumberField K]

/-- The finite local correction polynomial relating root counts and ideal norms. -/
noncomputable def rootIdealLocalPolynomial (Q : ℤ[X]) (p : ℕ) : ℝ[X] :=
  (1 + C (rootCount Q p : ℝ) * X) * idealLocalEulerPolynomial K p

theorem rootIdealCorrection_series_eq_polynomial (Q : ℤ[X]) {p : ℕ} (hp : p.Prime) :
    arithmeticPrimeSeries (rootIdealCorrection K Q) p =
      (rootIdealLocalPolynomial K Q p : PowerSeries ℝ) := by
  rw [rootIdealCorrection, arithmeticPrimeSeries_mul _ _ hp,
    squarefreeRootArithmetic_series Q hp, idealNormInverse_series_eq_euler K hp]
  exact (Polynomial.coe_mul _ _).symm

theorem rootIdealCorrection_prime_pow_eq_coeff (Q : ℤ[X]) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    rootIdealCorrection K Q (p ^ k) = (rootIdealLocalPolynomial K Q p).coeff k := by
  rw [← arithmeticPrimeSeries_coeff, rootIdealCorrection_series_eq_polynomial K Q hp,
      Polynomial.coeff_coe]

theorem idealLocalEulerPolynomial_eval_pos {p : ℕ} (hp : p.Prime) :
    0 < (idealLocalEulerPolynomial K p).eval (1 / (p : ℝ)) := by
  unfold idealLocalEulerPolynomial weightedEulerPolynomial
  rw [Polynomial.eval_prod]
  apply prod_pos
  intro P _
  simp only [eval_sub, eval_one, eval_pow, eval_X]
  apply sub_pos.mpr
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hbase : (1 : ℝ) / p < 1 := (div_lt_one (by linarith)).mpr hp1
  exact pow_lt_one₀ (by positivity) hbase (primeIdealSupport_inertiaDeg_pos hp P.2).ne'

theorem rootIdealLocalPolynomial_eval_pos (Q : ℤ[X]) {p : ℕ} (hp : p.Prime) :
    0 < (rootIdealLocalPolynomial K Q p).eval (1 / (p : ℝ)) := by
  unfold rootIdealLocalPolynomial
  rw [eval_mul]
  apply mul_pos _ (idealLocalEulerPolynomial_eval_pos K hp)
  simp only [eval_add, eval_one, eval_mul, eval_C, eval_X]
  have H : 0 ≤ (rootCount Q p : ℝ) * (1 / p) := by positivity
  linarith

theorem rootIdealCorrection_local_abs_summable (Q : ℤ[X]) {p : ℕ} (hp : p.Prime) :
    Summable (fun k : ℕ => |rootIdealCorrection K Q (p ^ k)| / (p : ℝ) ^ k) := by
  apply summable_of_ne_finset_zero (s := (rootIdealLocalPolynomial K Q p).support)
  intro k hk
  rw [rootIdealCorrection_prime_pow_eq_coeff K Q hp,
    Polynomial.notMem_support_iff.mp hk, abs_zero, zero_div]

theorem rootIdealCorrection_local_sum_eq_eval (Q : ℤ[X]) {p : ℕ} (hp : p.Prime) :
    (∑' k : ℕ, rootIdealCorrection K Q (p ^ k) / (p : ℝ) ^ k) =
      (rootIdealLocalPolynomial K Q p).eval (1 / (p : ℝ)) := by
  rw [tsum_eq_sum (s := (rootIdealLocalPolynomial K Q p).support) (by
    intro k hk
    rw [rootIdealCorrection_prime_pow_eq_coeff K Q hp, Polynomial.notMem_support_iff.mp hk,
        zero_div])]
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  apply sum_congr rfl
  intro k _
  rw [rootIdealCorrection_prime_pow_eq_coeff K Q hp]
  simp only [div_eq_mul_inv, one_mul, inv_pow]

theorem rootIdealCorrection_local_sum_pos (Q : ℤ[X]) {p : ℕ} (hp : p.Prime) :
    0 < ∑' k : ℕ, rootIdealCorrection K Q (p ^ k) / (p : ℝ) ^ k := by
  rw [rootIdealCorrection_local_sum_eq_eval K Q hp]
  exact rootIdealLocalPolynomial_eval_pos K Q hp

end NairTenenbaum
