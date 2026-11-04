/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.DyadicMeanDensity
public import LeanPool.NairTenenbaum.NumberFields.RootIdealCorrectionPositive

/-! # Positive root density from eventual prime-norm agreement -/

@[expose] public section

namespace NairTenenbaum

open Filter NumberField Polynomial
open scoped Topology

variable (K : Type*) [Field K] [NumberField K]

theorem rootIdealCorrection_prime_tails_summable_of_eventual_match {Q : ℤ[X]}
    (hQ : Q.IsPrimitive) (N : ℕ)
    (hmatch : ∀ p : ℕ, p.Prime → N < p → rootCount Q p = idealNormCount K p) :
    Summable (fun p : ℕ => if p.Prime then
      ∑' k : ℕ, |rootIdealCorrection K Q (p ^ (k + 1))| / (p : ℝ) ^ (k + 1) else 0) := by
  have HM : Summable (fun p : ℕ =>
      2 * rootIdealCorrectionGrowthConstant K Q ^ 2 / (p : ℝ) ^ 2) := by
    simpa only [div_eq_mul_inv] using
      (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < (2 : ℕ))).mul_left
        (2 * rootIdealCorrectionGrowthConstant K Q ^ 2)
  apply HM.of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop ⌈2 * rootIdealCorrectionGrowthConstant K Q⌉₊,
    eventually_gt_atTop N] with p hpbound hpN
  have hlarge : 2 * rootIdealCorrectionGrowthConstant K Q ≤ p :=
    (Nat.le_ceil _).trans (by exact_mod_cast hpbound)
  by_cases hp : p.Prime
  · rw [ite_eq_left hp, Real.norm_eq_abs, abs_of_nonneg
      (tsum_nonneg (fun k => div_nonneg (abs_nonneg _) (pow_nonneg (Nat.cast_nonneg p) _)))]
    apply (rootIdealCorrection_positivePower_tail K hQ hp hlarge ?_).2
    rw [rootIdealCorrection_prime K Q hp, hmatch p hp hpN, sub_self]
  · rw [ite_eq_right hp, norm_zero]
    positivity

theorem rootIdealCorrection_abs_summable_of_eventual_match {Q : ℤ[X]}
    (hQ : Q.IsPrimitive) (N : ℕ)
    (hmatch : ∀ p : ℕ, p.Prime → N < p → rootCount Q p = idealNormCount K p) :
    Summable (fun n : ℕ => |rootIdealCorrection K Q n| / n) := by
  apply summable_multiplicative_of_local_tails
  · intro n
    exact div_nonneg (abs_nonneg _) (Nat.cast_nonneg _)
  · simp [(rootIdealCorrection_isMultiplicative K Q).1]
  · intro m n hcop
    rw [(rootIdealCorrection_isMultiplicative K Q).2 hcop, abs_mul, Nat.cast_mul, mul_div_mul_comm]
  · intro p hp
    simpa only [Nat.cast_pow] using rootIdealCorrection_local_abs_summable K Q hp
  · simpa only [Nat.cast_pow] using rootIdealCorrection_prime_tails_summable_of_eventual_match K
      hQ N hmatch

theorem exists_squarefreeRoot_mean_of_eventual_ideal_match {Q : ℤ[X]}
    (hQ : Q.IsPrimitive) (N : ℕ)
    (hmatch : ∀ p : ℕ, p.Prime → N < p → rootCount Q p = idealNormCount K p) :
    ∃ L : ℝ, 0 < L ∧
      Tendsto (fun x : ℝ => arithmeticSummatory (squarefreeRootArithmetic Q) x / x)
        atTop (𝓝 L) := by
  have habs := rootIdealCorrection_abs_summable_of_eventual_match K hQ N hmatch
  have ht := rootIdealCorrection_prime_tails_summable_of_eventual_match K hQ N hmatch
  refine ⟨dedekindZeta_residue K * ∑' n : ℕ, rootIdealCorrection K Q n / n,
    mul_pos (dedekindZeta_residue_pos K) (rootIdealCorrection_sum_pos_of_absolute_convergence K Q
        habs ht), ?_⟩
  have H := idealNormArithmetic_convolution_mean K habs
  rw [rootIdealCorrection_mul_idealNorm] at H
  exact H

end NairTenenbaum
