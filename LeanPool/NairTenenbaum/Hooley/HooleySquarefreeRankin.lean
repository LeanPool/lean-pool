/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Hooley.HooleyDirichletPowerBound

/-! # From Dirichlet moments to finite squarefree Hooley sums

A Rankin comparison at `σ=1+1/log x` costs only `exp(1)`. The comparison
between the maximum window and an integral moment costs at most `2^t`.
-/

@[expose] public section

namespace NairTenenbaum

open Finset Real Polynomial

theorem hooleyDelta_rpow_le_moment_rpow (n : ℕ) {q : ℕ} (hq : 0 < q)
    {t : ℝ} (ht : 0 ≤ t) :
    (hooleyDelta n : ℝ) ^ t ≤ (2 : ℝ) ^ t * hooleyMoment q n ^ (t / q) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have H : (hooleyDelta n : ℝ) ^ q ≤ (2 : ℝ) ^ q * hooleyMoment q n :=
    (hooleyDelta_pow_le_moment n hq).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.sub_le _ _)) (hooleyMoment_nonneg q n))
  have H' := Real.rpow_le_rpow (pow_nonneg (Nat.cast_nonneg _) _) H (div_nonneg ht hq'.le)
  rw [Real.mul_rpow (by positivity) (hooleyMoment_nonneg q n),
    ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _),
    ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    show (q : ℝ) * (t / q) = t by field_simp] at H'
  exact H'

theorem reciprocal_le_rankin_weight {x σ : ℝ} (hσ : 1 ≤ σ)
    {n : ℕ} (hn : 0 < n) (hnx : (n : ℝ) ≤ x) :
    (n : ℝ)⁻¹ ≤ x ^ (σ - 1) * (n : ℝ) ^ (-σ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have H := mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow hn'.le hnx (by linarith : 0 ≤ σ - 1))
    (Real.rpow_nonneg hn'.le (-σ))
  rw [← Real.rpow_add hn', show σ - 1 + -σ = -1 by ring, Real.rpow_neg_one] at H
  exact H

theorem finite_reciprocal_hooleyMoment_le_dirichlet {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    {t x σ : ℝ} (ht : 0 ≤ t) {q : ℕ} (hq : 0 < q) (hx : 0 < x) (hσ : 1 < σ)
    (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n ∧ (n : ℝ) ≤ x) :
    (∑ n ∈ S, hooleyMomentCoefficient Q t q n / n) ≤ x ^ (σ - 1) * hooleyDirichlet Q t q σ := by
  calc
    _ ≤ ∑ n ∈ S, x ^ (σ - 1) * (hooleyMomentCoefficient Q t q n * (n : ℝ) ^ (-σ)) := by
      apply sum_le_sum
      intro n hn
      rw [div_eq_mul_inv]
      have H := mul_le_mul_of_nonneg_left
        (reciprocal_le_rankin_weight hσ.le (hS n hn).1 (hS n hn).2)
        (hooleyMomentCoefficient_nonneg Q t q n)
      simpa only [mul_left_comm] using H
    _ = x ^ (σ - 1) * ∑ n ∈ S, hooleyMomentCoefficient Q t q n * (n : ℝ) ^ (-σ) :=
      (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((summable_hooleyDirichlet hQ ht hq hσ).sum_le_tsum S (fun n _ =>
        mul_nonneg (hooleyMomentCoefficient_nonneg Q t q n) (Real.rpow_nonneg (Nat.cast_nonneg _)
            _)))
      (Real.rpow_nonneg hx.le _)

/-- The Hooley root sum restricted to squarefree integers. -/
noncomputable def squarefreeHooleyRootSum (Q : ℤ[X]) (t x : ℝ) : ℝ :=
  ∑ n ∈ (Icc 1 ⌊x⌋₊).filter Squarefree,
    (hooleyDelta n : ℝ) ^ t * (rootCount Q n : ℝ) / n

theorem squarefreeHooleyRootSum_le_dirichlet {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    {t x σ : ℝ} (ht : 0 ≤ t) {q : ℕ} (hq : 0 < q) (hx : 0 < x) (hσ : 1 < σ) :
    squarefreeHooleyRootSum Q t x ≤
      (2 : ℝ) ^ t * x ^ (σ - 1) * hooleyDirichlet Q t q σ := by
  classical
  unfold squarefreeHooleyRootSum
  calc
    _ ≤ ∑ n ∈ (Icc 1 ⌊x⌋₊).filter Squarefree, (2 : ℝ) ^ t * (hooleyMomentCoefficient Q t q n / n)
        := by
      apply sum_le_sum
      intro n hn
      rw [hooleyMomentCoefficient, ite_eq_left (mem_filter.mp hn).2]
      have H := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hooleyDelta_rpow_le_moment_rpow n hq ht) (Nat.cast_nonneg
            (rootCount Q n)))
        (Nat.cast_nonneg n)
      simpa only [mul_assoc, mul_div_assoc] using H
    _ = (2 : ℝ) ^ t * ∑ n ∈ (Icc 1 ⌊x⌋₊).filter Squarefree, hooleyMomentCoefficient Q t q n / n :=
      (mul_sum _ _ _).symm
    _ ≤ _ := by
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by norm_num) _)
      apply finite_reciprocal_hooleyMoment_le_dirichlet hQ ht hq hx hσ
      intro n hn
      have H := mem_Icc.mp (mem_filter.mp hn).1
      exact ⟨H.1, (Nat.cast_le.mpr H.2).trans (Nat.floor_le hx.le)⟩

theorem squarefreeHooleyRootSum_le_log_dirichlet {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    {t x : ℝ} (ht : 0 ≤ t) {q : ℕ} (hq : 0 < q) (hx : 1 < x) :
    squarefreeHooleyRootSum Q t x ≤ (2 : ℝ) ^ t * Real.exp 1 *
      hooleyDirichlet Q t q (1 + 1 / Real.log x) := by
  have hl : 0 < Real.log x := Real.log_pos hx
  have H := squarefreeHooleyRootSum_le_dirichlet hQ ht hq (by linarith : 0 < x)
    (by linarith [one_div_pos.mpr hl] : 1 < 1 + 1 / Real.log x)
  have hpow : x ^ ((1 + 1 / Real.log x) - 1) = Real.exp 1 := by
    rw [add_sub_cancel_left, Real.rpow_def_of_pos (by linarith : 0 < x)]
    congr 1
    field_simp
  rwa [hpow] at H

end NairTenenbaum
