/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.NumberFields.MinpolyEulerProduct

/-! # Comparing a root Euler product with its prime sum

The quadratic logarithm error is summable uniformly for `σ≥1`.
-/

@[expose] public section

namespace NairTenenbaum

open Finset Real Polynomial

theorem self_le_log_one_add_add_sq {x : ℝ} (hx : 0 ≤ x) : x ≤ Real.log (1 + x) + x ^ 2 := by
  have H := Real.le_log_one_add_of_nonneg hx
  have h : x - x ^ 2 ≤ 2 * x / (x + 2) := by
    apply (le_div_iff₀ (by linarith : 0 < x + 2)).mpr
    nlinarith [mul_nonneg hx (sq_nonneg x)]
  linarith

theorem monic_rootPrimePowerWeight_le_degree_div {Q : ℤ[X]} (hQ : Q.Monic)
    {p : ℕ} (hp : p.Prime) {σ : ℝ} (hσ : 1 ≤ σ) :
    (rootCount Q p : ℝ) * (p : ℝ) ^ (-σ) ≤ (Q.natDegree : ℝ) / p := by
  calc
    _ ≤ (Q.natDegree : ℝ) * (p : ℝ) ^ (-σ) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast rootCount_le_degree_of_monic hQ hp)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ ≤ (Q.natDegree : ℝ) * (p : ℝ) ^ (-1 : ℝ) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by
          exact_mod_cast hp.one_le) (by linarith)) (Nat.cast_nonneg _)
    _ = _ := by rw [Real.rpow_neg_one, div_eq_mul_inv]

theorem monic_primeRootSquare_sum_le {Q : ℤ[X]} (hQ : Q.Monic)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) {σ : ℝ} (hσ : 1 ≤ σ) :
    (∑ p ∈ S, ((rootCount Q p : ℝ) * (p : ℝ) ^ (-σ)) ^ 2) ≤
      (Q.natDegree : ℝ) ^ 2 * ∑' n : ℕ, (n : ℝ) ^ (-2 : ℝ) := by
  calc
    _ ≤ ∑ p ∈ S, (Q.natDegree : ℝ) ^ 2 * (p : ℝ) ^ (-2 : ℝ) := by
      apply sum_le_sum
      intro p hp
      have H := sq_le_sq₀
        (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg p)) |>.mpr
          (monic_rootPrimePowerWeight_le_degree_div hQ (hS p hp) hσ)
      apply H.trans_eq
      rw [div_pow, Real.rpow_neg (Nat.cast_nonneg p), div_eq_mul_inv]
      norm_num
    _ = (Q.natDegree : ℝ) ^ 2 * ∑ p ∈ S, (p : ℝ) ^ (-2 : ℝ) := (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1)).sum_le_tsum S
        (fun p _ => Real.rpow_nonneg (Nat.cast_nonneg p) _)) (sq_nonneg _)

theorem monic_primeRoot_sum_le_log_product {Q : ℤ[X]} (hQ : Q.Monic)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) {σ : ℝ} (hσ : 1 ≤ σ) :
    (∑ p ∈ S, (rootCount Q p : ℝ) * (p : ℝ) ^ (-σ)) ≤
      Real.log (∏ p ∈ S, (1 + (rootCount Q p : ℝ) * (p : ℝ) ^ (-σ))) +
      (Q.natDegree : ℝ) ^ 2 * ∑' n : ℕ, (n : ℝ) ^ (-2 : ℝ) := by
  have H := sum_le_sum (fun p (_ : p ∈ S) => self_le_log_one_add_add_sq
    (mul_nonneg (Nat.cast_nonneg (rootCount Q p)) (Real.rpow_nonneg (Nat.cast_nonneg p) (-σ))))
  rw [sum_add_distrib] at H
  apply H.trans
  rw [Real.log_prod (fun p _ => ne_of_gt (by
    have := mul_nonneg (Nat.cast_nonneg (rootCount Q p)) (Real.rpow_nonneg (Nat.cast_nonneg p) (-σ))
    linarith : 0 < 1 + (rootCount Q p : ℝ) * (p : ℝ) ^ (-σ)))]
  exact add_le_add_right (monic_primeRootSquare_sum_le hQ S hS hσ) _

end NairTenenbaum
