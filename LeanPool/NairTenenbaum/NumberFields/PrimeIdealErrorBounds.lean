/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.NumberFields.PrimeIdealNormBounds

/-! # Summable errors in the prime-ideal Euler product -/

@[expose] public section

namespace NairTenenbaum

open Finset Real NumberField Ideal

variable {K : Type*} [Field K] [NumberField K]

theorem primeIdeals_sum_baseWeight_le (S : Finset (Ideal (𝓞 K)))
    (hS : ∀ P ∈ S, Prime P) (f : ℕ → ℝ) (hf : ∀ p, 0 ≤ f p) :
    (∑ P ∈ S, f (rationalPrimeBelow P)) ≤
      (Module.finrank ℚ K : ℝ) * ∑ p ∈ S.image rationalPrimeBelow, f p := by
  classical
  rw [← sum_fiberwise_of_maps_to (g := rationalPrimeBelow) (s := S) (t := S.image
      rationalPrimeBelow)
    (fun P hP => mem_image.mpr ⟨P, hP, rfl⟩), mul_sum]
  apply sum_le_sum
  intro p hp
  have hprime : p.Prime := by
    obtain ⟨P, hP, rfl⟩ := mem_image.mp hp
    exact rationalPrimeBelow_prime (hS P hP)
  have HE : (∑ P ∈ S.filter (fun P => rationalPrimeBelow P = p), f (rationalPrimeBelow P)) =
      ((S.filter (fun P => rationalPrimeBelow P = p)).card : ℝ) * f p := by
    calc
      _ = ∑ _P ∈ S.filter (fun P => rationalPrimeBelow P = p), f p :=
        sum_congr rfl (fun P hP => congrArg f (mem_filter.mp hP).2)
      _ = _ := by simp
  rw [HE]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast primeIdeals_fiber_card_le S hS hprime) (hf p)

theorem primeIdeals_sum_baseWeight_le_tsum (S : Finset (Ideal (𝓞 K)))
    (hS : ∀ P ∈ S, Prime P) (f : ℕ → ℝ) (hf : ∀ p, 0 ≤ f p) (hs : Summable f) :
    (∑ P ∈ S, f (rationalPrimeBelow P)) ≤ (Module.finrank ℚ K : ℝ) * ∑' n, f n :=
  (primeIdeals_sum_baseWeight_le S hS f hf).trans
    (mul_le_mul_of_nonneg_left (hs.sum_le_tsum _ (fun n _ => hf n)) (Nat.cast_nonneg _))

theorem primeIdeal_weight_sq_le {P : Ideal (𝓞 K)} (hP : Prime P) {σ : ℝ} (hσ : 1 ≤ σ) :
    ((Ideal.absNorm P : ℝ) ^ (-σ)) ^ 2 ≤ (rationalPrimeBelow P : ℝ) ^ (-2 : ℝ) := by
  have hpos : (0 : ℝ) < rationalPrimeBelow P := by exact_mod_cast (rationalPrimeBelow_prime hP).pos
  have hn : (1 : ℝ) ≤ Ideal.absNorm P := by exact_mod_cast (idealNorm_prime_gt_one hP).le
  have H : (Ideal.absNorm P : ℝ) ^ (-σ) ≤ (rationalPrimeBelow P : ℝ)⁻¹ := by
    calc
      _ ≤ (Ideal.absNorm P : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn (by linarith)
      _ ≤ _ := by
        rw [Real.rpow_neg_one]
        exact inv_anti₀ hpos (by exact_mod_cast rationalPrimeBelow_le_norm hP)
  have HS := pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg _) _) H 2
  exact HS.trans_eq (by rw [inv_pow, Real.rpow_neg hpos.le, Real.rpow_two])

theorem primeIdeal_higherDegree_weight_le {P : Ideal (𝓞 K)} (hP : Prime P)
    (hneq : Ideal.absNorm P ≠ rationalPrimeBelow P) {σ : ℝ} (hσ : 1 ≤ σ) :
    (Ideal.absNorm P : ℝ) ^ (-σ) ≤ (rationalPrimeBelow P : ℝ) ^ (-2 : ℝ) := by
  have hp : (0 : ℝ) < rationalPrimeBelow P := by exact_mod_cast (rationalPrimeBelow_prime hP).pos
  calc
    _ ≤ (Ideal.absNorm P : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (idealNorm_prime_gt_one hP).le) (by linarith)
    _ ≤ _ := by
      rw [Real.rpow_neg_one, Real.rpow_neg hp.le, Real.rpow_two]
      apply inv_anti₀ (sq_pos_of_pos hp)
      exact_mod_cast rationalPrimeBelow_sq_le_norm hP hneq

theorem primeIdeal_square_error_sum_le (S : Finset (Ideal (𝓞 K)))
    (hS : ∀ P ∈ S, Prime P) {σ : ℝ} (hσ : 1 ≤ σ) :
    (∑ P ∈ S, ((Ideal.absNorm P : ℝ) ^ (-σ)) ^ 2) ≤
      (Module.finrank ℚ K : ℝ) * ∑' n : ℕ, (n : ℝ) ^ (-2 : ℝ) := by
  apply (sum_le_sum (fun P hP => primeIdeal_weight_sq_le (hS P hP) hσ)).trans
  exact primeIdeals_sum_baseWeight_le_tsum S hS (fun n : ℕ => (n : ℝ) ^ (-2 : ℝ))
    (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.summable_nat_rpow.mpr (by norm_num))

theorem primeIdeal_higherDegree_sum_le (S : Finset (Ideal (𝓞 K)))
    (hS : ∀ P ∈ S, Prime P) {σ : ℝ} (hσ : 1 ≤ σ) :
    (∑ P ∈ S.filter (fun P => Ideal.absNorm P ≠ rationalPrimeBelow P), (Ideal.absNorm P : ℝ) ^
        (-σ)) ≤
      (Module.finrank ℚ K : ℝ) * ∑' n : ℕ, (n : ℝ) ^ (-2 : ℝ) := by
  apply (sum_le_sum (fun P hP => primeIdeal_higherDegree_weight_le
    (hS P (mem_filter.mp hP).1) (mem_filter.mp hP).2 hσ)).trans
  exact primeIdeals_sum_baseWeight_le_tsum _ (fun P hP => hS P (mem_filter.mp hP).1)
    (fun n : ℕ => (n : ℝ) ^ (-2 : ℝ))
    (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.summable_nat_rpow.mpr (by norm_num))

end NairTenenbaum
