/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Hooley.HooleyMomentInterpolation
public import LeanPool.NairTenenbaum.Hooley.HooleyMomentRecurrence
public import LeanPool.NairTenenbaum.Hooley.HooleyPrimeSampling

/-! # Prime averages of the mixed terms

Prime sampling and interpolation prove the mixed-term estimate needed
before equation (2.10) of Tenenbaum's weighted mean argument. The estimate
holds for every finite set of primes, with constants independent of that set.
-/

@[expose] public section

namespace NairTenenbaum

open Finset Real MeasureTheory

theorem prime_sum_hooleyMixedMoment_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (n : ℕ) {j k : ℕ} (hj : 0 < j) (hk : 0 < k) :
    (∑ p ∈ S, (Real.log p / p) * hooleyMixedMoment j k n (Real.log p)) ≤
      ((2 : ℝ) ^ (k - 1) * (Real.log 4 * Real.exp 2)) *
        (hooleyMoment j n * hooleyMoment k n) := by
  have hi (p : ℕ) : Integrable (fun u => (Real.log p / p) *
      (hooleyWindow n u ^ j * hooleyWindow n (u - Real.log p) ^ k)) :=
    (integrable_hooleyMixedMoment j k n (Real.log p) (by omega)).const_mul _
  have Heq : (∑ p ∈ S, (Real.log p / p) * hooleyMixedMoment j k n (Real.log p)) =
      ∫ u, ∑ p ∈ S, (Real.log p / p) *
        (hooleyWindow n u ^ j * hooleyWindow n (u - Real.log p) ^ k) := by
    rw [integral_finsetSum _ (fun p _ => hi p)]
    simp only [integral_const_mul, hooleyMixedMoment]
  have Hpoint (u : ℝ) :
      (∑ p ∈ S, (Real.log p / p) *
        (hooleyWindow n u ^ j * hooleyWindow n (u - Real.log p) ^ k)) ≤
      hooleyWindow n u ^ j *
        ((2 : ℝ) ^ (k - 1) * (Real.log 4 * Real.exp 2) * hooleyMoment k n) := by
    have H := mul_le_mul_of_nonneg_left (prime_sampled_hooleyWindow_pow_le S hS n hk u)
      (pow_nonneg (hooleyWindow_nonneg n u) j)
    rw [mul_sum] at H
    simpa only [mul_left_comm, mul_assoc] using H
  rw [Heq]
  have H := integral_mono (integrable_finsetSum _ (fun p _ => hi p))
    ((integrable_hooleyWindow_pow n hj).mul_const _) Hpoint
  apply H.trans_eq
  rw [integral_mul_const]
  change hooleyMoment j n * _ = _
  ring

/-- The complementary moment factors no longer depend on the binomial index. -/
theorem prime_sum_hooleyMixedMoment_interpolated (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (n : ℕ) {j q : ℕ} (hq : 1 < q) (hj : 1 ≤ j) (hjq : j < q) :
    (∑ p ∈ S, (Real.log p / p) * hooleyMixedMoment j (q - j) n (Real.log p)) ≤
      ((2 : ℝ) ^ q * (Real.log 4 * Real.exp 2)) *
        ((n.divisors.card : ℝ) ^ ((q : ℝ) / ((q : ℝ) - 1)) *
          hooleyMoment q n ^ (((q : ℝ) - 2) / ((q : ℝ) - 1))) := by
  apply (prime_sum_hooleyMixedMoment_le S hS n (by omega : 0 < j) (by omega : 0 < q - j)).trans
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : q - j - 1 ≤ q)) (by positivity)
  · exact hooleyMoment_mixedProduct_le n hq hj hjq
  · exact mul_nonneg (hooleyMoment_nonneg _ _) (hooleyMoment_nonneg _ _)
  · positivity

/-- The finite prime mixed-term estimate, with the same `4^q` order and
moment exponents as the weighted mean proof. -/
theorem prime_sum_hooleyPrimeCrossMoment_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (n : ℕ) {q : ℕ} (hq : 1 < q) :
    (∑ p ∈ S, (Real.log p / p) * hooleyPrimeCrossMoment q n p) ≤
      (Real.log 4 * Real.exp 2) * (4 : ℝ) ^ q *
        ((n.divisors.card : ℝ) ^ ((q : ℝ) / ((q : ℝ) - 1)) *
          hooleyMoment q n ^ (((q : ℝ) - 2) / ((q : ℝ) - 1))) := by
  let R : ℝ := (n.divisors.card : ℝ) ^ ((q : ℝ) / ((q : ℝ) - 1)) *
    hooleyMoment q n ^ (((q : ℝ) - 2) / ((q : ℝ) - 1))
  have hR : 0 ≤ R := mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (Real.rpow_nonneg (hooleyMoment_nonneg q n) _)
  have hchoose : (∑ j ∈ Ico 1 q, (q.choose j : ℝ)) ≤ (2 : ℝ) ^ q := by
    calc
      _ ≤ ∑ j ∈ range (q + 1), (q.choose j : ℝ) := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro j hj
          exact mem_range.mpr (by have := (mem_Ico.mp hj).2; omega)
        · intro j hj _
          exact Nat.cast_nonneg _
      _ = (2 : ℝ) ^ q := by exact_mod_cast Nat.sum_range_choose q
  have Heq : (∑ p ∈ S, (Real.log p / p) * hooleyPrimeCrossMoment q n p) =
      ∑ j ∈ Ico 1 q, (q.choose j : ℝ) *
        ∑ p ∈ S, (Real.log p / p) * hooleyMixedMoment j (q - j) n (Real.log p) := by
    unfold hooleyPrimeCrossMoment
    simp_rw [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro j hj
    apply sum_congr rfl
    intro p hp
    ring
  rw [Heq]
  calc
    _ ≤ ∑ j ∈ Ico 1 q, (q.choose j : ℝ) * (((2 : ℝ) ^ q * (Real.log 4 * Real.exp 2)) * R) :=
      sum_le_sum fun j hj => mul_le_mul_of_nonneg_left
        (prime_sum_hooleyMixedMoment_interpolated S hS n hq (mem_Ico.mp hj).1 (mem_Ico.mp hj).2)
        (Nat.cast_nonneg _)
    _ = (∑ j ∈ Ico 1 q, (q.choose j : ℝ)) * (((2 : ℝ) ^ q * (Real.log 4 * Real.exp 2)) * R) :=
      (sum_mul _ _ _).symm
    _ ≤ (2 : ℝ) ^ q * (((2 : ℝ) ^ q * (Real.log 4 * Real.exp 2)) * R) :=
      mul_le_mul_of_nonneg_right hchoose (mul_nonneg (by positivity) hR)
    _ = _ := by
      have Hpow : (2 : ℝ) ^ q * (2 : ℝ) ^ q = (4 : ℝ) ^ q := by rw [← mul_pow]; norm_num
      change _ = (Real.log 4 * Real.exp 2) * 4 ^ q * R
      rw [← Hpow]
      ring

end NairTenenbaum
