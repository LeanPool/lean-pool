/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.PrimeArguments.PrimeArgumentSieve
public import LeanPool.NairTenenbaum.Sieve.SieveLevel

/-! # Absorbing the prime-argument sieve remainder

The additional logarithm costs an arbitrarily small power in the sieve level.
The threshold is uniform in the constant term of the original polynomial.
-/

@[expose] public section

namespace NairTenenbaum

open Finset Polynomial

theorem exists_sieveProduct_inv_mul_log_le_rpow (g : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (Q : ℤ[X]), NoFixedPrimeDivisor Q → Q.natDegree ≤ g →
      ∀ z : ℝ, 2 ≤ z → (sieveProduct Q z)⁻¹ * Real.log z ≤ B * z ^ δ := by
  obtain ⟨B, hB, H⟩ := exists_sieveProduct_inv_le_rpow g (by linarith : 0 < δ / 2)
  refine ⟨max 1 (B / (δ / 2)), le_max_left _ _, ?_⟩
  intro Q hQ hdeg z hz
  have hz0 : 0 < z := by linarith
  calc
    _ ≤ (B * z ^ (δ / 2)) * (z ^ (δ / 2) / (δ / 2)) :=
      mul_le_mul (H Q hQ hdeg z hz) (Real.log_le_rpow_div hz0.le (by linarith))
        (Real.log_nonneg (by linarith)) (by positivity)
    _ = (B / (δ / 2)) * z ^ δ := by
      rw [show z ^ δ = z ^ (δ / 2) * z ^ (δ / 2) by
        rw [← Real.rpow_add hz0]; congr 1; ring]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hz0.le _)

/-- The conditional sieve main term with the prime-argument corrections. -/
noncomputable def primeArgumentConditionalMainTerm {r : ℕ} (Q : ℤ[X]) (g : ℕ)
    (R : Fin r → ℤ[X]) (m : Tuple r) (a b : ℤ) (z : ℝ) : ℝ :=
  ((b : ℝ) - a) * sieveProduct Q z * totientTwist 1 (Q.eval 0).natAbs *
    totientTwist (g + 1) (mass m) / Real.log z *
    ∏ i, ((rootCount (R i) (m i) : ℝ) / m i)

theorem exists_primeArgument_conditional_sieve_level_bound (g : ℕ)
    {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    ∃ K B : ℝ, 1 ≤ K ∧ 1 ≤ B ∧
      ∀ (Q : ℤ[X]), NoFixedPrimeDivisor Q → Q.eval 0 ≠ 0 → Q.natDegree ≤ g →
      ∀ (r : ℕ) (R : Fin r → ℤ[X]) (m : Tuple r),
      (Pairwise fun i j => Nat.Coprime (m i) (m j)) →
      ∀ (a b : ℤ) (z : ℝ), a ≤ b → 2 ≤ z → 16 ≤ Real.log z →
      B * (mass m : ℝ) * z ^ (4 * ((g : ℝ) + 1) * (1 + η) + δ) ≤ (b : ℝ) - a →
      (conditionalPolynomialSiftedCount (Q * X)
        (primeArgumentSieveModulus Q g (mass m) z) R m a b : ℝ) ≤
        K * primeArgumentConditionalMainTerm Q g R m a b z := by
  obtain ⟨K, hK, hcount⟩ := exists_primeArgument_conditional_sieve_bound g hη
  obtain ⟨B, hB, hinv⟩ := exists_sieveProduct_inv_mul_log_le_rpow g hδ
  refine ⟨2 * K, B, by linarith, hB, ?_⟩
  intro Q hQ hzero hdeg r R m hpair a b z hab hz hzlog hlevel
  have hlog : 0 < Real.log z := by linarith
  have hS := sieveProduct_pos hQ z
  have hinv' : (sieveProduct Q z / Real.log z)⁻¹ ≤ B * z ^ δ := by
    rw [inv_div]
    simpa only [div_eq_mul_inv, mul_comm] using hinv Q hQ hdeg z hz
  have hT : 1 ≤ totientTwist 1 (Q.eval 0).natAbs * totientTwist (g + 1) (mass m) :=
    one_le_mul_of_one_le_of_one_le
      (totientTwist_one_le _ (Int.natAbs_ne_zero.mpr hzero))
      (totientTwist_one_le _ (mass_pos m).ne')
  have heq : primeArgumentConditionalMainTerm Q g R m a b z =
      ((b : ℝ) - a) * (sieveProduct Q z / Real.log z) *
        (totientTwist 1 (Q.eval 0).natAbs * totientTwist (g + 1) (mass m)) *
          ∏ i, ((rootCount (R i) (m i) : ℝ) / m i) := by
    unfold primeArgumentConditionalMainTerm
    ring
  rw [heq]
  apply absorb_sieve_remainder (zero_le_one.trans hK) (Nat.cast_nonneg (mass m))
    (show 0 ≤ ∏ i, ((rootCount (R i) (m i) : ℝ) / m i) by positivity)
    (div_pos hS hlog) hT
    (show 0 ≤ (b : ℝ) - a by exact_mod_cast sub_nonneg.mpr hab)
    (show 0 < z by linarith) hinv' hlevel
  rw [← heq, mass_mul_root_density]
  exact hcount Q hQ hzero hdeg r R m hpair a b z hab hz hzlog

end NairTenenbaum
