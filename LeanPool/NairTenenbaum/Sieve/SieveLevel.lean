/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Sieve.SieveProductLowerBound

/-! # Absorbing the conditional sieve remainder at an explicit level -/

@[expose] public section

namespace NairTenenbaum

open Finset Nat Real Polynomial

theorem mass_mul_root_density {r : ℕ} (R : Fin r → ℤ[X]) (m : Tuple r) :
    (mass m : ℝ) * (∏ i, ((rootCount (R i) (m i) : ℝ) / m i)) =
      ∏ i, (rootCount (R i) (m i) : ℝ) := by
  rw [Finset.prod_div_distrib]
  have hmass : (∏ i, (m i : ℝ)) = (mass m : ℝ) := by simp only [mass, Nat.cast_prod]
  rw [hmass]
  exact mul_div_cancel₀ _ (by exact_mod_cast (mass_pos m).ne')

/-- A power bound for the reciprocal sieve density absorbs the remainder at the given level. -/
theorem absorb_sieve_remainder {K B M D S T L z A δ count : ℝ}
    (hK : 0 ≤ K) (hM : 0 ≤ M) (hD : 0 ≤ D) (hS : 0 < S) (hT : 1 ≤ T)
    (hL : 0 ≤ L) (hz : 0 < z) (hinv : S⁻¹ ≤ B * z ^ δ)
    (hlevel : B * M * z ^ (A + δ) ≤ L)
    (hcount : count ≤ K * (L * S * T * D + (M * D) * z ^ A)) :
    count ≤ (2 * K) * (L * S * T * D) := by
  have hscaled : M * z ^ A * S⁻¹ ≤ L := by
    calc
      _ ≤ M * z ^ A * (B * z ^ δ) := by gcongr
      _ = B * M * z ^ (A + δ) := by rw [Real.rpow_add hz]; ring
      _ ≤ L := hlevel
  have hmass : M * z ^ A ≤ L * S := by
    have H := mul_le_mul_of_nonneg_right hscaled hS.le
    simpa only [mul_assoc, inv_mul_cancel₀ hS.ne', mul_one] using H
  have herr : (M * D) * z ^ A ≤ L * S * T * D := by
    calc
      _ = (M * z ^ A) * D := by ring
      _ ≤ (L * S) * D := by gcongr
      _ ≤ (L * S) * T * D := by
        apply mul_le_mul_of_nonneg_right _ hD
        exact le_mul_of_one_le_right (mul_nonneg hL hS.le) hT
  calc
    count ≤ K * (L * S * T * D + (M * D) * z ^ A) := hcount
    _ ≤ K * (L * S * T * D + L * S * T * D) := by gcongr
    _ = _ := by ring

/-- The conditional sieve main term with its congruence density and totient correction. -/
noncomputable def conditionalSieveMainTerm {r : ℕ} (Q : ℤ[X]) (g : ℕ)
    (R : Fin r → ℤ[X]) (m : Tuple r) (a b : ℤ) (z : ℝ) : ℝ :=
  ((b : ℝ) - a) * sieveProduct Q z * totientTwist g (mass m) *
    ∏ i, ((rootCount (R i) (m i) : ℝ) / m i)

/-- Explicit cutoff growth is sufficient to absorb the entire conditional
sieve remainder, uniformly in the conditioning polynomials and moduli. -/
theorem exists_conditional_sieve_level_bound {g : ℕ} (hg : 0 < g)
    {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    ∃ K B : ℝ, 1 ≤ K ∧ 1 ≤ B ∧
      ∀ (Q : ℤ[X]), NoFixedPrimeDivisor Q → Q.natDegree ≤ g →
      ∀ (r : ℕ) (R : Fin r → ℤ[X]) (m : Tuple r),
      (Pairwise fun i j => Nat.Coprime (m i) (m j)) →
      ∀ (a b : ℤ) (z : ℝ), a ≤ b → 2 ≤ z → 16 ≤ Real.log z →
      B * (mass m : ℝ) * z ^ (4 * (g : ℝ) * (1 + η) + δ) ≤ (b : ℝ) - a →
      (conditionalPolynomialSiftedCount Q (sieveModulus Q (mass m) z) R m a b : ℝ) ≤
        K * conditionalSieveMainTerm Q g R m a b z := by
  obtain ⟨K, hK, hcount⟩ := exists_restored_conditional_sieve_bound hg hη
  obtain ⟨B, hB, hinv⟩ := exists_sieveProduct_inv_le_rpow g hδ
  refine ⟨2 * K, B, by linarith, hB, ?_⟩
  intro Q hQ hdeg r R m hpair a b z hab hz hzlog hlevel
  have H := absorb_sieve_remainder (zero_le_one.trans hK) (Nat.cast_nonneg (mass m))
    (show 0 ≤ ∏ i, ((rootCount (R i) (m i) : ℝ) / m i) by positivity)
    (sieveProduct_pos hQ z) (totientTwist_one_le g (mass_pos m).ne')
    (show 0 ≤ (b : ℝ) - a by exact_mod_cast sub_nonneg.mpr hab)
    (show 0 < z by linarith) (hinv Q hQ hdeg z hz) hlevel
    (by simpa only [conditionalSieveMainTerm, mass_mul_root_density] using
      hcount Q hQ hdeg r R m hpair a b z hab hz hzlog)
  exact H

end NairTenenbaum
