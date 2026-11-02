/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.WeightedMomentPowers
public import LeanPool.NairTenenbaum.Polynomials.PolynomialSieve

/-! # Squarefree coefficients of the Hooley moment Dirichlet series

The subpolynomial bound is uniform in the positive integral moment order.
This uniformity permits choosing that order later in the mean-value proof.
-/

@[expose] public section

namespace NairTenenbaum

open Finset Real Polynomial

theorem hooleyMoment_rpow_le_card_rpow (n : ℕ) {q : ℕ} (hq : 0 < q)
    {t : ℝ} (ht : 0 ≤ t) :
    hooleyMoment q n ^ (t / q) ≤ (n.divisors.card : ℝ) ^ t := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  calc
    _ ≤ ((n.divisors.card : ℝ) ^ q) ^ (t / q) :=
      Real.rpow_le_rpow (hooleyMoment_nonneg q n) (hooleyMoment_le_card_pow n hq)
        (div_nonneg ht hq'.le)
    _ = _ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
      congr 1
      field_simp

theorem card_divisors_of_squarefree {n : ℕ} (hn : Squarefree n) :
    n.divisors.card = 2 ^ n.primeFactors.card := by
  rw [Nat.card_divisors hn.ne_zero]
  calc
    _ = ∏ _p ∈ n.primeFactors, 2 := by
      apply prod_congr rfl
      intro p hp
      rw [Nat.factorization_eq_one_of_squarefree hn (Nat.prime_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hp)]
    _ = _ := prod_const _

/-- The asterisk in the source Dirichlet series means squarefree support. -/
noncomputable def hooleyMomentCoefficient (Q : ℤ[X]) (t : ℝ) (q n : ℕ) : ℝ :=
  if Squarefree n then hooleyMoment q n ^ (t / q) * (rootCount Q n : ℝ) else 0

theorem hooleyMomentCoefficient_nonneg (Q : ℤ[X]) (t : ℝ) (q n : ℕ) :
    0 ≤ hooleyMomentCoefficient Q t q n := by
  unfold hooleyMomentCoefficient
  split_ifs
  · exact mul_nonneg (Real.rpow_nonneg (hooleyMoment_nonneg q n) _) (Nat.cast_nonneg _)
  · rfl

@[simp] theorem hooleyMomentCoefficient_zero (Q : ℤ[X]) (t : ℝ) (q : ℕ) :
    hooleyMomentCoefficient Q t q 0 = 0 := by
  simp [hooleyMomentCoefficient]

@[simp] theorem hooleyMoment_at_one {q : ℕ} (hq : 0 < q) : hooleyMoment q 1 = 1 := by
  have hlo := card_divisors_le_hooleyMoment 1 hq
  have hhi := hooleyMoment_le_card_pow 1 hq
  simp only [Nat.divisors_one, card_singleton, Nat.cast_one, one_pow] at hlo hhi
  exact le_antisymm hhi hlo

@[simp] theorem hooleyMomentCoefficient_one (Q : ℤ[X]) (t : ℝ) {q : ℕ} (hq : 0 < q) :
    hooleyMomentCoefficient Q t q 1 = 1 := by
  simp [hooleyMomentCoefficient, hooleyMoment_at_one hq, rootCount_one]

/-- Uniformity includes the polynomial coefficients and the moment order `q`. -/
theorem exists_hooleyMomentCoefficient_le_rpow (g : ℝ) {t η : ℝ}
    (ht : 0 ≤ t) (hη : 0 < η) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (Q : ℤ[X]), NoFixedPrimeDivisor Q → (Q.natDegree : ℝ) ≤ g →
      ∀ q : ℕ, 0 < q → ∀ n : ℕ, hooleyMomentCoefficient Q t q n ≤ C * (n : ℝ) ^ η := by
  let K := (2 : ℝ) ^ t * max 1 g
  have hK : 1 ≤ K := one_le_mul_of_one_le_of_one_le
    (Real.one_le_rpow (by norm_num) ht) (le_max_left _ _)
  obtain ⟨C, hC, hbound⟩ := exists_primeFactorPower_le_rpow hK hη
  refine ⟨C, hC, fun Q hQ hg q hq n => ?_⟩
  by_cases hn : Squarefree n
  · rw [hooleyMomentCoefficient, ite_eq_left hn]
    calc
      _ ≤ (n.divisors.card : ℝ) ^ t * (max 1 g) ^ n.primeFactors.card :=
        mul_le_mul (hooleyMoment_rpow_le_card_rpow n hq ht)
          (rootCount_squarefree_le hQ (hg.trans (le_max_right _ _)) hn)
          (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ = K ^ n.primeFactors.card := by
        rw [card_divisors_of_squarefree hn, Nat.cast_pow, Nat.cast_ofNat,
          ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2), ← mul_pow]
      _ ≤ _ := hbound n hn.ne_zero
  · rw [hooleyMomentCoefficient, ite_eq_right hn]
    exact mul_nonneg (zero_le_one.trans hC) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

end NairTenenbaum
