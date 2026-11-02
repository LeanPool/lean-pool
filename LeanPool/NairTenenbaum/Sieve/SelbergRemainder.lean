/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Sieve.SelbergCoefficientBounds

/-! # Quantitative control of the Selberg remainder -/

@[expose] public section

namespace NairTenenbaum

open Finset Nat Real

/-- A pair with least common multiple `d` consists of divisors of `d`, so
extending both inner sums to all divisors of `P` adds only zero terms. -/
theorem sum_lcm_expand {P d : ℕ} (hP : P ≠ 0) (hd : d ∣ P) (f : ℕ → ℕ → ℝ) :
    (∑ a ∈ d.divisors, ∑ b ∈ d.divisors, if d = Nat.lcm a b then f a b else 0) =
      ∑ a ∈ P.divisors, ∑ b ∈ P.divisors, if d = Nat.lcm a b then f a b else 0 := by
  have H (a b : ℕ) : (a ∣ d ∧ b ∣ d ∧ d = Nat.lcm a b) ↔ d = Nat.lcm a b := by
    constructor
    · exact fun h => h.2.2
    · intro h
      exact ⟨h ▸ Nat.dvd_lcm_left a b, h ▸ Nat.dvd_lcm_right a b, h⟩
  simp_rw [← Nat.divisors_filter_dvd_of_dvd hP hd, Finset.sum_filter,
    Finset.ite_sum_zero, ← ite_and, H]

/-- The weighted absolute sum of squared sieve coefficients is bounded by a
quadratic sum over the original coefficients. -/
theorem lambdaSquared_weighted_abs_le {P : ℕ} (hP : P ≠ 0) (w E : ℕ → ℝ)
    (hE : ∀ d, d ∣ P → 0 ≤ E d) :
    (∑ d ∈ P.divisors, |BoundingSieve.lambdaSquared w d| * E d) ≤
      ∑ a ∈ P.divisors, ∑ b ∈ P.divisors, |w a| * |w b| * E (Nat.lcm a b) := by
  calc
    _ ≤ ∑ d ∈ P.divisors, ∑ a ∈ d.divisors, ∑ b ∈ d.divisors,
        if d = Nat.lcm a b then |w a| * |w b| * E d else 0 := by
      apply Finset.sum_le_sum
      intro d hd
      have H : |BoundingSieve.lambdaSquared w d| ≤
          ∑ a ∈ d.divisors, ∑ b ∈ d.divisors, if d = Nat.lcm a b then |w a| * |w b| else 0 := by
        unfold BoundingSieve.lambdaSquared
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
        intro a _
        refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
        apply Finset.sum_congr rfl
        intro b _
        split_ifs <;> simp only [abs_mul, abs_zero]
      have H' := mul_le_mul_of_nonneg_right H (hE d (Nat.dvd_of_mem_divisors hd))
      simpa only [Finset.sum_mul, ite_mul, zero_mul] using H'
    _ = ∑ d ∈ P.divisors, ∑ a ∈ P.divisors, ∑ b ∈ P.divisors,
        if d = Nat.lcm a b then |w a| * |w b| * E d else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      exact sum_lcm_expand hP (Nat.dvd_of_mem_divisors hd) _
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b hb
      exact Finset.sum_ite_eq_of_mem' P.divisors (Nat.lcm a b) _
        (Nat.mem_divisors.mpr ⟨Nat.lcm_dvd (Nat.dvd_of_mem_divisors ha) (Nat.dvd_of_mem_divisors
            hb), hP⟩)

/-- A submultiplicative majorant for the local remainders yields a square of a
single coefficient sum. -/
theorem selberg_errSum_le_square (s : BoundingSieve) (w E : ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hE : ∀ d, d ∣ s.prodPrimes → 0 ≤ E d)
    (hlcm : ∀ a, a ∣ s.prodPrimes → ∀ b, b ∣ s.prodPrimes → E (Nat.lcm a b) ≤ E a * E b)
    (herr : ∀ d, d ∣ s.prodPrimes → |s.rem d| ≤ C * E d) :
    s.errSum (BoundingSieve.lambdaSquared w) ≤
      C * (∑ d ∈ s.prodPrimes.divisors, |w d| * E d) ^ 2 := by
  calc
    _ ≤ C * ∑ d ∈ s.prodPrimes.divisors, |BoundingSieve.lambdaSquared w d| * E d := by
      rw [BoundingSieve.errSum, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro d hd
      convert mul_le_mul_of_nonneg_left (herr d (Nat.dvd_of_mem_divisors hd))
        (abs_nonneg (BoundingSieve.lambdaSquared w d)) using 1
      ring
    _ ≤ C * ∑ a ∈ s.prodPrimes.divisors, ∑ b ∈ s.prodPrimes.divisors,
        |w a| * |w b| * E (Nat.lcm a b) :=
      mul_le_mul_of_nonneg_left (lambdaSquared_weighted_abs_le BoundingSieve.prodPrimes_ne_zero w
          E hE) hC
    _ ≤ C * ∑ a ∈ s.prodPrimes.divisors, ∑ b ∈ s.prodPrimes.divisors,
        (|w a| * E a) * (|w b| * E b) := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      convert mul_le_mul_of_nonneg_left (hlcm a (Nat.dvd_of_mem_divisors ha) b
          (Nat.dvd_of_mem_divisors hb))
        (mul_nonneg (abs_nonneg (w a)) (abs_nonneg (w b))) using 1
      ring
    _ = _ := by rw [pow_two, Finset.sum_mul_sum]

/-- A coefficient sum supported up to `R` inherits a pointwise power bound. -/
theorem coefficient_sum_le_rpow {P : ℕ} (w E : ℕ → ℝ) {R K η : ℝ}
    (hR : 1 ≤ R) (hK : 0 ≤ K) (hη : 0 ≤ η)
    (hsupport : ∀ d : ℕ, R < d → w d = 0)
    (hbound : ∀ d, d ∣ P → d ≠ 0 → |w d| * E d ≤ K * (d : ℝ) ^ η) :
    (∑ d ∈ P.divisors, |w d| * E d) ≤ K * R ^ (1 + η) := by
  let S := P.divisors.filter (fun d : ℕ => (d : ℝ) ≤ R)
  have heq : (∑ d ∈ P.divisors, |w d| * E d) = ∑ d ∈ S, |w d| * E d := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro d hd hnot
    have hRd : R < d := lt_of_not_ge (fun h => hnot (Finset.mem_filter.mpr ⟨hd, h⟩))
    rw [hsupport d hRd, abs_zero, zero_mul]
  have hcard : (S.card : ℝ) ≤ R := by
    have H : S.card ≤ ⌊R⌋₊ := by
      calc
        S.card ≤ (Finset.Icc 1 ⌊R⌋₊).card := Finset.card_le_card (by
          intro d hd
          obtain ⟨hd, hdR⟩ := Finset.mem_filter.mp hd
          exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,
            (Nat.le_floor_iff (zero_le_one.trans hR)).mpr hdR⟩)
        _ = _ := by simp
    exact (by exact_mod_cast H : (S.card : ℝ) ≤ ⌊R⌋₊).trans (Nat.floor_le (zero_le_one.trans hR))
  rw [heq]
  calc
    _ ≤ S.card * (K * R ^ η) := by
      simpa only [nsmul_eq_mul] using Finset.sum_le_card_nsmul S (fun d => |w d| * E d) (K * R ^
          η) (by
        intro d hd
        obtain ⟨hd, hdR⟩ := Finset.mem_filter.mp hd
        exact (hbound d (Nat.dvd_of_mem_divisors hd) (Nat.pos_of_mem_divisors hd).ne').trans
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg d) hdR hη) hK))
    _ ≤ R * (K * R ^ η) := mul_le_mul_of_nonneg_right hcard (mul_nonneg hK (Real.rpow_nonneg
        (zero_le_one.trans hR) η))
    _ = _ := by rw [Real.rpow_add (zero_lt_one.trans_le hR), Real.rpow_one]; ring

/-- The error is of order `R^(2+2η)` whenever the weighted coefficients have a
uniform `d^η` majorant. -/
theorem selberg_errSum_le_rpow (s : BoundingSieve) (w E : ℕ → ℝ) {C R K η : ℝ}
    (hC : 0 ≤ C) (hR : 1 ≤ R) (hK : 0 ≤ K) (hη : 0 ≤ η)
    (hE : ∀ d, d ∣ s.prodPrimes → 0 ≤ E d)
    (hlcm : ∀ a, a ∣ s.prodPrimes → ∀ b, b ∣ s.prodPrimes → E (Nat.lcm a b) ≤ E a * E b)
    (herr : ∀ d, d ∣ s.prodPrimes → |s.rem d| ≤ C * E d)
    (hsupport : ∀ d : ℕ, R < d → w d = 0)
    (hbound : ∀ d, d ∣ s.prodPrimes → d ≠ 0 → |w d| * E d ≤ K * (d : ℝ) ^ η) :
    s.errSum (BoundingSieve.lambdaSquared w) ≤ C * K ^ 2 * R ^ (2 + 2 * η) := by
  have H := coefficient_sum_le_rpow w E hR hK hη hsupport hbound
  have hsum : 0 ≤ ∑ d ∈ s.prodPrimes.divisors, |w d| * E d :=
    Finset.sum_nonneg (fun d hd => mul_nonneg (abs_nonneg _) (hE d (Nat.dvd_of_mem_divisors hd)))
  calc
    _ ≤ C * (∑ d ∈ s.prodPrimes.divisors, |w d| * E d) ^ 2 := selberg_errSum_le_square s w E hC hE
        hlcm herr
    _ ≤ C * (K * R ^ (1 + η)) ^ 2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hsum H 2) hC
    _ = _ := by
      rw [mul_pow, ← Real.rpow_mul_natCast (zero_le_one.trans hR)]
      norm_num only [Nat.cast_ofNat]
      rw [show (1 + η) * (2 : ℝ) = 2 + 2 * η by ring]
      ring

/-- A quantitative Selberg upper bound, uniform in the sieve and its prime set.
The constant depends only on the dimension and the error exponent. -/
theorem exists_selberg_upper_bound {g η : ℝ} (hg : 1 ≤ g) (hη : 0 < η) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (s : BoundingSieve) (z C : ℝ),
      2 ≤ z → 16 ≤ Real.log z → 0 ≤ C → 0 ≤ s.totalMass →
      (∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) ≤ z) →
      (∀ p ∈ s.prodPrimes.primeFactors, s.nu p ≤ g / p) →
      (∀ p ∈ s.prodPrimes.primeFactors, s.nu p ≤ 1 - 1 / (p : ℝ)) →
      (∀ d, d ∣ s.prodPrimes → |s.rem d| ≤ C * g ^ d.primeFactors.card) →
      s.siftedSum ≤ 4 * s.totalMass * (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) +
        C * K * z ^ (4 * g * (1 + η)) := by
  obtain ⟨K, hK, hcoef⟩ := exists_selberg_weighted_coefficient_bound hg hη
  refine ⟨K ^ 2, one_le_pow₀ hK, ?_⟩
  intro s z C hz hzlog hC hmass hprimes hdim hgap herr
  have hg₀ : 0 < g := zero_lt_one.trans_le hg
  have hz₀ : 0 < z := by linarith
  have hR : 1 ≤ z ^ (2 * g) := (Real.one_lt_rpow (by linarith) (by positivity)).le
  have Herror := selberg_errSum_le_rpow s (selbergWeights s (z ^ (2 * g)))
    (fun d => g ^ d.primeFactors.card) hC hR (zero_le_one.trans hK) hη.le
    (fun d _ => pow_nonneg (zero_le_one.trans hg) _)
    (fun a ha b hb => primeFactorPower_lcm_le hg
      (ne_zero_of_dvd_ne_zero BoundingSieve.prodPrimes_ne_zero ha)
      (ne_zero_of_dvd_ne_zero BoundingSieve.prodPrimes_ne_zero hb))
    herr (fun d hd => selbergWeights_eq_zero_of_lt s hd)
    (fun d hd _ => hcoef s z hz hzlog hprimes hdim hgap d hd)
  have hmain : s.totalMass / selbergDenominator s (z ^ (2 * g)) ≤
      4 * s.totalMass * (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) := by
    have H := mul_le_mul_of_nonneg_left
      (selbergDenominator_inv_le s hz hzlog hg₀ hprimes hdim) hmass
    simpa only [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using H
  have H := (selberg_siftedSum_le s hR).trans (add_le_add hmain Herror)
  convert H using 1
  rw [← Real.rpow_mul hz₀.le]
  congr 3
  ring

end NairTenenbaum
