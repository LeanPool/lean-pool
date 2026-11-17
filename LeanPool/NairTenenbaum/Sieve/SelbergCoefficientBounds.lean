/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.PrimeFactorBounds
public import LeanPool.NairTenenbaum.Sieve.SelbergDenominator

/-! # Bounds for the optimized Selberg coefficients -/

@[expose] public section

namespace NairTenenbaum

open Finset Nat Real
open scoped ArithmeticFunction.Moebius

theorem upperDivisorInverse_eq_sum {P d : ℕ} (hP : P ≠ 0) (hd : d ∣ P) (y : ℕ → ℝ) :
    upperDivisorInverse P y d = upperDivisorSum P (fun e => (μ (e / d) : ℝ) * y e) d := by
  rw [upperDivisorSum_eq_complement hP hd]
  apply Finset.sum_congr rfl
  intro k _
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm d k]

theorem upperDivisorSum_multiplicative (f : ArithmeticFunction ℝ) (hf : f.IsMultiplicative)
    {P d : ℕ} (hP : Squarefree P) (hd : d ∣ P) :
    upperDivisorSum P f d = f d * ∑ k ∈ (P / d).divisors, f k := by
  rw [upperDivisorSum_eq_complement hP.ne_zero hd]
  have hcop : Nat.Coprime d (P / d) := Nat.coprime_of_squarefree_mul
    (by simpa only [Nat.mul_div_cancel' hd] using hP)
  calc
    _ = ∑ k ∈ (P / d).divisors, f d * f (P / d / k) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkq := Nat.dvd_of_mem_divisors hk
      have heq : P / k = d * (P / d / k) := by
        calc
          _ = (d * (P / d)) / k := by rw [Nat.mul_div_cancel' hd]
          _ = _ := Nat.mul_div_assoc d hkq
      rw [heq, hf.map_mul_of_coprime (hcop.of_dvd_right (Nat.div_dvd_of_dvd hkq))]
    _ = _ := by rw [← Finset.mul_sum, Nat.sum_div_divisors]

theorem selberg_upper_sum_le (s : BoundingSieve) {d : ℕ} (hd : d ∣ s.prodPrimes) :
    upperDivisorSum s.prodPrimes s.selbergTerms d ≤ s.selbergTerms d * selbergFullSum s := by
  rw [upperDivisorSum_multiplicative _ BoundingSieve.selbergTerms_isMultiplicative
      s.prodPrimes_squarefree hd]
  apply mul_le_mul_of_nonneg_left _ (BoundingSieve.selbergTerms_pos hd).le
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (Nat.divisors_subset_of_dvd BoundingSieve.prodPrimes_ne_zero (Nat.div_dvd_of_dvd hd))
  intro e he _
  exact (BoundingSieve.selbergTerms_pos (Nat.dvd_of_mem_divisors he)).le

theorem selbergDiagonal_abs_le (s : BoundingSieve) {R : ℝ} (hR : 1 ≤ R)
    {d : ℕ} (hd : d ∣ s.prodPrimes) :
    |selbergDiagonal s R d| ≤ s.selbergTerms d / selbergDenominator s R := by
  have hg := BoundingSieve.selbergTerms_pos (s := s) hd
  have hG := selbergDenominator_pos s hR
  have hμ : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
  unfold selbergDiagonal
  split_ifs
  · rw [abs_div, abs_mul, abs_of_pos hg, abs_of_pos hG]
    exact div_le_div_of_nonneg_right (by nlinarith) hG.le
  · simpa only [abs_zero] using (div_pos hg hG).le

/-- A coefficient costs only its local sifting correction, times the ratio
between the full and truncated denominators. -/
theorem selbergWeights_abs_le_ratio (s : BoundingSieve) {R : ℝ} (hR : 1 ≤ R)
    {d : ℕ} (hd : d ∣ s.prodPrimes) :
    |selbergWeights s R d| ≤ (selbergFullSum s / selbergDenominator s R) *
      ∏ p ∈ d.primeFactors, (1 - s.nu p)⁻¹ := by
  have hν := BoundingSieve.nu_pos_of_dvd_prodPrimes (s := s) hd
  have hG := selbergDenominator_pos s hR
  have H : |upperDivisorInverse s.prodPrimes (selbergDiagonal s R) d| ≤
      upperDivisorSum s.prodPrimes s.selbergTerms d / selbergDenominator s R := by
    rw [upperDivisorInverse_eq_sum BoundingSieve.prodPrimes_ne_zero hd, upperDivisorSum,
      upperDivisorSum, Finset.sum_div]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
    intro e he
    split_ifs
    · rw [abs_mul]
      have hμ : |(μ (e / d) : ℝ)| ≤ 1 := by
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := e / d))
      calc
        _ ≤ 1 * |selbergDiagonal s R e| := mul_le_mul_of_nonneg_right hμ (abs_nonneg _)
        _ ≤ _ := by
          simpa only [one_mul] using selbergDiagonal_abs_le s hR (Nat.dvd_of_mem_divisors he)
    · simp
  rw [selbergWeights, ite_eq_left hd, abs_div, abs_of_pos hν]
  calc
    _ ≤ (upperDivisorSum s.prodPrimes s.selbergTerms d / selbergDenominator s R) / s.nu d :=
      div_le_div_of_nonneg_right H hν.le
    _ ≤ (s.selbergTerms d * selbergFullSum s / selbergDenominator s R) / s.nu d :=
      div_le_div_of_nonneg_right (div_le_div_of_nonneg_right (selberg_upper_sum_le s hd) hG.le)
          hν.le
    _ = _ := by
      rw [BoundingSieve.selbergTerms_apply]
      field_simp

theorem selbergWeights_abs_le_four (s : BoundingSieve) {z g : ℝ}
    (hz : 2 ≤ z) (hzlog : 16 ≤ Real.log z) (hg : 0 < g)
    (hprimes : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) ≤ z)
    (hdim : ∀ p ∈ s.prodPrimes.primeFactors, s.nu p ≤ g / p)
    {d : ℕ} (hd : d ∣ s.prodPrimes) :
    |selbergWeights s (z ^ (2 * g)) d| ≤ 4 * ∏ p ∈ d.primeFactors, (1 - s.nu p)⁻¹ := by
  have hR : 1 ≤ z ^ (2 * g) := (Real.one_lt_rpow (by linarith) (by positivity)).le
  have hratio : selbergFullSum s / selbergDenominator s (z ^ (2 * g)) ≤ 4 := by
    apply (div_le_iff₀ (selbergDenominator_pos s hR)).mpr
    have H := selbergDenominator_quarter s hz hzlog hg hprimes hdim
    linarith
  refine (selbergWeights_abs_le_ratio s hR hd).trans (mul_le_mul_of_nonneg_right hratio ?_)
  apply Finset.prod_nonneg
  intro p hp
  exact (inv_pos.mpr (sub_pos.mpr (s.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hp)
    ((Nat.dvd_of_mem_primeFactors hp).trans hd)))).le

/-- Integral root densities have a gap of at least `1/p` from one. Together
with the degree bound this bounds each local correction by `2g`. -/
theorem sieve_local_correction_le {g t : ℝ} {p : ℕ} (hg : 1 ≤ g) (hp : 0 < p)
    (ht : t < 1) (hdim : t ≤ g / p) (hgap : t ≤ 1 - 1 / (p : ℝ)) :
    (1 - t)⁻¹ ≤ 2 * g := by
  have hp₀ : (0 : ℝ) < p := by exact_mod_cast hp
  rw [← one_div]
  apply (div_le_iff₀ (sub_pos.mpr ht)).mpr
  by_cases hsmall : (p : ℝ) ≤ 2 * g
  · have H : 1 ≤ (1 - t) * (p : ℝ) := (div_le_iff₀ hp₀).mp (by linarith : 1 / (p : ℝ) ≤ 1 - t)
    nlinarith [mul_le_mul_of_nonneg_left hsmall (sub_nonneg.mpr ht.le)]
  · have H := (le_div_iff₀ hp₀).mp hdim
    have ht' : t ≤ 1 / 2 := by nlinarith
    nlinarith

/-- Weighted Selberg coefficients admit arbitrarily small power majorants,
with a constant depending only on the dimension and the chosen exponent. -/
theorem exists_selberg_weighted_coefficient_bound {g η : ℝ} (hg : 1 ≤ g) (hη : 0 < η) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (s : BoundingSieve) (z : ℝ),
      2 ≤ z → 16 ≤ Real.log z →
      (∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) ≤ z) →
      (∀ p ∈ s.prodPrimes.primeFactors, s.nu p ≤ g / p) →
      (∀ p ∈ s.prodPrimes.primeFactors, s.nu p ≤ 1 - 1 / (p : ℝ)) →
      ∀ d, d ∣ s.prodPrimes →
      |selbergWeights s (z ^ (2 * g)) d| * g ^ d.primeFactors.card ≤ K * (d : ℝ) ^ η := by
  obtain ⟨K, hK, hbound⟩ := exists_primeFactorPower_le_rpow (K := 2 * g ^ 2) (by nlinarith) hη
  refine ⟨4 * K, by linarith, ?_⟩
  intro s z hz hzlog hprimes hdim hgap d hd
  have hloc : (∏ p ∈ d.primeFactors, (1 - s.nu p)⁻¹) ≤ (2 * g) ^ d.primeFactors.card := by
    rw [← Finset.prod_const]
    apply Finset.prod_le_prod₀
    · intro p hp
      exact (inv_pos.mpr (sub_pos.mpr (s.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hp)
        ((Nat.dvd_of_mem_primeFactors hp).trans hd)))).le
    · intro p hp
      have hpP := Nat.primeFactors_mono hd BoundingSieve.prodPrimes_ne_zero hp
      exact sieve_local_correction_le hg (Nat.prime_of_mem_primeFactors hp).pos
        (s.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hp) ((Nat.dvd_of_mem_primeFactors
            hp).trans hd))
        (hdim p hpP) (hgap p hpP)
  have hw := (selbergWeights_abs_le_four s hz hzlog (zero_lt_one.trans_le hg) hprimes hdim hd).trans
    (mul_le_mul_of_nonneg_left hloc (by norm_num))
  calc
    _ ≤ (4 * (2 * g) ^ d.primeFactors.card) * g ^ d.primeFactors.card :=
      mul_le_mul_of_nonneg_right hw (pow_nonneg (zero_le_one.trans hg) _)
    _ = 4 * (2 * g ^ 2) ^ d.primeFactors.card := by rw [mul_assoc, ← mul_pow]; congr 2; ring
    _ ≤ 4 * (K * (d : ℝ) ^ η) := mul_le_mul_of_nonneg_left
      (hbound d (ne_zero_of_dvd_ne_zero BoundingSieve.prodPrimes_ne_zero hd)) (by norm_num)
    _ = _ := by ring

end NairTenenbaum
