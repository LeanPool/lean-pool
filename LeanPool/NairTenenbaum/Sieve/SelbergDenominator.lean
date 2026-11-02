/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Arithmetic.PrimeLogSums
public import LeanPool.NairTenenbaum.Sieve.SelbergWeights
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Quantitative lower bounds for the Selberg denominator

The logarithmic moment of the full finite Euler product controls the mass lost
by truncating the divisor sum. This avoids any asymptotic prime number theorem.
-/

@[expose] public section

namespace NairTenenbaum

open Finset Nat Real

/-- First moment of an additive statistic under finite product weights. -/
theorem powerset_prod_sum_moment {ι : Type*} (S : Finset ι) (w v : ι → ℝ)
    (hw : ∀ p ∈ S, 1 + w p ≠ 0) :
    (∑ T ∈ S.powerset, (∏ p ∈ T, w p) * ∑ p ∈ T, v p) =
      (∏ p ∈ S, (1 + w p)) * ∑ p ∈ S, w p / (1 + w p) * v p := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
    rw [Finset.sum_powerset_insert hp]
    have hsub : ∀ T ∈ S.powerset, p ∉ T := fun T hT hpT => hp ((Finset.mem_powerset.mp hT) hpT)
    have H : (∑ T ∈ S.powerset, (∏ q ∈ insert p T, w q) * ∑ q ∈ insert p T, v q) =
        w p * v p * (∏ q ∈ S, (1 + w q)) +
          w p * ∑ T ∈ S.powerset, (∏ q ∈ T, w q) * ∑ q ∈ T, v q := by
      rw [Finset.prod_one_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro T hT
      rw [Finset.prod_insert (hsub T hT), Finset.sum_insert (hsub T hT)]
      ring
    rw [H, ih (fun q hq => hw q (Finset.mem_insert_of_mem hq)),
      Finset.prod_insert hp, Finset.sum_insert hp]
    have hp₀ := hw p (Finset.mem_insert_self p S)
    field_simp
    ring

/-- The logarithm is additive across the distinct prime factors of a
squarefree divisor, so its weighted mean is a sum of local means. -/
theorem squarefree_divisor_log_moment (f : ArithmeticFunction ℝ) (hf : f.IsMultiplicative)
    {n : ℕ} (hn : Squarefree n) (hlocal : ∀ p ∈ n.primeFactors, 1 + f p ≠ 0) :
    (∑ d ∈ n.divisors, f d * Real.log d) =
      (∑ d ∈ n.divisors, f d) * ∑ p ∈ n.primeFactors, f p / (1 + f p) * Real.log p := by
  calc
    _ = ∑ T ∈ n.primeFactors.powerset, (∏ p ∈ T, f p) * ∑ p ∈ T, Real.log p := by
      rw [← Nat.divisors_filter_squarefree_of_squarefree hn,
        Nat.sum_divisors_filter_squarefree hn.ne_zero, Nat.factors_eq]
      apply Finset.sum_congr rfl
      intro T hT
      have hT' : T ⊆ n.primeFactors := Finset.mem_powerset.mp hT
      rw [T.prod_val]
      simp only [id_eq]
      rw [hf.map_prod_of_subset_primeFactors n T hT', Nat.cast_prod,
        Real.log_prod (fun p hp => by
          exact_mod_cast (Nat.prime_of_mem_primeFactors (hT' hp)).ne_zero)]
    _ = _ := by
      rw [powerset_prod_sum_moment _ _ _ hlocal, hf.prodPrimeFactors_one_add_of_squarefree hn]

/-- The full Selberg denominator sum before truncation. -/
noncomputable def selbergFullSum (s : BoundingSieve) : ℝ :=
  ∑ d ∈ s.prodPrimes.divisors, s.selbergTerms d

theorem selbergFullSum_pos (s : BoundingSieve) : 0 < selbergFullSum s := by
  have H := Finset.single_le_sum (s := s.prodPrimes.divisors) (f := fun d => s.selbergTerms d)
    (fun d hd => (BoundingSieve.selbergTerms_pos (Nat.dvd_of_mem_divisors hd)).le)
    (Nat.mem_divisors.mpr ⟨one_dvd _, BoundingSieve.prodPrimes_ne_zero⟩)
  exact (BoundingSieve.selbergTerms_pos (s := s) (one_dvd _)).trans_le H

theorem selbergTerms_prime (s : BoundingSieve) {p : ℕ} (hp : p.Prime) :
    s.selbergTerms p = s.nu p / (1 - s.nu p) := by
  rw [BoundingSieve.selbergTerms_apply, hp.primeFactors, Finset.prod_singleton, div_eq_mul_inv]

theorem selbergFullSum_euler (s : BoundingSieve) :
    selbergFullSum s = ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)⁻¹ := by
  rw [selbergFullSum, ←
      BoundingSieve.selbergTerms_isMultiplicative.prodPrimeFactors_one_add_of_squarefree
      s.prodPrimes_squarefree]
  apply Finset.prod_congr rfl
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have h₀ : 1 - s.nu p ≠ 0 := (sub_pos.mpr (s.nu_lt_one_of_prime p hprime
      (Nat.dvd_of_mem_primeFactors hp))).ne'
  rw [selbergTerms_prime s hprime]
  field_simp
  ring

theorem selbergFullSum_log_moment (s : BoundingSieve) :
    (∑ d ∈ s.prodPrimes.divisors, s.selbergTerms d * Real.log d) =
      selbergFullSum s * ∑ p ∈ s.prodPrimes.primeFactors, s.nu p * Real.log p := by
  have hlocal : ∀ p ∈ s.prodPrimes.primeFactors, 1 + s.selbergTerms p ≠ 0 := by
    intro p hp
    have H := BoundingSieve.selbergTerms_pos (s := s) (Nat.dvd_of_mem_primeFactors hp)
    linarith
  rw [squarefree_divisor_log_moment _ BoundingSieve.selbergTerms_isMultiplicative
      s.prodPrimes_squarefree hlocal]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have h₀ : 1 - s.nu p ≠ 0 := (sub_pos.mpr (s.nu_lt_one_of_prime p hprime
      (Nat.dvd_of_mem_primeFactors hp))).ne'
  rw [selbergTerms_prime s hprime]
  field_simp
  ring

/-- The logarithmic moment bounds the mass omitted by truncation. -/
theorem selbergDenominator_log_tail (s : BoundingSieve) {R : ℝ} (hR : 0 < R) :
    Real.log R * (selbergFullSum s - selbergDenominator s R) ≤
      selbergFullSum s * ∑ p ∈ s.prodPrimes.primeFactors, s.nu p * Real.log p := by
  rw [← selbergFullSum_log_moment, selbergFullSum, selbergDenominator,
    ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  have hd₁ : (1 : ℝ) ≤ d := by exact_mod_cast Nat.pos_of_mem_divisors hd
  have hg : 0 ≤ s.selbergTerms d := (BoundingSieve.selbergTerms_pos (Nat.dvd_of_mem_divisors hd)).le
  split_ifs with h
  · simp only [sub_self, mul_zero]
    exact mul_nonneg hg (Real.log_nonneg hd₁)
  · simp only [sub_zero]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left
      (Real.log_le_log hR (le_of_lt (lt_of_not_ge h))) hg

/-- A relative logarithmic-moment bound retains a fixed fraction of the full
Euler product. -/
theorem selbergDenominator_lower (s : BoundingSieve) {R θ : ℝ} (hR : 1 < R)
    (hmoment : (∑ p ∈ s.prodPrimes.primeFactors, s.nu p * Real.log p) ≤ θ * Real.log R) :
    (1 - θ) * selbergFullSum s ≤ selbergDenominator s R := by
  have H := (selbergDenominator_log_tail s (zero_lt_one.trans hR)).trans
    (mul_le_mul_of_nonneg_left hmoment (selbergFullSum_pos s).le)
  have hlog := Real.log_pos hR
  nlinarith

/-- The local dimension bound controls the logarithmic moment by an elementary
weighted prime sum. -/
theorem selberg_prime_log_sum_le (s : BoundingSieve) {z g : ℝ} (hz : 2 ≤ z) (hg : 0 ≤ g)
    (hprimes : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) ≤ z)
    (hdim : ∀ p ∈ s.prodPrimes.primeFactors, s.nu p ≤ g / p) :
    (∑ p ∈ s.prodPrimes.primeFactors, s.nu p * Real.log p) ≤
      g * (Real.log 4 * (1 + Real.log z)) := by
  have hsub : s.prodPrimes.primeFactors ⊆ (Finset.Icc 0 ⌊z⌋₊).filter Nat.Prime := by
    intro p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _,
      (Nat.le_floor_iff (by linarith)).mpr (hprimes p hp)⟩, Nat.prime_of_mem_primeFactors hp⟩
  calc
    _ ≤ ∑ p ∈ s.prodPrimes.primeFactors, g * (Real.log p / p) := by
      apply Finset.sum_le_sum
      intro p hp
      have hlog : 0 ≤ Real.log p := Real.log_nonneg (by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le)
      convert mul_le_mul_of_nonneg_right (hdim p hp) hlog using 1
      ring
    _ = g * ∑ p ∈ s.prodPrimes.primeFactors, Real.log p / p := (Finset.mul_sum _ _ _).symm
    _ ≤ g * primeLogSum z := by
      apply mul_le_mul_of_nonneg_left _ hg
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro p hp _
      exact div_nonneg (Real.log_nonneg (by
        exact_mod_cast (Finset.mem_filter.mp hp).2.one_le)) (Nat.cast_nonneg p)
    _ ≤ _ := mul_le_mul_of_nonneg_left (primeLogSum_le hz) hg

/-- A cutoff `R=z^(2g)` retains at least one quarter of the full Euler product
once `log z≥16`. Both constants are independent of the selected sieve primes. -/
theorem selbergDenominator_quarter (s : BoundingSieve) {z g : ℝ}
    (hz : 2 ≤ z) (hzlog : 16 ≤ Real.log z) (hg : 0 < g)
    (hprimes : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) ≤ z)
    (hdim : ∀ p ∈ s.prodPrimes.primeFactors, s.nu p ≤ g / p) :
    selbergFullSum s / 4 ≤ selbergDenominator s (z ^ (2 * g)) := by
  have hz₀ : 0 < z := by linarith
  have hR : 1 < z ^ (2 * g) := Real.one_lt_rpow (by linarith) (by positivity)
  have hlog4 : Real.log 4 ≤ 7 / 5 := by
    rw [Real.log_four_eq]
    linarith [Real.log_two_lt_d9]
  have hmoment : (∑ p ∈ s.prodPrimes.primeFactors, s.nu p * Real.log p) ≤
      (3 / 4 : ℝ) * Real.log (z ^ (2 * g)) := by
    calc
      _ ≤ g * (Real.log 4 * (1 + Real.log z)) := selberg_prime_log_sum_le s hz hg.le hprimes hdim
      _ ≤ g * ((3 / 2 : ℝ) * Real.log z) := by
        apply mul_le_mul_of_nonneg_left _ hg.le
        have H := mul_le_mul_of_nonneg_right hlog4 (by linarith : 0 ≤ 1 + Real.log z)
        nlinarith
      _ = _ := by rw [Real.log_rpow hz₀]; ring
  have H := selbergDenominator_lower s hR hmoment
  convert H using 1
  ring

/-- The optimized main sieve coefficient is bounded by four times the sifting
Euler product. -/
theorem selbergDenominator_inv_le (s : BoundingSieve) {z g : ℝ}
    (hz : 2 ≤ z) (hzlog : 16 ≤ Real.log z) (hg : 0 < g)
    (hprimes : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) ≤ z)
    (hdim : ∀ p ∈ s.prodPrimes.primeFactors, s.nu p ≤ g / p) :
    (selbergDenominator s (z ^ (2 * g)))⁻¹ ≤
      4 * ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) := by
  have H := selbergDenominator_quarter s hz hzlog hg hprimes hdim
  have hpos : 0 < selbergFullSum s / 4 := div_pos (selbergFullSum_pos s) (by norm_num)
  have HI := one_div_le_one_div_of_le hpos H
  rw [one_div, one_div, inv_div, selbergFullSum_euler, Finset.prod_inv_distrib] at HI
  simpa only [inv_inv, div_eq_mul_inv] using HI

end NairTenenbaum
