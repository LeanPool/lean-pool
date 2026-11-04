/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Polynomials.RootCount
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.NumberTheory.SelbergSieve

/-! # Truncated Selberg weights

Möbius inversion over multiples constructs the Selberg coefficients from the
diagonal variables. This supplies the optimizing weights missing from the
quadratic-form identity in Mathlib.
-/

@[expose] public section

namespace NairTenenbaum

open Finset Nat
open scoped ArithmeticFunction.Moebius

/-- The sum of the sieve coefficients over divisors of an integer. -/
noncomputable def upperDivisorSum (P : ℕ) (f : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ e ∈ P.divisors, if d ∣ e then f e else 0

/-- Complementation reverses the divisor order. -/
theorem upperDivisorSum_eq_complement {P d : ℕ} (hP : P ≠ 0) (hd : d ∣ P) (f : ℕ → ℝ) :
    upperDivisorSum P f d = ∑ k ∈ (P / d).divisors, f (P / k) := by
  unfold upperDivisorSum
  rw [← Nat.sum_div_divisors P (fun e => if d ∣ e then f e else 0)]
  have hf : P.divisors.filter (fun k => d ∣ P / k) = (P / d).divisors := by
    rw [← Nat.divisors_filter_dvd_of_dvd hP (Nat.div_dvd_of_dvd hd)]
    apply Finset.filter_congr
    intro k hk
    rw [Nat.dvd_div_iff_mul_dvd (Nat.dvd_of_mem_divisors hk), Nat.dvd_div_iff_mul_dvd hd, mul_comm]
  rw [← Finset.sum_filter, hf]

/-- Inverse of summing over multiples, written using complementary divisors. -/
noncomputable def upperDivisorInverse (P : ℕ) (y : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ k ∈ (P / d).divisors, (μ (P / d / k) : ℝ) * y (P / k)

theorem upperDivisorSum_inverse {P d : ℕ} (hP : P ≠ 0) (hd : d ∣ P) (y : ℕ → ℝ) :
    upperDivisorSum P (upperDivisorInverse P y) d = y d := by
  rw [upperDivisorSum_eq_complement hP hd]
  let f : ℕ → ℝ := fun n => ∑ k ∈ n.divisors, (μ (n / k) : ℝ) * y (P / k)
  have hinv : ∀ n > 0, ∑ k ∈ n.divisors, f k = y (P / n) := by
    apply ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mpr
    intro n _
    exact Nat.sum_divisorsAntidiagonal' (fun a b => (μ a : ℝ) * y (P / b))
  have heq : (∑ k ∈ (P / d).divisors, upperDivisorInverse P y (P / k)) =
      ∑ k ∈ (P / d).divisors, f k := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkP : k ∣ P := (Nat.dvd_of_mem_divisors hk).trans (Nat.div_dvd_of_dvd hd)
    simp only [upperDivisorInverse, Nat.div_div_self hkP hP, f]
  rw [heq, hinv _ (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hP (Nat.div_dvd_of_dvd hd))),
    Nat.div_div_self hd hP]

theorem upperDivisorInverse_one (P : ℕ) (y : ℕ → ℝ) :
    upperDivisorInverse P y 1 = ∑ d ∈ P.divisors, (μ d : ℝ) * y d := by
  simp only [upperDivisorInverse, Nat.div_one]
  exact Nat.sum_div_divisors P (fun d => (μ d : ℝ) * y d)

/-- The truncated denominator of the Selberg sieve. -/
noncomputable def selbergDenominator (s : BoundingSieve) (R : ℝ) : ℝ :=
  ∑ d ∈ s.prodPrimes.divisors, if (d : ℝ) ≤ R then s.selbergTerms d else 0

theorem selbergDenominator_pos (s : BoundingSieve) {R : ℝ} (hR : 1 ≤ R) :
    0 < selbergDenominator s R := by
  have h1 : 0 < (if (1 : ℝ) ≤ R then s.selbergTerms 1 else 0) := by
    rw [ite_eq_left hR]
    exact BoundingSieve.selbergTerms_pos (one_dvd _)
  apply h1.trans_le
  unfold selbergDenominator
  have H := Finset.single_le_sum (s := s.prodPrimes.divisors)
    (f := fun d : ℕ => if (d : ℝ) ≤ R then s.selbergTerms d else 0)
    (fun d hd => by
      split_ifs
      · exact (BoundingSieve.selbergTerms_pos (Nat.dvd_of_mem_divisors hd)).le
      · rfl)
    (Nat.mem_divisors.mpr ⟨one_dvd _, BoundingSieve.prodPrimes_ne_zero⟩)
  simpa only [Nat.cast_one] using H

/-- The diagonal quadratic form associated with the Selberg weights. -/
noncomputable def selbergDiagonal (s : BoundingSieve) (R : ℝ) (d : ℕ) : ℝ :=
  if (d : ℝ) ≤ R then (μ d : ℝ) * s.selbergTerms d / selbergDenominator s R else 0

/-- Coefficients normalized to be one at `1`. -/
noncomputable def selbergWeights (s : BoundingSieve) (R : ℝ) (d : ℕ) : ℝ :=
  if d ∣ s.prodPrimes then upperDivisorInverse s.prodPrimes (selbergDiagonal s R) d / s.nu d else 0

theorem selbergWeights_transform (s : BoundingSieve) (R : ℝ) {l : ℕ} (hl : l ∣ s.prodPrimes) :
    (∑ d ∈ s.prodPrimes.divisors, if l ∣ d then s.nu d * selbergWeights s R d else 0) =
      selbergDiagonal s R l := by
  have H := upperDivisorSum_inverse BoundingSieve.prodPrimes_ne_zero hl (selbergDiagonal s R)
  rw [← H]
  apply Finset.sum_congr rfl
  intro d hd
  have hdP := Nat.dvd_of_mem_divisors hd
  rw [selbergWeights, ite_eq_left hdP]
  congr 1
  exact mul_div_cancel₀ _ (BoundingSieve.nu_ne_zero hdP)

theorem selbergWeights_one (s : BoundingSieve) {R : ℝ} (hR : 1 ≤ R) :
    selbergWeights s R 1 = 1 := by
  rw [selbergWeights, ite_eq_left (one_dvd _), s.nu_mult.map_one, div_one, upperDivisorInverse_one]
  have hμ (d : ℕ) (hd : d ∈ s.prodPrimes.divisors) : (μ d : ℝ) ^ 2 = 1 := by
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
      (BoundingSieve.squarefree_of_mem_divisors_prodPrimes hd)
  have H : (∑ d ∈ s.prodPrimes.divisors, (μ d : ℝ) * selbergDiagonal s R d) =
      selbergDenominator s R / selbergDenominator s R := by
    rw [selbergDenominator, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d hd
    unfold selbergDiagonal
    split_ifs with h
    · calc
        _ = (μ d : ℝ) ^ 2 * s.selbergTerms d / selbergDenominator s R := by ring
        _ = _ := by rw [hμ d hd, one_mul]; rfl
    · simp
  exact H.trans (div_self (selbergDenominator_pos s hR).ne')

/-- The optimized main quadratic form is exactly the reciprocal denominator. -/
theorem selbergWeights_mainSum (s : BoundingSieve) {R : ℝ} (hR : 1 ≤ R) :
    s.mainSum (BoundingSieve.lambdaSquared (selbergWeights s R)) =
      (selbergDenominator s R)⁻¹ := by
  rw [BoundingSieve.mainSum_lambdaSquared_eq_sum_mul_sum_sq]
  have hG := (selbergDenominator_pos s hR).ne'
  calc
    _ = ∑ d ∈ s.prodPrimes.divisors,
        (if (d : ℝ) ≤ R then s.selbergTerms d else 0) / (selbergDenominator s R) ^ 2 := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdP := Nat.dvd_of_mem_divisors hd
      rw [selbergWeights_transform s R hdP]
      have hg := (BoundingSieve.selbergTerms_pos hdP).ne'
      have hμ : (μ d : ℝ) ^ 2 = 1 := by
        exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
          (BoundingSieve.squarefree_of_dvd_prodPrimes hdP)
      unfold selbergDiagonal
      split_ifs
      · rw [div_pow, mul_pow, hμ, one_mul]
        field_simp
      · simp
    _ = selbergDenominator s R / (selbergDenominator s R) ^ 2 := by
      rw [← Finset.sum_div]
      rfl
    _ = _ := by field_simp

/-- The coefficients vanish beyond the chosen cutoff. -/
theorem selbergWeights_eq_zero_of_lt (s : BoundingSieve) {R : ℝ} {d : ℕ} (hRd : R < d) :
    selbergWeights s R d = 0 := by
  unfold selbergWeights
  split_ifs with hd
  · have H : upperDivisorInverse s.prodPrimes (selbergDiagonal s R) d = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hkq := Nat.dvd_of_mem_divisors hk
      have hkP := hkq.trans (Nat.div_dvd_of_dvd hd)
      have hdq : d ∣ s.prodPrimes / k := by
        apply (Nat.dvd_div_iff_mul_dvd hkP).mpr
        simpa only [mul_comm] using (Nat.dvd_div_iff_mul_dvd hd).mp hkq
      have hle : d ≤ s.prodPrimes / k := Nat.le_of_dvd
        (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero BoundingSieve.prodPrimes_ne_zero
          (Nat.div_dvd_of_dvd hkP))) hdq
      have hlt : R < (s.prodPrimes / k : ℕ) := hRd.trans_le (by exact_mod_cast hle)
      simp only [selbergDiagonal, ite_eq_right hlt.not_ge, mul_zero]
    rw [H, zero_div]
  · rfl

/-- An upper bound with the optimized main term and the explicit remainder sum.
Further estimates of the denominator and remainder are separate analytic steps. -/
theorem selberg_siftedSum_le (s : BoundingSieve) {R : ℝ} (hR : 1 ≤ R) :
    s.siftedSum ≤ s.totalMass / selbergDenominator s R +
      s.errSum (BoundingSieve.lambdaSquared (selbergWeights s R)) := by
  have H := s.siftedSum_le_mainSum_errSum_of_upperMoebius
    (BoundingSieve.lambdaSquared (selbergWeights s R))
    (BoundingSieve.upperMoebius_lambdaSquared _ (selbergWeights_one s hR))
  simpa only [selbergWeights_mainSum s hR, div_eq_mul_inv] using H

end NairTenenbaum
