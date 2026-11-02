/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.SquarefreeEulerBound
public import LeanPool.NairTenenbaum.Hooley.HooleyDifferentialInequality

/-! # Euler bound for the squarefree divisor Dirichlet series

The divisor series in the differential inequality is at most the exponential
of `2^t` times the prime root series. Convergence is proved for `σ>1`.
-/

@[expose] public section

namespace NairTenenbaum

open Finset Real Polynomial

/-- The prime Dirichlet series weighted by polynomial root counts. -/
noncomputable def rootPrimePowerSum (Q : ℤ[X]) (σ : ℝ) : ℝ :=
  ∑' p : Nat.Primes, (rootCount Q p.1 : ℝ) * (p.1 : ℝ) ^ (-σ)

theorem rootPrimePowerSum_nonneg (Q : ℤ[X]) (σ : ℝ) : 0 ≤ rootPrimePowerSum Q σ :=
  tsum_nonneg (fun _p => mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))

theorem summable_rootPrimePowerWeight {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun p : Nat.Primes => (rootCount Q p.1 : ℝ) * (p.1 : ℝ) ^ (-σ)) := by
  have H := (summable_hooleyDirichlet hQ (le_refl (0 : ℝ)) (by decide : 0 < 1) hσ).subtype Nat.Prime
  apply H.congr
  intro p
  dsimp only [Function.comp_def]
  simp [hooleyMomentCoefficient, p.2.squarefree]

theorem hooleyDivisorDirichletTerm_eq_primeProduct (Q : ℤ[X]) (t σ : ℝ) (n : ℕ) :
    hooleyMomentCoefficient Q t 1 n * (n : ℝ) ^ (-σ) =
      squarefreePrimeProduct (fun p => (2 : ℝ) ^ t * (rootCount Q p : ℝ) * (p : ℝ) ^ (-σ)) n := by
  by_cases hn : Squarefree n
  · simp only [hooleyMomentCoefficient, squarefreePrimeProduct, ite_eq_left hn,
      Nat.cast_one, div_one, hooleyMoment_one]
    rw [card_divisors_of_squarefree hn, Nat.cast_pow, Nat.cast_ofNat,
      ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2),
      prod_mul_distrib, prod_mul_distrib, prod_const,
      ← Nat.cast_prod, ← rootCount_squarefree hn,
      Real.finsetProd_rpow _ _ (fun _ _ => Nat.cast_nonneg _) (-σ),
      ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hn]
  · simp [hooleyMomentCoefficient, squarefreePrimeProduct, hn]

theorem hooleyDivisorDirichlet_le_exp_prime_sum {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    (t : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    hooleyDirichlet Q t 1 σ ≤ Real.exp ((2 : ℝ) ^ t * rootPrimePowerSum Q σ) := by
  have H := summable_and_tsum_squarefreePrimeProduct_le_exp
    (a := fun p => (2 : ℝ) ^ t * (rootCount Q p : ℝ) * (p : ℝ) ^ (-σ))
    (fun p _ => mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Nat.cast_nonneg _))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (by simpa only [mul_assoc] using (summable_rootPrimePowerWeight hQ hσ).mul_left ((2 : ℝ) ^ t))
  simpa only [hooleyDirichlet, hooleyDivisorDirichletTerm_eq_primeProduct, mul_assoc,
    tsum_mul_left, rootPrimePowerSum] using H.2

theorem hooleyDirichlet_le_divisorSeries {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    {t σ : ℝ} (ht : 0 ≤ t) {q : ℕ} (hq : 0 < q) (hσ : 1 < σ) :
    hooleyDirichlet Q t q σ ≤ hooleyDirichlet Q t 1 σ := by
  apply Summable.tsum_le_tsum _ (summable_hooleyDirichlet hQ ht hq hσ)
    (summable_hooleyDirichlet hQ ht (by decide) hσ)
  intro n
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  by_cases hn : Squarefree n
  · simp only [hooleyMomentCoefficient, ite_eq_left hn, Nat.cast_one, div_one, hooleyMoment_one]
    exact mul_le_mul_of_nonneg_right (hooleyMoment_rpow_le_card_rpow n hq ht) (Nat.cast_nonneg _)
  · simp [hooleyMomentCoefficient, hn]

theorem hooleyDirichlet_le_exp_prime_sum {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    {t σ : ℝ} (ht : 0 ≤ t) {q : ℕ} (hq : 0 < q) (hσ : 1 < σ) :
    hooleyDirichlet Q t q σ ≤ Real.exp ((2 : ℝ) ^ t * rootPrimePowerSum Q σ) :=
  (hooleyDirichlet_le_divisorSeries hQ ht hq hσ).trans
    (hooleyDivisorDirichlet_le_exp_prime_sum hQ t hσ)

end NairTenenbaum
