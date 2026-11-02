/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.NumberFields.ArithmeticLogDerivative
public import LeanPool.NairTenenbaum.NumberFields.GeometricEulerDerivative
public import LeanPool.NairTenenbaum.NumberFields.PrimeIdealResidueDegree

/-! # Local ideal von Mangoldt coefficients -/

@[expose] public section

namespace NairTenenbaum

open Finset NumberField ArithmeticFunction

theorem arithmeticPrimeSeries_logWeight (f : ArithmeticFunction ℝ) {p : ℕ} (_hp : p.Prime) :
    arithmeticPrimeSeries (arithmeticLogWeight f) p =
      PowerSeries.C (Real.log p) * powerSeriesEulerDerivative (arithmeticPrimeSeries f p) := by
  ext k
  rw [arithmeticPrimeSeries_coeff, arithmeticLogWeight_apply, PowerSeries.coeff_C_mul,
    powerSeriesEulerDerivative_coeff, arithmeticPrimeSeries_coeff, Nat.cast_pow, Real.log_pow]
  ring

variable (K : Type*) [Field K] [NumberField K]

theorem idealLocalEulerPolynomial_coe {p : ℕ} :
    (idealLocalEulerPolynomial K p : PowerSeries ℝ) =
      ∏ P : primeIdealSupport K p, (1 - PowerSeries.X ^ P.1.inertiaDeg ℤ) := by
  unfold idealLocalEulerPolynomial weightedEulerPolynomial
  change Polynomial.coeToPowerSeries.ringHom (∏ P : primeIdealSupport K p,
    (1 - Polynomial.X ^ P.1.inertiaDeg ℤ)) = _
  rw [map_prod]
  simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_sub,
    Polynomial.coe_one, Polynomial.coe_pow, Polynomial.coe_X]

theorem idealNormArithmetic_series_eq_geometric_product {p : ℕ} (hp : p.Prime) :
    arithmeticPrimeSeries (idealNormArithmetic K) p =
      ∏ P : primeIdealSupport K p,
        weightedGeometricSeries (P.1.inertiaDeg ℤ) (primeIdealSupport_inertiaDeg_pos hp P.2).ne'
            := by
  let G := ∏ P : primeIdealSupport K p,
    weightedGeometricSeries (P.1.inertiaDeg ℤ) (primeIdealSupport_inertiaDeg_pos hp P.2).ne'
  have HG : G * (idealLocalEulerPolynomial K p : PowerSeries ℝ) = 1 := by
    rw [idealLocalEulerPolynomial_coe]
    dsimp [G]
    rw [← prod_mul_distrib]
    simp only [weightedGeometricSeries_mul_one_sub, prod_const_one]
  have HA := idealNormArithmetic_series_mul_euler K hp
  change arithmeticPrimeSeries (idealNormArithmetic K) p = G
  calc
    _ = arithmeticPrimeSeries (idealNormArithmetic K) p *
        ((idealLocalEulerPolynomial K p : PowerSeries ℝ) * G) := by rw [mul_comm _ G, HG, mul_one]
    _ = G := by rw [← mul_assoc, HA, one_mul]

theorem idealVonMangoldt_series {p : ℕ} (hp : p.Prime) :
    arithmeticPrimeSeries (idealVonMangoldt K) p = PowerSeries.C (Real.log p) *
      ∑ P : primeIdealSupport K p, (P.1.inertiaDeg ℤ : PowerSeries ℝ) *
        (weightedGeometricSeries (P.1.inertiaDeg ℤ) (primeIdealSupport_inertiaDeg_pos hp P.2).ne'
            - 1) := by
  unfold idealVonMangoldt arithmeticLogDerivative
  rw [arithmeticPrimeSeries_mul _ _ hp, arithmeticPrimeSeries_logWeight _ hp,
    idealNormInverse_series_eq_euler K hp, mul_assoc,
    idealNormArithmetic_series_eq_geometric_product K hp, idealLocalEulerPolynomial_coe,
    powerSeriesEulerDerivative_prod_mul_inverse _ _ _
      (fun P _ => weightedGeometricSeries_mul_one_sub _ _)]
  simp only [weightedGeometricSeries_eulerDerivative]

theorem idealVonMangoldt_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    idealVonMangoldt K (p ^ k) = Real.log p *
      ∑ P : primeIdealSupport K p,
        if P.1.inertiaDeg ℤ ∣ k then (P.1.inertiaDeg ℤ : ℝ) else 0 := by
  rw [← arithmeticPrimeSeries_coeff, idealVonMangoldt_series K hp, PowerSeries.coeff_C_mul, map_sum]
  congr 1
  apply sum_congr rfl
  intro P _
  rw [PowerSeries.coeff_natCast_mul, map_sub, weightedGeometricSeries_coeff, PowerSeries.coeff_one]
  simp only [hk, ite_false, sub_zero]
  split_ifs <;> simp

theorem idealVonMangoldt_prime_pow_nonneg {p : ℕ} (hp : p.Prime) (k : ℕ) :
    0 ≤ idealVonMangoldt K (p ^ k) := by
  by_cases hk : k = 0
  · simp [hk, idealVonMangoldt_one]
  rw [idealVonMangoldt_prime_pow K hp hk]
  apply mul_nonneg (Real.log_nonneg (by exact_mod_cast hp.one_le))
  apply sum_nonneg
  intro P _
  split_ifs <;> positivity

theorem idealVonMangoldt_prime_pow_le {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    idealVonMangoldt K (p ^ k) ≤ (Module.finrank ℚ K : ℝ) * Real.log p := by
  rw [idealVonMangoldt_prime_pow K hp hk, mul_comm (Module.finrank ℚ K : ℝ)]
  apply mul_le_mul_of_nonneg_left _ (Real.log_nonneg (by exact_mod_cast hp.one_le))
  calc
    _ ≤ ∑ P : primeIdealSupport K p, (P.1.inertiaDeg ℤ : ℝ) := by
      apply sum_le_sum
      intro P _
      split_ifs
      · exact le_rfl
      · exact Nat.cast_nonneg _
    _ ≤ _ := by exact_mod_cast primeIdealSupport_sum_inertiaDeg_le (K := K) hp

end NairTenenbaum
