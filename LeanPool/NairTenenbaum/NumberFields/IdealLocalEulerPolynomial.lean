/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.WeightedGeometricPolynomial
public import LeanPool.NairTenenbaum.NumberFields.DirichletInverseGrowth
public import LeanPool.NairTenenbaum.NumberFields.IdealMultiplicityVectors
public import LeanPool.NairTenenbaum.NumberFields.RootIdealCorrection

/-! # The polynomial inverse of the local ideal-counting series -/

@[expose] public section

namespace NairTenenbaum

open Finset NumberField Polynomial ArithmeticFunction

/-- The power series obtained by restricting an arithmetic function to powers of a prime. -/
noncomputable def arithmeticPrimeSeries (f : ArithmeticFunction ℝ) (p : ℕ) : PowerSeries ℝ :=
  PowerSeries.mk (fun k => f (p ^ k))

@[simp] theorem arithmeticPrimeSeries_coeff (f : ArithmeticFunction ℝ) (p k : ℕ) :
    PowerSeries.coeff k (arithmeticPrimeSeries f p) = f (p ^ k) := PowerSeries.coeff_mk _ _

theorem arithmeticPrimeSeries_mul (f g : ArithmeticFunction ℝ) {p : ℕ} (hp : p.Prime) :
    arithmeticPrimeSeries (f * g) p = arithmeticPrimeSeries f p * arithmeticPrimeSeries g p := by
  ext k
  rw [arithmeticPrimeSeries_coeff, arithmeticFunction_mul_prime_pow _ _ hp, PowerSeries.coeff_mul]
  simp only [arithmeticPrimeSeries_coeff, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

@[simp] theorem arithmeticPrimeSeries_one {p : ℕ} (hp : p.Prime) :
    arithmeticPrimeSeries 1 p = 1 := by
  ext k
  rw [arithmeticPrimeSeries_coeff]
  by_cases hk : k = 0
  · simp [hk]
  · simp [one_apply_ne (one_lt_pow₀ hp.one_lt hk).ne', PowerSeries.coeff_one, hk]

variable (K : Type*) [Field K] [NumberField K]

/-- The finite polynomial inverse of the local ideal-norm Euler factor. -/
noncomputable def idealLocalEulerPolynomial (p : ℕ) : ℝ[X] :=
  weightedEulerPolynomial (fun P : primeIdealSupport K p => P.1.inertiaDeg ℤ)

theorem idealNormArithmetic_series_mul_euler {p : ℕ} (hp : p.Prime) :
    arithmeticPrimeSeries (idealNormArithmetic K) p * (idealLocalEulerPolynomial K p : PowerSeries
        ℝ) = 1 := by
  ext k
  let w : primeIdealSupport K p → ℕ := fun P => P.1.inertiaDeg ℤ
  have hw (P : primeIdealSupport K p) : 0 < w P := primeIdealSupport_inertiaDeg_pos hp P.2
  have H := weightedGeometricPolynomial_mul_euler_coeff w hw (le_refl k)
  rw [← Polynomial.coeff_coe] at H
  have HE : PowerSeries.coeff k
      (arithmeticPrimeSeries (idealNormArithmetic K) p * (idealLocalEulerPolynomial K p :
          PowerSeries ℝ)) =
      (weightedGeometricPolynomial w k * weightedEulerPolynomial w).coeff k := by
    rw [PowerSeries.coeff_mul, Polynomial.coeff_mul]
    apply sum_congr rfl
    intro ij hij
    rw [arithmeticPrimeSeries_coeff, Polynomial.coeff_coe,
      idealNormArithmetic_apply_pos K (pow_pos hp.pos _), idealNormCount_prime_pow_eq_card_vectors
          hp,
      weightedGeometricPolynomial_coeff w hw (by
        have HH := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
        omega)]
    rfl
  rw [HE]
  simpa only [Polynomial.coeff_coe, Polynomial.coeff_one, PowerSeries.coeff_one] using H

theorem idealNormInverse_series_eq_euler {p : ℕ} (hp : p.Prime) :
    arithmeticPrimeSeries (idealNormInverse K) p = (idealLocalEulerPolynomial K p : PowerSeries ℝ)
        := by
  have H := congrArg (fun f : ArithmeticFunction ℝ => arithmeticPrimeSeries f p)
    (idealNormArithmetic_mul_inverse K)
  rw [arithmeticPrimeSeries_mul _ _ hp, arithmeticPrimeSeries_one hp] at H
  calc
    _ = arithmeticPrimeSeries (idealNormInverse K) p *
        (arithmeticPrimeSeries (idealNormArithmetic K) p * (idealLocalEulerPolynomial K p :
            PowerSeries ℝ)) := by
      rw [idealNormArithmetic_series_mul_euler K hp, mul_one]
    _ = (arithmeticPrimeSeries (idealNormArithmetic K) p * arithmeticPrimeSeries (idealNormInverse
        K) p) *
        (idealLocalEulerPolynomial K p : PowerSeries ℝ) := by ring
    _ = _ := by rw [H, one_mul]

end NairTenenbaum
