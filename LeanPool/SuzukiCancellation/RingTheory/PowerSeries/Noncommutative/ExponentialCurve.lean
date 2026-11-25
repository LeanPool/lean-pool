/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.RingTheory.PowerSeries.Noncommutative.SeriesDerivative
public import Mathlib.Algebra.Lie.OfAssociative

import Mathlib.Tactic.NoncommRing

/-!
# Exponential curves over noncommutative algebras

An extra formal parameter separates the differential identities for an
exponential from evaluation in a positive homogeneous series. The identities
keep arbitrary powers of the exponent intact.
-/

@[expose] public noncomputable section

namespace FQFP

open PowerSeries

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- The curve `exp(s a)` in an auxiliary formal variable `s`. -/
def exponentialCurve (a : A) : PowerSeries A :=
  mk fun n ↦ (Nat.factorial n : ℚ)⁻¹ • a ^ n

@[simp]
theorem coeff_exponentialCurve (a : A) (n : ℕ) :
    coeff n (exponentialCurve a) = (Nat.factorial n : ℚ)⁻¹ • a ^ n := by
  simp [exponentialCurve]

@[simp]
theorem constantCoeff_exponentialCurve (a : A) : constantCoeff (exponentialCurve a) = 1 := by
  simp [exponentialCurve]

@[simp]
theorem exponentialCurve_zero : exponentialCurve (0 : A) = 1 := by
  apply PowerSeries.ext
  intro n
  cases n <;> simp [coeff_one]

/-- An exponential-list factor is an exponential curve in the total-degree variable. -/
theorem expListSeries_cons_eq_exponentialCurve (a : A) (l : List A) :
    expListSeries (a :: l) = exponentialCurve a * expListSeries l := by
  rw [expListSeries_cons]
  rfl

private theorem factorial_succ_inv_mul (n : ℕ) :
    (n + 1 : ℚ) * (Nat.factorial (n + 1) : ℚ)⁻¹ = (Nat.factorial n : ℚ)⁻¹ := by
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add_one, mul_inv_rev]
  rw [mul_left_comm, mul_inv_cancel₀ (show (n + 1 : ℚ) ≠ 0 by positivity), mul_one]

/-- Differentiating an exponential curve multiplies by its exponent on the left. -/
theorem seriesDerivative_exponentialCurve (a : A) :
    seriesDerivative (exponentialCurve a) = C a * exponentialCurve a := by
  ext n
  simp only [coeff_seriesDerivative, coeff_exponentialCurve, coeff_C_mul, smul_smul,
    factorial_succ_inv_mul, mul_smul_comm, pow_succ']

/-- The exponent commutes with its exponential curve. -/
theorem exponentialCurve_mul_C (a : A) :
    exponentialCurve a * C a = C a * exponentialCurve a := by
  ext n
  simp only [coeff_mul_C, coeff_C_mul, coeff_exponentialCurve, smul_mul_assoc,
    mul_smul_comm, ← pow_succ, ← pow_succ']

/-- The inverse of an exponential curve is the curve of the negative exponent. -/
theorem exponentialCurve_mul_neg (a : A) : exponentialCurve a * exponentialCurve (-a) = 1 := by
  apply ext_seriesDerivative
  · rw [seriesDerivative_mul, seriesDerivative_exponentialCurve,
      seriesDerivative_exponentialCurve, ← exponentialCurve_mul_C, mul_assoc]
    simp only [map_neg, mul_neg, neg_mul, add_neg_cancel]
    exact (seriesDerivative_C (1 : A)).symm
  · simp

/-- A coefficientwise derivation obeys the linear adjoint equation on the right derivative. -/
theorem seriesDerivative_rightLogarithmicDerivative (D : A →ₗ[ℚ] A)
    (hD : ∀ a b, D (a * b) = D a * b + a * D b) (a : A) :
    seriesDerivative (mapSeriesLinear D (exponentialCurve a) * exponentialCurve (-a)) =
      C (D a) + C a * (mapSeriesLinear D (exponentialCurve a) * exponentialCurve (-a)) -
        (mapSeriesLinear D (exponentialCurve a) * exponentialCurve (-a)) * C a := by
  have hc : exponentialCurve (-a) * C a = C a * exponentialCurve (-a) := by
    simpa only [map_neg, mul_neg, neg_mul, neg_inj] using exponentialCurve_mul_C (-a)
  rw [seriesDerivative_mul, seriesDerivative_mapSeriesLinear,
    seriesDerivative_exponentialCurve, mapSeriesLinear_mul D hD, mapSeriesLinear_C,
    seriesDerivative_exponentialCurve]
  simp only [add_mul, mul_assoc, exponentialCurve_mul_neg, mul_one, map_neg, hc]
  noncomm_ring

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The coefficientwise adjoint is the difference of left and right multiplication. -/
theorem mapSeriesLinear_ad (a : A) (F : PowerSeries A) :
    mapSeriesLinear (LieAlgebra.ad ℚ A a) F = C a * F - F * C a := by
  ext n
  simp [LieAlgebra.ad, LieModule.toEnd, Ring.lie_def]

/-- The right differential of an exponential curve has the divided adjoint coefficients. -/
theorem coeff_succ_rightLogarithmicDerivative (D : A →ₗ[ℚ] A)
    (hD : ∀ a b, D (a * b) = D a * b + a * D b) (a : A) (n : ℕ) :
    coeff (n + 1) (mapSeriesLinear D (exponentialCurve a) * exponentialCurve (-a)) =
      (Nat.factorial (n + 1) : ℚ)⁻¹ • (LieAlgebra.ad ℚ A a ^ n) (D a) := by
  have hD1 : D 1 = 0 := by
    have h := hD 1 1
    simp only [mul_one, one_mul] at h
    exact add_left_cancel (h.symm.trans (add_zero (D 1)).symm)
  apply coeff_succ_of_seriesDerivative_eq_const_add_linear
  · simpa only [mapSeriesLinear_ad, add_sub_assoc] using
      seriesDerivative_rightLogarithmicDerivative D hD a
  · simp [hD1]

/-- Formal conjugation has exactly the exponential adjoint coefficients. -/
theorem coeff_conjugate_exponentialCurve (a b : A) (n : ℕ) :
    coeff n (exponentialCurve a * C b * exponentialCurve (-a)) =
      (Nat.factorial n : ℚ)⁻¹ • (LieAlgebra.ad ℚ A a ^ n) b := by
  have hc : exponentialCurve (-a) * C a = C a * exponentialCurve (-a) := by
    simpa only [map_neg, mul_neg, neg_mul, neg_inj] using exponentialCurve_mul_C (-a)
  have hF : seriesDerivative (exponentialCurve a * C b * exponentialCurve (-a)) =
      mapSeriesLinear (LieAlgebra.ad ℚ A a)
        (exponentialCurve a * C b * exponentialCurve (-a)) := by
    rw [mapSeriesLinear_ad, seriesDerivative_mul, seriesDerivative_mul,
      seriesDerivative_exponentialCurve, seriesDerivative_C, seriesDerivative_exponentialCurve]
    simp only [mul_zero, add_zero, mul_assoc, map_neg, hc]
    noncomm_ring
  simpa using coeff_of_seriesDerivative_eq_linear (LieAlgebra.ad ℚ A a) _ hF n

end FQFP
