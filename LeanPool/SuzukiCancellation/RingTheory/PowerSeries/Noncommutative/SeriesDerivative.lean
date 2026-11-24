/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.RingTheory.PowerSeries.Noncommutative.PositiveSeries
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# Differentiation of series over noncommutative algebras

Coefficientwise linear maps commute with differentiation in the series variable.
The Leibniz rule holds over associative rational algebras, without commutativity.
-/

@[expose] public noncomputable section

namespace FQFP

open Finset PowerSeries

variable {M N : Type*} [Ring M] [Algebra ℚ M] [Ring N] [Algebra ℚ N]

/-- Apply a rational linear map to every coefficient of a formal series. -/
def mapSeriesLinear (D : M →ₗ[ℚ] N) : PowerSeries M →ₗ[ℚ] PowerSeries N where
  toFun p := mk fun n ↦ D (coeff n p)
  map_add' p q := by ext n; simp
  map_smul' r p := by ext n; simp

@[simp]
theorem coeff_mapSeriesLinear (D : M →ₗ[ℚ] N) (p : PowerSeries M) (n : ℕ) :
    coeff n (mapSeriesLinear D p) = D (coeff n p) := by simp [mapSeriesLinear]

@[simp]
theorem constantCoeff_mapSeriesLinear (D : M →ₗ[ℚ] N) (p : PowerSeries M) :
    constantCoeff (mapSeriesLinear D p) = D (constantCoeff p) := by
  simp only [← coeff_zero_eq_constantCoeff_apply, coeff_mapSeriesLinear]

/-- Differentiation in the formal series variable, with rational algebra coefficients. -/
def seriesDerivative : PowerSeries M →ₗ[ℚ] PowerSeries M where
  toFun p := mk fun n ↦ (n + 1 : ℚ) • coeff (n + 1) p
  map_add' p q := by ext n; simp [smul_add]
  map_smul' r p := by
    ext n
    simp only [coeff_mk, coeff_smul, RingHom.id_apply]
    exact smul_comm _ _ _

@[simp]
theorem coeff_seriesDerivative (p : PowerSeries M) (n : ℕ) :
    coeff n (seriesDerivative p) = (n + 1 : ℚ) • coeff (n + 1) p := by
  simp [seriesDerivative]

/-- Coefficientwise linear operations commute with differentiation in a different variable. -/
theorem seriesDerivative_mapSeriesLinear (D : M →ₗ[ℚ] N) (p : PowerSeries M) :
    seriesDerivative (mapSeriesLinear D p) = mapSeriesLinear D (seriesDerivative p) := by
  ext n
  simp

/-- A formal series is determined by its derivative and constant coefficient. -/
theorem ext_seriesDerivative {p q : PowerSeries M}
    (hd : seriesDerivative p = seriesDerivative q) (hc : constantCoeff p = constantCoeff q) :
    p = q := by
  ext n
  cases n with
  | zero => simpa only [coeff_zero_eq_constantCoeff_apply] using hc
  | succ n =>
    have h := congrArg (coeff n) hd
    simp only [coeff_seriesDerivative] at h
    have hi := congrArg (fun x : M ↦ (n + 1 : ℚ)⁻¹ • x) h
    simpa only [inv_smul_smul₀ (show (n + 1 : ℚ) ≠ 0 by positivity)] using hi

@[simp]
theorem mapSeriesLinear_C (D : M →ₗ[ℚ] N) (a : M) :
    mapSeriesLinear D (C a) = C (D a) := by
  ext n
  simp only [coeff_mapSeriesLinear, coeff_C]
  split_ifs <;> simp

@[simp]
theorem seriesDerivative_C (a : M) : seriesDerivative (C a) = 0 := by
  ext n
  simp

/-- Coefficients of a homogeneous linear differential equation in a formal parameter. -/
theorem coeff_of_seriesDerivative_eq_linear (T : M →ₗ[ℚ] M) (F : PowerSeries M)
    (hF : seriesDerivative F = mapSeriesLinear T F) (n : ℕ) :
    coeff n F = (Nat.factorial n : ℚ)⁻¹ • (T ^ n) (constantCoeff F) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := congrArg (coeff n) hF
    simp only [coeff_seriesDerivative, coeff_mapSeriesLinear, ih, map_smul] at h
    have hi := congrArg (fun x : M ↦ (n + 1 : ℚ)⁻¹ • x) h
    simp only [inv_smul_smul₀ (show (n + 1 : ℚ) ≠ 0 by positivity), smul_smul] at hi
    rw [hi, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add_one, mul_inv_rev,
      mul_comm ((n + 1 : ℚ)⁻¹), pow_succ', mul_apply_eq_comp]

/-- Coefficients of a constant-forced linear equation with zero initial value. -/
theorem coeff_succ_of_seriesDerivative_eq_const_add_linear (T : M →ₗ[ℚ] M)
    (F : PowerSeries M) (b : M) (hF : seriesDerivative F = C b + mapSeriesLinear T F)
    (hzero : constantCoeff F = 0) (n : ℕ) :
    coeff (n + 1) F = (Nat.factorial (n + 1) : ℚ)⁻¹ • (T ^ n) b := by
  induction n with
  | zero =>
    have h := congrArg (coeff 0) hF
    simpa [coeff_zero_eq_constantCoeff_apply, hzero] using h
  | succ n ih =>
    have h := congrArg (coeff (n + 1)) hF
    simp only [coeff_seriesDerivative, map_add, coeff_succ_C, zero_add,
      coeff_mapSeriesLinear, ih, map_smul] at h
    have hi := congrArg (fun x : M ↦ ((n + 1 : ℕ) + 1 : ℚ)⁻¹ • x) h
    simp only [Nat.cast_add, Nat.cast_one] at hi
    simp only [inv_smul_smul₀ (show (n + 1 + 1 : ℚ) ≠ 0 by positivity), smul_smul] at hi
    have hs : (n + 1 + 1 : ℚ)⁻¹ * (Nat.factorial (n + 1) : ℚ)⁻¹ =
        (Nat.factorial (n + 1 + 1) : ℚ)⁻¹ := by
      rw [Nat.factorial_succ (n + 1), Nat.cast_mul, Nat.cast_add_one, mul_inv_rev]
      simp only [Nat.cast_add, Nat.cast_one, mul_comm]
    rw [hi, hs, pow_succ', mul_apply_eq_comp]

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- The Leibniz rule extends coefficientwise to noncommutative formal series. -/
theorem mapSeriesLinear_mul (D : A →ₗ[ℚ] A)
    (hD : ∀ a b, D (a * b) = D a * b + a * D b) (p q : PowerSeries A) :
    mapSeriesLinear D (p * q) = mapSeriesLinear D p * q + p * mapSeriesLinear D q := by
  ext n
  simp only [coeff_mapSeriesLinear, coeff_mul, map_sum, hD, sum_add_distrib, map_add]

omit [Algebra ℚ A] in
private theorem coeff_trunc_mul (p q : PowerSeries A) (N n : ℕ) (hn : n < N) :
    (trunc N p * trunc N q).coeff n = coeff n (p * q) := by
  simp only [Polynomial.coeff_mul, coeff_mul]
  apply sum_congr rfl
  intro ij hij
  have hij' := mem_antidiagonal.mp hij
  rw [coeff_trunc, coeff_trunc, ite_eq_left (by lia : ij.1 < N),
    ite_eq_left (by lia : ij.2 < N)]

private theorem coeff_derivative_eq_smul (p : Polynomial A) (n : ℕ) :
    p.derivative.coeff n = (n + 1 : ℚ) • p.coeff (n + 1) := by
  simp only [Polynomial.coeff_derivative, ← Nat.cast_add_one,
    Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
  exact (Nat.cast_commute _ _).symm.eq

/-- The formal derivative satisfies Leibniz over noncommutative coefficients. -/
theorem seriesDerivative_mul (p q : PowerSeries A) :
    seriesDerivative (p * q) = seriesDerivative p * q + p * seriesDerivative q := by
  ext n
  have hd := congrArg (fun r : Polynomial A ↦ r.coeff n)
    (Polynomial.derivative_mul (f := trunc (n + 2) p) (g := trunc (n + 2) q))
  rw [coeff_derivative_eq_smul, coeff_trunc_mul p q _ _ (by lia)] at hd
  simp only [Polynomial.coeff_add, Polynomial.coeff_mul, coeff_derivative_eq_smul] at hd
  rw [coeff_seriesDerivative]
  refine hd.trans ?_
  simp only [map_add, coeff_mul, coeff_seriesDerivative]
  congr 1 <;> apply sum_congr rfl <;> intro ij hij <;>
    have hij' := mem_antidiagonal.mp hij
  · rw [coeff_trunc, coeff_trunc, ite_eq_left (by lia : ij.1 + 1 < n + 2),
      ite_eq_left (by lia : ij.2 < n + 2)]
  · rw [coeff_trunc, coeff_trunc, ite_eq_left (by lia : ij.1 < n + 2),
      ite_eq_left (by lia : ij.2 + 1 < n + 2)]

end FQFP
