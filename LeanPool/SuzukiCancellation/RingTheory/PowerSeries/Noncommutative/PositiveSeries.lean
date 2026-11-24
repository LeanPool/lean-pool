/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.RingTheory.PowerSeries.Noncommutative.ExponentialListCoefficients
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Positive homogeneous coefficients as noncommutative power series

The finite convolution used by `positivePowerCoeff` agrees with powers in
`PowerSeries A`, for an arbitrary rational associative algebra `A`. This
interface keeps products as blocks and constructs no associative word table.
-/

@[expose] public noncomputable section

namespace FQFP

open Finset Finset.Nat PowerSeries

variable {A : Type*} [Semiring A]

/-- A family of positive-degree coefficients, with its degree-zero input ignored. -/
def positiveSeries (u : ℕ → A) : PowerSeries A :=
  mk fun n ↦ if n = 0 then 0 else u n

@[simp]
theorem coeff_positiveSeries_zero (u : ℕ → A) : coeff 0 (positiveSeries u) = 0 := by
  simp [positiveSeries]

@[simp]
theorem coeff_positiveSeries_succ (u : ℕ → A) (n : ℕ) :
    coeff (n + 1) (positiveSeries u) = u (n + 1) := by
  simp [positiveSeries]

/-- Every series with zero constant coefficient is recovered from its positive coefficients. -/
theorem positiveSeries_coeff (p : PowerSeries A) (hp : constantCoeff p = 0) :
    positiveSeries (fun n ↦ coeff n p) = p := by
  ext n
  cases n with
  | zero => simp [positiveSeries, hp]
  | succ n => simp

/-- Positive power convolution is actual multiplication of formal series over `A`. -/
theorem coeff_positiveSeries_pow (u : ℕ → A) (k n : ℕ) :
    coeff n (positiveSeries u ^ k) = positivePowerCoeff u k n := by
  induction k generalizing n with
  | zero => simp [positivePowerCoeff, coeff_one]
  | succ k ih =>
    rw [pow_succ', coeff_mul, sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ']
    simp only [coeff_positiveSeries_zero, zero_mul, add_zero, coeff_positiveSeries_succ, ih]
    change (∑ i ∈ range n, u (i + 1) * positivePowerCoeff u k (n - (i + 1))) =
      ∑ i ∈ range (n - k), u (i + 1) * positivePowerCoeff u k (n - (i + 1))
    symm
    apply sum_subset (range_mono (Nat.sub_le n k))
    intro i hi hin
    rw [positivePowerCoeff_eq_zero_of_lt u k _ (by
      have := mem_range.mp hi
      have := mem_range.not.mp hin
      lia), mul_zero]

/-- Positive powers have no coefficient below the number of factors. -/
theorem coeff_positiveSeries_pow_eq_zero_of_lt (u : ℕ → A) (k n : ℕ) (h : n < k) :
    coeff n (positiveSeries u ^ k) = 0 := by
  rw [coeff_positiveSeries_pow, positivePowerCoeff_eq_zero_of_lt u k n h]

variable [Algebra ℚ A]

/-- The exponential product as an actual formal series, without a commutative target. -/
def expListSeries (l : List A) : PowerSeries A := mk (expListTerm l)

@[simp]
theorem coeff_expListSeries (l : List A) (n : ℕ) :
    coeff n (expListSeries l) = expListTerm l n := by simp [expListSeries]

theorem expListSeries_nil : expListSeries ([] : List A) = 1 := by
  ext n
  simp [expListSeries, expListTerm, coeff_one]

/-- The formal exponential list is built by Cauchy products of exponential factors. -/
theorem expListSeries_cons (a : A) (l : List A) :
    expListSeries (a :: l) =
      (mk fun n ↦ (Nat.factorial n : ℚ)⁻¹ • a ^ n) * expListSeries l := by
  ext n
  simp only [expListSeries, coeff_mk, coeff_mul, expListTerm]

/-- Formal exponential products preserve concatenation order. -/
theorem expListSeries_append (l r : List A) :
    expListSeries (l ++ r) = expListSeries l * expListSeries r := by
  induction l with
  | nil => simp [expListSeries_nil]
  | cons a l ih =>
      simp only [List.cons_append, expListSeries_cons, ih, mul_assoc]

/-- The positive part of an exponential product is its formal series minus one. -/
theorem positiveSeries_expListTerm (l : List A) :
    positiveSeries (expListTerm l) + 1 = expListSeries l := by
  ext n
  cases n with
  | zero => simp [expListSeries, positiveSeries]
  | succ n => simp [expListSeries, coeff_one]

end FQFP
