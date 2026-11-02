/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Arithmetic.Arithmetic
public import Mathlib.RingTheory.PowerSeries.Derivative

/-! # The formal Euler derivative and finite Euler products -/

@[expose] public section

namespace NairTenenbaum

open Finset

/-- The Euler derivative of a power series, multiplying each coefficient by its index. -/
noncomputable def powerSeriesEulerDerivative (F : PowerSeries ℝ) : PowerSeries ℝ :=
  PowerSeries.X * PowerSeries.derivative F

theorem powerSeriesEulerDerivative_coeff (F : PowerSeries ℝ) (k : ℕ) :
    PowerSeries.coeff k (powerSeriesEulerDerivative F) = (k : ℝ) * PowerSeries.coeff k F := by
  cases k with
  | zero => simp [powerSeriesEulerDerivative, PowerSeries.coeff_zero_eq_constantCoeff]
  | succ k =>
    unfold powerSeriesEulerDerivative
    rw [mul_comm, ← pow_one (PowerSeries.X : PowerSeries ℝ), PowerSeries.coeff_mul_X_pow,
      PowerSeries.coeff_derivative]
    push_cast
    ring

@[simp] theorem powerSeriesEulerDerivative_one : powerSeriesEulerDerivative 1 = 0 := by
  simp [powerSeriesEulerDerivative]

theorem powerSeriesEulerDerivative_mul (F G : PowerSeries ℝ) :
    powerSeriesEulerDerivative (F * G) =
      powerSeriesEulerDerivative F * G + F * powerSeriesEulerDerivative G := by
  simp only [powerSeriesEulerDerivative, Derivation.leibniz, smul_eq_mul]
  ring

theorem powerSeriesEulerDerivative_prod_mul_inverse {ι : Type*} (S : Finset ι)
    (F G : ι → PowerSeries ℝ) (hFG : ∀ i ∈ S, F i * G i = 1) :
    powerSeriesEulerDerivative (∏ i ∈ S, F i) * (∏ i ∈ S, G i) =
      ∑ i ∈ S, powerSeriesEulerDerivative (F i) * G i := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hrest : ∀ j ∈ S, F j * G j = 1 := fun j hj => hFG j (mem_insert_of_mem hj)
    have Hprod : (∏ j ∈ S, F j) * (∏ j ∈ S, G j) = 1 := by
      rw [← prod_mul_distrib]
      simp only [prod_congr rfl hrest, prod_const_one]
    rw [prod_insert hi, prod_insert hi, sum_insert hi, powerSeriesEulerDerivative_mul]
    calc
      _ = (powerSeriesEulerDerivative (F i) * G i) * ((∏ j ∈ S, F j) * (∏ j ∈ S, G j)) +
          (F i * G i) * (powerSeriesEulerDerivative (∏ j ∈ S, F j) * (∏ j ∈ S, G j)) := by ring
      _ = _ := by rw [Hprod, hFG i (mem_insert_self _ _), mul_one, one_mul, ih hrest]

end NairTenenbaum
