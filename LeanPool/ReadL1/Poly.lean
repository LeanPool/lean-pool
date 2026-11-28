/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/

-- Modified for Lean Pool.

module

public import LeanPool.ReadL1.Basis
public import LeanPool.ReadL1.PolyNorm
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Polynomials in Śliwa's coordinates

A polynomial's coordinates in the basis `(fᵢ)`: `∑ cᵢ xⁱ ↦ ∑ cᵢ xPow i` (`ReadL1.toCoord`), so that
Śliwa's `‖f‖` is `nrm (toCoord f)`; the operator multiplies by `x` (`ReadL1.T₀_toCoord`), and
`q(T)` multiplies by `q` (`ReadL1.aeval_T₀_toCoord`).
-/

@[expose] public section

namespace ReadL1

open Polynomial Finsupp

variable {d : ℕ → ℕ}

/- ### Coordinates of a polynomial -/

/-- The coordinates of a polynomial in Śliwa's basis: `xⁱ ↦ xPow i`. -/
noncomputable def toCoord (d : ℕ → ℕ) : ℂ[X] →ₗ[ℂ] (ℕ →₀ ℂ) :=
  Polynomial.lsum fun n ↦ LinearMap.toSpanSingleton ℂ (ℕ →₀ ℂ) (xPow d n)

lemma toCoord_apply (p : ℂ[X]) : toCoord d p = p.sum fun i c ↦ c • xPow d i := by
  simp [toCoord, Polynomial.lsum_apply]

lemma toCoord_monomial (n : ℕ) (c : ℂ) : toCoord d (monomial n c) = c • xPow d n := by
  rw [toCoord_apply, Polynomial.sum_monomial_index]
  simp

lemma toCoord_X_pow (n : ℕ) : toCoord d (X ^ n) = xPow d n := by
  rw [← monomial_one_right_eq_X_pow, toCoord_monomial, one_smul]

/-- **The operator multiplies by `x`**, on polynomials. -/
lemma T₀_toCoord (h : PartitionHyp d) (p : ℂ[X]) : T₀ d (toCoord d p) = toCoord d (X * p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq, mul_add, map_add]
  | monomial n c => rw [toCoord_monomial, map_smul, T₀_xPow h, X_mul_monomial, toCoord_monomial]

lemma T₀_pow_toCoord (h : PartitionHyp d) (k : ℕ) (p : ℂ[X]) :
    (T₀ d ^ k) (toCoord d p) = toCoord d (X ^ k * p) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_apply_eq_comp, ih, T₀_toCoord h, ← mul_assoc, pow_succ']

/-- **`q(T)` multiplies by `q`**: `q(T) (toCoord y) = toCoord (q y)`. -/
lemma aeval_T₀_toCoord (h : PartitionHyp d) (q y : ℂ[X]) :
    (aeval (T₀ d) q) (toCoord d y) = toCoord d (q * y) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, LinearMap.add_apply, hp, hq, add_mul, map_add]
  | monomial n c =>
    rw [aeval_monomial, mul_apply_eq_comp, T₀_pow_toCoord h, Module.algebraMap_end_apply,
      ← C_mul_X_pow_eq_monomial, mul_assoc, ← smul_eq_C_mul]
    simp [map_smul]

end ReadL1
