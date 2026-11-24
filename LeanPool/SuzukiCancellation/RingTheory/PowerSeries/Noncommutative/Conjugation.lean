/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.RingTheory.PowerSeries.Noncommutative.AdjointSeries

import Mathlib.Tactic.NoncommRing

/-!
# Formal functional calculus and conjugation

Finite scalar polynomial truncations transport formal logarithms through
conjugation. Linear exponents give a finite sum of ordinary adjoint powers
in each homogeneous degree, without associative word expansion.
-/

@[expose] public noncomputable section

namespace FQFP

open Finset PowerSeries

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- Rescaling the scalar argument scales the positive input of functional calculus. -/
theorem scalarSeriesApply_rescale (c : PowerSeries ℚ) (r : ℚ) (p : PowerSeries A)
    (hp : constantCoeff p = 0) :
    scalarSeriesApply (rescale r c) (fun n ↦ coeff n p) =
      scalarSeriesApply c (fun n ↦ coeff n (r • p)) := by
  have hs : positiveSeries (fun n ↦ r • coeff n p) = r • p := by
    ext n
    cases n <;> simp [positiveSeries, hp, coeff_zero_eq_constantCoeff_apply]
  ext n
  simp only [scalarSeriesApply, coeff_mk, ← coeff_positiveSeries_pow,
    positiveSeries_coeff p hp, coeff_smul, hs, smul_pow, smul_smul, coeff_rescale]
  apply sum_congr rfl
  intro j hj
  rw [mul_comm]

/-- Scalar multiples of one positive exponent satisfy the exponential addition law. -/
theorem formalExp_add_smul (p : PowerSeries A) (hp : constantCoeff p = 0) (r s : ℚ) :
    formalExp (r • p) * formalExp (s • p) = formalExp ((r + s) • p) := by
  have h := congrArg (scalarSeriesApplyHom (fun n ↦ coeff n p))
    (exp_mul_exp_eq_exp_add r s)
  simpa only [map_mul, scalarSeriesApplyHom_apply, scalarSeriesApply_rescale _ _ p hp,
    formalExp] using h

private theorem aeval_conjugate (u v p : PowerSeries A)
    (huv : u * v = 1) (hvu : v * u = 1) (q : Polynomial ℚ) :
    Polynomial.aeval (u * p * v) q = u * Polynomial.aeval p q * v := by
  have hpow (j : ℕ) : (u * p * v) ^ j = u * p ^ j * v := by
    induction j with
    | zero => simp [huv]
    | succ j ih =>
      rw [pow_succ', ih, pow_succ']
      calc
        _ = u * (p * (v * u) * p ^ j) * v := by noncomm_ring
        _ = _ := by rw [hvu, mul_one]
  induction q using Polynomial.induction_on' with
  | add q t hq ht => simp only [map_add, hq, ht, mul_add, add_mul]
  | monomial j r =>
    simp only [Polynomial.aeval_monomial, hpow, ← Algebra.smul_def,
      mul_smul_comm, smul_mul_assoc]

/-- Scalar functional calculus commutes with conjugation by mutually inverse series. -/
theorem scalarSeriesApply_conjugate (c : PowerSeries ℚ) (u v p : PowerSeries A)
    (huv : u * v = 1) (hvu : v * u = 1) (hp : constantCoeff p = 0) :
    scalarSeriesApply c (fun n ↦ coeff n (u * p * v)) =
      u * scalarSeriesApply c (fun n ↦ coeff n p) * v := by
  have hconj : constantCoeff (u * p * v) = 0 := by simp [hp]
  ext n
  rw [coeff_scalarSeriesApply_eq_aeval_trunc c _ n (n + 1) (by lia),
    positiveSeries_coeff _ hconj, aeval_conjugate u v p huv hvu]
  simp only [coeff_mul]
  apply sum_congr rfl
  intro ij hij
  have hij' := mem_antidiagonal.mp hij
  congr 1
  apply sum_congr rfl
  intro kl hkl
  have hkl' := mem_antidiagonal.mp hkl
  rw [coeff_scalarSeriesApply_eq_aeval_trunc c _ kl.2 (n + 1) (by lia),
    positiveSeries_coeff p hp]

/-- The formal logarithm is equivariant under conjugation. -/
theorem formalLog_conjugate (u v p : PowerSeries A)
    (huv : u * v = 1) (hvu : v * u = 1) (hp : constantCoeff p = 1) :
    formalLog (u * p * v) = u * formalLog p * v := by
  have hsub : u * p * v - 1 = u * (p - 1) * v := by
    rw [mul_sub, sub_mul, mul_one, huv]
  simp only [formalLog, hsub]
  exact scalarSeriesApply_conjugate _ u v (p - 1) huv hvu (by simp [hp])

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The graded adjoint of a degree-one monomial is the corresponding operator monomial. -/
theorem adjointSeries_monomial_one (a : A) :
    adjointSeries (monomial 1 a) = monomial 1 (LieAlgebra.ad ℚ A a) := by
  ext n
  simp only [coeff_adjointSeries, coeff_monomial]
  split_ifs <;> simp

/-- A linear exponential conjugates each coefficient by finite ordinary adjoint powers. -/
theorem coeff_exponentialCurve_conjugate (a : A) (p : PowerSeries A) (n : ℕ) :
    coeff n (exponentialCurve a * p * exponentialCurve (-a)) =
      ∑ j ∈ range (n + 1), (Nat.factorial j : ℚ)⁻¹ •
        (LieAlgebra.ad ℚ A a ^ j) (coeff (n - j) p) := by
  have hz : constantCoeff (monomial 1 a) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    simp [coeff_monomial]
  rw [← formalExp_monomial_one a, ← formalExp_monomial_one (-a), map_neg]
  rw [← adjointSeriesApply_exp _ p hz, adjointSeriesApply,
    adjointSeries_monomial_one]
  change coeff n (seriesLinearAction (formalExp (monomial 1 (LieAlgebra.ad ℚ A a))) p) = _
  rw [formalExp_monomial_one, coeff_seriesLinearAction,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_exponentialCurve, LinearMap.smul_apply]

end FQFP
