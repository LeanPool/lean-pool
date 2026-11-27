/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.PolydiscCauchyCoefficients
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Actual contour coefficients of the multivariate exponential kernel

The coefficients are evaluated from the genuine Cauchy derivative
formula and the explicit iterated derivative of exp(c*z).
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open Complex MeasureTheory
open scoped BigOperators

theorem circleCoefficient_const_mul (R : ℝ) (a : ℂ) (f : ℂ → ℂ) (k : ℕ) :
    circleCoefficient R (fun z => a * f z) k = a * circleCoefficient R f k := by
  have he (z : ℂ) : z⁻¹ ^ k • z⁻¹ • (a * f z) = a * (z⁻¹ ^ k • z⁻¹ • f z) := by
    simp only [smul_eq_mul]
    ring
  unfold circleCoefficient
  simp_rw [he]
  rw [circleIntegral.integral_const_mul]
  simp only [smul_eq_mul]
  ring

theorem circleCoefficient_mul_const (R : ℝ) (f : ℂ → ℂ) (a : ℂ) (k : ℕ) :
    circleCoefficient R (fun z => f z * a) k = circleCoefficient R f k * a := by
  simp_rw [mul_comm (f _) a]
  rw [circleCoefficient_const_mul, mul_comm]

theorem polydiscCoefficient_const_mul (n : ℕ) (R : ℝ) (a : ℂ)
    (F : (Fin n → ℂ) → ℂ) (k : Fin n → ℕ) :
    polydiscCoefficient n R (fun z => a * F z) k = a * polydiscCoefficient n R F k := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [polydiscCoefficient, ih, circleCoefficient_const_mul]

theorem circleCoefficient_exp {R : ℝ} (hR : 0 < R) (c : ℂ) (k : ℕ) :
    circleCoefficient R (fun z => Complex.exp (c * z)) k = c ^ k / (k.factorial : ℂ) := by
  have hf : Differentiable ℂ (fun z : ℂ => Complex.exp (c * z)) := by fun_prop
  have h := hf.diffContOnCl.circleIntegral_one_div_sub_center_pow_smul (c := (0 : ℂ)) hR k
  have he (z : ℂ) : z⁻¹ ^ k • z⁻¹ • Complex.exp (c * z) =
      (1 / (z - 0) ^ (k + 1)) • Complex.exp (c * z) := by
    simp only [sub_zero, one_div, pow_succ, mul_inv_rev, ← inv_pow, smul_eq_mul]
    ring
  rw [circleCoefficient]
  simp_rw [he]
  rw [h, iteratedDeriv_cexp_const_mul]
  simp only [mul_zero, Complex.exp_zero, mul_one, smul_eq_mul]
  field_simp [Complex.two_pi_I_ne_zero, Nat.cast_ne_zero.mpr k.factorial_ne_zero]

theorem polydiscCoefficient_exp_sum (n : ℕ) {R : ℝ} (hR : 0 < R)
    (c : Fin n → ℂ) (k : Fin n → ℕ) :
    polydiscCoefficient n R (fun z => Complex.exp (∑ j, c j * z j)) k =
      ∏ j, c j ^ k j / ((k j).factorial : ℂ) := by
  induction n with
  | zero => simp [polydiscCoefficient]
  | succ n ih =>
    have he (z : ℂ) (w : Fin n → ℂ) :
        Complex.exp (∑ j : Fin (n + 1), c j * (Fin.cons z w : Fin (n + 1) → ℂ) j) =
          Complex.exp (c 0 * z) * Complex.exp (∑ j : Fin n, c j.succ * w j) := by
      rw [Fin.sum_univ_succ, Complex.exp_add]
      simp only [Fin.cons_zero, Fin.cons_succ]
    simp only [polydiscCoefficient, he, polydiscCoefficient_const_mul, ih]
    rw [circleCoefficient_mul_const, circleCoefficient_exp hR, Fin.prod_univ_succ]

end VacuumBellSeparation.Gaussian
