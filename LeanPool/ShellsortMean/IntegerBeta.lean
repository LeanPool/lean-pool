/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
Exact polynomial mixture weights for the finite tagged-subset input law.
This module proves integration identities only. The cardinality of the
permutation fibers is a separate combinatorial assertion.
-/
@[expose] public section

namespace Shellsort
open scoped BigOperators
open MeasureTheory

theorem complex_beta_nat_factorials (a b : ℕ) :
    Complex.betaIntegral ((a : ℂ) + 1) ((b : ℂ) + 1) =
      (a.factorial : ℂ) * b.factorial / (a + b + 1).factorial := by
  rw [Complex.betaIntegral_eq_Gamma_mul_div]
  · rw [Complex.Gamma_nat_eq_factorial, Complex.Gamma_nat_eq_factorial,
      show ((a : ℂ) + 1) + ((b : ℂ) + 1) = ((a + b + 1 : ℕ) : ℂ) + 1 by push_cast; ring,
      Complex.Gamma_nat_eq_factorial]
  · simp only [Complex.add_re, Complex.natCast_re, Complex.one_re]
    positivity
  · simp only [Complex.add_re, Complex.natCast_re, Complex.one_re]
    positivity

/-- The integer beta integral, including zero exponents and both endpoints. -/
theorem integer_beta_integral (a b : ℕ) :
    (∫ t : ℝ in 0..1, t ^ a * (1 - t) ^ b) =
      (a.factorial : ℝ) * b.factorial / (a + b + 1).factorial := by
  have hc : (∫ t : ℝ in 0..1, (t : ℂ) ^ a * (1 - (t : ℂ)) ^ b) =
      (a.factorial : ℂ) * b.factorial / (a + b + 1).factorial := by
    simpa only [Complex.betaIntegral, add_sub_cancel_right, Complex.cpow_natCast] using
      complex_beta_nat_factorials a b
  apply Complex.ofReal_injective
  calc
    ((∫ t : ℝ in 0..1, t ^ a * (1 - t) ^ b : ℝ) : ℂ) =
        ∫ t : ℝ in 0..1, ((t ^ a * (1 - t) ^ b : ℝ) : ℂ) :=
      intervalIntegral.integral_ofReal.symm
    _ = (a.factorial : ℂ) * b.factorial / (a + b + 1).factorial := by
      simpa only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_sub,
        Complex.ofReal_one] using hc
    _ = (((a.factorial : ℝ) * b.factorial / (a + b + 1).factorial : ℝ) : ℂ) := by
      push_cast
      rfl

theorem integer_beta_intervalIntegrable (a b : ℕ) :
    IntervalIntegrable (fun t : ℝ => t ^ a * (1 - t) ^ b) volume 0 1 := by
  apply Continuous.intervalIntegrable
  fun_prop

/-- Finite mixture integration is exact and requires no asymptotic exchange. -/
theorem finite_integer_beta_mixture {B : Type*} [Fintype B]
    (a b : B → ℕ) (F : B → ℝ) :
    (∫ t : ℝ in 0..1, ∑ x, t ^ (a x) * (1 - t) ^ (b x) * F x) =
      ∑ x, (a x).factorial * ((b x).factorial : ℝ) /
        (a x + b x + 1).factorial * F x := by
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro x _
    rw [intervalIntegral.integral_mul_const, integer_beta_integral]
  · intro x _
    exact (integer_beta_intervalIntegrable (a x) (b x)).mul_const (F x)

end Shellsort
