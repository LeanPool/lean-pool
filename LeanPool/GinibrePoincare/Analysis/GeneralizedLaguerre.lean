/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GeneralizedLaguerre.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Sequence
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic

/-! # Generalized Laguerre polynomials with integer Gamma shape

`polynomial k m` is the classical `L_m^(k-1)`, with its usual normalization
at zero. The coefficient formula, differential equation and polynomial basis
are algebraic; analytic Gamma orthogonality is proved separately.
-/

@[expose] public section

open Polynomial
open scoped BigOperators

namespace GinibrePoincare.Laguerre
noncomputable section

/-- Classical coefficients of `L_m^(k-1)`. -/
def coefficient (k m j : ℕ) : ℝ :=
  (-1 : ℝ) ^ j * (Nat.choose (m + k - 1) (m - j) : ℝ) / (j.factorial : ℝ)

/-- Classical generalized Laguerre polynomial for Gamma shape `k`. -/
def polynomial (k m : ℕ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range (m + 1), C (coefficient k m j) * X ^ j

theorem coeff_polynomial (k m j : ℕ) :
    (polynomial k m).coeff j = if j ≤ m then coefficient k m j else 0 := by
  simp [polynomial, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]

@[simp] theorem polynomial_zero (k : ℕ) : polynomial k 0 = 1 := by
  simp [polynomial, coefficient]

/-- The conventional normalization at zero. -/
theorem eval_zero (k m : ℕ) :
    (polynomial k m).eval 0 = (Nat.choose (m + k - 1) m : ℝ) := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, coeff_polynomial]
  simp [coefficient]

/-- The first Laguerre polynomial is `k-X`. -/
theorem polynomial_one (k : ℕ) : polynomial k 1 = C (k : ℝ) - X := by
  simp [polynomial, coefficient, Finset.sum_range_succ, sub_eq_add_neg]

/-- Exact top coefficient, including its sign and factorial. -/
theorem coeff_top (k m : ℕ) :
    (polynomial k m).coeff m = (-1 : ℝ) ^ m / (m.factorial : ℝ) := by
  simp [coeff_polynomial, coefficient]

theorem coeff_top_ne_zero (k m : ℕ) : (polynomial k m).coeff m ≠ 0 := by
  rw [coeff_top]
  positivity

theorem degree_polynomial (k m : ℕ) : (polynomial k m).degree = m := by
  apply Polynomial.degree_eq_of_le_of_coeff_ne_zero _ (coeff_top_ne_zero k m)
  apply (Polynomial.degree_le_iff_coeff_zero _ _).mpr
  intro j hj
  have hjm : ¬j ≤ m := by exact_mod_cast (not_le.mpr hj)
  simp [coeff_polynomial, hjm]

/-- Every degree occurs once, so the Laguerre family is a polynomial sequence. -/
def sequence (k : ℕ) : Polynomial.Sequence ℝ where
  elems' := polynomial k
  degree_eq' := degree_polynomial k

/-- The classical Laguerre polynomials are an algebraic basis of `ℝ[X]`. -/
def basis (k : ℕ) : Module.Basis ℕ ℝ (Polynomial ℝ) :=
  (sequence k).basis (fun m => isUnit_iff_ne_zero.mpr
    (Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.Sequence.ne_zero (sequence k) m)))

@[simp] theorem basis_apply (k m : ℕ) : basis k m = polynomial k m := by
  exact Polynomial.Sequence.basis_eq_self _ _ _

/-- The coefficient recurrence underlying the Laguerre equation. -/
theorem coefficient_recurrence (k m j : ℕ) (hk : 0 < k) (hj : j < m) :
    ((j : ℝ) + 1) * ((k : ℝ) + j) * coefficient k m (j + 1) +
      ((m : ℝ) - j) * coefficient k m j = 0 := by
  have hsub : m - j = (m - (j + 1)) + 1 := by omega
  have hN : m + k - 1 - (m - (j + 1)) = k + j := by omega
  have hc := Nat.choose_succ_right_eq (m + k - 1) (m - (j + 1))
  rw [hN, ← hsub] at hc
  have hcR : (Nat.choose (m + k - 1) (m - j) : ℝ) * ((m : ℝ) - j) =
      (Nat.choose (m + k - 1) (m - (j + 1)) : ℝ) * ((k : ℝ) + j) := by
    have hcast : ((m - j : ℕ) : ℝ) = (m : ℝ) - j := by
      simp [Nat.cast_sub hj.le]
    have hc' : (Nat.choose (m + k - 1) (m - j) : ℝ) * ((m - j : ℕ) : ℝ) =
        (Nat.choose (m + k - 1) (m - (j + 1)) : ℝ) * ((k + j : ℕ) : ℝ) := by
      exact_mod_cast hc
    simpa [hcast, Nat.cast_add] using hc'
  unfold coefficient
  rw [pow_succ, Nat.factorial_succ]
  push_cast
  have hjF : (j.factorial : ℝ) ≠ 0 := by positivity
  have hj1 : (j : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  nlinarith [congrArg (fun x : ℝ => (-1 : ℝ) ^ j * x) hcR]

/-- The generalized Laguerre differential operator. -/
def operator (k : ℕ) (P : Polynomial ℝ) : Polynomial ℝ :=
  X * P.derivative.derivative + (C (k : ℝ) - X) * P.derivative

theorem coeff_operator (k : ℕ) (P : Polynomial ℝ) (j : ℕ) :
    (operator k P).coeff j =
      ((j : ℝ) + 1) * ((k : ℝ) + j) * P.coeff (j + 1) - (j : ℝ) * P.coeff j := by
  cases j with
  | zero => simp [operator, sub_mul, Polynomial.coeff_derivative]
  | succ j =>
      simp [operator, sub_mul, Polynomial.coeff_derivative, Polynomial.coeff_X_mul]
      ring

/-- Classical Laguerre equation, with the paper's shape convention. -/
theorem operator_polynomial (k m : ℕ) (hk : 0 < k) :
    operator k (polynomial k m) = -C (m : ℝ) * polynomial k m := by
  ext j
  rw [coeff_operator]
  simp only [neg_mul, Polynomial.coeff_neg, Polynomial.coeff_C_mul]
  by_cases hj : j < m
  · rw [coeff_polynomial, coeff_polynomial]
    simp only [ite_eq_left (Nat.succ_le_of_lt hj), ite_eq_left hj.le]
    linarith [coefficient_recurrence k m j hk hj]
  · by_cases hjm : j = m
    · subst j
      simp [coeff_polynomial]
    · have hgt : m < j := by omega
      simp [coeff_polynomial, not_le.mpr hgt, not_le.mpr (hgt.trans (Nat.lt_succ_self j))]

/-- Evaluated differential equation for the classical generalized Laguerre polynomial. -/
theorem differential_equation (k m : ℕ) (hk : 0 < k) (x : ℝ) :
    x * (polynomial k m).derivative.derivative.eval x +
      ((k : ℝ) - x) * (polynomial k m).derivative.eval x =
        -(m : ℝ) * (polynomial k m).eval x := by
  have h := congrArg (fun P : Polynomial ℝ => P.eval x) (operator_polynomial k m hk)
  simpa [operator] using h

/-- The first derivative is the evaluated formal derivative. -/
theorem hasDerivAt_polynomial (k m : ℕ) (x : ℝ) :
    HasDerivAt (fun y => (polynomial k m).eval y)
      ((polynomial k m).derivative.eval x) x :=
  (polynomial k m).hasDerivAt x

/-- The second derivative also agrees with the formal polynomial derivative. -/
theorem hasDerivAt_derivative (k m : ℕ) (x : ℝ) :
    HasDerivAt (fun y => (polynomial k m).derivative.eval y)
      ((polynomial k m).derivative.derivative.eval x) x :=
  (polynomial k m).derivative.hasDerivAt x

end
end GinibrePoincare.Laguerre
