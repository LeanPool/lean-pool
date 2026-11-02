/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Noether.BivariateCoefficientMatrix
public import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

/-! Coefficient and determinant bounds for the integer closed-form matrix. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial Matrix

/-- Every coefficient of the integer bivariate polynomial `f` has absolute value at most `H`. -/
def BivariateCoefficientBound (f : ℤ[X][X]) (H : ℝ) : Prop :=
  ∀ i j, |(((f.coeff i).coeff j : ℤ) : ℝ)| ≤ H

/-- The `k`-th coefficient of `monomial n a * f` is `a * f.coeff (k - n)` if `n ≤ k` and zero
otherwise. -/
lemma coeff_monomial_mul_at {R : Type*} [CommRing R]
    (f : R[X]) (a : R) (n k : ℕ) :
    (monomial n a * f).coeff k = if n ≤ k then a * f.coeff (k - n) else 0 := by
  rw [← C_mul_X_pow_eq_monomial, mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  split_ifs <;> simp_all

/-- Multiplying an integer bivariate polynomial with coefficients bounded by `H ≥ 0` by a monomial
with coefficient `a` gives coefficients bounded by `|a| * H`. -/
lemma bivariateCoefficientBound_monomial_mul
    {f : ℤ[X][X]} {H : ℝ} (hH : 0 ≤ H) (hf : BivariateCoefficientBound f H)
    (a : ℤ) (m n : ℕ) :
    BivariateCoefficientBound (monomial m (monomial n a) * f) (|(a : ℝ)| * H) := by
  intro i j
  rw [coeff_monomial_mul_at]
  split_ifs
  · rw [coeff_monomial_mul_at]
    split_ifs
    · simp only [Int.cast_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (hf _ _) (abs_nonneg _)
    · simpa using mul_nonneg (abs_nonneg (a : ℝ)) hH
  · simpa using mul_nonneg (abs_nonneg (a : ℝ)) hH

private lemma bivariateCoefficientBound_sub {f g : ℤ[X][X]} {H K : ℝ}
    (hf : BivariateCoefficientBound f H) (hg : BivariateCoefficientBound g K) :
    BivariateCoefficientBound (f - g) (H + K) := by
  intro i j
  simp only [coeff_sub, Int.cast_sub]
  exact (abs_sub _ _).trans (add_le_add (hf i j) (hg i j))

/-- A coefficient bound `H` for `f` implies every larger coefficient bound `K`. -/
lemma bivariateCoefficientBound_mono {f : ℤ[X][X]} {H K : ℝ}
    (hf : BivariateCoefficientBound f H) (h : H ≤ K) :
    BivariateCoefficientBound f K := fun i j => (hf i j).trans h

private lemma bivariateGridPolynomial_single {R : Type*} [CommRing R] (d : ℕ)
    (i : BivariateGrid d) (a : R) :
    bivariateGridPolynomial R d (Pi.single i a) =
      monomial i.1.val (monomial i.2.val a) := by
  classical
  simp [bivariateGridPolynomial, Pi.single_apply, apply_ite]

/-- The standard basis vector of the first block decodes to the pair `(monomial, 0)` with the
corresponding grid monomial. -/
lemma closedFormPair_single_inl {R : Type*} [CommRing R] (d : ℕ)
    (i : BivariateGrid d) :
    closedFormPair R d (Pi.single (.inl i) 1) =
      (monomial i.1.val (monomial i.2.val 1), 0) := by
  classical
  apply Prod.ext
  · change bivariateGridPolynomial R d _ = _
    convert bivariateGridPolynomial_single d i (1 : R) using 1
    congr 1
    ext j
    simp [Pi.single_apply]
  · change bivariateGridPolynomial R d _ = 0
    simp only [Pi.single_apply, reduceCtorEq, ite_false]
    exact (bivariateGridPolynomial R d).map_zero

/-- The standard basis vector of the second block decodes to the pair `(0, monomial)` with the
corresponding grid monomial. -/
lemma closedFormPair_single_inr {R : Type*} [CommRing R] (d : ℕ)
    (i : BivariateGrid d) :
    closedFormPair R d (Pi.single (.inr i) 1) =
      (0, monomial i.1.val (monomial i.2.val 1)) := by
  classical
  apply Prod.ext
  · change bivariateGridPolynomial R d _ = 0
    simp only [Pi.single_apply, reduceCtorEq, ite_false]
    exact (bivariateGridPolynomial R d).map_zero
  · change bivariateGridPolynomial R d _ = _
    convert bivariateGridPolynomial_single d i (1 : R) using 1
    congr 1
    ext j
    simp [Pi.single_apply]

/-- Inner differentiation costs at most the inner degree. -/
private lemma bivariateCoefficientBound_innerDerivative
    {f : ℤ[X][X]} {H : ℝ} (d : ℕ) (hH : 0 ≤ H)
    (hf : BivariateCoefficientBound f H)
    (hd : ∀ i, (f.coeff i).natDegree ≤ d) :
    BivariateCoefficientBound ((bivariateCoefficientDerivative ℤ) f) (d * H) := by
  intro i j
  rw [coeff_bivariateCoefficientDerivative, coeff_derivative]
  by_cases hj : j + 1 ≤ d
  · simp only [Int.cast_mul, Int.cast_add, Int.cast_natCast, Int.cast_one, abs_mul,
      abs_of_nonneg (show (0 : ℝ) ≤ j + 1 by positivity)]
    rw [← Nat.cast_add_one]
    calc
      _ ≤ H * (j + 1 : ℕ) := mul_le_mul_of_nonneg_right (hf i (j + 1)) (Nat.cast_nonneg _)
      _ ≤ H * d := mul_le_mul_of_nonneg_left (by exact_mod_cast hj) hH
      _ = _ := mul_comm _ _
  · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hd i) (by omega))]
    simpa using mul_nonneg (Nat.cast_nonneg d) hH

/-- Outer differentiation costs at most the outer degree. -/
private lemma bivariateCoefficientBound_outerDerivative
    {f : ℤ[X][X]} {H : ℝ} (d : ℕ) (hH : 0 ≤ H)
    (hf : BivariateCoefficientBound f H) (hd : f.natDegree ≤ d) :
    BivariateCoefficientBound f.derivative (d * H) := by
  intro i j
  rw [coeff_derivative]
  by_cases hi : i + 1 ≤ d
  · rw [show (i : ℤ[X]) + 1 = C ((i : ℤ) + 1) by simp, coeff_mul_C]
    simp only [Int.cast_mul, Int.cast_add, Int.cast_natCast, Int.cast_one, abs_mul,
      abs_of_nonneg (show (0 : ℝ) ≤ i + 1 by positivity)]
    rw [← Nat.cast_add_one]
    calc
      _ ≤ H * (i + 1 : ℕ) := mul_le_mul_of_nonneg_right (hf (i + 1) j) (Nat.cast_nonneg _)
      _ ≤ H * d := mul_le_mul_of_nonneg_left (by exact_mod_cast hi) hH
      _ = _ := mul_comm _ _
  · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hd (by omega))]
    simpa using mul_nonneg (Nat.cast_nonneg d) hH

/-- Every matrix entry is at most 2*d*H in absolute value. -/
private theorem closedFormCoefficientMatrix_entry_bound
    (d : ℕ) (f : ℤ[X][X]) (H : ℝ) (hH : 0 ≤ H)
    (hf : BivariateCoefficientBound f H) (houter : f.natDegree ≤ d)
    (hinner : ∀ i, (f.coeff i).natDegree ≤ d) :
    ∀ i j, |((closedFormCoefficientMatrix d f i j : ℤ) : ℝ)| ≤ 2 * d * H := by
  intro i j
  change |((((closedFormOperator f (closedFormPair ℤ d (Pi.single j 1))).coeff i.1).coeff
    i.2 : ℤ) : ℝ)| ≤ _
  have hDH := mul_nonneg (Nat.cast_nonneg d) hH
  have hdi := bivariateCoefficientBound_innerDerivative d hH hf hinner
  have hdo := bivariateCoefficientBound_outerDerivative d hH hf houter
  cases j with
  | inl j =>
    rw [closedFormPair_single_inl]
    change |((((((bivariateCoefficientDerivative ℤ) (monomial j.1.val (monomial j.2.val 1))) * f -
      monomial j.1.val (monomial j.2.val 1) * (bivariateCoefficientDerivative ℤ) f -
      (0 : ℤ[X][X]).derivative * f + 0 * f.derivative).coeff i.1).coeff i.2 : ℤ) : ℝ)| ≤ _
    simp only [map_zero, zero_mul, sub_zero, add_zero, bivariateCoefficientDerivative_monomial,
      one_mul]
    have ha := bivariateCoefficientBound_monomial_mul hH hf (j.2.val : ℤ) j.1.val (j.2.val - 1)
    have hb := bivariateCoefficientBound_monomial_mul hDH hdi 1 j.1.val j.2.val
    have hh := (bivariateCoefficientBound_sub ha hb) i.1 i.2
    simp only [Int.cast_natCast, abs_of_nonneg (show (0 : ℝ) ≤ j.2.val from Nat.cast_nonneg _),
      Int.cast_one, abs_one, one_mul] at hh
    have hj : (j.2.val : ℝ) ≤ d := by exact_mod_cast j.2.isLt.le
    nlinarith
  | inr j =>
    rw [closedFormPair_single_inr]
    change |(((((bivariateCoefficientDerivative ℤ) 0 * f -
      0 * (bivariateCoefficientDerivative ℤ) f -
      (monomial j.1.val (monomial j.2.val 1)).derivative * f +
      monomial j.1.val (monomial j.2.val 1) * f.derivative).coeff i.1).coeff i.2 : ℤ) : ℝ)| ≤ _
    simp only [map_zero, zero_mul, sub_self, zero_sub, bivariate_derivative_monomial, one_mul]
    rw [neg_add_eq_sub]
    have ha := bivariateCoefficientBound_monomial_mul hDH hdo 1 j.1.val j.2.val
    have hb := bivariateCoefficientBound_monomial_mul hH hf (j.1.val : ℤ) (j.1.val - 1) j.2.val
    have hh := (bivariateCoefficientBound_sub ha hb) i.1 i.2
    simp only [Int.cast_natCast, abs_of_nonneg (show (0 : ℝ) ≤ j.1.val from Nat.cast_nonneg _),
      Int.cast_one, abs_one, one_mul] at hh
    have hj : (j.1.val : ℝ) ≤ d := by exact_mod_cast j.1.isLt.le
    nlinarith

/-- Expansion of a selected determinant gives a coefficient-controlled integer
witness bound, uniformly over all choices of rows and columns. -/
theorem closedForm_integer_minor_bound
    (d r : ℕ) (f : ℤ[X][X]) (H : ℝ) (hH : 0 ≤ H)
    (hf : BivariateCoefficientBound f H) (houter : f.natDegree ≤ d)
    (hinner : ∀ i, (f.coeff i).natDegree ≤ d)
    (a : Fin r → ℕ × ℕ) (c : Fin r → ClosedFormColumns d) :
    |((((closedFormCoefficientMatrix d f).submatrix a c).det : ℤ) : ℝ)| ≤
      (r.factorial : ℝ) * (2 * d * H) ^ r := by
  have he := closedFormCoefficientMatrix_entry_bound d f H hH hf houter hinner
  have hb := Matrix.det_le (abv := AbsoluteValue.abs)
    (A := ((closedFormCoefficientMatrix d f).submatrix a c).map (Int.castRingHom ℝ))
    (fun i j => he (a i) (c j))
  have hd : (((closedFormCoefficientMatrix d f).submatrix a c).map (Int.castRingHom ℝ)).det =
      ((((closedFormCoefficientMatrix d f).submatrix a c).det : ℤ) : ℝ) :=
    ((Int.castRingHom ℝ).map_det _).symm
  rw [hd] at hb
  simpa [nsmul_eq_mul] using hb

end
end CCDN
