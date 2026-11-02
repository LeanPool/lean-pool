/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Noether.ShearNormalization

/-! Explicit coefficient-height bounds for the bounded integral shear. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial

private lemma bivariateShear_outerX {R : Type*} [CommRing R] (a : R) :
    bivariateShear R a (X : R[X][X]) = X := by
  rw [← bivariatePolynomialEquiv_X_zero, bivariateShear_equiv]
  change bivariatePolynomialEquiv R (MvPolynomial.aeval _ (MvPolynomial.X 0)) = _
  simp only [MvPolynomial.aeval_X, Matrix.cons_val_zero, bivariatePolynomialEquiv_X_zero]

private lemma bivariateShear_innerX {R : Type*} [CommRing R] (a : R) :
    bivariateShear R a (C X : R[X][X]) = C X + C (C a) * X := by
  rw [← bivariatePolynomialEquiv_X_one, bivariateShear_equiv]
  change bivariatePolynomialEquiv R (MvPolynomial.aeval _ (MvPolynomial.X 1)) = _
  simp only [MvPolynomial.aeval_X, Matrix.cons_val_one, Matrix.cons_val_fin_one, map_add, map_mul,
    bivariatePolynomialEquiv_X_one, bivariatePolynomialEquiv_X_zero, bivariatePolynomialEquiv_C]

private lemma bivariateShear_constant {R : Type*} [CommRing R] (a c : R) :
    bivariateShear R a (C (C c)) = C (C c) :=
  (bivariateShear R a).commutes c

private lemma bivariateShear_monomial {R : Type*} [CommRing R]
    (a c : R) (i j : ℕ) :
    bivariateShear R a (monomial i (monomial j c)) =
      monomial i (monomial 0 c) * (C X + C (C a) * X) ^ j := by
  have he : monomial i (monomial j c) = C (C c) * (X : R[X][X]) ^ i * (C X) ^ j := by
    rw [← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial]
    simp only [map_mul, map_pow]
    ring
  rw [he, map_mul, map_mul, map_pow, map_pow, bivariateShear_outerX,
    bivariateShear_innerX, bivariateShear_constant]
  simp only [← C_mul_X_pow_eq_monomial, pow_zero, mul_one]

private lemma bivariateCoefficientBound_add {f g : ℤ[X][X]} {H K : ℝ}
    (hf : BivariateCoefficientBound f H) (hg : BivariateCoefficientBound g K) :
    BivariateCoefficientBound (f + g) (H + K) := by
  intro i j
  simp only [coeff_add, Int.cast_add]
  exact (abs_add_le _ _).trans (add_le_add (hf i j) (hg i j))

private lemma bivariateCoefficientBound_shear_linear_mul (a : ℤ)
    {f : ℤ[X][X]} {H : ℝ} (hH : 0 ≤ H) (hf : BivariateCoefficientBound f H) :
    BivariateCoefficientBound ((C X + C (C a) * X) * f) ((1 + |(a : ℝ)|) * H) := by
  have h₁ := bivariateCoefficientBound_monomial_mul hH hf 1 0 1
  have h₂ := bivariateCoefficientBound_monomial_mul hH hf a 1 0
  have hh := bivariateCoefficientBound_add h₁ h₂
  have he : monomial 0 (monomial 1 (1 : ℤ)) * f + monomial 1 (monomial 0 a) * f =
      (C X + C (C a) * X) * f := by
    simp only [← C_mul_X_pow_eq_monomial, pow_zero, pow_one, map_one, one_mul, mul_one]
    ring
  rw [he] at hh
  convert hh using 1
  simp only [Int.cast_one, abs_one, one_mul]
  ring

private lemma bivariateCoefficientBound_shear_linear_pow (a : ℤ) (n : ℕ) :
    BivariateCoefficientBound ((C X + C (C a) * X : ℤ[X][X]) ^ n)
      ((1 + |(a : ℝ)|) ^ n) := by
  induction n with
  | zero =>
    simp only [pow_zero]
    intro i j
    by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [coeff_one, hi, hj]
  | succ n ih =>
    rw [pow_succ', pow_succ']
    exact bivariateCoefficientBound_shear_linear_mul a (by positivity) ih

/-- A sheared monomial has coefficient height at most |c|*(1+|a|)^j. -/
private lemma bivariateCoefficientBound_shear_monomial (a c : ℤ) (i j : ℕ) :
    BivariateCoefficientBound (bivariateShear ℤ a (monomial i (monomial j c)))
      (|(c : ℝ)| * (1 + |(a : ℝ)|) ^ j) := by
  rw [bivariateShear_monomial]
  exact bivariateCoefficientBound_monomial_mul (by positivity)
    (bivariateCoefficientBound_shear_linear_pow a j) c i 0

private lemma bivariateCoefficientBound_sum {ι : Type*} [Fintype ι]
    (f : ι → ℤ[X][X]) (H : ℝ) (hf : ∀ i, BivariateCoefficientBound (f i) H) :
    BivariateCoefficientBound (∑ i, f i) ((Fintype.card ι : ℝ) * H) := by
  intro i j
  simp only [finsetSum_coeff, Int.cast_sum]
  calc
    _ ≤ ∑ k : ι, |(((f k).coeff i).coeff j : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : ι, H := Finset.sum_le_sum (fun k _ => hf k i j)
    _ = _ := by simp

/-- A shear costs at most (d+1)²*(1+|a|)^d in coefficient height. The proof
uses the coefficient grid and the two-term multiplication recurrence. -/
private theorem bivariateShear_coefficient_bound (a : ℤ) (d : ℕ) (f : ℤ[X][X])
    (hd : bivariateTotalDegree f ≤ d) (H : ℝ) (hH : 0 ≤ H)
    (hf : BivariateCoefficientBound f H) :
    BivariateCoefficientBound (bivariateShear ℤ a f)
      (((d : ℝ) + 1) ^ 2 * H * (1 + |(a : ℝ)|) ^ d) := by
  classical
  have hg : InBivariateGrid (d + 1) f := inBivariateGrid_of_totalDegree_lt _ _ (by omega)
  have he := bivariateGridPolynomial_reconstruct (d + 1) f hg
  change (∑ k : BivariateGrid (d + 1),
    monomial k.1.val (monomial k.2.val ((f.coeff k.1.val).coeff k.2.val))) = f at he
  rw [← he, map_sum]
  have hb : ∀ k : BivariateGrid (d + 1),
      BivariateCoefficientBound
        (bivariateShear ℤ a (monomial k.1.val (monomial k.2.val ((f.coeff k.1.val).coeff k.2.val))))
        (H * (1 + |(a : ℝ)|) ^ d) := by
    intro k
    apply bivariateCoefficientBound_mono
      (bivariateCoefficientBound_shear_monomial a _ k.1.val k.2.val)
    exact mul_le_mul (hf _ _) (pow_le_pow_right₀ (by linarith [abs_nonneg (a : ℝ)]) (by omega))
      (by positivity) hH
  have hh := bivariateCoefficientBound_sum _ _ hb
  convert hh using 1
  simp only [BivariateGrid, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one]
  ring

/-- For the selected parameter 0<=a<=d, the sheared height is at most
H*(d+1)^(d+2), hence its logarithm costs only O(d log d). -/
theorem bivariateShear_bounded_coefficient_bound (a d : ℕ) (ha : a ≤ d)
    (f : ℤ[X][X]) (hd : bivariateTotalDegree f ≤ d)
    (H : ℝ) (hH : 0 ≤ H) (hf : BivariateCoefficientBound f H) :
    BivariateCoefficientBound (bivariateShear ℤ (a : ℤ) f) (((d : ℝ) + 1) ^ (d + 2) * H) := by
  apply bivariateCoefficientBound_mono (bivariateShear_coefficient_bound (a : ℤ) d f hd H hH hf)
  simp only [Int.cast_natCast, abs_of_nonneg (show (0 : ℝ) ≤ a from Nat.cast_nonneg _)]
  have haR : (a : ℝ) ≤ d := by exact_mod_cast ha
  calc
    _ ≤ ((d : ℝ) + 1) ^ 2 * H * ((d : ℝ) + 1) ^ d :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 + a by positivity)
        (show (1 : ℝ) + a ≤ d + 1 by linarith) d) (by positivity)
    _ = _ := by rw [pow_add]; ring

end
end CCDN
