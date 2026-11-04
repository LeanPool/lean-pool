/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Noether.BivariateCoefficientMatrix
import LeanPool.CCDN.Noether.ClosedFormHeight
import Mathlib.Algebra.MvPolynomial.CommRing

/-! Parameter degrees of the closed-form matrix and its minors. Differentiation
in the two plane coordinates does not increase the parameter degree. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial

/-- Every coefficient of the bivariate polynomial `f`, whose coefficients are polynomials in the
parameters `τ`, has total degree at most `D` in the parameters; the two polynomial variables are
the coordinates on the plane. -/
def BivariateParameterDegreeBound {K τ : Type*} [CommRing K]
    (f : (MvPolynomial τ K)[X][X]) (D : ℕ) : Prop :=
  ∀ i j, ((f.coeff i).coeff j).totalDegree ≤ D

private lemma bivariateParameterDegreeBound_sub {K τ : Type*} [CommRing K]
    {f g : (MvPolynomial τ K)[X][X]} {D : ℕ}
    (hf : BivariateParameterDegreeBound f D) (hg : BivariateParameterDegreeBound g D) :
    BivariateParameterDegreeBound (f - g) D := by
  intro i j
  simp only [coeff_sub]
  exact (MvPolynomial.totalDegree_sub _ _).trans (max_le (hf i j) (hg i j))

private lemma bivariateParameterDegreeBound_monomial_mul {K τ : Type*} [CommRing K]
    {f : (MvPolynomial τ K)[X][X]} {D : ℕ}
    (hf : BivariateParameterDegreeBound f D) (a : K) (m n : ℕ) :
    BivariateParameterDegreeBound
      (monomial m (monomial n (MvPolynomial.C a)) * f) D := by
  intro i j
  rw [coeff_monomial_mul_at]
  split_ifs
  · rw [coeff_monomial_mul_at]
    split_ifs
    · exact (MvPolynomial.totalDegree_mul _ _).trans (by simpa using hf (i-m) (j-n))
    · simp
  · simp

private lemma bivariateParameterDegreeBound_innerDerivative {K τ : Type*} [CommRing K]
    {f : (MvPolynomial τ K)[X][X]} {D : ℕ}
    (hf : BivariateParameterDegreeBound f D) :
    BivariateParameterDegreeBound ((bivariateCoefficientDerivative _) f) D := by
  intro i j
  rw [coeff_bivariateCoefficientDerivative, coeff_derivative]
  have he : (j : MvPolynomial τ K) + 1 = MvPolynomial.C ((j : K) + 1) := by simp
  rw [he]
  exact (MvPolynomial.totalDegree_mul _ _).trans
    (by simpa only [MvPolynomial.totalDegree_C, Nat.add_zero] using hf i (j+1))

private lemma bivariateParameterDegreeBound_outerDerivative {K τ : Type*} [CommRing K]
    {f : (MvPolynomial τ K)[X][X]} {D : ℕ}
    (hf : BivariateParameterDegreeBound f D) :
    BivariateParameterDegreeBound f.derivative D := by
  intro i j
  rw [coeff_derivative]
  rw [show (i : (MvPolynomial τ K)[X]) + 1 =
    C (MvPolynomial.C ((i : K) + 1)) by simp, coeff_mul_C]
  exact (MvPolynomial.totalDegree_mul _ _).trans
    (by simpa only [MvPolynomial.totalDegree_C, Nat.add_zero] using hf (i+1) j)

/-- Every matrix entry depends linearly on the input polynomial coefficients. -/
private theorem closedFormCoefficientMatrix_parameterDegree {K τ : Type*} [CommRing K]
    (d : ℕ) (f : (MvPolynomial τ K)[X][X]) (D : ℕ)
    (hf : BivariateParameterDegreeBound f D) :
    ∀ i j, (closedFormCoefficientMatrix d f i j).totalDegree ≤ D := by
  intro i j
  change (((closedFormOperator f (closedFormPair _ d (Pi.single j 1))).coeff i.1).coeff
    i.2).totalDegree ≤ _
  have hdi := bivariateParameterDegreeBound_innerDerivative hf
  have hdo := bivariateParameterDegreeBound_outerDerivative hf
  cases j with
  | inl j =>
    rw [closedFormPair_single_inl]
    change (((((bivariateCoefficientDerivative _) (monomial j.1.val (monomial j.2.val 1))) * f -
      monomial j.1.val (monomial j.2.val 1) * (bivariateCoefficientDerivative _) f -
      (0 : (MvPolynomial τ K)[X][X]).derivative * f + 0 * f.derivative).coeff i.1).coeff
        i.2).totalDegree ≤ _
    simp only [map_zero, zero_mul, sub_zero, add_zero, bivariateCoefficientDerivative_monomial,
      one_mul]
    have ha := bivariateParameterDegreeBound_monomial_mul hf (j.2.val : K) j.1.val (j.2.val-1)
    have hb := bivariateParameterDegreeBound_monomial_mul hdi (1 : K) j.1.val j.2.val
    simpa only [map_natCast, map_one] using (bivariateParameterDegreeBound_sub ha hb) i.1 i.2
  | inr j =>
    rw [closedFormPair_single_inr]
    change ((((bivariateCoefficientDerivative _) 0 * f - 0 * (bivariateCoefficientDerivative _) f -
      (monomial j.1.val (monomial j.2.val 1)).derivative * f +
      monomial j.1.val (monomial j.2.val 1) * f.derivative).coeff i.1).coeff i.2).totalDegree ≤ _
    simp only [map_zero, zero_mul, sub_self, zero_sub, bivariate_derivative_monomial, one_mul]
    rw [neg_add_eq_sub]
    have ha := bivariateParameterDegreeBound_monomial_mul hdo (1 : K) j.1.val j.2.val
    have hb := bivariateParameterDegreeBound_monomial_mul hf (j.1.val : K) (j.1.val-1) j.2.val
    simpa only [map_natCast, map_one] using (bivariateParameterDegreeBound_sub ha hb) i.1 i.2

/-- If every entry of a square matrix of multivariate polynomials has total degree at most `D`, then
its determinant has total degree at most the size of the matrix times `D`. -/
lemma matrix_det_parameterDegree {K τ ι : Type*} [CommRing K] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (MvPolynomial τ K)) (D : ℕ)
    (hM : ∀ i j, (M i j).totalDegree ≤ D) :
    M.det.totalDegree ≤ Fintype.card ι * D := by
  classical
  rw [Matrix.det_apply]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro s _
  apply (MvPolynomial.totalDegree_smul_le _ _).trans
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc ∑ i, (M (s i) i).totalDegree ≤ ∑ _ : ι, D :=
      Finset.sum_le_sum (fun i _ => hM (s i) i)
    _ = _ := by simp

/-- The parameter degree of any r-row minor is at most r times the coefficient
parameter degree; no dependence on the chosen row exponents is introduced. -/
theorem closedForm_minor_parameterDegree {K τ : Type*} [CommRing K]
    (d r : ℕ) (f : (MvPolynomial τ K)[X][X]) (D : ℕ)
    (hf : BivariateParameterDegreeBound f D)
    (a : Fin r → ℕ × ℕ) (c : Fin r → ClosedFormColumns d) :
    (((closedFormCoefficientMatrix d f).submatrix a c).det).totalDegree ≤ r * D := by
  simpa only [Fintype.card_fin] using
    matrix_det_parameterDegree ((closedFormCoefficientMatrix d f).submatrix a c) D
      (fun i j => closedFormCoefficientMatrix_parameterDegree d f D hf (a i) (c j))

end
end CCDN
