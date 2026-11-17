/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Noether.BivariateClosedForms

/-! Integer coefficient matrices for the closed-form irreducibility criterion.
Columns encode pairs of polynomials in a finite rectangular monomial grid.
Rows are coefficient positions; finite independent rows will be selected when
extracting a determinant witness. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial Matrix

/-- Index set of the bivariate monomials whose outer and inner exponents are both less than `d`. -/
abbrev BivariateGrid (d : ℕ) := Fin d × Fin d
/-- Index set of the unknown coefficients of a pair of polynomials supported in the grid
`BivariateGrid d`; these index the columns of the closed-form coefficient matrix. -/
abbrev ClosedFormColumns (d : ℕ) := BivariateGrid d ⊕ BivariateGrid d

/-- Reconstruct a polynomial with outer and inner exponents less than d. -/
def bivariateGridPolynomial (R : Type*) [CommRing R] (d : ℕ) :
    (BivariateGrid d → R) →ₗ[R] R[X][X] where
  toFun v := ∑ i, monomial i.1.val (monomial i.2.val (v i))
  map_add' v w := by simp [Finset.sum_add_distrib]
  map_smul' a v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [smul_monomial, smul_eq_mul]

/-- The coefficient with outer exponent `i` and inner exponent `j` of the polynomial with grid
coefficients `v` is `v (i, j)`. -/
lemma bivariateGridPolynomial_coeff {R : Type*} [CommRing R] {d : ℕ}
    (v : BivariateGrid d → R) (i j : Fin d) :
    ((bivariateGridPolynomial R d v).coeff i.val).coeff j.val = v (i,j) := by
  classical
  simp [bivariateGridPolynomial, coeff_monomial, Fintype.sum_prod_type, Fin.val_inj]

private lemma bivariateGridPolynomial_injective {R : Type*} [CommRing R] (d : ℕ) :
    Function.Injective (bivariateGridPolynomial R d) := by
  intro v w h
  funext i
  have hh := congrArg (fun p : R[X][X] => (p.coeff i.1.val).coeff i.2.val) h
  simpa only [bivariateGridPolynomial_coeff] using hh

/-- The polynomial with coefficients `v` on the grid `BivariateGrid d` has outer degree less than
`d`. -/
lemma bivariateGridPolynomial_degree_lt {R : Type*} [CommRing R] {d : ℕ}
    (v : BivariateGrid d → R) : (bivariateGridPolynomial R d v).degree < d := by
  classical
  rw [degree_lt_iff_coeff_zero]
  intro n hn
  simp only [bivariateGridPolynomial, LinearMap.coe_mk, AddHom.coe_mk, finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro i _
  rw [coeff_monomial, ite_eq_right]
  omega

/-- Decode the two blocks of the unknown coefficient vector. -/
def closedFormPair (R : Type*) [CommRing R] (d : ℕ) :
    (ClosedFormColumns d → R) →ₗ[R] R[X][X] × R[X][X] where
  toFun v := (bivariateGridPolynomial R d (fun i => v (.inl i)),
    bivariateGridPolynomial R d (fun i => v (.inr i)))
  map_add' v w := by
    apply Prod.ext
    · exact (bivariateGridPolynomial R d).map_add _ _
    · exact (bivariateGridPolynomial R d).map_add _ _
  map_smul' a v := by
    apply Prod.ext
    · exact (bivariateGridPolynomial R d).map_smul a _
    · exact (bivariateGridPolynomial R d).map_smul a _

/-- Decoding a coefficient vector into a pair of grid polynomials is injective. -/
lemma closedFormPair_injective {R : Type*} [CommRing R] (d : ℕ) :
    Function.Injective (closedFormPair R d) := by
  intro v w h
  have hl := bivariateGridPolynomial_injective d (congrArg Prod.fst h)
  have hr := bivariateGridPolynomial_injective d (congrArg Prod.snd h)
  funext i
  cases i with
  | inl i => exact congrFun hl i
  | inr i => exact congrFun hr i

/-- The cleared differential equation as a linear operator on (P,Q). -/
def closedFormOperator {R : Type*} [CommRing R] (f : R[X][X]) :
    (R[X][X] × R[X][X]) →ₗ[R] R[X][X] where
  toFun u := (bivariateCoefficientDerivative R) u.1 * f -
    u.1 * (bivariateCoefficientDerivative R) f - u.2.derivative * f + u.2 * f.derivative
  map_add' u v := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, add_mul]
    ring
  map_smul' a u := by
    change (bivariateCoefficientDerivative R) (a • u.1) * f -
      (a • u.1) * (bivariateCoefficientDerivative R) f -
      (a • u.2).derivative * f + (a • u.2) * f.derivative = a • _
    rw [(bivariateCoefficientDerivative R).map_smul]
    simp only [derivative_smul, smul_mul_assoc, smul_sub, smul_add]

/-- All polynomial coefficients as a linear map. -/
def bivariateCoefficients (R : Type*) [CommRing R] : R[X][X] →ₗ[R] (ℕ × ℕ → R) where
  toFun f := fun i => (f.coeff i.1).coeff i.2
  map_add' f g := by ext; simp
  map_smul' a f := by ext; simp

/-- A bivariate polynomial is determined by its coefficients. -/
lemma bivariateCoefficients_injective {R : Type*} [CommRing R] :
    Function.Injective (bivariateCoefficients R) := by
  intro f g h
  ext i j
  exact congrFun h (i,j)

/-- The matrix of the closed-form equation on bounded unknowns.
In particular it is an integer matrix when R=Z. -/
def closedFormCoefficientMatrix {R : Type*} [CommRing R] (d : ℕ) (f : R[X][X]) :
    Matrix (ℕ × ℕ) (ClosedFormColumns d) R :=
  LinearMap.toMatrix'
    ((bivariateCoefficients R).comp ((closedFormOperator f).comp (closedFormPair R d)))

private lemma closedFormCoefficientMatrix_mulVec {R : Type*} [CommRing R] (d : ℕ) (f : R[X][X])
    (v : ClosedFormColumns d → R) :
    closedFormCoefficientMatrix d f *ᵥ v =
      bivariateCoefficients R (closedFormOperator f (closedFormPair R d v)) := by
  exact congrArg (fun u => u v) (Matrix.toLin'_toMatrix' _)

/-- Matrix kernel membership is precisely the polynomial closed-form equation. -/
theorem closedFormCoefficientMatrix_kernel {R : Type*} [CommRing R] (d : ℕ) (f : R[X][X])
    (v : ClosedFormColumns d → R) :
    closedFormCoefficientMatrix d f *ᵥ v = 0 ↔
      closedFormOperator f (closedFormPair R d v) = 0 := by
  rw [closedFormCoefficientMatrix_mulVec]
  exact (bivariateCoefficients_injective.eq_iff' (map_zero _))

end
end CCDN
