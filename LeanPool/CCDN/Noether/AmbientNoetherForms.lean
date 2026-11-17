/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.CoefficientwiseHomogeneous
public import LeanPool.CCDN.Noether.EulerUniversalForms
public import LeanPool.CCDN.Noether.UniversalHomogeneousForm
import LeanPool.CCDN.Noether.EulerPairSpecialization
import LeanPool.CCDN.Noether.UniversalPlaneWitness

/-! Universal Noether coefficient forms in an arbitrary ambient variable
space. They are the plane-parameter coefficients of Euler minors. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The `(row, col)` entry of the Euler closed-form coefficient matrix of the universal plane
restriction of a polynomial in the variables `σ`, as an `R`-linear function of that polynomial. -/
def ambientEulerEntryLinear (R σ : Type*) [CommRing R] (k : ℕ)
    (row : ℕ × ℕ) (col : EulerColumns k) :
    MvPolynomial σ R →ₗ[R] MvPolynomial (PlaneParameters σ) R :=
  ((eulerCoefficientEntryLinear (R := MvPolynomial (PlaneParameters σ) R)
    k row col).restrictScalars R).comp (universalPlanePolynomialLinear R σ)

/-- `ambientEulerEntryLinear R σ k row col f` is the `(row, col)` entry of the Euler closed-form
coefficient matrix of the universal plane restriction of `f`. -/
lemma ambientEulerEntryLinear_apply {R σ : Type*} [CommRing R] (k : ℕ)
    (row : ℕ × ℕ) (col : EulerColumns k) (f : MvPolynomial σ R) :
    ambientEulerEntryLinear R σ k row col f =
      eulerClosedFormCoefficientMatrix k (universalPlanePolynomial f) row col := rfl

/-- The entries `ambientEulerEntryLinear` commute with applying a coefficient ring homomorphism
`φ` to the polynomial. -/
lemma ambientEulerEntryLinear_map {R S σ : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (k : ℕ) (row : ℕ × ℕ) (col : EulerColumns k)
    (f : MvPolynomial σ R) :
    ambientEulerEntryLinear S σ k row col (MvPolynomial.map φ f) =
      MvPolynomial.map φ (ambientEulerEntryLinear R σ k row col f) := by
  simp only [ambientEulerEntryLinear_apply, universalPlanePolynomial_map]
  exact (congrFun (congrFun
    (eulerClosedFormCoefficientMatrix_map (MvPolynomial.map φ) k (universalPlanePolynomial f))
      row) col).symm

/-- The minor with rows `rows` and columns `cols` of the Euler closed-form coefficient matrix of
the universal plane restriction of the universal homogeneous form of degree `k + 2`. It is a
polynomial in the plane parameters with coefficients that are integer polynomials in the
coefficients of the form. -/
def ambientNoetherParameterMinor (σ : Type*) [Fintype σ] [DecidableEq σ]
    (k : ℕ) (rows : Fin ((k + 2) ^ 2 - 1) → ℕ × ℕ)
    (cols : Fin ((k + 2) ^ 2 - 1) → EulerColumns k) :
    MvPolynomial (PlaneParameters σ) (MvPolynomial (Sym σ (k + 2)) ℤ) :=
  ((eulerClosedFormCoefficientMatrix k
    (universalPlanePolynomial (universalHomogeneousForm σ (k + 2)))).submatrix rows cols).det

/-- The ambient Noether form indexed by a minor `(rows, cols)` and a plane-parameter monomial `m`:
the coefficient of `m` in `ambientNoetherParameterMinor σ k rows cols`, an integer polynomial in
the coefficients of a homogeneous form of degree `k + 2`. -/
def ambientNoetherForm (σ : Type*) [Fintype σ] [DecidableEq σ]
    (k : ℕ) (rows : Fin ((k + 2) ^ 2 - 1) → ℕ × ℕ)
    (cols : Fin ((k + 2) ^ 2 - 1) → EulerColumns k)
    (m : PlaneParameters σ →₀ ℕ) : MvPolynomial (Sym σ (k + 2)) ℤ :=
  (ambientNoetherParameterMinor σ k rows cols).coeff m

private lemma ambientEulerEntryLinear_coefficientwiseHomogeneous
    (σ : Type*) [Fintype σ] [DecidableEq σ] (k : ℕ)
    (row : ℕ × ℕ) (col : EulerColumns k) :
    CoefficientwiseHomogeneous
      (ambientEulerEntryLinear _ σ k row col (universalHomogeneousForm σ (k + 2))) 1 := by
  rw [universalHomogeneousForm_linear_expansion, map_sum]
  apply CoefficientwiseHomogeneous.sum
  intro i _
  rw [map_smul, ambientEulerEntryLinear_map, smul_eq_C_mul]
  have hh := (CoefficientwiseHomogeneous.C_of_isHomogeneous (isHomogeneous_X ℤ i)).mul
    (CoefficientwiseHomogeneous.map_C
      (ambientEulerEntryLinear ℤ σ k row col
        (monomial (homogeneousCoefficientExponent σ (k + 2) i) (1 : ℤ))))
  simpa only [add_zero] using hh

/-- Every extracted parameter coefficient is homogeneous of the exact
Noether degree d²−1 in the original equation's coefficients. -/
theorem ambientNoetherForm_homogeneous (σ : Type*) [Fintype σ] [DecidableEq σ]
    (k : ℕ) (rows : Fin ((k + 2) ^ 2 - 1) → ℕ × ℕ)
    (cols : Fin ((k + 2) ^ 2 - 1) → EulerColumns k)
    (m : PlaneParameters σ →₀ ℕ) :
    (ambientNoetherForm σ k rows cols m).IsHomogeneous ((k + 2) ^ 2 - 1) := by
  exact CoefficientwiseHomogeneous.det _ (fun i j =>
    ambientEulerEntryLinear_coefficientwiseHomogeneous σ k (rows i) (cols j)) m

private lemma ambientNoetherParameterMinor_specialize {R σ : Type*} [CommRing R]
    [Fintype σ] [DecidableEq σ]
    (k : ℕ) (f : MvPolynomial σ R) (hf : f.IsHomogeneous (k + 2))
    (rows : Fin ((k + 2) ^ 2 - 1) → ℕ × ℕ)
    (cols : Fin ((k + 2) ^ 2 - 1) → EulerColumns k) :
    MvPolynomial.map (homogeneousCoefficientSpecialization (k + 2) f)
      (ambientNoetherParameterMinor σ k rows cols) =
      ((eulerClosedFormCoefficientMatrix k (universalPlanePolynomial f)).submatrix
        rows cols).det := by
  rw [ambientNoetherParameterMinor, eulerClosedForm_minor_map,
    ← universalPlanePolynomial_map, universalHomogeneousForm_specialize _ f hf]

/-- Evaluation of a Noether form is exactly the corresponding coefficient
of the restricted-equation determinant. -/
theorem ambientNoetherForm_specialize {R σ : Type*} [CommRing R]
    [Fintype σ] [DecidableEq σ]
    (k : ℕ) (f : MvPolynomial σ R) (hf : f.IsHomogeneous (k + 2))
    (rows : Fin ((k + 2) ^ 2 - 1) → ℕ × ℕ)
    (cols : Fin ((k + 2) ^ 2 - 1) → EulerColumns k)
    (m : PlaneParameters σ →₀ ℕ) :
    homogeneousCoefficientSpecialization (k + 2) f (ambientNoetherForm σ k rows cols m) =
      (((eulerClosedFormCoefficientMatrix k (universalPlanePolynomial f)).submatrix
        rows cols).det).coeff m := by
  rw [← ambientNoetherParameterMinor_specialize k f hf rows cols, coeff_map]
  rfl

end
end CCDN
