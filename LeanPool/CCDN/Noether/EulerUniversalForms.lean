/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Noether.ClosedFormScaling
public import LeanPool.CCDN.Noether.EulerPairBasis
import LeanPool.CCDN.Noether.EulerPairBasisValues
import LeanPool.CCDN.Noether.EulerPairSpecialization
import LeanPool.CCDN.Noether.ShearNormalization

/-! Universal homogeneous coefficient minors of the Euler-restricted operator.
The constructed forms have degree exactly d^2-1 in the homogeneous sense,
specialize to coefficient minors, and detect normalized irreducibility
in characteristic zero. Reducibility vanishing and height bounds are separate. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Module

private lemma eulerLowBasis_repr_apply {R : Type*} [CommRing R] (d : ℕ)
    (f : restrictTotalDegree (Fin 2) R d) (i : EulerLowIndex d) :
    (eulerLowBasis R d).repr f i =
      f.val.coeff ((Finsupp.degreeLeEquivSym (Fin 2) d).symm i).val := by
  exact Basis.repr_reindex_apply _ _ _ _

/-- The bivariate monomial with coefficient one indexed by `i`, of total degree at most `d`. -/
def eulerCoefficientMonomial (R : Type*) [CommRing R] (d : ℕ) (i : EulerLowIndex d) :
    Polynomial (Polynomial R) :=
  bivariatePolynomialEquiv R (monomial ((Finsupp.degreeLeEquivSym (Fin 2) d).symm i).val 1)

/-- The coefficient of `f` at the bivariate monomial of total degree at most `d` indexed by `i`. -/
def eulerCoefficientData {R : Type*} [CommRing R] (d : ℕ)
    (f : Polynomial (Polynomial R)) (i : EulerLowIndex d) : R :=
  ((bivariatePolynomialEquiv R).symm f).coeff ((Finsupp.degreeLeEquivSym (Fin 2) d).symm i).val

/-- A bivariate polynomial of total degree at most `d` is the sum of the monomials
`eulerCoefficientMonomial R d i` weighted by its coefficients `eulerCoefficientData d f i`. -/
theorem eulerCoefficientData_reconstruct {R : Type*} [CommRing R] (d : ℕ)
    (f : Polynomial (Polynomial R)) (hf : bivariateTotalDegree f ≤ d) :
    ∑ i, eulerCoefficientData d f i • eulerCoefficientMonomial R d i = f := by
  let u : restrictTotalDegree (Fin 2) R d :=
    ⟨(bivariatePolynomialEquiv R).symm f, (mem_restrictTotalDegree _ _ _).mpr hf⟩
  have hh := congrArg (fun v : restrictTotalDegree (Fin 2) R d =>
    bivariatePolynomialEquiv R v.val) ((eulerLowBasis R d).sum_repr u)
  simpa only [Submodule.coe_sum, SetLike.val_smul, map_sum, map_smul,
    eulerLowBasis_repr_apply, eulerLowBasis_apply, AlgEquiv.apply_symm_apply,
    eulerCoefficientData, eulerCoefficientMonomial, u] using hh

/-- Applying a coefficient ring homomorphism fixes the monomials `eulerCoefficientMonomial`. -/
lemma eulerCoefficientMonomial_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (d : ℕ) (i : EulerLowIndex d) :
    bivariateMap φ (eulerCoefficientMonomial R d i) = eulerCoefficientMonomial S d i := by
  simp only [eulerCoefficientMonomial, bivariatePolynomialEquiv_map, map_monomial, map_one]

/-- The differential operator is linear in the defining equation as well
as in its pair of unknowns. -/
def closedFormEquationLinear {R : Type*} [CommRing R]
    (u : Polynomial (Polynomial R) × Polynomial (Polynomial R)) :
    Polynomial (Polynomial R) →ₗ[R] Polynomial (Polynomial R) where
  toFun f := closedFormOperator f u
  map_add' f g := by
    simp only [closedFormOperator, LinearMap.coe_mk, AddHom.coe_mk, map_add, mul_add]
    ring
  map_smul' a f := closedFormOperator_smul_equation a f u

/-- The `(row, col)` entry of the Euler closed-form coefficient matrix, as a linear function of the
equation. -/
def eulerCoefficientEntryLinear {R : Type*} [CommRing R] (k : ℕ)
    (row : ℕ × ℕ) (col : EulerColumns k) : Polynomial (Polynomial R) →ₗ[R] R :=
  (LinearMap.proj row).comp ((bivariateCoefficients R).comp
    (closedFormEquationLinear (eulerBivariatePair R k (eulerPairBasis R k col))))

private lemma eulerCoefficientEntryLinear_apply {R : Type*} [CommRing R] (k : ℕ)
    (row : ℕ × ℕ) (col : EulerColumns k) (f : Polynomial (Polynomial R)) :
    eulerCoefficientEntryLinear k row col f = eulerClosedFormCoefficientMatrix k f row col := rfl

private lemma eulerCoefficientMatrix_expand {R : Type*} [CommRing R] (k : ℕ)
    (f : Polynomial (Polynomial R)) (hf : bivariateTotalDegree f ≤ k + 2)
    (row : ℕ × ℕ) (col : EulerColumns k) :
    ∑ i, eulerCoefficientData (k + 2) f i *
      eulerClosedFormCoefficientMatrix k (eulerCoefficientMonomial R (k + 2) i) row col =
      eulerClosedFormCoefficientMatrix k f row col := by
  have hh := congrArg (eulerCoefficientEntryLinear k row col)
    (eulerCoefficientData_reconstruct (k + 2) f hf)
  rw [map_sum] at hh
  simpa only [map_smul, smul_eq_mul, eulerCoefficientEntryLinear_apply] using hh

/-- Integer universal matrix in all coefficients of a degree-at-most-d equation. -/
def universalEulerMatrix (k : ℕ) : Matrix (ℕ × ℕ) (EulerColumns k)
    (MvPolynomial (EulerLowIndex (k + 2)) ℤ) :=
  fun row col => ∑ i, C (eulerClosedFormCoefficientMatrix k
    (eulerCoefficientMonomial ℤ (k + 2) i) row col) * X i

/-- Every universal matrix entry specializes to the differential
coefficient matrix, with no characteristic restriction. -/
theorem universalEulerMatrix_specialize {R : Type*} [CommRing R]
    (k : ℕ) (f : Polynomial (Polynomial R)) (hf : bivariateTotalDegree f ≤ k + 2) :
    (universalEulerMatrix k).map (eval₂Hom (Int.castRingHom R) (eulerCoefficientData (k + 2) f)) =
      eulerClosedFormCoefficientMatrix k f := by
  classical
  ext row col
  simp only [Matrix.map_apply, universalEulerMatrix]
  simp only [map_sum, map_mul, eval₂Hom_C, Int.coe_castRingHom]
  have hX (i : EulerLowIndex (k + 2)) :
      eval₂Hom (Int.castRingHom R) (eulerCoefficientData (k + 2) f) (X i) =
        eulerCoefficientData (k + 2) f i := eval₂_X _ _ _
  simp only [hX]
  rw [← eulerCoefficientMatrix_expand k f hf row col]
  apply Finset.sum_congr rfl
  intro i _
  have he := congrFun (congrFun (eulerClosedFormCoefficientMatrix_map (Int.castRingHom R) k
    (eulerCoefficientMonomial ℤ (k + 2) i)) row) col
  rw [eulerCoefficientMonomial_map] at he
  change
    ((eulerClosedFormCoefficientMatrix k (eulerCoefficientMonomial ℤ (k + 2) i) row col : ℤ) : R) =
      _ at he
  rw [he]
  change _ * _ = _ * _
  exact mul_comm _ _

end
end CCDN
