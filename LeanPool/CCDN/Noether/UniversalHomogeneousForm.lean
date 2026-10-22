/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.HomogeneousMonomials
public import LeanPool.CCDN.Noether.UniversalPlane
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.RingTheory.MvPolynomial

/-! A homogeneous form with independent integer coefficient variables,
and its exact specialization to every homogeneous equation. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The exponent vector of degree `d` in the variables `σ` corresponding to a multiset `i` of size
`d`. -/
def homogeneousCoefficientExponent (σ : Type*) [Fintype σ] [DecidableEq σ]
    (d : ℕ) (i : Sym σ d) : σ →₀ ℕ :=
  ((degreeEqEquivSym σ d).symm i).val

/-- The exponent vector `homogeneousCoefficientExponent σ d i` has degree `d`. -/
lemma homogeneousCoefficientExponent_degree (σ : Type*) [Fintype σ] [DecidableEq σ]
    (d : ℕ) (i : Sym σ d) : (homogeneousCoefficientExponent σ d i).degree = d :=
  ((degreeEqEquivSym σ d).symm i).property

private lemma homogeneousCoefficientExponent_injective (σ : Type*) [Fintype σ] [DecidableEq σ]
    (d : ℕ) : Function.Injective (homogeneousCoefficientExponent σ d) :=
  Subtype.val_injective.comp (degreeEqEquivSym σ d).symm.injective

/-- The universal homogeneous form of degree `d` in the variables `σ`: the sum of all monomials of
degree `d`, each with its own independent integer coefficient variable. -/
def universalHomogeneousForm (σ : Type*) [Fintype σ] [DecidableEq σ] (d : ℕ) :
    MvPolynomial σ (MvPolynomial (Sym σ d) ℤ) :=
  ∑ i, monomial (homogeneousCoefficientExponent σ d i) (X i)

/-- The coefficient of `f` at the degree-`d` monomial indexed by `i`. -/
def homogeneousCoefficientData {R σ : Type*} [CommRing R] [Fintype σ] [DecidableEq σ]
    (d : ℕ) (f : MvPolynomial σ R) (i : Sym σ d) : R :=
  f.coeff (homogeneousCoefficientExponent σ d i)

/-- A homogeneous polynomial `f` of degree `d` is the sum of its degree-`d` monomials weighted by
`homogeneousCoefficientData d f`. -/
theorem homogeneousCoefficientData_reconstruct {R σ : Type*} [CommRing R]
    [Fintype σ] [DecidableEq σ] (d : ℕ)
    (f : MvPolynomial σ R) (hf : f.IsHomogeneous d) :
    ∑ i : Sym σ d, monomial (homogeneousCoefficientExponent σ d i)
      (homogeneousCoefficientData d f i) = f := by
  classical
  ext m
  rw [coeff_sum]
  by_cases hm : m.degree = d
  · let i : Sym σ d := degreeEqEquivSym σ d ⟨m, hm⟩
    have hi : homogeneousCoefficientExponent σ d i = m := by
      exact congrArg Subtype.val ((degreeEqEquivSym σ d).symm_apply_apply ⟨m, hm⟩)
    rw [Finset.sum_eq_single i]
    · rw [coeff_monomial, hi, ite_eq_left rfl]
      exact congrArg f.coeff hi
    · intro j _ hji
      rw [coeff_monomial, ite_eq_right]
      intro hj
      exact hji (homogeneousCoefficientExponent_injective σ d (hj.trans hi.symm))
    · simp
  · rw [hf.coeff_eq_zero hm]
    apply Finset.sum_eq_zero
    intro i _
    rw [coeff_monomial, ite_eq_right]
    intro hi
    exact hm (hi ▸ homogeneousCoefficientExponent_degree σ d i)

/-- The ring homomorphism from the integer polynomials in the coefficient variables to `R` that
sends each coefficient variable to the corresponding coefficient of `f`. -/
def homogeneousCoefficientSpecialization {R σ : Type*} [CommRing R] [Fintype σ] [DecidableEq σ]
    (d : ℕ) (f : MvPolynomial σ R) : MvPolynomial (Sym σ d) ℤ →+* R :=
  eval₂Hom (Int.castRingHom R) (homogeneousCoefficientData d f)

/-- The coefficient variables specialize to the homogeneous equation,
over every commutative coefficient ring. -/
theorem universalHomogeneousForm_specialize {R σ : Type*} [CommRing R]
    [Fintype σ] [DecidableEq σ] (d : ℕ)
    (f : MvPolynomial σ R) (hf : f.IsHomogeneous d) :
    MvPolynomial.map (homogeneousCoefficientSpecialization d f) (universalHomogeneousForm σ d) =
      f := by
  rw [universalHomogeneousForm, map_sum]
  have hX (i : Sym σ d) : homogeneousCoefficientSpecialization d f (X i) =
      homogeneousCoefficientData d f i := eval₂_X _ _ _
  simpa only [map_monomial, hX] using homogeneousCoefficientData_reconstruct d f hf

/-- The universal homogeneous form is the sum over all degree-`d` monomials of the coefficient
variable times that monomial, an expansion linear in the coefficient variables. -/
lemma universalHomogeneousForm_linear_expansion (σ : Type*) [Fintype σ] [DecidableEq σ]
    (d : ℕ) :
    universalHomogeneousForm σ d =
      ∑ i : Sym σ d, (X i : MvPolynomial (Sym σ d) ℤ) •
        MvPolynomial.map (C : ℤ →+* MvPolynomial (Sym σ d) ℤ)
          (monomial (homogeneousCoefficientExponent σ d i) (1 : ℤ)) := by
  simp only [universalHomogeneousForm, map_monomial, map_one, smul_monomial, smul_eq_mul, mul_one]

/-- The universal plane restriction `universalPlanePolynomial` as an `R`-linear map. -/
def universalPlanePolynomialLinear (R σ : Type*) [CommRing R] :
    MvPolynomial σ R →ₗ[R] Polynomial (Polynomial (MvPolynomial (PlaneParameters σ) R)) :=
  ((bivariatePolynomialEquiv (MvPolynomial (PlaneParameters σ) R)).toLinearMap.restrictScalars
    R).comp (universalPlaneMap R σ).toLinearMap

end
end CCDN
