/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Noether.ClosedFormBaseChange
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! Total degree of nested bivariate polynomials, transported from the
multivariate polynomial ring. This controls the support of factor forms. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial

/-- The identification of polynomials in two variables with nested polynomials `R[X][X]`:
variable zero is the outer variable, and variable one is the inner one. -/
def bivariatePolynomialEquiv (R : Type*) [CommRing R] :
    MvPolynomial (Fin 2) R ≃ₐ[R] R[X][X] :=
  (MvPolynomial.finSuccEquiv R 1).trans
    (Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv R (Fin 1)))

/-- The coefficient with outer exponent `i` and inner exponent `j` of the nested polynomial
associated with `f` is the coefficient of `f` at the exponent vector `(i, j)`. -/
lemma bivariatePolynomialEquiv_coeff {R : Type*} [CommRing R]
    (f : MvPolynomial (Fin 2) R) (i j : ℕ) :
    ((bivariatePolynomialEquiv R f).coeff i).coeff j =
      f.coeff (Finsupp.cons i (Finsupp.single 0 j)) := by
  change ((Polynomial.map (MvPolynomial.uniqueAlgEquiv R (Fin 1)).toRingHom
    (MvPolynomial.finSuccEquiv R 1 f)).coeff i).coeff j = _
  rw [Polynomial.coeff_map]
  change ((MvPolynomial.uniqueAlgEquiv R (Fin 1))
    ((MvPolynomial.finSuccEquiv R 1 f).coeff i)).coeff j = _
  rw [MvPolynomial.coeff_uniqueAlgEquiv, MvPolynomial.finSuccEquiv_coeff_coeff]
  rfl

/-- Every exponent vector in two variables is `Finsupp.cons` of its two components. -/
lemma bivariate_exponent_eq (m : Fin 2 →₀ ℕ) :
    m = Finsupp.cons (m 0) (Finsupp.single 0 (m 1)) := by
  ext i
  fin_cases i
  · simp
  · change m 1 = (Finsupp.cons (m 0) (Finsupp.single 0 (m 1))) (Fin.succ (0 : Fin 1))
    rw [Finsupp.cons_succ, Finsupp.single_eq_same]

/-- The degree of the two-variable exponent vector with components `i` and `j` is `i + j`. -/
lemma bivariate_exponent_sum (i j : ℕ) :
    (Finsupp.cons i (Finsupp.single 0 j) : Fin 2 →₀ ℕ).sum (fun _ e => e) = i + j := by
  simp [Finsupp.sum_cons]

/-- The total degree of a nested bivariate polynomial, with the usual convention that the zero
polynomial has natural-valued total degree zero. -/
def bivariateTotalDegree {R : Type*} [CommRing R] (f : R[X][X]) : ℕ :=
  ((bivariatePolynomialEquiv R).symm f).totalDegree

/-- If the coefficient of `f` with outer exponent `i` and inner exponent `j` is nonzero, then
`i + j` is at most the total degree of `f`. -/
lemma bivariateTotalDegree_coeff_le {R : Type*} [CommRing R]
    (f : R[X][X]) (i j : ℕ) (h : (f.coeff i).coeff j ≠ 0) :
    i + j ≤ bivariateTotalDegree f := by
  have hc := bivariatePolynomialEquiv_coeff ((bivariatePolynomialEquiv R).symm f) i j
  rw [AlgEquiv.apply_symm_apply] at hc
  have hm := MvPolynomial.mem_support_iff.mpr (hc ▸ h)
  simpa only [bivariate_exponent_sum, bivariateTotalDegree] using MvPolynomial.le_totalDegree hm

/-- The total degree of `f` is at most `d` if and only if `i + j ≤ d` whenever the coefficient of
`f` with outer exponent `i` and inner exponent `j` is nonzero. -/
lemma bivariateTotalDegree_le_iff {R : Type*} [CommRing R]
    (f : R[X][X]) (d : ℕ) :
    bivariateTotalDegree f ≤ d ↔ ∀ i j, (f.coeff i).coeff j ≠ 0 → i + j ≤ d := by
  constructor
  · intro h i j hij
    exact (bivariateTotalDegree_coeff_le f i j hij).trans h
  · intro h
    apply Finset.sup_le
    intro m hm
    rw [bivariate_exponent_eq m] at hm ⊢
    rw [bivariate_exponent_sum]
    apply h
    have hc := bivariatePolynomialEquiv_coeff ((bivariatePolynomialEquiv R).symm f) (m 0) (m 1)
    rw [AlgEquiv.apply_symm_apply] at hc
    exact hc.symm ▸ MvPolynomial.mem_support_iff.mp hm

private lemma bivariateTotalDegree_mul {R : Type*} [CommRing R] [IsDomain R]
    (f g : R[X][X]) (hf : f ≠ 0) (hg : g ≠ 0) :
    bivariateTotalDegree (f * g) = bivariateTotalDegree f + bivariateTotalDegree g := by
  unfold bivariateTotalDegree
  rw [map_mul]
  exact MvPolynomial.totalDegree_mul_of_isDomain
    ((map_ne_zero_iff _ (bivariatePolynomialEquiv R).symm.injective).mpr hf)
    ((map_ne_zero_iff _ (bivariatePolynomialEquiv R).symm.injective).mpr hg)

/-- The total degree of a product is at most the sum of the total degrees. -/
lemma bivariateTotalDegree_mul_le {R : Type*} [CommRing R] (f g : R[X][X]) :
    bivariateTotalDegree (f * g) ≤ bivariateTotalDegree f + bivariateTotalDegree g := by
  unfold bivariateTotalDegree
  rw [map_mul]
  exact MvPolynomial.totalDegree_mul _ _

/-- Differentiation in the outer variable lowers the total degree by at least one. -/
lemma bivariateTotalDegree_outerDerivative_le {R : Type*} [CommRing R]
    (f : R[X][X]) : bivariateTotalDegree f.derivative ≤ bivariateTotalDegree f - 1 := by
  rw [bivariateTotalDegree_le_iff]
  intro i j hij
  have hc : (f.coeff (i + 1)).coeff j ≠ 0 := by
    intro hz
    apply hij
    rw [coeff_derivative, show (i : R[X]) + 1 = C ((i : R) + 1) by simp, coeff_mul_C, hz, zero_mul]
  have h := bivariateTotalDegree_coeff_le f (i + 1) j hc
  omega

/-- Differentiation in the inner variable lowers the total degree by at least one. -/
lemma bivariateTotalDegree_innerDerivative_le {R : Type*} [CommRing R]
    (f : R[X][X]) :
    bivariateTotalDegree ((bivariateCoefficientDerivative R) f) ≤ bivariateTotalDegree f - 1 := by
  rw [bivariateTotalDegree_le_iff]
  intro i j hij
  have hc : (f.coeff i).coeff (j + 1) ≠ 0 := by
    intro hz
    apply hij
    rw [coeff_bivariateCoefficientDerivative, coeff_derivative, hz, zero_mul]
  have h := bivariateTotalDegree_coeff_le f i (j + 1) hc
  omega

/-- A bivariate polynomial of total degree less than `d` is supported in the grid of outer and inner
exponents less than `d`. -/
lemma inBivariateGrid_of_totalDegree_lt {R : Type*} [CommRing R]
    (d : ℕ) (f : R[X][X]) (hd : bivariateTotalDegree f < d) : InBivariateGrid d f := by
  intro i j hij
  by_contra hc
  have h := bivariateTotalDegree_coeff_le f i j hc
  omega

/-- The zero polynomial has total degree zero. -/
@[simp]
lemma bivariateTotalDegree_zero {R : Type*} [CommRing R] :
    bivariateTotalDegree (0 : R[X][X]) = 0 := by
  simp [bivariateTotalDegree]

/-- The degree in the outer variable is at most the total degree. -/
lemma bivariate_natDegree_le_totalDegree {R : Type*} [CommRing R]
    (f : R[X][X]) : f.natDegree ≤ bivariateTotalDegree f := by
  by_cases hf : f = 0
  · simp [hf]
  have hc : f.coeff f.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hf
  have hn : ((f.coeff f.natDegree).coeff (f.coeff f.natDegree).natDegree) ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hc
  have hh := bivariateTotalDegree_coeff_le f f.natDegree _ hn
  omega

/-- Both components of the gradient fit the grid for a positive total-degree
bound, in every characteristic. -/
lemma bivariate_gradient_in_grid {R : Type*} [CommRing R]
    (d : ℕ) (hd : 0 < d) (f : R[X][X]) (hf : bivariateTotalDegree f ≤ d) :
    InBivariateGrid d f.derivative ∧
      InBivariateGrid d ((bivariateCoefficientDerivative R) f) := by
  constructor
  · apply inBivariateGrid_of_totalDegree_lt
    have h := bivariateTotalDegree_outerDerivative_le f
    omega
  · apply inBivariateGrid_of_totalDegree_lt
    have h := bivariateTotalDegree_innerDerivative_le f
    omega

/-- The logarithmic form associated with a nonconstant factor has strictly
smaller total degree than the product, so both numerators fit the matrix. -/
lemma bivariate_factor_form_in_grid {R : Type*} [CommRing R] [IsDomain R]
    (d : ℕ) (g h : R[X][X]) (hg : g ≠ 0) (hh : h ≠ 0)
    (hgdeg : 0 < bivariateTotalDegree g) (hdeg : bivariateTotalDegree (g * h) ≤ d) :
    InBivariateGrid d (h * g.derivative) ∧
      InBivariateGrid d (h * (bivariateCoefficientDerivative R) g) := by
  rw [bivariateTotalDegree_mul g h hg hh] at hdeg
  constructor
  · apply inBivariateGrid_of_totalDegree_lt
    have h₁ := bivariateTotalDegree_mul_le h g.derivative
    have h₂ := bivariateTotalDegree_outerDerivative_le g
    omega
  · apply inBivariateGrid_of_totalDegree_lt
    have h₁ := bivariateTotalDegree_mul_le h ((bivariateCoefficientDerivative R) g)
    have h₂ := bivariateTotalDegree_innerDerivative_le g
    omega

/-- If `g` is nonconstant and `g ^ (k + 2) * h` has total degree at most `d`, then the products
of `g ^ k * h` with both partial derivatives of `g` (the numerators of the higher-pole form) fit
strictly inside the grid. -/
lemma bivariate_power_factor_form_in_grid {R : Type*} [CommRing R] [IsDomain R]
    (d k : ℕ) (g h : R[X][X]) (hg : g ≠ 0) (hh : h ≠ 0)
    (hgdeg : 0 < bivariateTotalDegree g)
    (hdeg : bivariateTotalDegree (g ^ (k + 2) * h) ≤ d) :
    InBivariateGrid d (g ^ k * h * g.derivative) ∧
      InBivariateGrid d (g ^ k * h * (bivariateCoefficientDerivative R) g) := by
  have he : g ^ (k + 2) * h = g * (g * (g ^ k * h)) := by
    rw [pow_add, pow_two]
    ring
  rw [he, bivariateTotalDegree_mul g _ hg (mul_ne_zero hg (mul_ne_zero (pow_ne_zero _ hg) hh)),
    bivariateTotalDegree_mul g _ hg (mul_ne_zero (pow_ne_zero _ hg) hh)] at hdeg
  apply bivariate_factor_form_in_grid d g (g ^ k * h) hg (mul_ne_zero (pow_ne_zero _ hg) hh) hgdeg
  rw [bivariateTotalDegree_mul g _ hg (mul_ne_zero (pow_ne_zero _ hg) hh)]
  omega

/-- The inner degree of each outer coefficient is at most the total degree. -/
lemma bivariate_coefficient_natDegree_le_totalDegree {R : Type*} [CommRing R]
    (f : R[X][X]) (i : ℕ) : (f.coeff i).natDegree ≤ bivariateTotalDegree f := by
  by_cases hc : f.coeff i = 0
  · simp [hc]
  have hn : (f.coeff i).coeff (f.coeff i).natDegree ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hc
  have hh := bivariateTotalDegree_coeff_le f i _ hn
  omega

/-- Applying a coefficient ring homomorphism to both levels preserves monicity in the outer
variable. -/
lemma bivariateMap_monic {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) {f : R[X][X]} (hf : f.Monic) : (bivariateMap φ f).Monic :=
  hf.map (Polynomial.mapRingHom φ)

/-- Applying a coefficient ring homomorphism to a polynomial monic in the outer variable preserves
its outer degree, provided the target ring is nontrivial. -/
lemma bivariateMap_natDegree_of_monic {R S : Type*} [CommRing R] [CommRing S] [Nontrivial S]
    (φ : R →+* S) {f : R[X][X]} (hf : f.Monic) :
    (bivariateMap φ f).natDegree = f.natDegree :=
  hf.natDegree_map (Polynomial.mapRingHom φ)

/-- Reduction of coefficients cannot increase the total degree. -/
lemma bivariateTotalDegree_map_le {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (f : R[X][X]) :
    bivariateTotalDegree (bivariateMap φ f) ≤ bivariateTotalDegree f := by
  rw [bivariateTotalDegree_le_iff]
  intro i j hij
  apply bivariateTotalDegree_coeff_le
  intro hz
  apply hij
  rw [bivariateMap_coeff, hz, map_zero]

end
end CCDN
