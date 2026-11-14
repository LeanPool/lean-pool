/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Noether.AmbientNoetherForms
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import LeanPool.CCDN.Noether.EulerPairSpecialization
import LeanPool.CCDN.Noether.EulerProductVanishing
import LeanPool.CCDN.Noether.UniversalPlaneBadWitness
import Mathlib.Algebra.MvPolynomial.Nilpotent

/-! The constructed ambient coefficient forms vanish on every geometrically
reducible homogeneous equation, in every characteristic. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private lemma universalPlanePolynomial_mul {R σ : Type*} [CommRing R]
    (g h : MvPolynomial σ R) :
    universalPlanePolynomial (g * h) = universalPlanePolynomial g * universalPlanePolynomial h := by
  simp only [universalPlanePolynomial, map_mul]

/-- The universal plane restriction of `f` has bivariate total degree at most the total degree of
`f`. -/
lemma universalPlanePolynomial_totalDegree_le {R σ : Type*} [CommRing R]
    (f : MvPolynomial σ R) : bivariateTotalDegree (universalPlanePolynomial f) ≤ f.totalDegree := by
  simpa only [universalPlanePolynomial, bivariateTotalDegree, AlgEquiv.symm_apply_apply] using
    universalPlaneMap_planeDegree_le f

/-- If `g` and `h` have total degrees at most `a` and `b`, with `a, b > 0` and `a + b = k + 2`,
then every minor of order `(k + 2)^2 - 1` of the Euler closed-form coefficient matrix of the
universal plane restriction of `g * h` vanishes. -/
theorem ambientEuler_minor_eq_zero_of_product {R σ : Type*} [CommRing R]
    (k a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = k + 2)
    (g h : MvPolynomial σ R) (hg : g.totalDegree ≤ a) (hh : h.totalDegree ≤ b)
    (rows : Fin ((k + 2) ^ 2 - 1) → ℕ × ℕ)
    (cols : Fin ((k + 2) ^ 2 - 1) → EulerColumns k) :
    ((eulerClosedFormCoefficientMatrix k (universalPlanePolynomial (g * h))).submatrix
      rows cols).det = 0 := by
  rw [universalPlanePolynomial_mul]
  exact eulerClosedForm_minor_eq_zero_of_product k a b ha hb hab _ _
    ((universalPlanePolynomial_totalDegree_le g).trans hg)
    ((universalPlanePolynomial_totalDegree_le h).trans hh) rows cols

/-- Reducibility forces the entire parameter determinant to vanish,
including the zero homogeneous equation. -/
private theorem ambientEuler_minor_eq_zero_of_not_irreducible {K σ : Type*} [Field K]
    (k : ℕ) (f : MvPolynomial σ K) (hf : f.IsHomogeneous (k + 2))
    (hred : ¬Irreducible f)
    (rows : Fin ((k + 2) ^ 2 - 1) → ℕ × ℕ)
    (cols : Fin ((k + 2) ^ 2 - 1) → EulerColumns k) :
    ((eulerClosedFormCoefficientMatrix k (universalPlanePolynomial f)).submatrix
      rows cols).det = 0 := by
  by_cases hf0 : f = 0
  · subst f
    simpa only [zero_mul] using ambientEuler_minor_eq_zero_of_product
      (σ := σ) k 1 (k + 1) (by omega) (by omega) (by omega)
      (0 : MvPolynomial σ K) 0 (by simp) (by simp) rows cols
  have hd : f.totalDegree = k + 2 := hf.totalDegree hf0
  have hfu : ¬IsUnit f := by
    intro hu
    have hh := (isUnit_iff_totalDegree_of_isReduced.mp hu).2
    omega
  obtain ⟨g, h, hgu, hhu, he⟩ := (irreducible_or_factor hfu).resolve_left hred
  have hgh0 : g * h ≠ 0 := he ▸ hf0
  have hg0 := (mul_ne_zero_iff.mp hgh0).1
  have hh0 := (mul_ne_zero_iff.mp hgh0).2
  have hgpos := totalDegree_pos_of_ne_zero_of_not_isUnit hg0 hgu
  have hhpos := totalDegree_pos_of_ne_zero_of_not_isUnit hh0 hhu
  have hsum : g.totalDegree + h.totalDegree = k + 2 := by
    rw [he, totalDegree_mul_of_isDomain hg0 hh0] at hd
    exact hd
  rw [he]
  exact ambientEuler_minor_eq_zero_of_product k _ _ hgpos hhpos hsum g h le_rfl le_rfl rows cols

/-- Minors of the Euler closed-form coefficient matrix of the universal plane restriction commute
with applying a coefficient ring homomorphism `φ` to the polynomial. -/
lemma ambientEuler_minor_map {R S σ : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (k : ℕ) (f : MvPolynomial σ R)
    (rows : Fin ((k + 2) ^ 2 - 1) → ℕ × ℕ)
    (cols : Fin ((k + 2) ^ 2 - 1) → EulerColumns k) :
    MvPolynomial.map φ
      (((eulerClosedFormCoefficientMatrix k (universalPlanePolynomial f)).submatrix
        rows cols).det) =
      ((eulerClosedFormCoefficientMatrix k
        (universalPlanePolynomial (MvPolynomial.map φ f))).submatrix rows cols).det := by
  rw [eulerClosedForm_minor_map, ← universalPlanePolynomial_map]

/-- The first implication in the universal Noether theorem, for the
constructed integer coefficient forms and arbitrary characteristic. -/
theorem ambientNoetherForm_eq_zero_of_not_absolutely_irreducible
    {K σ : Type*} [Field K] [Fintype σ] [DecidableEq σ]
    (k : ℕ) (f : MvPolynomial σ K) (hf : f.IsHomogeneous (k + 2))
    (hred : ¬Irreducible (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f))
    (rows : Fin ((k + 2) ^ 2 - 1) → ℕ × ℕ)
    (cols : Fin ((k + 2) ^ 2 - 1) → EulerColumns k)
    (m : PlaneParameters σ →₀ ℕ) :
    homogeneousCoefficientSpecialization (k + 2) f (ambientNoetherForm σ k rows cols m) = 0 := by
  let φ := algebraMap K (AlgebraicClosure K)
  have hz := ambientEuler_minor_eq_zero_of_not_irreducible k (MvPolynomial.map φ f)
    (hf.map φ) hred rows cols
  apply φ.injective
  rw [map_zero, ambientNoetherForm_specialize k f hf rows cols m,
    ← coeff_map, ambientEuler_minor_map, hz]
  rfl

end
end CCDN
