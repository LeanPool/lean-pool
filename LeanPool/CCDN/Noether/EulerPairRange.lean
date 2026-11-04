/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Noether.EulerClosedFormRank
import LeanPool.CCDN.ForMathlib.MvPolynomial
import LeanPool.CCDN.Hilbert.HomogeneousHilbert
import LeanPool.CCDN.Noether.ShearNormalization

/-! The explicit Euler parameters exhaust all polynomial pairs satisfying
the degree and Euler-contraction constraints. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private lemma totalDegree_sub_top_component_le {R σ : Type*} [CommRing R]
    (k : ℕ) (p : MvPolynomial σ R) (hp : p.totalDegree ≤ k + 1) :
    (p - homogeneousComponent (k + 1) p).totalDegree ≤ k := by
  classical
  apply Finset.sup_le
  intro m hm
  have hm0 := mem_support_iff.mp hm
  rw [coeff_sub, coeff_homogeneousComponent] at hm0
  by_cases he : m.degree = k + 1
  · simp only [he, ite_true, sub_self, ne_eq, not_true_eq_false] at hm0
  · simp only [he, ite_false, sub_zero] at hm0
    have hle := (le_totalDegree (mem_support_iff.mpr hm0)).trans hp
    change m.degree ≤ k
    change m.degree ≤ k + 1 at hle
    omega

/-- Every bounded pair with lower-degree Euler contraction has the unique
shape `(A+yQ,B-xQ)` used by the coefficient matrix. -/
private theorem exists_eulerPairCoordinates {F : Type*} [Field F]
    (k : ℕ) (p q : MvPolynomial (Fin 2) F)
    (hp : p.totalDegree ≤ k + 1) (hq : q.totalDegree ≤ k + 1)
    (he : (X 0 * p + X 1 * q).totalDegree ≤ k + 1) :
    ∃ u : EulerPairSpace F k, eulerPairCoordinates F k u = (p, q) := by
  let P := homogeneousComponent (k + 1) p
  let Q := homogeneousComponent (k + 1) q
  have htop : X 0 * P + X 1 * Q = 0 := by
    have hh := homogeneousComponent_eq_zero (k + 2) (X 0 * p + X 1 * q) (by omega)
    rw [map_add, show k + 2 = 1 + (k + 1) by omega,
      homogeneousComponent_mul_of_isHomogeneous_left (isHomogeneous_X F (0 : Fin 2)),
      homogeneousComponent_mul_of_isHomogeneous_left (isHomogeneous_X F (1 : Fin 2))] at hh
    exact hh
  have hdiv : X (1 : Fin 2) ∣ P := by
    have hh : X (1 : Fin 2) ∣ X 0 * P := by
      rw [show X 0 * P = -(X 1 * Q) by linear_combination htop]
      exact dvd_neg.mpr (dvd_mul_right _ _)
    exact (X_dvd_mul_iff.mp hh).resolve_left (by
      rw [X_dvd_X]
      decide)
  obtain ⟨r, hr⟩ := hdiv
  have hrhom : r.IsHomogeneous k := by
    have hh := homogeneous_multiplier (isHomogeneous_X F (1 : Fin 2))
      (X_ne_zero (1 : Fin 2))
      (show (X 1 * r).IsHomogeneous (k + 1) from
        hr ▸ homogeneousComponent_isHomogeneous (k + 1) p)
      (by omega)
    simpa only [Nat.add_sub_cancel] using hh
  have hQ : Q = -(X 0 * r) := by
    apply mul_left_cancel₀ (X_ne_zero (1 : Fin 2))
    rw [hr] at htop
    linear_combination htop
  let u : EulerPairSpace F k :=
    (⟨p - P, (mem_restrictTotalDegree _ _ _).mpr (totalDegree_sub_top_component_le k p hp)⟩,
     ⟨q - Q, (mem_restrictTotalDegree _ _ _).mpr (totalDegree_sub_top_component_le k q hq)⟩,
     ⟨r, hrhom⟩)
  refine ⟨u, ?_⟩
  apply Prod.ext
  · change p - P + X 1 * r = p
    rw [← hr]
    ring
  · change q - Q - X 0 * r = q
    rw [hQ]
    ring

/-- Every pair of bivariate polynomials of total degree at most `k + 1` whose radial contraction
also has total degree at most `k + 1` comes from an element of `EulerPairSpace F k`. -/
theorem exists_eulerBivariatePair {F : Type*} [Field F]
    (k : ℕ) (p q : Polynomial (Polynomial F))
    (hp : bivariateTotalDegree p ≤ k + 1)
    (hq : bivariateTotalDegree q ≤ k + 1)
    (he : bivariateTotalDegree (bivariateEulerContraction F (p, q)) ≤ k + 1) :
    ∃ u : EulerPairSpace F k, eulerBivariatePair F k u = (p, q) := by
  let e := bivariatePolynomialEquiv F
  have he' : (X 0 * e.symm p + X 1 * e.symm q).totalDegree ≤ k + 1 := by
    have hh : e (X 0 * e.symm p + X 1 * e.symm q) =
        bivariateEulerContraction F (p, q) := by
      simp only [map_add, map_mul, AlgEquiv.apply_symm_apply,
        bivariatePolynomialEquiv_X_zero, bivariatePolynomialEquiv_X_one,
        bivariateEulerContraction, LinearMap.coe_mk, AddHom.coe_mk, e]
    rw [← hh] at he
    simpa only [bivariateTotalDegree, e, AlgEquiv.symm_apply_apply] using he
  obtain ⟨u, hu⟩ := exists_eulerPairCoordinates k (e.symm p) (e.symm q) hp hq he'
  refine ⟨u, ?_⟩
  change (e (eulerPairCoordinates F k u).1, e (eulerPairCoordinates F k u).2) = (p, q)
  rw [hu]
  simp only [AlgEquiv.apply_symm_apply]

end
end CCDN
