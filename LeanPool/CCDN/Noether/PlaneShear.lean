/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Data.Fin.VecNotation
import LeanPool.CCDN.Noether.BivariateTotalDegree

/-! Integral plane shears are polynomial-ring automorphisms in every
characteristic. They will place the highest-degree part in the outer variable. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Fix variable zero and replace variable one by x₁+a*x₀. -/
def planeShearHom (R : Type*) [CommRing R] (a : R) :
    MvPolynomial (Fin 2) R →ₐ[R] MvPolynomial (Fin 2) R :=
  aeval ![X 0, X 1 + C a * X 0]

/-- Composing the plane shears with parameters `a` and `b` gives the shear with parameter
`a + b`. -/
lemma planeShearHom_comp {R : Type*} [CommRing R] (a b : R) :
    (planeShearHom R a).comp (planeShearHom R b) = planeShearHom R (a + b) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [planeShearHom]
  ring

/-- The plane shear with parameter zero is the identity. -/
@[simp]
lemma planeShearHom_zero (R : Type*) [CommRing R] :
    planeShearHom R 0 = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [planeShearHom]

/-- The plane shear `x₁ ↦ x₁ + a * x₀` as an algebra automorphism. The inverse shear uses the
negative parameter, so this works over Z and all its residue fields without determinant
denominators. -/
def planeShear (R : Type*) [CommRing R] (a : R) :
    MvPolynomial (Fin 2) R ≃ₐ[R] MvPolynomial (Fin 2) R :=
  AlgEquiv.ofAlgHom (planeShearHom R a) (planeShearHom R (-a))
    (by rw [planeShearHom_comp, add_neg_cancel, planeShearHom_zero])
    (by rw [planeShearHom_comp, neg_add_cancel, planeShearHom_zero])

private lemma planeShear_monomial {R : Type*} [CommRing R] (a : R)
    (m : Fin 2 →₀ ℕ) (c : R) :
    planeShear R a (monomial m c) =
      C c * (X 0) ^ m 0 * (X 1 + C a * X 0) ^ m 1 := by
  change aeval ![X 0, X 1 + C a * X 0] (monomial m c) = _
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [algebraMap_eq, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  ring

private lemma planeShear_monomial_totalDegree_le {R : Type*} [CommRing R] [Nontrivial R]
    (a : R) (m : Fin 2 →₀ ℕ) (c : R) :
    (planeShear R a (monomial m c)).totalDegree ≤ m.sum (fun _ e => e) := by
  have hx : (X 1 + C a * X 0 : MvPolynomial (Fin 2) R).totalDegree ≤ 1 := by
    apply (totalDegree_add _ _).trans
    apply max_le
    · simp
    · simpa using totalDegree_mul (C a : MvPolynomial (Fin 2) R) (X 0)
  rw [planeShear_monomial]
  have h₁ := totalDegree_mul (C c : MvPolynomial (Fin 2) R) ((X 0) ^ m 0)
  have h₂ := totalDegree_mul (C c * (X 0) ^ m 0 : MvPolynomial (Fin 2) R) ((X 1 + C a * X 0) ^ m 1)
  have h₃ := totalDegree_pow (X 1 + C a * X 0 : MvPolynomial (Fin 2) R) (m 1)
  simp only [totalDegree_C, totalDegree_X_pow, zero_add] at h₁
  have hs : m.sum (fun _ e => e) = m 0 + m 1 := by
    conv_lhs => rw [bivariate_exponent_eq m]
    exact bivariate_exponent_sum _ _
  rw [hs]
  have h₄ : ((X 1 + C a * X 0 : MvPolynomial (Fin 2) R) ^ m 1).totalDegree ≤ m 1 :=
    h₃.trans (by simpa using Nat.mul_le_mul_left (m 1) hx)
  omega

private lemma planeShear_totalDegree_le {R : Type*} [CommRing R] [Nontrivial R]
    (a : R) (f : MvPolynomial (Fin 2) R) :
    (planeShear R a f).totalDegree ≤ f.totalDegree := by
  classical
  conv_lhs => rw [f.as_sum, map_sum]
  apply (totalDegree_finsetSum _ _).trans
  apply Finset.sup_le
  intro m hm
  exact (planeShear_monomial_totalDegree_le a m (f.coeff m)).trans (le_totalDegree hm)

/-- A plane shear preserves the total degree; the inverse shear gives the reverse inequality. -/
lemma planeShear_totalDegree {R : Type*} [CommRing R] [Nontrivial R]
    (a : R) (f : MvPolynomial (Fin 2) R) :
    (planeShear R a f).totalDegree = f.totalDegree := by
  apply le_antisymm (planeShear_totalDegree_le a f)
  have h := planeShear_totalDegree_le (-a) (planeShear R a f)
  have he : planeShear R (-a) (planeShear R a f) = f := (planeShear R a).symm_apply_apply f
  rw [he] at h
  exact h

/-- `planeShear` commutes with every coefficient map. -/
lemma planeShear_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (a : R) (f : MvPolynomial (Fin 2) R) :
    MvPolynomial.map φ (planeShear R a f) =
      planeShear S (φ a) (MvPolynomial.map φ f) := by
  suffices hh : (MvPolynomial.map φ).comp (planeShear R a).toRingHom =
      (planeShear S (φ a)).toRingHom.comp (MvPolynomial.map φ) from
    congrArg (fun h : MvPolynomial (Fin 2) R →+* MvPolynomial (Fin 2) S => h f) hh
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [planeShear, planeShearHom]
  · intro i
    fin_cases i <;> simp [planeShear, planeShearHom]

end
end CCDN
