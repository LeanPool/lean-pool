/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.HomogeneousChart
public import LeanPool.CCDN.Algebra.HomogeneousTranslation
public import LeanPool.CCDN.Algebra.OriginShift

/-! The affine translations underlying the homogeneous coordinate changes
preserve degree and irreducibility, over every coefficient field. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The translation `X j ↦ X j + a j` of polynomials in `Fin n` variables, as an algebra
automorphism over `R`. -/
def affineTranslation (R : Type*) [CommRing R] {n : ℕ} (a : Fin n → R) :
    MvPolynomial (Fin n) R ≃ₐ[R] MvPolynomial (Fin n) R :=
  originShiftEquiv a

/-- An affine translation of variables preserves and reflects irreducibility. -/
lemma affineTranslation_irreducible_iff {R : Type*} [CommRing R] {n : ℕ}
    (a : Fin n → R) (f : MvPolynomial (Fin n) R) :
    Irreducible (affineTranslation R a f) ↔ Irreducible f :=
  MulEquiv.irreducible_iff (f := affineTranslation R a)

/-- An affine translation of variables does not increase the total degree. -/
lemma affineTranslation_totalDegree_le {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ}
    (a : Fin n → R) (f : MvPolynomial (Fin n) R) :
    (affineTranslation R a f).totalDegree ≤ f.totalDegree := by
  classical
  have hm (m : Fin n →₀ ℕ) (c : R) :
      (affineTranslation R a (monomial m c)).totalDegree ≤ m.sum (fun _ e => e) := by
    change (aeval (fun j => X j + C (a j)) (monomial m c)).totalDegree ≤ _
    rw [aeval_monomial]
    have hp : (m.prod (fun j e => (X j + C (a j)) ^ e)).totalDegree ≤ m.sum (fun _ e => e) := by
      apply (totalDegree_finsetProd _ _).trans
      apply Finset.sum_le_sum
      intro j _
      have hh : (X j + C (a j) : MvPolynomial (Fin n) R).totalDegree ≤ 1 := by
        exact (totalDegree_add _ _).trans (by simp)
      exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (m j) hh)
    have hh := totalDegree_mul (C c) (m.prod (fun j e => (X j + C (a j)) ^ e))
    simp only [totalDegree_C, zero_add] at hh
    exact hh.trans hp
  conv_lhs => rw [f.as_sum, map_sum]
  apply totalDegree_finsetSum_le
  intro m hm'
  exact (hm m _).trans (le_totalDegree hm')

/-- An affine translation of variables preserves the total degree over a nontrivial ring. -/
lemma affineTranslation_totalDegree {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ}
    (a : Fin n → R) (f : MvPolynomial (Fin n) R) :
    (affineTranslation R a f).totalDegree = f.totalDegree := by
  apply le_antisymm (affineTranslation_totalDegree_le a f)
  have hh := affineTranslation_totalDegree_le (-a) (affineTranslation R a f)
  have he : affineTranslation R (-a) (affineTranslation R a f) = f :=
    (affineTranslation R a).symm_apply_apply f
  rwa [he] at hh

/-- Affine translation commutes with mapping coefficients along a ring homomorphism `φ`, the
translation vector being mapped by `φ` as well. -/
lemma affineTranslation_map {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (φ : R →+* S) (a : Fin n → R) (f : MvPolynomial (Fin n) R) :
    MvPolynomial.map φ (affineTranslation R a f) =
      affineTranslation S (φ ∘ a) (MvPolynomial.map φ f) :=
  originShift_map φ a f

/-- Dehomogenizing at `X 0` intertwines the homogeneous translation
`Xⱼ₊₁ ↦ Xⱼ₊₁ + aⱼ X₀` with the affine translation `Xⱼ ↦ Xⱼ + aⱼ`. -/
lemma affineChart_homogeneousTranslation {R : Type*} [CommRing R] {n : ℕ}
    (a : Fin n → R) (f : MvPolynomial (Fin (n + 1)) R) :
    affineChart n (homogeneousTranslation R a f) = affineTranslation R a (affineChart n f) := by
  have he : (affineChart n).comp (homogeneousTranslation R a).toRingHom =
      (affineTranslation R a).toRingHom.comp (affineChart n) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [affineChart, homogeneousTranslation, homogeneousTranslationHom, affineTranslation]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i <;>
        simp [affineChart, homogeneousTranslation, homogeneousTranslationHom, affineTranslation]
  exact RingHom.congr_fun he f

end
end CCDN
