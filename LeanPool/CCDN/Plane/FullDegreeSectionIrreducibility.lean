/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Plane.FiniteFieldBadPlanes
import LeanPool.CCDN.ForMathlib.MvPolynomial
import LeanPool.CCDN.Plane.SectionBounds
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! An irreducible section retaining the full total degree forces the
original equation to be irreducible. Degree additivity prevents either
nonconstant ambient factor from disappearing under restriction. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private lemma polynomial_isUnit_of_nonzero_degree_zero {K σ : Type*} [Field K]
    (f : MvPolynomial σ K) (hf : f ≠ 0) (hd : f.totalDegree = 0) : IsUnit f := by
  by_contra hu
  exact (totalDegree_pos_of_ne_zero_of_not_isUnit hf hu).ne' hd

/-- A degree-nonincreasing polynomial ring homomorphism reflects irreducibility
at every equation whose full degree is retained. -/
theorem irreducible_of_full_degree_map {K σ τ : Type*} [Field K]
    (ψ : MvPolynomial σ K →+* MvPolynomial τ K)
    (hψ : ∀ g, (ψ g).totalDegree ≤ g.totalDegree)
    (f : MvPolynomial σ K) (hir : Irreducible (ψ f))
    (hdeg : (ψ f).totalDegree = f.totalDegree) : Irreducible f := by
  refine ⟨fun hu => hir.not_isUnit (hu.map ψ), ?_⟩
  intro a b he
  have he' : ψ f = ψ a * ψ b := by rw [he, map_mul]
  have ha : ψ a ≠ 0 := left_ne_zero_of_mul (he' ▸ hir.ne_zero)
  have hb : ψ b ≠ 0 := right_ne_zero_of_mul (he' ▸ hir.ne_zero)
  have ha0 : a ≠ 0 := by intro hz; exact ha (by rw [hz, map_zero])
  have hb0 : b ≠ 0 := by intro hz; exact hb (by rw [hz, map_zero])
  have ht := totalDegree_mul_of_isDomain ha0 hb0
  have ht' := totalDegree_mul_of_isDomain ha hb
  rw [← he] at ht
  rw [← he', hdeg] at ht'
  have hda := hψ a
  have hdb := hψ b
  rcases hir.isUnit_or_isUnit he' with hu | hu
  · left
    have hz := (isUnit_iff_totalDegree_of_isReduced.mp hu).2
    exact polynomial_isUnit_of_nonzero_degree_zero a ha0 (by omega)
  · right
    have hz := (isUnit_iff_totalDegree_of_isReduced.mp hu).2
    exact polynomial_isUnit_of_nonzero_degree_zero b hb0 (by omega)

/-- The ring homomorphism restricting a polynomial in the coordinates `σ` to the affine plane
`a + s • b + t • c` whose base point and directions are given by the parameters `v`, as a
polynomial in the plane coordinates `s` and `t`. -/
def planeSectionPolynomialHom {K σ : Type*} [CommRing K] (v : PlaneParameters σ → K) :
    MvPolynomial σ K →+* MvPolynomial (Fin 2) K :=
  (bivariatePolynomialEquiv K).symm.toRingHom.comp
    ((bivariateMap (eval v)).comp
      ((bivariatePolynomialEquiv _).toRingHom.comp (universalPlaneMap K σ).toRingHom))

/-- If the plane section of `f` at parameters `v` is irreducible and keeps the total degree of `f`,
then `f` is irreducible; the parameters `v` may be degenerate. -/
theorem irreducible_of_full_degree_planeSection {K σ : Type*} [Field K]
    (f : MvPolynomial σ K) (v : PlaneParameters σ → K)
    (hir : Irreducible (universalPlaneSection f v))
    (hdeg : bivariateTotalDegree (universalPlaneSection f v) = f.totalDegree) : Irreducible f := by
  apply irreducible_of_full_degree_map (planeSectionPolynomialHom v)
    (fun g => planeSectionPolynomial_totalDegree g v) f _ hdeg
  exact (MulEquiv.irreducible_iff (f := (bivariatePolynomialEquiv K).symm)).mpr hir

end
end CCDN
