/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.PolynomialPredicates
public import LeanPool.CCDN.Plane.FiniteFieldBadPlanes
import LeanPool.CCDN.Algebra.IntegerPolynomialAvoidance
import LeanPool.CCDN.Noether.ShearNormalization

/-!
# Specializations of universal plane sections

Evaluation of a universal section, including the three points obtained from the base point by
adding each direction. A nonzero universal witness certifies a geometrically irreducible plane
section in characteristic zero, and integer specialization can simultaneously avoid any
additional nonzero polynomial condition on the plane parameters.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Construct an integer plane specialization which is geometrically
 irreducible of full degree and avoids an additional algebraic condition.
 The parameter bound is independent of the equation's coefficient height. -/
theorem exists_integer_geometrically_good_plane_avoiding {σ : Type*} [Finite σ]
    (f : MvPolynomial (Option σ) ℤ)
    (hir : AbsolutelyIrreducible f)
    (hd : 0 < f.totalDegree)
    (P : MvPolynomial (PlaneParameters (Option σ)) ℤ) (hP : P ≠ 0) :
    ∃ v : PlaneParameters (Option σ) → ℤ,
      (∀ i, 0 ≤ v i ∧ v i ≤ 2 * f.totalDegree ^ 3 + P.totalDegree) ∧
      eval v P ≠ 0 ∧
      (bivariateMap (Int.castRingHom (AlgebraicClosure ℚ)) (universalPlaneSection f v)).natDegree =
        f.totalDegree ∧
      bivariateTotalDegree
          (bivariateMap (Int.castRingHom (AlgebraicClosure ℚ)) (universalPlaneSection f v)) =
        f.totalDegree ∧
      Irreducible (bivariateMap (Int.castRingHom (AlgebraicClosure ℚ))
        (universalPlaneSection f v)) := by
  classical
  let := Fintype.ofFinite σ
  obtain ⟨rows, cols, hW, hdegree⟩ := exists_integer_universalPlane_badWitness f hir hd
  let W := universalPlaneBadWitness f rows cols
  obtain ⟨v, hv, hvalue⟩ := exists_integer_grid_eval_ne_zero (W * P) (mul_ne_zero hW hP)
    (2 * f.totalDegree ^ 3 + P.totalDegree)
    ((totalDegree_mul W P).trans (Nat.add_le_add_right hdegree _))
  rw [eval_mul] at hvalue
  obtain ⟨hvW, hvP⟩ := mul_ne_zero_iff.mp hvalue
  let φ := (Int.castRingHom (AlgebraicClosure ℚ)).comp (eval v)
  have hwφ : φ W ≠ 0 := by
    simpa only [φ, RingHom.comp_apply, Int.coe_castRingHom, ne_eq, Int.cast_eq_zero] using hvW
  have hgood := universalPlaneBadWitness_good_specialization f hd (.of_charZero _) rows cols φ hwφ
  refine ⟨v, hv, hvP, ?_⟩
  simpa only [φ, bivariateMap_comp_apply, universalPlaneSection] using hgood

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

/-- Evaluate the outer coordinate at x and the inner coordinate at y. -/
def bivariateEval {K : Type*} [CommRing K] (x y : K) : Polynomial (Polynomial K) →+* K :=
  (Polynomial.evalRingHom x).comp (Polynomial.mapRingHom (Polynomial.evalRingHom y))

/-- Evaluating the universal plane section of `f` with parameters `v` at `(x, y)` gives `f` at the
point `a + x • b + y • c` of the plane with base point `a` and directions `b`, `c` given by `v`. -/
lemma universalPlaneSection_eval {K σ : Type*} [CommRing K]
    (f : MvPolynomial σ K) (v : PlaneParameters σ → K) (x y : K) :
    bivariateEval x y (universalPlaneSection f v) =
      eval (fun i => v (i,0) + v (i,1) * x + v (i,2) * y) f := by
  have he : (bivariateEval x y).comp
      ((bivariateMap (eval v)).comp
        ((bivariatePolynomialEquiv _).toRingHom.comp (universalPlaneMap K σ).toRingHom)) =
      eval (fun i => v (i,0) + v (i,1) * x + v (i,2) * y) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [bivariateEval, universalPlaneMap, bivariatePolynomialEquiv_C, bivariateMap]
    · intro i
      simp [bivariateEval, universalPlaneMap, bivariatePolynomialEquiv_C,
        bivariatePolynomialEquiv_X_zero, bivariatePolynomialEquiv_X_one, bivariateMap]
  exact RingHom.congr_fun he f

/-- The equivalence between plane parameters, a base point `a` with directions `b` and `c`, and
the three defining points `a`, `a + b` and `a + c` of the plane. -/
def planeTriplePointsEquiv {K σ : Type*} [CommRing K] :
    (PlaneParameters σ → K) ≃ (Fin 3 → σ → K) where
  toFun v := ![fun i => v (i,0), fun i => v (i,0) + v (i,1), fun i => v (i,0) + v (i,2)]
  invFun w := fun i => ![w 0 i.1, w 1 i.1 - w 0 i.1, w 2 i.1 - w 0 i.1] i.2
  left_inv v := by
    funext i
    rcases i with ⟨i,j⟩
    fin_cases j <;> simp
  right_inv w := by
    funext j i
    fin_cases j <;> simp

/-- A zero section contains all three defining points, including coincident
ones. This does not require the parameterization to be injective. -/
lemma zero_universalPlaneSection_three_points {K σ : Type*} [CommRing K]
    (f : MvPolynomial σ K) (v : PlaneParameters σ → K)
    (hv : universalPlaneSection f v = 0) (j : Fin 3) :
    eval (planeTriplePointsEquiv v j) f = 0 := by
  have h0 := universalPlaneSection_eval f v 0 0
  have h1 := universalPlaneSection_eval f v 1 0
  have h2 := universalPlaneSection_eval f v 0 1
  rw [hv, map_zero] at h0 h1 h2
  fin_cases j
  · simpa [planeTriplePointsEquiv] using h0.symm
  · simpa [planeTriplePointsEquiv] using h1.symm
  · simpa [planeTriplePointsEquiv] using h2.symm

end
end CCDN
