/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Plane.FiniteFieldConstants
public import LeanPool.CCDN.Plane.ParameterIncidence
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Analysis.Real.Sqrt
import LeanPool.CCDN.AuxiliaryPolynomial.PlaneBadPrimes
import LeanPool.CCDN.Noether.ShearNormalization
import LeanPool.CCDN.Plane.CurveCount
import LeanPool.CCDN.Plane.FiniteFieldZeroPlanes

/-! Section-point bounds in the good, nonzero and unrestricted cases.
The good-section bound uses the proved Stepanov theorem over the prime field. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Evaluating the nested-polynomial form of a bivariate polynomial `f` at `(t 0, t 1)` agrees
with evaluating `f` at `t`. -/
lemma bivariateEval_equiv {K : Type*} [CommRing K]
    (f : MvPolynomial (Fin 2) K) (t : Fin 2 → K) :
    bivariateEval (t 0) (t 1) (bivariatePolynomialEquiv K f) = eval t f := by
  have he : (bivariateEval (t 0) (t 1)).comp (bivariatePolynomialEquiv K).toRingHom = eval t := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [bivariateEval, bivariatePolynomialEquiv_C]
    · intro i
      fin_cases i <;> simp [bivariateEval,
        bivariatePolynomialEquiv_X_zero, bivariatePolynomialEquiv_X_one]
  exact RingHom.congr_fun he f

/-- The plane section `universalPlaneSection f v` as a polynomial in two variables
(`MvPolynomial (Fin 2)`), the presentation used by point counting. -/
def planeSectionPolynomial {K σ : Type*} [CommRing K]
    (f : MvPolynomial σ K) (v : PlaneParameters σ → K) : MvPolynomial (Fin 2) K :=
  (bivariatePolynomialEquiv K).symm (universalPlaneSection f v)

/-- A plane section of `f` has total degree at most that of `f`. -/
lemma planeSectionPolynomial_totalDegree {K σ : Type*} [CommRing K]
    (f : MvPolynomial σ K) (v : PlaneParameters σ → K) :
    (planeSectionPolynomial f v).totalDegree ≤ f.totalDegree :=
  universalPlanePolynomial_specialization_totalDegree f (eval v)

private lemma planeSectionPoints_card_eq {K σ : Type*} [CommRing K]
    (f : MvPolynomial σ K) (v : PlaneParameters σ → K) :
    Nat.card (PlaneSectionPoints f v) =
      Nat.card {t : Fin 2 → K // eval t (planeSectionPolynomial f v) = 0} := by
  have he (t : Fin 2 → K) : eval t (planeSectionPolynomial f v) =
      bivariateEval (t 0) (t 1) (universalPlaneSection f v) := by
    rw [← bivariateEval_equiv, planeSectionPolynomial, AlgEquiv.apply_symm_apply]
  apply Nat.card_congr
  exact { toFun := fun t => ⟨t.val, by rw [he]; exact t.property⟩
          invFun := fun t => ⟨t.val, by rw [← he]; exact t.property⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }

/-- The number of points of a plane section over a finite ring `K` is at most `|K| ^ 2`. -/
lemma planeSectionPoints_card_le_square {K σ : Type*} [CommRing K] [Fintype K]
    (f : MvPolynomial σ K) (v : PlaneParameters σ → K) :
    Nat.card (PlaneSectionPoints f v) ≤ Fintype.card K ^ 2 := by
  have h := Nat.card_le_card_of_injective (fun t : PlaneSectionPoints f v => t.val)
    Subtype.val_injective
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin] using h

/-- A nonzero plane section of `f` over a finite field `K` has at most `deg f * |K|` points. -/
lemma planeSectionPoints_card_le_degree_mul_card {K σ : Type*} [Field K] [Fintype K]
    (f : MvPolynomial σ K) (v : PlaneParameters σ → K)
    (hv : universalPlaneSection f v ≠ 0) :
    Nat.card (PlaneSectionPoints f v) ≤ f.totalDegree * Fintype.card K := by
  have hg : planeSectionPolynomial f v ≠ 0 := by
    intro hz
    apply hv
    have h := congrArg (bivariatePolynomialEquiv K) hz
    simpa only [planeSectionPolynomial, AlgEquiv.apply_symm_apply, map_zero] using h
  rw [planeSectionPoints_card_eq]
  have h := finite_field_polynomial_zeros_card (planeSectionPolynomial f v) hg
  simp only [Fintype.card_fin, Nat.reduceSub, pow_one] at h
  exact h.trans (Nat.mul_le_mul_right _ (planeSectionPolynomial_totalDegree f v))

/-- A plane section that is absolutely irreducible over `𝔽_p`, for `p > 27 d⁴`, has at most
`p + 161 d² √p` points. -/
lemma planeSectionPoints_card_le_add_mul_sqrt {σ : Type*}
    (p : ℕ) [Fact p.Prime] (f : MvPolynomial σ (ZMod p))
    (v : PlaneParameters σ → ZMod p)
    (hir : Irreducible (bivariateMap (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))
      (universalPlaneSection f v)))
    (hsize : stepanovThreshold (f.totalDegree : ℝ) < p) :
    (Nat.card (PlaneSectionPoints f v) : ℝ) ≤
      p + planeResidueConstant * (f.totalDegree : ℝ) ^ 2 * Real.sqrt p := by
  classical
  let g := planeSectionPolynomial f v
  have hg : Irreducible g := by
    apply mvPolynomial_irreducible_of_field_map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))
    apply (MulEquiv.irreducible_iff (f := bivariatePolynomialEquiv (AlgebraicClosure (ZMod p)))).mp
    rw [← bivariatePolynomialEquiv_map]
    simpa only [g, planeSectionPolynomial, AlgEquiv.apply_symm_apply] using hir
  have hd : g.totalDegree ≤ f.totalDegree := planeSectionPolynomial_totalDegree f v
  have hs : stepanovThreshold (g.totalDegree : ℝ) < p := by
    apply lt_of_le_of_lt _ hsize
    gcongr
  let S := {t : Fin 2 → ZMod p // eval t g = 0}
  have h := plane_finite_field_card_bound p g hg hs (fun t : S => t.val)
    Subtype.val_injective (fun t => t.property)
  rw [planeSectionPoints_card_eq, Nat.card_eq_fintype_card]
  apply h.trans
  gcongr
  exact planeResidueConstant_pos.le

end
end CCDN
