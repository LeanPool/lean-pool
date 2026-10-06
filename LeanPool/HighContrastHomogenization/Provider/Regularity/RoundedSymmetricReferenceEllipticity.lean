/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedSymmetricReferenceBounds

/-!
# High-contrast homogenization: Provider.Regularity.RoundedSymmetricReferenceEllipticity

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Ellipticity of the rounded symmetric reference

The rounded reference is not the identity.  Its source-level matrix sandwich
nevertheless gives the two coercivity inequalities required by
`IsEllipticMatrix`: the lower bound is read directly, while the upper bound is
reversed under matrix inversion.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ}

private theorem vecDot_matVecMul_le_of_matrix_le {A B : Mat d}
    (h : A ≤ B) (x : Vec d) :
    vecDot x (matVecMul A x) ≤ vecDot x (matVecMul B x) := by
  have hdiff : (B - A).PosSemidef := Matrix.le_iff.mp h
  have hx := hdiff.dotProduct_mulVec_nonneg x
  rw [Matrix.sub_mulVec, dotProduct_sub] at hx
  change x ⬝ᵥ A *ᵥ x ≤ x ⬝ᵥ B *ᵥ x
  simp only [star_trivial] at hx
  linarith only [hx]

private theorem vecDot_matVecMul_smul_one (c : ℝ) (x : Vec d) :
    vecDot x (matVecMul (c • (1 : Mat d)) x) = c * vecNormSq x := by
  have hone : matVecMul (1 : Mat d) x = x := by
    funext i
    simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]
  rw [smul_matVecMul, hone, vecDot_smul_right]
  rfl

private theorem scalar_mul_vecNormSq_le_of_smul_one_le {c : ℝ} {A : Mat d}
    (h : c • (1 : Mat d) ≤ A) (x : Vec d) :
    c * vecNormSq x ≤ vecDot x (matVecMul A x) := by
  have hquad := vecDot_matVecMul_le_of_matrix_le h x
  rw [vecDot_matVecMul_smul_one] at hquad
  exact hquad

/-- The rounded symmetric reference is positive definite at every point. -/
theorem roundedSymmetricReferenceCoefficient_posDef [NeZero d]
    (abar : Mat d) (hS : (symmPart abar).PosDef) (y : Vec d) :
    (roundedSymmetricReferenceCoefficient abar hS y).PosDef := by
  have hlower :=
    (roundedSymmetricReferenceCoefficient_order_bounds abar hS y).1
  have hscalar : ((99 / 100 : ℝ) • (1 : Mat d)).PosDef :=
    Matrix.PosDef.one.smul (by norm_num)
  exact posDef_of_posDef_le hscalar hlower

/-- The near-identity rounded reference has the source's explicit ellipticity
constants.  In particular, this does not identify it with the exact-root
identity coefficient. -/
theorem isEllipticMatrix_roundedSymmetricReferenceCoefficient [NeZero d]
    (abar : Mat d) (hS : (symmPart abar).PosDef) (y : Vec d) :
    IsEllipticMatrix (99 / 100 : ℝ) (101 / 100 : ℝ)
      (roundedSymmetricReferenceCoefficient abar hS y) := by
  let B : Mat d := roundedSymmetricReferenceCoefficient abar hS y
  obtain ⟨hlower, hupper⟩ :=
    roundedSymmetricReferenceCoefficient_order_bounds abar hS y
  have hB : B.PosDef := by
    simpa only [B] using
      roundedSymmetricReferenceCoefficient_posDef abar hS y
  have hupperPos : ((101 / 100 : ℝ) • (1 : Mat d)).PosDef :=
    Matrix.PosDef.one.smul (by norm_num)
  have hinvOrder : (100 / 101 : ℝ) • (1 : Mat d) ≤ B⁻¹ := by
    have h := inv_le_inv_of_le hB hupperPos hupper
    rw [inv_smul_of_isUnit (by norm_num : (101 / 100 : ℝ) ≠ 0)
      (by simp : IsUnit (1 : Mat d).det), inv_one] at h
    norm_num at h
    exact h
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · intro xi
    exact scalar_mul_vecNormSq_le_of_smul_one_le hlower xi
  · intro xi
    have hinvLower := scalar_mul_vecNormSq_le_of_smul_one_le hinvOrder xi
    have hconstant : (101 / 100 : ℝ)⁻¹ = 100 / 101 := by norm_num
    rw [hconstant]
    exact hinvLower

end

end HighContrast
end HCPolySupport
