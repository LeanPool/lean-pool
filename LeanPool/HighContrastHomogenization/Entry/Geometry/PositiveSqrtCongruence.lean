/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Geometry.QuadraticForm
public import LeanPool.HighContrastHomogenization.Entry.Geometry.SpectralExtrema
public import LeanPool.HighContrastHomogenization.Entry.Setup.SchattenNorm
public import Mathlib.Analysis.Matrix.Order

/-!
# High-contrast homogenization: Entry.Geometry.PositiveSqrtCongruence

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Positive Sqrt Congruence

The positive square root `𝔪^{1/2}` of a positive definite matrix `𝔪`, and the congruence
identity that compares relative matrices in the Loewner order.  For a positive definite `𝔪`
the module proves that `CFC.sqrt 𝔪` is positive definite, that `CFC.sqrt 𝔪 * CFC.sqrt 𝔪 = 𝔪`,
and the two eigenvalue bounds of the print: `⟨v, 𝔪^{1/2} v⟩ ≤ |𝔪|^{1/2} |v|²` for the largest
eigenvalue and `|v|² ≤ |𝔪⁻¹|^{1/2} ⟨v, 𝔪^{1/2} v⟩` for the smallest.  These are the matrix
ingredients of `e.rounded.grid.bounds`.  The module then proves that congruence
`A ↦ Pᵀ A P` preserves the Loewner order and, for invertible `P`, reflects it as well, which
is the substitution that compares relative matrices.
-/

section
/-!
## The positive square root `𝔪^{1/2}`

The print's `𝔪^{1/2}` for a positive matrix `𝔪` is Mathlib's `CFC.sqrt 𝔪`, the positive
semidefinite square root from the continuous functional calculus (`Mathlib.Analysis.Matrix.Order`
sets this up on real matrices under `open scoped MatrixOrder`).

What `e.rounded.grid.bounds` needs about it is the two eigenvalue statements of the print,
"the unrounded matrix `|𝔪⁻¹|^{1/2} 𝔪^{1/2}` has smallest eigenvalue one and largest eigenvalue
`(|𝔪| |𝔪⁻¹|)^{1/2}`", in the form of two-sided bounds on the quadratic form of `𝔪^{1/2}`:

* `⟨v, 𝔪^{1/2} v⟩ ≤ |𝔪|^{1/2} |v|²`, and
* `|v|² ≤ |𝔪⁻¹|^{1/2} ⟨v, 𝔪^{1/2} v⟩`.

Both are proved without the spectral theorem: the first from `|𝔪^{1/2} v|² = ⟨v, 𝔪 v⟩`, the second
by the same argument applied to `(𝔪^{1/2})⁻¹`, whose square is `𝔪⁻¹`, together with
Cauchy–Schwarz for the positive form of `(𝔪^{1/2})⁻¹`.
-/

namespace HCPolySupport.HighContrast.Geometry

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {d : ℕ} {m : Mat d}

theorem posDef_sqrt (hm : Matrix.PosDef m) : Matrix.PosDef (CFC.sqrt m) :=
  (Matrix.isStrictlyPositive_iff_posDef.mpr hm).sqrt.posDef

theorem sqrt_mul_sqrt (hm : Matrix.PosDef m) : CFC.sqrt m * CFC.sqrt m = m :=
  CFC.sqrt_mul_sqrt_self m hm.posSemidef.nonneg

theorem transpose_sqrt (hm : Matrix.PosDef m) : (CFC.sqrt m)ᵀ = CFC.sqrt m :=
  transpose_eq_of_isHermitian (posDef_sqrt hm).posSemidef.isHermitian

theorem sqrt_apply_comm (hm : Matrix.PosDef m) (a b : Fin d) :
    CFC.sqrt m b a = CFC.sqrt m a b := by
  have h := congrFun (congrFun (transpose_sqrt hm) a) b
  rwa [transpose_apply] at h

theorem dotProduct_sqrt_nonneg (hm : Matrix.PosDef m) (v : Vec d) :
    0 ≤ v ⬝ᵥ (CFC.sqrt m *ᵥ v) :=
  dotProduct_mulVec_nonneg_of_posSemidef (posDef_sqrt hm).posSemidef v

/-- The largest eigenvalue of `𝔪^{1/2}` is at most `|𝔪|^{1/2}`: `⟨v, 𝔪^{1/2} v⟩ ≤ √‖𝔪‖ |v|²`. -/
theorem dotProduct_sqrt_le (hm : Matrix.PosDef m) (v : Vec d) :
    v ⬝ᵥ (CFC.sqrt m *ᵥ v) ≤ Real.sqrt ‖m‖ * vecNormSq v :=
  dotProduct_mulVec_le_sqrt_opNorm_sq (transpose_sqrt hm) (sqrt_mul_sqrt hm) v

/-- The smallest eigenvalue of `𝔪^{1/2}` is at least `|𝔪⁻¹|^{-1/2}`:
`|v|² ≤ √‖𝔪⁻¹‖ ⟨v, 𝔪^{1/2} v⟩`. -/
theorem vecNormSq_le_sqrt_opNorm_inv_mul_dotProduct_sqrt (hm : Matrix.PosDef m) (v : Vec d) :
    vecNormSq v ≤ Real.sqrt ‖m⁻¹‖ * (v ⬝ᵥ (CFC.sqrt m *ᵥ v)) := by
  set S := CFC.sqrt m with hSdef
  set R := S⁻¹ with hRdef
  have hS : Matrix.PosDef S := posDef_sqrt hm
  have hR : Matrix.PosDef R := hS.inv
  have hRt : Rᵀ = R := transpose_eq_of_isHermitian hR.posSemidef.isHermitian
  have hRpos : ∀ x : Vec d, 0 ≤ x ⬝ᵥ (R *ᵥ x) :=
    dotProduct_mulVec_nonneg_of_posSemidef hR.posSemidef
  have hRR : R * R = m⁻¹ := by
    rw [hRdef, ← Matrix.mul_inv_rev, hSdef, sqrt_mul_sqrt hm]
  have hRS : R * S = 1 :=
    Matrix.nonsing_inv_mul S ((Matrix.isUnit_iff_isUnit_det S).mp hS.isUnit)
  have hRb : ∀ u : Vec d, u ⬝ᵥ (R *ᵥ u) ≤ Real.sqrt ‖m⁻¹‖ * vecNormSq u :=
    dotProduct_mulVec_le_sqrt_opNorm_sq hRt hRR
  have hRw : R *ᵥ (S *ᵥ v) = v := by
    rw [mulVec_mulVec, hRS, one_mulVec]
  have hvSv : v ⬝ᵥ (S *ᵥ v) = (S *ᵥ v) ⬝ᵥ (R *ᵥ (S *ᵥ v)) := by
    calc v ⬝ᵥ (S *ᵥ v) = (R *ᵥ (S *ᵥ v)) ⬝ᵥ (S *ᵥ v) := by rw [hRw]
      _ = (S *ᵥ v) ⬝ᵥ (R *ᵥ (S *ᵥ v)) := dotProduct_comm _ _
  have hcs := sq_dotProduct_mulVec_le hRt hRpos (S *ᵥ v) (R *ᵥ (S *ᵥ v))
  have h1 : (S *ᵥ v) ⬝ᵥ (R *ᵥ (R *ᵥ (S *ᵥ v))) = vecNormSq v := by
    conv_rhs => rw [← hRw]
    rw [vecNormSq_mulVec_eq hRt, mulVec_mulVec]
  have h2 : (R *ᵥ (S *ᵥ v)) ⬝ᵥ (R *ᵥ (R *ᵥ (S *ᵥ v))) ≤ Real.sqrt ‖m⁻¹‖ * vecNormSq v := by
    rw [hRw]
    exact hRb v
  rw [h1] at hcs
  have hv := vecNormSq_nonneg v
  have hS0 : 0 ≤ v ⬝ᵥ (S *ᵥ v) := dotProduct_sqrt_nonneg hm v
  have hN := Real.sqrt_nonneg ‖m⁻¹‖
  rcases eq_or_lt_of_le hv with h0 | h0
  · rw [← h0]
    exact mul_nonneg hN hS0
  · have h3 : vecNormSq v * vecNormSq v
        ≤ (Real.sqrt ‖m⁻¹‖ * (v ⬝ᵥ (S *ᵥ v))) * vecNormSq v := by
      calc vecNormSq v * vecNormSq v = vecNormSq v ^ 2 := by ring
        _ ≤ ((S *ᵥ v) ⬝ᵥ (R *ᵥ (S *ᵥ v))) * ((R *ᵥ (S *ᵥ v)) ⬝ᵥ (R *ᵥ (R *ᵥ (S *ᵥ v)))) :=
            hcs
        _ ≤ (v ⬝ᵥ (S *ᵥ v)) * (Real.sqrt ‖m⁻¹‖ * vecNormSq v) := by
            rw [hvSv]
            exact mul_le_mul_of_nonneg_left h2 (hRpos _)
        _ = (Real.sqrt ‖m⁻¹‖ * (v ⬝ᵥ (S *ᵥ v))) * vecNormSq v := by ring
    exact le_of_mul_le_mul_right h3 h0

end HCPolySupport.HighContrast.Geometry
end

section
/-!
## Congruence for the Loewner order

This file proves the quadratic-form congruence layer needed to compare the
relative matrix `m₀^{-1/2} m₁ m₀^{-1/2}` with the `MatLoewnerLE`
thresholds.  The congruence is purely by substitution in the quadratic form;
no commutativity between the two endpoint matrices is used.
-/

open HCPolySupport.HighContrast (matSqrt matSqrt_spec)
namespace HCPolySupport.HighContrast.Geometry

open Matrix
open scoped MatrixOrder

noncomputable section

variable {d : ℕ}

private theorem quadForm_congr (A P : Mat d) (x : Vec d) :
    vecDot x (matVecMul (matTranspose P * A * P) x) =
      vecDot (matVecMul P x) (matVecMul A (matVecMul P x)) := by
  rw [← matVecMul_mul (matTranspose P * A) P x]
  rw [← matVecMul_mul (matTranspose P) A (matVecMul P x)]
  rw [vecDot_matVecMul_transpose]

/-- Congruence preserves the Loewner order. -/
theorem matLoewnerLE_congr {A B P : Mat d} (h : MatLoewnerLE A B) :
    MatLoewnerLE (matTranspose P * A * P) (matTranspose P * B * P) := by
  intro x
  simpa [quadForm_congr] using h (matVecMul P x)

/-- Invertible congruence reflects and preserves the Loewner order. -/
theorem matLoewnerLE_congr_iff_of_isUnit_det {A B P : Mat d} (hP : IsUnit P.det) :
    MatLoewnerLE A B ↔
      MatLoewnerLE (matTranspose P * A * P) (matTranspose P * B * P) := by
  constructor
  · exact matLoewnerLE_congr
  · intro h y
    have hsurj : Function.Surjective (matVecMul P) := by
      simpa [matVecMul] using!
        (Matrix.mulVec_surjective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det P).mpr hP))
    obtain ⟨x, rfl⟩ := hsurj y
    simpa [quadForm_congr] using h x

/-- The square root of the inverse of a positive matrix is positive definite. -/
theorem matSqrt_inv_posDef {m : Mat d} (hm : m.PosDef) : (matSqrt m⁻¹).PosDef := by
  rw [matSqrt_eq_cfc_sqrt hm.inv.posSemidef]
  exact posDef_sqrt hm.inv

/-- The inverse square-root congruence sends a positive matrix to the identity. -/
theorem matSqrt_inv_mul_self_mul_matSqrt_inv {m : Mat d} (hm : m.PosDef) :
    matSqrt m⁻¹ * m * matSqrt m⁻¹ = 1 := by
  let S : Mat d := matSqrt m⁻¹
  have hSS : S * S = m⁻¹ := (matSqrt_spec hm.inv.posSemidef).2
  have hmDet : IsUnit m.det := (Matrix.isUnit_iff_isUnit_det m).mp hm.isUnit
  have hright : S * (S * m) = 1 := by
    rw [← mul_assoc, hSS, Matrix.nonsing_inv_mul m hmDet]
  have hSinv : S⁻¹ = S * m := Matrix.inv_eq_right_inv hright
  have hSDet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp (matSqrt_inv_posDef hm).isUnit
  calc
    S * m * S = S⁻¹ * S := by rw [hSinv]
    _ = 1 := Matrix.nonsing_inv_mul S hSDet

end

end HCPolySupport.HighContrast.Geometry
end
