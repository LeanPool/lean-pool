/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileRowCarriers
public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormAdjointAlgebra
public import LeanPool.HighContrastHomogenization.Annealed.SchattenDefinedness

/-!
# High-contrast homogenization: Provider.Response.ProfileRowSchur

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Schur estimate for an all-earlier response row

The inverse square root of `schurSigmaStar` is the square root of the
lower-right block.  Together with the top-left block this gives the exact
factor-two estimate used by the response row.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02

open scoped Matrix

noncomputable section

variable {d : ℕ}

private theorem upperLeft_posSemidef {H : BlockMat d}
    (hsymm : IsSymmetricBlockMat H) (hpos : BlockPosDef H) :
    H.upperLeft.PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext i j
    simp only [Matrix.conjTranspose, RCLike.star_def, Matrix.map_apply,
      Matrix.transpose_apply, conj_trivial]
    simpa only [blockMatEntry] using hsymm (Sum.inl j) (Sum.inl i)
  · intro x
    by_cases hx : x = 0
    · subst hx
      simp
    · have hX : ((x, 0) : BlockVec d) ≠ 0 := by
        intro hzero
        exact hx (congrArg Prod.fst hzero)
      have hquad := (hpos ((x, 0) : BlockVec d) hX).le
      simpa only [star_trivial, ge_iff_le, blockVecDot, blockMatVecMul,
        matVecMul_zero, add_zero, vecDot_zero_left] using! hquad

private theorem vecNorm_matSqrt_sq_eq {M : Mat d} (hM : M.PosSemidef)
    (x : Vec d) :
    Book.Ch02.vecNorm (matVecMul (matSqrt M) x) ^ 2 =
      vecDot x (matVecMul M x) := by
  rw [Book.Ch02.vecNorm_sq_eq_vecNormSq]
  change vecDot (matVecMul (matSqrt M) x) (matVecMul (matSqrt M) x) = _
  calc
    vecDot (matVecMul (matSqrt M) x) (matVecMul (matSqrt M) x) =
        vecDot x
          (matVecMul (matTranspose (matSqrt M))
            (matVecMul (matSqrt M) x)) :=
      (vecDot_matVecMul_transpose x (matVecMul (matSqrt M) x)
        (matSqrt M)).symm
    _ = vecDot x (matVecMul M x) := by
      have hs : matTranspose (matSqrt M) = matSqrt M := by
        change Matrix.transpose (matSqrt M) = matSqrt M
        exact (isSymm_matSqrt M).eq
      rw [hs, matVecMul_mul, (matSqrt_spec hM).2]

private theorem blockVecDot_inl' (H : BlockMat d) (x : Vec d) :
    blockVecDot ((x, 0) : BlockVec d)
        (blockMatVecMul H ((x, 0) : BlockVec d)) =
      vecDot x (matVecMul H.upperLeft x) := by
  change vecDot x (matVecMul H.upperLeft x + matVecMul H.upperRight 0) +
      vecDot 0 (matVecMul H.lowerLeft x + matVecMul H.lowerRight 0) = _
  rw [matVecMul_zero, matVecMul_zero, add_zero, add_zero,
    vecDot_zero_left, add_zero]

theorem profileSchurLoad_nonneg (H : BlockMat d) (Pcen Qcen : Vec d) :
    0 ≤ profileSchurLoad H Pcen Qcen := by
  exact sq_nonneg _

/-- The Schur diagonal load is at most twice the sum of the two diagonal
quadratic forms. -/
theorem profileSchurLoad_le_two_mul_profileQuadraticLoad {H : BlockMat d}
    (hsymm : IsSymmetricBlockMat H) (hpos : BlockPosDef H)
    (Pcen Qcen : Vec d) :
    profileSchurLoad H Pcen Qcen ≤
      2 * profileQuadraticLoad H Pcen Qcen := by
  have hdet : IsUnit H.lowerRight.det := isUnit_det_lowerRight hpos
  have hstar : (schurSigmaStar H)⁻¹ = H.lowerRight :=
    schurSigmaStar_inv H hdet
  have hupper := vecNorm_matSqrt_sq_eq
    (upperLeft_posSemidef hsymm hpos) Pcen
  have hlower := vecNorm_matSqrt_sq_eq
    (M := (schurSigmaStar H)⁻¹) (by
      rw [hstar]
      exact posSemidef_lowerRight hsymm hpos) Qcen
  rw [hstar] at hlower
  rw [profileSchurLoad, profileQuadraticLoad, blockVecDot_inl',
    blockVecDot_inr, ← hupper, ← hlower]
  rw [hstar]
  have hadd (a b : ℝ) : (a + b) ^ 2 ≤ 2 * (b ^ 2 + a ^ 2) := by
    nlinarith only [sq_nonneg (a - b)]
  exact hadd _ _

/-- Coefficient transposition leaves both diagonal Schur carriers unchanged. -/
theorem profileSchurLoad_adjointBlock (H : BlockMat d)
    (Pcen Qcen : Vec d) :
    profileSchurLoad (profileAdjointBlock H) Pcen Qcen =
      profileSchurLoad H Pcen Qcen := by
  rw [profileAdjointBlock, blockMatMul_blockDiag_one_neg_one]
  rfl

/-- Coefficient transposition leaves the sum of diagonal quadratic forms
unchanged. -/
theorem profileQuadraticLoad_adjointBlock (H : BlockMat d)
    (Pcen Qcen : Vec d) :
    profileQuadraticLoad (profileAdjointBlock H) Pcen Qcen =
      profileQuadraticLoad H Pcen Qcen := by
  rw [profileQuadraticLoad, profileAdjointBlock,
    blockQuadratic_adjointSign_congr, blockQuadratic_adjointSign_congr,
    adjointSign_mulVec, adjointSign_mulVec]
  rw [profileQuadraticLoad]
  simp only [blockVecDot, blockMatVecMul, matVecMul_zero, add_zero,
    vecDot_zero_left, zero_add, matVecMul_neg, vecDot_neg_right,
    vecDot_neg_left, neg_neg, neg_zero]

end

end HCPolySupport.HighContrast.Response
