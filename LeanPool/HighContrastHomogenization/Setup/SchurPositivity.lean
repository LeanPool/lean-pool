/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup.Contrast

/-!
# High-contrast homogenization: Setup.SchurPositivity

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Positivity of the Schur block and of the conjugated skew-corrected form

The reference text reads `|σ_*^{-1/2}(σ + (k - h)ᵗ σ_*⁻¹ (k - h))σ_*^{-1/2}|`,
the intrinsic contrast of the reference block, as the spectral norm of a
symmetric positive semidefinite matrix.  This file supplies that reading: on a
symmetric positive definite doubled block matrix `H`, the conjugated
skew-corrected form
`σ_*^{-1/2}(σ + (k - h)ᵗ σ_*⁻¹ (k - h))σ_*^{-1/2}` is symmetric and positive
semidefinite, for every skew parameter `h` — indeed for every `h` at all.

The substantive input is the positivity of the Schur block `σ`.  It comes from
the Schur complement identity: the doubled quadratic form of `H` evaluated at the
state `(p, k p)` built from the Schur skew block is exactly the quadratic form of
`σ` at `p`, so positive definiteness of `H` transfers to `σ`.
-/

namespace HCPolySupport
namespace HighContrast

open scoped Matrix

noncomputable section

variable {d : ℕ}

private theorem vecDot_sub_right (x y z : Vec d) :
    vecDot x (y - z) = vecDot x y - vecDot x z := by
  simp [vecDot, mul_sub, Finset.sum_sub_distrib]

private theorem matVecMul_neg_mat (M : Mat d) (x : Vec d) :
    matVecMul (-M) x = -matVecMul M x := by
  funext i
  simp [matVecMul]

private theorem sub_matVecMul (A B : Mat d) (x : Vec d) :
    matVecMul (A - B) x = matVecMul A x - matVecMul B x := by
  funext i
  simp [matVecMul, sub_mul, Finset.sum_sub_distrib]

private theorem matVecMul_one_left (x : Vec d) : matVecMul (1 : Mat d) x = x := by
  funext i
  simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]

/-- On real matrices, conjugate transpose agrees with transpose. -/
theorem conjTranspose_eq_matTranspose (A : Mat d) : Aᴴ = matTranspose A :=
  Matrix.conjTranspose_eq_transpose_of_trivial A

private theorem isHermitian_of_matTranspose_eq {A : Mat d}
    (h : matTranspose A = A) : A.IsHermitian := by
  show Aᴴ = A
  rw [conjTranspose_eq_matTranspose]
  exact h

/-! ## Symmetry of the blocks -/

/-- The upper-left block of a symmetric doubled block matrix is symmetric. -/
theorem matTranspose_upperLeft {H : BlockMat d} (hsymm : IsSymmetricBlockMat H) :
    matTranspose H.upperLeft = H.upperLeft := by
  ext i j
  exact hsymm (Sum.inl j) (Sum.inl i)

/-- The off-diagonal blocks of a symmetric doubled block matrix are transposes of
one another. -/
theorem upperRight_eq_matTranspose_lowerLeft {H : BlockMat d}
    (hsymm : IsSymmetricBlockMat H) :
    H.upperRight = matTranspose H.lowerLeft := by
  ext i j
  exact hsymm (Sum.inl i) (Sum.inr j)

/-! ## The Schur complement identity -/

/-- **The Schur complement identity.**  Evaluated at the state `(p, k p)` built
from the Schur skew block, the doubled quadratic form of a symmetric doubled
block matrix with invertible lower-right block is the quadratic form of its Schur
block `σ`. -/
theorem blockVecDot_blockMatVecMul_schurSkew {H : BlockMat d}
    (hsymm : IsSymmetricBlockMat H) (hdet : IsUnit H.lowerRight.det) (p : Vec d) :
    blockVecDot (p, matVecMul (schurSkew H) p)
        (blockMatVecMul H (p, matVecMul (schurSkew H) p)) =
      vecDot p (matVecMul (schurSigma H) p) := by
  have hUR : H.upperRight = matTranspose H.lowerLeft :=
    upperRight_eq_matTranspose_lowerLeft hsymm
  have hDD : H.lowerRight * H.lowerRight⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  set u : Vec d := matVecMul H.lowerLeft p with hu
  set v : Vec d := matVecMul H.lowerRight⁻¹ u with hv
  have hq : matVecMul (schurSkew H) p = -v := by
    rw [schurSkew, matVecMul_neg_mat, hv, hu, matVecMul_mul]
  have hDv : matVecMul H.lowerRight v = u := by
    rw [hv, matVecMul_mul, hDD, matVecMul_one_left]
  have hDnegv : matVecMul H.lowerRight (-v) = -u := by
    rw [matVecMul_neg, hDv]
  -- the three cross terms
  have hcross1 : vecDot p (matVecMul H.upperRight (-v)) = -vecDot v u := by
    rw [hUR, vecDot_matVecMul_transpose, ← hu, vecDot_neg_right, vecDot_comm]
  have hcross2 : vecDot (-v) (matVecMul H.lowerLeft p) = -vecDot v u := by
    rw [← hu, vecDot_neg_left]
  have hcross3 : vecDot (-v) (matVecMul H.lowerRight (-v)) = vecDot v u := by
    rw [hDnegv, vecDot_neg_left, vecDot_neg_right, neg_neg]
  -- the Schur block term
  have hsigma : vecDot p (matVecMul (schurSigma H) p) =
      vecDot p (matVecMul H.upperLeft p) - vecDot v u := by
    have hprod : matVecMul (matTranspose (schurSkew H) * H.lowerRight * schurSkew H) p =
        matVecMul (matTranspose (schurSkew H))
          (matVecMul H.lowerRight (matVecMul (schurSkew H) p)) := by
      rw [matVecMul_mul, matVecMul_mul]
    rw [schurSigma, sub_matVecMul, vecDot_sub_right, hprod, vecDot_matVecMul_transpose,
      hq, hDnegv, vecDot_neg_left, vecDot_neg_right, neg_neg]
  rw [hq]
  simp only [blockVecDot, blockMatVecMul, vecDot_add_right]
  rw [hcross1, hcross2, hcross3, hsigma]
  ring

/-! ## Positivity -/

/-- **The Schur block of a positive definite doubled block matrix is positive
semidefinite.** -/
theorem posSemidef_schurSigma {H : BlockMat d} (hsymm : IsSymmetricBlockMat H)
    (hpos : Book.Ch02.BlockPosDef H) : (schurSigma H).PosSemidef := by
  have hdet : IsUnit H.lowerRight.det := isUnit_det_lowerRight hpos
  have hherm : (schurSigma H).IsHermitian := by
    have hUL : H.upperLeft.IsHermitian :=
      isHermitian_of_matTranspose_eq (matTranspose_upperLeft hsymm)
    have hconj : ((schurSkew H)ᴴ * H.lowerRight * schurSkew H).IsHermitian :=
      Matrix.isHermitian_conjTranspose_mul_mul _ (isHermitian_lowerRight hsymm)
    rw [conjTranspose_eq_matTranspose] at hconj
    exact hUL.sub hconj
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm fun p => ?_
  show (0 : ℝ) ≤ vecDot p (matVecMul (schurSigma H) p)
  rw [← blockVecDot_blockMatVecMul_schurSkew hsymm hdet p]
  by_cases hp : p = 0
  · subst hp
    have hzero : matVecMul (schurSkew H) (0 : Vec d) = 0 := matVecMul_zero _
    rw [hzero]
    simp [blockVecDot, blockMatVecMul, matVecMul_zero, vecDot_zero_left]
  · exact le_of_lt (hpos _ fun hc => hp (congrArg Prod.fst hc))

/-- The skew-corrected Schur form of a symmetric positive definite doubled block
matrix is positive semidefinite, at every value of the skew parameter. -/
theorem posSemidef_skewCorrectedForm {H : BlockMat d} (hsymm : IsSymmetricBlockMat H)
    (hpos : Book.Ch02.BlockPosDef H) (h : Mat d) :
    (skewCorrectedForm H h).PosSemidef := by
  have hconj : (matTranspose (schurSkew H - h) * H.lowerRight * (schurSkew H - h)).PosSemidef := by
    have hc := (posSemidef_lowerRight hsymm hpos).conjTranspose_mul_mul_same (schurSkew H - h)
    rwa [conjTranspose_eq_matTranspose] at hc
  exact (posSemidef_schurSigma hsymm hpos).add hconj

/-- **The conjugated skew-corrected form is symmetric positive semidefinite.**
This is what makes `specBound` of it the spectral norm `|·|` written in the
intrinsic contrast of the reference block and in `e.Theta.m`. -/
theorem posSemidef_matSqrt_mul_skewCorrectedForm_mul {H : BlockMat d}
    (hsymm : IsSymmetricBlockMat H) (hpos : Book.Ch02.BlockPosDef H) (h : Mat d) :
    (matSqrt H.lowerRight * skewCorrectedForm H h * matSqrt H.lowerRight).PosSemidef := by
  have hR : (matSqrt H.lowerRight).PosSemidef :=
    (matSqrt_spec (posSemidef_lowerRight hsymm hpos)).1
  have hc := (posSemidef_skewCorrectedForm hsymm hpos h).conjTranspose_mul_mul_same
    (matSqrt H.lowerRight)
  rwa [hR.isHermitian] at hc

/-- The conjugated skew-corrected form is symmetric in the ambient encoding. -/
theorem matTranspose_matSqrt_mul_skewCorrectedForm_mul {H : BlockMat d}
    (hsymm : IsSymmetricBlockMat H) (hpos : Book.Ch02.BlockPosDef H) (h : Mat d) :
    matTranspose (matSqrt H.lowerRight * skewCorrectedForm H h * matSqrt H.lowerRight) =
      matSqrt H.lowerRight * skewCorrectedForm H h * matSqrt H.lowerRight := by
  have hherm :=
    (posSemidef_matSqrt_mul_skewCorrectedForm_mul hsymm hpos h).isHermitian.eq
  rwa [conjTranspose_eq_matTranspose] at hherm

end

end HighContrast
end HCPolySupport
