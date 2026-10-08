/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup.Contrast
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Order.Compact
public import LeanPool.HighContrastHomogenization.Setup.Attainment
public import LeanPool.HighContrastHomogenization.Setup.BlockAlgebra
public import LeanPool.HighContrastHomogenization.Setup.SpectralBound
public import LeanPool.HighContrastHomogenization.Geometry.AspectRatioMonotone

/-!
# High-contrast homogenization: Entry.Analysis.ContrastOrder

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Monotonicity of the intrinsic contrast in the Loewner order

The intrinsic contrast of `e.Theta.m` is the infimum over skew `h` of the scalings `t` with
`σ + (k - h)ᵗ σ_*⁻¹ (k - h) ≤ t σ_*`.  Both sides of this comparison are monotone in the
doubled block matrix: the quadratic form of the left side at `e` is the doubled quadratic
form at the block vector `(e, h e)`, and `σ_*` is the inverse of the lower-right block,
which is antitone in the Loewner order.  Hence a Loewner comparison `A ≤ B` of two symmetric
positive definite doubled block matrices forces `Θ(A) ≤ Θ(B)`, with the minimizing skew
matrix of `B` admissible for `A`.
-/

open HCPolySupport.HighContrast (IsSkewMat blockContrast blockContrast_le blockContrast_nonneg
  exists_coercivity_of_quadratic_pos exists_isSkewMat_matLoewnerLE_sInf_smul
  isUnit_det_lowerRight matLoewnerLE_lowerRight_of_blockMatLoewnerLE posDef_lowerRight
  quadratic_pos_lowerRight quadratic_pos_schurSigmaStar schurSigma schurSigmaStar schurSkew
  skewCorrectedForm)
namespace HCPolySupport.HighContrast

noncomputable section

variable {d : ℕ}

/-! ## Vector algebra -/

private theorem vecDot_sub_right (x y z : Vec d) :
    vecDot x (y - z) = vecDot x y - vecDot x z := by
  rw [sub_eq_add_neg, vecDot_add_right, vecDot_neg_right, sub_eq_add_neg]

private theorem vecDot_sub_left (x y z : Vec d) :
    vecDot (x - y) z = vecDot x z - vecDot y z := by
  rw [sub_eq_add_neg, vecDot_add_left, vecDot_neg_left, sub_eq_add_neg]

private theorem matVecMul_sub (A : Mat d) (x y : Vec d) :
    matVecMul A (x - y) = matVecMul A x - matVecMul A y := by
  rw [sub_eq_add_neg, matVecMul_add, matVecMul_neg, sub_eq_add_neg]

private theorem matVecMul_one (x : Vec d) : matVecMul (1 : Mat d) x = x := by
  funext i
  simp [matVecMul, Matrix.one_apply]

private theorem vecDot_matVecMul_smul (t : ℝ) (A : Mat d) (x : Vec d) :
    vecDot x (matVecMul (t • A) x) = t * vecDot x (matVecMul A x) := by
  rw [smul_matVecMul, vecDot_smul_right]

/-! ## Block symmetry -/

private theorem matTranspose_lowerRight {H : BlockMat d} (hsymm : IsSymmetricBlockMat H) :
    matTranspose H.lowerRight = H.lowerRight := by
  ext i j
  exact hsymm (Sum.inr j) (Sum.inr i)

private theorem matTranspose_lowerLeft {H : BlockMat d} (hsymm : IsSymmetricBlockMat H) :
    matTranspose H.lowerLeft = H.upperRight := by
  ext i j
  exact hsymm (Sum.inr j) (Sum.inl i)

/-- The lower-left block is `-σ_*⁻¹ k`. -/
private theorem lowerRight_mul_schurSkew {H : BlockMat d} (hdet : IsUnit H.lowerRight.det) :
    H.lowerRight * schurSkew H = -H.lowerLeft := by
  rw [schurSkew, Matrix.mul_neg, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet,
    Matrix.one_mul]

/-! ## The skew-corrected form as a doubled quadratic form -/

/-! ## Order consequences of a Loewner comparison -/

/-- Positivity passes up the doubled Loewner order. -/
theorem blockPosDef_of_blockMatLoewnerLE {A B : BlockMat d}
    (hApos : Book.Ch02.BlockPosDef A) (hAB : BlockMatLoewnerLE A B) :
    Book.Ch02.BlockPosDef B := fun X hX => by
  have h1 := hApos X hX
  have h2 := hAB X
  linarith only [h1, h2]

/-- Completing the square: the inverse quadratic form dominates every affine-quadratic test
`2 x ⬝ y - y ⬝ N y`, with defect the quadratic form of `N` at `y - N⁻¹ x`. -/
private theorem inv_quadratic_sub_test {N : Mat d} (hN : N.PosDef) (x y : Vec d) :
    vecDot x (matVecMul N⁻¹ x) - (2 * vecDot x y - vecDot y (matVecMul N y)) =
      vecDot (y - matVecMul N⁻¹ x) (matVecMul N (y - matVecMul N⁻¹ x)) := by
  have hdet : IsUnit N.det := (Matrix.isUnit_iff_isUnit_det N).1 hN.isUnit
  have hNsymm : matTranspose N = N := by
    have hH : Matrix.conjTranspose N = N := hN.isHermitian.eq
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hH
    exact hH
  set z := matVecMul N⁻¹ x with hz
  have hNz : matVecMul N z = x := by
    rw [hz, matVecMul_mul, Matrix.mul_nonsing_inv N hdet, matVecMul_one]
  have hsym : vecDot z (matVecMul N y) = vecDot x y := by
    have := vecDot_matVecMul_transpose z y N
    rwa [hNsymm, hNz] at this
  rw [matVecMul_sub, vecDot_sub_left, vecDot_sub_right, vecDot_sub_right, hNz, hsym,
    vecDot_comm y x, vecDot_comm z x]
  ring

/-- **Antitonicity of the inverse.**  On positive definite matrices the Loewner order is
reversed by inversion. -/
theorem matLoewnerLE_inv_of_matLoewnerLE {L M : Mat d} (hL : L.PosDef) (hM : M.PosDef)
    (hLM : MatLoewnerLE L M) : MatLoewnerLE M⁻¹ L⁻¹ := fun x => by
  set y := matVecMul M⁻¹ x with hy
  have h1 : vecDot x (matVecMul M⁻¹ x) = 2 * vecDot x y - vecDot y (matVecMul M y) := by
    have h := inv_quadratic_sub_test hM x y
    rw [← hy, sub_self, matVecMul_zero, vecDot_zero_left] at h
    linarith only [h]
  have h2 := inv_quadratic_sub_test hL x y
  have h3 : 0 ≤ vecDot (y - matVecMul L⁻¹ x) (matVecMul L (y - matVecMul L⁻¹ x)) := by
    have h := hL.posSemidef.dotProduct_mulVec_nonneg (y - matVecMul L⁻¹ x)
    simpa [star_trivial, dotProduct, Matrix.mulVec, vecDot, matVecMul] using h
  have h4 := hLM y
  linarith only [h1, h2, h3, h4]

/-- The Schur block `σ_*` is antitone in the doubled Loewner order: `A ≤ B` gives
`σ_*(B) ≤ σ_*(A)`. -/
theorem matLoewnerLE_schurSigmaStar_of_blockMatLoewnerLE {A B : BlockMat d}
    (hAsymm : IsSymmetricBlockMat A) (hApos : Book.Ch02.BlockPosDef A)
    (hBsymm : IsSymmetricBlockMat B) (hAB : BlockMatLoewnerLE A B) :
    MatLoewnerLE (schurSigmaStar B) (schurSigmaStar A) :=
  matLoewnerLE_inv_of_matLoewnerLE (posDef_lowerRight hAsymm hApos)
    (posDef_lowerRight hBsymm (blockPosDef_of_blockMatLoewnerLE hApos hAB))
    (matLoewnerLE_lowerRight_of_blockMatLoewnerLE hAB)

/-- The intrinsic contrast of a symmetric positive definite doubled block matrix is itself an
admissible Loewner scaling: some skew `h` realizes it. -/
theorem exists_isSkewMat_matLoewnerLE_blockContrast_smul {H : BlockMat d}
    (hsymm : IsSymmetricBlockMat H) (hpos : Book.Ch02.BlockPosDef H) :
    ∃ h : Mat d, IsSkewMat h ∧
      MatLoewnerLE (skewCorrectedForm H h) (blockContrast H • schurSigmaStar H) :=
  exists_isSkewMat_matLoewnerLE_sInf_smul (quadratic_pos_lowerRight hpos)
    (exists_coercivity_of_quadratic_pos (quadratic_pos_schurSigmaStar hsymm hpos))

/-! ## Monotonicity of the intrinsic contrast -/

/-- **Monotonicity of the intrinsic contrast.**  If `A ≤ B` in the doubled Loewner order,
with `A` symmetric positive definite and `B` symmetric, then `Θ(A) ≤ Θ(B)`: the skew matrix
realizing `Θ(B)` is admissible for `A` at the same scaling, because the skew-corrected form
of `A` at `(e, h e)` lies below that of `B`, while `σ_*(B) ≤ σ_*(A)`. -/
theorem blockContrast_le_of_blockMatLoewnerLE {A B : BlockMat d}
    (hAsymm : IsSymmetricBlockMat A) (hApos : Book.Ch02.BlockPosDef A)
    (hBsymm : IsSymmetricBlockMat B) (hAB : BlockMatLoewnerLE A B) :
    blockContrast A ≤ blockContrast B := by
  have hBpos := blockPosDef_of_blockMatLoewnerLE hApos hAB
  obtain ⟨h, hskew, hle⟩ := exists_isSkewMat_matLoewnerLE_blockContrast_smul hBsymm hBpos
  have hstar := matLoewnerLE_schurSigmaStar_of_blockMatLoewnerLE hAsymm hApos hBsymm hAB
  refine blockContrast_le (blockContrast_nonneg B) hskew fun e => ?_
  change (1 / 2 : ℝ) * vecDot e (matVecMul (skewCorrectedForm A h) e) ≤
    (1 / 2 : ℝ) * vecDot e (matVecMul (blockContrast B • schurSigmaStar A) e)
  have hA := vecDot_matVecMul_skewCorrectedForm hAsymm (isUnit_det_lowerRight hApos) h e
  have hB := vecDot_matVecMul_skewCorrectedForm hBsymm (isUnit_det_lowerRight hBpos) h e
  have h1 := hAB (e, matVecMul h e)
  have h2 := hle e
  have h3 := hstar e
  rw [vecDot_matVecMul_smul] at h2 ⊢
  have h4 : blockContrast B * vecDot e (matVecMul (schurSigmaStar B) e) ≤
      blockContrast B * vecDot e (matVecMul (schurSigmaStar A) e) :=
    mul_le_mul_of_nonneg_left (by linarith only [h3]) (blockContrast_nonneg B)
  linarith only [hA, hB, h1, h2, h4]

end

end HCPolySupport.HighContrast
