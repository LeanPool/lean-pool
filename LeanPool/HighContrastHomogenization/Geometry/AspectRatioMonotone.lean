/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Geometry.AspectRatioOrder
public import LeanPool.HighContrastHomogenization.Setup.SchurPositivity

/-!
# High-contrast homogenization: Geometry.AspectRatioMonotone

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Monotonicity of the reference aspect ratio

The aspect ratio `Π` of `e.reference.aspect.ratio` is monotone for the quadratic
form order on symmetric positive definite doubled blocks: if `A ≤ E` then
`Π(A) ≤ Π(E)`.

Both factors of `Π = Λ_0 |σ_{*,0}^{-1}|` are monotone, for different reasons.
The spectral bound of the lower-right block is monotone because the doubled
order restricts to the lower-right corner along the vectors `(0, q)`.

The constant `Λ_0` is monotone because of a slice identity: at a fixed `h`, the
skew-corrected form of `e.reference.aspect.ratio` is the doubled quadratic form
evaluated on the graph of `h`,

`p · (σ + (k - h)ᵗ σ_*⁻¹ (k - h)) p = (p, h p) · H (p, h p)`,

which is checked by expanding the Schur parametrization into
`σ + (k - h)ᵗ σ_*⁻¹ (k - h) = H₁₁ + H₁₂ h + hᵗ H₂₁ + hᵗ H₂₂ h`.  So a doubled
inequality between blocks gives, at every fixed `h`, an inequality of
skew-corrected forms, and the defining infima are then compared term by term.
-/

namespace HCPolySupport
namespace HighContrast

noncomputable section

variable {d : ℕ}

private theorem vecDot_matVecMul_conj (D M : Mat d) (x : Vec d) :
    vecDot x (matVecMul (matTranspose D * M * D) x) =
      vecDot (matVecMul D x) (matVecMul M (matVecMul D x)) := by
  rw [mul_assoc, ← matVecMul_mul, vecDot_matVecMul_transpose, matVecMul_mul]

private theorem bigLambdaRef_eq_sInf_set (E : BlockMat d) :
    bigLambdaRef E = sInf {t : ℝ | 0 ≤ t ∧ ∃ h : Mat d, IsSkewMat h ∧
      MatLoewnerLE (skewCorrectedForm E h) (t • (1 : Mat d))} := rfl

/-! ## The slice identity -/

/-- The skew-corrected form of `e.reference.aspect.ratio` expanded in the four
corners: `σ + (k - h)ᵗ σ_*⁻¹ (k - h) = H₁₁ + H₁₂ h + hᵗ H₂₁ + hᵗ H₂₂ h`.  The
Schur relations `H₂₂ k = -H₂₁` and `kᵗ H₂₂ = -H₁₂` cancel every term carrying
the Schur skew block `k`. -/
theorem skewCorrectedForm_eq_of_isSymmetricBlockMat {H : BlockMat d}
    (hsymm : IsSymmetricBlockMat H) (hdet : IsUnit H.lowerRight.det) (h : Mat d) :
    skewCorrectedForm H h =
      H.upperLeft + H.upperRight * h + matTranspose h * H.lowerLeft
        + matTranspose h * H.lowerRight * h := by
  have hRsymm : matTranspose H.lowerRight = H.lowerRight := by
    ext i j
    exact hsymm (Sum.inr j) (Sum.inr i)
  have hUR : H.upperRight = matTranspose H.lowerLeft :=
    upperRight_eq_matTranspose_lowerLeft hsymm
  have hRk : H.lowerRight * schurSkew H = -H.lowerLeft := by
    rw [schurSkew, Matrix.mul_neg, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet,
      Matrix.one_mul]
  have hkR : matTranspose (schurSkew H) * H.lowerRight = -H.upperRight := by
    have hT := congrArg matTranspose hRk
    rw [show matTranspose (H.lowerRight * schurSkew H)
        = matTranspose (schurSkew H) * matTranspose H.lowerRight from
      Matrix.transpose_mul _ _, hRsymm,
      show matTranspose (-H.lowerLeft) = -matTranspose H.lowerLeft from
        Matrix.transpose_neg _, ← hUR] at hT
    exact hT
  have hhRk : matTranspose h * H.lowerRight * schurSkew H
      = -(matTranspose h * H.lowerLeft) := by
    rw [Matrix.mul_assoc, hRk, Matrix.mul_neg]
  rw [skewCorrectedForm, schurSigma,
    show matTranspose (schurSkew H - h)
        = matTranspose (schurSkew H) - matTranspose h from Matrix.transpose_sub _ _]
  rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hkR, hhRk]
  simp only [Matrix.neg_mul]
  abel

/-- **The slice identity.**  The quadratic form of the skew-corrected form at
`p` is the doubled quadratic form of the block at the vector `(p, h p)`. -/
theorem vecDot_matVecMul_skewCorrectedForm {H : BlockMat d}
    (hsymm : IsSymmetricBlockMat H) (hdet : IsUnit H.lowerRight.det) (h : Mat d)
    (p : Vec d) :
    vecDot p (matVecMul (skewCorrectedForm H h) p) =
      blockVecDot (p, matVecMul h p) (blockMatVecMul H (p, matVecMul h p)) := by
  rw [skewCorrectedForm_eq_of_isSymmetricBlockMat hsymm hdet h]
  have e1 : vecDot p (matVecMul (H.upperRight * h) p)
      = vecDot p (matVecMul H.upperRight (matVecMul h p)) := by
    rw [matVecMul_mul]
  have e2 : vecDot p (matVecMul (matTranspose h * H.lowerLeft) p)
      = vecDot (matVecMul h p) (matVecMul H.lowerLeft p) := by
    rw [← matVecMul_mul, vecDot_matVecMul_transpose]
  have e3 : vecDot p (matVecMul (matTranspose h * H.lowerRight * h) p)
      = vecDot (matVecMul h p) (matVecMul H.lowerRight (matVecMul h p)) :=
    vecDot_matVecMul_conj _ _ _
  show _ = vecDot p (matVecMul H.upperLeft p + matVecMul H.upperRight (matVecMul h p))
      + vecDot (matVecMul h p) (matVecMul H.lowerLeft p
        + matVecMul H.lowerRight (matVecMul h p))
  simp only [add_matVecMul, vecDot_add_right]
  rw [e1, e2, e3]
  ring

/-! ## Monotonicity of the two factors -/

/-- The doubled order restricts to the lower-right corner. -/
theorem matLoewnerLE_lowerRight_of_blockMatLoewnerLE {A E : BlockMat d}
    (hle : BlockMatLoewnerLE A E) : MatLoewnerLE A.lowerRight E.lowerRight := by
  intro q
  have hq := hle ((0 : Vec d), q)
  rwa [blockVecDot_inr, blockVecDot_inr] at hq

/-- At a fixed skew parameter the skew-corrected form is monotone in the block,
by the slice identity. -/
theorem matLoewnerLE_skewCorrectedForm_of_blockMatLoewnerLE {A E : BlockMat d}
    (hAsymm : IsSymmetricBlockMat A) (hApos : Book.Ch02.BlockPosDef A)
    (hEsymm : IsSymmetricBlockMat E) (hEpos : Book.Ch02.BlockPosDef E)
    (hle : BlockMatLoewnerLE A E) (h : Mat d) :
    MatLoewnerLE (skewCorrectedForm A h) (skewCorrectedForm E h) := by
  intro p
  rw [vecDot_matVecMul_skewCorrectedForm hAsymm (isUnit_det_lowerRight hApos),
    vecDot_matVecMul_skewCorrectedForm hEsymm (isUnit_det_lowerRight hEpos)]
  exact hle (p, matVecMul h p)

/-- The reference constant `Λ_0` is monotone: the defining set of thresholds only
grows as the block decreases. -/
theorem bigLambdaRef_mono {A E : BlockMat d}
    (hAsymm : IsSymmetricBlockMat A) (hApos : Book.Ch02.BlockPosDef A)
    (hEsymm : IsSymmetricBlockMat E) (hEpos : Book.Ch02.BlockPosDef E)
    (hle : BlockMatLoewnerLE A E) : bigLambdaRef A ≤ bigLambdaRef E := by
  rw [bigLambdaRef_eq_sInf_set, bigLambdaRef_eq_sInf_set]
  refine csInf_le_csInf ⟨0, fun t ht => ht.1⟩ ?_ ?_
  · obtain ⟨b, hb0, hb⟩ := exists_matLoewnerLE_smul_one (skewCorrectedForm E 0)
    exact ⟨b, hb0, 0, isSkewMat_zero, hb⟩
  · rintro t ⟨ht, h, hskew, hlet⟩
    exact ⟨ht, h, hskew,
      (matLoewnerLE_skewCorrectedForm_of_blockMatLoewnerLE hAsymm hApos hEsymm hEpos
        hle h).trans hlet⟩

/-! ## The conclusion -/

/-- **The aspect ratio is monotone** for the quadratic form order on symmetric
positive definite doubled blocks. -/
theorem aspectRatio_mono {A E : BlockMat d}
    (hAsymm : IsSymmetricBlockMat A) (hApos : Book.Ch02.BlockPosDef A)
    (hEsymm : IsSymmetricBlockMat E) (hEpos : Book.Ch02.BlockPosDef E)
    (hle : BlockMatLoewnerLE A E) : aspectRatio A ≤ aspectRatio E := by
  rw [aspectRatio_eq_bigLambdaRef_mul_specBound, aspectRatio_eq_bigLambdaRef_mul_specBound]
  exact mul_le_mul (bigLambdaRef_mono hAsymm hApos hEsymm hEpos hle)
    (specBound_le (specBound_nonneg _)
      ((matLoewnerLE_lowerRight_of_blockMatLoewnerLE hle).trans
        (matLoewnerLE_specBound_smul_one _)))
    (specBound_nonneg _) (bigLambdaRef_nonneg E)

end

end HighContrast
end HCPolySupport
