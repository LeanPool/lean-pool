/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.AnnealedContrastAntitone
public import LeanPool.HighContrastHomogenization.Provider.Entry.EuclideanAdapter
public import LeanPool.HighContrastHomogenization.Provider.Quenched.UnitRangeReferenceComparison

/-!
# High-contrast homogenization: Provider.Quenched.BlockScaleGeometry

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Scalar dilation of reference geometry

This file records the homogeneity of the reference aspect ratio and the
quadratic upper homogeneity of the intrinsic contrast under a positive common
scalar dilation of a doubled block.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

noncomputable section

variable {d : Nat}

private theorem matLoewnerLE_smul {A B : Mat d} {c : Real} (hc : 0 <= c)
    (h : MatLoewnerLE A B) : MatLoewnerLE (c • A) (c • B) := by
  intro x
  rw [smul_matVecMul, smul_matVecMul, vecDot_smul_right, vecDot_smul_right]
  have hx := h x
  have hm := mul_le_mul_of_nonneg_left hx hc
  linarith only [hm]

private theorem matLoewnerLE_smul_iff {A B : Mat d} {c : Real} (hc : 0 < c) :
    MatLoewnerLE (c • A) (c • B) ↔ MatLoewnerLE A B := by
  refine ⟨fun h => ?_, matLoewnerLE_smul hc.le⟩
  have h' := matLoewnerLE_smul (c := c⁻¹) (inv_nonneg.2 hc.le) h
  rwa [inv_smul_smul₀ hc.ne', inv_smul_smul₀ hc.ne'] at h'

private theorem specBound_smul {c : Real} (hc : 0 < c) (M : Mat d) :
    specBound (c • M) = c * specBound M := by
  refine le_antisymm ?_ ?_
  · refine specBound_le (mul_nonneg hc.le (specBound_nonneg M)) ?_
    have h := matLoewnerLE_smul hc.le (matLoewnerLE_specBound_smul_one M)
    rwa [smul_smul] at h
  · have h := matLoewnerLE_smul (c := c⁻¹) (inv_nonneg.2 hc.le)
      (matLoewnerLE_specBound_smul_one (c • M))
    rw [inv_smul_smul₀ hc.ne', smul_smul] at h
    have h' : specBound M <= c⁻¹ * specBound (c • M) :=
      specBound_le (mul_nonneg (inv_nonneg.2 hc.le) (specBound_nonneg _)) h
    have := mul_le_mul_of_nonneg_left h' hc.le
    rwa [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] at this

private theorem inv_smul_mat {c : Real} (hc : c ≠ 0) (M : Mat d) :
    (c • M)⁻¹ = c⁻¹ • M⁻¹ := by
  by_cases h : IsUnit M.det
  · refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc,
      one_smul, Matrix.nonsing_inv_mul _ h]
  · have hz : M.det = 0 := by simpa [isUnit_iff_ne_zero] using h
    have hscaled : ¬ IsUnit (c • M).det := by
      rw [Matrix.det_smul, hz, mul_zero]
      simp
    rw [Matrix.nonsing_inv_apply_not_isUnit _ hscaled,
      Matrix.nonsing_inv_apply_not_isUnit _ h, smul_zero]

private theorem schurSkew_blockScale {c : Real} (hc : c ≠ 0) (E : BlockMat d) :
    schurSkew (blockScale c E) = schurSkew E := by
  change -((c • E.lowerRight)⁻¹ * (c • E.lowerLeft)) =
    -(E.lowerRight⁻¹ * E.lowerLeft)
  rw [inv_smul_mat hc, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    inv_mul_cancel₀ hc, one_smul]

private theorem schurSigma_blockScale {c : Real} (hc : c ≠ 0)
    (E : BlockMat d) : schurSigma (blockScale c E) = c • schurSigma E := by
  rw [schurSigma, schurSkew_blockScale hc, schurSigma]
  change c • E.upperLeft -
      matTranspose (schurSkew E) * (c • E.lowerRight) * schurSkew E =
    c • (E.upperLeft -
      matTranspose (schurSkew E) * E.lowerRight * schurSkew E)
  rw [Matrix.mul_smul, Matrix.smul_mul, smul_sub]

private theorem lambdaRef_blockScale {c : Real} (hc : 0 < c) (E : BlockMat d) :
    lambdaRef (blockScale c E) = c⁻¹ * lambdaRef E := by
  change (specBound (c • E.lowerRight))⁻¹ =
    c⁻¹ * (specBound E.lowerRight)⁻¹
  rw [specBound_smul hc, mul_inv]

private theorem sInf_mul_left {c : Real} (hc : 0 < c) {S : Set Real}
    (hne : S.Nonempty) (hbdd : BddBelow S) :
    sInf ((fun x => c * x) '' S) = c * sInf S := by
  have hne' := hne.image (fun x => c * x)
  have hbdd' : BddBelow ((fun x => c * x) '' S) := by
    obtain ⟨b, hb⟩ := hbdd
    refine ⟨c * b, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact mul_le_mul_of_nonneg_left (hb hx) hc.le
  refine le_antisymm ?_ ?_
  · have hdiv : sInf ((fun x => c * x) '' S) / c <= sInf S := by
      refine le_csInf hne fun x hx => ?_
      exact (div_le_iff₀ hc).2 (csInf_le hbdd' ⟨x, hx, mul_comm _ _⟩)
    have := mul_le_mul_of_nonneg_left hdiv hc.le
    rwa [mul_div_cancel₀ _ hc.ne'] at this
  · refine le_csInf hne' ?_
    rintro _ ⟨x, hx, rfl⟩
    exact mul_le_mul_of_nonneg_left (csInf_le hbdd hx) hc.le

private theorem bigLambdaRefSet_nonempty (E : BlockMat d) :
    {t : Real | 0 <= t ∧ ∃ h : Mat d, IsSkewMat h ∧
      MatLoewnerLE
        (schurSigma E + matTranspose (schurSkew E - h) * E.lowerRight *
          (schurSkew E - h)) (t • (1 : Mat d))}.Nonempty := by
  obtain ⟨s, hs0, hs⟩ := exists_matLoewnerLE_smul_one
    (schurSigma E + matTranspose (schurSkew E) * E.lowerRight * schurSkew E)
  refine ⟨s, hs0, 0, ?_, ?_⟩
  · simp [IsSkewMat, matTranspose]
  · simpa using hs

private theorem bigLambdaRefSet_bddBelow (E : BlockMat d) :
    BddBelow {t : Real | 0 <= t ∧ ∃ h : Mat d, IsSkewMat h ∧
      MatLoewnerLE
        (schurSigma E + matTranspose (schurSkew E - h) * E.lowerRight *
          (schurSkew E - h)) (t • (1 : Mat d))} :=
  ⟨0, fun _ hx => hx.1⟩

private theorem bigLambdaRef_blockScale {c : Real} (hc : 0 < c)
    (E : BlockMat d) : bigLambdaRef (blockScale c E) = c * bigLambdaRef E := by
  have hmat : forall h : Mat d,
      schurSigma (blockScale c E) +
          matTranspose (schurSkew (blockScale c E) - h) *
            (blockScale c E).lowerRight * (schurSkew (blockScale c E) - h) =
        c • (schurSigma E + matTranspose (schurSkew E - h) * E.lowerRight *
          (schurSkew E - h)) := by
    intro h
    rw [schurSkew_blockScale hc.ne', schurSigma_blockScale hc.ne']
    change c • schurSigma E +
        matTranspose (schurSkew E - h) * (c • E.lowerRight) *
          (schurSkew E - h) = _
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_add]
  have hset :
      {t : Real | 0 <= t ∧ ∃ h : Mat d, IsSkewMat h ∧
        MatLoewnerLE
          (schurSigma (blockScale c E) +
            matTranspose (schurSkew (blockScale c E) - h) *
              (blockScale c E).lowerRight *
                (schurSkew (blockScale c E) - h)) (t • (1 : Mat d))} =
      (fun x => c * x) ''
        {t : Real | 0 <= t ∧ ∃ h : Mat d, IsSkewMat h ∧
          MatLoewnerLE
            (schurSigma E + matTranspose (schurSkew E - h) * E.lowerRight *
              (schurSkew E - h)) (t • (1 : Mat d))} := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_image, hmat]
    constructor
    · rintro ⟨ht0, h, hh, hle⟩
      refine ⟨t / c, ⟨div_nonneg ht0 hc.le, h, hh, ?_⟩, by field_simp⟩
      have hs : MatLoewnerLE
          (c • (schurSigma E + matTranspose (schurSkew E - h) * E.lowerRight *
            (schurSkew E - h))) (c • ((t / c) • (1 : Mat d))) := by
        rwa [smul_smul, mul_div_cancel₀ _ hc.ne']
      exact (matLoewnerLE_smul_iff hc).1 hs
    · rintro ⟨s, ⟨hs0, h, hh, hle⟩, rfl⟩
      refine ⟨mul_nonneg hc.le hs0, h, hh, ?_⟩
      have hs := matLoewnerLE_smul hc.le hle
      rwa [smul_smul] at hs
  rw [bigLambdaRef, bigLambdaRef, hset,
    sInf_mul_left hc (bigLambdaRefSet_nonempty E) (bigLambdaRefSet_bddBelow E)]

/-- The reference aspect ratio is homogeneous of degree two under a common
positive scalar dilation of a doubled block. -/
theorem aspectRatio_blockScale {c : Real} (hc : 0 < c) (E : BlockMat d) :
    aspectRatio (blockScale c E) = c ^ 2 * aspectRatio E := by
  rw [aspectRatio, aspectRatio, bigLambdaRef_blockScale hc,
    lambdaRef_blockScale hc, div_eq_mul_inv, div_eq_mul_inv, mul_inv, inv_inv]
  ring

private theorem schurSigmaStar_blockScale_of_pos {B : BlockMat d}
    (hB : Book.Ch02.BlockPosDef B) {c : Real} (hc : 0 < c) :
    schurSigmaStar (blockScale c B) = c⁻¹ • schurSigmaStar B := by
  have hdet := isUnit_det_lowerRight hB
  change (c • B.lowerRight)⁻¹ = c⁻¹ • B.lowerRight⁻¹
  exact inv_smul_of_isUnit hc.ne' hdet

/-- Intrinsic contrast grows by at most the square of a positive common
scalar dilation. -/
theorem blockContrast_blockScale_le {B : BlockMat d}
    (hBsymm : IsSymmetricBlockMat B) (hBpos : Book.Ch02.BlockPosDef B)
    {c : Real} (hc : 0 < c) :
    blockContrast (blockScale c B) <= c ^ 2 * blockContrast B := by
  obtain ⟨h, hh, hchain⟩ :=
    Initialization.exists_isSkewMat_matLoewnerLE_refContrast_smul hBsymm hBpos
  have hscaled := matLoewnerLE_smul hc.le hchain
  refine blockContrast_le
    (mul_nonneg (sq_nonneg c) (blockContrast_nonneg B)) hh ?_
  rw [schurSigma_blockScale hc.ne', schurSkew_blockScale hc.ne']
  have hleft : c • schurSigma B +
      matTranspose (schurSkew B - h) * (blockScale c B).lowerRight *
        (schurSkew B - h) =
      c • (schurSigma B + matTranspose (schurSkew B - h) * B.lowerRight *
        (schurSkew B - h)) := by
    change c • schurSigma B + matTranspose (schurSkew B - h) *
      (c • B.lowerRight) * (schurSkew B - h) = _
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_add]
  rw [hleft, schurSigmaStar_blockScale_of_pos hBpos hc, smul_smul]
  have hrhs : (c ^ 2 * blockContrast B) * c⁻¹ = c * blockContrast B := by
    field_simp
  rw [hrhs]
  simpa only [smul_smul] using! hscaled

end

end Quenched
end HighContrast
end HCPolySupport
