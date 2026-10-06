/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.Prop42Tilt.AdaptedHatIntrinsic
public import LeanPool.HighContrastHomogenization.Provider.Quenched.AnnealedContrastAntitone
public import LeanPool.HighContrastHomogenization.Provider.Persistence.EuclideanTransfer
public import LeanPool.HighContrastHomogenization.Provider.Entry.AdapterAssembly
public import LeanPool.HighContrastHomogenization.Provider.Entry.ContrastBridge
public import LeanPool.HighContrastHomogenization.Provider.PortableHistory.MajorizationSize

/-!
# High-contrast homogenization: Provider.Quenched.Prop42Tilt.AdapterScalarization

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Scalarization of the adapted-to-Euclidean tilt comparison

The one-sided block adapter is first absorbed into a multiplicative comparison
with the adapted mean.  Intrinsic contrast has degree two under a common scalar
dilation, so this comparison combines with the hatted-trace polynomial without
any additional smallness premise.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open MeasureTheory

open scoped MatrixOrder Matrix

noncomputable section

variable {d : ℕ}

private theorem schurSkew_blockScale_of_pos {B : BlockMat d}
    (hB : Book.Ch02.BlockPosDef B) {c : ℝ} (hc : 0 < c) :
    schurSkew (blockScale c B) = schurSkew B := by
  have hdet : IsUnit B.lowerRight.det := isUnit_det_lowerRight hB
  change -((c • B.lowerRight)⁻¹ * (c • B.lowerLeft)) =
    -(B.lowerRight⁻¹ * B.lowerLeft)
  rw [inv_smul_of_isUnit hc.ne' hdet, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]

private theorem schurSigma_blockScale_of_pos {B : BlockMat d}
    (hB : Book.Ch02.BlockPosDef B) {c : ℝ} (hc : 0 < c) :
    schurSigma (blockScale c B) = c • schurSigma B := by
  rw [schurSigma, schurSigma, schurSkew_blockScale_of_pos hB hc]
  change c • B.upperLeft -
      matTranspose (schurSkew B) * (c • B.lowerRight) * schurSkew B =
    c • (B.upperLeft -
      matTranspose (schurSkew B) * B.lowerRight * schurSkew B)
  rw [Matrix.mul_smul, Matrix.smul_mul, smul_sub]

private theorem schurSigmaStar_blockScale_of_pos {B : BlockMat d}
    (hB : Book.Ch02.BlockPosDef B) {c : ℝ} (hc : 0 < c) :
    schurSigmaStar (blockScale c B) = c⁻¹ • schurSigmaStar B := by
  have hdet : IsUnit B.lowerRight.det := isUnit_det_lowerRight hB
  change (c • B.lowerRight)⁻¹ = c⁻¹ • B.lowerRight⁻¹
  exact inv_smul_of_isUnit hc.ne' hdet

/-- Intrinsic contrast grows by at most the square of a positive scalar under
scalar dilation of a positive block. -/
theorem blockContrast_blockScale_le {B : BlockMat d}
    (hBsymm : IsSymmetricBlockMat B) (hBpos : Book.Ch02.BlockPosDef B)
    {c : ℝ} (hc : 0 < c) :
    blockContrast (blockScale c B) ≤ c ^ 2 * blockContrast B := by
  obtain ⟨h, hh, hchain⟩ :=
    Initialization.exists_isSkewMat_matLoewnerLE_refContrast_smul hBsymm hBpos
  have hchainScaled := matLoewnerLE_smul hc.le hchain
  refine blockContrast_le
    (mul_nonneg (sq_nonneg c) (blockContrast_nonneg B)) hh ?_
  rw [schurSigma_blockScale_of_pos hBpos hc,
    schurSkew_blockScale_of_pos hBpos hc]
  have hleft : c • schurSigma B +
      matTranspose (schurSkew B - h) * (blockScale c B).lowerRight *
        (schurSkew B - h) =
      c • (schurSigma B +
        matTranspose (schurSkew B - h) * B.lowerRight * (schurSkew B - h)) := by
    change c • schurSigma B +
        matTranspose (schurSkew B - h) * (c • B.lowerRight) *
          (schurSkew B - h) = _
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_add]
  rw [hleft]
  rw [schurSigmaStar_blockScale_of_pos hBpos hc, smul_smul]
  have hrhs : (c ^ 2 * blockContrast B) * c⁻¹ =
      c * blockContrast B := by
    field_simp
  rw [hrhs]
  simpa only [smul_smul] using! hchainScaled

/-- A one-sided adapter error gives a corrected scalar contrast comparison.
The error size is measured natively by `blockSize E B`; no tolerance or
smallness hypothesis is added. -/
theorem blockContrast_sub_one_le_adaptedHatted_of_adapter [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {A E : BlockMat d} {l r : ℤ} {q : Mat d}
    (hAsymm : IsSymmetricBlockMat A) (hApos : Book.Ch02.BlockPosDef A)
    (hEsymm : IsSymmetricBlockMat E) (hEpos : Book.Ch02.BlockPosDef E)
    (hq : IsRoundedGrid l q) (hfin : HasFiniteAdaptedMean P q r)
    {c : ℝ} (hc : 0 ≤ c)
    (hsub : BlockMatLoewnerLE
      (blockSub A (adaptedMean P q r)) (blockScale c E)) :
    let eta := c * blockSize E (adaptedMean P q r)
    let x := (d : ℝ) * (adaptedHattedContrast P q r - 1)
    blockContrast A - 1 ≤
      (1 + eta) ^ 2 *
        (1 + (5 / 4 : ℝ) * x + (1 / 4 : ℝ) * x ^ 2) - 1 := by
  let B : BlockMat d := adaptedMean P q r
  let eta : ℝ := c * blockSize E B
  let x : ℝ := (d : ℝ) * (adaptedHattedContrast P q r - 1)
  have hBsymm : IsSymmetricBlockMat B :=
    Recurrence.isSymmetricBlockMat_adaptedMean P q r
  have hBpos : Book.Ch02.BlockPosDef B :=
    Recurrence.blockPosDef_adaptedMean_of_isRoundedGrid hq r hfin
  have heta0 : 0 ≤ eta :=
    mul_nonneg hc (PortableHistory.blockSize_nonneg hEsymm hBsymm hBpos)
  have herr := Persistence.toFullBlockMat_blockScale_le_smul
    hEsymm hEpos hBsymm hBpos hc (le_refl eta)
  have hupper : BlockMatLoewnerLE A (blockScale (1 + eta) B) :=
    Persistence.blockMatLoewnerLE_one_add hAsymm hBsymm hEsymm hsub herr
  have hscalePos : 0 < 1 + eta := by linarith only [heta0]
  have hmono : blockContrast A ≤ blockContrast (blockScale (1 + eta) B) :=
    blockContrast_le_of_blockMatLoewnerLE hAsymm hApos
      (isSymmetricBlockMat_blockScale (1 + eta) hBsymm)
      (Transport.blockPosDef_blockScale hscalePos hBpos) hupper
  have hscale := blockContrast_blockScale_le hBsymm hBpos hscalePos
  have hhat := adaptedContrast_sub_one_le_hatted_polynomial hq hfin
  dsimp only [B, eta, x] at hmono hscale hhat ⊢
  nlinarith only [hmono, hscale, hhat, sq_nonneg (1 + c * blockSize E (adaptedMean P q r))]

end

end Quenched
end HighContrast
end HCPolySupport
