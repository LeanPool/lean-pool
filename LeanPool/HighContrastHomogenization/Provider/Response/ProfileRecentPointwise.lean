/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileCarriers
public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormComparison
public import LeanPool.HighContrastHomogenization.Provider.Response.LoadCalibrationTheta
public import LeanPool.HighContrastHomogenization.Provider.PortableHistory.MajorizationSup

/-!
# High-contrast homogenization: Provider.Response.ProfileRecentPointwise

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Pointwise bounds for the recent profile terms

The recent cell defect is split at its scale-dependent annealed mean.  The two
centered pieces are read from the terminal centered maximum, while the positive
mean increment is read from the nonlinear gain.  The averaged defect uses the
same positive increment after expectation.
-/

namespace HCPolySupport.HighContrast.Response

open MeasureTheory Book.Ch02

open scoped ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder

noncomputable section

variable {d : ℕ}

/-! ## Normalized block algebra -/

/-- The scalar size of a difference is symmetric in its two endpoints. -/
theorem blockSize_blockSub_comm {A B F : BlockMat d}
    (hA : IsSymmetricBlockMat A) (hB : IsSymmetricBlockMat B)
    (hF : IsSymmetricBlockMat F) (hFpd : BlockPosDef F) :
    blockSize (blockSub A B) F = blockSize (blockSub B A) F := by
  rw [PortableHistory.blockSize_eq_norm (isSymmetricBlockMat_blockSub hA hB) hF hFpd,
    PortableHistory.blockSize_eq_norm (isSymmetricBlockMat_blockSub hB hA) hF hFpd]
  have hneg :
      toFullBlockMat (normalizedBlock (blockSub B A) F) =
        -toFullBlockMat (normalizedBlock (blockSub A B) F) := by
    simp only [Recurrence.toFullBlockMat_normalizedBlock_blockSub]
    noncomm_ring
  rw [hneg, norm_neg]

/-- The normalized scalar size obeys the triangle inequality through an
intermediate symmetric block. -/
theorem blockSize_blockSub_triangle {A B C F : BlockMat d}
    (hA : IsSymmetricBlockMat A) (hB : IsSymmetricBlockMat B)
    (hC : IsSymmetricBlockMat C) (hF : IsSymmetricBlockMat F)
    (hFpd : BlockPosDef F) :
    blockSize (blockSub A C) F ≤
      blockSize (blockSub A B) F + blockSize (blockSub B C) F := by
  rw [PortableHistory.blockSize_eq_norm (isSymmetricBlockMat_blockSub hA hC) hF hFpd,
    PortableHistory.blockSize_eq_norm (isSymmetricBlockMat_blockSub hA hB) hF hFpd,
    PortableHistory.blockSize_eq_norm (isSymmetricBlockMat_blockSub hB hC) hF hFpd]
  have hsplit :
      toFullBlockMat (normalizedBlock (blockSub A C) F) =
        toFullBlockMat (normalizedBlock (blockSub A B) F) +
          toFullBlockMat (normalizedBlock (blockSub B C) F) := by
    simp only [Recurrence.toFullBlockMat_normalizedBlock_blockSub]
    noncomm_ring
  rw [hsplit]
  exact norm_add_le _ _

/-! ## The nonlinear mean increment -/

/-- For `Q ≥ 1`, the trace gap is at most the `Q`-th root of its nonlinear
gain. -/
theorem traceGap_le_frakH_rpow_inv {Q x : ℝ} (hQ : 1 ≤ Q) (hx : 0 ≤ x) :
    x ≤ ((1 + x) ^ Q - 1) ^ Q⁻¹ := by
  have hpow : x ^ Q ≤ (1 + x) ^ Q - 1 := by
    have h := Real.add_rpow_le_rpow_add zero_le_one hx hQ
    rw [Real.one_rpow] at h
    linarith only [h]
  have hright : 0 ≤ (1 + x) ^ Q - 1 := by
    have hone : (1 : ℝ) ≤ (1 + x) ^ Q := by
      have hbase : (1 : ℝ) ≤ 1 + x := by linarith only [hx]
      have := Real.rpow_le_rpow zero_le_one hbase (by linarith only [hQ])
      rwa [Real.one_rpow] at this
    linarith only [hone]
  have hroot := Real.rpow_le_rpow (Real.rpow_nonneg hx Q) hpow
    (inv_nonneg.mpr (by linarith only [hQ]))
  calc
    x = (x ^ Q) ^ Q⁻¹ := by
      rw [← Real.rpow_mul hx, mul_inv_cancel₀ (by linarith only [hQ] : Q ≠ 0),
        Real.rpow_one]
    _ ≤ ((1 + x) ^ Q - 1) ^ Q⁻¹ := hroot

/-! ## Reading the centered maximum -/

/-- A centered cell on a retained scale is one of the terms of `Z_t`. -/
theorem ofReal_centered_cell_le_profileCenteredMaximum
    {P : Measure (CoeffSpace d)} {rhoMax : ℝ} {q : Mat d}
    {jStar k t : ℤ} (hjk : jStar ≤ k) (hkt : k ≤ t)
    {w : Fin d → ℤ} (hw : adaptedCellCenter q k w ∈ adaptedCell q t)
    (a : CoeffSpace d) :
    ENNReal.ofReal
        ((3 : ℝ) ^ (-rhoMax * ((t : ℝ) - (k : ℝ))) *
          blockSize
            (blockSub (adaptedResponse q k w a) (adaptedMean P q k))
            (adaptedMean P q t)) ≤
      profileCenteredMaximum P rhoMax q jStar t a := by
  exact le_iSup_of_le k (le_iSup_of_le hjk (le_iSup_of_le hkt
    (le_iSup_of_le w (le_iSup_of_le hw le_rfl))))

/-- On the finite branch, a centered cell is bounded by the growing terminal
weight times `Z_t`. -/
theorem centered_cell_le_profileCenteredMaximum_toReal
    {P : Measure (CoeffSpace d)} {rhoMax : ℝ} {q : Mat d}
    {jStar k t : ℤ} (hjk : jStar ≤ k) (hkt : k ≤ t)
    {w : Fin d → ℤ} (hw : adaptedCellCenter q k w ∈ adaptedCell q t)
    {a : CoeffSpace d}
    (htop : profileCenteredMaximum P rhoMax q jStar t a ≠ ⊤)
    (hsize : 0 ≤ blockSize
      (blockSub (adaptedResponse q k w a) (adaptedMean P q k))
      (adaptedMean P q t)) :
    blockSize
        (blockSub (adaptedResponse q k w a) (adaptedMean P q k))
        (adaptedMean P q t) ≤
      (3 : ℝ) ^ (rhoMax * ((t : ℝ) - (k : ℝ))) *
        (profileCenteredMaximum P rhoMax q jStar t a).toReal := by
  let W : ℝ := (3 : ℝ) ^ (-rhoMax * ((t : ℝ) - (k : ℝ)))
  let R : ℝ := (3 : ℝ) ^ (rhoMax * ((t : ℝ) - (k : ℝ)))
  have hW0 : 0 ≤ W := Real.rpow_nonneg (by norm_num) _
  have hread := ENNReal.toReal_mono htop
    (ofReal_centered_cell_le_profileCenteredMaximum hjk hkt hw a)
  rw [ENNReal.toReal_ofReal (mul_nonneg hW0 hsize)] at hread
  have hWR : R * W = 1 := by
    dsimp only [R, W]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    rw [show rhoMax * ((t : ℝ) - (k : ℝ)) +
      -rhoMax * ((t : ℝ) - (k : ℝ)) = 0 by ring, Real.rpow_zero]
  calc
    blockSize
          (blockSub (adaptedResponse q k w a) (adaptedMean P q k))
          (adaptedMean P q t) =
        R * (W * blockSize
          (blockSub (adaptedResponse q k w a) (adaptedMean P q k))
          (adaptedMean P q t)) := by rw [← mul_assoc, hWR, one_mul]
    _ ≤ R * (profileCenteredMaximum P rhoMax q jStar t a).toReal :=
      mul_le_mul_of_nonneg_left hread (Real.rpow_nonneg (by norm_num) _)

end

end HCPolySupport.HighContrast.Response
