/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastMeanDilation
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastHattedCarrier
public import LeanPool.HighContrastHomogenization.Provider.Transport.WindowCenteredBound
public import LeanPool.HighContrastHomogenization.Provider.Transport.WindowCellBounds
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.MeanOrder

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastMeanDropCarrier

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The mean-drop carrier

The reference-normalized mean drop between two scales of one grid is
first-order in the hatted contrast drop: the mean dilation bounds the
difference by `4d·(hat_j − hat_p)` times the later mean, the terminal
envelope converts the later mean into the scaled reference, and the
sandwich bound converts the Loewner estimate into the scalar size.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ}

/-- **The mean-drop carrier bound.** -/
theorem blockSize_meanDrop_le [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {l : ℤ} {q : Mat d} (hgrid : IsRoundedGrid l q)
    {j p : ℤ} (hlj : l ≤ j) (hjp : j ≤ p)
    (hfinj : HasFiniteAdaptedMean P q j)
    (hfinp : HasFiniteAdaptedMean P q p)
    (hsmall : (d : ℝ) *
      (adaptedHattedContrast P q j - adaptedHattedContrast P q p) ≤ 1)
    {E : BlockMat d} (hEsym : IsSymmetricBlockMat E)
    {cT : ℝ} (hcT : 0 ≤ cT)
    (henvT : BlockMatLoewnerLE (adaptedMean P q p) (blockScale cT E))
    {F : BlockMat d} (hFsym : IsSymmetricBlockMat F)
    (hFpd : Book.Ch02.BlockPosDef F) :
    blockSize (blockSub (adaptedMean P q j) (adaptedMean P q p)) F ≤
      4 * (d : ℝ) *
        (adaptedHattedContrast P q j - adaptedHattedContrast P q p) *
        cT * blockSize E F := by
  classical
  have hdrop0 : 0 ≤
      adaptedHattedContrast P q j - adaptedHattedContrast P q p :=
    sub_nonneg.mpr (adaptedHattedContrast_le hstat hgrid hlj hjp hfinj
      hfinp)
  have hc0 : 0 ≤ 4 * (d : ℝ) *
      (adaptedHattedContrast P q j - adaptedHattedContrast P q p) * cT := by
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    positivity
  have hdil := adaptedMean_le_hattedContrast_dilation hstat hgrid hlj hjp
    hfinj hfinp hsmall
  have hmono := Recurrence.toFullBlockMat_adaptedMean_le hstat hgrid hlj hjp
    hfinj hfinp
  have hXsym : IsSymmetricBlockMat
      (blockSub (adaptedMean P q j) (adaptedMean P q p)) :=
    isSymmetricBlockMat_blockSub
      (Recurrence.isSymmetricBlockMat_adaptedMean P q j)
      (Recurrence.isSymmetricBlockMat_adaptedMean P q p)
  have hXfull : toFullBlockMat
      (blockSub (adaptedMean P q j) (adaptedMean P q p)) =
      toFullBlockMat (adaptedMean P q j) -
        toFullBlockMat (adaptedMean P q p) :=
    Transport.toFullBlockMat_blockSub _ _
  have hXps : (toFullBlockMat
      (blockSub (adaptedMean P q j) (adaptedMean P q p))).PosSemidef := by
    rw [hXfull]
    exact Matrix.le_iff.mp hmono
  have henvFull : toFullBlockMat (adaptedMean P q p) ≤
      cT • toFullBlockMat E := by
    have h := le_of_blockMatLoewnerLE
      (Recurrence.isSymmetricBlockMat_adaptedMean P q p)
      (isSymmetricBlockMat_blockScale cT hEsym) henvT
    rwa [toFullBlockMat_blockScale] at h
  have hXle : toFullBlockMat
      (blockSub (adaptedMean P q j) (adaptedMean P q p)) ≤
      (4 * (d : ℝ) *
        (adaptedHattedContrast P q j - adaptedHattedContrast P q p) *
        cT) • toFullBlockMat E := by
    rw [hXfull]
    have hstep : toFullBlockMat (adaptedMean P q j) -
        toFullBlockMat (adaptedMean P q p) ≤
        (4 * (d : ℝ) *
          (adaptedHattedContrast P q j - adaptedHattedContrast P q p)) •
          toFullBlockMat (adaptedMean P q p) := by
      have h := hdil
      have hsub := sub_le_sub_right h (toFullBlockMat (adaptedMean P q p))
      refine hsub.trans (le_of_eq ?_)
      rw [add_smul, one_smul, add_sub_cancel_left]
    refine hstep.trans ?_
    have h := smul_le_smul_of_nonneg_left henvFull
      (by positivity : (0 : ℝ) ≤ 4 * (d : ℝ) *
        (adaptedHattedContrast P q j - adaptedHattedContrast P q p))
    rwa [smul_smul] at h
  have hXle' : BlockMatLoewnerLE
      (blockSub (adaptedMean P q j) (adaptedMean P q p))
      (blockScale (4 * (d : ℝ) *
        (adaptedHattedContrast P q j - adaptedHattedContrast P q p) *
        cT * blockSize E F) F) := by
    refine blockMatLoewnerLE_of_le ?_
    rw [toFullBlockMat_blockScale]
    refine hXle.trans ?_
    have hEF := (PortableHistory.blockSize_sandwich hEsym hFsym hFpd).1
    have h := smul_le_smul_of_nonneg_left hEF hc0
    rwa [smul_smul] at h
  refine Transport.blockSize_le_of_blockMatLoewnerLE_blockScale hXsym hXps
    hFsym hFpd ?_ hXle'
  exact mul_nonneg hc0
    (PortableHistory.blockSize_nonneg hEsym hFsym hFpd)

end

end HCPolySupport.HighContrast.Quenched
