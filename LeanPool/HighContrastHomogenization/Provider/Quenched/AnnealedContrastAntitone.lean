/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Geometry.AspectRatioMonotone
public import LeanPool.HighContrastHomogenization.Provider.Entry.IdentityCells
public import LeanPool.HighContrastHomogenization.Provider.Quenched.TriadicDilationResponse
public import LeanPool.HighContrastHomogenization.Provider.SourceControl.ReferenceIntermediate
public import LeanPool.HighContrastHomogenization.Provider.SourceControl.SchurHelpers

/-!
# High-contrast homogenization: Provider.Quenched.AnnealedContrastAntitone

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Monotonicity of the annealed contrast

The intrinsic contrast decreases when a symmetric positive doubled block
decreases in Loewner order.  Applied to the annealed coarse blocks, this gives
the generation monotonicity used when a law is rebased at a later triadic
scale.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open MeasureTheory

open scoped MatrixOrder

noncomputable section

variable {d : ℕ}

/-- The intrinsic contrast is monotone for the quadratic-form order on
symmetric positive doubled blocks. -/
theorem blockContrast_le_of_blockMatLoewnerLE {A E : BlockMat d}
    (hAsymm : IsSymmetricBlockMat A) (hApos : Book.Ch02.BlockPosDef A)
    (hEsymm : IsSymmetricBlockMat E) (hEpos : Book.Ch02.BlockPosDef E)
    (hle : BlockMatLoewnerLE A E) :
    blockContrast A ≤ blockContrast E := by
  obtain ⟨h, hh, hE⟩ :=
    Initialization.exists_isSkewMat_matLoewnerLE_refContrast_smul hEsymm hEpos
  have hcorr : MatLoewnerLE (skewCorrectedForm A h) (skewCorrectedForm E h) :=
    matLoewnerLE_skewCorrectedForm_of_blockMatLoewnerLE
      hAsymm hApos hEsymm hEpos hle h
  have hAlr : A.lowerRight.PosDef := posDef_lowerRight hAsymm hApos
  have hElr : E.lowerRight.PosDef := posDef_lowerRight hEsymm hEpos
  have hlr : A.lowerRight ≤ E.lowerRight :=
    Initialization.le_of_matLoewnerLE hAlr.isHermitian hElr.isHermitian
      (matLoewnerLE_lowerRight_of_blockMatLoewnerLE hle)
  have hstarOrd : schurSigmaStar E ≤ schurSigmaStar A := by
    simpa only [schurSigmaStar] using inv_le_inv_of_le hAlr hElr hlr
  have hscaled : MatLoewnerLE
      (blockContrast E • schurSigmaStar E)
      (blockContrast E • schurSigmaStar A) :=
    Initialization.matLoewnerLE_of_le
      (smul_le_smul_of_le (blockContrast_nonneg E) hstarOrd)
  have hE' : MatLoewnerLE (skewCorrectedForm E h)
      (blockContrast E • schurSigmaStar E) := by
    simpa only [refContrast] using hE
  refine blockContrast_le (blockContrast_nonneg E) hh ?_
  simpa only [skewCorrectedForm] using hcorr.trans (hE'.trans hscaled)

/-- The annealed intrinsic contrast decreases between nonnegative Euclidean
generations. -/
theorem annealedContrast_le_of_nonneg_of_le [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ}
    {S : CoeffSpace d → ℝ}
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {j p : ℤ} (hj : 0 ≤ j) (hjp : j ≤ p) :
    annealedContrast P p ≤ annealedContrast P j := by
  simpa only [annealedContrast] using
    blockContrast_le_of_blockMatLoewnerLE
      (isSymmetricBlockMat_annealedBlock P (centeredCube d p))
      (blockPosDef_annealedBlock_of_coarseEllipticityDagger hdag p)
      (isSymmetricBlockMat_annealedBlock P (centeredCube d j))
      (blockPosDef_annealedBlock_of_coarseEllipticityDagger hdag j)
      (Entry.annealedBlock_centeredCube_le_of_nonneg hstat hdag hj hjp)

/-- The annealed intrinsic contrast is antitone along the natural-number
generations. -/
theorem annealedContrast_antitone [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ}
    {S : CoeffSpace d → ℝ}
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) :
    Antitone (fun n : ℕ ↦ annealedContrast P (n : ℤ)) := by
  intro j p hjp
  exact annealedContrast_le_of_nonneg_of_le hstat hdag
    (Int.natCast_nonneg j) (Int.ofNat_le.mpr hjp)

/-- Small contrast at an entry generation remains valid at generation zero of
a law rebased at any later generation. -/
theorem annealedContrast_triadicRebasedLaw_zero_sub_one_le_of_le [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ}
    {S : CoeffSpace d → ℝ}
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {mEnt nBase : ℕ} (hmn : mEnt ≤ nBase) {cStar : ℝ}
    (hsmall : annealedContrast P (mEnt : ℤ) - 1 ≤ cStar) :
    annealedContrast (triadicRebasedLaw nBase P) 0 - 1 ≤ cStar := by
  have hmono := annealedContrast_antitone hstat hdag hmn
  rw [annealedContrast_triadicRebasedLaw]
  norm_num
  linarith only [hmono, hsmall]

end

end Quenched
end HighContrast
end HCPolySupport
