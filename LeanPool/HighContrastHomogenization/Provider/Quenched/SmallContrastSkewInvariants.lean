/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastRecenteredSharp
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastHattedCarrier

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastSkewInvariants

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Scalar invariance of the contrasts under a constant-skew recentering

The observation of Section 2.5 of HC, equation (2.65), is that subtracting a
constant skew `g` from the coefficient
field leaves `σ` and `σ_*` untouched and replaces `k` by `k - g`.  Both
contrasts of the paper are functions of the Schur data that are blind to the
skew coordinate — the hatted contrast does not mention it, and the intrinsic
contrast minimizes over it — so both are invariant.

This file records that invariance at the level of doubled blocks, which is the
algebraic half of the law-side API for that recentering: once
`annealedBlock (P.map (·.subSkew g hg)) U = skewBlockCongr g (annealedBlock P U)`
is available, `annealedContrast` and `adaptedHattedContrast` are literally
unchanged by the recentering.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## Reading the Schur data off a Schur form -/

/-- The Schur data of a block in Schur form is the data of the form. -/
theorem schurData_of_schurBlock {H : BlockMat d} {S SStar K : Mat d}
    (hStar : SStar.PosDef) (hH : toFullBlockMat H = schurBlock S SStar K) :
    H.lowerRight = SStar⁻¹ ∧ schurSigmaStar H = SStar ∧ schurSkew H = K ∧
      schurSigma H = S := by
  have hStarDet : IsUnit SStar.det := isUnit_det_of_posDef hStar
  have hlowerRight : H.lowerRight = SStar⁻¹ := by
    have hblock : H.lowerRight = (toFullBlockMat H).toBlocks₂₂ := rfl
    rw [hblock, hH, toBlocks₂₂_schurBlock]
  have hlowerLeft : H.lowerLeft = -(SStar⁻¹ * K) := by
    have hblock : H.lowerLeft = (toFullBlockMat H).toBlocks₂₁ := rfl
    rw [hblock, hH, toBlocks₂₁_schurBlock]
  have hupperLeft : H.upperLeft = S + Kᴴ * SStar⁻¹ * K := by
    have hblock : H.upperLeft = (toFullBlockMat H).toBlocks₁₁ := rfl
    rw [hblock, hH, toBlocks₁₁_schurBlock]
  have hinvinv : (SStar⁻¹)⁻¹ = SStar :=
    Matrix.nonsing_inv_nonsing_inv _ hStarDet
  have hstar : schurSigmaStar H = SStar := by
    rw [schurSigmaStar, hlowerRight, hinvinv]
  have hskew : schurSkew H = K := by
    rw [schurSkew, hlowerRight, hlowerLeft, hinvinv, Matrix.mul_neg, neg_neg,
      ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hStarDet, Matrix.one_mul]
  have hsigma : schurSigma H = S := by
    rw [schurSigma, hskew, hupperLeft, hlowerRight, matTranspose,
      ← conjTranspose_eq_transpose']
    abel
  exact ⟨hlowerRight, hstar, hskew, hsigma⟩

/-! ## The hatted contrast is skew-blind -/

/-! ## The intrinsic contrast is skew-blind -/

/-- The defining set of the intrinsic contrast, written in Schur data. -/
@[expose]
public def contrastSet (S SStar K : Mat d) : Set ℝ :=
  {t : ℝ | 0 ≤ t ∧ ∃ h : Mat d, IsSkewMat h ∧
    MatLoewnerLE (S + matTranspose (K - h) * SStar⁻¹ * (K - h)) (t • SStar)}

/-- The intrinsic contrast in terms of the Schur data of a Schur form. -/
private theorem blockContrast_eq_contrastSet {H : BlockMat d}
    {S SStar K : Mat d} (hStar : SStar.PosDef)
    (hH : toFullBlockMat H = schurBlock S SStar K) :
    blockContrast H = sInf (contrastSet S SStar K) := by
  obtain ⟨hlow, hstar, hskew, hsigma⟩ := schurData_of_schurBlock hStar hH
  rw [blockContrast, contrastSet, hsigma, hskew, hlow, hstar]

/-- Shifting a skew matrix by a skew matrix stays skew. -/
private theorem isSkewMat_add {h g : Mat d} (hh : IsSkewMat h)
    (hg : IsSkewMat g) : IsSkewMat (h + g) := by
  rw [IsSkewMat, matTranspose, Matrix.transpose_add]
  rw [IsSkewMat, matTranspose] at hh hg
  rw [hh, hg]
  abel

/-- Negating a skew matrix stays skew. -/
private theorem isSkewMat_neg' {g : Mat d} (hg : IsSkewMat g) :
    IsSkewMat (-g) := by
  rw [IsSkewMat, matTranspose, Matrix.transpose_neg]
  rw [IsSkewMat, matTranspose] at hg
  rw [hg]

/-- **The intrinsic contrast is invariant under a constant-skew recentering.**
The minimization over the skew coordinate absorbs the shift. -/
theorem blockContrast_skewBlockCongr {H : BlockMat d} {S SStar K : Mat d}
    (hStar : SStar.PosDef) (hH : toFullBlockMat H = schurBlock S SStar K)
    {g : Mat d} (hg : IsSkewMat g) :
    blockContrast (Response.skewBlockCongr g H) = blockContrast H := by
  have hH' : toFullBlockMat (Response.skewBlockCongr g H) =
      schurBlock S SStar (K - g) :=
    toFullBlockMat_skewBlockCongr_of_schurBlock g hH
  rw [blockContrast_eq_contrastSet hStar hH',
    blockContrast_eq_contrastSet hStar hH]
  congr 1
  ext t
  simp only [contrastSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨ht, h, hskew, hle⟩
    refine ⟨ht, h + g, isSkewMat_add hskew hg, ?_⟩
    have hrw : K - (h + g) = K - g - h := by abel
    rw [hrw]
    exact hle
  · rintro ⟨ht, h, hskew, hle⟩
    have hskewsub : IsSkewMat (h - g) := by
      have hh := isSkewMat_add hskew (isSkewMat_neg' hg)
      rwa [← sub_eq_add_neg] at hh
    refine ⟨ht, h - g, hskewsub, ?_⟩
    have hrw : K - g - (h - g) = K - h := by abel
    rw [hrw]
    exact hle

end

end HCPolySupport.HighContrast.Quenched
