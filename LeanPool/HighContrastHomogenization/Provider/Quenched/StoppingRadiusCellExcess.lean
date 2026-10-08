/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Window.SuccessorDiscrete
public import LeanPool.HighContrastHomogenization.Provider.Window.Successor
public import LeanPool.HighContrastHomogenization.Provider.Quenched.QuenchedPolynomialNormalizer
public import LeanPool.HighContrastHomogenization.Provider.Transport.WindowBelowStart
public import LeanPool.HighContrastHomogenization.Provider.Transport.WindowCellBounds
public import LeanPool.HighContrastHomogenization.Provider.Transport.FillingExhaustion
public import LeanPool.HighContrastHomogenization.Provider.Quenched.AnnealedLimitBlock

/-!
# High-contrast homogenization: Provider.Quenched.StoppingRadiusCellExcess

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The normalized cell excess below the stopping radius

Below the stopping radius of a generation the window supplies a discounted
Loewner bound against that generation's reference block.  Comparing the
reference block with the homogenized block turns it into a bound on the
normalized excess, which is the quantity the weighted row of
`e.random.quenched.row` sums.  The comparison of the two
blocks is the only input this file does not prove.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Rescaling a doubled block twice is rescaling once by the product. -/
theorem blockScale_blockScale (c c' : ℝ) (A : BlockMat d) :
    blockScale c (blockScale c' A) = blockScale (c * c') A := by
  simp only [blockScale, smul_smul]

/-- A discounted Loewner bound against a reference block, together with a
comparison of that block with the homogenized one, bounds the normalized
excess. -/
theorem blockExcess_le_of_blockMatLoewnerLE
    {H E Abar : BlockMat d} (hH : IsSymmetricBlockMat H)
    (hHps : (toFullBlockMat H).PosSemidef)
    (hAbar : IsSymmetricBlockMat Abar) (hAbarpd : Book.Ch02.BlockPosDef Abar)
    {s c : ℝ} (hs : 0 ≤ s) (hc : 0 ≤ c)
    (hcell : BlockMatLoewnerLE H (blockScale s E))
    (hcomp : BlockMatLoewnerLE E (blockScale c Abar)) :
    blockExcess H Abar ≤ s * c := by
  have hstep : BlockMatLoewnerLE (blockScale s E) (blockScale s (blockScale c Abar)) :=
    blockMatLoewnerLE_blockScale_of_le hs hcomp
  have hchain : BlockMatLoewnerLE H (blockScale (s * c) Abar) := by
    have h := BlockMatLoewnerLE.trans hcell hstep
    rwa [blockScale_blockScale] at h
  have hsize : blockSize H Abar ≤ s * c :=
    Transport.blockSize_le_of_blockMatLoewnerLE_blockScale hH hHps hAbar hAbarpd
      (mul_nonneg hs hc) hchain
  exact le_trans (Transport.blockExcess_le_blockSize hH hHps hAbar hAbarpd) hsize

end

end Quenched
end HighContrast
end HCPolySupport
