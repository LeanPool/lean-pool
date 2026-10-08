/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.UnitRangeBlockCutoff
public import LeanPool.HighContrastHomogenization.Annealed.WitnessBlock

/-!
# High-contrast homogenization: Provider.Quenched.UnitRangeNormalizedTransfer

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Normalized coordinates and the Loewner order

The concentration estimate bounds the entries of a doubled block, and the
reassembly turns entrywise bounds into a Loewner bound against a reference block
dominating the identity form.  The renormalization argument needs the bound
against the reference block of the coarse-ellipticity datum instead, and that
block carries no coercivity constant.

The printed argument avoids the difficulty by working in normalized coordinates
throughout: it bounds the entries of the normalized block and reads the result
against the identity, which un-normalizes to the reference block.  This file
supplies the missing step, that conjugation by the square root of the reference
block preserves the Loewner order, and the entrywise consequence the
renormalization argument consumes.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open scoped MatrixOrder Matrix

noncomputable section

variable {d : ℕ}

/-! ## The scaled identity block -/

theorem blockMatEntry_scaledBlockIdentity (c : ℝ) (α β : BlockCoord d) :
    blockMatEntry (scaledBlockIdentity d c) α β = if α = β then c else 0 := by
  cases α <;> cases β <;>
    simp [scaledBlockIdentity, blockMatEntry, Matrix.one_apply, Matrix.smul_apply]

theorem toFullBlockMat_scaledBlockIdentity (c : ℝ) :
    toFullBlockMat (scaledBlockIdentity d c)
      = c • (1 : Matrix (BlockCoord d) (BlockCoord d) ℝ) := by
  ext α β
  rw [toFullBlockMat_eq_blockMatEntry, blockMatEntry_scaledBlockIdentity]
  simp [Matrix.one_apply]

/-- The quadratic form of the scaled identity block. -/
theorem blockVecDot_scaledBlockIdentity (c : ℝ) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul (scaledBlockIdentity d c) X)
      = c * ∑ α : BlockCoord d, toFullBlockVec X α * toFullBlockVec X α := by
  classical
  rw [blockVecDot_blockMatVecMul_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.sum_eq_single α]
  · rw [blockMatEntry_scaledBlockIdentity, ite_eq_left rfl]
    ring
  · intro β _ hβ
    rw [blockMatEntry_scaledBlockIdentity, ite_eq_right (Ne.symm hβ)]
    ring
  · intro hcon
    exact absurd (Finset.mem_univ α) hcon

theorem isSymmetricBlockMat_scaledBlockIdentity (c : ℝ) :
    IsSymmetricBlockMat (scaledBlockIdentity d c) := by
  have hrw : scaledBlockIdentity d c
      = ofFullBlockMat (c • (1 : Matrix (BlockCoord d) (BlockCoord d) ℝ)) := by
    refine toFullBlockMat_injective ?_
    rw [toFullBlockMat_scaledBlockIdentity, toFullBlockMat_ofFullBlockMat]
  rw [hrw]
  refine isSymmetricBlockMat_of_isSymm ?_
  simp [Matrix.IsSymm, Matrix.transpose_smul, Matrix.transpose_one]

/-! ## Conjugation preserves the Loewner order -/

/-- **The normalized block transfers the Loewner order.**  A bound of the
normalized block against the scaled identity is a bound of the block itself
against the scaled reference block: conjugation by the square root of the
reference block preserves the order. -/
theorem blockMatLoewnerLE_blockScale_of_normalizedBlock {D E : BlockMat d}
    (hD : IsSymmetricBlockMat D) (hE : IsSymmetricBlockMat E)
    (hEpd : Book.Ch02.BlockPosDef E) {kappa : ℝ}
    (h : BlockMatLoewnerLE (normalizedBlock D E) (scaledBlockIdentity d kappa)) :
    BlockMatLoewnerLE D (blockScale kappa E) := by
  set T : Matrix (BlockCoord d) (BlockCoord d) ℝ := toFullBlockMat E with hTdef
  have hT : T.PosDef := posDef_toFullBlockMat hE hEpd
  set R : Matrix (BlockCoord d) (BlockCoord d) ℝ := matSqrt T with hRdef
  have hR : R.PosDef := posDef_matSqrt hT
  have hRR : R * R = T := (matSqrt_spec hT.posSemidef).2
  have hRherm : Rᴴ = R := hR.isHermitian
  have hSeq : matSqrt T⁻¹ = R⁻¹ := by rw [hRdef]; exact matSqrt_inv hT
  have hRunit : IsUnit R := by
    rw [hRdef]
    exact isUnit_matSqrt hT
  have hRdet : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det R).mp hRunit
  have hRinvR : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R hRdet
  have hRinvR' : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R hRdet
  -- the flattened normalized block
  have hnormflat : toFullBlockMat (normalizedBlock D E)
      = R⁻¹ * toFullBlockMat D * R⁻¹ := by
    rw [Recurrence.toFullBlockMat_normalizedBlock, ← hTdef, hSeq]
  have hnormsymm : IsSymmetricBlockMat (normalizedBlock D E) := by
    refine isSymmetricBlockMat_of_isSymm ?_
    rw [← hTdef, hSeq]
    have hDsymm : (toFullBlockMat D).IsSymm := isSymm_toFullBlockMat hD
    have hRinvsymm : (R⁻¹).IsSymm := by
      rw [Matrix.IsSymm, ← hSeq]
      exact transpose_matSqrt_inv hT
    rw [Matrix.IsSymm, Matrix.transpose_mul, Matrix.transpose_mul, hRinvsymm, hDsymm,
      Matrix.mul_assoc]
  -- the flattened hypothesis
  have hflat : toFullBlockMat (normalizedBlock D E)
      ≤ toFullBlockMat (scaledBlockIdentity d kappa) :=
    le_of_blockMatLoewnerLE hnormsymm (isSymmetricBlockMat_scaledBlockIdentity kappa) h
  rw [Matrix.le_iff, toFullBlockMat_scaledBlockIdentity, hnormflat] at hflat
  -- conjugate by the square root
  have hconj := hflat.conjTranspose_mul_mul_same R
  have hexpand : Rᴴ * (kappa • (1 : Matrix (BlockCoord d) (BlockCoord d) ℝ)
        - R⁻¹ * toFullBlockMat D * R⁻¹) * R
      = kappa • T - toFullBlockMat D := by
    rw [hRherm, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, hRR]
    congr 1
    calc R * (R⁻¹ * toFullBlockMat D * R⁻¹) * R
        = (R * R⁻¹) * toFullBlockMat D * (R⁻¹ * R) := by
          simp only [Matrix.mul_assoc]
      _ = toFullBlockMat D := by rw [hRinvR, hRinvR', Matrix.one_mul, Matrix.mul_one]
  rw [hexpand] at hconj
  refine blockMatLoewnerLE_of_le ?_
  rw [Matrix.le_iff, toFullBlockMat_blockScale, ← hTdef]
  exact hconj

/-! ## The entrywise consequence -/

end

end Quenched
end HighContrast
end HCPolySupport
