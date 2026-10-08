/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.UnitRangeNormalizedTransfer

/-!
# High-contrast homogenization: Provider.Quenched.UnitRangeNormalizedLocality

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The normalized block: locality, entry bounds, positivity

The renormalization argument applies the concentration estimate to the entries of
the normalized coarse block.  Three properties of that block are needed before
the estimate can be used, and all three follow from the flattening
`toFullBlockMat (normalizedBlock H E) = E'^{-1/2} · toFullBlockMat H · E'^{-1/2}`.

Locality: each entry of the normalized block is a fixed finite linear
combination of the entries of the block itself, so it is measurable for the local
sigma-field of the cell.  Positivity: conjugation by an invertible symmetric
matrix preserves positive definiteness.  Entry bounds: a positive block below the
scaled identity has entries bounded by the scale, which is what makes the cutoff
of the previous file inactive on the burnt-in event.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open scoped MatrixOrder Matrix

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## The entries of the normalized block -/

/-- Each entry of the normalized block is a fixed finite linear combination of
the entries of the block. -/
theorem blockMatEntry_normalizedBlock_eq_sum (H E : BlockMat d) (α β : BlockCoord d) :
    blockMatEntry (normalizedBlock H E) α β =
      ∑ delta : BlockCoord d, ∑ gamma : BlockCoord d,
        matSqrt (toFullBlockMat E)⁻¹ α gamma *
          (blockMatEntry H gamma delta * matSqrt (toFullBlockMat E)⁻¹ delta β) := by
  rw [← toFullBlockMat_eq_blockMatEntry, Recurrence.toFullBlockMat_normalizedBlock]
  simp only [Matrix.mul_apply, Finset.sum_mul, toFullBlockMat_eq_blockMatEntry]
  refine Finset.sum_congr rfl fun delta _ => ?_
  refine Finset.sum_congr rfl fun gamma _ => ?_
  ring

/-- **Locality of the normalized coarse block.**  Every entry of the normalized
coarse block of a standard aligned cube is measurable for the local sigma-field
of that cube. -/
theorem measurable_blockMatEntry_normalizedBlock_coarseBlock_standardCell
    (E : BlockMat d) (k : ℤ) (w : Fin d → ℤ) (α β : BlockCoord d) :
    @Measurable (CoeffSpace d) ℝ (coeffSigma d (standardCell d k w)) _
      (fun a => blockMatEntry
        (normalizedBlock (coarseBlock (standardCell d k w) a) E) α β) := by
  let : MeasurableSpace (CoeffSpace d) := coeffSigma d (standardCell d k w)
  have hrw : (fun a : CoeffSpace d => blockMatEntry
      (normalizedBlock (coarseBlock (standardCell d k w) a) E) α β)
      = fun a : CoeffSpace d => ∑ delta : BlockCoord d, ∑ gamma : BlockCoord d,
          matSqrt (toFullBlockMat E)⁻¹ α gamma *
            (blockMatEntry (coarseBlock (standardCell d k w) a) gamma delta *
              matSqrt (toFullBlockMat E)⁻¹ delta β) := by
    funext a
    exact blockMatEntry_normalizedBlock_eq_sum _ E α β
  rw [hrw]
  refine Finset.measurable_sum _ fun delta _ => Finset.measurable_sum _ fun gamma _ => ?_
  exact ((measurable_blockMatEntry_coarseBlock_standardCell k w gamma delta).mul_const
    (matSqrt (toFullBlockMat E)⁻¹ delta β)).const_mul _

/-! ## Positivity of the normalized block -/

/-- **Conjugation preserves positivity.**  The normalized block of a positive
block is positive. -/
theorem blockPosDef_normalizedBlock {H E : BlockMat d} (hH : IsSymmetricBlockMat H)
    (hHpd : Book.Ch02.BlockPosDef H) (hE : IsSymmetricBlockMat E)
    (hEpd : Book.Ch02.BlockPosDef E) :
    Book.Ch02.BlockPosDef (normalizedBlock H E) := by
  set T : Matrix (BlockCoord d) (BlockCoord d) ℝ := toFullBlockMat E with hTdef
  have hT : T.PosDef := posDef_toFullBlockMat hE hEpd
  have hHfull : (toFullBlockMat H).PosDef := posDef_toFullBlockMat hH hHpd
  set S : Matrix (BlockCoord d) (BlockCoord d) ℝ := matSqrt T⁻¹ with hSdef
  have hS : S.PosDef := by
    rw [hSdef]
    exact posDef_matSqrt hT.inv
  have hSherm : Sᴴ = S := hS.isHermitian
  have hSunit : IsUnit S := by
    rw [hSdef]
    exact isUnit_matSqrt hT.inv
  have hSdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hSunit
  have hSinj : Function.Injective S.mulVec := by
    intro x y hxy
    have hstep : S⁻¹ *ᵥ (S *ᵥ x) = S⁻¹ *ᵥ (S *ᵥ y) := by
      show S⁻¹ *ᵥ S.mulVec x = S⁻¹ *ᵥ S.mulVec y
      rw [hxy]
    rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul S hSdet,
      Matrix.one_mulVec, Matrix.one_mulVec] at hstep
  have hflat : toFullBlockMat (normalizedBlock H E) = S * toFullBlockMat H * S := by
    rw [Recurrence.toFullBlockMat_normalizedBlock, ← hTdef, ← hSdef]
  have hsymm : IsSymmetricBlockMat (normalizedBlock H E) := by
    refine isSymmetricBlockMat_of_isSymm ?_
    rw [← hTdef, ← hSdef]
    have hSsymm : S.IsSymm := by
      rw [Matrix.IsSymm, ← Matrix.conjTranspose_eq_transpose_of_trivial, hSherm]
    have hHsymm : (toFullBlockMat H).IsSymm := isSymm_toFullBlockMat hH
    rw [Matrix.IsSymm, Matrix.transpose_mul, Matrix.transpose_mul, hSsymm, hHsymm,
      Matrix.mul_assoc]
  refine (blockPosDef_iff_posDef hsymm).mpr ?_
  rw [hflat]
  have hconj := hHfull.conjTranspose_mul_mul_same (B := S) hSinj
  rwa [hSherm] at hconj

/-! ## Entry bounds from a Loewner bound -/

theorem blockEntrySum_scaledBlockIdentity (c : ℝ) :
    blockEntrySum (scaledBlockIdentity d c) = 2 * (d : ℝ) * |c| := by
  classical
  rw [blockEntrySum]
  have hrow : ∀ α : BlockCoord d,
      ∑ β : BlockCoord d, |blockMatEntry (scaledBlockIdentity d c) α β| = |c| := by
    intro α
    rw [Finset.sum_eq_single α]
    · rw [blockMatEntry_scaledBlockIdentity, ite_eq_left rfl]
    · intro β _ hβ
      rw [blockMatEntry_scaledBlockIdentity, ite_eq_right (Ne.symm hβ), abs_zero]
    · intro hcon
      exact absurd (Finset.mem_univ α) hcon
  rw [Finset.sum_congr rfl fun α _ => hrow α, Finset.sum_const, card_blockCoord,
    nsmul_eq_mul]
  push_cast
  ring

/-- **Entry bounds for a positive block below the scaled identity.** -/
theorem abs_blockMatEntry_le_of_blockMatLoewnerLE_scaledBlockIdentity {M : BlockMat d}
    {c : ℝ} (hsymm : IsSymmetricBlockMat M)
    (hnn : ∀ X : BlockVec d, 0 ≤ blockVecDot X (blockMatVecMul M X))
    (hle : BlockMatLoewnerLE M (scaledBlockIdentity d c)) (α β : BlockCoord d) :
    |blockMatEntry M α β| ≤ 4 * (d : ℝ) * |c| := by
  have hdiag0 : ∀ gamma : BlockCoord d, 0 ≤ blockMatEntry M gamma gamma := by
    intro gamma
    rw [← blockBasis_pairing]
    exact hnn _
  have hdiagF : ∀ gamma : BlockCoord d,
      blockMatEntry M gamma gamma ≤
        blockMatEntry (scaledBlockIdentity d c) gamma gamma := by
    intro gamma
    have h := hle (blockBasis gamma)
    rw [blockBasis_pairing, blockBasis_pairing] at h
    linarith only [h]
  have hsum0 : 0 ≤ blockVecDot (blockBasis α + blockBasis β)
      (blockMatVecMul M (blockBasis α + blockBasis β)) := hnn _
  have hsumF : blockVecDot (blockBasis α + blockBasis β)
        (blockMatVecMul M (blockBasis α + blockBasis β)) ≤
      blockVecDot (blockBasis α + blockBasis β)
        (blockMatVecMul (scaledBlockIdentity d c) (blockBasis α + blockBasis β)) := by
    have h := hle (blockBasis α + blockBasis β)
    linarith only [h]
  have hbound := abs_blockMatEntry_le_of_bounds hsymm hdiag0 hdiagF hsum0 hsumF
  rw [blockEntrySum_scaledBlockIdentity] at hbound
  calc |blockMatEntry M α β| ≤ 2 * (2 * (d : ℝ) * |c|) := hbound
    _ = 4 * (d : ℝ) * |c| := by ring


/-! ## The converse transfer -/

/-- **The converse of the normalized transfer.**  A bound of the block against
the scaled reference block is a bound of the normalized block against the scaled
identity.  This is what makes the cutoff inactive on the burnt-in event. -/
theorem blockMatLoewnerLE_scaledBlockIdentity_of_blockScale {D E : BlockMat d}
    (hD : IsSymmetricBlockMat D) (hE : IsSymmetricBlockMat E)
    (hEpd : Book.Ch02.BlockPosDef E) {kappa : ℝ}
    (h : BlockMatLoewnerLE D (blockScale kappa E)) :
    BlockMatLoewnerLE (normalizedBlock D E) (scaledBlockIdentity d kappa) := by
  set T : Matrix (BlockCoord d) (BlockCoord d) ℝ := toFullBlockMat E with hTdef
  have hT : T.PosDef := posDef_toFullBlockMat hE hEpd
  set R : Matrix (BlockCoord d) (BlockCoord d) ℝ := matSqrt T with hRdef
  have hR : R.PosDef := posDef_matSqrt hT
  have hRR : R * R = T := (matSqrt_spec hT.posSemidef).2
  have hSeq : matSqrt T⁻¹ = R⁻¹ := by rw [hRdef]; exact matSqrt_inv hT
  have hSherm : (R⁻¹)ᴴ = R⁻¹ := by
    rw [← hSeq, Matrix.conjTranspose_eq_transpose_of_trivial]
    exact transpose_matSqrt_inv hT
  have hRunit : IsUnit R := by rw [hRdef]; exact isUnit_matSqrt hT
  have hRdet : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det R).mp hRunit
  have hRinvR : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R hRdet
  have hRinvR' : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R hRdet
  have hflat : toFullBlockMat D ≤ toFullBlockMat (blockScale kappa E) :=
    le_of_blockMatLoewnerLE hD (isSymmetricBlockMat_blockScale kappa hE) h
  rw [Matrix.le_iff, toFullBlockMat_blockScale, ← hTdef] at hflat
  have hconj := hflat.conjTranspose_mul_mul_same R⁻¹
  have hexpand : (R⁻¹)ᴴ * (kappa • T - toFullBlockMat D) * R⁻¹
      = kappa • (1 : Matrix (BlockCoord d) (BlockCoord d) ℝ)
        - R⁻¹ * toFullBlockMat D * R⁻¹ := by
    rw [hSherm, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_assoc]
    congr 2
    calc R⁻¹ * (T * R⁻¹) = R⁻¹ * (R * R * R⁻¹) := by rw [hRR]
      _ = (R⁻¹ * R) * (R * R⁻¹) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hRinvR, hRinvR', Matrix.one_mul]
  rw [hexpand] at hconj
  refine blockMatLoewnerLE_of_le ?_
  rw [Matrix.le_iff, toFullBlockMat_scaledBlockIdentity,
    Recurrence.toFullBlockMat_normalizedBlock, ← hTdef, hSeq]
  exact hconj

/-! ## Locality of the cutoff of a local block family -/

/-- **The cutoff of a local block family is local.**  The branch condition is a
finite conjunction of conditions on entries that are local. -/
theorem measurable_blockMatEntry_blockCutoff_of_local {U : Set (Vec d)} (B : ℝ)
    {H : CoeffSpace d → BlockMat d}
    (hH : ∀ alpha beta : BlockCoord d, @Measurable (CoeffSpace d) ℝ
      (coeffSigma d U) _ (fun a => blockMatEntry (H a) alpha beta))
    (α β : BlockCoord d) :
    @Measurable (CoeffSpace d) ℝ (coeffSigma d U) _
      (fun a => blockMatEntry (blockCutoff B (H a)) α β) := by
  classical
  let : MeasurableSpace (CoeffSpace d) := coeffSigma d U
  have hset : MeasurableSet
      {a : CoeffSpace d | ∀ alpha beta : BlockCoord d,
        |blockMatEntry (H a) alpha beta| ≤ B} := by
    have hrw : {a : CoeffSpace d | ∀ alpha beta : BlockCoord d,
        |blockMatEntry (H a) alpha beta| ≤ B}
        = ⋂ alpha : BlockCoord d, ⋂ beta : BlockCoord d,
            {a : CoeffSpace d | |blockMatEntry (H a) alpha beta| ≤ B} := by
      ext a
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    rw [hrw]
    exact MeasurableSet.iInter fun alpha => MeasurableSet.iInter fun beta =>
      measurableSet_le (continuous_abs.measurable.comp (hH alpha beta)) measurable_const
  have hfun : (fun a : CoeffSpace d => blockMatEntry (blockCutoff B (H a)) α β)
      = fun a : CoeffSpace d =>
          if ∀ alpha beta : BlockCoord d, |blockMatEntry (H a) alpha beta| ≤ B then
            blockMatEntry (H a) α β else 0 := by
    funext a
    exact blockMatEntry_blockCutoff B _ α β
  rw [hfun]
  exact Measurable.ite hset (hH α β) measurable_const

end

end Quenched
end HighContrast
end HCPolySupport
