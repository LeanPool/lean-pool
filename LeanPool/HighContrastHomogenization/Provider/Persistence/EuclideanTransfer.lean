/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Persistence.AdaptedPersistence
public import LeanPool.HighContrastHomogenization.Provider.Persistence.TransferGauge
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.PositiveGapClosure
public import LeanPool.HighContrastHomogenization.Geometry.OperatorOrder

/-!
# High-contrast homogenization: Provider.Persistence.EuclideanTransfer

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The Euclidean transfer of the entry mean

The comparison between adapted and Euclidean cubes compares a Euclidean annealed
block with an adapted mean up to an error measured in units of the reference
block `𝐄`.  This file turns two such comparisons, read on the two distinct strict
generation chains of the forward and of the reverse comparison, into the
two-sided near-isometry `e.response.transfer.block.comparison` and a bound on the
Euclidean imbalance after the transfer.

The mechanism is one congruence and one rearrangement.  The congruence is the
entry ratio `Λ_t = |(E_t^q)^{-1/2}𝐄(E_t^q)^{-1/2}|`, one of the normalization
constants of the transfer: it is exactly the least scalar with `𝐄 ≤ Λ_t E_t^q`,
so an error `c𝐄` whose congruenced size `cΛ_t` is below a tolerance `η` is an
error below `ηE_t^q`.  The forward comparison then reads as the upper Euclidean
comparison.

The reverse comparison is one-sided in the wrong direction: it bounds the
adapted mean at the auxiliary scale by the Euclidean block.  The persistence
clause at that scale turns it into a lower bound for the Euclidean block in terms
of the entry mean, at the cost of the factor `(1+δ_ad)^d`, which is the lower
Euclidean comparison.  The tolerance conditions `e.response.transfer.tolerances`
were chosen exactly so that the two one-sided bounds close up into the symmetric
sandwich.

The last step is `e.global.selection.metric.comparison` at the sandwich: the Euclidean
block is positive definite because it dominates a positive multiple of the entry
mean — the Euclidean cube is not contained in the window, so this, and not the
window estimate, is the route to its definedness.
-/

namespace HCPolySupport
namespace HighContrast
namespace Persistence

open MeasureTheory

open scoped MatrixOrder Matrix

noncomputable section

variable {d : ℕ}

/-! ## The reference block measured against a positive block -/

/-- **The entry ratio is a Loewner bound.**  The scalar size
`blockSize E F = |F^{-1/2}EF^{-1/2}|` is the least nonnegative `t` with
`E ≤ tF`, so in particular it is one. -/
theorem toFullBlockMat_le_blockSize_smul {E F : BlockMat d} (hE : IsSymmetricBlockMat E)
    (hEpd : Book.Ch02.BlockPosDef E) (hF : IsSymmetricBlockMat F)
    (hFpd : Book.Ch02.BlockPosDef F) :
    toFullBlockMat E ≤ blockSize E F • toFullBlockMat F := by
  have hEfull := posDef_toFullBlockMat hE hEpd
  rw [blockSize_eq_relSize hE hF hFpd hEfull.posSemidef]
  exact le_relSize_smul hEfull.posSemidef (posDef_toFullBlockMat hF hFpd)

/-- **An error in units of the reference block, congruenced by a positive
block.**  A dilation `c𝐄` of the reference block whose congruenced size `cΛ` is
below `η` is below `ηF`. -/
theorem toFullBlockMat_blockScale_le_smul {E F : BlockMat d} (hE : IsSymmetricBlockMat E)
    (hEpd : Book.Ch02.BlockPosDef E) (hF : IsSymmetricBlockMat F)
    (hFpd : Book.Ch02.BlockPosDef F) {c eta : ℝ} (hc : 0 ≤ c)
    (hgap : c * blockSize E F ≤ eta) :
    toFullBlockMat (blockScale c E) ≤ eta • toFullBlockMat F := by
  rw [toFullBlockMat_blockScale]
  calc c • toFullBlockMat E ≤ c • (blockSize E F • toFullBlockMat F) :=
        smul_le_smul_of_le hc (toFullBlockMat_le_blockSize_smul hE hEpd hF hFpd)
    _ = (c * blockSize E F) • toFullBlockMat F := smul_smul _ _ _
    _ ≤ eta • toFullBlockMat F :=
        smul_le_smul_of_le_right (posDef_toFullBlockMat hF hFpd).posSemidef hgap

/-- Enlarging the scalar of a dilation of a positive block preserves a Loewner
upper bound. -/
theorem blockMatLoewnerLE_blockScale_mono {A B : BlockMat d} (hA : IsSymmetricBlockMat A)
    (hB : IsSymmetricBlockMat B) (hBpd : Book.Ch02.BlockPosDef B) {c₁ c₂ : ℝ}
    (hc : c₁ ≤ c₂) (h : BlockMatLoewnerLE A (blockScale c₁ B)) :
    BlockMatLoewnerLE A (blockScale c₂ B) := by
  refine blockMatLoewnerLE_of_le ?_
  rw [toFullBlockMat_blockScale]
  refine le_trans ?_
    (smul_le_smul_of_le_right (posDef_toFullBlockMat hB hBpd).posSemidef hc)
  have h' := le_of_blockMatLoewnerLE hA (isSymmetricBlockMat_blockScale c₁ hB) h
  rwa [toFullBlockMat_blockScale] at h'

/-! ## The two absorptions -/

/-- **The upper absorption**, giving the upper Euclidean comparison: an adapter
comparison `A ≤ B + c𝐄` whose error is below `ηB` reads as `A ≤ (1+η)B`. -/
theorem blockMatLoewnerLE_one_add {A B E : BlockMat d} (hA : IsSymmetricBlockMat A)
    (hB : IsSymmetricBlockMat B) (hE : IsSymmetricBlockMat E) {c eta : ℝ}
    (hsub : BlockMatLoewnerLE (blockSub A B) (blockScale c E))
    (herr : toFullBlockMat (blockScale c E) ≤ eta • toFullBlockMat B) :
    BlockMatLoewnerLE A (blockScale (1 + eta) B) := by
  have hsub' : toFullBlockMat A - toFullBlockMat B ≤ eta • toFullBlockMat B := by
    rw [← Recurrence.toFullBlockMat_blockSub]
    exact le_trans (le_of_blockMatLoewnerLE (isSymmetricBlockMat_blockSub hA hB)
      (isSymmetricBlockMat_blockScale c hE) hsub) herr
  refine blockMatLoewnerLE_of_le ?_
  rw [toFullBlockMat_blockScale]
  refine Matrix.le_iff.mpr ?_
  have hrw : (1 + eta) • toFullBlockMat B - toFullBlockMat A =
      eta • toFullBlockMat B - (toFullBlockMat A - toFullBlockMat B) := by
    rw [add_smul, one_smul]; abel
  rw [hrw]
  exact Matrix.le_iff.mp hsub'

/-- **The lower absorption**, giving the lower Euclidean comparison: an adapter
comparison `C ≤ A + c𝐄` in the wrong direction, whose error is below `η₋B`,
becomes a lower bound for `A` once the persistence clause `B ≤ ϱ C` is available.
Rearranging gives `(ϱ^{-1} - η₋)B ≤ A`, and the tolerance conditions
`e.response.transfer.tolerances` weaken the scalar to the symmetric one. -/
theorem blockMatLoewnerLE_one_sub {A B C E : BlockMat d} (hA : IsSymmetricBlockMat A)
    (hB : IsSymmetricBlockMat B) (hC : IsSymmetricBlockMat C) (hE : IsSymmetricBlockMat E)
    (hBpd : Book.Ch02.BlockPosDef B) {c etaMinus ratio eta : ℝ} (hratio : 0 < ratio)
    (hsub : BlockMatLoewnerLE (blockSub C A) (blockScale c E))
    (herr : toFullBlockMat (blockScale c E) ≤ etaMinus • toFullBlockMat B)
    (hpers : BlockMatLoewnerLE B (blockScale ratio C))
    (htol : eta ≤ ratio⁻¹ - etaMinus) :
    BlockMatLoewnerLE (blockScale eta B) A := by
  have hsub' : toFullBlockMat C - toFullBlockMat A ≤ etaMinus • toFullBlockMat B := by
    rw [← Recurrence.toFullBlockMat_blockSub]
    exact le_trans (le_of_blockMatLoewnerLE (isSymmetricBlockMat_blockSub hC hA)
      (isSymmetricBlockMat_blockScale c hE) hsub) herr
  have hpers' : toFullBlockMat B ≤ ratio • toFullBlockMat C := by
    have h := le_of_blockMatLoewnerLE hB (isSymmetricBlockMat_blockScale ratio hC) hpers
    rwa [toFullBlockMat_blockScale] at h
  -- the entry mean, from below, in terms of the Euclidean block and itself
  have hchain : toFullBlockMat B ≤
      ratio • toFullBlockMat A + (ratio * etaMinus) • toFullBlockMat B := by
    refine le_trans hpers' (Matrix.le_iff.mpr ?_)
    have hscaled : ratio • (toFullBlockMat C - toFullBlockMat A) ≤
        ratio • (etaMinus • toFullBlockMat B) := smul_le_smul_of_le hratio.le hsub'
    have hrw : ratio • toFullBlockMat A + (ratio * etaMinus) • toFullBlockMat B -
        ratio • toFullBlockMat C =
          ratio • (etaMinus • toFullBlockMat B) -
            ratio • (toFullBlockMat C - toFullBlockMat A) := by
      rw [smul_sub, smul_smul]; abel
    rw [hrw]
    exact Matrix.le_iff.mp hscaled
  -- the rearrangement
  have hrear : (1 - ratio * etaMinus) • toFullBlockMat B ≤ ratio • toFullBlockMat A := by
    refine Matrix.le_iff.mpr ?_
    have hrw : ratio • toFullBlockMat A - (1 - ratio * etaMinus) • toFullBlockMat B =
        ratio • toFullBlockMat A + (ratio * etaMinus) • toFullBlockMat B -
          toFullBlockMat B := by
      rw [sub_smul, one_smul]; abel
    rw [hrw]
    exact Matrix.le_iff.mp hchain
  have hdiv : (ratio⁻¹ * (1 - ratio * etaMinus)) • toFullBlockMat B ≤ toFullBlockMat A := by
    have h := smul_inv_le_of_le_smul hratio hrear
    rwa [smul_smul] at h
  have heq : ratio⁻¹ * (1 - ratio * etaMinus) = ratio⁻¹ - etaMinus := by
    rw [mul_sub, mul_one, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hratio), one_mul]
  rw [heq] at hdiv
  refine blockMatLoewnerLE_of_le ?_
  rw [toFullBlockMat_blockScale]
  exact le_trans
    (smul_le_smul_of_le_right (posDef_toFullBlockMat hB hBpd).posSemidef htol) hdiv

/-! ## The Euclidean imbalance -/

/-! ## The Euclidean transfer -/

end

end Persistence
end HighContrast
end HCPolySupport
