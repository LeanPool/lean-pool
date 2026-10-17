/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Block
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.BlockCoarseMatrix
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.BlockFormalism.EllipticBounds
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.SharpBlockBounds.DiagonalSandwich

/-!
# CompletedSquares

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: the two completed-square formulas for the doubled response

This file proves local versions of the displays `e.bfJ.magic` and `e.bfJ.magic2` of
ABK26:

* `bfJ(U,P,Q) = 1/2 P.  (bfA - bfA_*) P
                 + 1/2 (Q - bfA_* P). bfA_*^{-1} (Q - bfA_* P)`;
* `bfJ(U,P,Q) = 1/2 Q.  (bfA_*^{-1} - bfA^{-1}) Q
                 + 1/2 (P - bfA^{-1} Q). bfA (P - bfA^{-1} Q)`.

Both are pure block-matrix algebra on top of CoarseGraining's public splitting

`bfJ(U,P,Q) = 1/2 P . bfA P + 1/2 Q . bfA_*^{-1} Q - P . Q`

(`Homogenization.Book.Ch02.BlockCoarseMatrixTheory.doubled_response_splitting`),
using only symmetry of `bfA` and `bfA_*^{-1}` and the two-sided inverse
relations between `bfA_*` and `bfA_*^{-1}`.

## Notation for differences of block matrices

`BlockMat d` is a four-field structure without a `Sub` instance, so
CoarseGraining writes the difference of two block matrices as `ofFullBlockMat
(toFullBlockMat A - toFullBlockMat B)`; the quadratic form of such a difference
splits by `Homogenization.blockVecDot_blockMatVecMul_ofFullBlockMat_sub`.  That
is the spelling used below.

## The inverse of `bfA`

CoarseGraining names `bfA_*^{-1}(U;a) = blockReflect (bfA(U;a))` and
`bfA_*(U;a) = blockMatInv (bfA_*^{-1}(U;a))` but does not name `bfA^{-1}`.  It
is introduced here as `coarseBlockMatrixInv`, defined by the same generic block
inverse `blockMatInv`, and identified with `blockReflect (bfA_*(U;a))`; the
two-sided inverse identities then follow from CoarseGraining's
`starred_left_inverse` and `starred_right_inverse` because `blockReflect` is a
multiplicative involution.
-/

namespace Algsuperdiff.Section3.Provider.Block

open HCPolySupport HCPolySupport.Book.Ch02

variable {d : ℕ}

/-! ## Bilinearity helpers for the doubled pairing -/

private theorem blockVecDot_sub_left (X Y Z : BlockVec d) :
    blockVecDot (X - Y) Z = blockVecDot X Z - blockVecDot Y Z := by
  have hneg : blockVecDot (-Y) Z = -blockVecDot Y Z := by
    simpa using blockVecDot_smul_left (-1) Y Z
  rw [sub_eq_add_neg, blockVecDot_add_left, hneg, sub_eq_add_neg]

private theorem blockMatVecMul_sub (A : BlockMat d) (X Y : BlockVec d) :
    blockMatVecMul A (X - Y) = blockMatVecMul A X - blockMatVecMul A Y := by
  have hneg : blockMatVecMul A (-Y) = -blockMatVecMul A Y := by
    simpa using blockMatVecMul_smul A (-1) Y
  rw [sub_eq_add_neg, blockMatVecMul_add, hneg, sub_eq_add_neg]

/-! ## `blockReflect` is a multiplicative involution -/

private theorem blockMatMul_blockReflect (A B : BlockMat d) :
    blockMatMul (blockReflect A) (blockReflect B) = blockReflect (blockMatMul A B) := by
  refine blockMat_ext ?_ ?_ ?_ ?_ <;> simp [blockMatMul, add_comm]

private theorem blockReflect_blockIdentity :
    blockReflect (blockIdentity d) = blockIdentity d := by
  refine blockMat_ext ?_ ?_ ?_ ?_ <;> rfl

private theorem toFullBlockMat_blockMatMul (A B : BlockMat d) :
    toFullBlockMat (blockMatMul A B) = toFullBlockMat A * toFullBlockMat B := by
  ext alpha beta
  cases alpha <;> cases beta <;>
    simp [blockMatMul, toFullBlockMat, Matrix.mul_apply, Fintype.sum_sum_type]

private theorem toFullBlockMat_blockIdentity :
    toFullBlockMat (blockIdentity d) = 1 := by
  ext alpha beta
  cases alpha <;> cases beta <;>
    simp [blockIdentity, blockDiag, toFullBlockMat, Matrix.one_apply]

/-! ## The inverse of the coarse block matrix -/

/-- The inverse `bfA^{-1}(U; a)` of the coarse block matrix, defined by the same
generic doubled inverse `blockMatInv` that CoarseGraining uses for `bfA_*(U;
a)`. -/
noncomputable def coarseBlockMatrixInv (U : Domain d) (a : CoeffOn U) : BlockMat d :=
  blockMatInv (Book.Ch02.coarseBlockMatrix U a)

private theorem blockReflect_coarseStarredBlockMatrixInv (U : Domain d) (a : CoeffOn U) :
    blockReflect (Book.Ch02.coarseStarredBlockMatrixInv U a) = Book.Ch02.coarseBlockMatrix U a := by
  rw [Book.Ch02.coarseStarredBlockMatrixInv_eq_blockReflect, blockReflect_blockReflect]

private theorem blockMatMul_blockReflect_coarseStarredBlockMatrix_left
    (U : Domain d) (a : CoeffOn U) :
    blockMatMul (blockReflect (coarseStarredBlockMatrix U a)) (Book.Ch02.coarseBlockMatrix U a) =
      blockIdentity d := by
  have hstar := (blockCoarseMatrixTheory U a).starred_left_inverse
  calc
    blockMatMul (blockReflect (coarseStarredBlockMatrix U a)) (Book.Ch02.coarseBlockMatrix U a)
        = blockMatMul (blockReflect (coarseStarredBlockMatrix U a))
            (blockReflect (Book.Ch02.coarseStarredBlockMatrixInv U a)) := by
          rw [blockReflect_coarseStarredBlockMatrixInv]
    _ = blockReflect
          (blockMatMul (coarseStarredBlockMatrix U a)
            (Book.Ch02.coarseStarredBlockMatrixInv U a)) := blockMatMul_blockReflect _ _
    _ = blockReflect (blockIdentity d) := by rw [hstar]
    _ = blockIdentity d := blockReflect_blockIdentity

private theorem blockMatMul_blockReflect_coarseStarredBlockMatrix_right
    (U : Domain d) (a : CoeffOn U) :
    blockMatMul (Book.Ch02.coarseBlockMatrix U a) (blockReflect (coarseStarredBlockMatrix U a)) =
      blockIdentity d := by
  have hstar := (blockCoarseMatrixTheory U a).starred_right_inverse
  calc
    blockMatMul (Book.Ch02.coarseBlockMatrix U a) (blockReflect (coarseStarredBlockMatrix U a))
        = blockMatMul (blockReflect (Book.Ch02.coarseStarredBlockMatrixInv U a))
            (blockReflect (coarseStarredBlockMatrix U a)) := by
          rw [blockReflect_coarseStarredBlockMatrixInv]
    _ = blockReflect
          (blockMatMul (Book.Ch02.coarseStarredBlockMatrixInv U a)
            (coarseStarredBlockMatrix U a)) := blockMatMul_blockReflect _ _
    _ = blockReflect (blockIdentity d) := by rw [hstar]
    _ = blockIdentity d := blockReflect_blockIdentity

/-- `bfA^{-1}(U; a)` is the block reflection of `bfA_*(U; a)`, mirroring
CoarseGraining's identity `bfA_*^{-1}(U; a) = blockReflect (bfA(U; a))`. -/
theorem coarseBlockMatrixInv_eq_blockReflect (U : Domain d) (a : CoeffOn U) :
    coarseBlockMatrixInv U a = blockReflect (coarseStarredBlockMatrix U a) := by
  have hleft :
      toFullBlockMat (blockReflect (coarseStarredBlockMatrix U a)) *
          toFullBlockMat (Book.Ch02.coarseBlockMatrix U a) = 1 := by
    rw [← toFullBlockMat_blockMatMul,
      blockMatMul_blockReflect_coarseStarredBlockMatrix_left,
      toFullBlockMat_blockIdentity]
  have hinv :
      (toFullBlockMat (Book.Ch02.coarseBlockMatrix U a))⁻¹ =
        toFullBlockMat (blockReflect (coarseStarredBlockMatrix U a)) :=
    Matrix.inv_eq_left_inv hleft
  calc
    coarseBlockMatrixInv U a
        = ofFullBlockMat ((toFullBlockMat (Book.Ch02.coarseBlockMatrix U a))⁻¹) := rfl
    _ = ofFullBlockMat (toFullBlockMat (blockReflect (coarseStarredBlockMatrix U a))) := by
          rw [hinv]
    _ = blockReflect (coarseStarredBlockMatrix U a) := ofFullBlockMat_toFullBlockMat _

/-- `bfA(U; a)` cancels `bfA^{-1}(U; a)` on doubled loads. -/
theorem blockMatVecMul_coarseBlockMatrix_coarseBlockMatrixInv
    (U : Domain d) (a : CoeffOn U) (X : BlockVec d) :
    blockMatVecMul (Book.Ch02.coarseBlockMatrix U a)
        (blockMatVecMul (coarseBlockMatrixInv U a) X) = X := by
  rw [coarseBlockMatrixInv_eq_blockReflect, ← blockMatVecMul_blockMatMul,
    blockMatMul_blockReflect_coarseStarredBlockMatrix_right, blockMatVecMul_blockIdentity]

/-! ## `e.bfJ.magic2`: completing the square in the potential variable -/

/-- Second completed-square formula `e.bfJ.magic2` for the doubled response. -/
theorem doubledResponseJ_eq_primal_completed_square (U : Domain d) (a : CoeffOn U)
    (P Q : BlockVec d) :
    doubledResponseJ U a P Q =
      (1 / 2 : ℝ) *
          blockVecDot Q
            (blockMatVecMul
              (ofFullBlockMat
                (toFullBlockMat (Book.Ch02.coarseStarredBlockMatrixInv U a) -
                  toFullBlockMat (coarseBlockMatrixInv U a))) Q) +
        (1 / 2 : ℝ) *
          blockVecDot (P - blockMatVecMul (coarseBlockMatrixInv U a) Q)
            (blockMatVecMul (Book.Ch02.coarseBlockMatrix U a)
              (P - blockMatVecMul (coarseBlockMatrixInv U a) Q)) := by
  have hsplit := (blockCoarseMatrixTheory U a).doubled_response_splitting P Q
  have hdiff :
      blockVecDot Q
          (blockMatVecMul
            (ofFullBlockMat
              (toFullBlockMat (Book.Ch02.coarseStarredBlockMatrixInv U a) -
                toFullBlockMat (coarseBlockMatrixInv U a))) Q) =
        blockVecDot Q (blockMatVecMul (Book.Ch02.coarseStarredBlockMatrixInv U a) Q) -
          blockVecDot Q (blockMatVecMul (coarseBlockMatrixInv U a) Q) :=
    blockVecDot_blockMatVecMul_ofFullBlockMat_sub _ _ Q
  have hcross :
      blockVecDot (blockMatVecMul (coarseBlockMatrixInv U a) Q)
          (blockMatVecMul (Book.Ch02.coarseBlockMatrix U a) P) =
        blockVecDot P Q := by
    rw [blockVecDot_blockMatVecMul_comm_of_isSymmetricBlockMat
        (isSymmetricBlockMat_coarseBlockMatrix U a)
        (blockMatVecMul (coarseBlockMatrixInv U a) Q) P,
      blockMatVecMul_coarseBlockMatrix_coarseBlockMatrixInv]
  have hload :
      blockMatVecMul (Book.Ch02.coarseBlockMatrix U a)
          (P - blockMatVecMul (coarseBlockMatrixInv U a) Q) =
        blockMatVecMul (Book.Ch02.coarseBlockMatrix U a) P - Q := by
    rw [blockMatVecMul_sub, blockMatVecMul_coarseBlockMatrix_coarseBlockMatrixInv]
  have hsquare :
      blockVecDot (P - blockMatVecMul (coarseBlockMatrixInv U a) Q)
          (blockMatVecMul (Book.Ch02.coarseBlockMatrix U a)
            (P - blockMatVecMul (coarseBlockMatrixInv U a) Q)) =
        blockVecDot P (blockMatVecMul (Book.Ch02.coarseBlockMatrix U a) P) -
            2 * blockVecDot P Q +
          blockVecDot Q (blockMatVecMul (coarseBlockMatrixInv U a) Q) := by
    rw [hload, blockVecDot_sub_right, blockVecDot_sub_left, blockVecDot_sub_left,
      hcross, blockVecDot_comm (blockMatVecMul (coarseBlockMatrixInv U a) Q) Q]
    ring
  rw [hsplit, hdiff, hsquare]
  ring

end Algsuperdiff.Section3.Provider.Block
