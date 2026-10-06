/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.NormalizedBlockPositivity

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.NormalizedResponseExcess

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Normalized response bounded by block excess

The intrinsic normalization of the doubled response uses a load `P` with unit
quadratic energy in the constant comparison block and pairs it with the dual
load obtained by applying that block.  The doubled splitting then bounds both
quadratic terms by the same one-sided excess.  This formulation avoids choosing
coordinates for the positive square root and is stable under the affine and
constant-skew changes of variables used later.
-/

namespace HCPolySupport
namespace HighContrast

open Book.Ch02

open scoped MatrixOrder

noncomputable section

variable {d : ℕ}

private theorem coarseBlockMatrix_le_one_add_blockExcess_constant
    {U : Domain d} (a : CoeffOn U) {a0 : Mat d}
    (ha0 : (symmPart a0).PosDef) :
    BlockMatLoewnerLE (Book.Ch02.coarseBlockMatrix U a)
      (blockScale
        (1 + blockExcess (Book.Ch02.coarseBlockMatrix U a)
          (Book.Ch02.constantBlockMatrix a0))
        (Book.Ch02.constantBlockMatrix a0)) := by
  let A := Book.Ch02.coarseBlockMatrix U a
  let E := Book.Ch02.constantBlockMatrix a0
  have hAsym : IsSymmetricBlockMat A :=
    Book.Ch02.isSymmetricBlockMat_coarseBlockMatrix U a
  have hApd : BlockPosDef A :=
    (blockCoarseMatrixTheory U a).block_matrix_posDef
  have hApsd : (toFullBlockMat A).PosSemidef :=
    (posDef_toFullBlockMat hAsym hApd).posSemidef
  have hEsym : IsSymmetricBlockMat E := by
    simpa [E, Book.Ch02.constantBlockMatrix, blockMatrixOfCoeff] using
      isSymmetricBlockMat_blockMatrixOfCoeff a0
  have hEpd : BlockPosDef E := by
    simpa only [E] using
      blockPosDef_constantBlockMatrix_of_posDef_symmPart ha0
  have hsize : blockSize A E ≤ 1 + blockExcess A E :=
    Response.blockSize_le_one_add_blockExcess hAsym hApsd hEsym hEpd
  have hAEsize : BlockMatLoewnerLE A (blockScale (blockSize A E) E) := by
    apply blockMatLoewnerLE_of_le
    simpa only [toFullBlockMat_blockScale] using
      (PortableHistory.blockSize_sandwich hAsym hEsym hEpd).1
  exact Persistence.blockMatLoewnerLE_blockScale_mono
    hAsym hEsym hEpd hsize hAEsize

private theorem constantBlock_dualQuadratic_eq_one
    {a0 : Mat d} (ha0 : (symmPart a0).PosDef) (P : BlockVec d)
    (hquad :
      blockVecDot P
        (blockMatVecMul (Book.Ch02.constantBlockMatrix a0) P) = 1) :
    blockVecDot (blockMatVecMul (Book.Ch02.constantBlockMatrix a0) P)
        (blockMatVecMul (blockReflect (Book.Ch02.constantBlockMatrix a0))
          (blockMatVecMul (Book.Ch02.constantBlockMatrix a0) P)) = 1 := by
  let E := Book.Ch02.constantBlockMatrix a0
  let Q := blockMatVecMul E P
  have hEsym : IsSymmetricBlockMat E := by
    simpa [E, Book.Ch02.constantBlockMatrix, blockMatrixOfCoeff] using
      isSymmetricBlockMat_blockMatrixOfCoeff a0
  have hEreflectQ :
      blockMatVecMul E (blockMatVecMul (blockReflect E) Q) = Q := by
    simpa only [E] using
      blockMatVecMul_constantBlockMatrix_blockReflect_inv_of_posDef_symmPart ha0 Q
  calc
    blockVecDot Q (blockMatVecMul (blockReflect E) Q) =
        blockVecDot (blockMatVecMul (blockReflect E) Q) Q :=
      blockVecDot_comm _ _
    _ = blockVecDot P
        (blockMatVecMul E (blockMatVecMul (blockReflect E) Q)) := by
      simpa only [Q] using
        (blockVecDot_blockMatVecMul_comm_of_isSymmetricBlockMat hEsym P
          (blockMatVecMul (blockReflect E) Q)).symm
    _ = blockVecDot P Q := by rw [hEreflectQ]
    _ = 1 := by simpa only [Q, E] using hquad

/-- A doubled response at an intrinsically normalized load is bounded by the
one-sided excess of its coarse block over the constant comparison block. -/
theorem doubledResponseJ_le_blockExcess_of_constantBlockQuadratic_eq_one
    {U : Domain d} (a : CoeffOn U) {a0 : Mat d}
    (ha0 : (symmPart a0).PosDef) (P : BlockVec d)
    (hquad :
      blockVecDot P
        (blockMatVecMul (Book.Ch02.constantBlockMatrix a0) P) = 1) :
    doubledResponseJ U a P
        (blockMatVecMul (Book.Ch02.constantBlockMatrix a0) P) ≤
      blockExcess (Book.Ch02.coarseBlockMatrix U a)
        (Book.Ch02.constantBlockMatrix a0) := by
  let A := Book.Ch02.coarseBlockMatrix U a
  let E := Book.Ch02.constantBlockMatrix a0
  let t := blockExcess A E
  let Q := blockMatVecMul E P
  have hAE : BlockMatLoewnerLE A (blockScale (1 + t) E) := by
    simpa only [A, E, t] using
      coarseBlockMatrix_le_one_add_blockExcess_constant a ha0
  have hreflect :
      BlockMatLoewnerLE (blockReflect A)
        (blockScale (1 + t) (blockReflect E)) := by
    have h := Transport.blockMatLoewnerLE_blockReflect hAE
    simpa only [Transport.blockScale_blockReflect] using h
  have hprimal := hAE P
  rw [Sharp.blockVecDot_blockMatVecMul_blockScale, hquad, mul_one] at hprimal
  have hdualquad :
      blockVecDot Q (blockMatVecMul (blockReflect E) Q) = 1 := by
    simpa only [Q, E] using constantBlock_dualQuadratic_eq_one ha0 P hquad
  have hdual := hreflect Q
  rw [Sharp.blockVecDot_blockMatVecMul_blockScale, hdualquad, mul_one] at hdual
  rw [(blockCoarseMatrixTheory U a).doubled_response_splitting,
    (blockCoarseMatrixTheory U a).starred_inverse_formula]
  change
    (1 / 2 : ℝ) * blockVecDot P (blockMatVecMul A P) +
          (1 / 2 : ℝ) * blockVecDot Q (blockMatVecMul (blockReflect A) Q) -
        blockVecDot P Q ≤ t
  have hpair : blockVecDot P Q = 1 := by simpa only [Q] using hquad
  linarith only [hprimal, hdual, hpair]

end

end HighContrast
end HCPolySupport
