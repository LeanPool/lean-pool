/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormPrimal

/-!
# High-contrast homogenization: Provider.Response.DiagonalWeakNormAdjointAlgebra

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Adjoint sign-congruence algebra

The diagonal sign matrix transports the primal weak estimate to the adjoint
coefficient.  This file records its involution, order, scalar-size, and
inverse-square-root invariances in the doubled block dialect.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02

open scoped Matrix

noncomputable section

variable {d : ℕ}

theorem adjointSign_mulVec (X : BlockVec d) :
    blockMatVecMul (blockDiag 1 (-1)) X = (X.1, -X.2) := by
  apply Prod.ext
  · change matVecMul 1 X.1 + matVecMul 0 X.2 = X.1
    rw [matVecMul_one, zero_matVecMul, add_zero]
  · change matVecMul 0 X.1 + matVecMul (-1) X.2 = -X.2
    rw [zero_matVecMul, zero_add, neg_matVecMul, matVecMul_one]

theorem adjointSign_mulVec_involution (X : BlockVec d) :
    blockMatVecMul (blockDiag 1 (-1))
        (blockMatVecMul (blockDiag 1 (-1)) X) = X := by
  rw [adjointSign_mulVec, adjointSign_mulVec]
  simp

theorem blockMatVecMul_adjointSign_congr (A : BlockMat d) (X : BlockVec d) :
    blockMatVecMul
        (blockMatMul (blockDiag 1 (-1))
          (blockMatMul A (blockDiag 1 (-1)))) X =
      blockMatVecMul (blockDiag 1 (-1))
        (blockMatVecMul A (blockMatVecMul (blockDiag 1 (-1)) X)) := by
  rw [blockMatVecMul_blockMatMul, blockMatVecMul_blockMatMul]

theorem blockQuadratic_adjointSign_congr (A : BlockMat d) (X : BlockVec d) :
    blockVecDot X
        (blockMatVecMul
          (blockMatMul (blockDiag 1 (-1))
            (blockMatMul A (blockDiag 1 (-1)))) X) =
      blockVecDot (blockMatVecMul (blockDiag 1 (-1)) X)
        (blockMatVecMul A (blockMatVecMul (blockDiag 1 (-1)) X)) := by
  rw [blockMatVecMul_adjointSign_congr]
  simp only [adjointSign_mulVec]
  simp [blockVecDot, blockMatVecMul, vecDot_add_right, vecDot_neg_left,
    vecDot_neg_right]
  ring

theorem adjointSign_mulVec_injective (X : BlockVec d)
    (hX : blockMatVecMul (blockDiag 1 (-1)) X = 0) : X = 0 := by
  rw [adjointSign_mulVec] at hX
  have h1 : X.1 = 0 := congrArg (fun Z : BlockVec d => Z.1) hX
  have h2 : -X.2 = 0 := congrArg (fun Z : BlockVec d => Z.2) hX
  exact Prod.ext h1 (neg_eq_zero.mp h2)

theorem adjointSign_congr_loewner_iff (A B : BlockMat d) :
    BlockMatLoewnerLE
        (blockMatMul (blockDiag 1 (-1))
          (blockMatMul A (blockDiag 1 (-1))))
        (blockMatMul (blockDiag 1 (-1))
          (blockMatMul B (blockDiag 1 (-1)))) ↔
      BlockMatLoewnerLE A B := by
  constructor
  · intro h X
    simpa only [blockQuadratic_adjointSign_congr, adjointSign_mulVec_involution] using
      h (blockMatVecMul (blockDiag 1 (-1)) X)
  · intro h X
    simpa only [blockQuadratic_adjointSign_congr] using
      h (blockMatVecMul (blockDiag 1 (-1)) X)

theorem blockScale_adjointSign_congr (c : ℝ) (A : BlockMat d) :
    blockMatMul (blockDiag 1 (-1))
        (blockMatMul (blockScale c A) (blockDiag 1 (-1))) =
      blockScale c
        (blockMatMul (blockDiag 1 (-1))
          (blockMatMul A (blockDiag 1 (-1)))) := by
  apply toFullBlockMat_injective
  simp only [toFullBlockMat_blockMatMul, toFullBlockMat_blockScale]
  simp

theorem blockSub_adjointSign_congr (A B : BlockMat d) :
    blockMatMul (blockDiag 1 (-1))
        (blockMatMul (blockSub A B) (blockDiag 1 (-1))) =
      blockSub
        (blockMatMul (blockDiag 1 (-1))
          (blockMatMul A (blockDiag 1 (-1))))
        (blockMatMul (blockDiag 1 (-1))
          (blockMatMul B (blockDiag 1 (-1)))) := by
  apply toFullBlockMat_injective
  simp only [toFullBlockMat_blockMatMul, Recurrence.toFullBlockMat_blockSub]
  rw [Matrix.sub_mul, Matrix.mul_sub]

theorem blockSize_adjointSign_congr (A E : BlockMat d) :
    blockSize
        (blockMatMul (blockDiag 1 (-1))
          (blockMatMul A (blockDiag 1 (-1))))
        (blockMatMul (blockDiag 1 (-1))
          (blockMatMul E (blockDiag 1 (-1)))) =
      blockSize A E := by
  unfold blockSize
  congr 1
  ext c
  simp only [Set.mem_ofPred_eq]
  rw [← blockScale_adjointSign_congr c E,
    ← blockScale_adjointSign_congr (-c) E,
    adjointSign_congr_loewner_iff, adjointSign_congr_loewner_iff]

theorem blockExcess_adjointSign_congr (A E : BlockMat d) :
    blockExcess
        (blockMatMul (blockDiag 1 (-1))
          (blockMatMul A (blockDiag 1 (-1))))
        (blockMatMul (blockDiag 1 (-1))
          (blockMatMul E (blockDiag 1 (-1)))) =
      blockExcess A E := by
  unfold blockExcess
  congr 1
  ext c
  simp only [Set.mem_ofPred_eq]
  rw [← blockScale_adjointSign_congr (1 + c) E,
    adjointSign_congr_loewner_iff]

theorem blockPosDef_adjointSign_congr {A : BlockMat d} (hA : BlockPosDef A) :
    BlockPosDef
      (blockMatMul (blockDiag 1 (-1))
        (blockMatMul A (blockDiag 1 (-1)))) := by
  intro X hX
  rw [blockQuadratic_adjointSign_congr]
  exact hA _ (fun hzero => hX (adjointSign_mulVec_injective X hzero))

theorem isSymmetricBlockMat_adjointSign_congr {A : BlockMat d}
    (hA : IsSymmetricBlockMat A) :
    IsSymmetricBlockMat
      (blockMatMul (blockDiag 1 (-1))
        (blockMatMul A (blockDiag 1 (-1)))) := by
  rw [blockMatMul_blockDiag_one_neg_one]
  intro α β
  cases α with
  | inl i =>
      cases β with
      | inl j => exact hA (Sum.inl i) (Sum.inl j)
      | inr j =>
          simpa only [blockMatEntry, Matrix.neg_apply] using
            congrArg Neg.neg (hA (Sum.inl i) (Sum.inr j))
  | inr i =>
      cases β with
      | inl j =>
          simpa only [blockMatEntry, Matrix.neg_apply] using
            congrArg Neg.neg (hA (Sum.inr i) (Sum.inl j))
      | inr j => exact hA (Sum.inr i) (Sum.inr j)

theorem adjointSign_mul_self :
    toFullBlockMat (blockDiag (1 : Mat d) (-1)) *
        toFullBlockMat (blockDiag (1 : Mat d) (-1)) = 1 := by
  rw [toFullBlockMat_blockDiag, Matrix.fromBlocks_multiply,
    ← Matrix.fromBlocks_one]
  simp

theorem adjointSign_conjTranspose :
    Matrix.conjTranspose (toFullBlockMat (blockDiag (1 : Mat d) (-1))) =
      toFullBlockMat (blockDiag (1 : Mat d) (-1)) := by
  rw [toFullBlockMat_blockDiag]
  rw [Matrix.fromBlocks_conjTranspose]
  simp

theorem isUnit_adjointSign :
    IsUnit (toFullBlockMat (blockDiag (1 : Mat d) (-1))) := by
  exact ⟨⟨toFullBlockMat (blockDiag (1 : Mat d) (-1)),
    toFullBlockMat (blockDiag (1 : Mat d) (-1)), adjointSign_mul_self,
    adjointSign_mul_self⟩, rfl⟩

theorem adjointSign_inv :
    (toFullBlockMat (blockDiag (1 : Mat d) (-1)))⁻¹ =
      toFullBlockMat (blockDiag (1 : Mat d) (-1)) :=
  Matrix.inv_eq_right_inv adjointSign_mul_self

theorem adjointSign_congr_inv (E : BlockMat d) :
    (toFullBlockMat (blockDiag (1 : Mat d) (-1)) * toFullBlockMat E *
        toFullBlockMat (blockDiag (1 : Mat d) (-1)))⁻¹ =
      toFullBlockMat (blockDiag (1 : Mat d) (-1)) *
        (toFullBlockMat E)⁻¹ *
          toFullBlockMat (blockDiag (1 : Mat d) (-1)) := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  simp only [adjointSign_inv]
  exact (Matrix.mul_assoc _ _ _).symm

theorem adjointSign_congr_sqrt_inv {E : BlockMat d}
    (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E) :
    matSqrt
        ((toFullBlockMat (blockDiag (1 : Mat d) (-1)) *
          (toFullBlockMat E *
            toFullBlockMat (blockDiag (1 : Mat d) (-1))))⁻¹) =
      toFullBlockMat (blockDiag (1 : Mat d) (-1)) *
        (matSqrt ((toFullBlockMat E)⁻¹) *
          toFullBlockMat (blockDiag (1 : Mat d) (-1))) := by
  let C := toFullBlockMat (blockDiag (1 : Mat d) (-1))
  let P := toFullBlockMat E
  let R := matSqrt P⁻¹
  change matSqrt ((C * (P * C))⁻¹) = C * (R * C)
  have hP : P.PosDef := posDef_toFullBlockMat hE hEpd
  have hQ : (C * (P * C)).PosDef := by
    have hconj := posDef_conj hP isUnit_adjointSign
    rw [adjointSign_conjTranspose] at hconj
    simpa only [C, Matrix.mul_assoc] using hconj
  have hRps : R.PosSemidef := (matSqrt_spec hP.inv.posSemidef).1
  have hCand : (C * (R * C)).PosSemidef := by
    have hconj := hRps.conjTranspose_mul_mul_same C
    rw [show Matrix.conjTranspose C = C by exact adjointSign_conjTranspose] at hconj
    simpa only [Matrix.mul_assoc] using hconj
  refine matSqrt_eq hQ.inv.posSemidef hCand ?_
  have hR2 : R * R = P⁻¹ := (matSqrt_spec hP.inv.posSemidef).2
  have hQinv : (C * (P * C))⁻¹ = C * (P⁻¹ * C) := by
    simpa only [C, P, Matrix.mul_assoc] using adjointSign_congr_inv E
  calc
    (C * (R * C)) * (C * (R * C)) = C * R * (C * C) * R * C := by
      noncomm_ring
    _ = C * R * R * C := by rw [adjointSign_mul_self, Matrix.mul_one]
    _ = C * (R * R) * C := by noncomm_ring
    _ = C * (P⁻¹ * C) := by rw [hR2]; noncomm_ring
    _ = (C * (P * C))⁻¹ := hQinv.symm

theorem normalizedBlock_adjointSign_congr {E : BlockMat d}
    (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E) (A : BlockMat d) :
    normalizedBlock
        (blockMatMul (blockDiag 1 (-1))
          (blockMatMul A (blockDiag 1 (-1))))
        (blockMatMul (blockDiag 1 (-1))
          (blockMatMul E (blockDiag 1 (-1)))) =
      blockMatMul (blockDiag 1 (-1))
        (blockMatMul (normalizedBlock A E) (blockDiag 1 (-1))) := by
  apply toFullBlockMat_injective
  simp only [Recurrence.toFullBlockMat_normalizedBlock, toFullBlockMat_blockMatMul]
  rw [adjointSign_congr_sqrt_inv hE hEpd]
  let C := toFullBlockMat (blockDiag (1 : Mat d) (-1))
  let R := matSqrt (toFullBlockMat E)⁻¹
  let P := toFullBlockMat A
  change (C * (R * C)) * (C * (P * C)) * (C * (R * C)) =
    C * ((R * P * R) * C)
  calc
    (C * (R * C)) * (C * (P * C)) * (C * (R * C)) =
        C * R * (C * C) * P * (C * C) * R * C := by
      noncomm_ring
    _ = C * ((R * P * R) * C) := by
      rw [adjointSign_mul_self, Matrix.mul_one]
      noncomm_ring

end

end HCPolySupport.HighContrast.Response
