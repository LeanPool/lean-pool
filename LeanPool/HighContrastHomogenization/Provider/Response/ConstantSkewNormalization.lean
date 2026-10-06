/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PortableHistory.MajorizationSize
public import LeanPool.HighContrastHomogenization.Provider.Response.ConstantSkewBlock

/-!
# High-contrast homogenization: Provider.Response.ConstantSkewNormalization

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Scalar invariants of constant-skew congruence

The lower triangular shear is invertible.  A common congruence by this shear
therefore preserves the doubled Loewner order and the two scalar sizes used by
the response profile.  Normalization is also recorded as a linear operation,
which lets the recent averaged defect be handled without choosing an
orthogonal representative of the congruence.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

variable {d : ℕ}

/-- A common shear congruence preserves and reflects the structural Loewner
order. -/
theorem skewBlockCongr_loewner_iff (g : Mat d) (A B : BlockMat d) :
    BlockMatLoewnerLE (skewBlockCongr g A) (skewBlockCongr g B) ↔
      BlockMatLoewnerLE A B := by
  constructor
  · intro h X
    have hX := h (X.1, -matVecMul g X.1 + X.2)
    simp only [blockQuadratic_skewBlockCongr] at hX
    have hshift :
        matVecMul g X.1 + (-matVecMul g X.1 + X.2) = X.2 := by
      abel
    rwa [hshift] at hX
  · intro h X
    rw [blockQuadratic_skewBlockCongr, blockQuadratic_skewBlockCongr]
    exact h (X.1, matVecMul g X.1 + X.2)

/-- Scalar dilation commutes with a shear congruence. -/
theorem blockScale_skewBlockCongr (g : Mat d) (c : ℝ) (A : BlockMat d) :
    skewBlockCongr g (blockScale c A) =
      blockScale c (skewBlockCongr g A) := by
  apply toFullBlockMat_injective
  simp only [toFullBlockMat_skewBlockCongr, toFullBlockMat_blockScale]
  rw [Matrix.mul_smul, Matrix.smul_mul]

/-- Subtraction commutes with a shear congruence. -/
theorem blockSub_skewBlockCongr (g : Mat d) (A B : BlockMat d) :
    skewBlockCongr g (blockSub A B) =
      blockSub (skewBlockCongr g A) (skewBlockCongr g B) := by
  apply toFullBlockMat_injective
  simp only [toFullBlockMat_skewBlockCongr, Recurrence.toFullBlockMat_blockSub]
  rw [Matrix.mul_sub, Matrix.sub_mul]

/-- The two-sided normalized block size is invariant under a common shear
congruence. -/
theorem blockSize_skewBlockCongr (g : Mat d) (A E : BlockMat d) :
    blockSize (skewBlockCongr g A) (skewBlockCongr g E) = blockSize A E := by
  unfold blockSize
  congr 1
  ext c
  simp only [Set.mem_ofPred_eq]
  rw [← blockScale_skewBlockCongr g c E,
    ← blockScale_skewBlockCongr g (-c) E,
    skewBlockCongr_loewner_iff, skewBlockCongr_loewner_iff]

/-- The positive normalized excess is invariant under a common shear
congruence. -/
theorem blockExcess_skewBlockCongr (g : Mat d) (A E : BlockMat d) :
    blockExcess (skewBlockCongr g A) (skewBlockCongr g E) = blockExcess A E := by
  unfold blockExcess
  congr 1
  ext c
  simp only [Set.mem_ofPred_eq]
  rw [← blockScale_skewBlockCongr g (1 + c) E,
    skewBlockCongr_loewner_iff]

private theorem isSymmetricBlockMat_identity :
    IsSymmetricBlockMat (blockIdentity d) := by
  apply isSymmetricBlockMat_of_isSymm_toFullBlockMat
  rw [toFullBlockMat_blockIdentity]
  exact Matrix.isSymm_one

private theorem blockPosDef_identity : BlockPosDef (blockIdentity d) :=
  (blockPosDef_iff_posDef isSymmetricBlockMat_identity).mpr <| by
    rw [toFullBlockMat_blockIdentity]
    exact Matrix.PosDef.one

private theorem matSqrt_one_fullBlock :
    matSqrt (1 : FullBlockMat d) = 1 :=
  matSqrt_eq Matrix.PosSemidef.one Matrix.PosSemidef.one (by simp)

/-- Measuring a normalized symmetric block against the identity gives the
same scalar size as measuring the original block against its reference. -/
theorem blockSize_normalizedBlock_identity {A E : BlockMat d}
    (hA : IsSymmetricBlockMat A) (hE : IsSymmetricBlockMat E)
    (hEpd : BlockPosDef E) :
    blockSize (normalizedBlock A E) (blockIdentity d) = blockSize A E := by
  rw [PortableHistory.blockSize_eq_norm (isSymmetricBlockMat_normalizedBlock hA)
      isSymmetricBlockMat_identity blockPosDef_identity,
    PortableHistory.blockSize_eq_norm hA hE hEpd]
  congr 1
  rw [Recurrence.toFullBlockMat_normalizedBlock, toFullBlockMat_blockIdentity,
    inv_one, matSqrt_one_fullBlock, Matrix.one_mul, Matrix.mul_one]

/-- A fixed normalization commutes with a finite weighted sum. -/
theorem normalizedBlock_ofFullBlockMat_smul_sum {ι : Type*}
    (s : Finset ι) (c : ℝ) (A : ι → BlockMat d) (E : BlockMat d) :
    normalizedBlock
        (ofFullBlockMat (c • ∑ i ∈ s, toFullBlockMat (A i))) E =
      ofFullBlockMat
        (c • ∑ i ∈ s, toFullBlockMat (normalizedBlock (A i) E)) := by
  apply toFullBlockMat_injective
  simp only [Recurrence.toFullBlockMat_normalizedBlock,
    toFullBlockMat_ofFullBlockMat]
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum]
  rw [Finset.sum_mul]

/-- A shear congruence commutes with a finite weighted sum. -/
theorem skewBlockCongr_ofFullBlockMat_smul_sum {ι : Type*}
    (g : Mat d) (s : Finset ι) (c : ℝ) (A : ι → BlockMat d) :
    skewBlockCongr g
        (ofFullBlockMat (c • ∑ i ∈ s, toFullBlockMat (A i))) =
      ofFullBlockMat
        (c • ∑ i ∈ s, toFullBlockMat (skewBlockCongr g (A i))) := by
  apply toFullBlockMat_injective
  simp only [toFullBlockMat_skewBlockCongr, toFullBlockMat_ofFullBlockMat]
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum]
  rw [Finset.sum_mul]

end

end HCPolySupport.HighContrast.Response
