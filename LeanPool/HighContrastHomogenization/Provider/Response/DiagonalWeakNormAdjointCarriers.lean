/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormAdjointAlgebra

/-!
# High-contrast homogenization: Provider.Response.DiagonalWeakNormAdjointCarriers

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Adjoint invariance of the diagonal weak carriers

Coefficient transposition and the matching signed reference block leave the
maximum and recent defects unchanged.  The primal load becomes the adjoint
load, while the diagonal metric is fixed.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02

open scoped ENNReal

noncomputable section

variable {d : ℕ}

theorem adjointSign_diagonalMetric (m : Mat d) :
    blockMatMul (blockDiag 1 (-1))
        (blockMatMul (blockDiag m m⁻¹) (blockDiag 1 (-1))) =
      blockDiag m m⁻¹ := by
  rw [blockMatMul_blockDiag_one_neg_one]
  simp [blockDiag]

theorem adjointSign_blockIdentity :
    blockMatMul (blockDiag 1 (-1))
        (blockMatMul (blockIdentity d) (blockDiag 1 (-1))) =
      blockIdentity d := by
  rw [blockMatMul_blockDiag_one_neg_one]
  simp [blockIdentity, blockDiag]

theorem diagonalWeakMetricFactor_adjoint (m : Mat d) (E : BlockMat d) :
    diagonalWeakMetricFactor m
        (blockMatMul (blockDiag 1 (-1))
          (blockMatMul E (blockDiag 1 (-1)))) =
      diagonalWeakMetricFactor m E := by
  rw [diagonalWeakMetricFactor_eq, diagonalWeakMetricFactor_eq]
  congr 1
  calc
    blockSize
        (blockMatMul (blockDiag 1 (-1))
          (blockMatMul E (blockDiag 1 (-1)))) (blockDiag m m⁻¹) =
        blockSize
          (blockMatMul (blockDiag 1 (-1))
            (blockMatMul E (blockDiag 1 (-1))))
          (blockMatMul (blockDiag 1 (-1))
            (blockMatMul (blockDiag m m⁻¹) (blockDiag 1 (-1)))) := by
      rw [adjointSign_diagonalMetric]
    _ = blockSize E (blockDiag m m⁻¹) := blockSize_adjointSign_congr E _

theorem diagonalWeakLoadMinus_adjoint (E : BlockMat d) (p r : Vec d) :
    diagonalWeakLoadMinus
        (blockMatMul (blockDiag 1 (-1))
          (blockMatMul E (blockDiag 1 (-1)))) p r =
      diagonalWeakLoadPlus E p r := by
  rw [diagonalWeakLoadMinus_eq, diagonalWeakLoadPlus_eq]
  congr 1
  rw [blockQuadratic_adjointSign_congr, adjointSign_mulVec]
  change blockVecDot ((-p, -r) : BlockVec d)
      (blockMatVecMul E ((-p, -r) : BlockVec d)) =
    blockVecDot ((p, r) : BlockVec d)
      (blockMatVecMul E ((p, r) : BlockVec d))
  have hneg : ((-p, -r) : BlockVec d) = -((p, r) : BlockVec d) := rfl
  rw [hneg]
  rw [← neg_one_smul ℝ ((p, r) : BlockVec d)]
  rw [blockMatVecMul_smul, blockVecDot_smul_left,
    blockVecDot_smul_right]
  norm_num

theorem diagonalWeakMaximum_adjoint (rho : ℝ) {q : Mat d} (hq : q.PosDef)
    (t : ℤ) (E : BlockMat d) (a : CoeffSpace d) :
    diagonalWeakMaximum rho q t
        (blockMatMul (blockDiag 1 (-1))
          (blockMatMul E (blockDiag 1 (-1)))) a.transpose =
      diagonalWeakMaximum rho q t E a := by
  unfold diagonalWeakMaximum
  simp_rw [adaptedResponse_transpose hq, blockExcess_adjointSign_congr]

theorem diagonalWeakCellDefect_adjoint {q : Mat d} (hq : q.PosDef) (k t : ℤ)
    (E : BlockMat d) (a : CoeffSpace d) :
    diagonalWeakCellDefect q k t
        (blockMatMul (blockDiag 1 (-1))
          (blockMatMul E (blockDiag 1 (-1)))) a.transpose =
      diagonalWeakCellDefect q k t E a := by
  rw [diagonalWeakCellDefect_eq, diagonalWeakCellDefect_eq]
  apply congrArg Real.sqrt
  unfold avsum
  apply congrArg (((alignedIndex q k t).card : ℝ)⁻¹ * ·)
  refine Finset.sum_congr rfl fun w _ => ?_
  change blockSize
      (blockSub (adaptedResponse q k w a.transpose)
        (coarseBlock (adaptedCell q t) a.transpose))
        (blockMatMul (blockDiag 1 (-1))
          (blockMatMul E (blockDiag 1 (-1)))) ^ 2 =
    blockSize
      (blockSub (adaptedResponse q k w a)
        (coarseBlock (adaptedCell q t) a)) E ^ 2
  have hparent := coarseBlock_transpose a (adaptedDomain hq t)
  rw [adaptedResponse_transpose hq]
  rw [show coarseBlock (adaptedCell q t) a.transpose =
      blockMatMul (blockDiag 1 (-1))
        (blockMatMul (coarseBlock (adaptedCell q t) a)
          (blockDiag 1 (-1))) by
    simpa only [adaptedDomain_carrier] using hparent]
  rw [← blockSub_adjointSign_congr, blockSize_adjointSign_congr]

theorem diagonalWeakAverageDefect_adjoint {q : Mat d} (hq : q.PosDef) (k t : ℤ)
    {E : BlockMat d} (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    (a : CoeffSpace d) :
    diagonalWeakAverageDefect q k t
        (blockMatMul (blockDiag 1 (-1))
          (blockMatMul E (blockDiag 1 (-1)))) a.transpose =
      blockMatMul (blockDiag 1 (-1))
        (blockMatMul (diagonalWeakAverageDefect q k t E a)
          (blockDiag 1 (-1))) := by
  have hparent := coarseBlock_transpose a (adaptedDomain hq t)
  have hparent' : coarseBlock (adaptedCell q t) a.transpose =
      blockMatMul (blockDiag 1 (-1))
        (blockMatMul (coarseBlock (adaptedCell q t) a)
          (blockDiag 1 (-1))) := by
    simpa only [adaptedDomain_carrier] using hparent
  have hnorm : ∀ w : Fin d → ℤ,
      normalizedBlock
          (blockSub (adaptedResponse q k w a.transpose)
            (coarseBlock (adaptedCell q t) a.transpose))
          (blockMatMul (blockDiag 1 (-1))
            (blockMatMul E (blockDiag 1 (-1)))) =
        blockMatMul (blockDiag 1 (-1))
          (blockMatMul
            (normalizedBlock
              (blockSub (adaptedResponse q k w a)
                (coarseBlock (adaptedCell q t) a)) E)
            (blockDiag 1 (-1))) := by
    intro w
    rw [adaptedResponse_transpose hq, hparent',
      ← blockSub_adjointSign_congr,
      normalizedBlock_adjointSign_congr hE hEpd]
  apply toFullBlockMat_injective
  unfold diagonalWeakAverageDefect
  simp only [toFullBlockMat_ofFullBlockMat, toFullBlockMat_blockMatMul]
  simp_rw [hnorm, toFullBlockMat_blockMatMul]
  rw [← Finset.mul_sum, ← Finset.sum_mul]
  simp

theorem blockSize_diagonalWeakAverageDefect_adjoint {q : Mat d} (hq : q.PosDef)
    (k t : ℤ) {E : BlockMat d} (hE : IsSymmetricBlockMat E)
    (hEpd : BlockPosDef E) (a : CoeffSpace d) :
    blockSize
        (diagonalWeakAverageDefect q k t
          (blockMatMul (blockDiag 1 (-1))
            (blockMatMul E (blockDiag 1 (-1)))) a.transpose)
        (blockIdentity d) =
      blockSize (diagonalWeakAverageDefect q k t E a) (blockIdentity d) := by
  rw [diagonalWeakAverageDefect_adjoint hq k t hE hEpd]
  calc
    blockSize
        (blockMatMul (blockDiag 1 (-1))
          (blockMatMul (diagonalWeakAverageDefect q k t E a)
            (blockDiag 1 (-1)))) (blockIdentity d) =
      blockSize
        (blockMatMul (blockDiag 1 (-1))
          (blockMatMul (diagonalWeakAverageDefect q k t E a)
            (blockDiag 1 (-1))))
        (blockMatMul (blockDiag 1 (-1))
          (blockMatMul (blockIdentity d) (blockDiag 1 (-1)))) := by
      rw [adjointSign_blockIdentity]
    _ = blockSize (diagonalWeakAverageDefect q k t E a)
        (blockIdentity d) := blockSize_adjointSign_congr _ _

theorem diagonalWeakCellSum_adjoint {q : Mat d} (hq : q.PosDef) (t : ℤ)
    (H : ℕ) (s : ℝ) (E : BlockMat d) (a : CoeffSpace d) :
    diagonalWeakCellSum q t H s
        (blockMatMul (blockDiag 1 (-1))
          (blockMatMul E (blockDiag 1 (-1)))) a.transpose =
      diagonalWeakCellSum q t H s E a := by
  rw [diagonalWeakCellSum_eq, diagonalWeakCellSum_eq]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [diagonalWeakCellDefect_adjoint hq]

theorem diagonalWeakAverageSum_adjoint {q : Mat d} (hq : q.PosDef) (t : ℤ)
    (H : ℕ) (s rho : ℝ) {E : BlockMat d} (hE : IsSymmetricBlockMat E)
    (hEpd : BlockPosDef E) (a : CoeffSpace d) :
    diagonalWeakAverageSum q t H s rho
        (blockMatMul (blockDiag 1 (-1))
          (blockMatMul E (blockDiag 1 (-1)))) a.transpose =
      diagonalWeakAverageSum q t H s rho E a := by
  rw [diagonalWeakAverageSum_eq, diagonalWeakAverageSum_eq]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [blockSize_diagonalWeakAverageDefect_adjoint hq _ _ hE hEpd]

end

end HCPolySupport.HighContrast.Response
