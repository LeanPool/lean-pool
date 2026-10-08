/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileWeakConstant
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileRecentCellLp
public import LeanPool.HighContrastHomogenization.Provider.Response.CenteredResponseAdjointAnnealed
public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormComparison

/-!
# High-contrast homogenization: Provider.Response.ProfileCenterPointwise

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Pointwise control of terminal optimizer centers

The optimizer-average identity turns the difference between a random terminal
average and its annealed center into the block reflection of one centered
response matrix.  The self-dual metric comparison then bounds its length by
the centered terminal maximum.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory

open scoped ENNReal Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

private theorem blockMatVecMul_sub_right (A : BlockMat d)
    (X Y : BlockVec d) :
    blockMatVecMul A (X - Y) =
      blockMatVecMul A X - blockMatVecMul A Y := by
  have hneg : blockMatVecMul A (-Y) = -blockMatVecMul A Y := by
    simpa using blockMatVecMul_smul A (-1) Y
  rw [sub_eq_add_neg, blockMatVecMul_add, hneg]
  rfl

/-- A centered response matrix controls the reflected optimizer-average
difference in the diagonal metric. -/
theorem metricBlockNormSq_responseAverage_sub_le
    {m : Mat d} (hm : m.PosDef) {A E : BlockMat d}
    (hA : IsSymmetricBlockMat A) (hE : IsSymmetricBlockMat E)
    (hEpd : BlockPosDef E) (X : BlockVec d) :
    metricBlockNormSq m
        ((blockMatVecMul (blockR d) (blockMatVecMul A X) + X) -
          (blockMatVecMul (blockR d) (blockMatVecMul E X) + X)) ≤
      diagonalWeakMetricFactor m E ^ 2 *
        blockVecDot X (blockMatVecMul E X) *
          blockSize (blockSub A E) E ^ 2 := by
  let M : BlockMat d := blockDiag m m⁻¹
  let D : BlockMat d := blockSub A E
  have hMsymm : IsSymmetricBlockMat M := by
    exact isSymmetricBlockMat_diagonalMetric hm
  have hMpd : BlockPosDef M := blockPosDef_diagonalMetric hm
  have hMfull : (toFullBlockMat M).PosDef :=
    posDef_toFullBlockMat hMsymm hMpd
  have hEfull : (toFullBlockMat E).PosDef :=
    posDef_toFullBlockMat hE hEpd
  have hDsymm : IsSymmetricBlockMat D :=
    isSymmetricBlockMat_blockSub hA hE
  have hreflect :
      toFullBlockMat (blockReflect M) = (toFullBlockMat M)⁻¹ := by
    rw [← toFullBlockMat_blockMatInv]
    exact congrArg toFullBlockMat
      (blockMatInv_metric_eq_blockReflect (isUnit_det_of_posDef hm)).symm
  have hdiff :
      (blockMatVecMul (blockR d) (blockMatVecMul A X) + X) -
          (blockMatVecMul (blockR d) (blockMatVecMul E X) + X) =
        blockMatVecMul (blockR d) (blockMatVecMul D X) := by
    rw [show blockMatVecMul D X =
        blockMatVecMul A X - blockMatVecMul E X by
      exact blockMatVecMul_blockSub A E X,
      blockMatVecMul_sub_right]
    abel
  have hcomparison := centered_metric_quadratic_le hMfull hEfull
    (toFullBlockVec X) (D := toFullBlockMat D)
  rw [hdiff, metricBlockNormSq, metric_quadratic_blockR,
    blockVecDot_blockMatVecMul_eq_dotProduct,
    toFullBlockVec_blockMatVecMul, hreflect]
  calc
    toFullBlockMat D *ᵥ toFullBlockVec X ⬝ᵥ
        (toFullBlockMat M)⁻¹ *ᵥ (toFullBlockMat D *ᵥ toFullBlockVec X) ≤
        relSize (toFullBlockMat E) (toFullBlockMat M) *
          ‖matSqrt (toFullBlockMat E)⁻¹ * toFullBlockMat D *
              matSqrt (toFullBlockMat E)⁻¹‖ ^ 2 *
            (toFullBlockVec X ⬝ᵥ toFullBlockMat E *ᵥ toFullBlockVec X) :=
      hcomparison
    _ = diagonalWeakMetricFactor m E ^ 2 *
          blockVecDot X (blockMatVecMul E X) * blockSize D E ^ 2 := by
      rw [sq_diagonalWeakMetricFactor hm hE,
        blockVecDot_blockMatVecMul_eq_dotProduct,
        ← blockSize_eq_relSize hE hMsymm hMpd hEfull.posSemidef,
        PortableHistory.blockSize_eq_norm hDsymm hE hEpd,
        Recurrence.toFullBlockMat_normalizedBlock]
      ring

/-- The square-root form of the primal centered-average comparison. -/
theorem sqrt_metricBlockNormSq_responseAverage_sub_le
    {m : Mat d} (hm : m.PosDef) {A E : BlockMat d}
    (hA : IsSymmetricBlockMat A) (hE : IsSymmetricBlockMat E)
    (hEpd : BlockPosDef E) (p r : Vec d) :
    Real.sqrt (metricBlockNormSq m
        ((blockMatVecMul (blockR d)
              (blockMatVecMul A ((-p, r) : BlockVec d)) + ((-p, r) : BlockVec d)) -
          (blockMatVecMul (blockR d)
              (blockMatVecMul E ((-p, r) : BlockVec d)) + ((-p, r) : BlockVec d)))) ≤
      diagonalWeakMetricFactor m E * diagonalWeakLoadMinus E p r *
        blockSize (blockSub A E) E := by
  let K := diagonalWeakMetricFactor m E
  let L := diagonalWeakLoadMinus E p r
  let B := blockSize (blockSub A E) E
  have hK0 : 0 ≤ K := diagonalWeakMetricFactor_nonneg m E
  have hL0 : 0 ≤ L := diagonalWeakLoadMinus_nonneg E p r
  have hB0 : 0 ≤ B :=
    PortableHistory.blockSize_nonneg (isSymmetricBlockMat_blockSub hA hE) hE hEpd
  have hsq := metricBlockNormSq_responseAverage_sub_le hm hA hE hEpd
    ((-p, r) : BlockVec d)
  rw [← sq_diagonalWeakLoadMinus hE hEpd] at hsq
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · simpa only [K, L, B] using (hsq.trans_eq (by ring))

end

end HCPolySupport.HighContrast.Response
