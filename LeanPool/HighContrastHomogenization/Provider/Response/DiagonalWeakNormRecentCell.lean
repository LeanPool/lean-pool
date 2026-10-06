/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormRecentState

/-!
# High-contrast homogenization: Provider.Response.DiagonalWeakNormRecentCell

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The coarse-block term on recent scales

The difference between the child optimizer average and the parent optimizer
average is controlled by the normalized child/parent coarse-block defect.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

open Book.Ch02

noncomputable section

variable {d : ℕ}

/-- The normalized square sum of child-optimizer average differences is
bounded by the recent cell defect. -/
theorem diagonalWeak_recent_cell_bound [NeZero d]
    {q : Mat d} (hq : q.PosDef) (k t : ℤ) {S m : Mat d}
    (hsymm : matTranspose S = S) (hsq : S * S = m) (hm : m.PosDef)
    {E : BlockMat d} (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    (a : CoeffSpace d) (p r : Vec d) :
    blockAvsumL2 (alignedIndex q k t) (fun w =>
        blockMatVecMul (blockDiag S S⁻¹)
          (blockCellAverage (adaptedCellAt q k w)
              (diagonalWeakChildState hq k w a p r) -
            blockCellAverage (adaptedCell q t)
              (diagonalWeakState hq t a p r))) ≤
      diagonalWeakMetricFactor m E * diagonalWeakLoadMinus E p r *
        diagonalWeakCellDefect q k t E a := by
  let Z := alignedIndex q k t
  let K := diagonalWeakMetricFactor m E
  let L := diagonalWeakLoadMinus E p r
  let C := diagonalWeakCellDefect q k t E a
  let B : (Fin d → ℤ) → ℝ := fun w =>
    blockSize
      (blockSub (adaptedResponse q k w a)
        (coarseBlock (adaptedCell q t) a)) E
  have hK0 : 0 ≤ K := diagonalWeakMetricFactor_nonneg m E
  have hL0 : 0 ≤ L := diagonalWeakLoadMinus_nonneg E p r
  have hC0 : 0 ≤ C := diagonalWeakCellDefect_nonneg q k t E a
  have hcell : ∀ w ∈ Z,
      blockVecDot
          (blockMatVecMul (blockDiag S S⁻¹)
            (blockCellAverage (adaptedCellAt q k w)
                (diagonalWeakChildState hq k w a p r) -
              blockCellAverage (adaptedCell q t)
                (diagonalWeakState hq t a p r)))
          (blockMatVecMul (blockDiag S S⁻¹)
            (blockCellAverage (adaptedCellAt q k w)
                (diagonalWeakChildState hq k w a p r) -
              blockCellAverage (adaptedCell q t)
                (diagonalWeakState hq t a p r))) ≤
        K ^ 2 * L ^ 2 * B w ^ 2 := by
    intro w _hw
    have hcomparison := metricNormSq_blockAverage_sub_adapted_le
      hq k t w hm hE hEpd
      (coarseBlock_eq_coarseBlockMatrix a (adaptedDomainAt hq k w)).symm
      (coarseBlock_eq_coarseBlockMatrix a (adaptedDomain hq t)).symm
      (diagonalWeakChildOptimizer_isMaximizer hq k w a p r)
      (diagonalWeakOptimizer_isMaximizer hq t a p r)
    rw [← blockCellAverage_diagonalWeakChildState,
      ← blockCellAverage_diagonalWeakState] at hcomparison
    rw [blockVecDot_self_blockDiag_root hsymm hsq]
    exact hcomparison
  have hsum : avsum Z (fun w =>
      blockVecDot
        (blockMatVecMul (blockDiag S S⁻¹)
          (blockCellAverage (adaptedCellAt q k w)
              (diagonalWeakChildState hq k w a p r) -
            blockCellAverage (adaptedCell q t)
              (diagonalWeakState hq t a p r)))
        (blockMatVecMul (blockDiag S S⁻¹)
          (blockCellAverage (adaptedCellAt q k w)
              (diagonalWeakChildState hq k w a p r) -
            blockCellAverage (adaptedCell q t)
              (diagonalWeakState hq t a p r)))) ≤
      (K * L) ^ 2 * C ^ 2 := by
    calc
      avsum Z (fun w =>
          blockVecDot
            (blockMatVecMul (blockDiag S S⁻¹)
              (blockCellAverage (adaptedCellAt q k w)
                  (diagonalWeakChildState hq k w a p r) -
                blockCellAverage (adaptedCell q t)
                  (diagonalWeakState hq t a p r)))
            (blockMatVecMul (blockDiag S S⁻¹)
              (blockCellAverage (adaptedCellAt q k w)
                  (diagonalWeakChildState hq k w a p r) -
                blockCellAverage (adaptedCell q t)
                  (diagonalWeakState hq t a p r)))) ≤
          avsum Z (fun w => K ^ 2 * L ^ 2 * B w ^ 2) :=
        avsum_le_avsum hcell
      _ = (K ^ 2 * L ^ 2) * avsum Z (fun w => B w ^ 2) :=
        avsum_const_mul Z _ _
      _ = (K * L) ^ 2 * C ^ 2 := by
        rw [show C ^ 2 = avsum Z (fun w => B w ^ 2) from
          Real.sq_sqrt (avsum_nonneg fun w _ => sq_nonneg (B w))]
        ring_nf
  change blockAvsumL2 Z (fun w =>
      blockMatVecMul (blockDiag S S⁻¹)
        (blockCellAverage (adaptedCellAt q k w)
            (diagonalWeakChildState hq k w a p r) -
          blockCellAverage (adaptedCell q t)
            (diagonalWeakState hq t a p r))) ≤ K * L * C
  rw [blockAvsumL2_eq]
  calc
    Real.sqrt (avsum Z (fun w =>
        blockVecDot
          (blockMatVecMul (blockDiag S S⁻¹)
            (blockCellAverage (adaptedCellAt q k w)
                (diagonalWeakChildState hq k w a p r) -
              blockCellAverage (adaptedCell q t)
                (diagonalWeakState hq t a p r)))
          (blockMatVecMul (blockDiag S S⁻¹)
            (blockCellAverage (adaptedCellAt q k w)
                (diagonalWeakChildState hq k w a p r) -
              blockCellAverage (adaptedCell q t)
                (diagonalWeakState hq t a p r))))) ≤
        Real.sqrt ((K * L) ^ 2 * C ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt ((K * L * C) ^ 2) := by ring_nf
    _ = K * L * C := Real.sqrt_sq (by positivity)

end

end HCPolySupport.HighContrast.Response

end HighContrast

end HCPolySupport

end
