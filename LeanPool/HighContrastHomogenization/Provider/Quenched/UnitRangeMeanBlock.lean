/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.UnitRangeReferenceComparison

/-!
# High-contrast homogenization: Provider.Quenched.UnitRangeMeanBlock

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The mean block of a block-valued observable

The concentration estimate centres each observable at its own mean, so the
renormalization argument needs to compare the block of those means with the
annealed block.  The printed argument makes that comparison one-sided and free
of error terms: the truncated block is below the coarse block at every sample,
because the cutoff multiplies a positive block by a factor at most one, and the
mean is monotone.

This file records the block of entrywise means, identifies its quadratic form as
the average of the quadratic forms, and proves the monotonicity that the printed
argument uses.  The annealed block is the mean block of the coarse block, so the
comparison specializes to it.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## The mean block -/

/-- The block of entrywise means of a block-valued observable. -/
@[expose]
def meanBlock (P : Measure (CoeffSpace d)) (M : CoeffSpace d → BlockMat d) :
    BlockMat d where
  upperLeft := Matrix.of fun i j => ∫ a, (M a).upperLeft i j ∂P
  upperRight := Matrix.of fun i j => ∫ a, (M a).upperRight i j ∂P
  lowerLeft := Matrix.of fun i j => ∫ a, (M a).lowerLeft i j ∂P
  lowerRight := Matrix.of fun i j => ∫ a, (M a).lowerRight i j ∂P

/-- The annealed block is the mean block of the coarse block. -/
theorem annealedBlock_eq_meanBlock (P : Measure (CoeffSpace d)) (U : Set (Vec d)) :
    annealedBlock P U = meanBlock P fun a => coarseBlock U a := rfl

/-- The entries of the mean block are the integrals of the entries. -/
theorem blockMatEntry_meanBlock (P : Measure (CoeffSpace d))
    (M : CoeffSpace d → BlockMat d) (α β : BlockCoord d) :
    blockMatEntry (meanBlock P M) α β = ∫ a, blockMatEntry (M a) α β ∂P := by
  cases α <;> cases β <;> rfl

/-- The entrywise integrability of a block-valued observable. -/
@[expose]
def HasIntegrableBlock (P : Measure (CoeffSpace d)) (M : CoeffSpace d → BlockMat d) :
    Prop :=
  ∀ α β : BlockCoord d, Integrable (fun a => blockMatEntry (M a) α β) P

theorem hasIntegrableBlock_coarseBlock {P : Measure (CoeffSpace d)} {U : Set (Vec d)}
    (hint : HasIntegrableCoarseBlock P U) :
    HasIntegrableBlock P fun a => coarseBlock U a := hint

/-- The quadratic form of a block-valued observable is integrable as soon as its
entries are. -/
theorem integrable_blockVecDot_of_hasIntegrableBlock {P : Measure (CoeffSpace d)}
    {M : CoeffSpace d → BlockMat d} (hint : HasIntegrableBlock P M) (X : BlockVec d) :
    Integrable (fun a => blockVecDot X (blockMatVecMul (M a) X)) P := by
  have hrw : (fun a => blockVecDot X (blockMatVecMul (M a) X))
      = fun a => ∑ α : BlockCoord d, ∑ β : BlockCoord d,
          toFullBlockVec X α *
            (blockMatEntry (M a) α β * toFullBlockVec X β) := by
    funext a
    exact blockVecDot_blockMatVecMul_eq_sum _ _
  rw [hrw]
  refine integrable_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ => ?_
  exact ((hint α β).mul_const (toFullBlockVec X β)).const_mul (toFullBlockVec X α)

/-- **The quadratic form of the mean block is the average of the quadratic
forms.** -/
theorem blockVecDot_meanBlock_eq_integral {P : Measure (CoeffSpace d)}
    {M : CoeffSpace d → BlockMat d} (hint : HasIntegrableBlock P M) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul (meanBlock P M) X)
      = ∫ a, blockVecDot X (blockMatVecMul (M a) X) ∂P := by
  have hrw : (∫ a, blockVecDot X (blockMatVecMul (M a) X) ∂P)
      = ∫ a, ∑ α : BlockCoord d, ∑ β : BlockCoord d,
          toFullBlockVec X α *
            (blockMatEntry (M a) α β * toFullBlockVec X β) ∂P := by
    refine integral_congr_ae (_root_.Filter.Eventually.of_forall fun a => ?_)
    exact blockVecDot_blockMatVecMul_eq_sum _ _
  rw [blockVecDot_blockMatVecMul_eq_sum, hrw,
    integral_finsetSum _ fun α _ =>
      integrable_finsetSum _ fun β _ =>
        ((hint α β).mul_const (toFullBlockVec X β)).const_mul (toFullBlockVec X α)]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [integral_finsetSum _ fun β _ =>
    ((hint α β).mul_const (toFullBlockVec X β)).const_mul (toFullBlockVec X α)]
  refine Finset.sum_congr rfl fun β _ => ?_
  calc toFullBlockVec X α * (blockMatEntry (meanBlock P M) α β * toFullBlockVec X β)
      = (∫ a, blockMatEntry (M a) α β ∂P) *
          (toFullBlockVec X α * toFullBlockVec X β) := by
        rw [blockMatEntry_meanBlock]
        ring
    _ = ∫ a, blockMatEntry (M a) α β *
          (toFullBlockVec X α * toFullBlockVec X β) ∂P :=
        (integral_mul_const _ _).symm
    _ = ∫ a, toFullBlockVec X α *
          (blockMatEntry (M a) α β * toFullBlockVec X β) ∂P := by
        refine integral_congr_ae (_root_.Filter.Eventually.of_forall fun a => ?_)
        ring

/-! ## Monotonicity of the mean -/

/-- **The mean block is monotone.**  A block-valued observable dominated at
almost every sample has a dominated mean.  This is the printed step
`𝐀hom(□_l) ≥ E[Ã_z]`, one-sided and free of error terms. -/
theorem blockMatLoewnerLE_meanBlock {P : Measure (CoeffSpace d)}
    {M N : CoeffSpace d → BlockMat d} (hM : HasIntegrableBlock P M)
    (hN : HasIntegrableBlock P N)
    (hle : ∀ᵐ a ∂P, BlockMatLoewnerLE (M a) (N a)) :
    BlockMatLoewnerLE (meanBlock P M) (meanBlock P N) := by
  intro X
  rw [blockVecDot_meanBlock_eq_integral hM, blockVecDot_meanBlock_eq_integral hN]
  have hpt : (fun a => blockVecDot X (blockMatVecMul (M a) X)) ≤ᵐ[P]
      fun a => blockVecDot X (blockMatVecMul (N a) X) := by
    filter_upwards [hle] with a ha
    have h := ha X
    linarith only [h]
  have hint := integral_mono_ae (integrable_blockVecDot_of_hasIntegrableBlock hM X)
    (integrable_blockVecDot_of_hasIntegrableBlock hN X) hpt
  linarith only [hint]

end

end Quenched
end HighContrast
end HCPolySupport
