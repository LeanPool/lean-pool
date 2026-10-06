/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileCenterPointwise
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# High-contrast homogenization: Provider.Response.ProfileRecentMeasurability

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Measurability of the recent weak-norm sums

The two recent sums are finite combinations of coarse-block observables.  The
cell term uses two random blocks on the same sample, while the averaged term
uses the positive averaged-defect measurability theorem.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory

open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The normalized size of the difference of two random coarse blocks is
almost everywhere measurable. -/
theorem aemeasurable_blockSize_coarseBlock_sub_coarseBlock
    {P : Measure (CoeffSpace d)} {U V : Set (Vec d)}
    (hU : HasMeasurableCoarseBlock P U)
    (hV : HasMeasurableCoarseBlock P V)
    {E : BlockMat d} (hE : IsSymmetricBlockMat E)
    (hEpd : BlockPosDef E) :
    AEMeasurable (fun a ↦
      blockSize (blockSub (coarseBlock U a) (coarseBlock V a)) E) P := by
  have hrw : (fun a ↦
      blockSize (blockSub (coarseBlock U a) (coarseBlock V a)) E) =
      fun a ↦ ‖(Matrix.of fun α β ↦
        toFullBlockMat
          (normalizedBlock
            (blockSub (coarseBlock U a) (coarseBlock V a)) E) α β :
          FullBlockMat d)‖ := by
    funext a
    exact PortableHistory.blockSize_eq_norm
      (isSymmetricBlockMat_blockSub
        (isSymmetricBlockMat_coarseBlock U a)
        (isSymmetricBlockMat_coarseBlock V a)) hE hEpd
  have hentry : ∀ δ γ : BlockCoord d,
      AEStronglyMeasurable (fun a : CoeffSpace d ↦
        toFullBlockMat (coarseBlock U a) δ γ -
          toFullBlockMat (coarseBlock V a) δ γ) P := by
    intro δ γ
    exact (hU δ γ).sub (hV δ γ)
  have hcomponent : ∀ α β : BlockCoord d,
      AEStronglyMeasurable (fun a ↦
        toFullBlockMat
          (normalizedBlock
            (blockSub (coarseBlock U a) (coarseBlock V a)) E) α β) P := by
    intro α β
    have hfun : (fun a ↦
        toFullBlockMat
          (normalizedBlock
            (blockSub (coarseBlock U a) (coarseBlock V a)) E) α β) =
        fun a ↦ ∑ γ : BlockCoord d, ∑ δ : BlockCoord d,
          matSqrt ((toFullBlockMat E)⁻¹) α δ *
              (toFullBlockMat (coarseBlock U a) δ γ -
                toFullBlockMat (coarseBlock V a) δ γ) *
            matSqrt ((toFullBlockMat E)⁻¹) γ β := by
      funext a
      rw [Recurrence.toFullBlockMat_normalizedBlock_apply]
      exact Finset.sum_congr rfl fun γ _ ↦
        Finset.sum_congr rfl fun δ _ ↦ by
          rw [Recurrence.toFullBlockMat_blockSub_apply]
    have hsum : AEStronglyMeasurable
        (∑ γ : BlockCoord d, ∑ δ : BlockCoord d,
          fun a : CoeffSpace d ↦
            matSqrt ((toFullBlockMat E)⁻¹) α δ *
                (toFullBlockMat (coarseBlock U a) δ γ -
                  toFullBlockMat (coarseBlock V a) δ γ) *
              matSqrt ((toFullBlockMat E)⁻¹) γ β) P :=
      Finset.aestronglyMeasurable_sum _ fun γ _ ↦
        Finset.aestronglyMeasurable_sum _ fun δ _ ↦
          (((hentry δ γ).const_mul _).mul_const _)
    rw [hfun]
    refine hsum.congr (Filter.Eventually.of_forall fun a ↦ ?_)
    simp only [Finset.sum_apply]
  rw [hrw]
  have hpi : AEMeasurable (fun a ↦ fun α β ↦
      toFullBlockMat
        (normalizedBlock
          (blockSub (coarseBlock U a) (coarseBlock V a)) E) α β) P :=
    aemeasurable_pi_iff.mpr fun α ↦
      aemeasurable_pi_iff.mpr fun β ↦ (hcomponent α β).aemeasurable
  have hcont : Measurable (fun e : BlockCoord d → BlockCoord d → ℝ ↦
      ‖(Matrix.of e : FullBlockMat d)‖) :=
    Continuous.measurable (continuous_norm.comp (continuous_matrix fun α β ↦
      (continuous_apply β).comp (continuous_apply α)))
  exact hcont.comp_aemeasurable hpi

/-- One recent cell defect is almost everywhere measurable. -/
theorem aemeasurable_diagonalWeakCellDefect
    {P : Measure (CoeffSpace d)} {q : Mat d} (hq : q.PosDef)
    (k t : ℤ) {E : BlockMat d} (hE : IsSymmetricBlockMat E)
    (hEpd : BlockPosDef E) :
    AEMeasurable (diagonalWeakCellDefect q k t E) P := by
  have hterm : ∀ w : Fin d → ℤ, AEMeasurable (fun a ↦
      blockSize
        (blockSub (adaptedResponse q k w a)
          (coarseBlock (adaptedCell q t) a)) E ^ 2) P := by
    intro w
    exact (aemeasurable_blockSize_coarseBlock_sub_coarseBlock
      (Recurrence.hasMeasurableCoarseBlock_adaptedCellAt P hq k w)
      (Recurrence.hasMeasurableCoarseBlock_adaptedCell P hq t) hE hEpd).pow_const 2
  rw [show diagonalWeakCellDefect q k t E = fun a ↦
      Real.sqrt (avsum (alignedIndex q k t) fun w ↦
        blockSize
          (blockSub (adaptedResponse q k w a)
            (coarseBlock (adaptedCell q t) a)) E ^ 2) by rfl]
  apply AEMeasurable.sqrt
  unfold avsum
  exact (Finset.aemeasurable_fun_sum (alignedIndex q k t)
    fun w _ ↦ hterm w).const_mul _

/-- The recent cell sum is almost everywhere measurable. -/
theorem aemeasurable_diagonalWeakCellSum
    {P : Measure (CoeffSpace d)} {q : Mat d} (hq : q.PosDef)
    (t : ℤ) (H : ℕ) (s : ℝ) {E : BlockMat d}
    (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E) :
    AEMeasurable (diagonalWeakCellSum q t H s E) P := by
  rw [show diagonalWeakCellSum q t H s E = fun a ↦
      ∑ j ∈ Finset.range (H + 1),
        (3 : ℝ) ^ (-s * (j : ℝ)) *
          diagonalWeakCellDefect q (t - (j : ℤ)) t E a by rfl]
  exact Finset.aemeasurable_fun_sum (Finset.range (H + 1)) fun j _ ↦
    (aemeasurable_diagonalWeakCellDefect hq (t - (j : ℤ)) t hE hEpd).const_mul _

end

end HCPolySupport.HighContrast.Response
