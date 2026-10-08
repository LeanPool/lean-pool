/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastVarianceHatted
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSingleCellVariance
public import LeanPool.HighContrastHomogenization.Provider.Quenched.AlignedSubdivisionVariance
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastWeakAverageVariance
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastWeakCap
public import LeanPool.HighContrastHomogenization.Provider.Quenched.FixedGridWindowAccount

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastVarianceLagged

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The lagged variance measurability and average carrier

Measurability of the subdivision-average fluctuation size against an
arbitrary positive frame, by the entrywise route, and its identification
with the norm of the normalized block.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

noncomputable section

variable {d : ℕ}

/-- Measurability of the subdivision-average fluctuation size. -/
theorem aemeasurable_blockSize_subdivisionDefect
    {P : Measure (CoeffSpace d)} {q : Mat d} (hq : q.PosDef)
    (j : ℤ) (Z : Finset (Fin d → ℤ)) {Gj Gp : BlockMat d}
    (hGjsym : IsSymmetricBlockMat Gj)
    (hGpsym : IsSymmetricBlockMat Gp)
    (hGppd : Book.Ch02.BlockPosDef Gp) :
    AEMeasurable (fun a => blockSize
      (blockSub (ofFullBlockMat ((Z.card : ℝ)⁻¹ •
        ∑ w ∈ Z, toFullBlockMat (coarseBlock (adaptedCellAt q j w) a)))
        Gj) Gp) P := by
  classical
  have hXw : ∀ (w : Fin d → ℤ) (γ δ : BlockCoord d), AEStronglyMeasurable
      (fun a =>
        toFullBlockMat (coarseBlock (adaptedCellAt q j w) a) γ δ) P := by
    intro w γ δ
    have h := Transport.hasMeasurableCoarseBlock_adaptedCellTranslate
      P hq j (adaptedCellCenter q j w)
    rw [← adaptedCellAt_eq_adaptedCellTranslate] at h
    exact h γ δ
  have hraw : AEMeasurable (fun a => fun γ δ : BlockCoord d =>
      (Z.card : ℝ)⁻¹ *
        ∑ w ∈ Z,
          toFullBlockMat (coarseBlock (adaptedCellAt q j w) a) γ δ -
        toFullBlockMat Gj γ δ) P :=
    aemeasurable_pi_iff.mpr fun γ => aemeasurable_pi_iff.mpr fun δ =>
      (((Finset.aemeasurable_fun_sum _ fun w _ =>
        (hXw w γ δ).aemeasurable).const_mul _).sub aemeasurable_const)
  have hcont : Measurable (fun e : BlockCoord d → BlockCoord d → ℝ =>
      ‖matSqrt (toFullBlockMat Gp)⁻¹ * (Matrix.of e : FullBlockMat d) *
        matSqrt (toFullBlockMat Gp)⁻¹‖) := by
    refine Continuous.measurable (continuous_norm.comp ?_)
    refine continuous_matrix fun α β => ?_
    simp only [Matrix.mul_apply, Matrix.of_apply]
    refine continuous_finsetSum _ fun δ _ => ?_
    refine Continuous.mul (continuous_finsetSum _ fun γ _ => ?_)
      continuous_const
    exact Continuous.mul continuous_const
      ((continuous_apply δ).comp (continuous_apply γ))
  have hcomp := hcont.comp_aemeasurable hraw
  refine hcomp.congr (_root_.Filter.Eventually.of_forall fun a => ?_)
  change ‖matSqrt (toFullBlockMat Gp)⁻¹ *
      (Matrix.of fun γ δ : BlockCoord d =>
        (Z.card : ℝ)⁻¹ *
          ∑ w ∈ Z,
            toFullBlockMat (coarseBlock (adaptedCellAt q j w) a) γ δ -
          toFullBlockMat Gj γ δ) *
      matSqrt (toFullBlockMat Gp)⁻¹‖ =
    blockSize
      (blockSub (ofFullBlockMat ((Z.card : ℝ)⁻¹ •
        ∑ w ∈ Z, toFullBlockMat (coarseBlock (adaptedCellAt q j w) a)))
        Gj) Gp
  have hmat : (Matrix.of (fun γ δ : BlockCoord d =>
      (Z.card : ℝ)⁻¹ *
        ∑ w ∈ Z,
          toFullBlockMat (coarseBlock (adaptedCellAt q j w) a) γ δ -
        toFullBlockMat Gj γ δ) : FullBlockMat d) =
      (Z.card : ℝ)⁻¹ •
        ∑ w ∈ Z,
          toFullBlockMat (coarseBlock (adaptedCellAt q j w) a) -
        toFullBlockMat Gj := by
    ext γ δ
    simp only [Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.sum_apply, smul_eq_mul]
  have hsubsym : IsSymmetricBlockMat
      (blockSub (ofFullBlockMat ((Z.card : ℝ)⁻¹ •
        ∑ w ∈ Z, toFullBlockMat (coarseBlock (adaptedCellAt q j w) a)))
        Gj) := by
    refine isSymmetricBlockMat_blockSub ?_ hGjsym
    refine isSymmetricBlockMat_of_posSemidef ?_
    rw [toFullBlockMat_ofFullBlockMat]
    refine Matrix.PosSemidef.smul ?_ (by positivity : (0 : ℝ) ≤ _)
    refine Matrix.posSemidef_sum Z fun w hw => ?_
    exact (posDef_toFullBlockMat
      (Recurrence.isSymmetricBlockMat_coarseBlock_adaptedCellAt q j w a)
      (Recurrence.blockPosDef_coarseBlock_adaptedCellAt hq j w a)).posSemidef
  rw [hmat, PortableHistory.blockSize_eq_norm hsubsym hGpsym hGppd,
    Recurrence.toFullBlockMat_normalizedBlock, Transport.toFullBlockMat_blockSub,
    toFullBlockMat_ofFullBlockMat]

end

end HCPolySupport.HighContrast.Quenched
