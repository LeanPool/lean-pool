/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastWeakCellVariance
public import LeanPool.HighContrastHomogenization.Provider.Response.ConstantSkewProfiles
public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormComparison

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastWeakAverageVariance

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The recent average sums by per-scale variances

The weighted recent average sum of the weak-norm split is bounded in `L²(P)`
by the square roots of the same per-scale variance carriers and mean drops:
the normalized average defect is dominated pathwise by the average of the
per-cell normalized deviations (the operator norm of an average is at most
the average of the norms), whose first moments are the per-scale carriers by
the exponent comparison on the probability space.  This is the second
(aligned average) group of the printed display HC (3.68).
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

noncomputable section

variable {d : ℕ}

/-- The identity is its own square root (generic index type). -/
private theorem matSqrt_one' {n : Type*} [Fintype n] [DecidableEq n] :
    matSqrt (1 : Matrix n n ℝ) = 1 :=
  matSqrt_eq Matrix.PosSemidef.one Matrix.PosSemidef.one (by simp)

/-- Structural symmetry of a scaled sum of flattened symmetric blocks
(clone of the constant-skew profile helper). -/
private theorem isSymmetricBlockMat_ofFullBlockMat_smul_sum' {ι : Type*}
    (s : Finset ι) (c : ℝ) (A : ι → BlockMat d)
    (hA : ∀ i ∈ s, IsSymmetricBlockMat (A i)) :
    IsSymmetricBlockMat
      (ofFullBlockMat (c • ∑ i ∈ s, toFullBlockMat (A i))) := by
  intro α β
  simp only [blockMatEntry_ofFullBlockMat, Matrix.smul_apply,
    Matrix.sum_apply, smul_eq_mul]
  apply congrArg (c * ·)
  apply Finset.sum_congr rfl
  intro i hi
  have h := hA i hi α β
  simpa only [blockMatEntry_eq_toFullBlockMat] using h

/-- Symmetry of the per-cell deviation. -/
private theorem isSymmetricBlockMat_cellDeviation (q : Mat d) (k t : ℤ)
    (w : Fin d → ℤ) (a : CoeffSpace d) :
    IsSymmetricBlockMat
      (blockSub (adaptedResponse q k w a)
        (coarseBlock (adaptedCell q t) a)) :=
  isSymmetricBlockMat_blockSub
    (Recurrence.isSymmetricBlockMat_coarseBlock_adaptedCellAt q k w a)
    (isSymmetricBlockMat_coarseBlock _ _)

/-- Symmetry of the normalized average defect. -/
private theorem isSymmetricBlockMat_averageDefect (q : Mat d) (k t : ℤ)
    (F : BlockMat d) (a : CoeffSpace d) :
    IsSymmetricBlockMat (Response.diagonalWeakAverageDefect q k t F a) := by
  rw [Response.diagonalWeakAverageDefect_eq_normalized_average]
  refine isSymmetricBlockMat_normalizedBlock ?_
  exact isSymmetricBlockMat_ofFullBlockMat_smul_sum' _ _ _
    fun w _ => isSymmetricBlockMat_cellDeviation q k t w a

/-- Measurability of the identity-size of the average defect at an arbitrary
normalization. -/
theorem aemeasurable_blockSize_averageDefect [NeZero d]
    {P : Measure (CoeffSpace d)} {q : Mat d} (hq : q.PosDef)
    (k t : ℤ) (F : BlockMat d) :
    AEMeasurable (fun a => blockSize
      (Response.diagonalWeakAverageDefect q k t F a) (blockIdentity d)) P := by
  classical
  have hXw : ∀ (w : Fin d → ℤ) (γ δ : BlockCoord d), AEStronglyMeasurable
      (fun a => toFullBlockMat
        (blockSub (adaptedResponse q k w a)
          (coarseBlock (adaptedCell q t) a)) γ δ) P := by
    intro w γ δ
    have h1 := Recurrence.hasMeasurableCoarseBlock_adaptedCellAt P hq k w γ δ
    have h2 := Recurrence.hasMeasurableCoarseBlock_adaptedCell P hq t γ δ
    have h := h1.sub h2
    simpa only [Recurrence.toFullBlockMat_blockSub_apply] using! h
  have hraw : AEMeasurable (fun a => fun γ δ : BlockCoord d =>
      (((Response.alignedIndex q k t).card : ℝ))⁻¹ *
        ∑ w ∈ Response.alignedIndex q k t,
          toFullBlockMat
            (blockSub (adaptedResponse q k w a)
              (coarseBlock (adaptedCell q t) a)) γ δ) P :=
    aemeasurable_pi_iff.mpr fun γ => aemeasurable_pi_iff.mpr fun δ =>
      (Finset.aemeasurable_fun_sum _ fun w _ =>
        (hXw w γ δ).aemeasurable).const_mul _
  have hcont : Measurable (fun e : BlockCoord d → BlockCoord d → ℝ =>
      ‖matSqrt (toFullBlockMat F)⁻¹ * (Matrix.of e : FullBlockMat d) *
        matSqrt (toFullBlockMat F)⁻¹‖) := by
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
  show ‖matSqrt (toFullBlockMat F)⁻¹ *
      (Matrix.of fun γ δ : BlockCoord d =>
        (((Response.alignedIndex q k t).card : ℝ))⁻¹ *
          ∑ w ∈ Response.alignedIndex q k t,
            toFullBlockMat
              (blockSub (adaptedResponse q k w a)
                (coarseBlock (adaptedCell q t) a)) γ δ) *
      matSqrt (toFullBlockMat F)⁻¹‖ =
    blockSize (Response.diagonalWeakAverageDefect q k t F a) (blockIdentity d)
  have hmat : (Matrix.of (fun γ δ : BlockCoord d =>
      (((Response.alignedIndex q k t).card : ℝ))⁻¹ *
        ∑ w ∈ Response.alignedIndex q k t,
          toFullBlockMat
            (blockSub (adaptedResponse q k w a)
              (coarseBlock (adaptedCell q t) a)) γ δ) : FullBlockMat d) =
      (((Response.alignedIndex q k t).card : ℝ))⁻¹ •
        ∑ w ∈ Response.alignedIndex q k t,
          toFullBlockMat
            (blockSub (adaptedResponse q k w a)
              (coarseBlock (adaptedCell q t) a)) := by
    ext γ δ
    simp only [Matrix.of_apply, Matrix.smul_apply, Matrix.sum_apply,
      smul_eq_mul]
  rw [hmat, PortableHistory.blockSize_eq_norm
    (isSymmetricBlockMat_averageDefect q k t F a)
    Response.isSymmetricBlockMat_blockIdentity Response.blockPosDef_blockIdentity,
    Recurrence.toFullBlockMat_normalizedBlock, toFullBlockMat_blockIdentity,
    inv_one, matSqrt_one', Matrix.one_mul, Matrix.mul_one,
    Response.diagonalWeakAverageDefect_eq_normalized_average,
    Recurrence.toFullBlockMat_normalizedBlock, toFullBlockMat_ofFullBlockMat]

end

end HCPolySupport.HighContrast.Quenched
