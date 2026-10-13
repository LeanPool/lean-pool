/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Base.CutoffBaseTailArithmetic
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Tail.OneTermSqrt

/-!
# BaseCaseMStarError

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The corrected shifted base-case error tail below the second landmark

This module proves the error half of the corrected Section 3.2 base case on
the range `m <= m*`.  The cutoff response square is bounded almost everywhere
by a deterministic plateau plus the linearly weighted descendant mass.  The
plateau has square root at most one on this range, so it fits inside the
source's deterministic shift `2`.  The weighted mass has a one-sided
`Gamma_1` tail whose square-root scale gives the exact shifted `Gamma_2`
amplitude, with one dimension-only constant chosen before every model and
scale parameter.

## Main results

* `cutoffHomogenizationError_isDeterministicShiftOneSidedOrlicz_le_mStar`
  proves the direct model-specific shifted tail, with the amplitude displayed
  explicitly in terms of `cutoffMassSqrtConst`, `cstarPlus M` and `baseLoss`.
-/

namespace Algsuperdiff.Section3.Provider.Base

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.IndependentSums
open Algsuperdiff.Section3.Provider.Scales

noncomputable section

variable {d : ℕ}

/-- Below `m*`, the cutoff homogenization error has the corrected shifted
one-sided `Gamma_2` tail with its explicit dimension-only constant. -/
theorem cutoffHomogenizationError_isDeterministicShiftOneSidedOrlicz_le_mStar
    (M : ABKModel d) (m : ℤ) (hm : m ≤ mStar M)
    (s : {s : ℝ // s ∈ Set.Ioo 0 1}) :
    Probability.IsDeterministicShiftOneSidedOrlicz
      (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2)
      (Observable.cutoffHomogenizationError M m
        ⟨(s : ℝ), (Set.mem_Ioo.mp s.2).1⟩)
      2
      (cutoffMassSqrtConst d *
        (Real.sqrt (Disorder.cstarPlus M))⁻¹ * Real.sqrt (baseLoss d s)) := by
  let B : ℝ := cutoffMassSqrtConst d *
    (Real.sqrt (Disorder.cstarPlus M))⁻¹ * Real.sqrt (baseLoss d s)
  have hBpos : 0 < B := by
    dsimp only [B]
    exact mul_pos
      (mul_pos (cutoffMassSqrtConst_pos d)
        (inv_pos.mpr (Real.sqrt_pos_of_pos (Disorder.cstarPlus_pos M))))
      (Real.sqrt_pos_of_pos (baseLoss_pos d s))
  have hDb : Real.sqrt (cutoffPlateauAmplitude M m) ≤ 2 := by
    exact (sqrt_cutoffPlateauAmplitude_le_one_of_le_mStar M m hm).trans
      (by norm_num)
  have hAb :
      Real.sqrt
          (gammaTriangleConst 1 * cutoffMassLinearWeightedScale M m s) ≤ B := by
    exact sqrt_cutoffMassTailScale_le_mStar M m s hm
  have htail :=
    Tail.isDeterministicShiftOneSidedOrlicz_gammaSigma_two_of_sq_le_add
      (mu := (Cutoff.cutoffSampleLaw M).toMeasure)
      (X := Observable.cutoffHomogenizationError M m
        ⟨(s : ℝ), (Set.mem_Ioo.mp s.2).1⟩)
      (Y := cutoffMassLinearWeightedSum M (originCube d m) m s)
      (D := cutoffPlateauAmplitude M m)
      (A := gammaTriangleConst 1 * cutoffMassLinearWeightedScale M m s)
      (b := 2) (B := B)
      (Observable.measurable_cutoffHomogenizationError M m
        ⟨(s : ℝ), (Set.mem_Ioo.mp s.2).1⟩)
      (Observable.cutoffHomogenizationError_nonneg M m
        ⟨(s : ℝ), (Set.mem_Ioo.mp s.2).1⟩)
      (cutoffMassLinearWeightedSum_nonneg M (originCube d m) m s)
      (cutoffPlateauAmplitude_pos M m).le
      (mul_nonneg gammaTriangleConst_pos.le
        (cutoffMassLinearWeightedScale_pos M m s).le)
      (ae_cutoffHomogenizationError_sq_le_cutoffPlateauAmplitude_add_mass M m s)
      (isBigOWith_gammaSigma_one_cutoffMassLinearWeightedSum
        M (originCube d m) m s)
      hDb hAb hBpos
  simpa only [B] using htail

end

end Algsuperdiff.Section3.Provider.Base
