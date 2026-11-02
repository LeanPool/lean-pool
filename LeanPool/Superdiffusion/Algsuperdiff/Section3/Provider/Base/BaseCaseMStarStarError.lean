/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Base.CutoffBaseTailArithmetic
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Tail.OneTermSqrt

/-!
# BaseCaseMStarStarError

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The corrected base-case error tail below the first landmark

This module proves the error half of the corrected Section 3.2 base case on
the range `m <= m**`.  The cutoff response square is bounded almost
everywhere by a deterministic plateau plus the linearly weighted descendant
mass.  The latter has a one-sided `Gamma_1` tail.  The one-term square-root
transform turns these two inputs into the exact one-sided `Gamma_2` bound, with
one explicit dimension-only constant chosen before the model and all scale
parameters.

## Main results

* `baseCaseMStarStarErrorConst` is the explicit positive dimension-only
  constant for this branch.
* `cutoffHomogenizationError_isOneSidedOrlicz_le_mStarStar` proves the direct
  model-specific tail at that constant.
* `exists_baseCaseMStarStarErrorConst` packages the residual clause with the
  constant chosen before `M`, `m`, and `s`.
-/

namespace Algsuperdiff.Section3.Provider.Base

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.IndependentSums
open Algsuperdiff.Section3.Provider.Scales

noncomputable section

variable {d : ℕ}

/-- The explicit dimension-only constant in the corrected `m <= m**` error
tail. -/
noncomputable def baseCaseMStarStarErrorConst (d : ℕ) : ℝ :=
  Tail.gammaTwoAdditionConst * cutoffBaseSqrtConst d

/-- The corrected `m <= m**` error-tail constant is strictly positive. -/
theorem baseCaseMStarStarErrorConst_pos (d : ℕ) :
    0 < baseCaseMStarStarErrorConst d := by
  exact mul_pos Tail.gammaTwoAdditionConst_pos (cutoffBaseSqrtConst_pos d)

/-- Below `m**`, the cutoff homogenization error has the corrected one-sided
`Gamma_2` tail with its explicit dimension-only constant. -/
theorem cutoffHomogenizationError_isOneSidedOrlicz_le_mStarStar
    (M : ABKModel d) (m : ℤ) (hm : m ≤ mStarStar M)
    (s : {s : ℝ // s ∈ Set.Ioo 0 1}) :
    Probability.IsOneSidedOrlicz
      (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2)
      (Observable.cutoffHomogenizationError M m
        ⟨(s : ℝ), (Set.mem_Ioo.mp s.2).1⟩)
      (baseCaseMStarStarErrorConst d *
        (Real.sqrt (Disorder.cstarPlus M))⁻¹ * Real.sqrt M.gamma *
          Real.sqrt (baseLoss d s)) := by
  let core : ℝ := (Real.sqrt (Disorder.cstarPlus M))⁻¹ *
    Real.sqrt M.gamma * Real.sqrt (baseLoss d s)
  let B : ℝ := cutoffBaseSqrtConst d * core
  have hcore : 0 < core := by
    dsimp only [core]
    exact mul_pos
      (mul_pos
        (inv_pos.mpr (Real.sqrt_pos_of_pos (Disorder.cstarPlus_pos M)))
        (Real.sqrt_pos_of_pos M.shellPrefix.gamma_pos))
      (Real.sqrt_pos_of_pos (baseLoss_pos d s))
  have hBpos : 0 < B := by
    exact mul_pos (cutoffBaseSqrtConst_pos d) hcore
  have hplateauConst :
      cutoffPlateauSqrtConst d ≤ cutoffBaseSqrtConst d := by
    exact le_add_of_nonneg_right (cutoffMassSqrtConst_pos d).le
  have hmassConst : cutoffMassSqrtConst d ≤ cutoffBaseSqrtConst d := by
    exact le_add_of_nonneg_left (cutoffPlateauSqrtConst_pos d).le
  have hDb : Real.sqrt (cutoffPlateauAmplitude M m) ≤ B := by
    calc
      Real.sqrt (cutoffPlateauAmplitude M m) ≤
          cutoffPlateauSqrtConst d *
            (Real.sqrt (Disorder.cstarPlus M))⁻¹ * Real.sqrt M.gamma *
              Real.sqrt (baseLoss d s) :=
        sqrt_cutoffPlateauAmplitude_le_mStarStar M m s hm
      _ = cutoffPlateauSqrtConst d * core := by
        simp only [core, mul_assoc]
      _ ≤ cutoffBaseSqrtConst d * core :=
        mul_le_mul_of_nonneg_right hplateauConst hcore.le
      _ = B := rfl
  have hAb :
      Real.sqrt
          (gammaTriangleConst 1 * cutoffMassLinearWeightedScale M m s) ≤ B := by
    calc
      Real.sqrt
          (gammaTriangleConst 1 * cutoffMassLinearWeightedScale M m s) ≤
        cutoffMassSqrtConst d *
          (Real.sqrt (Disorder.cstarPlus M))⁻¹ * Real.sqrt M.gamma *
            Real.sqrt (baseLoss d s) :=
        sqrt_cutoffMassTailScale_le_mStarStar M m s hm
      _ = cutoffMassSqrtConst d * core := by
        simp only [core, mul_assoc]
      _ ≤ cutoffBaseSqrtConst d * core :=
        mul_le_mul_of_nonneg_right hmassConst hcore.le
      _ = B := rfl
  have htail :=
    Tail.isOneSidedOrlicz_gammaSigma_two_of_sq_le_add
      (mu := (Cutoff.cutoffSampleLaw M).toMeasure)
      (X := Observable.cutoffHomogenizationError M m
        ⟨(s : ℝ), (Set.mem_Ioo.mp s.2).1⟩)
      (Y := cutoffMassLinearWeightedSum M (originCube d m) m s)
      (D := cutoffPlateauAmplitude M m)
      (A := gammaTriangleConst 1 * cutoffMassLinearWeightedScale M m s)
      (B := B)
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
  simpa only [baseCaseMStarStarErrorConst, B, core, mul_assoc] using htail

/-- There is one positive dimension-only constant, chosen before the model and all
scale parameters, that proves the corrected residual clause. -/
theorem exists_baseCaseMStarStarErrorConst (d : ℕ) :
    ∃ C2 : ℝ, 0 < C2 ∧
      ∀ (M : ABKModel d) (m : ℤ), m ≤ mStarStar M →
        ∀ s : {s : ℝ // s ∈ Set.Ioo 0 1},
          Probability.IsOneSidedOrlicz
            (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2)
            (Observable.cutoffHomogenizationError M m
              ⟨(s : ℝ), (Set.mem_Ioo.mp s.2).1⟩)
            (C2 * (Real.sqrt (Disorder.cstarPlus M))⁻¹ *
              Real.sqrt M.gamma * Real.sqrt (baseLoss d s)) := by
  refine ⟨baseCaseMStarStarErrorConst d,
    baseCaseMStarStarErrorConst_pos d, ?_⟩
  intro M m hm s
  exact cutoffHomogenizationError_isOneSidedOrlicz_le_mStarStar M m hm s

end

end Algsuperdiff.Section3.Provider.Base
