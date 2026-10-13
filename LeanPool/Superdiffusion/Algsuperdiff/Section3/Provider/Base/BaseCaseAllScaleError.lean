/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Base.BaseCaseMStarStarError
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.TwoTermPromotion

/-!
# BaseCaseAllScaleError

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The corrected all-scale base-case error tail

This module proves the error half of the corrected Section 3.2 base case at
every integer scale.  The cutoff response square is bounded almost everywhere
by a deterministic plateau plus the linearly weighted descendant mass.  Both
square roots have the same all-scale core, so the one-term square-root transform
gives a `Gamma_2` tail at the exact corrected first amplitude.  Promoting that
tail with a zero `Gamma_4` witness gives the source's two-term conclusion at
the two exact corrected amplitudes.

## Main results

* `cutoffHomogenizationError_isOneSidedOrlicz_allScale` proves the stronger
  direct one-sided `Gamma_2` tail used internally.
* `cutoffHomogenizationError_isTwoTermBigOWith_allScale` proves the corrected
  source-facing all-scale two-term tail.
-/

namespace Algsuperdiff.Section3.Provider.Base

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.IndependentSums
open Algsuperdiff.Section3.Provider.Scales

noncomputable section

variable {d : ℕ}

/-- At every integer scale, the cutoff homogenization error has a corrected
one-sided `Gamma_2` tail at the first all-scale amplitude. -/
theorem cutoffHomogenizationError_isOneSidedOrlicz_allScale
    (M : ABKModel d) (m : ℤ) (s : {s : ℝ // s ∈ Set.Ioo 0 1}) :
    Probability.IsOneSidedOrlicz
      (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2)
      (Observable.cutoffHomogenizationError M m
        ⟨(s : ℝ), (Set.mem_Ioo.mp s.2).1⟩)
      (baseCaseMStarStarErrorConst d * M.nu⁻¹ *
        (Real.sqrt M.gamma)⁻¹ * (3 : ℝ) ^ (M.gamma * (m : ℝ)) *
          Real.sqrt (baseLoss d s)) := by
  let core : ℝ := M.nu⁻¹ * (Real.sqrt M.gamma)⁻¹ *
    (3 : ℝ) ^ (M.gamma * (m : ℝ)) * Real.sqrt (baseLoss d s)
  let B : ℝ := cutoffBaseSqrtConst d * core
  have hcore : 0 < core := by
    dsimp only [core]
    exact mul_pos
      (mul_pos
        (mul_pos (inv_pos.mpr M.nu_pos)
          (inv_pos.mpr (Real.sqrt_pos_of_pos M.shellPrefix.gamma_pos)))
        (Real.rpow_pos_of_pos (by norm_num) _))
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
          cutoffPlateauSqrtConst d * M.nu⁻¹ *
            (Real.sqrt M.gamma)⁻¹ * (3 : ℝ) ^ (M.gamma * (m : ℝ)) *
              Real.sqrt (baseLoss d s) :=
        sqrt_cutoffPlateauAmplitude_le_allScale M m s
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
        cutoffMassSqrtConst d * M.nu⁻¹ *
          (Real.sqrt M.gamma)⁻¹ * (3 : ℝ) ^ (M.gamma * (m : ℝ)) *
            Real.sqrt (baseLoss d s) :=
        sqrt_cutoffMassTailScale_le_allScale M m s
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

/-- At every integer scale, the cutoff homogenization error satisfies the
corrected two-term `Gamma_2`/`Gamma_4` base-case tail. -/
theorem cutoffHomogenizationError_isTwoTermBigOWith_allScale
    (M : ABKModel d) (m : ℤ) (s : {s : ℝ // s ∈ Set.Ioo 0 1}) :
    Probability.IsTwoTermBigOWith
      (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2) (gammaSigma 4)
      (Observable.cutoffHomogenizationError M m
        ⟨(s : ℝ), (Set.mem_Ioo.mp s.2).1⟩)
      (baseCaseMStarStarErrorConst d * M.nu⁻¹ *
        (Real.sqrt M.gamma)⁻¹ * (3 : ℝ) ^ (M.gamma * (m : ℝ)) *
          Real.sqrt (baseLoss d s))
      (baseCaseMStarStarErrorConst d * (Real.sqrt M.nu)⁻¹ *
        (Real.sqrt (Real.sqrt M.gamma))⁻¹ *
          (3 : ℝ) ^ (M.gamma * (m : ℝ) / 2) *
            Real.sqrt (Real.sqrt (baseLoss d s))) := by
  have htail := cutoffHomogenizationError_isOneSidedOrlicz_allScale M m s
  have hA1pos :
      0 < baseCaseMStarStarErrorConst d * M.nu⁻¹ *
        (Real.sqrt M.gamma)⁻¹ * (3 : ℝ) ^ (M.gamma * (m : ℝ)) *
          Real.sqrt (baseLoss d s) := by
    exact mul_pos
      (mul_pos
        (mul_pos
          (mul_pos (baseCaseMStarStarErrorConst_pos d) (inv_pos.mpr M.nu_pos))
          (inv_pos.mpr (Real.sqrt_pos_of_pos M.shellPrefix.gamma_pos)))
        (Real.rpow_pos_of_pos (by norm_num) _))
      (Real.sqrt_pos_of_pos (baseLoss_pos d s))
  have hA2pos :
      0 < baseCaseMStarStarErrorConst d * (Real.sqrt M.nu)⁻¹ *
        (Real.sqrt (Real.sqrt M.gamma))⁻¹ *
          (3 : ℝ) ^ (M.gamma * (m : ℝ) / 2) *
            Real.sqrt (Real.sqrt (baseLoss d s)) := by
    exact mul_pos
      (mul_pos
        (mul_pos
          (mul_pos (baseCaseMStarStarErrorConst_pos d)
            (inv_pos.mpr (Real.sqrt_pos_of_pos M.nu_pos)))
          (inv_pos.mpr
            (Real.sqrt_pos_of_pos
              (Real.sqrt_pos_of_pos M.shellPrefix.gamma_pos))))
        (Real.rpow_pos_of_pos (by norm_num) _))
      (Real.sqrt_pos_of_pos
        (Real.sqrt_pos_of_pos (baseLoss_pos d s)))
  exact Provider.Orlicz.isTwoTermBigOWith_of_isOneSidedOrlicz
    (by norm_num) (by norm_num) htail (le_refl _) hA1pos hA2pos

end

end Algsuperdiff.Section3.Provider.Base
