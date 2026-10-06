/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorNormalizedL2Bridge
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedEllipsoidTriadicGeometry
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CubeVolume

/-!
# High-contrast homogenization: Provider.Regularity.RoundedEllipsoidWeightedNormBridge

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Normalized weighted-energy transfer across rounded real-radius domains

This module supplies the measure-normalization part of the Lane-C terminal
consumer.  Every comparison is between the exact rounded pullback ellipsoid
and the exact origin cubes selected by `RoundedEllipsoidTriadicGeometry`.
The constants are deliberately coarse and depend only on the dimension.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- Restricting a normalized weighted gradient norm to a smaller
positive finite-volume set costs the square root of the volume ratio. -/
theorem weightedGradNorm_mono_set_le_volumeRatio
    {U V : Set (Vec d)} (hUV : U ⊆ V)
    (hUzero : volume U ≠ 0) (hUtop : volume U ≠ ⊤)
    (hVzero : volume V ≠ 0) (hVtop : volume V ≠ ⊤)
    (b : CoeffField d) (F : Vec d → Vec d) :
    weightedGradNorm b U F ≤
      (volume V / volume U) ^ (1 / 2 : ℝ) * weightedGradNorm b V F := by
  let IU : ℝ≥0∞ := ∫⁻ x in U,
    ENNReal.ofReal
      (vecDot (F x) (matVecMul (symmPart (b x)) (F x))) ∂volume
  let IV : ℝ≥0∞ := ∫⁻ x in V,
    ENNReal.ofReal
      (vecDot (F x) (matVecMul (symmPart (b x)) (F x))) ∂volume
  have hI : IU ≤ IV := by
    dsimp only [IU, IV]
    exact lintegral_mono'
      (Measure.restrict_mono_set volume hUV) le_rfl
  have hbase : IU / volume U ≤
      (volume V / volume U) * (IV / volume V) := by
    rw [ENNReal.div_le_iff hUzero hUtop]
    have hcancel :
        (volume V / volume U) * (IV / volume V) * volume U = IV := by
      calc
        (volume V / volume U) * (IV / volume V) * volume U =
            (volume V / volume U * volume U) * (IV / volume V) := by
          ac_rfl
        _ = volume V * (IV / volume V) := by
          rw [ENNReal.div_mul_cancel hUzero hUtop]
        _ = IV := ENNReal.mul_div_cancel hVzero hVtop
    exact hI.trans_eq hcancel.symm
  have hrpow := ENNReal.rpow_le_rpow hbase
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [ENNReal.mul_rpow_of_nonneg _ _
    (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hrpow
  simpa only [weightedGradNorm, eVolumeAverage, IU, IV] using hrpow

end

end HighContrast
end HCPolySupport
