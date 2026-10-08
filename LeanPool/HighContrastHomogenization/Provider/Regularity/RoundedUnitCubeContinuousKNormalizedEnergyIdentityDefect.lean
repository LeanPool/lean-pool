/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedReferenceDualIdentityReduction
public import LeanPool.HighContrastHomogenization.Provider.Regularity.UnitCubeContinuousKNormalizedEnergyConstantMatrix

/-!
# High-contrast homogenization:
Provider.Regularity.RoundedUnitCubeContinuousKNormalizedEnergyIdentityDefect

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Rounded identity defect on the normalized unit-cube continuous K-energy

The rounded reference differs from the identity by at most `1/100` in the
Euclidean matrix operator norm.  The constant-matrix action on the quadratic
continuous `K`-energy therefore yields the exact squared defect factor.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The rounded reference identity defect contracts the normalized quadratic
continuous `K`-energy by the square of the fixed one-percent factor. -/
theorem unitCubeNormalizedContinuousKEnergy_roundedReferenceMatrix_sub_one_mul_le
    [NeZero d] (abar : Mat d) (hS : (symmPart abar).PosDef)
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) :
    ((unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞)
          (unitCubeEuclideanL2FieldConstMatrixMul
            (roundedReferenceMatrix abar hS - 1) F)) ^ 2 +
        ENNReal.ofReal (2 * s.1) *
          (∫⁻ t in Set.Ioo (0 : ℝ) 1,
            continuousKSeminormIntegrand s.1
              (unitCubeEuclideanL2FieldConstMatrixMul
                (roundedReferenceMatrix abar hS - 1) F) t) ≤
      ENNReal.ofReal ((1 / 100 : ℝ) ^ 2) *
        (((unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞)
            F) ^ 2 +
          ENNReal.ofReal (2 * s.1) *
            ∫⁻ t in Set.Ioo (0 : ℝ) 1,
              continuousKSeminormIntegrand s.1 F t) := by
  let D : Mat d := roundedReferenceMatrix abar hS - 1
  let energy : ℝ≥0∞ :=
    ((unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞) F) ^ 2 +
      ENNReal.ofReal (2 * s.1) *
        ∫⁻ t in Set.Ioo (0 : ℝ) 1,
          continuousKSeminormIntegrand s.1 F t
  have hnorm : ‖D‖ ≤ (1 / 100 : ℝ) := by
    simpa only [D] using norm_roundedReferenceMatrix_sub_one_le abar hS
  have hnormSq : ‖D‖ ^ 2 ≤ (1 / 100 : ℝ) ^ 2 := by
    simpa only [pow_two] using
      mul_self_le_mul_self (norm_nonneg D) hnorm
  have hcoefficient :
      ENNReal.ofReal (‖D‖ ^ 2) ≤ ENNReal.ofReal ((1 / 100 : ℝ) ^ 2) :=
    ENNReal.ofReal_le_ofReal hnormSq
  change
    ((unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞)
          (unitCubeEuclideanL2FieldConstMatrixMul D F)) ^ 2 +
        ENNReal.ofReal (2 * s.1) *
          (∫⁻ t in Set.Ioo (0 : ℝ) 1,
            continuousKSeminormIntegrand s.1
              (unitCubeEuclideanL2FieldConstMatrixMul D F) t) ≤
      ENNReal.ofReal ((1 / 100 : ℝ) ^ 2) * energy
  calc
    ((unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞)
          (unitCubeEuclideanL2FieldConstMatrixMul D F)) ^ 2 +
        ENNReal.ofReal (2 * s.1) *
          (∫⁻ t in Set.Ioo (0 : ℝ) 1,
            continuousKSeminormIntegrand s.1
              (unitCubeEuclideanL2FieldConstMatrixMul D F) t) ≤
      ENNReal.ofReal (‖D‖ ^ 2) * energy := by
        simpa only [energy] using
          unitCubeNormalizedContinuousKEnergy_constMatrixMul_le s D F
    _ ≤ ENNReal.ofReal ((1 / 100 : ℝ) ^ 2) * energy := by
      gcongr

end

end HighContrast
end HCPolySupport
