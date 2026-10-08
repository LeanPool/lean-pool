/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedUnitCubeContinuousKNormalizedEnergyIdentityDefect
public import LeanPool.HighContrastHomogenization.Provider.Regularity.UnitCubeContinuousKNormalizedEnergyAddition

/-!
# High-contrast homogenization:
Provider.Regularity.RoundedUnitCubeDirichletContinuousKDefectResponseContraction

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Small-order contraction of the rounded defect response

The identity Dirichlet response is evaluated at the rounded reference
identity-defect datum.  The selected small-order expansion factor and the
one-percent matrix-defect action combine to give a strict quadratic-energy
contraction, with every coefficient inequality derived before the later
matrix, field, and solution binders.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator

noncomputable section

/-- For each positive dimension, the small fractional order selected for the
identity Dirichlet response also makes the response to the rounded identity
defect a strict contraction in the normalized quadratic continuous
`K`-energy. -/
theorem exists_roundedUnitCubeDirichletContinuousKDefectResponseContraction
    (d : ℕ) [NeZero d] :
    ∃ A : ℝ, 1 ≤ A ∧
      ∃ s : FractionalOrder,
        s.1 < (1 : ℝ) / 12 ∧
          (ENNReal.ofReal A) ^ (2 * s.1) <
            ENNReal.ofReal ((101 : ℝ) / 100) ∧
          (ENNReal.ofReal A) ^ (2 * s.1) *
              ENNReal.ofReal ((1 / 100 : ℝ) ^ 2) <
            ENNReal.ofReal ((101 : ℝ) / 1000000) ∧
          (ENNReal.ofReal A) ^ (2 * s.1) *
              ENNReal.ofReal ((1 / 100 : ℝ) ^ 2) < 1 ∧
          ∀ (abar : Mat d) (hS : (symmPart abar).PosDef)
            (F : UnitCubeEuclideanL2Field d)
            (w : H10Function (openCubeSet (originCube d 0))),
            CubeDirichletDivergenceProblem (originCube d 0) w
                (unitCubeEuclideanL2FieldConstMatrixMul
                  (roundedReferenceMatrix abar hS - 1) F) →
              unitCubeNormalizedContinuousKEnergy s
                  (unitCubeGradientEuclideanL2Field w) ≤
                ((ENNReal.ofReal A) ^ (2 * s.1) *
                    ENNReal.ofReal ((1 / 100 : ℝ) ^ 2)) *
                  unitCubeNormalizedContinuousKEnergy s F := by
  rcases exists_unitCubeDirichletContinuousKNormalizedEnergySmallOrder d with
    ⟨A, honeA, s, hs, hfactor, hidentity⟩
  let delta : ℝ≥0∞ := ENNReal.ofReal ((1 / 100 : ℝ) ^ 2)
  let factor : ℝ≥0∞ := (ENNReal.ofReal A) ^ (2 * s.1)
  have hdeltaPos : 0 < delta := by
    exact ENNReal.ofReal_pos.mpr (sq_pos_of_pos (by norm_num))
  have hdeltaNe : delta ≠ 0 := ne_of_gt hdeltaPos
  have hdeltaTop : delta ≠ ∞ := ENNReal.ofReal_ne_top
  have hcoefficient : factor * delta <
      ENNReal.ofReal ((101 : ℝ) / 1000000) := by
    calc
      factor * delta < ENNReal.ofReal ((101 : ℝ) / 100) * delta :=
        ENNReal.mul_lt_mul_left hdeltaNe hdeltaTop (by
          simpa only [factor] using hfactor)
      _ = ENNReal.ofReal
          (((101 : ℝ) / 100) * ((1 / 100 : ℝ) ^ 2)) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 101 / 100)]
      _ = ENNReal.ofReal ((101 : ℝ) / 1000000) := by
        norm_num
  have hthreshold : ENNReal.ofReal ((101 : ℝ) / 1000000) < 1 := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)).2
      (by norm_num)
  have honeCoefficient : factor * delta < 1 :=
    hcoefficient.trans hthreshold
  refine ⟨A, honeA, s, hs, hfactor, ?_, ?_, ?_⟩
  · simpa only [factor, delta] using hcoefficient
  · simpa only [factor, delta] using honeCoefficient
  intro abar hS F w hproblem
  have hidentityResponse :
      unitCubeNormalizedContinuousKEnergy s
          (unitCubeGradientEuclideanL2Field w) ≤
        factor * unitCubeNormalizedContinuousKEnergy s
          (unitCubeEuclideanL2FieldConstMatrixMul
            (roundedReferenceMatrix abar hS - 1) F) := by
    simpa only [factor, unitCubeNormalizedContinuousKEnergy] using
      hidentity
        (unitCubeEuclideanL2FieldConstMatrixMul
          (roundedReferenceMatrix abar hS - 1) F) w hproblem
  have hdefect :
      unitCubeNormalizedContinuousKEnergy s
          (unitCubeEuclideanL2FieldConstMatrixMul
            (roundedReferenceMatrix abar hS - 1) F) ≤
        delta * unitCubeNormalizedContinuousKEnergy s F := by
    simpa only [delta, unitCubeNormalizedContinuousKEnergy] using
      unitCubeNormalizedContinuousKEnergy_roundedReferenceMatrix_sub_one_mul_le
        abar hS s F
  calc
    unitCubeNormalizedContinuousKEnergy s
        (unitCubeGradientEuclideanL2Field w) ≤
      factor * unitCubeNormalizedContinuousKEnergy s
        (unitCubeEuclideanL2FieldConstMatrixMul
          (roundedReferenceMatrix abar hS - 1) F) := hidentityResponse
    _ ≤ factor * (delta * unitCubeNormalizedContinuousKEnergy s F) := by
      simpa only [mul_comm] using mul_le_mul_left hdefect factor
    _ = (factor * delta) * unitCubeNormalizedContinuousKEnergy s F := by
      ring

end

end HighContrast
end HCPolySupport
