/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedUnitCubeDirichletContinuousKDefectResponseContraction
public import LeanPool.HighContrastHomogenization.Provider.Regularity.UnitCubeDirichletDivergenceResponse
public import LeanPool.HighContrastHomogenization.Support.Deterministic.ConstantCoefficientDirichletBesov.DirichletBridge

/-!
# High-contrast homogenization:
Provider.Regularity.RoundedUnitCubeDirichletContinuousKDefectResponseDifferenceContraction

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Difference contraction for the rounded affine response step

The selected identity response is specialized both to the rounded-reference
identity defect and to the affine datum used by the perturbative iteration.
Subtracting two affine-step weak equations cancels their common forcing and
turns the response difference into the identity Dirichlet response to the
defect acting on the datum difference.  The previously selected small
fractional order therefore contracts successive response differences with
the same strict coefficient.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- Pointwise subtraction, packaged on the unit-cube Euclidean `L²` carrier. -/
@[expose]
noncomputable def unitCubeEuclideanL2FieldSub
    (F G : UnitCubeEuclideanL2Field d) : UnitCubeEuclideanL2Field d where
  toField := fun x ↦ F x - G x
  euclideanMemL2 := by
    have h := F.euclideanMemL2.sub G.euclideanMemL2
    convert h using 1
    · rfl

@[simp] theorem unitCubeEuclideanL2FieldSub_apply
    (F G : UnitCubeEuclideanL2Field d) (x : Vec d) :
    unitCubeEuclideanL2FieldSub F G x = F x - G x :=
  rfl

/-- One affine Picard step: solve the identity Dirichlet problem with the
common forcing plus the rounded-reference defect acting on the current
gradient field. -/
@[expose]
noncomputable def roundedUnitCubeDirichletContinuousKIterationStep
    [NeZero d] (abar : Mat d) (hS : (symmPart abar).PosDef)
    (h F : UnitCubeEuclideanL2Field d) :
    H10Function (openCubeSet (originCube d 0)) :=
  unitCubeDirichletDivergenceResponse
    (unitCubeEuclideanL2FieldAdd h
      (unitCubeEuclideanL2FieldConstMatrixMul
        (roundedReferenceMatrix abar hS - 1) F))

/-- The selected affine step satisfies its defining identity Dirichlet weak
equation with the forcing and rounded defect kept as a literal sum. -/
theorem roundedUnitCubeDirichletContinuousKIterationStep_problem
    [NeZero d] (abar : Mat d) (hS : (symmPart abar).PosDef)
    (h F : UnitCubeEuclideanL2Field d) :
    CubeDirichletDivergenceProblem (originCube d 0)
      (roundedUnitCubeDirichletContinuousKIterationStep abar hS h F)
      (unitCubeEuclideanL2FieldAdd h
        (unitCubeEuclideanL2FieldConstMatrixMul
          (roundedReferenceMatrix abar hS - 1) F)) :=
  unitCubeDirichletDivergenceResponse_problem
    (unitCubeEuclideanL2FieldAdd h
      (unitCubeEuclideanL2FieldConstMatrixMul
        (roundedReferenceMatrix abar hS - 1) F))

/-- For each positive dimension, the small order and contraction coefficient
selected before all analytic inputs contract the difference of any two
selected rounded defect responses by the energy of the datum difference. -/
theorem exists_roundedUnitCubeDirichletContinuousKIterationStepDifferenceContraction
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
            (h F G : UnitCubeEuclideanL2Field d),
            unitCubeNormalizedContinuousKEnergy s
                (unitCubeGradientEuclideanL2Field
                  (roundedUnitCubeDirichletContinuousKIterationStep abar hS h F -
                    roundedUnitCubeDirichletContinuousKIterationStep abar hS h G)) ≤
              ((ENNReal.ofReal A) ^ (2 * s.1) *
                  ENNReal.ofReal ((1 / 100 : ℝ) ^ 2)) *
                unitCubeNormalizedContinuousKEnergy s
                  (unitCubeEuclideanL2FieldSub F G) := by
  rcases
      exists_roundedUnitCubeDirichletContinuousKDefectResponseContraction d with
    ⟨A, honeA, s, hs, hfactor, hcoefficient, honeCoefficient, hcontraction⟩
  refine ⟨A, honeA, s, hs, hfactor, hcoefficient, honeCoefficient, ?_⟩
  intro abar hS h F G
  let D : Mat d := roundedReferenceMatrix abar hS - 1
  let wF : H10Function (openCubeSet (originCube d 0)) :=
    roundedUnitCubeDirichletContinuousKIterationStep abar hS h F
  let wG : H10Function (openCubeSet (originCube d 0)) :=
    roundedUnitCubeDirichletContinuousKIterationStep abar hS h G
  have hFMem : MemLp
      (unitCubeEuclideanL2FieldAdd h
        (unitCubeEuclideanL2FieldConstMatrixMul D F))
      (2 : ℝ≥0∞) (normalizedCubeMeasure (originCube d 0)) :=
    unitCubeEuclideanL2Field_memLp_normalizedCubeMeasure
      (unitCubeEuclideanL2FieldAdd h
        (unitCubeEuclideanL2FieldConstMatrixMul D F))
  have hGMem : MemLp
      (unitCubeEuclideanL2FieldAdd h
        (unitCubeEuclideanL2FieldConstMatrixMul D G))
      (2 : ℝ≥0∞) (normalizedCubeMeasure (originCube d 0)) :=
    unitCubeEuclideanL2Field_memLp_normalizedCubeMeasure
      (unitCubeEuclideanL2FieldAdd h
        (unitCubeEuclideanL2FieldConstMatrixMul D G))
  have hwF : CubeDirichletDivergenceProblem (originCube d 0) wF
      (unitCubeEuclideanL2FieldAdd h
        (unitCubeEuclideanL2FieldConstMatrixMul D F)) := by
    simpa only [D, wF] using
      roundedUnitCubeDirichletContinuousKIterationStep_problem abar hS h F
  have hwG : CubeDirichletDivergenceProblem (originCube d 0) wG
      (unitCubeEuclideanL2FieldAdd h
        (unitCubeEuclideanL2FieldConstMatrixMul D G)) := by
    simpa only [D, wG] using
      roundedUnitCubeDirichletContinuousKIterationStep_problem abar hS h G
  have hdatum :
      (fun x ↦
        unitCubeEuclideanL2FieldAdd h
            (unitCubeEuclideanL2FieldConstMatrixMul D F) x -
          unitCubeEuclideanL2FieldAdd h
            (unitCubeEuclideanL2FieldConstMatrixMul D G) x) =
        unitCubeEuclideanL2FieldConstMatrixMul D
          (unitCubeEuclideanL2FieldSub F G) := by
    funext x
    simp only [unitCubeEuclideanL2FieldAdd_apply,
      unitCubeEuclideanL2FieldConstMatrixMul_apply,
      unitCubeEuclideanL2FieldSub_apply]
    calc
      h x + matVecMul D (F x) - (h x + matVecMul D (G x)) =
          matVecMul D (F x) - matVecMul D (G x) := by abel
      _ = matVecMul D (F x - G x) :=
        matVecMul_sub_vec D (F x) (G x)
  have hsubProblem : CubeDirichletDivergenceProblem (originCube d 0) (wF - wG)
      (unitCubeEuclideanL2FieldConstMatrixMul D
        (unitCubeEuclideanL2FieldSub F G)) := by
    have hproblem := cubeDirichletDivergenceProblem_sub hFMem hGMem hwF hwG
    rw [hdatum] at hproblem
    exact hproblem
  have hbound := hcontraction abar hS
    (unitCubeEuclideanL2FieldSub F G) (wF - wG) (by
      simpa only [D] using hsubProblem)
  simpa only [wF, wG] using hbound

end

end HighContrast
end HCPolySupport
