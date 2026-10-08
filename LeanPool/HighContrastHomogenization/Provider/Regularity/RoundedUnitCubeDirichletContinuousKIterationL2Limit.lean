/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedUnitCubeDirichletContinuousKIterationGeometric
public import LeanPool.HighContrastHomogenization.Support.Sobolev.L2Ambient
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# High-contrast homogenization:
Provider.Regularity.RoundedUnitCubeDirichletContinuousKIterationL2Limit

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Base L2 limit of the rounded affine iteration

The gradient iterates are embedded in the Hilbert-valued `L²` space on the
open centered unit cube.  On this unit cube, restricted volume is exactly the
normalized cube measure.  The geometric continuous-K increment bound controls
the Hilbert `L²` distance, so completeness supplies an actual limit without
cancelling any potentially infinite extended-real term.
-/

namespace HCPolySupport
namespace HighContrast

open _root_.Filter MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator Topology

noncomputable section

variable {d : ℕ}

/-- A proof-carrying normalized unit-cube field is a physical vector `L²`
field on the open unit cube because that cube has volume one. -/
theorem unitCubeEuclideanL2Field_memVectorL2
    (F : UnitCubeEuclideanL2Field d) :
    MemVectorL2 (openCubeSet (originCube d 0)) F := by
  change MemLp F (2 : ℝ≥0∞)
    (volumeMeasureOn (openCubeSet (originCube d 0)))
  rw [← normalizedCubeMeasure_originCube_zero_eq_volumeMeasureOn_openCubeSet]
  exact unitCubeEuclideanL2Field_memLp_normalizedCubeMeasure F

/-- The Hilbert-valued physical `L²` representative of a proof-carrying
normalized unit-cube Euclidean field. -/
@[expose]
noncomputable def unitCubeEuclideanL2FieldHilbertL2
    (F : UnitCubeEuclideanL2Field d) :
    HilbertVectorL2 (openCubeSet (originCube d 0)) :=
  toHilbertVectorL2OfVecField (unitCubeEuclideanL2Field_memVectorL2 F)

/-- The norm of the Hilbert representative is the real value of the
normalized Euclidean extended `L²` norm. -/
theorem norm_unitCubeEuclideanL2FieldHilbertL2
    (F : UnitCubeEuclideanL2Field d) :
    ‖unitCubeEuclideanL2FieldHilbertL2 F‖ =
      ((unitCenteredCubeDomain d).normalizedEuclideanLpENorm
        (2 : ℝ≥0∞) F).toReal := by
  unfold unitCubeEuclideanL2FieldHilbertL2 toHilbertVectorL2OfVecField
    toHilbertVectorL2 BoundedMeasurableDomain.normalizedEuclideanLpENorm
    BoundedMeasurableDomain.normalizedLpENorm
  rw [MeasureTheory.Lp.norm_toLp]
  rw [← normalizedCubeMeasure_originCube_zero_eq_volumeMeasureOn_openCubeSet]
  rw [← normalizedCubeMeasure_originCube_zero_eq_unitCenteredCubeDomain_normalizedVolume]
  congr 1
  have hF : MeasureTheory.AEStronglyMeasurable (hilbertifyVecField F.toField)
      (normalizedCubeMeasure (originCube d 0)) := by
    rw [normalizedCubeMeasure_originCube_zero_eq_unitCenteredCubeDomain_normalizedVolume]
    exact F.euclideanMemL2.aestronglyMeasurable
  refine MeasureTheory.eLpNorm_congr_norm_ae hF ?_ ?_
  · simpa only [euclideanNorm_eq_norm_ofVec, hilbertifyVecField] using hF.norm
  exact _root_.Filter.Eventually.of_forall fun x ↦ by
    simp only [hilbertifyVecField, euclideanNorm_eq_norm_ofVec,
      Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]

/-- The Hilbert representative respects pointwise subtraction. -/
theorem unitCubeEuclideanL2FieldHilbertL2_sub
    (F G : UnitCubeEuclideanL2Field d) :
    unitCubeEuclideanL2FieldHilbertL2 (unitCubeEuclideanL2FieldSub F G) =
      unitCubeEuclideanL2FieldHilbertL2 F -
        unitCubeEuclideanL2FieldHilbertL2 G := by
  simpa only [unitCubeEuclideanL2FieldHilbertL2,
    unitCubeEuclideanL2FieldSub_apply] using!
      (toHilbertVectorL2OfVecField_sub
        (unitCubeEuclideanL2Field_memVectorL2 F)
        (unitCubeEuclideanL2Field_memVectorL2 G))

/-- Hilbert `L²` distance is the real normalized Euclidean `L²` norm of
the pointwise field difference. -/
theorem dist_unitCubeEuclideanL2FieldHilbertL2
    (F G : UnitCubeEuclideanL2Field d) :
    dist (unitCubeEuclideanL2FieldHilbertL2 F)
        (unitCubeEuclideanL2FieldHilbertL2 G) =
      ((unitCenteredCubeDomain d).normalizedEuclideanLpENorm
        (2 : ℝ≥0∞) (unitCubeEuclideanL2FieldSub F G)).toReal := by
  rw [dist_eq_norm, ← unitCubeEuclideanL2FieldHilbertL2_sub,
    norm_unitCubeEuclideanL2FieldHilbertL2]

/-- The normalized Euclidean `L²` square is the first, nonnegative term of
the quadratic continuous-K energy. -/
theorem unitCubeNormalizedEuclideanLpENorm_sq_le_continuousKEnergy
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) :
    ((unitCenteredCubeDomain d).normalizedEuclideanLpENorm
        (2 : ℝ≥0∞) F) ^ 2 ≤
      unitCubeNormalizedContinuousKEnergy s F := by
  rw [unitCubeNormalizedContinuousKEnergy_eq]
  exact self_le_add_right _ _

/-- The Hilbert `L²` sequence formed by the packaged gradients of the
zero-started rounded affine responses. -/
@[expose]
noncomputable def roundedUnitCubeDirichletContinuousKIterationGradientHilbertL2
    [NeZero d] (abar : Mat d) (hS : (symmPart abar).PosDef)
    (h : UnitCubeEuclideanL2Field d) (n : ℕ) :
    HilbertVectorL2 (openCubeSet (originCube d 0)) :=
  unitCubeEuclideanL2FieldHilbertL2
    (unitCubeGradientEuclideanL2Field
      (roundedUnitCubeDirichletContinuousKIteration abar hS h n))

/-- Consecutive Hilbert `L²` distance is exactly the real normalized
Euclidean `L²` size of the corresponding packaged gradient increment. -/
theorem dist_roundedUnitCubeDirichletContinuousKIterationGradientHilbertL2_succ
    [NeZero d] (abar : Mat d) (hS : (symmPart abar).PosDef)
    (h : UnitCubeEuclideanL2Field d) (n : ℕ) :
    dist
        (roundedUnitCubeDirichletContinuousKIterationGradientHilbertL2
          abar hS h n)
        (roundedUnitCubeDirichletContinuousKIterationGradientHilbertL2
          abar hS h (n + 1)) =
      ((unitCenteredCubeDomain d).normalizedEuclideanLpENorm
        (2 : ℝ≥0∞)
        (roundedUnitCubeDirichletContinuousKIterationIncrement
          abar hS h n)).toReal := by
  rw [dist_comm]
  unfold roundedUnitCubeDirichletContinuousKIterationGradientHilbertL2
  rw [dist_unitCubeEuclideanL2FieldHilbertL2]
  rw [← unitCubeGradientEuclideanL2Field_sub]
  rfl

end

end HighContrast
end HCPolySupport
