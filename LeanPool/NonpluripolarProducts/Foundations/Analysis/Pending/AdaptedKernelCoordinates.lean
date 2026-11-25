/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.ComplexManifold
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Coordinates adapted to finite-dimensional complex normed spaces

A finite-dimensional real normed space carrying a compatible complex vector
space structure is finite-dimensional over `ℂ`.  Consequently it admits a
continuous complex-linear equivalence with the standard complex model of its
complex dimension.  Pushing an additive Haar measure through this equivalence
gives an additive Haar measure in the coordinates, and the coordinate map is
measure-preserving for that pushed-forward measure.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace SGPT.Foundations.Analysis.Pending

open FirstPass

variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E]

/-- Finite-dimensionality over `ℝ` implies finite-dimensionality over `ℂ`
when the two scalar actions form the expected tower. -/
theorem finiteDimensional_complex_of_real : FiniteDimensional ℂ E :=
  Module.Finite.of_restrictScalars_finite ℝ ℂ E

/-- A compatible finite-dimensional complex normed space is continuously
complex-linearly equivalent to the standard complex model of the same complex
dimension. -/
noncomputable def adaptedComplexModelEquiv :
    E ≃L[ℂ] ComplexModel (Module.finrank ℂ E) := by
  letI : FiniteDimensional ℂ E := finiteDimensional_complex_of_real
  exact ContinuousLinearEquiv.ofFinrankEq (by
    rw [finrank_euclideanSpace_fin])

section Measure

variable [MeasurableSpace E] [BorelSpace E]

/-- The additive Haar measure in the adapted complex coordinates. -/
noncomputable def adaptedCoordinateMeasure (μ : Measure E) :
    Measure (ComplexModel (Module.finrank ℂ E)) :=
  μ.map adaptedComplexModelEquiv

/-- Pushing an additive Haar measure through the adapted complex-linear
equivalence again gives an additive Haar measure. -/
theorem adaptedCoordinateMeasure_isAddHaarMeasure
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    (adaptedCoordinateMeasure μ).IsAddHaarMeasure := by
  let _ : FiniteDimensional ℂ E := finiteDimensional_complex_of_real
  dsimp only [adaptedCoordinateMeasure]
  infer_instance

/-- The adapted coordinate equivalence preserves `μ` when its target is
equipped with the pushed-forward coordinate measure. -/
theorem adaptedComplexModelEquiv_measurePreserving (μ : Measure E) :
    MeasurePreserving adaptedComplexModelEquiv μ
      (adaptedCoordinateMeasure μ) := by
  exact adaptedComplexModelEquiv.continuous.measurable.measurePreserving μ

/-- The inverse adapted coordinate equivalence preserves the coordinate
measure back to the original measure. -/
theorem adaptedComplexModelEquiv_symm_measurePreserving (μ : Measure E) :
    MeasurePreserving adaptedComplexModelEquiv.symm
      (adaptedCoordinateMeasure μ) μ := by
  exact MeasurePreserving.symm
    adaptedComplexModelEquiv.toHomeomorph.toMeasurableEquiv
    (adaptedComplexModelEquiv_measurePreserving μ)

/-- Change of variables from the original space to its adapted complex
coordinates. -/
theorem integral_comp_adaptedComplexModelEquiv (μ : Measure E)
    (f : ComplexModel (Module.finrank ℂ E) → ℝ) :
    (∫ x, f (adaptedComplexModelEquiv x) ∂μ) =
      ∫ y, f y ∂adaptedCoordinateMeasure μ := by
  exact (adaptedComplexModelEquiv_measurePreserving μ).integral_comp'
    (f := adaptedComplexModelEquiv.toHomeomorph.toMeasurableEquiv) f

end Measure

end SGPT.Foundations.Analysis.Pending
