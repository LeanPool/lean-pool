/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.PositiveDistributionMeasure

/-!
# Measures representing positive linear functionals on test functions

A linear functional on smooth test functions of an open set which is
nonnegative on nonnegative tests is integration against a regular locally
finite measure on the open set. No continuity is assumed: positivity and the
order-cofinality of smooth tests among compactly supported continuous functions
suffice for the M. Riesz extension, and Riesz–Markov–Kakutani gives the measure.
-/

@[expose] public section

noncomputable section

open Set Function MeasureTheory TopologicalSpace
open scoped Distributions CompactlySupported

namespace SGPT.Foundations.Analysis.Pending

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {Ω : Opens E}

theorem exists_positiveLinearMap_of_testFunctional (T : 𝓓(Ω, ℝ) →ₗ[ℝ] ℝ)
    (hT : ∀ φ : 𝓓(Ω, ℝ), (∀ x, 0 ≤ φ x) → 0 ≤ T φ) :
    ∃ Λ : C_c(Ω, ℝ) →ₚ[ℝ] ℝ,
      ∀ φ : 𝓓(Ω, ℝ), Λ (testFunctionToCompactlySupportedLM Ω φ) = T φ :=
  exists_positiveLinearMap_of_nonneg_testFunctional T hT

variable [MeasurableSpace E] [BorelSpace E]

/-- A positive linear functional on test functions is integration against a
regular locally finite measure on the open set. -/
theorem exists_regular_measure_of_testFunctional (T : 𝓓(Ω, ℝ) →ₗ[ℝ] ℝ)
    (hT : ∀ φ : 𝓓(Ω, ℝ), (∀ x, 0 ≤ φ x) → 0 ≤ T φ) :
    ∃ ν : Measure Ω, ν.Regular ∧ IsLocallyFiniteMeasure ν ∧
      ∀ φ : 𝓓(Ω, ℝ), (∫ x : Ω, φ x ∂ν) = T φ :=
  exists_regular_measure_of_nonneg_testFunctional T hT

end SGPT.Foundations.Analysis.Pending
