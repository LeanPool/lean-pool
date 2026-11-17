/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Probability.Moments.CovarianceBilin
public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Centered covariance operator

The Riesz operator of Mathlib's centered covariance bilinear form provides the covariance
normalization used by KLS. This foundational definition is shared with the linear-test results,
which are kept out of the statement's import closure.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace FunctionalInequalities.Covariance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]

/-- The centered covariance operator, obtained by Riesz representation of
`ProbabilityTheory.covarianceBilin μ` using `InnerProductSpace.continuousLinearMapOfBilin`.

For a probability measure with `MemLp id 2 μ`, write `m = ∫ x, x ∂μ`. Then
`⟪operator μ u, v⟫ = ∫ x, ⟪u, x - m⟫ * ⟪v, x - m⟫ ∂μ`.
The definition accepts every measure; if `¬ MemLp id 2 μ`, it inherits Mathlib's zero value.

In the pinned Mathlib version, `ProbabilityTheory.covarianceOperator μ` uses the uncentered
second moment. This definition is definitionally equal to
`ProbabilityTheory.covarianceOperator (μ.map (fun x => x - ∫ y, y ∂μ))`. -/
def operator (μ : Measure E) : E →L[ℝ] E :=
  InnerProductSpace.continuousLinearMapOfBilin (covarianceBilin μ)

/-- The defining Riesz identity, from `InnerProductSpace.continuousLinearMapOfBilin_apply`.
For a finite measure with `MemLp id 2 μ`, combine it with
`ProbabilityTheory.covarianceBilin_apply` to obtain the centered integral formula. -/
@[simp]
theorem operator_inner (μ : Measure E) (x y : E) :
    inner ℝ (operator μ x) y = covarianceBilin μ x y := by
  exact InnerProductSpace.continuousLinearMapOfBilin_apply (covarianceBilin μ) x y

end FunctionalInequalities.Covariance
