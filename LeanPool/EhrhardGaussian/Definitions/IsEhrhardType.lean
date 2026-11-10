/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Algebra.Order.Round
public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.CDF
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # Ehrhard-type real probability laws -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise

namespace EhrhardGaussian

/-- Ehrhard type (§3.3): `X` is constant, or `P(X < a) < 1` for all `a` and
`a ↦ Φ⁻¹(P(X < a))` is concave (with `Φ⁻¹(0) = −∞`), `Φ` the standard Gaussian distribution
function. Stated for the law `μ` of `X`: on `{a : μ(−∞, a) > 0}` (where `Φ⁻¹(μ(−∞,a))` is finite)
`μ(−∞, a) = Φ(g a)` for a concave `g`. -/
def IsEhrhardType (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧
  ((∃ c, μ = Measure.dirac c) ∨
  ((∀ a, μ (Set.Iio a) < 1) ∧
    ∃ g : ℝ → ℝ, ConcaveOn ℝ {a | 0 < μ (Set.Iio a)} g ∧
      ∀ a, 0 < μ (Set.Iio a) → (μ (Set.Iio a)).toReal = cdf (gaussianReal 0 1) (g a)))

end EhrhardGaussian

end

end
