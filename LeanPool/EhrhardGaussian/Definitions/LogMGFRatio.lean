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

/-! # Normalized logarithmic moment-generating functions -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise

namespace EhrhardGaussian

/-- `Φ_F(q) = q⁻¹ log E e^{qF}` for `q ≠ 0` and `E F` for `q = 0` (§3.1). -/
def logMGFRatio {E : Type*} [MeasurableSpace E] (μ : Measure E) (F : E → ℝ) (q : ℝ) : ℝ :=
  if q = 0 then ∫ x, F x ∂μ else q⁻¹ * Real.log (∫ x, Real.exp (q * F x) ∂μ)

end EhrhardGaussian

end

end
