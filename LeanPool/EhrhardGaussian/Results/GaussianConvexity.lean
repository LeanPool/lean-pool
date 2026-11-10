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
public import LeanPool.EhrhardGaussian.Definitions.LogMGFRatio
public import LeanPool.EhrhardGaussian.Provider.GaussianConvexity

/-! # Convexity of normalized Gaussian log moments -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise

namespace EhrhardGaussian

/-- **Gaussian convexity** (KPZ Theorem 3.1 `thm:Chen`, §3.1): for a convex function `F` of a
finite-dimensional Gaussian vector with `E e^{λF} < ∞` for all `λ > 0`, `q ↦ Φ_F(q)` is convex. -/
theorem gaussian_convexity {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsGaussian μ]
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (hF : ConvexOn ℝ Set.univ F)
    (hexp : ∀ q : ℝ, 0 < q → Integrable (fun x => Real.exp (q * F x)) μ) :
    ConvexOn ℝ Set.univ (logMGFRatio μ F) :=
  by exact EhrhardGaussian.Provider.gaussian_convexity μ F hF hexp
end EhrhardGaussian

end

end
