/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.GaussianConvexity.ConvexGaussian
public import LeanPool.EhrhardGaussian.GaussianConvexity.Normal
public import LeanPool.EhrhardGaussian.GaussianConvexity.Derivative
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import LeanPool.EhrhardGaussian.GaussianConvexity.ExponentialInterpolation
public import LeanPool.EhrhardGaussian.GaussianConvexity.FMPComparison

/-! # Gaussian convexity

Theorem 3.1 of the paper follows from Ehrhard’s inequality and the one-dimensional moment comparison
for monotone convex Gaussian functions.
-/

public section

open MeasureTheory ProbabilityTheory

namespace EhrhardGaussian.Provider

/-- For a finite convex Gaussian functional with finite positive exponential moments, the
logarithmic moment-generating function divided by its parameter, continuously extended at zero, is
convex on ℝ (Theorem 3.1 of the paper). -/
theorem gaussian_convexity {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsGaussian μ]
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (hF : ConvexOn ℝ Set.univ F)
    (hexp : ∀ q : ℝ, 0 < q → Integrable (fun x => Real.exp (q * F x)) μ) :
    ConvexOn ℝ Set.univ (logMGFRatio μ F) :=
  GaussianConvexity.convexOn_logMGFRatio_of_convex_gaussian μ F hF hexp

end EhrhardGaussian.Provider
