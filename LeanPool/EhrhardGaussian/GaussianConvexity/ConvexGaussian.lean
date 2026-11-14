/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.EhrhardType.GaussianImages
public import LeanPool.EhrhardGaussian.GaussianConvexity.FMPComparison
public import LeanPool.EhrhardGaussian.GaussianConvexity.Normal
import Mathlib.Analysis.Convex.Continuous

/-! # Normalized log-MGF convexity for finite convex Gaussian functionals

The Gaussian image has an Ehrhard-type law. Its positive moments are the given
moments, and its nonpositive moments follow from the proved one-dimensional
representation. Thus the finite-domain FMP comparison applies on all of ℝ,
including negative parameters and the continuous extension at zero.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace EhrhardGaussian.GaussianConvexity

/-- The finite-dimensional Gaussian convexity theorem, transported through the image law. -/
theorem convexOn_logMGFRatio_of_convex_gaussian {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsGaussian μ]
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (hF : ConvexOn ℝ univ F)
    (hexp : ∀ q : ℝ, 0 < q → Integrable (fun x => Real.exp (q * F x)) μ) :
    ConvexOn ℝ univ (logMGFRatio μ F) := by
  have hcont : Continuous F := continuousOn_univ.mp (hF.continuousOn isOpen_univ)
  have hν := EhrhardType.isEhrhardType_map_of_convex μ F hF
  have hpos (q : ℝ) (hq : 0 < q) :
      Integrable (fun x : ℝ => Real.exp (q * x)) (μ.map F) := by
    apply (integrable_map_measure (by fun_prop) hcont.measurable.aemeasurable).mpr
    exact hexp q hq
  have hD : integrableExpSet id (μ.map F) = univ := by
    ext q
    simp only [mem_univ, iff_true]
    by_cases hq : 0 < q
    · exact hpos q hq
    · exact EhrhardType.integrable_exp_mul_of_isEhrhardType hν (le_of_not_gt hq)
  have hconv := convexOn_logMGFRatio_of_isEhrhardType_of_positive_moment hν zero_lt_one
    (hpos 1 zero_lt_one)
  rw [hD] at hconv
  have heq : logMGFRatio (μ.map F) id = logMGFRatio μ F :=
    funext (logMGFRatio_map μ F hcont.measurable)
  rwa [heq] at hconv

end EhrhardGaussian.GaussianConvexity

end
