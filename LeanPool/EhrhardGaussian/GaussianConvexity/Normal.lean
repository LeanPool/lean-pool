/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real

public import LeanPool.EhrhardGaussian.Definitions.LogMGFRatio
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Normalized log MGFs and Gaussian laws

The exact Gaussian formula includes zero variance and parameter zero. The law
transport lemma fixes the normalization shared by Gaussian convexity, the Ehrhard-type
characterization, and the FMP25 comparison.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace EhrhardGaussian.GaussianConvexity

/-- The normalized log MGF depends only on the pushed-forward law, including at zero. -/
theorem logMGFRatio_map {E : Type*} [MeasurableSpace E] (μ : Measure E)
    (F : E → ℝ) (hF : Measurable F) (q : ℝ) :
    logMGFRatio (μ.map F) id q = logMGFRatio μ F q := by
  by_cases hq : q = 0
  · simp only [logMGFRatio, hq, ite_true]
    exact integral_map hF.aemeasurable (by fun_prop)
  · simp only [logMGFRatio, hq, ite_false]
    rw [integral_map hF.aemeasurable (by fun_prop)]
    rfl

/-- The normalized log MGF of a Gaussian law is affine in its parameter. -/
theorem logMGFRatio_gaussianReal (m : ℝ) (v : NNReal) (q : ℝ) :
    logMGFRatio (gaussianReal m v) id q = m + (v : ℝ) * q / 2 := by
  by_cases hq : q = 0
  · simp only [logMGFRatio, hq, ite_true, mul_zero, zero_div, add_zero]
    change (∫ x : ℝ, x ∂gaussianReal m v) = m
    exact integral_id_gaussianReal
  · simp only [logMGFRatio, hq, ite_false]
    change q⁻¹ * Real.log (mgf id (gaussianReal m v) q) = _
    rw [mgf_id_gaussianReal, Real.log_exp]
    field_simp

/-- Gaussian laws, including constants, satisfy the convexity conclusion. -/
theorem convexOn_logMGFRatio_gaussianReal (m : ℝ) (v : NNReal) :
    ConvexOn ℝ univ (logMGFRatio (gaussianReal m v) id) := by
  have hfun : logMGFRatio (gaussianReal m v) id = fun q => m + (v : ℝ) * q / 2 :=
    funext (logMGFRatio_gaussianReal m v)
  rw [hfun]
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b _ _ hab
  change m + (v : ℝ) * (a * x + b * y) / 2 ≤
    a * (m + (v : ℝ) * x / 2) + b * (m + (v : ℝ) * y / 2)
  apply le_of_eq
  calc
    _ = (a + b) * m + (v : ℝ) * (a * x + b * y) / 2 := by rw [hab, one_mul]
    _ = _ := by ring

end EhrhardGaussian.GaussianConvexity
