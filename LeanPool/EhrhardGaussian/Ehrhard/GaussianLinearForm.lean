/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.FunctionalHessian
public import LeanPool.EhrhardGaussian.Gaussian.GaussianLaw
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Moments.Variance

/-! # The exact Gaussian law of a linear form of independent coordinates -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open EhrhardGaussian.Gaussian (standardGaussianMeasure)
open scoped BigOperators

namespace EhrhardGaussian.Ehrhard

/-- A linear combination of standard Gaussian coordinates has mean zero. -/
theorem integral_coordinateForm {n : ℕ} (c : Fin n → ℝ) :
    ∫ z, coordinateForm c z ∂standardGaussianMeasure n = 0 := by
  simp only [coordinateForm_apply]
  rw [integral_finsetSum]
  · simp [integral_const_mul, standardGaussianMeasure, integral_eval, integral_id_gaussianReal]
  · intro i _
    exact (integrable_eval (μ := fun _ : Fin n => gaussianReal 0 1)
      ((memLp_id_gaussianReal 1).integrable (by norm_num))).const_mul (c i)

/-- The variance of a standard Gaussian linear form is the sum of its squared coefficients. -/
theorem variance_coordinateForm {n : ℕ} (c : Fin n → ℝ) :
    Var[coordinateForm c; standardGaussianMeasure n] = ∑ i, c i ^ 2 := by
  have heq : (coordinateForm c : (Fin n → ℝ) → ℝ) = ∑ i, fun z => c i * z i := by
    funext z
    simp only [Finset.sum_apply]
    exact coordinateForm_apply c z
  rw [heq, standardGaussianMeasure, variance_sum_pi]
  · change (∑ i, Var[fun x : ℝ => c i * id x; gaussianReal 0 1]) = _
    simp_rw [variance_const_mul, variance_id_gaussianReal]
    simp only [NNReal.coe_one, mul_one]
  · exact fun i => (memLp_id_gaussianReal 2).const_mul (c i)

/-- A standard Gaussian linear form has the centered Gaussian law with its coefficient variance. -/
theorem hasLaw_coordinateForm {n : ℕ} (c : Fin n → ℝ) :
    HasLaw (coordinateForm c) (gaussianReal 0 (∑ i, c i ^ 2).toNNReal) (standardGaussianMeasure n)
      where
  aemeasurable := (coordinateForm c).continuous.measurable.aemeasurable
  map_eq := by
    have := EhrhardGaussian.Gaussian.isGaussian_standardGaussianMeasure n
    rw [IsGaussian.map_eq_gaussianReal, integral_coordinateForm, variance_coordinateForm]

end EhrhardGaussian.Ehrhard

end
