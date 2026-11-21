/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.Cutfast.Defs
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Standard Gaussian density and its radial profile

The density description serves both the Gaussian scale mixture and the pushforward to a sphere.
-/

@[expose] public section

open MeasureTheory Filter Topology Metric Real
open scoped ENNReal InnerProductSpace

namespace Cutfast

namespace Sphere

/-- The radial profile of the standard Gaussian density on `ℝᵈ`. -/
noncomputable def gaussProfile (d : ℕ) (r : ℝ) : ℝ := (√(2 * π))⁻¹ ^ d * rexp (-r ^ 2 / 2)

end Sphere

namespace Student

variable {d : ℕ}

/-- The standard Gaussian density `(2π)^{-d/2} e^{-|y|²/2}`. -/
noncomputable def gaussDensity (d : ℕ) (y : E d) : ℝ := Sphere.gaussProfile d ‖y‖

lemma gaussDensity_eq_formula (y : E d) :
    gaussDensity d y = ((2 * π) ^ ((d : ℝ) / 2))⁻¹ * exp (-(1 / 2) * ‖y‖ ^ 2) := by
  unfold gaussDensity Sphere.gaussProfile
  rw [inv_pow, sqrt_eq_rpow, ← rpow_mul_natCast (by positivity)]
  rw [show (1 / 2 : ℝ) * d = (d : ℝ) / 2 by ring,
    show -‖y‖ ^ 2 / 2 = -(1 / 2) * ‖y‖ ^ 2 by ring]

lemma gaussDensity_pos (y : E d) : 0 < gaussDensity d y := by
  rw [gaussDensity_eq_formula]
  positivity

lemma continuous_gaussDensity : Continuous (gaussDensity d) := by
  unfold gaussDensity Sphere.gaussProfile
  fun_prop

lemma integral_exp_half :
    ∫ y : E d, exp (-(1 / 2) * ‖y‖ ^ 2) = (2 * π) ^ ((d : ℝ) / 2) := by
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm (by norm_num : (0 : ℝ) < 1 / 2),
    finrank_euclideanSpace_fin]
  congr 1; field_simp

lemma integrable_exp_half : Integrable (fun y : E d => exp (-(1 / 2) * ‖y‖ ^ 2)) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_exp_half]; positivity

lemma integrable_gaussDensity : Integrable (gaussDensity d) := by
  change Integrable (fun y : E d => gaussDensity d y)
  simp only [gaussDensity_eq_formula]
  exact integrable_exp_half.const_mul _

lemma integral_gaussDensity : ∫ y, gaussDensity d y = 1 := by
  simp only [gaussDensity_eq_formula]
  rw [integral_const_mul, integral_exp_half, inv_mul_cancel₀ (by positivity)]

/-- The standard Gaussian measure has density `(2π)^{-d/2} e^{-|y|²/2}`. -/
lemma stdGaussian_eq_withDensity :
    ProbabilityTheory.stdGaussian (E d) =
      volume.withDensity (fun y => ENNReal.ofReal (gaussDensity d y)) := by
  have hfin : IsFiniteMeasure (volume.withDensity (fun y : E d => ENNReal.ofReal (gaussDensity d
    y))) :=
    isFiniteMeasure_withDensity_ofReal integrable_gaussDensity.2
  refine Measure.ext_of_charFun ?_
  ext t
  rw [ProbabilityTheory.charFun_stdGaussian, charFun_apply,
    integral_withDensity_eq_integral_toReal_smul
      (by exact ENNReal.measurable_ofReal.comp continuous_gaussDensity.measurable)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have e : ∀ x : E d, (ENNReal.ofReal (gaussDensity d x)).toReal • Complex.exp (⟪x,
    t⟫_ℝ * Complex.I) =
      (((2 * π) ^ ((d : ℝ) / 2))⁻¹ : ℝ) *
        Complex.exp (-(1 / 2 : ℂ) * ‖x‖ ^ 2 + Complex.I * ⟪t, x⟫_ℝ) := by
    intro x
    rw [ENNReal.toReal_ofReal (gaussDensity_pos x).le, Complex.real_smul, gaussDensity_eq_formula,
      Complex.ofReal_mul, mul_assoc, Complex.ofReal_exp, ← Complex.exp_add, real_inner_comm]
    push_cast
    ring_nf
  simp_rw [e]
  rw [integral_const_mul, GaussianFourier.integral_cexp_neg_mul_sq_norm_add (by norm_num),
    finrank_euclideanSpace_fin]
  have h2 : ((π : ℂ) / (1 / 2)) ^ ((d : ℂ) / 2) = (((2 * π) ^ ((d : ℝ) / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (by positivity)]
    push_cast
    congr 1; field_simp
  rw [h2, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ (by positivity)]
  simp only [Complex.ofReal_one, one_mul, Complex.I_sq]
  congr 1
  ring

end Student

end Cutfast
