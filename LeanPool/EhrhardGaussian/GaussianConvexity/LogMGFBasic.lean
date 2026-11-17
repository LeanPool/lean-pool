/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.GaussianConvexity.Normal
import Mathlib.Tactic.Ring

/-! The normalized log moment-generating function admits evaluation and normalization identities. -/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace EhrhardGaussian.GaussianConvexity

/-- The order-zero ratio of a real law is its expectation. -/
theorem logMGFRatio_id_zero (μ : Measure ℝ) :
    logMGFRatio μ id 0 = ∫ x, x ∂μ := by
  simp only [logMGFRatio, ite_true]
  rfl

/-- Multiplication by the order recovers the log moment, including at order zero. -/
theorem mul_logMGFRatio {E : Type*} [MeasurableSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] (F : E → ℝ) (q : ℝ) :
    q * logMGFRatio μ F q = Real.log (mgf F μ q) := by
  by_cases hq : q = 0
  · subst q
    rw [zero_mul, mgf_zero, Real.log_one]
  · simp only [logMGFRatio, hq, ite_false]
    rw [← mul_assoc, mul_inv_cancel₀ hq, one_mul]
    rfl

/-- Normalization `E exp X = 1` makes the ratio vanish at order one. -/
theorem logMGFRatio_id_one_of_normalized (μ : Measure ℝ)
    (hμ : ∫ x, Real.exp x ∂μ = 1) : logMGFRatio μ id 1 = 0 := by
  simp only [logMGFRatio, one_ne_zero, ite_false, inv_one, one_mul]
  change Real.log (∫ x : ℝ, Real.exp x ∂μ) = 0
  rw [hμ, Real.log_one]

/-- At order two the formula is half the log of the second exponential moment. -/
theorem logMGFRatio_id_two (μ : Measure ℝ) :
    logMGFRatio μ id 2 = Real.log (mgf id μ 2) / 2 := by
  simp only [logMGFRatio, OfNat.ofNat_ne_zero, ite_false]
  rw [div_eq_inv_mul]
  rfl

end EhrhardGaussian.GaussianConvexity
