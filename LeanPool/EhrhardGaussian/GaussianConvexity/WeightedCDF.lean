/-
Copyright (c) 2026 Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ahmed Bou-Rabee, Scott Armstrong
-/

/-
Modified for EhrhardGaussian, 2026.

The indicator-difference and product-Fubini proof pattern is adapted from
Lattice-Probability, LatticeProb/Prob/CdfDifferenceFourier.lean.
The real exponential weight and its integrability proof are new here.
-/
module

public import Mathlib.Probability.CDF
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Signed exponentially weighted CDF differences

FMP25 §3 needs the difference-of-tails formula for both signs of the exponential
parameter. A product coupling and compact interval indicators prove it without
integrating the individual weighted tails, which need not be integrable.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter

namespace EhrhardGaussian.GaussianConvexity

/-- Difference of the two closed half-line indicators, as a real-valued function. -/
noncomputable def cdfIndDiff (x y u : ℝ) : ℝ :=
  (Iic u).indicator (fun _ => (1 : ℝ)) x - (Iic u).indicator (fun _ => (1 : ℝ)) y

/-- Ordered indicators differ exactly on the interval between the two points. -/
theorem cdfIndDiff_of_le {x y : ℝ} (h : x ≤ y) (u : ℝ) :
    cdfIndDiff x y u = (Ico x y).indicator (fun _ => (1 : ℝ)) u := by
  unfold cdfIndDiff
  by_cases h1 : x ≤ u <;> by_cases h2 : y ≤ u <;>
    simp only [mem_Iic, mem_Ico, h1, h2, indicator_of_mem, indicator_of_notMem,
      sub_self, sub_zero, zero_sub, true_and, false_and, not_lt, not_false_eq_true,
      indicator_apply, left_eq_ite_iff, one_ne_zero, imp_self, neg_eq_zero]
  all_goals (exfalso; linarith only [h, h1, h2])

/-- Reversing the points negates their indicator difference. -/
theorem cdfIndDiff_swap (x y u : ℝ) : cdfIndDiff y x u = -cdfIndDiff x y u := by
  unfold cdfIndDiff
  ring

/-- Joint measurability of the indicator difference. -/
theorem measurable_cdfIndDiff :
    Measurable (fun q : ℝ × (ℝ × ℝ) => cdfIndDiff q.2.1 q.2.2 q.1) := by
  simp only [cdfIndDiff, indicator_apply, mem_Iic]
  exact (Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) measurable_const
    measurable_const).sub
    (Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) measurable_const
      measurable_const)

/-- The real exponential interval primitive is valid for either sign of a nonzero parameter. -/
theorem integral_Ico_exp_mul {x y p : ℝ} (hxy : x ≤ y) (hp : p ≠ 0) :
    ∫ t in Ico x y, Real.exp (p * t) = (Real.exp (p * y) - Real.exp (p * x)) / p := by
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hxy]
  have hD : ∀ t : ℝ, HasDerivAt (fun u => Real.exp (p * u) / p) (Real.exp (p * t)) t := by
    intro t
    have h := (((hasDerivAt_id' t).const_mul p).exp.div_const p)
    simpa only [mul_one, mul_div_cancel_right₀ _ hp] using h
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hD t)]
  · ring
  · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _

/-- The weighted indicator difference is supported in a bounded interval and is integrable. -/
theorem integrable_cdfIndDiff_exp (x y p : ℝ) :
    Integrable (fun t => cdfIndDiff x y t * Real.exp (p * t)) := by
  rcases le_total x y with hxy | hyx
  · have heq : (fun t => cdfIndDiff x y t * Real.exp (p * t)) =
        (Ico x y).indicator (fun t => Real.exp (p * t)) := by
      funext t
      rw [cdfIndDiff_of_le hxy]
      by_cases ht : t ∈ Ico x y <;> simp only [indicator_apply, ht, ite_true, ite_false, one_mul,
        zero_mul]
    rw [heq]
    apply (integrable_indicator_iff measurableSet_Ico).mpr
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).integrableOn_Icc.mono_set
      Ico_subset_Icc_self
  · have heq : (fun t => cdfIndDiff x y t * Real.exp (p * t)) =
        fun t => -(cdfIndDiff y x t * Real.exp (p * t)) := by
      funext t
      rw [cdfIndDiff_swap, neg_mul]
    rw [heq]
    have heq' : (fun t => cdfIndDiff y x t * Real.exp (p * t)) =
        (Ico y x).indicator (fun t => Real.exp (p * t)) := by
      funext t
      rw [cdfIndDiff_of_le hyx]
      by_cases ht : t ∈ Ico y x <;> simp only [indicator_apply, ht, ite_true, ite_false, one_mul,
        zero_mul]
    have hi : Integrable (fun t => cdfIndDiff y x t * Real.exp (p * t)) := by
      rw [heq']
      exact (integrable_indicator_iff measurableSet_Ico).mpr
        ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).integrableOn_Icc.mono_set
          Ico_subset_Icc_self)
    exact hi.neg

/-- Exact integral of the weighted indicator difference, for positive or negative parameters. -/
theorem integral_cdfIndDiff_exp (x y : ℝ) {p : ℝ} (hp : p ≠ 0) :
    ∫ t, cdfIndDiff x y t * Real.exp (p * t) =
      (Real.exp (p * y) - Real.exp (p * x)) / p := by
  rcases le_total x y with hxy | hyx
  · have heq : (fun t => cdfIndDiff x y t * Real.exp (p * t)) =
        (Ico x y).indicator (fun t => Real.exp (p * t)) := by
      funext t
      rw [cdfIndDiff_of_le hxy]
      by_cases ht : t ∈ Ico x y <;> simp only [indicator_apply, ht, ite_true, ite_false, one_mul,
        zero_mul]
    rw [heq, integral_indicator measurableSet_Ico]
    exact integral_Ico_exp_mul hxy hp
  · have heq : (fun t => cdfIndDiff x y t * Real.exp (p * t)) =
        fun t => -((Ico y x).indicator (fun t => Real.exp (p * t)) t) := by
      funext t
      rw [cdfIndDiff_swap, neg_mul, cdfIndDiff_of_le hyx]
      by_cases ht : t ∈ Ico y x <;> simp only [indicator_apply, ht, ite_true, ite_false, one_mul,
        zero_mul, neg_zero]
    rw [heq, integral_neg, integral_indicator measurableSet_Ico, integral_Ico_exp_mul hyx hp]
    ring

/-- Constant sign of the indicator difference gives its weighted absolute integral exactly. -/
theorem integral_norm_cdfIndDiff_exp (x y : ℝ) {p : ℝ} (hp : p ≠ 0) :
    ∫ t, ‖cdfIndDiff x y t * Real.exp (p * t)‖ =
      |(Real.exp (p * y) - Real.exp (p * x)) / p| := by
  have hordered : ∀ {a b : ℝ}, a ≤ b →
      (∫ t, ‖cdfIndDiff a b t * Real.exp (p * t)‖) =
        |(Real.exp (p * b) - Real.exp (p * a)) / p| := by
    intro a b hab
    have hnonneg : ∀ t, 0 ≤ cdfIndDiff a b t * Real.exp (p * t) := by
      intro t
      rw [cdfIndDiff_of_le hab]
      exact mul_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _) (Real.exp_pos _).le
    simp_rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg _)]
    rw [← integral_cdfIndDiff_exp a b hp, abs_of_nonneg (integral_nonneg hnonneg)]
  rcases le_total x y with hxy | hyx
  · exact hordered hxy
  · simp_rw [cdfIndDiff_swap y x, neg_mul, norm_neg]
    rw [hordered hyx]
    rw [abs_div, abs_div, abs_sub_comm]

end EhrhardGaussian.GaussianConvexity
