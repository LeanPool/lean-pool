/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Convexity of the ordinary cumulant on its finite moment domain

Normalized exponential functions and the scalar convexity of `exp` give the
log-convexity of a finite MGF. In particular, secant slopes through zero are
monotone. This is the ordinary moment monotonicity needed to construct the
matching Gaussian; it is not the stronger FMP normalized-log-MGF convexity.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace EhrhardGaussian.GaussianConvexity

/-- An exponential tilted by its cumulant has integral one. -/
theorem integral_exp_sub_cgf {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) {p : ℝ}
    (hp : Integrable (fun x => Real.exp (p * X x)) μ) :
    ∫ x, Real.exp (p * X x - cgf X μ p) ∂μ = 1 := by
  simp_rw [Real.exp_sub]
  rw [integral_div, exp_cgf hp]
  exact div_self (mgf_pos hp).ne'

/-- The ordinary cumulant is convex wherever its exponential moments are finite. -/
theorem convexOn_cgf_integrableExpSet {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) :
    ConvexOn ℝ (integrableExpSet X μ) (cgf X μ) := by
  refine ⟨convex_integrableExpSet, ?_⟩
  intro p hp q hq a b ha hb hab
  change cgf X μ (a * p + b * q) ≤ a * cgf X μ p + b * cgf X μ q
  have hr : Integrable (fun x => Real.exp ((a * p + b * q) * X x)) μ :=
    convex_integrableExpSet hp hq ha hb hab
  let U := a * cgf X μ p + b * cgf X μ q
  have hi_p : Integrable (fun x => Real.exp (p * X x - cgf X μ p)) μ := by
    simp_rw [Real.exp_sub]
    exact hp.div_const _
  have hi_q : Integrable (fun x => Real.exp (q * X x - cgf X μ q)) μ := by
    simp_rw [Real.exp_sub]
    exact hq.div_const _
  have hi_r : Integrable (fun x => Real.exp ((a * p + b * q) * X x - U)) μ := by
    simp_rw [Real.exp_sub]
    exact hr.div_const _
  have hpt : ∀ x, Real.exp ((a * p + b * q) * X x - U) ≤
      a * Real.exp (p * X x - cgf X μ p) + b * Real.exp (q * X x - cgf X μ q) := by
    intro x
    have h := convexOn_exp.2 (mem_univ (p * X x - cgf X μ p))
      (mem_univ (q * X x - cgf X μ q)) ha hb hab
    have heq : a * (p * X x - cgf X μ p) + b * (q * X x - cgf X μ q) =
        (a * p + b * q) * X x - U := by dsimp [U]; ring
    simpa only [smul_eq_mul, heq] using h
  have hint := integral_mono hi_r ((hi_p.const_mul a).add (hi_q.const_mul b)) hpt
  rw [integral_add' (hi_p.const_mul a) (hi_q.const_mul b), integral_const_mul,
    integral_const_mul, integral_exp_sub_cgf μ X hp, integral_exp_sub_cgf μ X hq,
    mul_one, mul_one, hab] at hint
  have hratio : mgf X μ (a * p + b * q) / Real.exp U ≤ 1 := by
    simpa only [Real.exp_sub, integral_div, mgf] using hint
  have hM := (div_le_one (Real.exp_pos U)).mp hratio
  have hlog := Real.log_le_log (mgf_pos hr) hM
  rw [Real.log_exp] at hlog
  exact hlog

end EhrhardGaussian.GaussianConvexity
