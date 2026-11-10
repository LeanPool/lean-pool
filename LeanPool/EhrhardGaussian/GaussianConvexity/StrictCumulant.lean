/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.GaussianConvexity.CumulantConvexity
public import LeanPool.EhrhardGaussian.GaussianConvexity.Normal
import Mathlib.Analysis.Convex.Slope
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Strict ordinary moment monotonicity

For a nonconstant law the ordinary cumulant is strictly convex. Secant slopes
through zero give a strictly positive variance for FMP's matching Gaussian.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace EhrhardGaussian.GaussianConvexity

/-- Equality in the normalized exponential Jensen inequality forces a constant random variable. -/
theorem strictConvexOn_cgf_integrableExpSet {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hn : ¬ ∃ c : ℝ, X =ᵐ[μ] fun _ => c) :
    StrictConvexOn ℝ (integrableExpSet X μ) (cgf X μ) := by
  refine ⟨convex_integrableExpSet, ?_⟩
  intro p hp q hq hpq a b ha hb hab
  change cgf X μ (a * p + b * q) < a * cgf X μ p + b * cgf X μ q
  have hle := (convexOn_cgf_integrableExpSet μ X).2 hp hq ha.le hb.le hab
  apply lt_of_le_of_ne hle
  intro heq
  let U := a * cgf X μ p + b * cgf X μ q
  change cgf X μ (a * p + b * q) = U at heq
  have hr : Integrable (fun x => Real.exp ((a * p + b * q) * X x)) μ :=
    convex_integrableExpSet hp hq ha.le hb.le hab
  have hi_p : Integrable (fun x => Real.exp (p * X x - cgf X μ p)) μ := by
    simp_rw [Real.exp_sub]
    exact hp.div_const _
  have hi_q : Integrable (fun x => Real.exp (q * X x - cgf X μ q)) μ := by
    simp_rw [Real.exp_sub]
    exact hq.div_const _
  have hi_r : Integrable (fun x => Real.exp ((a * p + b * q) * X x - U)) μ := by
    simp_rw [Real.exp_sub]
    exact hr.div_const _
  have hlin : ∀ x, a * (p * X x - cgf X μ p) + b * (q * X x - cgf X μ q) =
      (a * p + b * q) * X x - U := by intro x; dsimp [U]; ring
  have hpt : ∀ x, Real.exp ((a * p + b * q) * X x - U) ≤
      a * Real.exp (p * X x - cgf X μ p) + b * Real.exp (q * X x - cgf X μ q) := by
    intro x
    simpa only [smul_eq_mul, hlin] using
      convexOn_exp.2 (mem_univ (p * X x - cgf X μ p))
        (mem_univ (q * X x - cgf X μ q)) ha.le hb.le hab
  have hint : (∫ x, Real.exp ((a * p + b * q) * X x - U) ∂μ) =
      ∫ x, (a * Real.exp (p * X x - cgf X μ p) + b * Real.exp (q * X x - cgf X μ q)) ∂μ := by
    rw [← heq, integral_exp_sub_cgf μ X hr,
      integral_add (hi_p.const_mul a) (hi_q.const_mul b), integral_const_mul, integral_const_mul,
      integral_exp_sub_cgf μ X hp, integral_exp_sub_cgf μ X hq, mul_one, mul_one, hab]
  have hequal := (integral_eq_iff_of_ae_le hi_r
    ((hi_p.const_mul a).add (hi_q.const_mul b)) (ae_of_all _ hpt)).mp hint
  apply hn
  refine ⟨(cgf X μ p - cgf X μ q) / (p - q), ?_⟩
  filter_upwards [hequal] with x hx
  have hargs : p * X x - cgf X μ p = q * X x - cgf X μ q := by
    by_contra hneq
    have hs := strictConvexOn_exp.2 (mem_univ (p * X x - cgf X μ p))
      (mem_univ (q * X x - cgf X μ q)) hneq ha hb hab
    simp only [smul_eq_mul, hlin] at hs
    exact hs.ne hx
  apply (eq_div_iff (sub_ne_zero.mpr hpq)).mpr
  nlinarith only [hargs]

/-- A probability law is nonconstant exactly when its identity variable is not a.e. constant. -/
theorem not_ae_constant_id_of_not_dirac (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hn : ¬ ∃ c, μ = Measure.dirac c) : ¬ ∃ c : ℝ, id =ᵐ[μ] fun _ => c := by
  rintro ⟨c, hc⟩
  apply hn
  refine ⟨c, ?_⟩
  have hm : μ.map (id : ℝ → ℝ) = μ.map (fun _ : ℝ => c) := Measure.map_congr hc
  rw [Measure.map_id, Measure.map_const, measure_univ, one_smul] at hm
  exact hm

/-- Distinct nonzero moment orders have strictly increasing normalized log moments for nonconstant
laws. -/
theorem logMGFRatio_lt_of_nonconstant {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hn : ¬ ∃ c, μ = Measure.dirac c) {p q : ℝ} (hpq : p < q)
    (hp : Integrable (fun x => Real.exp (p * x)) μ)
    (hq : Integrable (fun x => Real.exp (q * x)) μ) (hp0 : p ≠ 0) (hq0 : q ≠ 0) :
    logMGFRatio μ id p < logMGFRatio μ id q := by
  have hc := strictConvexOn_cgf_integrableExpSet μ id (not_ae_constant_id_of_not_dirac μ hn)
  have h0 : (0 : ℝ) ∈ integrableExpSet id μ := by
    change Integrable (fun x : ℝ => Real.exp (0 * x)) μ
    simp only [zero_mul, Real.exp_zero]
    exact integrable_const _
  have hs := hc.secant_strict_mono h0 hp hq hp0 hq0 hpq
  simp only [cgf_zero, sub_zero] at hs
  simp only [logMGFRatio, hp0, hq0, ite_false]
  simpa only [div_eq_inv_mul, cgf, mgf] using hs

end EhrhardGaussian.GaussianConvexity
