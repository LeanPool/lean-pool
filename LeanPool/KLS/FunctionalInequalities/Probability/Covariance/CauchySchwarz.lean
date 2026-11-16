/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.Moments.Variance

/-!
# Covariance Cauchy–Schwarz

`cov[X, Y]² ≤ Var X · Var Y` for two square-integrable real statistics under a probability measure,
on
an arbitrary measurable space. The pinned Mathlib has `covariance_eq_sub`, `covariance_self`, the
bilinearity lemmas and `variance_nonneg` but no such endpoint. It is a deterministic support of the
BKL (68)
posterior noise estimate: the nonnegative variance polynomial of `Y − tX` is expanded by
bilinearity, and both the zero-variance and positive-variance branches in `X` are treated.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace FunctionalInequalities.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Covariance Cauchy–Schwarz**: `cov[X, Y]² ≤ Var X · Var Y` for `X, Y ∈ L²`. -/
theorem covariance_sq_le_variance_mul_variance {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    covariance X Y μ ^ 2 ≤ variance X μ * variance Y μ := by
    have hpoly (t : ℝ) :
        0 ≤ variance X μ * t ^ 2 - 2 * covariance X Y μ * t + variance Y μ := by
      let Z : Ω → ℝ := fun ω => Y ω - t * X ω
      have hXt : MemLp (fun ω => t * X ω) 2 μ := hX.const_mul t
      have hZ : MemLp Z 2 μ := hY.sub hXt
      have hnonneg : 0 ≤ variance Z μ := variance_nonneg Z μ
      rw [← covariance_self hZ.aestronglyMeasurable.aemeasurable] at hnonneg
      change 0 ≤
        covariance (fun ω => Y ω - t * X ω)
          (fun ω => Y ω - t * X ω) μ at hnonneg
      rw [covariance_fun_sub_left hY hXt hZ,
        covariance_fun_sub_right hY hY hXt,
        covariance_const_mul_left t,
        covariance_const_mul_right t] at hnonneg
      rw [covariance_fun_sub_right hX hY hXt,
        covariance_const_mul_right t,
        covariance_self hY.aestronglyMeasurable.aemeasurable,
        covariance_self hX.aestronglyMeasurable.aemeasurable] at hnonneg
      have hcomm : covariance Y X μ = covariance X Y μ := by
        rw [covariance_comm]
      rw [hcomm] at hnonneg
      nlinarith
    have hVX : 0 ≤ variance X μ := variance_nonneg X μ
    have hVY : 0 ≤ variance Y μ := variance_nonneg Y μ
    by_cases hzero : variance X μ = 0
    · have hcov : covariance X Y μ = 0 := by
        by_contra hc
        let t : ℝ := (variance Y μ + 1) / (2 * covariance X Y μ)
        have ht := hpoly t
        have hden : 2 * covariance X Y μ ≠ 0 := by
          intro h
          apply hc
          nlinarith
        have hcalc :
            2 * covariance X Y μ * t = variance Y μ + 1 := by
          dsimp [t]
          field_simp
        nlinarith
      simp [hzero, hcov]
    · have hpos : 0 < variance X μ := lt_of_le_of_ne hVX (Ne.symm hzero)
      let t : ℝ := covariance X Y μ / variance X μ
      have ht := hpoly t
      have hcalc : variance X μ * t = covariance X Y μ := by
        dsimp [t]
        field_simp
      nlinarith

end FunctionalInequalities.Probability
