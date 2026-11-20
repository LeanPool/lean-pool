/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric

/-!
# Minimal modified-Bessel layer

This file defines only the two integer orders needed by the Ponomarenko dispersion relation.
It uses Mathlib's kernel-checked regularized hypergeometric series, whose convergence radius is
proved in Mathlib to be infinite in this parameter range.
-/

@[expose] public section

namespace FastDynamo.ModifiedBessel

open Complex

/-- The order-zero modified Bessel function, represented as `₀F₁(;1;z²/4)`. -/
noncomputable def I0 (z : ℂ) : ℂ :=
  regularizedHGFun 0 {(1 : ℂ)} (z ^ 2 / 4)

/-- The order-two modified Bessel function, represented as `(z²/4)` times the
*regularized* `₀F₁(;3;z²/4)`. Equivalently, it is `(z²/8)` times the ordinary
`₀F₁`; since `Γ (n+3) = (n+2)!`, this has the usual `I₂` coefficients. -/
noncomputable def I2 (z : ℂ) : ℂ :=
  (z ^ 2 / 4) * regularizedHGFun 0 {(3 : ℂ)} (z ^ 2 / 4)

/-- The hypergeometric series underlying `I₀` converges on the whole complex plane. -/
theorem I0_series_radius : (regularizedHGFunSeries 0 {(1 : ℂ)}).radius = ⊤ :=
  radius_regularizedHGFunSeries_eq_top (by simp)

/-- The regularized hypergeometric function with a single denominator parameter
is entire. -/
theorem regularizedHGFun_analyticAt_singleton (c z : ℂ) :
    AnalyticAt ℂ (regularizedHGFun 0 {c}) z := by
  have hr : (regularizedHGFunSeries 0 {c}).radius = ⊤ :=
    radius_regularizedHGFunSeries_eq_top (by simp)
  have hz : z ∈ Metric.eball (0 : ℂ) (regularizedHGFunSeries 0 {c}).radius := by
    rw [hr]
    exact edist_lt_top _ _
  exact (regularizedHGFunSeries 0 {c}).hasFPowerSeriesOnBall (by simp [hr])
    |>.analyticAt_of_mem hz

/-- `I₀` is complex analytic at every point. -/
theorem I0_analyticAt (z : ℂ) : AnalyticAt ℂ I0 z := by
  unfold I0
  have hinner : AnalyticAt ℂ (fun z : ℂ ↦ z ^ 2 / 4) z :=
    (analyticAt_id.pow 2).div_const
  change AnalyticAt ℂ
    ((regularizedHGFun 0 {(1 : ℂ)}) ∘ fun z : ℂ ↦ z ^ 2 / 4) z
  exact AnalyticAt.comp
    (g := regularizedHGFun 0 {(1 : ℂ)}) (f := fun z : ℂ ↦ z ^ 2 / 4)
    (regularizedHGFun_analyticAt_singleton 1 (z ^ 2 / 4)) hinner

/-- `I₂` is complex analytic at every point. -/
theorem I2_analyticAt (z : ℂ) : AnalyticAt ℂ I2 z := by
  unfold I2
  have hinner : AnalyticAt ℂ (fun z : ℂ ↦ z ^ 2 / 4) z :=
    (analyticAt_id.pow 2).div_const
  have hcomp : AnalyticAt ℂ
      ((regularizedHGFun 0 {(3 : ℂ)}) ∘ fun z : ℂ ↦ z ^ 2 / 4) z :=
    AnalyticAt.comp
      (g := regularizedHGFun 0 {(3 : ℂ)}) (f := fun z : ℂ ↦ z ^ 2 / 4)
      (regularizedHGFun_analyticAt_singleton 3 (z ^ 2 / 4)) hinner
  exact hinner.mul hcomp

/-- The order-zero function is even. -/
@[simp] theorem I0_neg (z : ℂ) : I0 (-z) = I0 z := by
  simp [I0]

/-- The order-two function is even. -/
@[simp] theorem I2_neg (z : ℂ) : I2 (-z) = I2 z := by
  simp [I2]

/-- Scalar multiplication by a constant is complex differentiable with
derivative that constant. -/
theorem mul_variable_hasDerivAt (kappa r : ℂ) :
    HasDerivAt (fun s : ℂ ↦ kappa * s) kappa r := by
  simpa using (hasDerivAt_id r).const_mul kappa

end FastDynamo.ModifiedBessel
