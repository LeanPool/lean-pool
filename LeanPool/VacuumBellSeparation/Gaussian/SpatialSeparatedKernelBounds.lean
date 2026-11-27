/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.SpatialBesselKernels

/-!
# Actual complex separated-kernel supremum estimates

The principal radius bounds and the genuine Bessel integral estimates
give mass-uniform geometric prefactors on a complex Euclidean
neighbourhood. Taylor coefficient extraction is done in another module
(`spatialFieldCoefficient_expansion`, `spatialFieldCoefficient_norm_le` and their momentum
counterparts in `Gaussian/SpatialKernelCoefficients.lean`).
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

theorem separated_radius_bessel_parameters {μ s d r : ℝ}
    (hμ : 0 < μ) (hs : 0 < s) (hsep : 4 * d ≤ s)
    (hrlow : s - 2 * d ≤ r) (hrup : r ≤ s + d) :
    0 < r ∧ s / 2 ≤ r ∧
      1 + μ * r ≤ 2 * (1 + μ * s) ∧
      Real.sqrt (1 + μ * r) ≤ 2 * Real.sqrt (1 + μ * s) ∧
      Real.exp (-(μ * r)) ≤ Real.exp (-μ * s + 2 * μ * d) := by
  have hrhalf : s / 2 ≤ r := by linarith
  have hr : 0 < r := (by positivity : 0 < s / 2).trans_le hrhalf
  have hrs : r ≤ 2 * s := by linarith
  have hlin : 1 + μ * r ≤ 2 * (1 + μ * s) := by
    have hmul := mul_le_mul_of_nonneg_left hrs hμ.le
    linarith
  have hsqrt : Real.sqrt (1 + μ * r) ≤ 2 * Real.sqrt (1 + μ * s) := by
    have hlin4 : 1 + μ * r ≤ 4 * (1 + μ * s) := by
      nlinarith [mul_pos hμ hs]
    have hsqrt4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq two_pos.le]
    calc
      _ ≤ Real.sqrt (4 * (1 + μ * s)) := Real.sqrt_le_sqrt hlin4
      _ = _ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), hsqrt4]
  refine ⟨hr, hrhalf, hlin, hsqrt, ?_⟩
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonneg_left hrlow hμ.le
  linarith

theorem besselFieldKernel_norm_le_separated {μ s d : ℝ} {ρ : ℂ}
    (hμ : 0 < μ) (hs : 0 < s) (hsep : 4 * d ≤ s)
    (hrlow : s - 2 * d ≤ ρ.re) (hrup : ρ.re ≤ s + d) :
    ‖besselFieldKernel μ ρ‖ ≤
      (6 / s ^ 2) * Real.sqrt (1 + μ * s) * Real.exp (-μ * s + 2 * μ * d) := by
  obtain ⟨hr, hrhalf, hlin, hsqrt, he⟩ :=
    separated_radius_bessel_parameters hμ hs hsep hrlow hrup
  have hpi : 1 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have hsq : s ^ 2 ≤ 4 * ρ.re ^ 2 := by nlinarith
  have hden : s ^ 2 ≤ 4 * Real.pi ^ 2 * ρ.re ^ 2 := by
    have hp := mul_le_mul_of_nonneg_right hpi (show 0 ≤ 4 * ρ.re ^ 2 by positivity)
    nlinarith
  have hc : 3 / (4 * Real.pi ^ 2 * ρ.re ^ 2) ≤ 3 / s ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
  calc
    _ ≤ (3 / (4 * Real.pi ^ 2 * ρ.re ^ 2)) *
        Real.sqrt (1 + μ * ρ.re) * Real.exp (-(μ * ρ.re)) :=
      besselFieldKernel_norm_le hμ hr
    _ ≤ (3 / s ^ 2) * (2 * Real.sqrt (1 + μ * s)) *
        Real.exp (-μ * s + 2 * μ * d) := by
      apply mul_le_mul
      · exact mul_le_mul hc hsqrt (Real.sqrt_nonneg _) (by positivity)
      · exact he
      · exact (Real.exp_pos _).le
      · positivity
    _ = _ := by ring

theorem besselMomentumKernel_norm_le_separated {μ s d : ℝ} {ρ : ℂ}
    (hμ : 0 < μ) (hs : 0 < s) (hsep : 4 * d ≤ s)
    (hrlow : s - 2 * d ≤ ρ.re) (hrup : ρ.re ≤ s + d) :
    ‖besselMomentumKernel μ ρ‖ ≤
      (128 / s ^ 4) * (1 + μ * s) * Real.sqrt (1 + μ * s) *
        Real.exp (-μ * s + 2 * μ * d) := by
  obtain ⟨hr, hrhalf, hlin, hsqrt, he⟩ :=
    separated_radius_bessel_parameters hμ hs hsep hrlow hrup
  have hpi : 1 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have hfour := pow_le_pow_left₀ (show 0 ≤ s / 2 by positivity) hrhalf 4
  have hden : s ^ 4 ≤ 4 * (4 * Real.pi ^ 2 * ρ.re ^ 4) := by
    have hp := mul_le_mul_of_nonneg_right hpi (show 0 ≤ 16 * ρ.re ^ 4 by positivity)
    norm_num [div_pow] at hfour
    nlinarith
  have hc : 8 / (4 * Real.pi ^ 2 * ρ.re ^ 4) ≤ 32 / s ^ 4 := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  calc
    _ ≤ (8 / (4 * Real.pi ^ 2 * ρ.re ^ 4)) *
        (1 + μ * ρ.re) * Real.sqrt (1 + μ * ρ.re) * Real.exp (-(μ * ρ.re)) :=
      besselMomentumKernel_norm_le hμ hr
    _ ≤ (32 / s ^ 4) * (2 * (1 + μ * s)) *
        (2 * Real.sqrt (1 + μ * s)) * Real.exp (-μ * s + 2 * μ * d) := by
      apply mul_le_mul
      · apply mul_le_mul
        · exact mul_le_mul hc hlin (by positivity) (by positivity)
        · exact hsqrt
        · exact Real.sqrt_nonneg _
        · positivity
      · exact he
      · exact (Real.exp_pos _).le
      · positivity
    _ = _ := by ring

theorem spatialBesselFieldKernel_norm_le {μ s d : ℝ}
    (hμ : 0 < μ) (hs : 0 < s) (hd : 0 ≤ d) (hsep : 4 * d ≤ s)
    (δ : EuclideanSpace ℂ (Fin 3)) (hδ : ‖δ‖ ≤ d) :
    ‖besselFieldKernel μ (spatialComplexRadius s δ)‖ ≤
      (6 / s ^ 2) * Real.sqrt (1 + μ * s) * Real.exp (-μ * s + 2 * μ * d) :=
  besselFieldKernel_norm_le_separated hμ hs hsep
    (spatialComplexRadius_re_lower hs.le hd hsep δ hδ)
    (spatialComplexRadius_re_upper hs.le hd δ hδ)

theorem spatialBesselMomentumKernel_norm_le {μ s d : ℝ}
    (hμ : 0 < μ) (hs : 0 < s) (hd : 0 ≤ d) (hsep : 4 * d ≤ s)
    (δ : EuclideanSpace ℂ (Fin 3)) (hδ : ‖δ‖ ≤ d) :
    ‖besselMomentumKernel μ (spatialComplexRadius s δ)‖ ≤
      (128 / s ^ 4) * (1 + μ * s) * Real.sqrt (1 + μ * s) *
        Real.exp (-μ * s + 2 * μ * d) :=
  besselMomentumKernel_norm_le_separated hμ hs hsep
    (spatialComplexRadius_re_lower hs.le hd hsep δ hδ)
    (spatialComplexRadius_re_upper hs.le hd δ hδ)

end VacuumBellSeparation.Gaussian
