/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.SpatialRadiusHolomorphic

/-!
# Literal Bessel expressions for the separated field and momentum kernels

These are the expressions in the manuscript, constructed from actual
complex cosh integrals. Holomorphy and bounds are proved here. Equality
with the Fourier covariance distribution is a separate theorem.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

/-- Bessel field kernel given by `(μ : ℂ) / ((4 * Real.pi ^ 2 : ℝ) * ρ) *
modifiedBesselComplexIntegral 1 ((μ : ℂ) * ρ)`. -/
noncomputable def besselFieldKernel (μ : ℝ) (ρ : ℂ) : ℂ :=
  (μ : ℂ) / ((4 * Real.pi ^ 2 : ℝ) * ρ) * modifiedBesselComplexIntegral 1 ((μ : ℂ) * ρ)

/-- Momentum part of the covariance kernel in its Bessel-function representation. -/
noncomputable def besselMomentumKernel (μ : ℝ) (ρ : ℂ) : ℂ :=
  -(μ : ℂ) ^ 2 / ((4 * Real.pi ^ 2 : ℝ) * ρ ^ 2) *
    modifiedBesselComplexIntegral 2 ((μ : ℂ) * ρ)

theorem differentiableAt_besselFieldKernel {μ : ℝ} (hμ : 0 < μ)
    {ρ : ℂ} (hρ : 0 < ρ.re) : DifferentiableAt ℂ (besselFieldKernel μ) ρ := by
  have harg : 0 < ((μ : ℂ) * ρ).re := by simpa using mul_pos hμ hρ
  have hK := (hasDerivAt_modifiedBesselComplexIntegral 1
    (fun x hx => by simpa only [Nat.cast_one, one_mul] using integrableOn_modifiedBessel_one hx)
    harg).differentiableAt
  have hρ0 : ρ ≠ 0 := by intro h; simp [h] at hρ
  unfold besselFieldKernel
  apply DifferentiableAt.mul
  · exact (differentiableAt_const _).div
      ((differentiableAt_const _).mul differentiableAt_id)
      (mul_ne_zero (by exact_mod_cast (show (4 * Real.pi ^ 2 : ℝ) ≠ 0 by positivity)) hρ0)
  · exact hK.comp ρ ((differentiableAt_const _).mul differentiableAt_id)

theorem differentiableAt_besselMomentumKernel {μ : ℝ} (hμ : 0 < μ)
    {ρ : ℂ} (hρ : 0 < ρ.re) : DifferentiableAt ℂ (besselMomentumKernel μ) ρ := by
  have harg : 0 < ((μ : ℂ) * ρ).re := by simpa using mul_pos hμ hρ
  have hK := (hasDerivAt_modifiedBesselComplexIntegral 2
    (fun x hx => by simpa only [Nat.cast_ofNat] using integrableOn_modifiedBessel_two hx)
    harg).differentiableAt
  have hρ0 : ρ ≠ 0 := by intro h; simp [h] at hρ
  unfold besselMomentumKernel
  apply DifferentiableAt.mul
  · exact (differentiableAt_const _).div
      ((differentiableAt_const _).mul (differentiableAt_id.pow 2))
      (mul_ne_zero (by exact_mod_cast (show (4 * Real.pi ^ 2 : ℝ) ≠ 0 by positivity))
        (pow_ne_zero _ hρ0))
  · exact hK.comp ρ ((differentiableAt_const _).mul differentiableAt_id)

theorem besselFieldKernel_norm_le {μ : ℝ} (hμ : 0 < μ)
    {ρ : ℂ} (hρ : 0 < ρ.re) :
    ‖besselFieldKernel μ ρ‖ ≤
      (3 / (4 * Real.pi ^ 2 * ρ.re ^ 2)) *
        Real.sqrt (1 + μ * ρ.re) * Real.exp (-(μ * ρ.re)) := by
  have hrn : ρ.re ≤ ‖ρ‖ := Complex.re_le_norm _
  have hn : 0 < ‖ρ‖ := hρ.trans_le hrn
  have hc : 0 < 4 * Real.pi ^ 2 := by positivity
  have ht : 0 < μ * ρ.re := mul_pos hμ hρ
  have hK := modifiedBesselComplexIntegral_norm_le 1 ((μ : ℂ) * ρ)
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hK
  have hKr : 0 ≤ modifiedBesselIntegral 1 (μ * ρ.re) :=
    hK.trans' (norm_nonneg _)
  calc
    ‖besselFieldKernel μ ρ‖ = μ / (4 * Real.pi ^ 2 * ‖ρ‖) *
        ‖modifiedBesselComplexIntegral 1 ((μ : ℂ) * ρ)‖ := by
      simp only [besselFieldKernel, norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hμ, abs_of_nonneg (sq_nonneg Real.pi)]
      norm_num
    _ ≤ μ / (4 * Real.pi ^ 2 * ρ.re) * modifiedBesselIntegral 1 (μ * ρ.re) := by
      apply mul_le_mul
      · exact div_le_div_of_nonneg_left hμ.le (mul_pos hc hρ)
          (mul_le_mul_of_nonneg_left hrn hc.le)
      · exact hK
      · exact norm_nonneg _
      · positivity
    _ = ((μ * ρ.re) * modifiedBesselIntegral 1 (μ * ρ.re)) /
        (4 * Real.pi ^ 2 * ρ.re ^ 2) := by field_simp
    _ ≤ (3 * Real.sqrt (1 + μ * ρ.re) * Real.exp (-(μ * ρ.re))) /
        (4 * Real.pi ^ 2 * ρ.re ^ 2) :=
      div_le_div_of_nonneg_right (modifiedBesselIntegral_one_scaled_le ht) (by positivity)
    _ = _ := by ring

theorem besselMomentumKernel_norm_le {μ : ℝ} (hμ : 0 < μ)
    {ρ : ℂ} (hρ : 0 < ρ.re) :
    ‖besselMomentumKernel μ ρ‖ ≤
      (8 / (4 * Real.pi ^ 2 * ρ.re ^ 4)) *
        (1 + μ * ρ.re) * Real.sqrt (1 + μ * ρ.re) * Real.exp (-(μ * ρ.re)) := by
  have hrn : ρ.re ≤ ‖ρ‖ := Complex.re_le_norm _
  have hn : 0 < ‖ρ‖ := hρ.trans_le hrn
  have hc : 0 < 4 * Real.pi ^ 2 := by positivity
  have ht : 0 < μ * ρ.re := mul_pos hμ hρ
  have hK := modifiedBesselComplexIntegral_norm_le 2 ((μ : ℂ) * ρ)
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hK
  calc
    ‖besselMomentumKernel μ ρ‖ = μ ^ 2 / (4 * Real.pi ^ 2 * ‖ρ‖ ^ 2) *
        ‖modifiedBesselComplexIntegral 2 ((μ : ℂ) * ρ)‖ := by
      simp only [besselMomentumKernel, norm_mul, norm_div, norm_neg, norm_pow,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hμ,
        abs_of_pos Real.pi_pos]
      norm_num
    _ ≤ μ ^ 2 / (4 * Real.pi ^ 2 * ρ.re ^ 2) * modifiedBesselIntegral 2 (μ * ρ.re) := by
      apply mul_le_mul
      · apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
        apply mul_le_mul_of_nonneg_left _ hc.le
        nlinarith
      · exact hK
      · exact norm_nonneg _
      · positivity
    _ = ((μ * ρ.re) ^ 2 * modifiedBesselIntegral 2 (μ * ρ.re)) /
        (4 * Real.pi ^ 2 * ρ.re ^ 4) := by field_simp
    _ ≤ (8 * (1 + μ * ρ.re) * Real.sqrt (1 + μ * ρ.re) * Real.exp (-(μ * ρ.re))) /
        (4 * Real.pi ^ 2 * ρ.re ^ 4) :=
      div_le_div_of_nonneg_right (modifiedBesselIntegral_two_scaled_le ht) (by positivity)
    _ = _ := by ring

theorem differentiableAt_spatialBesselFieldKernel {μ s : ℝ} (hμ : 0 < μ)
    (δ : EuclideanSpace ℂ (Fin 3)) (hδ : 0 < (spatialSquaredRadius s δ).re) :
    DifferentiableAt ℂ (fun d => besselFieldKernel μ (spatialComplexRadius s d)) δ :=
  (differentiableAt_besselFieldKernel hμ (spatialComplexRadius_re_pos_of_squared s δ hδ)).comp δ
    (differentiableAt_spatialComplexRadius s δ hδ)

theorem differentiableAt_spatialBesselMomentumKernel {μ s : ℝ} (hμ : 0 < μ)
    (δ : EuclideanSpace ℂ (Fin 3)) (hδ : 0 < (spatialSquaredRadius s δ).re) :
    DifferentiableAt ℂ (fun d => besselMomentumKernel μ (spatialComplexRadius s d)) δ :=
  (differentiableAt_besselMomentumKernel hμ (spatialComplexRadius_re_pos_of_squared s δ hδ)).comp δ
    (differentiableAt_spatialComplexRadius s δ hδ)

end VacuumBellSeparation.Gaussian
