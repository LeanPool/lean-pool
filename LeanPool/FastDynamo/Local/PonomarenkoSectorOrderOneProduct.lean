/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Local.PonomarenkoSecondOrderProduct

/-!
# The order-one product estimate on a sector

The paper chooses the radial parameter on the segment `κ = ϱ(1+it)`, `t ∈ [1/2, 3/4]`
(proof of `lem:jump-horizontal-mode`).  Combined with the second-order cancellation of
`PonomarenkoSecondOrderProduct`, the order-one product estimate only needs `1 ≤ Re z` and the
aperture-two sector condition `‖z‖ ≤ 2 Re z` for the argument `z = ϱw`.  This module proves the
estimate with `z` free, so that it applies verbatim on the paper's segment and on any disk
inside the sector (`PonomarenkoSegmentDispersion`).

## Contents

* Factorization of `z I₁(z) K₁(z)` into `(z/π)` times the two exponentially normalized Gaussian
  factors, at a free argument.
* The sectorised second-order estimate `‖z I₁(z) K₁(z) - 1/2‖ ≤ 3/(Re z)²`.
-/

@[expose] public section

noncomputable section

namespace FastDynamo

open Complex MeasureTheory Set Real

/-- Factorization of the order-one product `z I₁(z)K₁(z)` into `(z/π)` times the product of the
two exponentially normalized integral factors `π e^{-z}I₁(z)` and `e^{z}K₁(z)`, at a free
argument. -/
theorem ponomarenkoOrderOneProduct_mul_eq_factors (z : ℂ) :
    z * ponomarenkoOrderOneProduct z =
      (z / (Real.pi : ℂ)) *
        (ponomarenkoI1Factor z * ponomarenkoK1Factor z) := by
  rw [ponomarenkoOrderOneProduct, ponomarenkoI1Factor, ponomarenkoK1Factor]
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [Complex.exp_neg]
  field_simp [hpi, Complex.exp_ne_zero]

/-- The sectorised second-order product estimate.  For every `z` with `1 ≤ Re z` inside the
aperture-two sector `‖z‖ ≤ 2 Re z`, the order-one modified-Bessel product satisfies
`‖z I₁(z) K₁(z) - 1/2‖ ≤ 3/(Re z)²`.

This is an effective order-one counterpart of the product expansion
`I_ν(κ)K_ν(κ) = 1/(2κ) - (4ν²-1)/(16κ³) + O(ϱ⁻⁵)`, `ν ∈ {0, 2}`, which the paper quotes from
DLMF as `eq:bessel-product-expansion` (proof of `lem:jump-horizontal-mode`); the formalisation
reaches the orders `0, 2` through this order-one estimate (`PonomarenkoSegmentDispersion`).
The first corrections of the two factors are `∓3/(8z)` and cancel, leaving an
`O((Re z)⁻²)` remainder. -/
theorem norm_ponomarenkoOrderOneProduct_mul_sub_half_le_three_div_re_sq
    {z : ℂ} (hzOne : 1 ≤ z.re) (hzSector : ‖z‖ ≤ 2 * z.re) :
    ‖z * ponomarenkoOrderOneProduct z - (1 / 2 : ℂ)‖ ≤ 3 / z.re ^ 2 := by
  let a : ℝ := z.re
  let A : ℂ := ponomarenkoI1Factor z
  let B : ℂ := ponomarenkoK1Factor z
  let G : ℂ := ponomarenkoHalfGaussian z
  let H : ℝ := ponomarenkoHalfGaussianMajorant z
  let c : ℂ := ponomarenkoOrderOneFirstCorrection z
  let rI : ℂ := ponomarenkoI1SecondOrderRemainder z
  let rK : ℂ := ponomarenkoK1SecondOrderRemainder z
  let RI : ℝ := 15 * H / (16 * a ^ 2)
  let RK : ℝ := 15 * H / (128 * a ^ 2)
  have haOne : 1 ≤ a := hzOne
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one haOne
  have hz : 0 < z.re := ha
  have hzNormLe : ‖z‖ ≤ 2 * a := hzSector
  have hGle : ‖G‖ ≤ H := by
    simpa [G, H] using norm_ponomarenkoHalfGaussian_le_majorant hz
  have hH0 : 0 ≤ H := by
    dsimp [H, ponomarenkoHalfGaussianMajorant]
    positivity
  have hHsq : H ^ 2 = Real.pi / (2 * a) := by
    simpa [H, a] using ponomarenkoHalfGaussianMajorant_sq hz
  have hRI0 : 0 ≤ RI := by dsimp [RI]; positivity
  have hRK0 : 0 ≤ RK := by dsimp [RK]; positivity
  have hrI : ‖rI‖ ≤ RI := by
    have hint :=
      ModifiedBessel.norm_integral_I1SecondOrderGaussianRemainderKernel_le_halfLine hz
    have hrealG : ModifiedBessel.realGaussianHalfLine a = H := by
      simpa [a, H] using realGaussianHalfLine_eq_ponomarenkoMajorant hz
    change ‖z * ∫ x : ℝ in Ioi 0,
      ModifiedBessel.I1SecondOrderGaussianRemainderKernel z x‖ ≤ RI
    rw [norm_mul]
    calc
      ‖z‖ * ‖∫ x : ℝ in Ioi 0,
          ModifiedBessel.I1SecondOrderGaussianRemainderKernel z x‖ ≤
          ‖z‖ * (15 * ModifiedBessel.realGaussianHalfLine z.re /
            (32 * z.re ^ 3)) :=
        mul_le_mul_of_nonneg_left hint (norm_nonneg z)
      _ ≤ (2 * a) * (15 * H / (32 * a ^ 3)) := by
        rw [show z.re = a by rfl, hrealG]
        gcongr
      _ = RI := by
        dsimp [RI]
        field_simp [ha.ne']
        ring
  have hrK : ‖rK‖ ≤ RK := by
    have hint :=
      ModifiedBessel.norm_integral_K1FirstOrderGaussianRemainderKernel_le_halfLine hz
    have hrealG : ModifiedBessel.realGaussianHalfLine a = H := by
      simpa [a, H] using realGaussianHalfLine_eq_ponomarenkoMajorant hz
    simpa [rK, RK, ponomarenkoK1SecondOrderRemainder, a, hrealG] using hint
  have hc : ‖c‖ ≤ 3 / (8 * a) := by
    have hzNormPos : 0 < ‖z‖ := by
      apply norm_pos_iff.mpr
      intro h
      rw [h] at hz
      simp at hz
    have hreNorm : a ≤ ‖z‖ := by
      simpa [a] using Complex.re_le_norm z
    change ‖(3 / 8 : ℂ) * z⁻¹‖ ≤ 3 / (8 * a)
    rw [norm_mul, norm_inv]
    norm_num
    calc
      3 / 8 * ‖z‖⁻¹ = 3 / (8 * ‖z‖) := by
        field_simp [hzNormPos.ne']
      _ ≤ 3 / (8 * a) := by
        rw [div_le_div_iff₀ (show 0 < 8 * ‖z‖ by positivity)
          (show 0 < 8 * a by positivity)]
        nlinarith
  have hcOne : ‖c‖ ≤ 1 := by
    calc
      ‖c‖ ≤ 3 / (8 * a) := hc
      _ ≤ 1 := by
        rw [div_le_iff₀ (show 0 < 8 * a by positivity)]
        nlinarith
  have hOneSub : ‖1 - c‖ ≤ 2 := by
    calc
      ‖1 - c‖ ≤ ‖(1 : ℂ)‖ + ‖c‖ := norm_sub_le _ _
      _ ≤ 2 := by norm_num; linarith
  have hOneAdd : ‖1 + c‖ ≤ 2 := by
    calc
      ‖1 + c‖ ≤ ‖(1 : ℂ)‖ + ‖c‖ := norm_add_le _ _
      _ ≤ 2 := by norm_num; linarith
  have hcancel : A * B - G ^ 2 =
      -(c ^ 2 * G ^ 2) + (1 - c) * G * rK +
        (1 + c) * G * rI + rI * rK := by
    simpa [A, B, G, c, rI, rK] using
      ponomarenko_corrected_factors_product_sub_gaussian_sq hz
  have hab : ‖A * B - G ^ 2‖ ≤
      (3 / (8 * a)) ^ 2 * H ^ 2 +
        2 * H * RK + 2 * H * RI + RI * RK := by
    rw [hcancel]
    calc
      ‖-(c ^ 2 * G ^ 2) + (1 - c) * G * rK +
          (1 + c) * G * rI + rI * rK‖ ≤
          ((‖c ^ 2 * G ^ 2‖ + ‖(1 - c) * G * rK‖) +
            ‖(1 + c) * G * rI‖) + ‖rI * rK‖ := by
        calc
          _ ≤ ‖-(c ^ 2 * G ^ 2) + (1 - c) * G * rK +
                (1 + c) * G * rI‖ + ‖rI * rK‖ := norm_add_le _ _
          _ ≤ (‖-(c ^ 2 * G ^ 2) + (1 - c) * G * rK‖ +
                ‖(1 + c) * G * rI‖) + ‖rI * rK‖ := by
            gcongr
            exact norm_add_le _ _
          _ ≤ ((‖-(c ^ 2 * G ^ 2)‖ + ‖(1 - c) * G * rK‖) +
                ‖(1 + c) * G * rI‖) + ‖rI * rK‖ := by
            gcongr
            exact norm_add_le _ _
          _ = _ := by rw [norm_neg]
      _ = ((‖c‖ ^ 2 * ‖G‖ ^ 2 + ‖1 - c‖ * ‖G‖ * ‖rK‖) +
            ‖1 + c‖ * ‖G‖ * ‖rI‖) + ‖rI‖ * ‖rK‖ := by
        simp only [norm_mul, norm_pow]
      _ ≤ (3 / (8 * a)) ^ 2 * H ^ 2 +
          2 * H * RK + 2 * H * RI + RI * RK := by
        gcongr
  have hscale :
      z * ponomarenkoOrderOneProduct z - (1 / 2 : ℂ) =
        (z / (Real.pi : ℂ)) * (A * B - G ^ 2) := by
    rw [ponomarenkoOrderOneProduct_mul_eq_factors]
    dsimp [A, B, G]
    rw [ponomarenkoHalfGaussian_sq hz]
    have hz0 : z ≠ 0 := by
      intro h
      rw [h] at hz
      simp at hz
    have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp [hz0, hpi]
  have hscaleNorm : ‖z / (Real.pi : ℂ)‖ ≤ 2 * a / Real.pi := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    gcongr
  have hexact :
      (2 * a / Real.pi) *
          ((3 / (8 * a)) ^ 2 * H ^ 2 +
            2 * H * RK + 2 * H * RI + RI * RK) =
        9 / (4 * a ^ 2) + 225 / (2048 * a ^ 4) := by
    have hcombine :
        (3 / (8 * a)) ^ 2 * H ^ 2 +
            2 * H * RK + 2 * H * RI + RI * RK =
          9 / (4 * a ^ 2) * H ^ 2 +
            225 / (2048 * a ^ 4) * H ^ 2 := by
      dsimp [RI, RK]
      field_simp [ha.ne']
      ring
    rw [hcombine, hHsq]
    field_simp [ha.ne', Real.pi_ne_zero]
  have haPow : a ^ 2 ≤ a ^ 4 := by
    have haSqOne : 1 ≤ a ^ 2 := by nlinarith
    calc
      a ^ 2 = a ^ 2 * 1 := by ring
      _ ≤ a ^ 2 * a ^ 2 := mul_le_mul_of_nonneg_left haSqOne (sq_nonneg a)
      _ = a ^ 4 := by ring
  have hcross : 225 / (2048 * a ^ 4) ≤ 3 / (4 * a ^ 2) := by
    rw [div_le_div_iff₀ (show 0 < 2048 * a ^ 4 by positivity)
      (show 0 < 4 * a ^ 2 by positivity)]
    nlinarith
  calc
    ‖z * ponomarenkoOrderOneProduct z - (1 / 2 : ℂ)‖ =
        ‖z / (Real.pi : ℂ)‖ * ‖A * B - G ^ 2‖ := by
      rw [hscale, norm_mul]
    _ ≤ (2 * a / Real.pi) *
        ((3 / (8 * a)) ^ 2 * H ^ 2 +
          2 * H * RK + 2 * H * RI + RI * RK) := by
      exact mul_le_mul hscaleNorm hab (norm_nonneg _) (by positivity)
    _ = 9 / (4 * a ^ 2) + 225 / (2048 * a ^ 4) := hexact
    _ ≤ 9 / (4 * a ^ 2) + 3 / (4 * a ^ 2) := by gcongr
    _ = 3 / a ^ 2 := by ring
    _ = 3 / z.re ^ 2 := by rfl

end FastDynamo
