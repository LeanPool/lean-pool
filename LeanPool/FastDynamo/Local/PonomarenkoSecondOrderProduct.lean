/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Local.ModifiedBesselKSecondOrderGaussian
public import LeanPool.FastDynamo.Local.PonomarenkoGaussianFactors

/-!
# Second-order cancellation in the Ponomarenko order-one product

The quantitative form of the dispersion function on the segment of Lemma 2.1
(`lem:jump-horizontal-mode`), proved in `PonomarenkoSegmentDispersion`, needs a uniform bound
on `‖Q(z) - 1/2‖` for the order-one product `Q(z) = z I₁(z) K₁(z)` on a sector; that bound is
`PonomarenkoSectorOrderOneProduct`.  A first-order Gaussian expansion of the two factors is
not enough: their leading corrections are `∓3/(8z)` and cancel, so the true rate is
`O((Re z)⁻²)` and a second-order expansion is required.  This module supplies it.

The `K₁` expansion is `ModifiedBesselKSecondOrderGaussian`; this module supplies that of the
order-one first-kind factor.  Its exact Gaussian-coordinate
amplitude `x² √(1 - x²/4)` is expanded past its first two Taylor terms `x² - x⁴/8`, the
remainder is bounded by `x⁶/32` on the whole half-line, and the exact fourth and sixth
Gaussian moments convert that into a corrected `I₁` expansion with an explicit remainder.

Combining it with the corresponding `K₁` expansion, the two first corrections cancel in the
product (`ponomarenko_corrected_factors_product_sub_gaussian_sq`).

## Contents

* Second-order Gaussian expansion for `I₁`: the amplitude remainder and its kernel, their
  half-line bounds and integrals, and the corrected expansion of the exponentially normalized
  `I₁`.
* Second-order cancellation in the Ponomarenko order-one product: the common first
  correction, the two exact remainders, the corrected factorizations, and the cancellation in
  the product.
-/

@[expose] public section

/-!
## Second-order Gaussian expansion for `I₁`

The exact Gaussian-coordinate amplitude for the exponentially normalized
order-one modified Bessel function is

`x² sqrt (1 - x² / 4)`.

Its first two Taylor terms `x² - x⁴/8` are subtracted here.  The
totalized square root still permits a global half-line estimate: the remaining
amplitude is bounded by `x⁶/32`, including beyond the cutoff `x = 2`.
Together with the exact fourth and sixth Gaussian moments, this yields the
corrected `I₁` expansion.
-/

noncomputable section

open Complex MeasureTheory Set Filter Real

namespace FastDynamo.ModifiedBessel

/-- The second-order remainder after subtracting `x² - x⁴/8` from the
nonsingular `I₁` Gaussian amplitude. -/
def I1SecondOrderGaussianAmplitudeRemainder (x : ℝ) : ℝ :=
  I1QuadraticGaussianAmplitude x - x ^ 2 + x ^ 4 / 8

/-- The corresponding complex Gaussian remainder kernel. -/
def I1SecondOrderGaussianRemainderKernel (z : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (-z * (x : ℂ) ^ 2 / 2) *
    (I1SecondOrderGaussianAmplitudeRemainder x : ℂ)

/-- On `[0, 2]` the second-order amplitude remainder equals `-x² (s-1)²/2` with
`s = sqrt (1 - x²/4)`, hence is bounded in absolute value by `x⁶/32`. -/
private lemma abs_I1SecondOrderGaussianAmplitudeRemainder_le_of_le_two
    {x : ℝ} (hx0 : 0 ≤ x) (hx2 : x ≤ 2) :
    |I1SecondOrderGaussianAmplitudeRemainder x| ≤ x ^ 6 / 32 := by
  let s : ℝ := Real.sqrt (1 - x ^ 2 / 4)
  have hrad : 0 ≤ 1 - x ^ 2 / 4 := by
    nlinarith [sq_nonneg x]
  have hsSq : s ^ 2 = 1 - x ^ 2 / 4 := by
    exact Real.sq_sqrt hrad
  have hquarter : x ^ 2 / 8 = (1 - s ^ 2) / 2 := by
    nlinarith [hsSq]
  have hremainder : I1SecondOrderGaussianAmplitudeRemainder x =
      -(x ^ 2 * (s - 1) ^ 2 / 2) := by
    rw [I1SecondOrderGaussianAmplitudeRemainder,
      I1QuadraticGaussianAmplitude]
    change x ^ 2 * s - x ^ 2 + x ^ 4 / 8 = _
    rw [show x ^ 4 / 8 = x ^ 2 * (x ^ 2 / 8) by ring, hquarter]
    ring
  have hsBound : |s - 1| ≤ x ^ 2 / 4 := by
    exact abs_sqrt_one_sub_quarter_sq_sub_one_le hx0
  have hsPowBound : (s - 1) ^ 2 ≤ (x ^ 2 / 4) ^ 2 := by
    apply sq_le_sq.mpr
    simpa [abs_of_nonneg (by positivity : 0 ≤ x ^ 2 / 4)] using hsBound
  rw [hremainder, abs_neg, abs_div, abs_mul,
    abs_of_nonneg (sq_nonneg x), abs_pow]
  norm_num
  calc
    x ^ 2 * (s - 1) ^ 2 / 2 ≤ x ^ 2 * (x ^ 2 / 4) ^ 2 / 2 := by
      gcongr
    _ = x ^ 6 / 32 := by ring

/-- Beyond the cutoff `x = 2` the totalized square root makes the amplitude vanish, so the
remainder reduces to `x⁴/8 - x²`, which is still bounded in absolute value by `x⁶/32`. -/
private lemma abs_I1SecondOrderGaussianAmplitudeRemainder_le_of_two_le
    {x : ℝ} (hx2 : 2 ≤ x) :
    |I1SecondOrderGaussianAmplitudeRemainder x| ≤ x ^ 6 / 32 := by
  have hrad : 1 - x ^ 2 / 4 ≤ 0 := by
    nlinarith [sq_nonneg x]
  have hamp : I1QuadraticGaussianAmplitude x = 0 := by
    rw [I1QuadraticGaussianAmplitude, Real.sqrt_eq_zero_of_nonpos hrad]
    ring
  let y : ℝ := x ^ 2
  have hy4 : 4 ≤ y := by
    dsimp [y]
    nlinarith [sq_nonneg x]
  have hremainder : I1SecondOrderGaussianAmplitudeRemainder x = y ^ 2 / 8 - y := by
    rw [I1SecondOrderGaussianAmplitudeRemainder, hamp]
    dsimp [y]
    ring
  rw [hremainder, show x ^ 6 / 32 = y ^ 3 / 32 by
    dsimp [y]
    ring]
  by_cases hy8 : y ≤ 8
  · have hnonpos : y ^ 2 / 8 - y ≤ 0 := by
      nlinarith [sq_nonneg y]
    rw [abs_of_nonpos hnonpos]
    have hfactor : 0 ≤ y * (y - 4) * (y + 8) := by positivity
    nlinarith
  · have hy8' : 8 ≤ y := le_of_not_ge hy8
    have hnonneg : 0 ≤ y ^ 2 / 8 - y := by
      nlinarith [sq_nonneg y]
    rw [abs_of_nonneg hnonneg]
    have hfactor : 0 ≤ y ^ 2 * (y - 4) := by positivity
    nlinarith

/-- Global second-order Taylor estimate for the totalized `I₁` Gaussian
amplitude.  The constant `1/32` is also attained at the cutoff `x = 2`. -/
theorem abs_I1SecondOrderGaussianAmplitudeRemainder_le
    {x : ℝ} (hx0 : 0 ≤ x) :
    |I1SecondOrderGaussianAmplitudeRemainder x| ≤ x ^ 6 / 32 := by
  rcases le_total x 2 with hx2 | hx2
  · exact abs_I1SecondOrderGaussianAmplitudeRemainder_le_of_le_two hx0 hx2
  · exact abs_I1SecondOrderGaussianAmplitudeRemainder_le_of_two_le hx2

/-- Pointwise complex-kernel form of the global sixth-order remainder. -/
theorem norm_I1SecondOrderGaussianRemainderKernel_le
    (z : ℂ) {x : ℝ} (hx0 : 0 ≤ x) :
    ‖I1SecondOrderGaussianRemainderKernel z x‖ ≤
      Real.exp (-z.re * x ^ 2 / 2) * (x ^ 6 / 32) := by
  rw [I1SecondOrderGaussianRemainderKernel, norm_mul, Complex.norm_exp]
  have hre : (-z * (x : ℂ) ^ 2 / 2).re = -z.re * x ^ 2 / 2 := by
    simp [Complex.mul_re, pow_two]
  rw [hre, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left
    (abs_I1SecondOrderGaussianAmplitudeRemainder_le hx0)
    (Real.exp_pos _).le

/-- For `a > 0` the sixth-order Gaussian majorant `exp(-a x²/2) · x⁶/32` is integrable on the
positive half-line. -/
private theorem integrableOn_I1SecondOrderGaussianMajorant
    {a : ℝ} (ha : 0 < a) :
    IntegrableOn
      (fun x : ℝ ↦ Real.exp (-a * x ^ 2 / 2) * (x ^ 6 / 32))
      (Ioi 0) := by
  have h := (integrableOn_rpow_mul_exp_neg_mul_sq
    (show 0 < a / 2 by positivity) (s := (6 : ℝ)) (by norm_num)).const_mul
      (1 / 32 : ℝ)
  have heq :
      (fun x : ℝ ↦ Real.exp (-a * x ^ 2 / 2) * (x ^ 6 / 32)) =
        (fun x : ℝ ↦ (1 / 32 : ℝ) *
          (x ^ (6 : ℝ) * Real.exp (-(a / 2) * x ^ 2))) := by
    funext x
    rw [← Real.rpow_natCast x 6]
    have hexp : -a * x ^ 2 / 2 = -(a / 2) * x ^ 2 := by ring
    rw [hexp]
    ring_nf
  rw [heq]
  exact h

/-- For `Re z > 0` the second-order `I₁` Gaussian remainder kernel is integrable on the positive
half-line, being dominated by the sixth-order majorant. -/
private theorem integrableOn_I1SecondOrderGaussianRemainderKernel
    {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (I1SecondOrderGaussianRemainderKernel z) (Ioi 0) := by
  have hmajor := integrableOn_I1SecondOrderGaussianMajorant hz
  apply Integrable.mono hmajor
  · apply Continuous.aestronglyMeasurable
    unfold I1SecondOrderGaussianRemainderKernel
      I1SecondOrderGaussianAmplitudeRemainder I1QuadraticGaussianAmplitude
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (by positivity))]
    exact norm_I1SecondOrderGaussianRemainderKernel_le z (mem_Ioi.mp hx).le

/-- Integrated remainder estimate before evaluating the real sixth moment. -/
theorem norm_integral_I1SecondOrderGaussianRemainderKernel_le
    {z : ℂ} (hz : 0 < z.re) :
    ‖∫ x : ℝ in Ioi 0, I1SecondOrderGaussianRemainderKernel z x‖ ≤
      ∫ x : ℝ in Ioi 0,
        Real.exp (-z.re * x ^ 2 / 2) * (x ^ 6 / 32) := by
  apply norm_integral_le_of_norm_le
    (integrableOn_I1SecondOrderGaussianMajorant hz)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact norm_I1SecondOrderGaussianRemainderKernel_le z (mem_Ioi.mp hx).le

/-- Evaluation of the real sixth-moment majorant in the nonsingular
half-Gaussian normalization. -/
theorem integral_I1SecondOrderGaussianMajorant
    {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ in Ioi 0,
        Real.exp (-a * x ^ 2 / 2) * (x ^ 6 / 32)) =
      15 * realGaussianHalfLine a / (32 * a ^ 3) := by
  calc
    (∫ x : ℝ in Ioi 0,
        Real.exp (-a * x ^ 2 / 2) * (x ^ 6 / 32)) =
        (1 / 32 : ℝ) *
          (∫ x : ℝ in Ioi 0, x ^ 6 * Real.exp (-a * x ^ 2 / 2)) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      ring
    _ = 15 * realGaussianHalfLine a / (32 * a ^ 3) := by
      rw [integral_realGaussianSixthMoment_eq_fifteen_mul_halfLine_div_cube ha]
      ring

/-- Integrated complex remainder after exact sixth-moment evaluation. -/
theorem norm_integral_I1SecondOrderGaussianRemainderKernel_le_halfLine
    {z : ℂ} (hz : 0 < z.re) :
    ‖∫ x : ℝ in Ioi 0, I1SecondOrderGaussianRemainderKernel z x‖ ≤
      15 * realGaussianHalfLine z.re / (32 * z.re ^ 3) := by
  calc
    ‖∫ x : ℝ in Ioi 0, I1SecondOrderGaussianRemainderKernel z x‖ ≤
        ∫ x : ℝ in Ioi 0,
          Real.exp (-z.re * x ^ 2 / 2) * (x ^ 6 / 32) :=
      norm_integral_I1SecondOrderGaussianRemainderKernel_le hz
    _ = 15 * realGaussianHalfLine z.re / (32 * z.re ^ 3) :=
      integral_I1SecondOrderGaussianMajorant hz

/-- Exact corrected expansion of the exponentially normalized `I₁` factor.
Writing `G(z) = ∫₀∞ exp (-z x²/2) dx`, the displayed main terms are
`G(z) - (3/(8z)) G(z)`; the final integral is the sixth-order
amplitude remainder. -/
theorem exp_neg_mul_pi_mul_I1_eq_complexGaussian_secondOrder_add_remainder
    {z : ℂ} (hz : 0 < z.re) :
    Complex.exp (-z) * ((Real.pi : ℂ) * I1 z) =
      (∫ x : ℝ in Ioi 0, Complex.exp (-z * (x : ℂ) ^ 2 / 2)) -
        (3 / 8 : ℂ) * z⁻¹ *
          (∫ x : ℝ in Ioi 0, Complex.exp (-z * (x : ℂ) ^ 2 / 2)) +
        z * (∫ x : ℝ in Ioi 0,
          I1SecondOrderGaussianRemainderKernel z x) := by
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    simp at hz
  let Q : ℝ → ℂ := I1QuadraticGaussianKernel z
  let M₂ : ℝ → ℂ := fun x ↦
    (x : ℂ) ^ 2 * Complex.exp (-z * (x : ℂ) ^ 2 / 2)
  let M₄ : ℝ → ℂ := fun x ↦
    (x : ℂ) ^ 4 * Complex.exp (-z * (x : ℂ) ^ 2 / 2)
  let R : ℝ → ℂ := I1SecondOrderGaussianRemainderKernel z
  have hM₂ : IntegrableOn M₂ (Ioi 0) := by
    simpa only [M₂] using integrableOn_complexGaussianNatMoment hz 2
  have hM₄ : IntegrableOn M₄ (Ioi 0) := by
    simpa only [M₄] using integrableOn_complexGaussianNatMoment hz 4
  have hR : IntegrableOn R (Ioi 0) := by
    simpa only [R] using integrableOn_I1SecondOrderGaussianRemainderKernel hz
  have hdecomp :
      (∫ x : ℝ in Ioi 0, Q x) =
        (∫ x : ℝ in Ioi 0, M₂ x) -
          (1 / 8 : ℂ) * (∫ x : ℝ in Ioi 0, M₄ x) +
          (∫ x : ℝ in Ioi 0, R x) := by
    calc
      (∫ x : ℝ in Ioi 0, Q x) =
          ∫ x : ℝ in Ioi 0, M₂ x - (1 / 8 : ℂ) * M₄ x + R x := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x _
        dsimp [Q, M₂, M₄, R, I1QuadraticGaussianKernel,
          I1SecondOrderGaussianRemainderKernel,
          I1SecondOrderGaussianAmplitudeRemainder]
        push_cast
        ring
      _ = (∫ x : ℝ in Ioi 0, M₂ x) -
          (1 / 8 : ℂ) * (∫ x : ℝ in Ioi 0, M₄ x) +
          (∫ x : ℝ in Ioi 0, R x) := by
        have hscaled : IntegrableOn
            (fun x ↦ (1 / 8 : ℂ) * M₄ x) (Ioi 0) :=
          hM₄.const_mul (1 / 8 : ℂ)
        have hleft : IntegrableOn
            (fun x ↦ M₂ x - (1 / 8 : ℂ) * M₄ x) (Ioi 0) :=
          hM₂.sub hscaled
        rw [integral_add hleft hR, integral_sub hM₂ hscaled,
          integral_const_mul]
  have hsecond :
      (∫ x : ℝ in Ioi 0, M₂ x) =
        z⁻¹ * (∫ x : ℝ in Ioi 0,
          Complex.exp (-z * (x : ℂ) ^ 2 / 2)) := by
    simpa only [M₂] using integral_complexGaussianSecondMoment hz
  have hfourth :
      (∫ x : ℝ in Ioi 0, M₄ x) =
        3 * (z ^ 2)⁻¹ * (∫ x : ℝ in Ioi 0,
          Complex.exp (-z * (x : ℂ) ^ 2 / 2)) := by
    simpa only [M₄] using integral_complexGaussianFourthMoment hz
  rw [exp_neg_mul_pi_mul_I1_eq_z_mul_integral_quadraticKernel_Ioi]
  change z * (∫ x : ℝ in Ioi 0, Q x) = _
  rw [hdecomp, hsecond, hfourth]
  field_simp
  ring

end FastDynamo.ModifiedBessel

end

/-!
## Second-order cancellation in the Ponomarenko order-one product

The exponentially normalized `I₁` and `K₁` factors have opposite
first corrections `−3/(8z)` and `+3/(8z)`.  Their exact
remainders are packaged here and the cancellation algebra in the product is proved; the
uniform estimate on a sector is `PonomarenkoSectorOrderOneProduct`.
-/

noncomputable section

namespace FastDynamo

open Complex MeasureTheory Set Real

/-- The common first correction coefficient `3/(8z)`. -/
def ponomarenkoOrderOneFirstCorrection (z : ℂ) : ℂ :=
  (3 / 8 : ℂ) * z⁻¹

/-- Exact corrected remainder in the exponentially normalized `I₁` factor. -/
def ponomarenkoI1SecondOrderRemainder (z : ℂ) : ℂ :=
  z * ∫ x : ℝ in Ioi 0,
    ModifiedBessel.I1SecondOrderGaussianRemainderKernel z x

/-- Exact corrected remainder in the exponentially normalized `K₁` factor. -/
def ponomarenkoK1SecondOrderRemainder (z : ℂ) : ℂ :=
  ∫ x : ℝ in Ioi 0,
    ModifiedBessel.K1FirstOrderGaussianRemainderKernel z x

/-- Exact `I₁` factor expansion in the notation used by the order-one
Ponomarenko product. -/
theorem ponomarenkoI1Factor_eq_corrected
    {z : ℂ} (hz : 0 < z.re) :
    ponomarenkoI1Factor z =
      (1 - ponomarenkoOrderOneFirstCorrection z) *
          ponomarenkoHalfGaussian z +
        ponomarenkoI1SecondOrderRemainder z := by
  have h :=
    ModifiedBessel.exp_neg_mul_pi_mul_I1_eq_complexGaussian_secondOrder_add_remainder hz
  rw [ponomarenkoI1Factor]
  change (Real.pi : ℂ) * Complex.exp (-z) * ModifiedBessel.I1 z = _
  rw [show (Real.pi : ℂ) * Complex.exp (-z) * ModifiedBessel.I1 z =
      Complex.exp (-z) * ((Real.pi : ℂ) * ModifiedBessel.I1 z) by ring]
  rw [h]
  simp only [ponomarenkoOrderOneFirstCorrection,
    ponomarenkoI1SecondOrderRemainder, ponomarenkoHalfGaussian]
  ring

/-- Exact `K₁` factor expansion with the opposite first correction. -/
theorem ponomarenkoK1Factor_eq_corrected
    {z : ℂ} (hz : 0 < z.re) :
    ponomarenkoK1Factor z =
      (1 + ponomarenkoOrderOneFirstCorrection z) *
          ponomarenkoHalfGaussian z +
        ponomarenkoK1SecondOrderRemainder z := by
  have h :=
    ModifiedBessel.exp_mul_K1_eq_complexGaussian_firstOrder_add_remainder hz
  rw [ponomarenkoK1Factor]
  rw [h]
  simp only [ponomarenkoOrderOneFirstCorrection,
    ponomarenkoK1SecondOrderRemainder, ponomarenkoHalfGaussian]
  ring

/-- Cancellation of the opposite first-order terms.  The only pure
correction left is quadratic, `-c²G²`; all other terms contain one of the
explicit Gaussian remainders. -/
theorem ponomarenko_corrected_factors_product_sub_gaussian_sq
    {z : ℂ} (hz : 0 < z.re) :
    ponomarenkoI1Factor z * ponomarenkoK1Factor z -
        ponomarenkoHalfGaussian z ^ 2 =
      -(ponomarenkoOrderOneFirstCorrection z ^ 2 *
          ponomarenkoHalfGaussian z ^ 2) +
        (1 - ponomarenkoOrderOneFirstCorrection z) *
          ponomarenkoHalfGaussian z * ponomarenkoK1SecondOrderRemainder z +
        (1 + ponomarenkoOrderOneFirstCorrection z) *
          ponomarenkoHalfGaussian z * ponomarenkoI1SecondOrderRemainder z +
        ponomarenkoI1SecondOrderRemainder z *
          ponomarenkoK1SecondOrderRemainder z := by
  rw [ponomarenkoI1Factor_eq_corrected hz,
    ponomarenkoK1Factor_eq_corrected hz]
  ring

end FastDynamo
