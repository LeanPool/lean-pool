/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Local.ModifiedBesselHigherGaussianMoments
public import LeanPool.FastDynamo.Local.ModifiedBesselKGaussian

/-!
# Second-order Gaussian expansion for `K₁`

For the exact `K₁` Gaussian amplitude

`(1 + x²/2) / sqrt (1 + x²/4)`,

this file proves global Taylor remainders after the quadratic and quartic
corrections.  The resulting integral estimates give both the corrected
`O(G/(re z)²)` approximation needed for the Ponomarenko product and a
stronger quartic-corrected `O(G/(re z)³)` expansion.
-/

@[expose] public section

noncomputable section

open Complex MeasureTheory Set Filter Real

namespace FastDynamo.ModifiedBessel

/-- Remainder after the quadratic correction `1 + 3x²/8`. -/
def K1FirstOrderGaussianAmplitudeRemainder (x : ℝ) : ℝ :=
  K1GaussianAmplitude x - 1 - 3 * x ^ 2 / 8

/-- Gaussian kernel carrying the quadratic-corrected amplitude remainder. -/
def K1FirstOrderGaussianRemainderKernel (z : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (-z * (x : ℂ) ^ 2 / 2) *
    (K1FirstOrderGaussianAmplitudeRemainder x : ℂ)

/-- Global quadratic-correction remainder for the `K₁` Gaussian amplitude.
The coefficient `5/128` is the exact quartic Taylor coefficient at zero. -/
theorem abs_K1FirstOrderGaussianAmplitudeRemainder_le (x : ℝ) :
    |K1FirstOrderGaussianAmplitudeRemainder x| ≤ 5 * x ^ 4 / 128 := by
  let s : ℝ := Real.sqrt (1 + x ^ 2 / 4)
  have hspos : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hsge : 1 ≤ s := by
    dsimp [s]
    rw [Real.one_le_sqrt]
    nlinarith [sq_nonneg x]
  have hsSq : s ^ 2 = 1 + x ^ 2 / 4 := by
    exact Real.sq_sqrt (by positivity)
  have hxSq : x ^ 2 = 4 * (s ^ 2 - 1) := by
    nlinarith [hsSq]
  have hxFourth : x ^ 4 = 16 * (s - 1) ^ 2 * (s + 1) ^ 2 := by
    rw [show x ^ 4 = (x ^ 2) ^ 2 by ring, hxSq]
    ring
  have hremainder : K1FirstOrderGaussianAmplitudeRemainder x =
      -((s - 1) ^ 2 * (3 * s + 2) / (2 * s)) := by
    rw [K1FirstOrderGaussianAmplitudeRemainder, K1GaussianAmplitude]
    change (1 + x ^ 2 / 2) / s - 1 - 3 * x ^ 2 / 8 = _
    rw [hxSq]
    field_simp [hspos.ne']
    ring
  have hnonpos : K1FirstOrderGaussianAmplitudeRemainder x ≤ 0 := by
    rw [hremainder]
    exact neg_nonpos.mpr (by positivity)
  rw [abs_of_nonpos hnonpos, hremainder, neg_neg]
  have hcoeff : 4 * (3 * s + 2) ≤ 5 * s * (s + 1) ^ 2 := by
    have hfactor : 0 ≤ (s - 1) * (5 * s ^ 2 + 15 * s + 8) := by
      positivity
    nlinarith
  have hscale : 0 ≤ (s - 1) ^ 2 / (8 * s) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hcoeff hscale
  rw [hxFourth]
  calc
    (s - 1) ^ 2 * (3 * s + 2) / (2 * s) =
        ((s - 1) ^ 2 / (8 * s)) * (4 * (3 * s + 2)) := by
      field_simp [hspos.ne']
      ring
    _ ≤ ((s - 1) ^ 2 / (8 * s)) * (5 * s * (s + 1) ^ 2) := hmul
    _ = 5 * (16 * (s - 1) ^ 2 * (s + 1) ^ 2) / 128 := by
      field_simp [hspos.ne']
      ring

/-- Pointwise kernel estimate after the quadratic correction. -/
theorem norm_K1FirstOrderGaussianRemainderKernel_le (z : ℂ) (x : ℝ) :
    ‖K1FirstOrderGaussianRemainderKernel z x‖ ≤
      Real.exp (-z.re * x ^ 2 / 2) * (5 * x ^ 4 / 128) := by
  rw [K1FirstOrderGaussianRemainderKernel, norm_mul, Complex.norm_exp]
  have hre : (-z * (x : ℂ) ^ 2 / 2).re = -z.re * x ^ 2 / 2 := by
    simp [Complex.mul_re, pow_two]
  rw [hre, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left
    (abs_K1FirstOrderGaussianAmplitudeRemainder_le x)
    (Real.exp_pos _).le

/-- For `a > 0` the fourth-order Gaussian majorant `exp(-a x²/2) · 5x⁴/128` is integrable on the
positive half-line; it dominates the quadratic-corrected `K₁` amplitude remainder. -/
private theorem integrableOn_K1FirstOrderGaussianMajorant
    {a : ℝ} (ha : 0 < a) :
    IntegrableOn
      (fun x : ℝ ↦ Real.exp (-a * x ^ 2 / 2) * (5 * x ^ 4 / 128))
      (Ioi 0) := by
  have h := (integrableOn_rpow_mul_exp_neg_mul_sq
    (show 0 < a / 2 by positivity) (s := (4 : ℝ)) (by norm_num)).const_mul
      (5 / 128 : ℝ)
  have heq :
      (fun x : ℝ ↦ Real.exp (-a * x ^ 2 / 2) * (5 * x ^ 4 / 128)) =
        (fun x : ℝ ↦ (5 / 128 : ℝ) *
          (x ^ (4 : ℝ) * Real.exp (-(a / 2) * x ^ 2))) := by
    funext x
    rw [← Real.rpow_natCast x 4]
    have hexp : -a * x ^ 2 / 2 = -(a / 2) * x ^ 2 := by ring
    rw [hexp]
    ring_nf
  rw [heq]
  exact h

/-- For `Re z > 0` the quadratic-corrected `K₁` Gaussian remainder kernel is integrable on the
positive half-line. -/
private theorem integrableOn_K1FirstOrderGaussianRemainderKernel
    {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (K1FirstOrderGaussianRemainderKernel z) (Ioi 0) := by
  have hmajor := integrableOn_K1FirstOrderGaussianMajorant hz
  apply Integrable.mono hmajor
  · apply Continuous.aestronglyMeasurable
    unfold K1FirstOrderGaussianRemainderKernel
      K1FirstOrderGaussianAmplitudeRemainder K1GaussianAmplitude
    have hden : ∀ x : ℝ, Real.sqrt (1 + x ^ 2 / 4) ≠ 0 := fun x ↦ by
      exact (Real.sqrt_pos.2 (by positivity)).ne'
    fun_prop
  · filter_upwards with x
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (by positivity))]
    exact norm_K1FirstOrderGaussianRemainderKernel_le z x

/-- The evaluated real fourth-moment majorant. -/
theorem integral_K1FirstOrderGaussianMajorant
    {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ in Ioi 0,
        Real.exp (-a * x ^ 2 / 2) * (5 * x ^ 4 / 128)) =
      15 * realGaussianHalfLine a / (128 * a ^ 2) := by
  calc
    (∫ x : ℝ in Ioi 0,
        Real.exp (-a * x ^ 2 / 2) * (5 * x ^ 4 / 128)) =
        (5 / 128 : ℝ) *
          (∫ x : ℝ in Ioi 0, x ^ 4 * Real.exp (-a * x ^ 2 / 2)) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      ring
    _ = 15 * realGaussianHalfLine a / (128 * a ^ 2) := by
      rw [integral_realGaussianFourthMoment_eq_three_mul_halfLine_div_sq ha]
      ring

/-- Integrated quadratic-corrected remainder. -/
theorem norm_integral_K1FirstOrderGaussianRemainderKernel_le_halfLine
    {z : ℂ} (hz : 0 < z.re) :
    ‖∫ x : ℝ in Ioi 0, K1FirstOrderGaussianRemainderKernel z x‖ ≤
      15 * realGaussianHalfLine z.re / (128 * z.re ^ 2) := by
  calc
    ‖∫ x : ℝ in Ioi 0, K1FirstOrderGaussianRemainderKernel z x‖ ≤
        ∫ x : ℝ in Ioi 0,
          Real.exp (-z.re * x ^ 2 / 2) * (5 * x ^ 4 / 128) := by
      apply norm_integral_le_of_norm_le
        (integrableOn_K1FirstOrderGaussianMajorant hz)
      filter_upwards with x
      exact norm_K1FirstOrderGaussianRemainderKernel_le z x
    _ = 15 * realGaussianHalfLine z.re / (128 * z.re ^ 2) :=
      integral_K1FirstOrderGaussianMajorant hz

/-- Removing the exterior exponential from the established `K₁` Gaussian
representation leaves exactly the normalized Gaussian kernel integral. -/
theorem exp_mul_K1_eq_integral_normalizedGaussianKernel
    {z : ℂ} (hz : 0 < z.re) :
    Complex.exp z * K1 z =
      ∫ x : ℝ in Ioi 0, K1NormalizedGaussianKernel z x := by
  rw [K1_eq_exp_neg_mul_integral_normalizedGaussianKernel hz,
    ← mul_assoc, ← Complex.exp_add]
  simp

/-- Exact quadratic-corrected expansion.  With
`G(z) = ∫₀∞ exp (-z x²/2) dx`, this is
`e^z K₁(z) = G(z) + (3/(8z))G(z) + ∫ R₁`. -/
theorem exp_mul_K1_eq_complexGaussian_firstOrder_add_remainder
    {z : ℂ} (hz : 0 < z.re) :
    Complex.exp z * K1 z =
      (∫ x : ℝ in Ioi 0, Complex.exp (-z * (x : ℂ) ^ 2 / 2)) +
        (3 / 8 : ℂ) * z⁻¹ *
          (∫ x : ℝ in Ioi 0, Complex.exp (-z * (x : ℂ) ^ 2 / 2)) +
        (∫ x : ℝ in Ioi 0, K1FirstOrderGaussianRemainderKernel z x) := by
  let Q : ℝ → ℂ := K1NormalizedGaussianKernel z
  let G : ℝ → ℂ := fun x ↦ Complex.exp (-z * (x : ℂ) ^ 2 / 2)
  let M₂ : ℝ → ℂ := fun x ↦
    (x : ℂ) ^ 2 * Complex.exp (-z * (x : ℂ) ^ 2 / 2)
  let R₁ : ℝ → ℂ := K1FirstOrderGaussianRemainderKernel z
  have hG : IntegrableOn G (Ioi 0) := by
    simpa only [G, pow_zero, one_mul] using
      integrableOn_complexGaussianNatMoment hz 0
  have hM₂ : IntegrableOn M₂ (Ioi 0) := by
    simpa only [M₂] using integrableOn_complexGaussianNatMoment hz 2
  have hR₁ : IntegrableOn R₁ (Ioi 0) := by
    simpa only [R₁] using integrableOn_K1FirstOrderGaussianRemainderKernel hz
  have hscaled : IntegrableOn (fun x ↦ (3 / 8 : ℂ) * M₂ x) (Ioi 0) :=
    hM₂.const_mul (3 / 8 : ℂ)
  have hbase : IntegrableOn (fun x ↦ G x + (3 / 8 : ℂ) * M₂ x) (Ioi 0) :=
    hG.add hscaled
  have hdecomp :
      (∫ x : ℝ in Ioi 0, Q x) =
        (∫ x : ℝ in Ioi 0, G x) +
          (3 / 8 : ℂ) * (∫ x : ℝ in Ioi 0, M₂ x) +
          (∫ x : ℝ in Ioi 0, R₁ x) := by
    calc
      (∫ x : ℝ in Ioi 0, Q x) =
          ∫ x : ℝ in Ioi 0, G x + (3 / 8 : ℂ) * M₂ x + R₁ x := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x _
        dsimp [Q, G, M₂, R₁, K1NormalizedGaussianKernel,
          K1FirstOrderGaussianRemainderKernel,
          K1FirstOrderGaussianAmplitudeRemainder]
        push_cast
        ring
      _ = (∫ x : ℝ in Ioi 0, G x) +
          (3 / 8 : ℂ) * (∫ x : ℝ in Ioi 0, M₂ x) +
          (∫ x : ℝ in Ioi 0, R₁ x) := by
        rw [integral_add hbase hR₁,
          integral_add hG hscaled, integral_const_mul]
  have hsecond :
      (∫ x : ℝ in Ioi 0, M₂ x) =
        z⁻¹ * (∫ x : ℝ in Ioi 0, G x) := by
    simpa only [M₂, G] using integral_complexGaussianSecondMoment hz
  rw [exp_mul_K1_eq_integral_normalizedGaussianKernel hz]
  change (∫ x : ℝ in Ioi 0, Q x) = _
  rw [hdecomp, hsecond]
  dsimp only [G, R₁]
  ring

end FastDynamo.ModifiedBessel
