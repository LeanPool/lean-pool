/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

/-!
# Half-line Gaussian moments for the order-one Bessel estimates

This file packages the exact complex zeroth and second moments of
`exp (-z x^2 / 2)` on the positive half-line, as well as the real second and fourth moments
used to majorize the transformed `I₁` and `K₁` kernels.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Real

namespace FastDynamo.ModifiedBessel

/-- Halving preserves a strictly positive real part. -/
lemma half_re_pos {z : ℂ} (hz : 0 < z.re) : 0 < (z / 2).re := by
  simpa using div_pos hz (by norm_num : (0 : ℝ) < 2)

/-- For `Re z > 0` the second moment integrand `x² exp(-z x²/2)` is integrable on the positive
half-line, dominated by the real Gaussian moment `x² exp(-(Re z) x²/2)`. -/
private theorem integrableOn_complexGaussianSecondMoment {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn
      (fun x : ℝ ↦ (x : ℂ) ^ 2 * Complex.exp (-z * (x : ℂ) ^ 2 / 2))
      (Ioi 0) := by
  have hreal := integrableOn_rpow_mul_exp_neg_mul_sq (half_re_pos hz)
    (s := (2 : ℝ)) (by norm_num)
  apply Integrable.mono' hreal
  · apply Continuous.aestronglyMeasurable
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 ≤ x := le_of_lt hx
    have hexp : -z * (x : ℂ) ^ 2 / 2 = -(z / 2) * (x : ℂ) ^ 2 := by ring
    rw [hexp, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0,
      norm_cexp_neg_mul_sq]
    simp only [Real.rpow_two]
    have hre : (z / 2).re = z.re / 2 := by simp
    rw [hre]

/-- For `Re z > 0` the first moment `x exp(-z x²/2)` tends to `0` as `x → ∞`; this is the
boundary term that vanishes in the integration by parts computing the second moment. -/
private theorem tendsto_mul_complexGaussian_atTop {z : ℂ} (hz : 0 < z.re) :
    Tendsto
      (fun x : ℝ ↦ (x : ℂ) * Complex.exp (-z * (x : ℂ) ^ 2 / 2))
      atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hzero :=
    (tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact
      (a := z.re / 2) (by linarith) (1 : ℝ)).mono_left atTop_le_cocompact
  convert hzero using 1
  funext x
  have hexp : -z * (x : ℂ) ^ 2 / 2 = -(z / 2) * (x : ℂ) ^ 2 := by ring
  rw [hexp, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_cexp_neg_mul_sq]
  simp only [Real.rpow_one]
  have hre : (z / 2).re = z.re / 2 := by simp
  rw [hre]

/-- Derivative of `u ↦ u exp(-z u²/2)` on `ℂ`, namely `exp(-z x²/2) - z x² exp(-z x²/2)`; it is
the antiderivative relation linking the zeroth and second half-line Gaussian moments. -/
private lemma hasDerivAt_mul_complexGaussian (z x : ℂ) :
    HasDerivAt
      (fun u : ℂ ↦ u * Complex.exp (-z * u ^ 2 / 2))
      (Complex.exp (-z * x ^ 2 / 2) - z * x ^ 2 * Complex.exp (-z * x ^ 2 / 2)) x := by
  have hinner := ((hasDerivAt_pow 2 x).const_mul (-z)).div_const (2 : ℂ)
  have hexp : HasDerivAt (fun u : ℂ ↦ Complex.exp (-z * u ^ 2 / 2))
      (-z * x * Complex.exp (-z * x ^ 2 / 2)) x := by
    apply hinner.cexp.congr_deriv
    ring
  have hp := (hasDerivAt_id x).mul hexp
  apply hp.congr_deriv
  simp only [id_eq]
  ring

/-- The exact second complex Gaussian moment, reduced to the zeroth moment without making
any additional branch choice for the square root. -/
theorem integral_complexGaussianSecondMoment {z : ℂ} (hz : 0 < z.re) :
    (∫ x : ℝ in Ioi 0,
        (x : ℂ) ^ 2 * Complex.exp (-z * (x : ℂ) ^ 2 / 2)) =
      z⁻¹ * (∫ x : ℝ in Ioi 0, Complex.exp (-z * (x : ℂ) ^ 2 / 2)) := by
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    simp at hz
  let g : ℝ → ℂ := fun x ↦ Complex.exp (-z * (x : ℂ) ^ 2 / 2)
  let m : ℝ → ℂ := fun x ↦
    (x : ℂ) ^ 2 * Complex.exp (-z * (x : ℂ) ^ 2 / 2)
  let d : ℝ → ℂ := fun x ↦ g x - z * m x
  have hg : IntegrableOn g (Ioi 0) := by
    have h : IntegrableOn
        (fun x : ℝ ↦ Complex.exp (-(z / 2) * (x : ℂ) ^ 2)) (Ioi 0) :=
      (integrable_cexp_neg_mul_sq (half_re_pos hz)).integrableOn
    convert h using 1
    funext x
    dsimp [g]
    congr 1
    ring
  have hm : IntegrableOn m (Ioi 0) := by
    simpa only [m] using integrableOn_complexGaussianSecondMoment hz
  have hd : IntegrableOn d (Ioi 0) := hg.sub (hm.const_mul z)
  have hzero : (∫ x in Ioi (0 : ℝ), d x) = 0 := by
    have hftc := integral_Ioi_of_hasDerivAt_of_tendsto'
      (f := fun x : ℝ ↦ (x : ℂ) * Complex.exp (-z * (x : ℂ) ^ 2 / 2))
      (f' := d) (a := (0 : ℝ)) (m := (0 : ℂ))
      (fun x _ ↦ by
        apply (hasDerivAt_mul_complexGaussian z (x : ℂ)).comp_ofReal.congr_deriv
        dsimp only [d, g, m]
        ring)
      hd (tendsto_mul_complexGaussian_atTop hz)
    simpa using hftc
  have hrelation : (∫ x in Ioi (0 : ℝ), g x) =
      z * (∫ x in Ioi (0 : ℝ), m x) := by
    rw [show (∫ x in Ioi (0 : ℝ), d x) =
        (∫ x in Ioi (0 : ℝ), g x) - z * (∫ x in Ioi (0 : ℝ), m x) by
      rw [integral_sub hg (hm.const_mul z), integral_const_mul]] at hzero
    exact sub_eq_zero.mp hzero
  have hsolve : (∫ x in Ioi (0 : ℝ), m x) =
      z⁻¹ * (∫ x in Ioi (0 : ℝ), g x) := by
    rw [hrelation]
    field_simp
  exact hsolve

/-- Exact real second Gaussian moment on the positive half-line. -/
theorem integral_realGaussianSecondMoment {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ in Ioi 0, x ^ 2 * Real.exp (-a * x ^ 2 / 2)) =
      (a / 2) ^ (-(3 : ℝ) / 2) * Real.sqrt Real.pi / 4 := by
  have h := _root_.integral_rpow_mul_exp_neg_mul_rpow
    (p := (2 : ℝ)) (q := (2 : ℝ)) (b := a / 2)
    (by norm_num) (by norm_num) (by linarith)
  have hgamma : Real.Gamma (((2 : ℝ) + 1) / 2) = Real.sqrt Real.pi / 2 := by
    convert Real.Gamma_nat_add_half 1 using 1 <;> norm_num
  rw [hgamma] at h
  convert h using 1
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    calc
      x ^ 2 * Real.exp (-a * x ^ 2 / 2) =
          Real.rpow x (2 : ℝ) * Real.exp (-a * x ^ 2 / 2) := by
            exact congrArg (fun y : ℝ ↦ y * Real.exp (-a * x ^ 2 / 2))
              (Real.rpow_natCast x 2).symm
      _ = Real.rpow x (2 : ℝ) * Real.exp (-(a / 2) * x ^ 2) := by
        congr 1
        congr 1
        ring
      _ = x ^ 2 * Real.exp (-(a / 2) * x ^ 2) := by
        exact congrArg (fun q : ℝ ↦ q * Real.exp (-(a / 2) * x ^ 2))
          (Real.rpow_natCast x 2)
    calc
      x ^ 2 * Real.exp (-(a / 2) * x ^ 2) =
          Real.rpow x (2 : ℝ) * Real.exp (-(a / 2) * x ^ 2) := by
            exact congrArg (fun q : ℝ ↦ q * Real.exp (-(a / 2) * x ^ 2))
              (Real.rpow_natCast x 2).symm
      _ = Real.rpow x (2 : ℝ) * Real.exp (-(a / 2) * Real.rpow x (2 : ℝ)) := by
        exact congrArg (fun q : ℝ ↦ Real.rpow x (2 : ℝ) * Real.exp (-(a / 2) * q))
          (Real.rpow_natCast x 2).symm
  · norm_num
    ring

/-- Exact real fourth Gaussian moment on the positive half-line. -/
theorem integral_realGaussianFourthMoment {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ in Ioi 0, x ^ 4 * Real.exp (-a * x ^ 2 / 2)) =
      (a / 2) ^ (-(5 : ℝ) / 2) * (3 * Real.sqrt Real.pi) / 8 := by
  have h := _root_.integral_rpow_mul_exp_neg_mul_rpow
    (p := (2 : ℝ)) (q := (4 : ℝ)) (b := a / 2)
    (by norm_num) (by norm_num) (by linarith)
  have hgamma : Real.Gamma (((4 : ℝ) + 1) / 2) = 3 * Real.sqrt Real.pi / 4 := by
    convert Real.Gamma_nat_add_half 2 using 1 <;> norm_num
  rw [hgamma] at h
  convert h using 1
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    calc
      x ^ 4 * Real.exp (-a * x ^ 2 / 2) =
          Real.rpow x (4 : ℝ) * Real.exp (-a * x ^ 2 / 2) := by
            exact congrArg (fun y : ℝ ↦ y * Real.exp (-a * x ^ 2 / 2))
              (Real.rpow_natCast x 4).symm
      _ = Real.rpow x (4 : ℝ) * Real.exp (-(a / 2) * x ^ 2) := by
        congr 1
        congr 1
        ring
      _ = x ^ 4 * Real.exp (-(a / 2) * x ^ 2) := by
        exact congrArg (fun q : ℝ ↦ q * Real.exp (-(a / 2) * x ^ 2))
          (Real.rpow_natCast x 4)
    calc
      x ^ 4 * Real.exp (-(a / 2) * x ^ 2) =
          Real.rpow x (4 : ℝ) * Real.exp (-(a / 2) * x ^ 2) := by
            exact congrArg (fun q : ℝ ↦ q * Real.exp (-(a / 2) * x ^ 2))
              (Real.rpow_natCast x 4).symm
      _ = Real.rpow x (4 : ℝ) * Real.exp (-(a / 2) * Real.rpow x (2 : ℝ)) := by
        exact congrArg (fun q : ℝ ↦ Real.rpow x (4 : ℝ) * Real.exp (-(a / 2) * q))
          (Real.rpow_natCast x 2).symm
  · norm_num
    ring

/-- The real half-Gaussian in the same `a/2` normalization as the complex kernel. -/
noncomputable def realGaussianHalfLine (a : ℝ) : ℝ :=
  ∫ x : ℝ in Ioi 0, Real.exp (-a * x ^ 2 / 2)

/-- The second moment is the half-Gaussian divided by its parameter. -/
theorem integral_realGaussianSecondMoment_eq_halfLine_div
    {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ in Ioi 0, x ^ 2 * Real.exp (-a * x ^ 2 / 2)) =
      realGaussianHalfLine a / a := by
  have hc := integral_complexGaussianSecondMoment (z := (a : ℂ)) (by simpa using ha)
  apply Complex.ofReal_injective
  calc
    ((∫ x : ℝ in Ioi 0, x ^ 2 * Real.exp (-a * x ^ 2 / 2)) : ℝ) =
        ∫ x : ℝ in Ioi 0, ((x ^ 2 * Real.exp (-a * x ^ 2 / 2) : ℝ) : ℂ) := by
          exact (integral_complex_ofReal
            (f := fun x : ℝ ↦ x ^ 2 * Real.exp (-a * x ^ 2 / 2))
            (μ := volume.restrict (Ioi 0))).symm
    _ = ∫ x : ℝ in Ioi 0,
        (x : ℂ) ^ 2 * Complex.exp (-a * (x : ℂ) ^ 2 / 2) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro x hx
          push_cast
          rfl
    _ = (a : ℂ)⁻¹ *
        (∫ x : ℝ in Ioi 0, Complex.exp (-a * (x : ℂ) ^ 2 / 2)) := hc
    _ = (a : ℂ)⁻¹ *
        (∫ x : ℝ in Ioi 0, ((Real.exp (-a * x ^ 2 / 2) : ℝ) : ℂ)) := by
          congr 2
          funext x
          push_cast
          rfl
    _ = ((realGaussianHalfLine a / a : ℝ) : ℂ) := by
      rw [integral_complex_ofReal]
      simp only [realGaussianHalfLine, Complex.ofReal_div]
      ring

/-- Closed form of the real half-Gaussian. -/
theorem realGaussianHalfLine_eq_sqrt {a : ℝ} :
    realGaussianHalfLine a = Real.sqrt (Real.pi / (a / 2)) / 2 := by
  unfold realGaussianHalfLine
  have h := integral_gaussian_Ioi (a / 2)
  convert h using 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  ring_nf

/-- The fourth moment is three times the second moment divided by `a`. -/
theorem integral_realGaussianFourthMoment_eq_three_div_mul_second
    {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ in Ioi 0, x ^ 4 * Real.exp (-a * x ^ 2 / 2)) =
      (3 / a) * (∫ x : ℝ in Ioi 0, x ^ 2 * Real.exp (-a * x ^ 2 / 2)) := by
  rw [integral_realGaussianFourthMoment ha, integral_realGaussianSecondMoment ha]
  have hb : 0 < a / 2 := by linarith
  have hexp : (-(5 : ℝ) / 2) = (-(3 : ℝ) / 2) + (-1 : ℝ) := by ring
  rw [hexp, Real.rpow_add hb, Real.rpow_neg_one]
  field_simp
  ring

/-- The fourth moment in the nonsingular half-Gaussian normalization. -/
theorem integral_realGaussianFourthMoment_eq_three_mul_halfLine_div_sq
    {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ in Ioi 0, x ^ 4 * Real.exp (-a * x ^ 2 / 2)) =
      3 * realGaussianHalfLine a / a ^ 2 := by
  rw [integral_realGaussianFourthMoment_eq_three_div_mul_second ha,
    integral_realGaussianSecondMoment_eq_halfLine_div ha]
  field_simp

end FastDynamo.ModifiedBessel
