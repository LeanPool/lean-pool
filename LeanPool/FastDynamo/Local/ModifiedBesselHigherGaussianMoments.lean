/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Local.ModifiedBesselGaussianMoments

/-!
# Higher half-line Gaussian moments for the Bessel asymptotics

This file extends the Gaussian-moment foundation used by the `I₁` and `K₁`
representations.  In the same kernel normalization

`exp (-z x² / 2)`,

it proves the exact complex fourth moment by integration by parts.  It also
evaluates the real sixth moment and records recurrence and half-Gaussian forms
that can be inserted directly into higher-order remainder estimates.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Real

namespace FastDynamo.ModifiedBessel

/-- Every natural complex moment of the decaying half-line Gaussian is
integrable.  This internal lemma keeps the fourth-moment integration by parts
independent of a special-purpose integrability assumption. -/
theorem integrableOn_complexGaussianNatMoment
    {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    IntegrableOn
      (fun x : ℝ ↦ (x : ℂ) ^ n * Complex.exp (-z * (x : ℂ) ^ 2 / 2))
      (Ioi 0) := by
  have hreal := integrableOn_rpow_mul_exp_neg_mul_sq (half_re_pos hz)
    (s := (n : ℝ)) (by
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith)
  apply Integrable.mono' hreal
  · apply Continuous.aestronglyMeasurable
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 ≤ x := le_of_lt hx
    have hexp : -z * (x : ℂ) ^ 2 / 2 = -(z / 2) * (x : ℂ) ^ 2 := by
      ring
    rw [hexp, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hx0, norm_cexp_neg_mul_sq, Real.rpow_natCast]

/-- A polynomial of any natural degree times the complex half-line Gaussian
tends to zero at `+∞`. -/
private theorem tendsto_natPower_mul_complexGaussian_atTop
    {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    Tendsto
      (fun x : ℝ ↦ (x : ℂ) ^ n * Complex.exp (-z * (x : ℂ) ^ 2 / 2))
      atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hzero :=
    (tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact
      (a := z.re / 2) (by linarith) (n : ℝ)).mono_left atTop_le_cocompact
  convert hzero using 1
  funext x
  have hexp : -z * (x : ℂ) ^ 2 / 2 = -(z / 2) * (x : ℂ) ^ 2 := by
    ring
  rw [hexp, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    norm_cexp_neg_mul_sq, Real.rpow_natCast]
  rw [show (z / 2).re = z.re / 2 by simp]

/-- Derivative of `u ↦ u³ exp(-z u²/2)` on `ℂ`, namely
`3x² exp(-z x²/2) - z x⁴ exp(-z x²/2)`; it is the antiderivative relation linking the second and
fourth half-line Gaussian moments. -/
private lemma hasDerivAt_cube_mul_complexGaussian (z x : ℂ) :
    HasDerivAt
      (fun u : ℂ ↦ u ^ 3 * Complex.exp (-z * u ^ 2 / 2))
      (3 * x ^ 2 * Complex.exp (-z * x ^ 2 / 2) -
        z * x ^ 4 * Complex.exp (-z * x ^ 2 / 2)) x := by
  have hinner := ((hasDerivAt_pow 2 x).const_mul (-z)).div_const (2 : ℂ)
  have hexp : HasDerivAt (fun u : ℂ ↦ Complex.exp (-z * u ^ 2 / 2))
      (-z * x * Complex.exp (-z * x ^ 2 / 2)) x := by
    apply hinner.cexp.congr_deriv
    ring
  have hp := (hasDerivAt_pow 3 x).mul hexp
  apply hp.congr_deriv
  ring

/-- Complex Gaussian integration by parts in the form needed for the first
higher correction: the fourth moment is `3 z⁻¹` times the second moment. -/
theorem integral_complexGaussianFourthMoment_eq_three_inv_mul_second
    {z : ℂ} (hz : 0 < z.re) :
    (∫ x : ℝ in Ioi 0,
        (x : ℂ) ^ 4 * Complex.exp (-z * (x : ℂ) ^ 2 / 2)) =
      3 * z⁻¹ *
        (∫ x : ℝ in Ioi 0,
          (x : ℂ) ^ 2 * Complex.exp (-z * (x : ℂ) ^ 2 / 2)) := by
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    simp at hz
  let m₂ : ℝ → ℂ := fun x ↦
    (x : ℂ) ^ 2 * Complex.exp (-z * (x : ℂ) ^ 2 / 2)
  let m₄ : ℝ → ℂ := fun x ↦
    (x : ℂ) ^ 4 * Complex.exp (-z * (x : ℂ) ^ 2 / 2)
  let d : ℝ → ℂ := fun x ↦ 3 * m₂ x - z * m₄ x
  have hm₂ : IntegrableOn m₂ (Ioi 0) := by
    simpa only [m₂] using integrableOn_complexGaussianNatMoment hz 2
  have hm₄ : IntegrableOn m₄ (Ioi 0) := by
    simpa only [m₄] using integrableOn_complexGaussianNatMoment hz 4
  have hd : IntegrableOn d (Ioi 0) :=
    (hm₂.const_mul (3 : ℂ)).sub (hm₄.const_mul z)
  have hzero : (∫ x in Ioi (0 : ℝ), d x) = 0 := by
    have hftc := integral_Ioi_of_hasDerivAt_of_tendsto'
      (f := fun x : ℝ ↦
        (x : ℂ) ^ 3 * Complex.exp (-z * (x : ℂ) ^ 2 / 2))
      (f' := d) (a := (0 : ℝ)) (m := (0 : ℂ))
      (fun x _ ↦ by
        apply (hasDerivAt_cube_mul_complexGaussian z (x : ℂ)).comp_ofReal.congr_deriv
        dsimp only [d, m₂, m₄]
        ring)
      hd (tendsto_natPower_mul_complexGaussian_atTop hz 3)
    simpa using hftc
  have hrelation :
      3 * (∫ x in Ioi (0 : ℝ), m₂ x) =
        z * (∫ x in Ioi (0 : ℝ), m₄ x) := by
    rw [show (∫ x in Ioi (0 : ℝ), d x) =
        3 * (∫ x in Ioi (0 : ℝ), m₂ x) -
          z * (∫ x in Ioi (0 : ℝ), m₄ x) by
      rw [integral_sub (hm₂.const_mul (3 : ℂ)) (hm₄.const_mul z),
        integral_const_mul, integral_const_mul]] at hzero
    exact sub_eq_zero.mp hzero
  change (∫ x in Ioi (0 : ℝ), m₄ x) =
    3 * z⁻¹ * (∫ x in Ioi (0 : ℝ), m₂ x)
  calc
    (∫ x in Ioi (0 : ℝ), m₄ x) =
        z⁻¹ * (z * (∫ x in Ioi (0 : ℝ), m₄ x)) := by
          field_simp
    _ = z⁻¹ * (3 * (∫ x in Ioi (0 : ℝ), m₂ x)) := by
      rw [← hrelation]
    _ = 3 * z⁻¹ * (∫ x in Ioi (0 : ℝ), m₂ x) := by ring

/-- The exact complex fourth moment reduced all the way to the zeroth
half-line Gaussian. -/
theorem integral_complexGaussianFourthMoment
    {z : ℂ} (hz : 0 < z.re) :
    (∫ x : ℝ in Ioi 0,
        (x : ℂ) ^ 4 * Complex.exp (-z * (x : ℂ) ^ 2 / 2)) =
      3 * (z ^ 2)⁻¹ *
        (∫ x : ℝ in Ioi 0,
          Complex.exp (-z * (x : ℂ) ^ 2 / 2)) := by
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    simp at hz
  rw [integral_complexGaussianFourthMoment_eq_three_inv_mul_second hz,
    integral_complexGaussianSecondMoment hz]
  field_simp

/-- Exact real sixth Gaussian moment on the positive half-line. -/
theorem integral_realGaussianSixthMoment {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ in Ioi 0, x ^ 6 * Real.exp (-a * x ^ 2 / 2)) =
      (a / 2) ^ (-(7 : ℝ) / 2) * (15 * Real.sqrt Real.pi) / 16 := by
  have h := _root_.integral_rpow_mul_exp_neg_mul_rpow
    (p := (2 : ℝ)) (q := (6 : ℝ)) (b := a / 2)
    (by norm_num) (by norm_num) (by linarith)
  have hgamma : Real.Gamma (((6 : ℝ) + 1) / 2) =
      15 * Real.sqrt Real.pi / 8 := by
    convert Real.Gamma_nat_add_half 3 using 1 <;> norm_num
  rw [hgamma] at h
  convert h using 1
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    calc
      x ^ 6 * Real.exp (-a * x ^ 2 / 2) =
          Real.rpow x (6 : ℝ) * Real.exp (-a * x ^ 2 / 2) := by
            exact congrArg (fun y : ℝ ↦ y * Real.exp (-a * x ^ 2 / 2))
              (Real.rpow_natCast x 6).symm
      _ = Real.rpow x (6 : ℝ) * Real.exp (-(a / 2) * x ^ 2) := by
        congr 1
        congr 1
        ring
      _ = x ^ 6 * Real.exp (-(a / 2) * x ^ 2) := by
        exact congrArg (fun q : ℝ ↦ q * Real.exp (-(a / 2) * x ^ 2))
          (Real.rpow_natCast x 6)
    calc
      x ^ 6 * Real.exp (-(a / 2) * x ^ 2) =
          Real.rpow x (6 : ℝ) * Real.exp (-(a / 2) * x ^ 2) := by
            exact congrArg (fun q : ℝ ↦ q * Real.exp (-(a / 2) * x ^ 2))
              (Real.rpow_natCast x 6).symm
      _ = Real.rpow x (6 : ℝ) *
          Real.exp (-(a / 2) * Real.rpow x (2 : ℝ)) := by
        exact congrArg
          (fun q : ℝ ↦ Real.rpow x (6 : ℝ) * Real.exp (-(a / 2) * q))
          (Real.rpow_natCast x 2).symm
  · norm_num
    ring

/-- The sixth real moment is `5/a` times the fourth moment. -/
theorem integral_realGaussianSixthMoment_eq_five_div_mul_fourth
    {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ in Ioi 0, x ^ 6 * Real.exp (-a * x ^ 2 / 2)) =
      (5 / a) *
        (∫ x : ℝ in Ioi 0, x ^ 4 * Real.exp (-a * x ^ 2 / 2)) := by
  rw [integral_realGaussianSixthMoment ha, integral_realGaussianFourthMoment ha]
  have hb : 0 < a / 2 := by linarith
  have hexp : (-(7 : ℝ) / 2) = (-(5 : ℝ) / 2) + (-1 : ℝ) := by ring
  rw [hexp, Real.rpow_add hb, Real.rpow_neg_one]
  field_simp
  ring

/-- The sixth moment in the nonsingular half-Gaussian normalization. -/
theorem integral_realGaussianSixthMoment_eq_fifteen_mul_halfLine_div_cube
    {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ in Ioi 0, x ^ 6 * Real.exp (-a * x ^ 2 / 2)) =
      15 * realGaussianHalfLine a / a ^ 3 := by
  rw [integral_realGaussianSixthMoment_eq_five_div_mul_fourth ha,
    integral_realGaussianFourthMoment_eq_three_mul_halfLine_div_sq ha]
  field_simp
  ring

end FastDynamo.ModifiedBessel
