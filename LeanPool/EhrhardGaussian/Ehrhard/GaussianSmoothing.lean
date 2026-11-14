/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.GaussianTailMoment

/-! Exponential tilting differentiates translated Gaussian averages of bounded measurable functions
without assuming differentiability of those functions. -/

public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace EhrhardGaussian.Ehrhard

/-- A translated Gaussian density equals the standard density times its exponential tilt. -/
theorem gaussianPDFReal_shift (x m : ℝ) :
    gaussianPDFReal m 1 x =
      Real.exp (-m ^ 2 / 2) * (gaussianPDFReal 0 1 x * Real.exp (m * x)) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  have hexp : -(x - m) ^ 2 / 2 = -m ^ 2 / 2 + (-x ^ 2 / 2 + m * x) := by ring
  rw [hexp, Real.exp_add, Real.exp_add]
  ring

/-- Change of Gaussian mean expressed as an exponential tilt. -/
theorem integral_add_gaussianReal_eq_tilt {f : ℝ → ℝ} (hf : Measurable f) (m : ℝ) :
    ∫ x, f (x + m) ∂gaussianReal 0 1 =
      Real.exp (-m ^ 2 / 2) * ∫ x, f x * Real.exp (m * x) ∂gaussianReal 0 1 := by
  have hmap : (gaussianReal 0 1).map (fun x => x + m) = gaussianReal m 1 := by
    rw [gaussianReal_map_add_const, zero_add]
  rw [← integral_map (by fun_prop) hf.aestronglyMeasurable, hmap,
    integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0),
    integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0),
    ← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    dsimp only
    rw [gaussianPDFReal_shift, smul_eq_mul, smul_eq_mul]
    ring

/-- Derivative at zero obtained by differentiating the MGF of the finite
measure with density `f` relative to the standard Gaussian. -/
theorem hasDerivAt_integral_add_gaussianReal_zero {f : ℝ → ℝ} (hf : Measurable f)
    (hbound : ∀ x, f x ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun m => ∫ x, f (x + m) ∂gaussianReal 0 1)
      (∫ x, x * f x ∂gaussianReal 0 1) 0 := by
  let ν := (gaussianReal 0 1).withDensity (fun x => ENNReal.ofReal (f x))
  have hν : ν ≤ gaussianReal 0 1 := by
    calc
      ν ≤ (gaussianReal 0 1).withDensity (fun _ => 1) :=
        withDensity_mono (ae_of_all _ fun x => by
          exact (ENNReal.ofReal_le_ofReal (hbound x).2).trans_eq ENNReal.ofReal_one)
      _ = gaussianReal 0 1 := withDensity_one
  have hexp : integrableExpSet id ν = univ := by
    apply eq_univ_of_forall
    intro t
    exact (integrable_exp_mul_gaussianReal t).mono_measure hν
  have hmgf := hasDerivAt_mgf (X := id) (μ := ν) (t := 0) (by rw [hexp]; simp only [interior_univ,
    mem_univ])
  have hint (g : ℝ → ℝ) : ∫ x, g x ∂ν = ∫ x, f x * g x ∂gaussianReal 0 1 := by
    rw [integral_withDensity_eq_integral_toReal_smul (hf.ennreal_ofReal)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    congr 1
    ext x
    rw [ENNReal.toReal_ofReal (hbound x).1, smul_eq_mul]
  have hfun : mgf id ν = fun m => ∫ x, f x * Real.exp (m * x) ∂gaussianReal 0 1 := by
    funext m
    exact hint _
  rw [hfun, hint] at hmgf
  simp only [id_eq, zero_mul, Real.exp_zero, mul_one] at hmgf
  have he := (((hasDerivAt_id' (0 : ℝ)).pow 2).neg.div_const 2).exp
  simp only [Pi.neg_apply, Pi.pow_apply] at he
  norm_num at he
  have hprod := he.mul hmgf
  simp only [zero_mul, neg_zero, zero_pow (by decide : 2 ≠ 0), zero_div,
    Real.exp_zero, zero_add, one_mul] at hprod
  convert hprod using 1
  · funext m
    exact integral_add_gaussianReal_eq_tilt hf m
  · apply integral_congr_ae
    exact ae_of_all _ fun x => mul_comm x (f x)

/-- Differentiation of scalar Gaussian convolution for bounded measurable inputs. -/
theorem hasDerivAt_integral_add_gaussianReal {f : ℝ → ℝ} (hf : Measurable f)
    (hbound : ∀ x, f x ∈ Icc (0 : ℝ) 1) (m : ℝ) :
    HasDerivAt (fun y => ∫ x, f (x + y) ∂gaussianReal 0 1)
      (∫ x, x * f (x + m) ∂gaussianReal 0 1) m := by
  have hg := hasDerivAt_integral_add_gaussianReal_zero (hf.comp (measurable_id.add_const m))
    (fun x => hbound (x + m))
  have hg' : HasDerivAt (fun h => ∫ x, f (x + h + m) ∂gaussianReal 0 1)
      (∫ x, x * f (x + m) ∂gaussianReal 0 1) ((fun y : ℝ => y - m) m) := by
    simpa only [sub_self, Function.comp_def, id_eq] using hg
  have hcomp := hg'.comp (h := fun y : ℝ => y - m) m ((hasDerivAt_id' m).sub_const m)
  simp only [mul_one] at hcomp
  convert hcomp using 1
  funext y
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    dsimp only [Function.comp_def]
    congr 1
    ring

/-- Direct differentiation at every positive smoothing scale, with arbitrary
real attenuation. This is the Gaussian convolution derivative, rather than a
derivative of the measurable input. -/
theorem hasDerivAt_gaussian_smoothing {f : ℝ → ℝ} (hf : Measurable f)
    (hbound : ∀ x, f x ∈ Icc (0 : ℝ) 1) {a : ℝ} (ha : a ≠ 0) (r x : ℝ) :
    HasDerivAt (fun y => ∫ z, f (r * y + a * z) ∂gaussianReal 0 1)
      ((r / a) * ∫ z, z * f (r * x + a * z) ∂gaussianReal 0 1) x := by
  have hg := hasDerivAt_integral_add_gaussianReal (hf.comp (measurable_const.mul measurable_id))
    (fun z => hbound (a * z)) ((r / a) * x)
  have hcomp := hg.comp (h := fun y : ℝ => (r / a) * y) x ((hasDerivAt_id' x).const_mul (r / a))
  change HasDerivAt (fun y => ∫ z, f (a * (z + (r / a) * y)) ∂gaussianReal 0 1)
    ((∫ z, z * f (a * (z + (r / a) * x)) ∂gaussianReal 0 1) * ((r / a) * 1)) x at hcomp
  have harg (y z : ℝ) : a * (z + (r / a) * y) = r * y + a * z := by
    field_simp
    ring
  simp_rw [harg, mul_one] at hcomp
  convert hcomp using 1
  exact mul_comm _ _

/-- The direct scalar smoothing gradient estimate in half-line coordinates.
For the OU kernel substitute `r = exp (-t)` and
`a = σ * sqrt (1 - exp (-2*t))`. The mean selects the half-line threshold;
its density is the usual Gaussian profile `I(q)`. -/
theorem abs_deriv_gaussian_smoothing_le {f : ℝ → ℝ} (hf : Measurable f)
    (hbound : ∀ x, f x ∈ Icc (0 : ℝ) 1) {a : ℝ} (ha : a ≠ 0) (r x c : ℝ)
    (hmean : ∫ z, f (r * x + a * z) ∂gaussianReal 0 1 =
      ((gaussianReal 0 1) (Ioi c)).toReal) :
    |deriv (fun y => ∫ z, f (r * y + a * z) ∂gaussianReal 0 1) x| ≤
      |r / a| * gaussianPDFReal 0 1 c := by
  rw [(hasDerivAt_gaussian_smoothing hf hbound ha r x).deriv, abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg (r / a))
  exact abs_integral_mul_le_gaussianPDFReal
    (hf.comp (measurable_const.add (measurable_const.mul measurable_id)))
    (fun z => hbound (r * x + a * z)) c hmean

/-- The exact OU gradient coefficient from NP16, with the Gaussian profile
written as the density at the upper-half-line threshold of the smoothed mean. -/
theorem abs_deriv_ou_smoothing_le {f : ℝ → ℝ} (hf : Measurable f)
    (hbound : ∀ x, f x ∈ Icc (0 : ℝ) 1) {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t)
    (x c : ℝ)
    (hmean : ∫ z, f (Real.exp (-t) * x +
        (σ * Real.sqrt (1 - Real.exp (-2 * t))) * z) ∂gaussianReal 0 1 =
      ((gaussianReal 0 1) (Ioi c)).toReal) :
    |deriv (fun y => ∫ z, f (Real.exp (-t) * y +
      (σ * Real.sqrt (1 - Real.exp (-2 * t))) * z) ∂gaussianReal 0 1) x| ≤
      gaussianPDFReal 0 1 c / (σ * Real.sqrt (Real.exp (2 * t) - 1)) := by
  have hr : 0 < 1 - Real.exp (-2 * t) := by
    apply sub_pos.mpr
    apply Real.exp_lt_one_iff.mpr
    linarith only [ht]
  have ha : 0 < σ * Real.sqrt (1 - Real.exp (-2 * t)) :=
    mul_pos hσ (Real.sqrt_pos.mpr hr)
  have hexp : Real.exp (-2 * t) * Real.exp (2 * t) = 1 := by
    rw [← Real.exp_add, show -2 * t + 2 * t = 0 by ring, Real.exp_zero]
  have hrad : 1 - Real.exp (-2 * t) =
      Real.exp (-2 * t) * (Real.exp (2 * t) - 1) := by
    rw [mul_sub, mul_one, hexp]
  have hsqrt : Real.sqrt (1 - Real.exp (-2 * t)) =
      Real.exp (-t) * Real.sqrt (Real.exp (2 * t) - 1) := by
    rw [hrad, Real.sqrt_mul (Real.exp_pos _).le, ← Real.exp_half]
    congr 2
    ring
  have hcoef : Real.exp (-t) / (σ * Real.sqrt (1 - Real.exp (-2 * t))) =
      1 / (σ * Real.sqrt (Real.exp (2 * t) - 1)) := by
    rw [hsqrt, show σ * (Real.exp (-t) * Real.sqrt (Real.exp (2 * t) - 1)) =
      Real.exp (-t) * (σ * Real.sqrt (Real.exp (2 * t) - 1)) by ring,
      div_mul_eq_div_div, div_self (Real.exp_ne_zero _)]
  have h := abs_deriv_gaussian_smoothing_le hf hbound ha.ne' (Real.exp (-t)) x c hmean
  rw [abs_of_pos (div_pos (Real.exp_pos _) ha), hcoef] at h
  simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using h

end EhrhardGaussian.Ehrhard
