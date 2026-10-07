/-
Copyright (c) 2026 rainrzk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: rainrzk
-/
module

public import LeanPool.PolylogIntegrals.Lemmas.LogSinSq
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# A radial argument on the upper half disk

Mathlib has no Cauchy theorem for a half disk. This file replaces it, for the one function A015
needs, by differentiating the half-circle mean with respect to the radius.

Let `F` be holomorphic on the open unit disk, and put `H(ρ) = ∫₀^π F(ρ e^{iθ}) dθ`. Differentiating
under the integral sign and then integrating in `θ`,
`H'(ρ) = ∫₀^π F'(ρ e^{iθ}) e^{iθ} dθ = (F(ρ e^{iπ}) - F(ρ)) / (iρ) = i (F(ρ) - F(-ρ))/ρ`.

For `F(z) = log³((1+z)/2)` the values `F(±ρ)` are real, so `h(ρ) = Im H(ρ)` has derivative
`(F(ρ) - F(-ρ))/ρ` and `h(0) = 0`. At `ρ = 1` the function `h` is continuous by dominated
convergence: for `ρ > 1/2`, `|1 + ρ e^{iθ}| ≥ ρ sin θ` bounds `|Re log((1 + ρ e^{iθ})/2)|` by
`log 4 + |log sin θ|`, and `Im log³ = 3 Re² Im - Im³` only involves the square of the real part,
which is integrable.

## Main results

* `LeanPolyLog.Radial.hasDerivAt_integral`: for `F` with a continuous derivative `F'` on the unit
  disk and `|ρ| < 1`, `d/dρ ∫₀^π F(ρ e^{iθ}) dθ = ∫₀^π F'(ρ e^{iθ}) e^{iθ} dθ`.
* `LeanPolyLog.Radial.integral_deriv_mul_exp`: for `0 < |ρ| < 1`,
  `∫₀^π F'(ρ e^{iθ}) e^{iθ} dθ = i (F(ρ) - F(-ρ))/ρ`.
* `LeanPolyLog.Radial.integral_im_logCube`:
  `∫₀^π Im log³((1 + e^{iθ})/2) dθ = ∫₀¹ (log³((1+r)/2) - log³((1-r)/2))/r dr`, provided the
  integrand on the right is integrable on `[0, 1]`.
* `LeanPolyLog.Radial.im_logCube_exp_two_mul`: for `|x| < π/2`,
  `Im log³((1 + e^{2ix})/2) = 3x log² cos x - x³`, because `log((1 + e^{2ix})/2) = log cos x + ix`.
-/

open Real MeasureTheory Set Filter Topology

namespace LeanPolyLog.Radial

/-- `‖ρ e^{iθ}‖ = |ρ|`. -/
public theorem norm_ofReal_mul_exp (ρ θ : ℝ) : ‖(ρ : ℂ) * Complex.exp (θ * Complex.I)‖ = |ρ| := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-! ### Holomorphic functions on the unit disk -/

section General

variable {F F' : ℂ → ℂ}

/-- Differentiation under the integral sign: if `F` has the continuous derivative `F'` on the unit
disk, then for `|ρ₀| < 1`, `d/dρ ∫₀^π F(ρ e^{iθ}) dθ = ∫₀^π F'(ρ₀ e^{iθ}) e^{iθ} dθ` at `ρ₀`. -/
public theorem hasDerivAt_integral (hF : ∀ z ∈ Metric.ball (0 : ℂ) 1, HasDerivAt F (F' z) z)
    (hF' : ContinuousOn F' (Metric.ball 0 1)) {ρ₀ : ℝ} (hρ₀ : |ρ₀| < 1) :
    HasDerivAt (fun ρ : ℝ ↦ ∫ θ in (0 : ℝ)..π, F (ρ * Complex.exp (θ * Complex.I)))
      (∫ θ in (0 : ℝ)..π, F' (ρ₀ * Complex.exp (θ * Complex.I)) * Complex.exp (θ * Complex.I))
      ρ₀ := by
  set r := (1 + |ρ₀|) / 2 with hr
  have hr1 : r < 1 := by rw [hr]; linarith
  have hρr : |ρ₀| < r := by rw [hr]; linarith
  have hball : ∀ ρ ∈ Ioo (-r) r, ∀ θ : ℝ,
      (ρ : ℂ) * Complex.exp (θ * Complex.I) ∈ Metric.closedBall (0 : ℂ) r := by
    intro ρ hρ θ
    rw [mem_closedBall_zero_iff, norm_ofReal_mul_exp, abs_le]
    exact ⟨hρ.1.le, hρ.2.le⟩
  have hsub : Metric.closedBall (0 : ℂ) r ⊆ Metric.ball 0 1 := Metric.closedBall_subset_ball hr1
  obtain ⟨M, hM⟩ :=
    (isCompact_closedBall (0 : ℂ) r).exists_bound_of_continuousOn (hF'.mono hsub)
  have hFc : ContinuousOn F (Metric.ball 0 1) := fun z hz ↦
    (hF z hz).continuousAt.continuousWithinAt
  have hρ₀' : ρ₀ ∈ Ioo (-r) r := abs_lt.1 hρr
  have hs : Ioo (-r) r ∈ 𝓝 ρ₀ := Ioo_mem_nhds hρ₀'.1 hρ₀'.2
  have hcont : ∀ ρ ∈ Ioo (-r) r,
      Continuous fun θ : ℝ ↦ F (ρ * Complex.exp (θ * Complex.I)) := fun ρ hρ ↦
    hFc.comp_continuous (by fun_prop) fun θ ↦ hsub (hball ρ hρ θ)
  have hcont' : Continuous fun θ : ℝ ↦
      F' (ρ₀ * Complex.exp (θ * Complex.I)) * Complex.exp (θ * Complex.I) :=
    (hF'.comp_continuous (by fun_prop) fun θ ↦ hsub (hball ρ₀ hρ₀' θ)).mul (by fun_prop)
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (ρ θ : ℝ) ↦ F (ρ * Complex.exp (θ * Complex.I)))
    (F' := fun (ρ θ : ℝ) ↦ F' (ρ * Complex.exp (θ * Complex.I)) * Complex.exp (θ * Complex.I))
    (bound := fun _ ↦ M) hs ?_ ((hcont ρ₀ hρ₀').intervalIntegrable 0 π)
    hcont'.aestronglyMeasurable ?_ intervalIntegrable_const ?_).2
  · filter_upwards [hs] with ρ hρ
    exact (hcont ρ hρ).aestronglyMeasurable
  · refine ae_of_all _ fun θ _ ρ hρ ↦ ?_
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    exact hM _ (hball ρ hρ θ)
  · refine ae_of_all _ fun θ _ ρ hρ ↦ ?_
    have hlin : HasDerivAt (fun ρ : ℝ ↦ (ρ : ℂ) * Complex.exp (θ * Complex.I))
        (Complex.exp (θ * Complex.I)) ρ := by
      simpa using (hasDerivAt_id' ρ).ofReal_comp.mul_const (Complex.exp (θ * Complex.I))
    exact (hF _ (hsub (hball ρ hρ θ))).comp ρ hlin

/-- The fundamental theorem of calculus in `θ`: for `0 < |ρ| < 1`,
`∫₀^π F'(ρ e^{iθ}) e^{iθ} dθ = (F(-ρ) - F(ρ))/(iρ) = i (F(ρ) - F(-ρ))/ρ`. -/
public theorem integral_deriv_mul_exp (hF : ∀ z ∈ Metric.ball (0 : ℂ) 1, HasDerivAt F (F' z) z)
    (hF' : ContinuousOn F' (Metric.ball 0 1)) {ρ : ℝ} (hρ0 : ρ ≠ 0) (hρ : |ρ| < 1) :
    ∫ θ in (0 : ℝ)..π, F' (ρ * Complex.exp (θ * Complex.I)) * Complex.exp (θ * Complex.I) =
      Complex.I * (F ρ - F (-ρ)) / ρ := by
  have hball : ∀ θ : ℝ, (ρ : ℂ) * Complex.exp (θ * Complex.I) ∈ Metric.ball (0 : ℂ) 1 := by
    intro θ
    rw [mem_ball_zero_iff, norm_ofReal_mul_exp]
    exact hρ
  have hderiv : ∀ θ : ℝ, HasDerivAt (fun θ : ℝ ↦ F (ρ * Complex.exp (θ * Complex.I)))
      (ρ * Complex.I * (F' (ρ * Complex.exp (θ * Complex.I)) * Complex.exp (θ * Complex.I))) θ := by
    intro θ
    have h1 : HasDerivAt (fun θ : ℝ ↦ (θ : ℂ) * Complex.I) Complex.I θ := by
      simpa using (hasDerivAt_id' θ).ofReal_comp.mul_const Complex.I
    exact ((hF _ (hball θ)).comp θ (h1.cexp.const_mul (ρ : ℂ))).congr_deriv (by ring)
  have hcont : Continuous fun θ : ℝ ↦
      ρ * Complex.I * (F' (ρ * Complex.exp (θ * Complex.I)) * Complex.exp (θ * Complex.I)) :=
    continuous_const.mul ((hF'.comp_continuous (by fun_prop) hball).mul (by fun_prop))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ ↦ hderiv θ)
    (hcont.intervalIntegrable 0 π)
  rw [intervalIntegral.integral_const_mul, Complex.exp_pi_mul_I, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, mul_one, mul_neg_one] at hFTC
  set X := ∫ θ in (0 : ℝ)..π, F' (ρ * Complex.exp (θ * Complex.I)) * Complex.exp (θ * Complex.I)
  have hρ' : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hρ0
  rw [eq_div_iff hρ']
  linear_combination (-Complex.I) * hFTC + ρ * X * Complex.I_sq

end General

/-! ### The function `log³((1+z)/2)` -/

/-- For `‖z‖ < 1`, `1 + z ≠ 0`. -/
public theorem one_add_ne_zero {z : ℂ} (hz : ‖z‖ < 1) : 1 + z ≠ 0 := by
  intro h
  have : z = -1 := by linear_combination h
  rw [this, norm_neg, norm_one] at hz
  exact lt_irrefl _ hz

/-- For `‖z‖ < 1`, `(1 + z)/2` lies in the slit plane: its real part is positive. -/
public theorem mem_slitPlane {z : ℂ} (hz : ‖z‖ < 1) : (1 + z) / 2 ∈ Complex.slitPlane := by
  refine Complex.mem_slitPlane_iff.2 (Or.inl ?_)
  have h := Complex.abs_re_le_norm z
  rw [Complex.div_ofNat_re, Complex.add_re, Complex.one_re]
  have := neg_abs_le z.re
  linarith

/-- `d/dz log³((1+z)/2) = 3 log²((1+z)/2)/(1+z)` on the unit disk. -/
public theorem hasDerivAt_logCube {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    HasDerivAt (fun z ↦ Complex.log ((1 + z) / 2) ^ 3)
      (3 * Complex.log ((1 + z) / 2) ^ 2 / (1 + z)) z := by
  have hz' : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
  have h1 : HasDerivAt (fun z : ℂ ↦ (1 + z) / 2) (1 / 2) z :=
    ((hasDerivAt_id' z).const_add 1).div_const 2
  refine ((h1.clog (mem_slitPlane hz')).pow 3).congr_deriv ?_
  have h1z := one_add_ne_zero hz'
  field_simp
  norm_num

/-- `3 log²((1+z)/2)/(1+z)` is continuous on the unit disk. -/
public theorem continuousOn_deriv_logCube :
    ContinuousOn (fun z : ℂ ↦ 3 * Complex.log ((1 + z) / 2) ^ 2 / (1 + z))
      (Metric.ball 0 1) := by
  intro z hz
  have hz' : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
  exact ((continuousAt_const.mul ((((continuousAt_const.add continuousAt_id).div_const 2).clog
    (mem_slitPlane hz')).pow 2)).div (continuousAt_const.add continuousAt_id)
    (one_add_ne_zero hz')).continuousWithinAt

/-- On real arguments `ρ ≥ -1`, `log³((1+ρ)/2)` is the real `log³((1+ρ)/2)`. -/
public theorem logCube_ofReal {ρ : ℝ} (hρ : -1 ≤ ρ) :
    Complex.log ((1 + (ρ : ℂ)) / 2) ^ 3 = ((Real.log ((1 + ρ) / 2) ^ 3 : ℝ) : ℂ) := by
  have h : (1 + (ρ : ℂ)) / 2 = (((1 + ρ) / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [h, ← Complex.ofReal_log (by linarith), ← Complex.ofReal_pow]

/-- On real arguments `ρ ≤ 1`, `log³((1-ρ)/2)` is the real `log³((1-ρ)/2)`. -/
public theorem logCube_neg_ofReal {ρ : ℝ} (hρ : ρ ≤ 1) :
    Complex.log ((1 + -(ρ : ℂ)) / 2) ^ 3 = ((Real.log ((1 - ρ) / 2) ^ 3 : ℝ) : ℂ) := by
  have h : (1 + -(ρ : ℂ)) / 2 = (((1 - ρ) / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [h, ← Complex.ofReal_log (by linarith), ← Complex.ofReal_pow]

/-! ### The half-circle mean of `Im log³((1+z)/2)` -/

/-- `halfCircleIm ρ = ∫₀^π Im log³((1 + ρ e^{iθ})/2) dθ`. -/
@[expose] public noncomputable def halfCircleIm (ρ : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..π, (Complex.log ((1 + ρ * Complex.exp (θ * Complex.I)) / 2) ^ 3).im

/-- For `|ρ| < 1`, `θ ↦ log³((1 + ρ e^{iθ})/2)` is continuous. -/
public theorem continuous_logCube_mul_exp {ρ : ℝ} (hρ : |ρ| < 1) :
    Continuous fun θ : ℝ ↦ Complex.log ((1 + ρ * Complex.exp (θ * Complex.I)) / 2) ^ 3 := by
  have hFc : ContinuousOn (fun z : ℂ ↦ Complex.log ((1 + z) / 2) ^ 3) (Metric.ball 0 1) :=
    fun z hz ↦ (hasDerivAt_logCube hz).continuousAt.continuousWithinAt
  exact hFc.comp_continuous (by fun_prop) fun θ ↦ by
    rw [mem_ball_zero_iff, norm_ofReal_mul_exp]
    exact hρ

/-- Near any `|ρ| < 1`, `halfCircleIm` is the imaginary part of `∫₀^π log³((1 + ρ e^{iθ})/2) dθ`. -/
public theorem halfCircleIm_eventuallyEq {ρ₀ : ℝ} (hρ₀ : |ρ₀| < 1) :
    halfCircleIm =ᶠ[𝓝 ρ₀] fun ρ : ℝ ↦
      (∫ θ in (0 : ℝ)..π, Complex.log ((1 + ρ * Complex.exp (θ * Complex.I)) / 2) ^ 3).im := by
  have hρ₀' := abs_lt.1 hρ₀
  filter_upwards [Ioo_mem_nhds hρ₀'.1 hρ₀'.2] with ρ hρ
  exact intervalIntegral.intervalIntegral_im
    ((continuous_logCube_mul_exp (abs_lt.2 hρ)).intervalIntegrable 0 π)

/-- The complex half-circle mean has a derivative at every `|ρ| < 1`. -/
public theorem hasDerivAt_integral_logCube {ρ : ℝ} (hρ : |ρ| < 1) :
    HasDerivAt (fun ρ : ℝ ↦
        ∫ θ in (0 : ℝ)..π, Complex.log ((1 + ρ * Complex.exp (θ * Complex.I)) / 2) ^ 3)
      (∫ θ in (0 : ℝ)..π, 3 * Complex.log ((1 + ρ * Complex.exp (θ * Complex.I)) / 2) ^ 2
        / (1 + ρ * Complex.exp (θ * Complex.I)) * Complex.exp (θ * Complex.I)) ρ :=
  hasDerivAt_integral (F := fun z ↦ Complex.log ((1 + z) / 2) ^ 3)
    (fun _ hz ↦ hasDerivAt_logCube hz) continuousOn_deriv_logCube hρ

/-- For `0 < ρ < 1`, `halfCircleIm' ρ = (log³((1+ρ)/2) - log³((1-ρ)/2))/ρ`. -/
public theorem hasDerivAt_halfCircleIm {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    HasDerivAt halfCircleIm ((Real.log ((1 + ρ) / 2) ^ 3 - Real.log ((1 - ρ) / 2) ^ 3) / ρ) ρ := by
  have hρ : |ρ| < 1 := by rw [abs_of_pos hρ0]; exact hρ1
  have hH := hasDerivAt_integral_logCube hρ
  rw [integral_deriv_mul_exp (F := fun z ↦ Complex.log ((1 + z) / 2) ^ 3)
    (fun _ hz ↦ hasDerivAt_logCube hz) continuousOn_deriv_logCube hρ0.ne' hρ] at hH
  have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt ρ hH
  simp only [Function.comp_def, Complex.imCLM_apply] at him
  refine (him.congr_of_eventuallyEq (halfCircleIm_eventuallyEq hρ)).congr_deriv ?_
  rw [logCube_ofReal (by linarith), logCube_neg_ofReal hρ1.le]
  have e : Complex.I * ((Real.log ((1 + ρ) / 2) ^ 3 : ℝ) - (Real.log ((1 - ρ) / 2) ^ 3 : ℝ) : ℂ)
      / (ρ : ℂ) = (((Real.log ((1 + ρ) / 2) ^ 3 - Real.log ((1 - ρ) / 2) ^ 3) / ρ : ℝ) : ℂ)
        * Complex.I := by
    push_cast
    ring
  rw [e, Complex.mul_I_im, Complex.ofReal_re]

/-- `halfCircleIm 0 = 0`: the integrand is `Im log³(1/2) = 0`. -/
public theorem halfCircleIm_zero : halfCircleIm 0 = 0 := by
  have h := logCube_ofReal (ρ := 0) (by norm_num)
  unfold halfCircleIm
  simp only [Complex.ofReal_zero, zero_mul] at h ⊢
  rw [h, Complex.ofReal_im, intervalIntegral.integral_zero]

/-- The imaginary part of `z³` is `3 (Re z)² Im z - (Im z)³`. -/
public theorem im_pow_three (z : ℂ) : (z ^ 3).im = 3 * z.re ^ 2 * z.im - z.im ^ 3 := by
  simp only [pow_succ, pow_zero, one_mul, Complex.mul_im, Complex.mul_re]
  ring

/-- For `1/2 < ρ ≤ 1` and `0 < θ < π`:
`|Im log³((1 + ρ e^{iθ})/2)| ≤ 3π (2 log² 4 + 2 log² sin θ) + π³`. -/
public theorem abs_im_logCube_le {ρ θ : ℝ} (hρ : ρ ∈ Ioc (1 / 2 : ℝ) 1) (hθ : θ ∈ Ioo 0 π) :
    ‖(Complex.log ((1 + ρ * Complex.exp (θ * Complex.I)) / 2) ^ 3).im‖ ≤
      3 * π * (2 * Real.log 4 ^ 2 + 2 * Real.log (Real.sin θ) ^ 2) + π ^ 3 := by
  set u := (1 + ρ * Complex.exp (θ * Complex.I)) / 2 with hu
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have huim : u.im = ρ * Real.sin θ / 2 := by
    rw [hu, Complex.div_ofNat_im, Complex.add_im, Complex.one_im, Complex.im_ofReal_mul,
      Complex.exp_ofReal_mul_I_im, zero_add]
  have hlow : Real.sin θ / 4 ≤ ‖u‖ := by
    have h := Complex.abs_im_le_norm u
    rw [huim, abs_of_pos (by have := hρ.1; positivity)] at h
    nlinarith [hρ.1]
  have hup : ‖u‖ ≤ 1 := by
    rw [hu, norm_div, Complex.norm_ofNat, div_le_one (by norm_num)]
    calc ‖1 + (ρ : ℂ) * Complex.exp (θ * Complex.I)‖
        ≤ ‖(1 : ℂ)‖ + ‖(ρ : ℂ) * Complex.exp (θ * Complex.I)‖ := norm_add_le _ _
      _ = 1 + |ρ| := by rw [norm_one, norm_ofReal_mul_exp]
      _ ≤ 2 := by rw [abs_of_pos (by linarith [hρ.1])]; linarith [hρ.2]
  have hpos : 0 < ‖u‖ := lt_of_lt_of_le (by positivity) hlow
  set a := (Complex.log u).re with ha
  set b := (Complex.log u).im with hb
  have ha' : a = Real.log ‖u‖ := Complex.log_re u
  have hb' : |b| ≤ π := by rw [hb, Complex.log_im]; exact Complex.abs_arg_le_pi u
  have ha0 : a ≤ 0 := by rw [ha']; exact Real.log_nonpos hpos.le hup
  have ha1 : Real.log (Real.sin θ) - Real.log 4 ≤ a := by
    rw [ha', ← Real.log_div hs.ne' (by norm_num)]
    exact Real.log_le_log (by positivity) hlow
  have ha2 : a ^ 2 ≤ 2 * Real.log 4 ^ 2 + 2 * Real.log (Real.sin θ) ^ 2 := by
    nlinarith [sq_nonneg (Real.log (Real.sin θ) + Real.log 4)]
  rw [im_pow_three, Real.norm_eq_abs]
  have hb2 : |b| ^ 3 ≤ π ^ 3 := pow_le_pow_left₀ (abs_nonneg b) hb' 3
  calc |3 * a ^ 2 * b - b ^ 3| ≤ 3 * a ^ 2 * |b| + |b| ^ 3 := by
        refine (abs_sub _ _).trans ?_
        rw [abs_mul, abs_pow, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3), abs_pow,
          sq_abs]
    _ ≤ 3 * (2 * Real.log 4 ^ 2 + 2 * Real.log (Real.sin θ) ^ 2) * π + π ^ 3 := by
        gcongr
    _ = 3 * π * (2 * Real.log 4 ^ 2 + 2 * Real.log (Real.sin θ) ^ 2) + π ^ 3 := by ring

/-- Almost every `θ` differs from `π`. -/
public theorem ae_ne_pi : ∀ᵐ θ : ℝ ∂volume, θ ≠ π := by
  rw [ae_iff]
  simp

/-- `halfCircleIm` is continuous at `1` within `[0, 1]`, by dominated convergence. -/
public theorem continuousWithinAt_halfCircleIm_one :
    ContinuousWithinAt halfCircleIm (Icc 0 1) 1 := by
  have hev : ∀ᶠ ρ in 𝓝[Icc 0 1] (1 : ℝ), ρ ∈ Ioc (1 / 2 : ℝ) 1 := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds
      (by norm_num : (1 / 2 : ℝ) < 1))] with ρ hρ h2
    exact ⟨h2, hρ.2⟩
  refine intervalIntegral.continuousWithinAt_of_dominated_interval
    (bound := fun θ ↦ 3 * π * (2 * Real.log 4 ^ 2 + 2 * Real.log (Real.sin θ) ^ 2) + π ^ 3)
    ?_ ?_ ?_ ?_
  · refine Eventually.of_forall fun ρ ↦ ?_
    have : Measurable fun θ : ℝ ↦
        (Complex.log ((1 + ρ * Complex.exp (θ * Complex.I)) / 2) ^ 3).im :=
      Complex.measurable_im.comp ((Complex.measurable_log.comp
        (by fun_prop : Continuous fun θ : ℝ ↦
          (1 + ρ * Complex.exp (θ * Complex.I)) / 2).measurable).pow_const 3)
    exact this.aestronglyMeasurable
  · filter_upwards [hev] with ρ hρ
    filter_upwards [ae_ne_pi] with θ hθπ hθ
    rw [uIoc_of_le pi_pos.le] at hθ
    exact abs_im_logCube_le hρ ⟨hθ.1, lt_of_le_of_ne hθ.2 hθπ⟩
  · exact ((intervalIntegrable_const.add
      (LogSinSq.intervalIntegrable_log_sin_sq_zero_pi.const_mul 2)).const_mul (3 * π)).add
      intervalIntegrable_const
  · filter_upwards [ae_ne_pi] with θ hθπ hθ
    rw [uIoc_of_le pi_pos.le] at hθ
    have hθ' : θ < π := lt_of_le_of_ne hθ.2 hθπ
    have hslit : (1 + ((1 : ℝ) : ℂ) * Complex.exp (θ * Complex.I)) / 2 ∈ Complex.slitPlane := by
      refine Complex.mem_slitPlane_iff.2 (Or.inl ?_)
      rw [Complex.div_ofNat_re, Complex.add_re, Complex.one_re, Complex.re_ofReal_mul,
        Complex.exp_ofReal_mul_I_re]
      have := Real.cos_lt_cos_of_nonneg_of_le_pi hθ.1.le le_rfl hθ'
      rw [Real.cos_pi] at this
      linarith
    have hc : ContinuousAt (fun ρ : ℝ ↦ (1 + ρ * Complex.exp (θ * Complex.I)) / 2) 1 := by
      fun_prop
    exact (Complex.continuous_im.continuousAt.comp ((hc.clog hslit).pow 3)).continuousWithinAt

/-- `halfCircleIm` is continuous on `[0, 1]`. -/
public theorem continuousOn_halfCircleIm : ContinuousOn halfCircleIm (Icc 0 1) := by
  intro ρ hρ
  rcases eq_or_lt_of_le hρ.2 with rfl | hρ1
  · exact continuousWithinAt_halfCircleIm_one
  · have hρ' : |ρ| < 1 := abs_lt.2 ⟨by linarith [hρ.1], hρ1⟩
    have hc := (Complex.continuous_im.continuousAt.comp
      (hasDerivAt_integral_logCube hρ').continuousAt)
    exact (hc.congr (halfCircleIm_eventuallyEq hρ').symm).continuousWithinAt

/-- The radial identity: if `(log³((1+r)/2) - log³((1-r)/2))/r` is integrable on `[0, 1]`, then
`∫₀^π Im log³((1 + e^{iθ})/2) dθ = ∫₀¹ (log³((1+r)/2) - log³((1-r)/2))/r dr`. -/
public theorem integral_im_logCube
    (hint : IntervalIntegrable
      (fun r ↦ (Real.log ((1 + r) / 2) ^ 3 - Real.log ((1 - r) / 2) ^ 3) / r) volume 0 1) :
    ∫ θ in (0 : ℝ)..π, (Complex.log ((1 + Complex.exp (θ * Complex.I)) / 2) ^ 3).im =
      ∫ r in (0 : ℝ)..1, (Real.log ((1 + r) / 2) ^ 3 - Real.log ((1 - r) / 2) ^ 3) / r := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one continuousOn_halfCircleIm
    (fun ρ hρ ↦ hasDerivAt_halfCircleIm hρ.1 hρ.2) hint, halfCircleIm_zero, sub_zero]
  unfold halfCircleIm
  simp only [Complex.ofReal_one, one_mul]

/-! ### The boundary values -/

/-- For `|x| < π/2`: `log((1 + e^{2ix})/2) = log cos x + ix`, since
`(1 + e^{2ix})/2 = cos x · e^{ix}` with `cos x > 0`. -/
public theorem log_one_add_exp_two_mul {x : ℝ} (hx : |x| < π / 2) :
    Complex.log ((1 + Complex.exp (((2 * x : ℝ) : ℂ) * Complex.I)) / 2) =
      (Real.log (Real.cos x) : ℂ) + x * Complex.I := by
  have hx' := abs_lt.1 hx
  have hc : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨hx'.1, hx'.2⟩
  have e : (1 + Complex.exp (((2 * x : ℝ) : ℂ) * Complex.I)) / 2 =
      Complex.exp ((Real.log (Real.cos x) : ℂ) + x * Complex.I) := by
    rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hc, Complex.ofReal_cos]
    have h2 := Complex.two_cos (x : ℂ)
    have h3 : Complex.exp (((2 * x : ℝ) : ℂ) * Complex.I) =
        Complex.exp (x * Complex.I) * Complex.exp (x * Complex.I) := by
      rw [← Complex.exp_add]
      push_cast
      ring_nf
    have h4 : Complex.exp (-(x : ℂ) * Complex.I) * Complex.exp (x * Complex.I) = 1 := by
      rw [← Complex.exp_add, show -(x : ℂ) * Complex.I + x * Complex.I = 0 by ring,
        Complex.exp_zero]
    linear_combination (1 / 2 : ℂ) * h3 - (Complex.exp (x * Complex.I) / 2) * h2
      - (1 / 2 : ℂ) * h4
  rw [e, Complex.log_exp]
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_zero, mul_one, zero_add, add_zero]
    linarith [pi_pos]
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_zero, mul_one, zero_add, add_zero]
    linarith [pi_pos]

/-- For `|x| < π/2`: `Im log³((1 + e^{2ix})/2) = 3x log² cos x - x³`. -/
public theorem im_logCube_exp_two_mul {x : ℝ} (hx : |x| < π / 2) :
    (Complex.log ((1 + Complex.exp (((2 * x : ℝ) : ℂ) * Complex.I)) / 2) ^ 3).im =
      3 * x * Real.log (Real.cos x) ^ 2 - x ^ 3 := by
  rw [log_one_add_exp_two_mul hx, im_pow_three]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, Complex.add_im, Complex.mul_im]
  ring

end LeanPolyLog.Radial
