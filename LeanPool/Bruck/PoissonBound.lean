/-
Copyright (c) 2026 Fang, Hu, Li, Tang, and Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pengcheng Fang, Tao Hu, Yanyang Li, Quanyu Tang, Haiqi Zhang
-/

module

public import LeanPool.Bruck.WVMaximumModulus
public import Mathlib.Analysis.Complex.ValueDistribution.CharacteristicFunction
import Mathlib.Tactic.Lemma

-- Adapted from QuanyuTang/three-im-one-cm-formalization (Apache-2.0),
-- commit 2874a773c15da244347c6a6ccdc1a30e9bdd2a26, RequestProject/ThreeIM/PoissonBound.lean.

/-!
# The maximum-modulus bound `log⁺ M(r, h) ≤ (R + r)/(R - r) T(R, h)`

For an entire function `h`, `1 ≤ r < R` and `|z| = r`, we prove
`log⁺ |h(z)| ≤ (R + r)/(R - r) · T(R, h)`.

The proof replaces the Poisson–Jensen formula by Jensen's formula composed with a disk
automorphism: with `ρ = r/R` and `z = r e^{iα}`, the function
`g(ζ) = h(R e^{iα} (ζ + ρ)/(1 + ρ ζ))` is holomorphic near the closed unit disk and
`g(0) = h(z)`, so Jensen's inequality gives `log |h(z)| ≤ (1/2π) ∫ log |g(e^{iθ})| dθ`.
On the unit circle, `(e^{iθ} + ρ)/(1 + ρ e^{iθ}) = e^{iψ(θ)}` with the explicit increasing lift
`ψ(θ) = θ - 2 arctan(ρ sin θ / (1 + ρ cos θ))`, whose derivative
`ψ'(θ) = (1 - ρ²)/(1 + 2ρ cos θ + ρ²)` is at least `(1 - ρ)/(1 + ρ)`.  The substitution
`t = ψ(θ)` then bounds the average of `log⁺ |g|` by `(1 + ρ)/(1 - ρ) · m(R, h)`.
-/

public section

open Real MeasureTheory Set Filter

namespace Bruck

/-- For an entire function, the pole-counting term is zero, so the Nevanlinna
characteristic is the circular average of the positive logarithm of the norm. -/
theorem characteristic_eq_circleAverage_posLog {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (r : ℝ) : ValueDistribution.characteristic f ⊤ r =
      circleAverage (fun z => log⁺ ‖f z‖) 0 r := by
  have ha : AnalyticOnNhd ℂ f univ := fun z _ => hf.analyticAt z
  have hdiv := MeromorphicOn.AnalyticOnNhd.divisor_nonneg ha
  simp [ValueDistribution.characteristic, ValueDistribution.proximity_top,
    ValueDistribution.logCounting_top, negPart_eq_zero.mpr hdiv]

/-- Jensen's inequality: for `g` holomorphic near the closed unit disk with `g(0) ≠ 0`,
`log |g(0)| ≤ (1/2π) ∫ log |g(e^{iθ})| dθ`. -/
private lemma log_norm_le_circleAverage {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (Metric.closedBall 0 1))
    (hg0 : g 0 ≠ 0) : log ‖g 0‖ ≤ circleAverage (fun z => log ‖g z‖) 0 1 := by
  have hg' : AnalyticOnNhd ℂ g (Metric.closedBall 0 |1|) := by rw [abs_one]; exact hg
  have hm : MeromorphicOn g (Metric.closedBall 0 |1|) := hg'.meromorphicOn
  rw [MeromorphicOn.circleAverage_log_norm one_ne_zero hm,
    (hg 0 (by simp)).meromorphicTrailingCoeffAt_of_ne_zero hg0, log_one, mul_zero, add_zero]
  have hnn : 0 ≤ ∑ᶠ u, (MeromorphicOn.divisor g (Metric.closedBall 0 |1|) u : ℝ) *
      log (1 * ‖0 - u‖⁻¹) := by
    apply finsum_nonneg
    intro u
    rcases eq_or_ne u 0 with rfl | h0
    · simp
    by_cases hu : u ∈ Metric.closedBall (0 : ℂ) |1|
    · apply mul_nonneg
      · exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hg' u
      · apply Real.log_nonneg
        rw [one_mul, zero_sub, norm_neg]
        rw [Metric.mem_closedBall, dist_zero_right, abs_one] at hu
        exact one_le_inv₀ (norm_pos_iff.2 h0) |>.2 hu
    · simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]
  linarith

/-- The explicit lift of the boundary map of the disk automorphism `ζ ↦ (ζ + ρ)/(1 + ρ ζ)`. -/
private noncomputable def mobLift (ρ θ : ℝ) : ℝ := θ - 2 * arctan (ρ * sin θ / (1 + ρ * cos θ))

private lemma polar_of_re_pos {x y : ℝ} (hx : 0 < x) :
    (x : ℂ) + y * Complex.I =
      ((x * √(1 + (y / x) ^ 2) : ℝ) : ℂ) * Complex.exp (arctan (y / x) * Complex.I) := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_arctan, Real.sin_arctan]
  apply Complex.ext <;> simp <;> field_simp

private lemma one_add_mul_cos_pos {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (θ : ℝ) :
    0 < 1 + ρ * cos θ := by
  have lower := mul_le_mul_of_nonneg_left (neg_one_le_cos θ) hρ0
  linarith only [lower, hρ1]

private lemma mobius_denominator_pos {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (θ : ℝ) :
    0 < 1 + 2 * ρ * cos θ + ρ ^ 2 := by
  have lower := mul_le_mul_of_nonneg_left (neg_one_le_cos θ) (show 0 ≤ 2 * ρ by positivity)
  nlinarith only [lower, pow_pos (sub_pos.mpr hρ1) 2]

private lemma mobLift_spec {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (θ : ℝ) :
    (Complex.exp (θ * Complex.I) + ρ) / (1 + ρ * Complex.exp (θ * Complex.I)) =
      Complex.exp (mobLift ρ θ * Complex.I) := by
  have hx : 0 < 1 + ρ * cos θ := one_add_mul_cos_pos hρ0 hρ1 θ
  set x := 1 + ρ * cos θ
  set y := ρ * sin θ
  set β := arctan (y / x)
  set c := ((x * √(1 + (y / x) ^ 2) : ℝ) : ℂ)
  have hc : c ≠ 0 := by
    have : 0 < x * √(1 + (y / x) ^ 2) := mul_pos hx (Real.sqrt_pos.2 (by positivity))
    exact Complex.ofReal_ne_zero.2 this.ne'
  have h1 : 1 + ρ * Complex.exp (θ * Complex.I) = c * Complex.exp (β * Complex.I) := by
    rw [← polar_of_re_pos hx, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp only [x, y]; push_cast; ring
  have h2 : 1 + ρ * Complex.exp (-(θ * Complex.I)) = c * Complex.exp (-(β * Complex.I)) := by
    have := polar_of_re_pos (y := -y) hx
    rw [neg_div, Real.arctan_neg, neg_sq] at this
    rw [show -(β * Complex.I) = ((-β : ℝ) : ℂ) * Complex.I by push_cast; ring]
    rw [show -(θ * Complex.I) = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring]
    rw [← this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp only [x, y, Real.cos_neg, Real.sin_neg]; push_cast; ring
  have h3 : Complex.exp (θ * Complex.I) + ρ =
      Complex.exp (θ * Complex.I) * (1 + ρ * Complex.exp (-(θ * Complex.I))) := by
    rw [mul_add, mul_one, ← mul_assoc, mul_comm _ (ρ : ℂ), mul_assoc, ← Complex.exp_add]
    simp
  rw [h3, h2, h1, show mobLift ρ θ = θ - 2 * β from rfl, mul_div_assoc,
    mul_div_mul_left _ _ hc, ← Complex.exp_sub, ← Complex.exp_add]
  congr 1
  simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

private lemma hasDerivAt_mobLift {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (θ : ℝ) :
    HasDerivAt (mobLift ρ) ((1 - ρ ^ 2) / (1 + 2 * ρ * cos θ + ρ ^ 2)) θ := by
  have hc : 0 < 1 + ρ * cos θ := one_add_mul_cos_pos hρ0 hρ1 θ
  have h1 : HasDerivAt (fun θ => ρ * sin θ / (1 + ρ * cos θ))
      ((ρ * cos θ * (1 + ρ * cos θ) - ρ * sin θ * (ρ * -sin θ)) / (1 + ρ * cos θ) ^ 2) θ := by
    apply HasDerivAt.div ((hasDerivAt_sin θ).const_mul ρ)
      (((hasDerivAt_cos θ).const_mul ρ).const_add 1) hc.ne'
  have h2 := (h1.arctan).const_mul 2
  have h3 := (hasDerivAt_id θ).sub h2
  unfold mobLift
  convert h3 using 1
  · ext t
    simp
  · have hs : sin θ ^ 2 = 1 - cos θ ^ 2 := by linarith [sin_sq_add_cos_sq θ]
    have hd := mobius_denominator_pos hρ0 hρ1 θ
    have he : 1 + (ρ * sin θ / (1 + ρ * cos θ)) ^ 2 =
        (1 + 2 * ρ * cos θ + ρ ^ 2) / (1 + ρ * cos θ) ^ 2 := by
      field_simp; rw [hs]; ring
    have hN : ρ * cos θ * (1 + ρ * cos θ) - ρ * sin θ * (ρ * -sin θ) = ρ * cos θ + ρ ^ 2 := by
      have : ρ * sin θ * (ρ * -sin θ) = -(ρ ^ 2 * sin θ ^ 2) := by ring
      rw [this, hs]; ring
    rw [he, hN, one_div_div]
    have hc2 : (1 + ρ * cos θ) ^ 2 ≠ 0 := by positivity
    rw [div_mul_div_comm, mul_comm ((1 + ρ * cos θ) ^ 2), mul_div_mul_right _ _ hc2,
      eq_sub_iff_add_eq, mul_div_assoc', ← add_div, div_eq_one_iff_eq hd.ne']
    ring

private lemma mobLift_zero (ρ : ℝ) : mobLift ρ 0 = 0 := by simp [mobLift]

private lemma mobLift_two_pi (ρ : ℝ) : mobLift ρ (2 * π) = 2 * π := by simp [mobLift]

/-- Change of variables along the lift: for continuous `F ≥ 0`,
`∫₀^{2π} F(ψ(θ)) dθ ≤ (1 + ρ)/(1 - ρ) ∫₀^{2π} F(t) dt`. -/
private lemma integral_comp_mobLift_le {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {F : ℝ → ℝ}
    (hF : Continuous F) (hF0 : ∀ t, 0 ≤ F t) :
    ∫ θ in (0)..(2 * π), F (mobLift ρ θ) ≤ (1 + ρ) / (1 - ρ) * ∫ t in (0)..(2 * π), F t := by
  set d : ℝ → ℝ := fun θ => (1 - ρ ^ 2) / (1 + 2 * ρ * cos θ + ρ ^ 2) with hd
  have hD := mobius_denominator_pos hρ0 hρ1
  have hdc : Continuous d := by
    apply continuous_const.div (by fun_prop) (fun θ => (hD θ).ne')
  have hψc : Continuous (mobLift ρ) :=
    continuous_iff_continuousAt.2 fun θ => (hasDerivAt_mobLift hρ0 hρ1 θ).continuousAt
  have hsub := intervalIntegral.integral_comp_mul_deriv (a := 0) (b := 2 * π) (f := mobLift ρ)
    (f' := d) (g := F) (fun x _ => hasDerivAt_mobLift hρ0 hρ1 x) hdc.continuousOn hF
  rw [mobLift_zero, mobLift_two_pi] at hsub
  rw [← hsub, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on two_pi_pos.le
  · exact (hF.comp hψc).intervalIntegrable _ _
  · exact (continuous_const.mul ((hF.comp hψc).mul hdc)).intervalIntegrable _ _
  · intro θ _
    have h1 : 1 ≤ (1 + ρ) / (1 - ρ) * d θ := by
      simp only [hd]
      rw [div_mul_div_comm, le_div_iff₀ (mul_pos (by linarith) (hD θ))]
      have product_nonneg :=
        mul_nonneg (mul_nonneg (sub_nonneg.2 hρ1.le) hρ0) (sub_nonneg.2 (cos_le_one θ))
      nlinarith only [product_nonneg]
    simpa only [Function.comp_apply, one_mul, mul_assoc, mul_comm (d θ)] using
      mul_le_mul_of_nonneg_right h1 (hF0 (mobLift ρ θ))

/-- Pointwise characteristic bound: for an entire `h` and `1 ≤ r < R`,
`log⁺ |h(z)| ≤ (R + r)/(R - r) · T(R, h)` on `|z| = r`. -/
theorem entire_posLog_le {h : ℂ → ℂ} (hh : Differentiable ℂ h) {r R : ℝ} (hr : 1 ≤ r)
    (hrR : r < R) {z : ℂ} (hz : ‖z‖ = r) :
    Real.posLog ‖h z‖ ≤ (R + r) / (R - r) * ValueDistribution.characteristic h ⊤ R := by
  have hR1 : 1 ≤ R := hr.trans hrR.le
  have hR0 : 0 < R := by linarith
  have hT0 : 0 ≤ ValueDistribution.characteristic h ⊤ R :=
    ValueDistribution.characteristic_nonneg hR1
  rcases le_or_gt ‖h z‖ 1 with hle | hgt
  · have : Real.posLog ‖h z‖ = 0 := by
      rw [posLog_apply, max_eq_left (Real.log_nonpos (norm_nonneg _) hle)]
    rw [this]; positivity
  rw [posLog_eq_log (by rw [abs_norm]; exact hgt.le)]
  set ρ := r / R with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := (div_lt_one hR0).2 hrR
  set α := z.arg
  set u := Complex.exp (α * Complex.I)
  set G : ℝ → ℝ := fun t => log⁺ ‖h (circleMap 0 R t)‖ with hG
  have hGc : Continuous G :=
    continuous_posLog.comp ((hh.continuous.comp (continuous_circleMap 0 R)).norm)
  have hG0 : ∀ t, 0 ≤ G t := fun t => posLog_nonneg
  set g : ℂ → ℂ := fun ζ => h (R * u * ((ζ + ρ) / (1 + ρ * ζ))) with hg
  have hden : ∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, 1 + ρ * ζ ≠ 0 := by
    intro ζ hζ h0
    have : ‖(ρ : ℂ) * ζ‖ = 1 := by
      rw [show (ρ : ℂ) * ζ = -1 by linear_combination h0]; simp
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ0] at this
    have := mul_le_mul_of_nonneg_left (show ‖ζ‖ ≤ 1 by simpa using hζ) hρ0
    nlinarith
  have hgan : AnalyticOnNhd ℂ g (Metric.closedBall 0 1) := by
    intro ζ hζ
    apply (hh.analyticAt _).comp
    apply analyticAt_const.mul
    exact (analyticAt_id.add analyticAt_const).div
      (analyticAt_const.add (analyticAt_const.mul analyticAt_id)) (hden ζ hζ)
  have hg0 : g 0 = h z := by
    simp only [hg, zero_add, mul_zero, add_zero, div_one]
    congr 1
    have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR0.ne'
    conv_rhs => rw [← Complex.norm_mul_exp_arg_mul_I z, hz]
    simp only [hρ, u, α]
    push_cast; field_simp
  have hgbd : ∀ θ, g (circleMap 0 1 θ) = h (circleMap 0 R (α + mobLift ρ θ)) := by
    intro θ
    simp only [hg, circleMap, zero_add, Complex.ofReal_one, one_mul]
    rw [mobLift_spec hρ0 hρ1 θ]
    congr 1
    simp only [u, Complex.ofReal_add, add_mul, Complex.exp_add]; ring
  have hjen := log_norm_le_circleAverage hgan (by
    rw [hg0]; intro h0; rw [h0, norm_zero] at hgt; linarith)
  rw [hg0] at hjen
  have hint1 : IntervalIntegrable (fun θ => log ‖g (circleMap 0 1 θ)‖) volume 0 (2 * π) :=
    MeromorphicOn.circleIntegrable_log_norm (fun ζ hζ => (hgan ζ (by
      simp only [abs_one, Metric.mem_sphere] at hζ
      simp [hζ])).meromorphicAt)
  have hψc : Continuous (mobLift ρ) :=
    continuous_iff_continuousAt.2 fun θ => (hasDerivAt_mobLift hρ0 hρ1 θ).continuousAt
  have h1 : ∫ θ in (0)..(2 * π), log ‖g (circleMap 0 1 θ)‖ ≤
      ∫ θ in (0)..(2 * π), G (α + mobLift ρ θ) := by
    apply intervalIntegral.integral_mono_on two_pi_pos.le hint1
    · exact (hGc.comp (continuous_const.add hψc)).intervalIntegrable _ _
    · intro θ _
      rw [hgbd]
      exact le_max_right _ _
  have h2 := integral_comp_mobLift_le hρ0 hρ1 (F := fun t => G (α + t))
    (hGc.comp (continuous_const.add continuous_id)) (fun t => hG0 _)
  have hper : Function.Periodic G (2 * π) := fun t => by
    simp only [hG, periodic_circleMap 0 R t]
  have h3 : ∫ t in (0)..(2 * π), G (α + t) = ∫ t in (0)..(2 * π), G t := by
    rw [intervalIntegral.integral_comp_add_left, add_zero, hper.intervalIntegral_add_eq α 0,
      zero_add]
  have hKρ : (1 + ρ) / (1 - ρ) = (R + r) / (R - r) := by
    rw [hρ]; field_simp
  have hprox : circleAverage (fun z => log⁺ ‖h z‖) 0 R ≤
      ValueDistribution.characteristic h ⊤ R :=
    (characteristic_eq_circleAverage_posLog hh R).ge
  rw [circleAverage_def, smul_eq_mul] at hjen hprox
  rw [hKρ, h3] at h2
  calc log ‖h z‖ ≤ (2 * π)⁻¹ * ∫ θ in (0)..(2 * π), log ‖g (circleMap 0 1 θ)‖ := hjen
    _ ≤ (2 * π)⁻¹ * ((R + r) / (R - r) * ∫ t in (0)..(2 * π), G t) := by
      gcongr; exact h1.trans h2
    _ = (R + r) / (R - r) * ((2 * π)⁻¹ * ∫ t in (0)..(2 * π), G t) := by ring
    _ ≤ (R + r) / (R - r) * ValueDistribution.characteristic h ⊤ R := by gcongr

/-- Averaging around the circle gives the upper bound by its maximum modulus. -/
theorem characteristic_le_posLog_maximumModulus {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {r : ℝ} (hr : 0 ≤ r) :
    ValueDistribution.characteristic f ⊤ r ≤ Real.posLog (wvMaximumModulus f r) := by
  rw [characteristic_eq_circleAverage_posLog hf r]
  apply circleAverage_mono_on_of_le_circle
  · exact (continuous_posLog.comp hf.continuous.norm).continuousOn.circleIntegrable'
  · intro z hz
    apply posLog_le_posLog (neg_one_lt_zero.le.trans (norm_nonneg _))
    apply wv_norm_le_maximumModulus hf.continuous
    simpa only [Metric.mem_sphere, dist_zero_right, abs_of_nonneg hr] using hz

/-- The pointwise characteristic bound applied at a maximizing point. -/
theorem posLog_maximumModulus_le_characteristic {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {r R : ℝ} (hr : 1 ≤ r) (hrR : r < R) :
    Real.posLog (wvMaximumModulus f r) ≤
      (R + r) / (R - r) * ValueDistribution.characteristic f ⊤ R := by
  obtain ⟨z, hz, hmax⟩ :=
    wvMaximumModulus_attained hf.continuous ((zero_le_one : (0 : ℝ) ≤ 1).trans hr)
  simpa only [hmax] using entire_posLog_le hf hr hrR hz

/-- Affine changes of an entire function increase the characteristic by at most
a constant depending on the two coefficients. -/
theorem characteristic_affine_le {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (a b : ℂ) (r : ℝ) :
    ValueDistribution.characteristic (fun z => a * f z + b) ⊤ r ≤
      ValueDistribution.characteristic f ⊤ r + (log⁺ ‖a‖ + log⁺ ‖b‖ + log 2) := by
  let C : ℝ := log⁺ ‖a‖ + log⁺ ‖b‖ + log 2
  have hg : Differentiable ℂ (fun z => a * f z + b) := (hf.const_mul a).add_const b
  rw [characteristic_eq_circleAverage_posLog hg, characteristic_eq_circleAverage_posLog hf]
  have hi : CircleIntegrable (fun z => log⁺ ‖f z‖) 0 r :=
    (continuous_posLog.comp hf.continuous.norm).continuousOn.circleIntegrable'
  have hconst : CircleIntegrable (fun _ => C) 0 r := circleIntegrable_const C 0 r
  change _ ≤ _ + C
  rw [← show circleAverage (fun _ => C) 0 r = C from circleAverage_const C 0 r,
    ← circleAverage_fun_add hi hconst]
  apply circleAverage_mono
  · exact (continuous_posLog.comp hg.continuous.norm).continuousOn.circleIntegrable'
  · exact hi.add hconst
  · intro z _
    calc
      log⁺ ‖a * f z + b‖ ≤ log⁺ ‖a * f z‖ + log⁺ ‖b‖ + log 2 :=
        posLog_norm_add_le _ _
      _ ≤ log⁺ ‖f z‖ + C := by
        rw [norm_mul]
        linarith [posLog_mul (x := ‖a‖) (y := ‖f z‖)]

end Bruck
