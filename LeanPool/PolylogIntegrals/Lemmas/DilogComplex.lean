/-
Copyright (c) 2026 rainrzk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: rainrzk
-/
module

public import LeanPool.PolylogIntegrals.Lemmas.Dilog
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# The complex dilogarithm

Complex counterparts of `LeanPool.PolylogIntegrals.Lemmas.Dilog` for the series
`LeanPolyLog.Li`, and Landen's
identity on the closed unit disk.

## Main results

* `LeanPolyLog.Dilog.Li_one`: `Li_1(z) = -log(1 - z)` on the open unit disk.
* `LeanPolyLog.Dilog.ofReal_Lir`: `Lir s x = Li s x` for real `x`.
* `LeanPolyLog.Dilog.continuousOn_Li`: for `s ≥ 2`, `Li_s` is continuous on the closed unit disk.
* `LeanPolyLog.Dilog.hasDerivAt_Li_succ`, `LeanPolyLog.Dilog.hasDerivAt_Li_two`: for
  `0 < ‖z‖ < 1`, `Li_(s+1)'(z) = Li_s(z)/z`; in particular `Li_2'(z) = -log(1 - z)/z`.
* `LeanPolyLog.Dilog.Li_sq`: the duplication formula `Li_s(z²) = 2^(s-1) (Li_s(z) + Li_s(-z))`.
* `LeanPolyLog.Dilog.eq_of_hasDerivAt_eq_zero_complex`: a function `ℝ → ℂ` that is continuous on
  `[a, b]` with derivative `0` on `(a, b)` has `f a = f b`.
* `LeanPolyLog.Dilog.Li_two_add_Li_two_div_sub_one`: Landen's identity
  `Li_2(z) + Li_2(z/(z-1)) = -½ log²(1 - z)` for `‖z‖ ≤ 1` and `Re z ≤ 1/2`.
* `LeanPolyLog.Dilog.log_one_sub_I`: `log(1 - i) = ½ log 2 - (π/4) i`.

## Proof sketch

Landen's identity is proved along the segment `t ↦ tz`, `t ∈ [0, 1]`. The condition `Re z ≤ 1/2`
gives `‖tz‖ ≤ ‖tz - 1‖`, so `tz/(tz - 1)` stays in the closed unit disk, and `1 - tz` stays in
the right half-plane, where the principal `log` is holomorphic and `log (1 - tz)⁻¹ = -log (1 - tz)`.
The function `Li_2(tz) + Li_2(tz/(tz-1)) + ½ log²(1 - tz)` is therefore continuous on `[0, 1]`,
has derivative `0` on `(0, 1)` and vanishes at `t = 0`.
-/

open Real Set

namespace LeanPolyLog.Dilog

/-! ### The complex polylogarithm `Li` -/

/-- `Li_s(0) = 0`. -/
@[simp]
public theorem Li_zero (s : ℕ) : Li s 0 = 0 := by
  simp [Li]

/-- For `s ≥ 2` the series of `Li_s(z)` converges for `‖z‖ ≤ 1`. -/
public theorem hasSum_Li {s : ℕ} (hs : 2 ≤ s) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    HasSum (fun n : ℕ => z ^ (n + 1) / ((n + 1 : ℂ) ^ s)) (Li s z) :=
  (summable_pow_div_pow hs hz).hasSum

/-- For `s ≥ 2`, `Li_s` is continuous on the closed unit disk. -/
public theorem continuousOn_Li {s : ℕ} (hs : 2 ≤ s) : ContinuousOn (Li s) (Metric.closedBall 0 1) :=
  continuousOn_tsum_pow_div_pow hs

/-- `Li_1(z) = -log(1 - z)` on the open unit disk. -/
public theorem Li_one {z : ℂ} (hz : ‖z‖ < 1) : Li 1 z = -Complex.log (1 - z) := by
  unfold Li
  simp only [pow_one]
  exact (Complex.hasSum_taylorSeries_neg_log' hz).tsum_eq

/-- `d/dz Li_(s+1)(z) = Li_s(z)/z` for `0 < ‖z‖ < 1`. -/
public theorem hasDerivAt_Li_succ (s : ℕ) {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :
    HasDerivAt (Li (s + 1)) (Li s z / z) z := by
  have h := hasDerivAt_tsum_pow_div_pow (𝕜 := ℂ) s hz
  rw [tsum_pow_div_pow_eq_div s hz0] at h
  exact h

/-- `d/dz Li_2(z) = -log(1 - z)/z` for `0 < ‖z‖ < 1`. -/
public theorem hasDerivAt_Li_two {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :
    HasDerivAt (Li 2) (-Complex.log (1 - z) / z) z := by
  have h := hasDerivAt_Li_succ 1 hz hz0
  rwa [Li_one hz] at h

/-- On real arguments `Li_s` agrees with the real series `Lir s`. -/
public theorem ofReal_Lir (s : ℕ) (x : ℝ) : (Lir s x : ℂ) = Li s x := by
  unfold Lir Li
  rw [Complex.ofReal_tsum]
  push_cast
  rfl

/-- The duplication formula `Li_s(z²) = 2^(s-1) (Li_s(z) + Li_s(-z))` for `‖z‖ ≤ 1`, `s ≥ 2`. -/
public theorem Li_sq {s : ℕ} (hs : 2 ≤ s) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    Li s (z ^ 2) = 2 ^ (s - 1) * (Li s z + Li s (-z)) :=
  tsum_pow_div_pow_sq hs hz

/-! ### Constancy from a vanishing derivative -/

/-- A complex function of a real variable that is continuous on `[a, b]` and has derivative `0`
on `(a, b)` takes the same value at `a` and `b`. -/
public theorem eq_of_hasDerivAt_eq_zero_complex {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn f (Icc a b)) (hd : ∀ x ∈ Ioo a b, HasDerivAt f 0 x) : f a = f b := by
  apply Complex.ext
  · refine eq_of_hasDerivAt_eq_zero (f := fun x => (f x).re) hab
      (Complex.continuous_re.comp_continuousOn hc) fun x hx => ?_
    have C : HasFDerivAt Complex.re Complex.reCLM (f x) := Complex.reCLM.hasFDerivAt
    simpa using! C.comp_hasDerivAt x (hd x hx)
  · refine eq_of_hasDerivAt_eq_zero (f := fun x => (f x).im) hab
      (Complex.continuous_im.comp_continuousOn hc) fun x hx => ?_
    have C : HasFDerivAt Complex.im Complex.imCLM (f x) := Complex.imCLM.hasFDerivAt
    simpa using! C.comp_hasDerivAt x (hd x hx)

/-! ### Landen's identity -/

/-- If `2 Re a ≤ 1`, then `a` is at least as close to `0` as to `1`. -/
public theorem norm_le_norm_sub_one {a : ℂ} (h : 2 * a.re ≤ 1) : ‖a‖ ≤ ‖a - 1‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
  nlinarith

/-- If `2 Re a < 1`, then `a` is closer to `0` than to `1`. -/
public theorem norm_lt_norm_sub_one {a : ℂ} (h : 2 * a.re < 1) : ‖a‖ < ‖a - 1‖ := by
  rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
  nlinarith

/-- Landen's identity `Li_2(z) + Li_2(z/(z-1)) = -½ log²(1 - z)`, for `‖z‖ ≤ 1` and
`Re z ≤ 1/2` (so that also `‖z/(z-1)‖ ≤ 1`).

Proof: along the segment `t ↦ t z`, `t ∈ [0, 1]`, the function
`Li_2(tz) + Li_2(tz/(tz-1)) + ½ log²(1 - tz)` has derivative `0` and vanishes at `t = 0`. -/
public theorem Li_two_add_Li_two_div_sub_one {z : ℂ} (hz : ‖z‖ ≤ 1) (hre : z.re ≤ 1 / 2) :
    Li 2 z + Li 2 (z / (z - 1)) = -(Complex.log (1 - z) ^ 2 / 2) := by
  rcases eq_or_ne z 0 with rfl | hz0
  · simp
  -- facts about `t z` for `t ∈ [0, 1]`
  have hre_t : ∀ t ∈ Icc (0 : ℝ) 1, 2 * ((t : ℂ) * z).re ≤ 1 := by
    rintro t ⟨ht0, ht1⟩
    rw [Complex.re_ofReal_mul]
    nlinarith
  have hnorm_t : ∀ t ∈ Icc (0 : ℝ) 1, ‖(t : ℂ) * z‖ ≤ 1 := by
    rintro t ⟨ht0, ht1⟩
    rw [norm_mul, Complex.norm_of_nonneg ht0]
    nlinarith [norm_nonneg z]
  have hsub_ne : ∀ t ∈ Icc (0 : ℝ) 1, (t : ℂ) * z - 1 ≠ 0 := by
    intro t ht h
    have h2 := hre_t t ht
    have h3 := congrArg Complex.re h
    rw [Complex.sub_re, Complex.one_re, Complex.zero_re] at h3
    linarith
  have hslit_t : ∀ t ∈ Icc (0 : ℝ) 1, 1 - (t : ℂ) * z ∈ Complex.slitPlane := fun t ht =>
    Complex.mem_slitPlane_iff.2 (Or.inl (by
      rw [Complex.sub_re, Complex.one_re]
      linarith [hre_t t ht]))
  have hlin : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (t : ℂ) * z) z t := fun t => by
    simpa using (hasDerivAt_id' t).ofReal_comp.mul_const z
  -- the derivative vanishes on `(0, 1)`
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun t : ℝ => Li 2 ((t : ℂ) * z)
      + Li 2 ((t : ℂ) * z / ((t : ℂ) * z - 1)) + Complex.log (1 - (t : ℂ) * z) ^ 2 / 2) 0 t := by
    rintro t ⟨ht0, ht1⟩
    have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht0.le, ht1.le⟩
    have ht0' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht0.ne'
    have ha0 : (t : ℂ) * z ≠ 0 := mul_ne_zero ht0' hz0
    have ha1 : (t : ℂ) * z - 1 ≠ 0 := hsub_ne t htI
    have ha1' : 1 - (t : ℂ) * z ≠ 0 := Complex.slitPlane_ne_zero (hslit_t t htI)
    have hare : 2 * ((t : ℂ) * z).re < 1 := by
      rw [Complex.re_ofReal_mul]
      nlinarith
    have hanorm : ‖(t : ℂ) * z‖ < 1 := by
      rw [norm_mul, Complex.norm_of_nonneg ht0.le]
      nlinarith [norm_nonneg z]
    have hw0 : (t : ℂ) * z / ((t : ℂ) * z - 1) ≠ 0 := div_ne_zero ha0 ha1
    have hwnorm : ‖(t : ℂ) * z / ((t : ℂ) * z - 1)‖ < 1 := by
      rw [norm_div, div_lt_one (norm_pos_iff.2 ha1)]
      exact norm_lt_norm_sub_one hare
    have h1 := (hasDerivAt_Li_two hanorm ha0).comp t (hlin t)
    have h2 := (hasDerivAt_Li_two hwnorm hw0).comp t ((hlin t).div ((hlin t).sub_const 1) ha1)
    have h3 := ((((hlin t).const_sub 1).clog_real (hslit_t t htI)).pow 2).div_const 2
    refine ((h1.add h2).add h3).congr_deriv ?_
    have hlog : Complex.log (1 - (t : ℂ) * z / ((t : ℂ) * z - 1))
        = -Complex.log (1 - (t : ℂ) * z) := by
      rw [show 1 - (t : ℂ) * z / ((t : ℂ) * z - 1) = (1 - (t : ℂ) * z)⁻¹ by
        field_simp
        ring, Complex.log_inv]
      exact (Complex.mem_slitPlane_iff_arg.1 (hslit_t t htI)).1
    rw [hlog]
    field_simp
    ring
  -- continuity on `[0, 1]`
  have hcont : ContinuousOn (fun t : ℝ => Li 2 ((t : ℂ) * z)
      + Li 2 ((t : ℂ) * z / ((t : ℂ) * z - 1)) + Complex.log (1 - (t : ℂ) * z) ^ 2 / 2)
      (Icc 0 1) := by
    have hlinc : Continuous fun t : ℝ => (t : ℂ) * z := by fun_prop
    have hc1 : ContinuousOn (fun t : ℝ => Li 2 ((t : ℂ) * z)) (Icc 0 1) :=
      (continuousOn_Li le_rfl).comp hlinc.continuousOn fun t ht =>
        mem_closedBall_zero_iff.2 (hnorm_t t ht)
    have hc2 : ContinuousOn (fun t : ℝ => Li 2 ((t : ℂ) * z / ((t : ℂ) * z - 1))) (Icc 0 1) :=
      (continuousOn_Li le_rfl).comp
        (hlinc.continuousOn.div (hlinc.sub continuous_const).continuousOn hsub_ne) fun t ht =>
        mem_closedBall_zero_iff.2 (by
          rw [norm_div, div_le_one (norm_pos_iff.2 (hsub_ne t ht))]
          exact norm_le_norm_sub_one (hre_t t ht))
    have hc3 : ContinuousOn (fun t : ℝ => Complex.log (1 - (t : ℂ) * z) ^ 2 / 2) (Icc 0 1) :=
      (((continuous_const.sub hlinc).continuousOn.clog hslit_t).pow 2).div_const 2
    exact (hc1.add hc2).add hc3
  have h := eq_of_hasDerivAt_eq_zero_complex zero_le_one hcont hderiv
  simp only [Complex.ofReal_zero, zero_mul, zero_sub, zero_div, Li_zero, sub_zero,
    Complex.log_one, add_zero, Complex.ofReal_one, one_mul, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow] at h
  linear_combination -h

/-! ### Values at `1 - i` -/

/-- `arg(1 - i) = -π/4`. -/
public theorem arg_one_sub_I : Complex.arg (1 - Complex.I) = -(π / 4) := by
  have h : (1 - Complex.I) = (Real.sqrt 2 : ℂ) *
      (Complex.cos ↑(-(π / 4)) + Complex.sin ↑(-(π / 4)) * Complex.I) := by
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg,
      Real.cos_pi_div_four, Real.sin_pi_div_four]
    have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
      norm_num
    push_cast
    linear_combination (-(1 : ℂ) / 2 + Complex.I / 2) * h2
  rw [h, Complex.arg_mul_cos_add_sin_mul_I (by positivity)
    ⟨by linarith [pi_pos], by linarith [pi_pos]⟩]

/-- `log(1 - i) = ½ log 2 - (π/4) i`. -/
public theorem log_one_sub_I :
    Complex.log (1 - Complex.I) = ((Real.log 2 / 2 : ℝ) : ℂ) - ((π / 4 : ℝ) : ℂ) * Complex.I := by
  have hn : ‖1 - Complex.I‖ = Real.sqrt 2 := by
    rw [Complex.norm_def, Complex.normSq_apply]
    norm_num
  rw [Complex.log, arg_one_sub_I, hn, Real.log_sqrt (by norm_num)]
  push_cast
  ring

end LeanPolyLog.Dilog
