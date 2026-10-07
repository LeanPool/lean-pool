/-
Copyright (c) 2026 rainrzk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: rainrzk
-/
module

public import LeanPool.PolylogIntegrals.Lemmas.TrilogValues

/-!
# The integral `∫₀¹ log²(x/(1 + x))/(1 + x²) dx`

This file proves
`∫₀¹ (log x - log(1 + x))²/(1 + x²) dx = 2 G log 2 + 2 Im Li₃((1+i)/2)`,
the integral `𝒥` of A014, with an explicit primitive in the point
`χ(x) = x (1 - i)/(1 + x)`, which satisfies `|χ(x)| = √2 x/(1 + x) ≤ 1/√2` on `[0, 1]`.

## Main results

* `LeanPolyLog.Trilog.hasDerivAt_primJ`: on `(0, 1)`, with `L(x) = log x - log(1 + x)`,
  `primJ = L² log(1 - χ) + 2 L Li₂(χ) - 2 Li₃(χ)` has derivative `L² (1/(x - i) - 1/(x + 1))`,
  whose imaginary part is `L²/(1 + x²)`.
* `LeanPolyLog.Trilog.continuousOn_primJ`: `primJ` is continuous on `[0, 1]`, including at `0`,
  where `L` is unbounded.
* `LeanPolyLog.Trilog.integral_log_sub_log_sq_div_one_add_sq`: the value of the integral.

## Proof sketch

* `χ'/χ = 1/x - 1/(1 + x) = L'`, which makes the `Li₂` and `Li₃` terms cancel in the derivative,
  and `-χ'/(1 - χ) = 1/(x - i) - 1/(x + 1)`. This is the substitution `u = x/(1 + x)` of the
  tutorial, done inside the primitive.
* Continuity at `0`: `Li_s(z) = z ∑ zⁿ/(n+1)^s` (`LeanPolyLog.Trilog.Li_eq_mul_tsum`) and
  `log(1 - z) = -Li₁(z)`. So `L² log(1 - χ)` and `L Li₂(χ)` are `x L²` and `x L` times
  functions that are continuous because `|χ| ≤ 3/4`. Both `x L²` and `x L` are continuous at `0`.
* The integrand is nonnegative, so it is integrable
  (`intervalIntegral.integrableOn_deriv_of_nonneg`). Then `primJ 0 = 0`, and
  `Im primJ 1 = (π/4) log² 2 - 2 log 2 Im Li₂((1-i)/2) - 2 Im Li₃((1-i)/2)`.
-/

open Real Set MeasureTheory

namespace LeanPolyLog.Trilog

/-! ### The point `χ(x)` -/

/-- `χ(x) = x (1 - i)/(1 + x)`. -/
@[expose] public noncomputable def chi (x : ℝ) : ℂ := ((x / (1 + x) : ℝ) : ℂ) * (1 - Complex.I)

public theorem chi_re (x : ℝ) : (chi x).re = x / (1 + x) := by
  rw [chi, Complex.re_ofReal_mul]
  simp

/-- `|χ(x)|² = 2 (x/(1 + x))²`. -/
public theorem normSq_chi (x : ℝ) : Complex.normSq (chi x) = 2 * (x / (1 + x)) ^ 2 := by
  rw [chi, Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_apply]
  simp
  ring

/-- On `[0, 1]`, `|χ(x)| ≤ 1/√2 < 3/4`. -/
public theorem norm_chi_le {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : ‖chi x‖ ≤ 3 / 4 := by
  rw [← sq_le_sq₀ (norm_nonneg _) (by norm_num), Complex.sq_norm, normSq_chi]
  have h1 : 0 < 1 + x := by linarith [hx.1]
  have h2 : x / (1 + x) ≤ 1 / 2 := by
    rw [div_le_iff₀ h1]
    linarith [hx.2]
  have h3 : 0 ≤ x / (1 + x) := div_nonneg hx.1 h1.le
  nlinarith

public theorem norm_chi_lt_one {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : ‖chi x‖ < 1 :=
  (norm_chi_le hx).trans_lt (by norm_num)

public theorem chi_ne_zero {x : ℝ} (hx : 0 < x) : chi x ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.2 (div_pos hx (by linarith)).ne') one_sub_I_ne_zero

/-- For `x ≥ 0`, `Re (1 - χ(x)) = 1/(1 + x) > 0`. -/
public theorem one_sub_chi_mem_slitPlane {x : ℝ} (hx : 0 ≤ x) : 1 - chi x ∈ Complex.slitPlane := by
  refine Complex.mem_slitPlane_iff.2 (Or.inl ?_)
  rw [Complex.sub_re, Complex.one_re, chi_re, sub_pos, div_lt_one (by linarith)]
  linarith

public theorem one_add_mul_I_ne_zero (x : ℝ) : 1 + (x : ℂ) * Complex.I ≠ 0 := by
  intro h
  simpa using congrArg Complex.re h

/-- `1 - χ(x) = (1 + x i)/(1 + x)`. -/
public theorem one_sub_chi {x : ℝ} (hx : 0 ≤ x) : 1 - chi x = (1 + x * Complex.I) / (1 + x) := by
  have h1 : (1 : ℂ) + x ≠ 0 := by exact_mod_cast (by linarith : (1 : ℝ) + x ≠ 0)
  rw [chi]
  push_cast
  field_simp
  ring

public theorem chi_zero : chi 0 = 0 := by
  simp [chi]

public theorem chi_one : chi 1 = (1 - Complex.I) / 2 := by
  rw [chi]
  push_cast
  ring

/-! ### Derivatives -/

public theorem hasDerivAt_chi {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt chi (((1 / (1 + x) ^ 2 : ℝ) : ℂ) * (1 - Complex.I)) x := by
  have h1 : 1 + x ≠ 0 := by linarith
  have h := ((hasDerivAt_id x).div ((hasDerivAt_id x).const_add 1) h1).ofReal_comp.mul_const
    (1 - Complex.I)
  refine h.congr_deriv ?_
  congr 2
  simp only [id]
  field_simp
  ring

/-- `χ'/χ = 1/x - 1/(1 + x)`. -/
public theorem deriv_chi_div_chi {x : ℝ} (hx : 0 < x) :
    ((1 / (1 + x) ^ 2 : ℝ) : ℂ) * (1 - Complex.I) / chi x =
      ((1 / x - 1 / (1 + x) : ℝ) : ℂ) := by
  have h1 : 1 + x ≠ 0 := by linarith
  rw [chi, mul_div_mul_right _ _ one_sub_I_ne_zero, ← Complex.ofReal_div]
  congr 1
  field_simp
  ring

/-- `-χ'/(1 - χ) = 1/(x - i) - 1/(x + 1)`. -/
public theorem neg_deriv_chi_div_one_sub_chi {x : ℝ} (hx : 0 ≤ x) :
    -(((1 / (1 + x) ^ 2 : ℝ) : ℂ) * (1 - Complex.I)) / (1 - chi x) =
      1 / ((x : ℂ) - Complex.I) - 1 / ((x : ℂ) + 1) := by
  have h1 : (1 : ℂ) + x ≠ 0 := by exact_mod_cast (by linarith : (1 : ℝ) + x ≠ 0)
  have h1' : (x : ℂ) + 1 ≠ 0 := by rwa [add_comm]
  have h2 := ofReal_sub_I_ne_zero x
  have h3 := one_add_mul_I_ne_zero x
  rw [one_sub_chi hx]
  push_cast
  field_simp
  linear_combination (-((x : ℂ) + 1) * (1 + x)) * Complex.I_sq

/-! ### The primitive -/

/-- A primitive of `L(x)² (1/(x - i) - 1/(x + 1))` on `(0, 1)`, with `L(x) = log x - log(1 + x)`:
`L² log(1 - χ) + 2 L Li₂(χ) - 2 Li₃(χ)`. -/
@[expose] public noncomputable def primJ (x : ℝ) : ℂ :=
  ((Real.log x - Real.log (1 + x) : ℝ) : ℂ) ^ 2 * Complex.log (1 - chi x)
    + 2 * ((Real.log x - Real.log (1 + x) : ℝ) : ℂ) * Li 2 (chi x) - 2 * Li 3 (chi x)

/-- On `(0, 1)`, `primJ' = L² (1/(x - i) - 1/(x + 1))`. -/
public theorem hasDerivAt_primJ {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt primJ (((Real.log x - Real.log (1 + x) : ℝ) : ℂ) ^ 2 *
      (1 / ((x : ℂ) - Complex.I) - 1 / ((x : ℂ) + 1))) x := by
  have hxI : x ∈ Icc (0 : ℝ) 1 := ⟨hx0.le, hx1.le⟩
  have hχn := norm_chi_lt_one hxI
  have hχ0 := chi_ne_zero hx0
  have hχ := hasDerivAt_chi hx0.le
  have hw := deriv_chi_div_chi hx0
  have huv := neg_deriv_chi_div_one_sub_chi hx0.le
  have dL : HasDerivAt (fun t : ℝ ↦ ((Real.log t - Real.log (1 + t) : ℝ) : ℂ))
      ((1 / x - 1 / (1 + x) : ℝ) : ℂ) x := by
    have := ((hasDerivAt_log hx0.ne').sub
      (((hasDerivAt_id x).const_add 1).log (by simp; linarith))).ofReal_comp
    refine this.congr_deriv ?_
    simp only [id]
    push_cast
    ring
  have dlog : HasDerivAt (fun t ↦ Complex.log (1 - chi t))
      (1 / ((x : ℂ) - Complex.I) - 1 / ((x : ℂ) + 1)) x := by
    have := (hχ.const_sub 1).clog_real (one_sub_chi_mem_slitPlane hx0.le)
    rwa [huv] at this
  have d2 : HasDerivAt (fun t ↦ Li 2 (chi t))
      (-Complex.log (1 - chi x) * ((1 / x - 1 / (1 + x) : ℝ) : ℂ)) x := by
    refine ((Dilog.hasDerivAt_Li_two hχn hχ0).comp x hχ).congr_deriv ?_
    rw [← hw]
    ring
  have d3 : HasDerivAt (fun t ↦ Li 3 (chi t))
      (Li 2 (chi x) * ((1 / x - 1 / (1 + x) : ℝ) : ℂ)) x := by
    refine ((Dilog.hasDerivAt_Li_succ 2 hχn hχ0).comp x hχ).congr_deriv ?_
    rw [← hw]
    ring
  have h := (((dL.pow 2).mul dlog).add ((dL.const_mul 2).mul d2)).sub (d3.const_mul 2)
  refine h.congr_deriv ?_
  simp only [Nat.add_one_sub_one, Pi.pow_apply]
  ring

/-- `Im (a (1/(x - i) - 1/(x + 1))) = a/(1 + x²)` for real `a` and `x`. -/
public theorem im_ofReal_mul_sub (a x : ℝ) :
    ((a : ℂ) * (1 / ((x : ℂ) - Complex.I) - 1 / ((x : ℂ) + 1))).im = a / (1 + x ^ 2) := by
  have : (a : ℂ) * (1 / ((x : ℂ) - Complex.I) - 1 / ((x : ℂ) + 1)) =
      (a : ℂ) / ((x : ℂ) - Complex.I) - ((a / (x + 1) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [this, Complex.sub_im, im_ofReal_div_sub_I, Complex.ofReal_im, sub_zero]

/-- On `(0, 1)`, `(Im primJ)' = (log x - log(1 + x))²/(1 + x²)`. -/
public theorem hasDerivAt_im_primJ {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun t ↦ (primJ t).im)
      ((Real.log x - Real.log (1 + x)) ^ 2 / (1 + x ^ 2)) x := by
  rw [← im_ofReal_mul_sub, Complex.ofReal_pow]
  have C : HasFDerivAt Complex.im Complex.imCLM (primJ x) := Complex.imCLM.hasFDerivAt
  simpa using! C.comp_hasDerivAt x (hasDerivAt_primJ hx0 hx1)

/-! ### Continuity of the primitive at `0` -/

/-- `Li_s(z) = z ∑ zⁿ/(n+1)^s`. -/
public theorem Li_eq_mul_tsum (s : ℕ) (z : ℂ) :
    Li s z = z * ∑' n : ℕ, z ^ n / ((n + 1 : ℂ) ^ s) := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · rw [Dilog.tsum_pow_div_pow_eq_div s hz, mul_div_cancel₀ _ hz]
    rfl

/-- For `0 ≤ r < 1`, `z ↦ ∑ zⁿ/(n+1)^s` is continuous on the closed ball of radius `r`
(Weierstrass M-test with `rⁿ`). -/
public theorem continuousOn_tsum_pow_div_succ_pow (s : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ContinuousOn (fun z : ℂ ↦ ∑' n : ℕ, z ^ n / ((n + 1 : ℂ) ^ s)) (Metric.closedBall 0 r) := by
  refine continuousOn_tsum (u := fun n ↦ r ^ n) (fun n ↦ by fun_prop)
    (summable_geometric_of_lt_one hr0 hr1) fun n z hz ↦ ?_
  have hn : ‖(n + 1 : ℂ)‖ = (n : ℝ) + 1 := by
    exact_mod_cast RCLike.norm_natCast (K := ℂ) (n + 1)
  rw [norm_div, norm_pow, norm_pow, hn]
  calc ‖z‖ ^ n / ((n : ℝ) + 1) ^ s ≤ ‖z‖ ^ n :=
        div_le_self (by positivity) (one_le_pow₀ (by linarith [n.cast_nonneg (α := ℝ)]))
    _ ≤ r ^ n := pow_le_pow_left₀ (norm_nonneg z) (mem_closedBall_zero_iff.1 hz) n

/-- `x ↦ x (log x - log(1 + x))` is continuous on `[0, 1]`. -/
public theorem continuousOn_mul_log_sub_log :
    ContinuousOn (fun t : ℝ ↦ t * (Real.log t - Real.log (1 + t))) (Icc 0 1) := by
  have h1 : ContinuousOn (fun t : ℝ ↦ t * Real.log t) (Icc 0 1) := continuous_mul_log.continuousOn
  have h2 : ContinuousOn (fun t : ℝ ↦ t * Real.log (1 + t)) (Icc 0 1) :=
    continuousOn_id.mul continuousOn_log_one_add
  refine (h1.sub h2).congr fun t _ ↦ ?_
  simp only [Pi.sub_apply]
  ring

/-- `x ↦ x (log x - log(1 + x))²` is continuous on `[0, 1]`. -/
public theorem continuousOn_mul_log_sub_log_sq :
    ContinuousOn (fun t : ℝ ↦ t * (Real.log t - Real.log (1 + t)) ^ 2) (Icc 0 1) := by
  have h1 : ContinuousOn (fun t : ℝ ↦ t * Real.log t ^ 2) (Icc 0 1) :=
    Arctan.continuousOn_mul_log_sq.mono Icc_subset_Ici_self
  have h2 : ContinuousOn (fun t : ℝ ↦ 2 * (t * Real.log t) * Real.log (1 + t)) (Icc 0 1) :=
    (continuousOn_const.mul continuous_mul_log.continuousOn).mul continuousOn_log_one_add
  have h3 : ContinuousOn (fun t : ℝ ↦ t * Real.log (1 + t) ^ 2) (Icc 0 1) :=
    continuousOn_id.mul (continuousOn_log_one_add.pow 2)
  refine ((h1.sub h2).add h3).congr fun t _ ↦ ?_
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

public theorem continuousOn_chi : ContinuousOn chi (Icc 0 1) := by
  refine ContinuousOn.mul ?_ continuousOn_const
  exact Complex.continuous_ofReal.comp_continuousOn
    (continuousOn_id.div (by fun_prop) fun t ht ↦ (by linarith [ht.1] : (0 : ℝ) < 1 + t).ne')

/-- `primJ` is continuous on `[0, 1]`. On `[0, 1]` it equals
`-(x L²/(1 + x)) (1 - i) S₁(χ) + 2 (x L/(1 + x)) (1 - i) S₂(χ) - 2 Li₃(χ)` with
`S_s(z) = ∑ zⁿ/(n+1)^s`, and each factor is continuous there. -/
public theorem continuousOn_primJ : ContinuousOn primJ (Icc 0 1) := by
  have hχ : MapsTo chi (Icc (0 : ℝ) 1) (Metric.closedBall 0 (3 / 4)) := fun t ht ↦
    mem_closedBall_zero_iff.2 (norm_chi_le ht)
  have hχ1 : MapsTo chi (Icc (0 : ℝ) 1) (Metric.closedBall 0 1) := fun t ht ↦
    mem_closedBall_zero_iff.2 ((norm_chi_le ht).trans (by norm_num))
  have c1 := (continuousOn_tsum_pow_div_succ_pow 1 (by norm_num) (by norm_num)).comp
    continuousOn_chi hχ
  have c2 := (continuousOn_tsum_pow_div_succ_pow 2 (by norm_num) (by norm_num)).comp
    continuousOn_chi hχ
  have c3 := (Dilog.continuousOn_Li (s := 3) (by norm_num)).comp continuousOn_chi hχ1
  have hne : ∀ t ∈ Icc (0 : ℝ) 1, 1 + t ≠ 0 := fun t ht ↦
    (by linarith [ht.1] : (0 : ℝ) < 1 + t).ne'
  have cA : ContinuousOn
      (fun t : ℝ ↦ ((t * (Real.log t - Real.log (1 + t)) ^ 2 / (1 + t) : ℝ) : ℂ)) (Icc 0 1) :=
    Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_mul_log_sub_log_sq.div (by fun_prop) hne)
  have cB : ContinuousOn
      (fun t : ℝ ↦ ((t * (Real.log t - Real.log (1 + t)) / (1 + t) : ℝ) : ℂ)) (Icc 0 1) :=
    Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_mul_log_sub_log.div (by fun_prop) hne)
  have hF : ContinuousOn (fun t : ℝ ↦
      -(((t * (Real.log t - Real.log (1 + t)) ^ 2 / (1 + t) : ℝ) : ℂ) * (1 - Complex.I) *
          ∑' n : ℕ, chi t ^ n / ((n + 1 : ℂ) ^ 1)) +
        2 * ((t * (Real.log t - Real.log (1 + t)) / (1 + t) : ℝ) : ℂ) * (1 - Complex.I) *
          ∑' n : ℕ, chi t ^ n / ((n + 1 : ℂ) ^ 2) - 2 * Li 3 (chi t)) (Icc 0 1) :=
    (((cA.mul continuousOn_const).mul c1).neg.add
      (((continuousOn_const.mul cB).mul continuousOn_const).mul c2)).sub
      (continuousOn_const.mul c3)
  refine hF.congr fun t ht ↦ ?_
  have hlog : Complex.log (1 - chi t) =
      -(chi t * ∑' n : ℕ, chi t ^ n / ((n + 1 : ℂ) ^ 1)) := by
    rw [← Li_eq_mul_tsum, Dilog.Li_one (norm_chi_lt_one ht), neg_neg]
  simp only [primJ, hlog, Li_eq_mul_tsum 2 (chi t)]
  rw [chi]
  push_cast
  ring

/-! ### The integral -/

/-- `(log x - log(1 + x))²/(1 + x²)` is integrable on `[0, 1]`: it is the nonnegative derivative
of the continuous function `Im primJ`. -/
public theorem intervalIntegrable_log_sub_log_sq_div_one_add_sq :
    IntervalIntegrable (fun x : ℝ ↦ (Real.log x - Real.log (1 + x)) ^ 2 / (1 + x ^ 2))
      volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  exact intervalIntegral.integrableOn_deriv_of_nonneg
    (Complex.continuous_im.comp_continuousOn continuousOn_primJ)
    (fun _ hx ↦ hasDerivAt_im_primJ hx.1 hx.2) fun _ _ ↦ by positivity

/-- `∫₀¹ (log x - log(1 + x))²/(1 + x²) dx = Im primJ 1 - Im primJ 0`. -/
public theorem integral_log_sub_log_sq_div_one_add_sq_eq :
    ∫ x in (0 : ℝ)..1, (Real.log x - Real.log (1 + x)) ^ 2 / (1 + x ^ 2) =
      (primJ 1).im - (primJ 0).im :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
    (Complex.continuous_im.comp_continuousOn continuousOn_primJ)
    (fun _ hx ↦ hasDerivAt_im_primJ hx.1 hx.2) intervalIntegrable_log_sub_log_sq_div_one_add_sq

public theorem primJ_zero : primJ 0 = 0 := by
  simp [primJ, chi_zero]

/-- `Im primJ 1 = 2 G log 2 + 2 Im Li₃((1+i)/2)`. -/
public theorem im_primJ_one :
    (primJ 1).im = 2 * G * Real.log 2 + 2 * (Li 3 ((1 + Complex.I) / 2)).im := by
  have h1 : 1 - (1 - Complex.I) / 2 = (1 + Complex.I) / 2 := by ring
  have h2 : (1 : ℝ) + 1 = 2 := by norm_num
  simp only [primJ, chi_one, h1, h2, Real.log_one, zero_sub]
  rw [log_one_add_I_div_two]
  simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.add_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, pow_succ, pow_zero, one_mul,
    Complex.re_ofNat, Complex.im_ofNat, mul_zero, zero_mul, add_zero, zero_add, sub_zero, mul_one]
  rw [im_Li_two_one_sub_I_div_two, im_Li_three_one_sub_I_div_two]
  ring

/-- `∫₀¹ (log x - log(1 + x))²/(1 + x²) dx = 2 G log 2 + 2 Im Li₃((1+i)/2)`. -/
public theorem integral_log_sub_log_sq_div_one_add_sq :
    ∫ x in (0 : ℝ)..1, (Real.log x - Real.log (1 + x)) ^ 2 / (1 + x ^ 2) =
      2 * G * Real.log 2 + 2 * (Li 3 ((1 + Complex.I) / 2)).im := by
  rw [integral_log_sub_log_sq_div_one_add_sq_eq, im_primJ_one, primJ_zero, Complex.zero_im,
    sub_zero]

end LeanPolyLog.Trilog
