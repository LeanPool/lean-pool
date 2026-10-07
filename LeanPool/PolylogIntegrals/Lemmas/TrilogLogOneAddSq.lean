/-
Copyright (c) 2026 rainrzk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: rainrzk
-/
module

public import LeanPool.PolylogIntegrals.Lemmas.TrilogValues

/-!
# The integral `∫₀¹ log²(1 + x)/(1 + x²) dx`

This file proves
`∫₀¹ log²(1 + x)/(1 + x²) dx = 7π³/64 + (3π/16) log² 2 - 2 G log 2 - 4 Im Li₃((1+i)/2)`,
the integral `ℳ` of A014, using `Li` only on the closed unit disk.

The tutorial expands `1/(x - i)` in powers of `x/(1+i)` on `[1, 2]`, which diverges for
`x > √2`, and arrives at `Li₃(1+i)`, outside the disk. Instead we use an explicit primitive
built from the two points
* `ψ(x) = ((1 - x) + (1 + x) i)/2`, with `|ψ(x)|² = (1 + x²)/2`, and
* `φ(x) = (x - i)/(x + 1) = ψ(x)/(ψ(x) - 1)`, with `|φ(x)|² = (1 + x²)/(1 + x)²`.

For `x ∈ [0, 1]` both lie in the closed unit disk, and for `x ∈ (0, 1)` in the open disk. The
endpoints are `ψ(0) = (1+i)/2`, `ψ(1) = i`, `φ(0) = -i` and `φ(1) = (1-i)/2`.

## Main results

* `LeanPolyLog.Trilog.hasDerivAt_primM`: on `(0, 1)`, with `μ = log((1 - i)/2)`,
  `primM = μ² log ψ - 2 log(1 + x) Li₂(ψ) + 2 Li₃(φ) + 2 Li₃(ψ) - (log(1 + x) + μ)³/3`
  has derivative `log²(1 + x)/(x - i)`.
* `LeanPolyLog.Trilog.continuousOn_primM`: `primM` is continuous on `[0, 1]`.
* `LeanPolyLog.Trilog.integral_log_one_add_sq_div_one_add_sq`: the value of the integral.

## Proof sketch

* `ψ'/ψ = 1/(x - i)` and `φ'/φ = 1/(x - i) - 1/(x + 1)`, and `1 - ψ = (1 + x)(1 - i)/2`, so
  `log(1 - ψ) = log(1 + x) + μ`.
* Landen's identity (`LeanPolyLog.Dilog.Li_two_add_Li_two_div_sub_one`, which applies because
  `|ψ| ≤ 1` and `Re ψ = (1 - x)/2 ≤ 1/2`) gives `Li₂(φ) = -Li₂(ψ) - ½ (log(1 + x) + μ)²`. With
  it, the derivative of `primM` collapses to `log²(1 + x)/(x - i)`.
* Since `Im (1/(x - i)) = 1/(1 + x²)`, the fundamental theorem of calculus applied to `Im primM`
  gives the integral as `Im (primM 1 - primM 0)`, which is evaluated with `Im Li₃(±i) = ±π³/32`,
  `Im Li₂(i) = G`, `Im Li₃((1-i)/2) = -Im Li₃((1+i)/2)` and the logarithms of `i` and `(1±i)/2`.
-/

open Real Set MeasureTheory

namespace LeanPolyLog.Trilog

/-! ### The points `ψ(x)` and `φ(x)` -/

/-- `ψ(x) = ((1 - x) + (1 + x) i)/2`. -/
@[expose] public noncomputable def psi (x : ℝ) : ℂ :=
  (1 + Complex.I) / 2 + x * ((Complex.I - 1) / 2)

/-- `φ(x) = (x - i)/(x + 1)`, which equals `ψ(x)/(ψ(x) - 1)`. -/
@[expose] public noncomputable def phi (x : ℝ) : ℂ := (x - Complex.I) / (x + 1)

public theorem psi_re (x : ℝ) : (psi x).re = (1 - x) / 2 := by
  simp [psi]
  ring

public theorem psi_im (x : ℝ) : (psi x).im = (1 + x) / 2 := by
  simp [psi]
  ring

/-- `|ψ(x)|² = (1 + x²)/2`. -/
public theorem normSq_psi (x : ℝ) : Complex.normSq (psi x) = (1 + x ^ 2) / 2 := by
  rw [Complex.normSq_apply, psi_re, psi_im]
  ring

public theorem norm_psi_le_one {x : ℝ} (hx : |x| ≤ 1) : ‖psi x‖ ≤ 1 := by
  rw [← sq_le_one_iff₀ (norm_nonneg _), Complex.sq_norm, normSq_psi]
  nlinarith [sq_abs x, abs_nonneg x]

public theorem norm_psi_lt_one {x : ℝ} (hx : |x| < 1) : ‖psi x‖ < 1 := by
  rw [← sq_lt_one_iff₀ (norm_nonneg _), Complex.sq_norm, normSq_psi]
  nlinarith [sq_abs x, abs_nonneg x]

/-- For `x > -1`, `Im ψ(x) > 0`, so `ψ(x)` is in the slit plane. -/
public theorem psi_mem_slitPlane {x : ℝ} (hx : -1 < x) : psi x ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.2 (Or.inr (by rw [psi_im]; linarith))

public theorem psi_ne_zero {x : ℝ} (hx : -1 < x) : psi x ≠ 0 :=
  Complex.slitPlane_ne_zero (psi_mem_slitPlane hx)

public theorem ofReal_add_one_ne_zero {x : ℝ} (hx : -1 < x) : (x : ℂ) + 1 ≠ 0 := by
  exact_mod_cast (by linarith : x + 1 ≠ 0)

/-- `|φ(x)|² = (x² + 1)/(x + 1)²`. -/
public theorem normSq_phi (x : ℝ) : Complex.normSq (phi x) = (x ^ 2 + 1) / (x + 1) ^ 2 := by
  rw [phi, Complex.normSq_div]
  have h1 : Complex.normSq ((x : ℂ) + 1) = (x + 1) ^ 2 := by
    rw [show (x : ℂ) + 1 = ((x + 1 : ℝ) : ℂ) by push_cast; ring, Complex.normSq_ofReal]
    ring
  rw [h1, Complex.normSq_apply]
  simp
  ring

public theorem norm_phi_le_one {x : ℝ} (hx : 0 ≤ x) : ‖phi x‖ ≤ 1 := by
  rw [← sq_le_one_iff₀ (norm_nonneg _), Complex.sq_norm, normSq_phi,
    div_le_one (by positivity)]
  nlinarith

public theorem norm_phi_lt_one {x : ℝ} (hx : 0 < x) : ‖phi x‖ < 1 := by
  rw [← sq_lt_one_iff₀ (norm_nonneg _), Complex.sq_norm, normSq_phi,
    div_lt_one (by positivity)]
  nlinarith

public theorem phi_ne_zero {x : ℝ} (hx : -1 < x) : phi x ≠ 0 :=
  div_ne_zero (ofReal_sub_I_ne_zero x) (ofReal_add_one_ne_zero hx)

/-- `1 - ψ(x) = (1 + x)(1 - i)/2`. -/
public theorem one_sub_psi (x : ℝ) : 1 - psi x = ((1 + x : ℝ) : ℂ) * ((1 - Complex.I) / 2) := by
  rw [psi]
  push_cast
  ring

/-- `log(1 - ψ(x)) = log(1 + x) + log((1 - i)/2)` for `x > -1`. -/
public theorem log_one_sub_psi {x : ℝ} (hx : -1 < x) :
    Complex.log (1 - psi x) = Real.log (1 + x) + Complex.log ((1 - Complex.I) / 2) := by
  rw [one_sub_psi, Complex.log_ofReal_mul (by linarith)
    (div_ne_zero one_sub_I_ne_zero two_ne_zero)]

/-- `ψ(x)/(ψ(x) - 1) = φ(x)`. -/
public theorem psi_div_psi_sub_one {x : ℝ} (hx : -1 < x) : psi x / (psi x - 1) = phi x := by
  have h1 : psi x - 1 ≠ 0 := by
    rw [← neg_sub, neg_ne_zero, one_sub_psi]
    exact mul_ne_zero (by exact_mod_cast (by linarith : 1 + x ≠ 0))
      (div_ne_zero one_sub_I_ne_zero two_ne_zero)
  rw [phi, div_eq_div_iff h1 (ofReal_add_one_ne_zero hx), psi]
  linear_combination ((x : ℂ) / 2 + 1 / 2) * Complex.I_sq

public theorem psi_zero : psi 0 = (1 + Complex.I) / 2 := by
  simp [psi]

public theorem psi_one : psi 1 = Complex.I := by
  simp only [psi, Complex.ofReal_one, one_mul]
  ring

public theorem phi_zero : phi 0 = -Complex.I := by
  simp [phi]

public theorem phi_one : phi 1 = (1 - Complex.I) / 2 := by
  simp only [phi, Complex.ofReal_one]
  ring

/-! ### Derivatives -/

public theorem hasDerivAt_psi (x : ℝ) : HasDerivAt psi ((Complex.I - 1) / 2) x := by
  have h := ((hasDerivAt_id x).ofReal_comp.mul_const ((Complex.I - 1) / 2)).const_add
    ((1 + Complex.I) / 2)
  rw [Complex.ofReal_one, one_mul] at h
  exact h

public theorem hasDerivAt_phi {x : ℝ} (hx : -1 < x) :
    HasDerivAt phi ((1 + Complex.I) / ((x : ℂ) + 1) ^ 2) x := by
  have hid : HasDerivAt (fun y : ℝ ↦ (y : ℂ)) 1 x := by
    simpa using (hasDerivAt_id x).ofReal_comp
  exact ((hid.sub_const Complex.I).div (hid.add_const 1) (ofReal_add_one_ne_zero hx)).congr_deriv
    (by ring)

/-- `ψ'/ψ = 1/(x - i)`. -/
public theorem deriv_psi_div_psi {x : ℝ} (hx : -1 < x) :
    (Complex.I - 1) / 2 / psi x = 1 / ((x : ℂ) - Complex.I) := by
  rw [div_eq_div_iff (psi_ne_zero hx) (ofReal_sub_I_ne_zero x), psi]
  linear_combination (-1 / 2 : ℂ) * Complex.I_sq

/-- `φ'/φ = 1/(x - i) - 1/(x + 1)`. -/
public theorem deriv_phi_div_phi {x : ℝ} (hx : -1 < x) :
    (1 + Complex.I) / ((x : ℂ) + 1) ^ 2 / phi x =
      1 / ((x : ℂ) - Complex.I) - 1 / ((x : ℂ) + 1) := by
  have h1 := ofReal_add_one_ne_zero hx
  have h2 := ofReal_sub_I_ne_zero x
  rw [phi]
  field_simp
  ring

/-! ### The primitive -/

/-- A primitive of `log²(1 + x)/(x - i)` on `(0, 1)`: with `μ = log((1 - i)/2)`,
`μ² log ψ - 2 log(1 + x) Li₂(ψ) + 2 Li₃(φ) + 2 Li₃(ψ) - (log(1 + x) + μ)³/3`. -/
@[expose] public noncomputable def primM (x : ℝ) : ℂ :=
  Complex.log ((1 - Complex.I) / 2) ^ 2 * Complex.log (psi x)
    - 2 * (Real.log (1 + x) : ℂ) * Li 2 (psi x) + 2 * Li 3 (phi x) + 2 * Li 3 (psi x)
    - ((Real.log (1 + x) : ℂ) + Complex.log ((1 - Complex.I) / 2)) ^ 3 / 3

/-- On `(0, 1)`, `primM' = log²(1 + x)/(x - i)`. -/
public theorem hasDerivAt_primM {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt primM ((Real.log (1 + x) : ℂ) ^ 2 / ((x : ℂ) - Complex.I)) x := by
  set μ := Complex.log ((1 - Complex.I) / 2) with hμ
  have hx' : -1 < x := by linarith
  have habs : |x| < 1 := abs_lt.2 ⟨by linarith, hx1⟩
  have hψn := norm_psi_lt_one habs
  have hψ0 := psi_ne_zero hx'
  have hφn := norm_phi_lt_one hx0
  have hφ0 := phi_ne_zero hx'
  have hψ := hasDerivAt_psi x
  have hφ := hasDerivAt_phi hx'
  have hu := deriv_psi_div_psi hx'
  have hv := deriv_phi_div_phi hx'
  have hlog := log_one_sub_psi hx'
  -- Landen: `Li₂(ψ) + Li₂(φ) = -½ log²(1 - ψ)`
  have hL := Dilog.Li_two_add_Li_two_div_sub_one (z := psi x) (norm_psi_le_one habs.le)
    (by rw [psi_re]; linarith)
  rw [psi_div_psi_sub_one hx', hlog, ← hμ] at hL
  have d1 : HasDerivAt (fun t ↦ Complex.log (psi t)) (1 / ((x : ℂ) - Complex.I)) x := by
    have := hψ.clog_real (psi_mem_slitPlane hx')
    rwa [hu] at this
  have d2 : HasDerivAt (fun t : ℝ ↦ (Real.log (1 + t) : ℂ)) (1 / ((x : ℂ) + 1)) x := by
    have := (((hasDerivAt_id x).const_add 1).log (by simp; linarith)).ofReal_comp
    refine this.congr_deriv ?_
    simp only [id]
    push_cast
    ring
  have d3 : HasDerivAt (fun t ↦ Li 2 (psi t))
      (-((Real.log (1 + x) : ℂ) + μ) * (1 / ((x : ℂ) - Complex.I))) x := by
    refine ((Dilog.hasDerivAt_Li_two hψn hψ0).comp x hψ).congr_deriv ?_
    rw [hlog, ← hu]
    ring
  have d4 : HasDerivAt (fun t ↦ Li 3 (psi t))
      (Li 2 (psi x) * (1 / ((x : ℂ) - Complex.I))) x := by
    refine ((Dilog.hasDerivAt_Li_succ 2 hψn hψ0).comp x hψ).congr_deriv ?_
    rw [← hu]
    ring
  have d5 : HasDerivAt (fun t ↦ Li 3 (phi t))
      (Li 2 (phi x) * (1 / ((x : ℂ) - Complex.I) - 1 / ((x : ℂ) + 1))) x := by
    refine ((Dilog.hasDerivAt_Li_succ 2 hφn hφ0).comp x hφ).congr_deriv ?_
    rw [← hv]
    ring
  have h := ((((d1.const_mul (μ ^ 2)).sub ((d2.const_mul 2).mul d3)).add (d5.const_mul 2)).add
    (d4.const_mul 2)).sub (((d2.add_const μ).pow 3).div_const 3)
  refine h.congr_deriv ?_
  simp only [Nat.add_one_sub_one]
  linear_combination (2 * (1 / ((x : ℂ) - Complex.I) - 1 / ((x : ℂ) + 1))) * hL

/-- On `(0, 1)`, `(Im primM)' = log²(1 + x)/(1 + x²)`. -/
public theorem hasDerivAt_im_primM {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun t ↦ (primM t).im) (Real.log (1 + x) ^ 2 / (1 + x ^ 2)) x := by
  rw [← im_ofReal_div_sub_I, Complex.ofReal_pow]
  have C : HasFDerivAt Complex.im Complex.imCLM (primM x) := Complex.imCLM.hasFDerivAt
  simpa using! C.comp_hasDerivAt x (hasDerivAt_primM hx0 hx1)

public theorem continuous_psi : Continuous psi := by
  unfold psi
  fun_prop

public theorem continuousOn_phi : ContinuousOn phi (Icc 0 1) :=
  ContinuousOn.div (by fun_prop) (by fun_prop) fun t ht ↦
    ofReal_add_one_ne_zero (by linarith [ht.1])

/-- `primM` is continuous on `[0, 1]`: `ψ` and `φ` stay in the closed unit disk, where `Li₂` and
`Li₃` are continuous, and `ψ` stays in the upper half-plane. -/
public theorem continuousOn_primM : ContinuousOn primM (Icc 0 1) := by
  have hψ : MapsTo psi (Icc (0 : ℝ) 1) (Metric.closedBall 0 1) := fun t ht ↦
    mem_closedBall_zero_iff.2 (norm_psi_le_one (abs_le.2 ⟨by linarith [ht.1], ht.2⟩))
  have hφ : MapsTo phi (Icc (0 : ℝ) 1) (Metric.closedBall 0 1) := fun t ht ↦
    mem_closedBall_zero_iff.2 (norm_phi_le_one ht.1)
  have c1 : ContinuousOn (fun t ↦ Complex.log (psi t)) (Icc 0 1) :=
    continuous_psi.continuousOn.clog fun t ht ↦ psi_mem_slitPlane (by linarith [ht.1])
  have c2 : ContinuousOn (fun t : ℝ ↦ (Real.log (1 + t) : ℂ)) (Icc 0 1) :=
    Complex.continuous_ofReal.comp_continuousOn continuousOn_log_one_add
  have c3 : ContinuousOn (fun t ↦ Li 2 (psi t)) (Icc 0 1) :=
    (Dilog.continuousOn_Li le_rfl).comp continuous_psi.continuousOn hψ
  have c4 : ContinuousOn (fun t ↦ Li 3 (psi t)) (Icc 0 1) :=
    (Dilog.continuousOn_Li (by norm_num)).comp continuous_psi.continuousOn hψ
  have c5 : ContinuousOn (fun t ↦ Li 3 (phi t)) (Icc 0 1) :=
    (Dilog.continuousOn_Li (by norm_num)).comp continuousOn_phi hφ
  exact ((((continuousOn_const.mul c1).sub ((continuousOn_const.mul c2).mul c3)).add
    (continuousOn_const.mul c5)).add (continuousOn_const.mul c4)).sub
    (((c2.add continuousOn_const).pow 3).div_const 3)

/-! ### The integral -/

/-- `∫₀¹ log²(1 + x)/(1 + x²) dx = Im (primM 1 - primM 0)`. -/
public theorem integral_log_one_add_sq_div_one_add_sq_eq :
    ∫ x in (0 : ℝ)..1, Real.log (1 + x) ^ 2 / (1 + x ^ 2) = (primM 1 - primM 0).im := by
  have hcont : ContinuousOn (fun t ↦ (primM t).im) (Icc 0 1) :=
    Complex.continuous_im.comp_continuousOn continuousOn_primM
  have hint : IntervalIntegrable (fun x : ℝ ↦ Real.log (1 + x) ^ 2 / (1 + x ^ 2)) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact (continuousOn_log_one_add.pow 2).div (by fun_prop) fun t _ ↦ by positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont
    (fun _ hx ↦ hasDerivAt_im_primM hx.1 hx.2) hint, Complex.sub_im]

/-- `Im (primM 1 - primM 0) = 7π³/64 + (3π/16) log² 2 - 2 G log 2 - 4 Im Li₃((1+i)/2)`. -/
public theorem im_primM_one_sub_primM_zero :
    (primM 1 - primM 0).im = 7 * π ^ 3 / 64 + 3 * π / 16 * Real.log 2 ^ 2 - 2 * G * Real.log 2
      - 4 * (Li 3 ((1 + Complex.I) / 2)).im := by
  have h2 : (1 : ℝ) + 1 = 2 := by norm_num
  simp only [primM, psi_one, psi_zero, phi_one, phi_zero, add_zero, h2, Real.log_one,
    Complex.ofReal_zero, zero_add, mul_zero, zero_mul, sub_zero]
  rw [Complex.log_I, log_one_add_I_div_two, log_one_sub_I_div_two]
  simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.sub_re,
    Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, pow_succ,
    pow_zero, one_mul, Complex.div_ofNat_im, Complex.div_ofNat_re, Complex.re_ofNat,
    Complex.im_ofNat, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, mul_one]
  rw [im_Li_two_I, im_Li_three_I, im_Li_three_neg_I, im_Li_three_one_sub_I_div_two]
  ring

/-- `∫₀¹ log²(1 + x)/(1 + x²) dx = 7π³/64 + (3π/16) log² 2 - 2 G log 2 - 4 Im Li₃((1+i)/2)`. -/
public theorem integral_log_one_add_sq_div_one_add_sq :
    ∫ x in (0 : ℝ)..1, Real.log (1 + x) ^ 2 / (1 + x ^ 2) =
      7 * π ^ 3 / 64 + 3 * π / 16 * Real.log 2 ^ 2 - 2 * G * Real.log 2
        - 4 * (Li 3 ((1 + Complex.I) / 2)).im := by
  rw [integral_log_one_add_sq_div_one_add_sq_eq, im_primM_one_sub_primM_zero]

end LeanPolyLog.Trilog
