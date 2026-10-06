/-
Copyright (c) 2026 rainrzk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: rainrzk
-/
module

public import LeanPool.PolylogIntegrals.Lemmas.Series
public import Mathlib.Analysis.Complex.AbelLimit
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# The integral `∫₀^{π/4} x log (2 + 2 cos 2x) dx`

This file computes `∫₀^{π/4} x log (2 + 2 cos 2x) dx = (π/4) G - (21/64) ζ(3)`, the heart of A007
(and hence of A008 and A009), by an Abel-limit argument.

## Main results

* `LeanPolyLog.Fourier.hasSum_neg_pow_mul_cos_div`: for `0 ≤ r < 1`,
  `∑_{n ≥ 1} (-r)ⁿ cos (nθ) / n = -log (1 + 2r cos θ + r²) / 2`.
* `LeanPolyLog.Fourier.integral_mul_cos_two_mul`:
  `∫₀^{π/4} x cos (2nx) dx = (π/8) sin (nπ/2) / n + (cos (nπ/2) - 1) / (4n²)` for `n ≠ 0`.
* `LeanPolyLog.Fourier.hasSum_integral_mul_log`: for `0 ≤ r < 1`,
  `∫₀^{π/4} x log (1 + 2r cos 2x + r²) dx = ∑ₙ coeff n * rⁿ`.
* `LeanPolyLog.Fourier.hasSum_one_div_odd_cube`: `∑_{k ≥ 0} 1/(2k+1)³ = (7/8) ζ(3)`.
* `LeanPolyLog.Fourier.hasSum_coeff`: `∑ₙ coeff n = (π/4) G - (21/64) ζ(3)`.
* `LeanPolyLog.Fourier.integral_mul_log_two_add_two_cos`:
  `∫₀^{π/4} x log (2 + 2 cos 2x) dx = (π/4) G - (21/64) ζ(3)`.

## Proof sketch

* For `0 ≤ r < 1`, the real part of `∑ zⁿ/n = -log (1 - z)` at `z = -r e^{iθ}` is the cosine
  series of `log (1 + 2r cos θ + r²)` above. Its terms are bounded by `rⁿ`, so after putting
  `θ = 2x` and multiplying by `x` it can be integrated term by term over `[0, π/4]`. This writes
  `L(r) = ∫₀^{π/4} x log (1 + 2r cos 2x + r²) dx` as a power series `∑ coeff n * rⁿ`.
* The complex logarithm is never used at `r = 1`. Instead, `L` is continuous at `r = 1` by
  dominated convergence (for `x ∈ [0, π/4]` and `r` near `1` the argument of the logarithm lies in
  `[1, 9]`), and the power series tends to `∑ coeff n` as `r → 1⁻` by Abel's limit theorem
  (`Real.tendsto_tsum_powerSeries_nhdsWithin_lt`). Hence `L(1) = ∑ coeff n`.
* Splitting `n` by its residue mod `4`, the `sin (nπ/2)` terms give `(π/4) G` and the
  `cos (nπ/2)` terms give `-(1/2 - 1/8) ∑ 1/(2k+1)³ = -(21/64) ζ(3)`.
-/

open Real MeasureTheory Set Filter Topology

namespace LeanPolyLog.Fourier

/-- `‖1 + r e^{iθ}‖² = 1 + 2 r cos θ + r²`. -/
public theorem sq_norm_one_add_mul_exp (r θ : ℝ) :
    ‖1 + (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ 2 = 1 + 2 * r * cos θ + r ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.one_re, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re,
    Complex.add_im, Complex.one_im, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im, zero_add]
  linear_combination r ^ 2 * sin_sq_add_cos_sq θ

/-- The real part of `(-r e^{iθ})ⁿ` is `(-r)ⁿ cos (nθ)`. -/
public theorem re_neg_mul_exp_pow (r θ : ℝ) (n : ℕ) :
    ((-(r : ℂ) * Complex.exp (θ * Complex.I)) ^ n).re = (-r) ^ n * cos (n * θ) := by
  rw [mul_pow, ← Complex.exp_nat_mul, ← Complex.ofReal_neg, ← Complex.ofReal_pow,
    show (n : ℂ) * (θ * Complex.I) = ((n * θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

/-- For `0 ≤ r < 1`: `∑_{n ≥ 1} (-r)ⁿ cos (nθ) / n = -log (1 + 2 r cos θ + r²) / 2`. The `n = 0`
term is `0` because Lean divides by `0`. This is the real part of `∑ zⁿ/n = -log (1 - z)` at
`z = -r e^{iθ}`. -/
public theorem hasSum_neg_pow_mul_cos_div {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (θ : ℝ) :
    HasSum (fun n : ℕ ↦ (-r) ^ n * cos (n * θ) / n)
      (-(log (1 + 2 * r * cos θ + r ^ 2) / 2)) := by
  have hz : ‖-(r : ℂ) * Complex.exp (θ * Complex.I)‖ < 1 := by
    rwa [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, norm_neg, Complex.norm_real,
      Real.norm_of_nonneg hr0]
  have h := Complex.hasSum_re (Complex.hasSum_taylorSeries_neg_log hz)
  simp only [Complex.div_natCast_re, re_neg_mul_exp_pow, Complex.neg_re, Complex.log_re] at h
  convert h using 2
  rw [show (1 : ℂ) - -(r : ℂ) * Complex.exp (θ * Complex.I) =
      1 + (r : ℂ) * Complex.exp (θ * Complex.I) by ring, ← sq_norm_one_add_mul_exp, Real.log_pow]
  push_cast
  ring

/-! ### The integrals `∫₀^{π/4} x cos (2nx) dx` -/

/-- `∫₀^{π/4} x cos (2nx) dx = (π/8) sin (nπ/2) / n + (cos (nπ/2) - 1) / (4n²)` for `n ≠ 0`. -/
public theorem integral_mul_cos_two_mul {n : ℕ} (hn : n ≠ 0) :
    ∫ x in (0 : ℝ)..(π / 4), x * cos (2 * n * x) =
      π / 8 * sin (n * π / 2) / n + (cos (n * π / 2) - 1) / (4 * n ^ 2) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hderiv : ∀ x ∈ uIcc (0 : ℝ) (π / 4), HasDerivAt
      (fun x ↦ x * sin (2 * n * x) / (2 * n) + cos (2 * n * x) / (4 * n ^ 2))
      (x * cos (2 * n * x)) x := by
    intro x _
    have hl : HasDerivAt (fun x : ℝ ↦ 2 * n * x) (2 * n) x := by
      simpa using (hasDerivAt_id x).const_mul (2 * (n : ℝ))
    have h1 := ((hasDerivAt_id x).mul hl.sin).div_const (2 * n)
    have h2 := hl.cos.div_const (4 * n ^ 2)
    convert h1.add h2 using 1
    · rfl
    simp only [id]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (by apply Continuous.intervalIntegrable; fun_prop),
    show 2 * (n : ℝ) * (π / 4) = n * π / 2 by ring]
  simp only [mul_zero, sin_zero, zero_div, cos_zero, one_div, mul_inv_rev, zero_add]
  field_simp
  ring

/-! ### Termwise integration for `r < 1` -/

/-- The coefficients of `∫₀^{π/4} x log (1 + 2r cos 2x + r²) dx` as a power series in `r`. -/
@[expose] public noncomputable def coeff (n : ℕ) : ℝ :=
  -2 * (-1) ^ n / n * ∫ x in (0 : ℝ)..(π / 4), x * cos (2 * n * x)

/-- For `0 ≤ r < 1`: `x log (1 + 2r cos 2x + r²) = ∑ₙ (-2 (-r)ⁿ / n) x cos (2nx)`. -/
public theorem hasSum_mul_log {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (x : ℝ) :
    HasSum (fun n : ℕ ↦ -2 * (-r) ^ n / n * (x * cos (2 * n * x)))
      (x * log (1 + 2 * r * cos (2 * x) + r ^ 2)) := by
  convert (hasSum_neg_pow_mul_cos_div hr0 hr1 (2 * x)).mul_left (-2 * x) using 1
  · ext n
    rw [show (n : ℝ) * (2 * x) = 2 * n * x by ring]
    ring
  · ring

/-- The terms of the series in `hasSum_mul_log` are bounded by `2 rⁿ (π/4)` on `(0, π/4]`. -/
public theorem norm_term_le {r : ℝ} (hr0 : 0 ≤ r) (n : ℕ) {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) (π / 4)) :
    ‖-2 * (-r) ^ n / n * (x * cos (2 * n * x))‖ ≤ 2 * r ^ n * (π / 4) := by
  rw [norm_mul]
  have h1 : ‖-2 * (-r) ^ n / (n : ℝ)‖ ≤ 2 * r ^ n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [norm_div, norm_mul, norm_neg, norm_pow, norm_neg, Real.norm_of_nonneg hr0,
        Real.norm_natCast]
      norm_num
      exact div_le_self (by positivity) (by exact_mod_cast hn)
  have h2 : ‖x * cos (2 * n * x)‖ ≤ π / 4 := by
    rw [norm_mul, Real.norm_of_nonneg hx.1.le]
    calc x * ‖cos (2 * n * x)‖ ≤ x * 1 :=
          mul_le_mul_of_nonneg_left (abs_cos_le_one _) hx.1.le
      _ ≤ π / 4 := by linarith [hx.2]
  exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)

/-- For `0 ≤ r < 1`: `∫₀^{π/4} x log (1 + 2r cos 2x + r²) dx = ∑ₙ coeff n * rⁿ`. -/
public theorem hasSum_integral_mul_log {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun n : ℕ ↦ coeff n * r ^ n)
      (∫ x in (0 : ℝ)..(π / 4), x * log (1 + 2 * r * cos (2 * x) + r ^ 2)) := by
  have hπ : (0 : ℝ) ≤ π / 4 := by positivity
  have h := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume)
    (F := fun (n : ℕ) (x : ℝ) ↦ -2 * (-r) ^ n / n * (x * cos (2 * n * x)))
    (fun n _ ↦ 2 * r ^ n * (π / 4))
    (fun n ↦ (by fun_prop : Continuous _).aestronglyMeasurable)
    (fun n ↦ ae_of_all _ fun x hx ↦ norm_term_le hr0 n (by rwa [uIoc_of_le hπ] at hx))
    (ae_of_all _ fun x _ ↦ ((summable_geometric_of_lt_one hr0 hr1).mul_left 2).mul_right _)
    intervalIntegrable_const
    (ae_of_all _ fun x _ ↦ hasSum_mul_log hr0 hr1 x)
  convert h using 1
  ext n
  rw [intervalIntegral.integral_const_mul, coeff, neg_pow]
  ring

/-! ### Continuity at `r = 1` and Abel's limit -/

/-- For `0 < r < 2` and `x ∈ (0, π/4]`: `1 ≤ 1 + 2r cos 2x + r² ≤ 9`. -/
public theorem one_le_and_le_nine {r x :
    ℝ} (hr : r ∈ Ioo (0 : ℝ) 2) (hx : x ∈ Ioc (0 : ℝ) (π / 4)) :
    1 ≤ 1 + 2 * r * cos (2 * x) + r ^ 2 ∧ 1 + 2 * r * cos (2 * x) + r ^ 2 ≤ 9 := by
  have hc : 0 ≤ cos (2 * x) :=
    cos_nonneg_of_mem_Icc ⟨by linarith [hx.1, pi_pos], by linarith [hx.2]⟩
  have hc1 := cos_le_one (2 * x)
  constructor <;> nlinarith [hr.1, hr.2]

/-- `r ↦ ∫₀^{π/4} x log (1 + 2r cos 2x + r²) dx` is continuous at `r = 1`, by dominated
convergence: for `r` near `1` the integrand is bounded by `(π/4) log 9`. -/
public theorem continuousAt_integral_mul_log :
    ContinuousAt (fun r : ℝ ↦ ∫ x in (0 : ℝ)..(π / 4), x * log (1 + 2 * r * cos (2 * x) + r ^ 2))
      1 := by
  have hπ : (0 : ℝ) ≤ π / 4 := by positivity
  apply intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ ↦ π / 4 * log 9)
  · exact Eventually.of_forall fun r ↦ (by fun_prop : Measurable _).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhds zero_lt_one one_lt_two] with r hr
    refine ae_of_all _ fun x hx ↦ ?_
    rw [uIoc_of_le hπ] at hx
    obtain ⟨h1, h9⟩ := one_le_and_le_nine hr hx
    rw [norm_mul, Real.norm_of_nonneg hx.1.le, Real.norm_of_nonneg (log_nonneg h1)]
    exact mul_le_mul hx.2 (log_le_log (by linarith) h9) (log_nonneg h1) (by positivity)
  · exact intervalIntegrable_const
  · refine ae_of_all _ fun x hx ↦ ?_
    rw [uIoc_of_le hπ] at hx
    have hne : 1 + 2 * 1 * cos (2 * x) + (1 : ℝ) ^ 2 ≠ 0 :=
      (zero_lt_one.trans_le (one_le_and_le_nine ⟨zero_lt_one, one_lt_two⟩ hx).1).ne'
    exact continuousAt_const.mul ((by fun_prop : Continuous fun r : ℝ ↦
      1 + 2 * r * cos (2 * x) + r ^ 2).continuousAt.log hne)

/-- Abel's limit: if `∑ coeff n = S`, then `∫₀^{π/4} x log (2 + 2 cos 2x) dx = S`. -/
public theorem integral_mul_log_eq_of_hasSum {S : ℝ} (hS : HasSum coeff S) :
    ∫ x in (0 : ℝ)..(π / 4), x * log (1 + 2 * 1 * cos (2 * x) + 1 ^ 2) = S := by
  have hAbel := Real.tendsto_tsum_powerSeries_nhdsWithin_lt hS.tendsto_sum_nat
  have hL := continuousAt_integral_mul_log.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio 1))
  refine tendsto_nhds_unique (hL.congr' ?_) hAbel
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with r hr
  exact (hasSum_integral_mul_log hr.1.le hr.2).tsum_eq.symm

/-! ### The sum of the coefficients -/

/-- The series defining `ζ(3)` converges to `zeta3`. -/
public theorem hasSum_zeta3 : HasSum (fun n : ℕ ↦ 1 / ((n : ℝ) + 1) ^ 3) zeta3 := by
  have hs : Summable (fun n : ℕ ↦ 1 / ((n : ℝ) + 1) ^ 3) := by
    simpa using (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 3))
  exact hs.hasSum

/-- `∑_{n ≥ 0} 1/n³ = ζ(3)`, where the `n = 0` term is `1/0 = 0`. -/
public theorem hasSum_one_div_natCast_cube : HasSum (fun n : ℕ ↦ 1 / (n : ℝ) ^ 3) zeta3 := by
  rw [← hasSum_nat_add_iff' 1]
  simpa using hasSum_zeta3

/-- `∑_{k ≥ 0} 1/(2k+1)³ = (7/8) ζ(3)`. -/
public theorem hasSum_one_div_odd_cube :
    HasSum (fun k : ℕ ↦ 1 / (2 * (k : ℝ) + 1) ^ 3) (7 / 8 * zeta3) := by
  have he : HasSum (fun k : ℕ ↦ 1 / ((2 * k : ℕ) : ℝ) ^ 3) (zeta3 / 8) := by
    convert hasSum_one_div_natCast_cube.mul_left (1 / 8) using 1
    · ext k
      push_cast
      ring
    · ring
  have ho : Summable (fun k : ℕ ↦ 1 / ((2 * k + 1 : ℕ) : ℝ) ^ 3) :=
    hasSum_one_div_natCast_cube.summable.comp_injective fun a b h ↦ by simpa using h
  have h := (HasSum.even_add_odd (f := fun n : ℕ ↦ 1 / (n : ℝ) ^ 3) he ho.hasSum).unique
    hasSum_one_div_natCast_cube
  convert ho.hasSum using 1
  · ext k
    push_cast
    ring
  · linarith

/-- The odd coefficients: `coeff (2k+1) = (π/4) (-1)ᵏ/(2k+1)² - 1/(2 (2k+1)³)`. -/
public theorem coeff_odd (k : ℕ) :
    coeff (2 * k + 1) = π / 4 * ((-1) ^ k / (2 * k + 1) ^ 2) - 1 / 2 * (1 / (2 * k + 1) ^ 3) := by
  have h : ((2 * k + 1 : ℕ) : ℝ) * π / 2 = k * π + π / 2 := by
    push_cast
    ring
  rw [coeff, integral_mul_cos_two_mul (by omega), h, sin_add_pi_div_two, cos_add_pi_div_two,
    cos_nat_mul_pi, sin_nat_mul_pi, pow_succ, pow_mul]
  have : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- The even coefficients: `coeff (2k) = (1 - (-1)ᵏ) / (16 k³)`. -/
public theorem coeff_even (k : ℕ) : coeff (2 * k) = (1 - (-1) ^ k) / (16 * k ^ 3) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [coeff]
  have h : ((2 * k : ℕ) : ℝ) * π / 2 = k * π := by
    push_cast
    ring
  rw [coeff, integral_mul_cos_two_mul (by omega), h, sin_nat_mul_pi, cos_nat_mul_pi, pow_mul]
  have : (k : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- `∑ₙ coeff n = (π/4) G - (21/64) ζ(3)`. -/
public theorem hasSum_coeff : HasSum coeff (π / 4 * G - 21 / 64 * zeta3) := by
  have ho : HasSum (fun k ↦ coeff (2 * k + 1)) (π / 4 * G - 1 / 2 * (7 / 8 * zeta3)) := by
    simp only [coeff_odd]
    exact (Series.hasSum_catalan.mul_left _).sub (hasSum_one_div_odd_cube.mul_left _)
  have hee : HasSum (fun j ↦ coeff (2 * (2 * j))) 0 := by
    simp [coeff_even, pow_mul]
  have heo : HasSum (fun j ↦ coeff (2 * (2 * j + 1))) (1 / 8 * (7 / 8 * zeta3)) := by
    convert hasSum_one_div_odd_cube.mul_left (1 / 8) using 1
    ext j
    rw [coeff_even, pow_succ, pow_mul]
    push_cast
    have : (2 * (j : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  have he : HasSum (fun k ↦ coeff (2 * k)) (0 + 1 / 8 * (7 / 8 * zeta3)) :=
    HasSum.even_add_odd (f := fun k ↦ coeff (2 * k)) hee heo
  convert he.even_add_odd ho using 1
  ring

/-- `∫₀^{π/4} x log (2 + 2 cos 2x) dx = (π/4) G - (21/64) ζ(3)`. -/
public theorem integral_mul_log_two_add_two_cos :
    ∫ x in (0 : ℝ)..(π / 4), x * log (1 + 2 * 1 * cos (2 * x) + 1 ^ 2) =
      π / 4 * G - 21 / 64 * zeta3 :=
  integral_mul_log_eq_of_hasSum hasSum_coeff

end LeanPolyLog.Fourier
