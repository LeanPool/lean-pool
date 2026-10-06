/-
Copyright (c) 2026 rainrzk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: rainrzk
-/
module

public import LeanPool.PolylogIntegrals.Lemmas.Dilog
public import LeanPool.PolylogIntegrals.Lemmas.LogTrig
public import LeanPool.PolylogIntegrals.Lemmas.Series
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integrals against `1/(1+x²)` and the kernel of A012

This file collects the lemmas behind A012 (and A013): termwise integration of geometric series
over `[0, 1]`, the integral representation of `Li₂(-x)`, an explicit kernel, and the Fubini swap
that connects them.

## Main results

* `LeanPolyLog.Arctan.hasSum_integral_div_one_sub`: termwise integration of
  `φ(y)/(1 - q(y)) = ∑ q(y)ⁿ φ(y)` over `[0, 1]`, when `|q| < 1` on `(0, 1)` and the integrals of
  the norms of the terms are summable.
* `LeanPolyLog.Arctan.hasSum_integral_mul_div_one_add_mul`,
  `LeanPolyLog.Arctan.hasSum_integral_div_one_add_sq`: the cases `q(y) = -xy` and `q(y) = -y²`.
* `LeanPolyLog.Arctan.integral_pow_mul_log`: `∫₀¹ tᵐ log t dt = -1/(m+1)²`.
* `LeanPolyLog.Arctan.integral_mul_log_div_one_add_mul`: for `0 ≤ x ≤ 1`,
  `∫₀¹ x log y/(1 + xy) dy = Li₂(-x)`.
* `LeanPolyLog.Arctan.integral_kernel`: for `y ≥ 0`,
  `∫₀¹ x/((1+x²)(1+xy)) dx = (log 2/2 + πy/4 - log(1+y))/(1+y²)`.
* `LeanPolyLog.Arctan.integral_integral_swap_kernel`: for `φ` integrable on `[0, 1]`,
  `∫₀¹ (1+x²)⁻¹ ∫₀¹ x φ(y)/(1+xy) dy dx = ∫₀¹ φ(y) ∫₀¹ x/((1+x²)(1+xy)) dx dy`.
* `LeanPolyLog.Arctan.integral_log_div_one_add_sq`,
  `LeanPolyLog.Arctan.integral_mul_log_div_one_add_sq`: `∫₀¹ log y/(1+y²) dy = -G` and
  `∫₀¹ y log y/(1+y²) dy = -π²/48`.
* `LeanPolyLog.Arctan.hasDerivAt_Lir_two_neg_add`: on `(0, 1)`, `Li₂(-x) + log x · log(1+x)` is
  an antiderivative of `log x/(1+x)`.

## Proof sketch

* Termwise integration is `MeasureTheory.hasSum_integral_of_summable_integral_norm`. The geometric
  series `∑ q(y)ⁿ` converges on `(0, 1)`, which differs from `(0, 1]` by a null set.
* For `Li₂(-x)`, expand `x log y/(1+xy) = ∑ (-x)ⁿ x yⁿ log y` and use
  `∫₀¹ yⁿ log y dy = -1/(n+1)²`; the norms of the terms integrate to `x^(n+1)/(n+1)²`.
* The kernel has the explicit antiderivative `(log(1+x²)/2 + y arctan x - log(1+xy))/(1+y²)`
  (partial fractions).
* For the swap, on `(0, 1]²` the integrand `x φ(y)/((1+x²)(1+xy))` is bounded by `|φ(y)|`, which
  is integrable on the square, so Fubini applies (`intervalIntegral_intervalIntegral_swap`).
* `∫₀¹ y log y/(1+y²) dy = ∑ (-1)ⁿ ∫₀¹ y^(2n+1) log y dy = -η(2)/4 = -π²/48`.
-/

open Real MeasureTheory Set

namespace LeanPolyLog.Arctan

/-! ### Termwise integration of geometric series -/

/-- Termwise integration of `φ(y)/(1 - q(y)) = ∑ q(y)ⁿ φ(y)` over `[0, 1]`, when `|q(y)| < 1` on
`(0, 1)` and the integrals of the norms of the terms are summable. -/
public theorem hasSum_integral_div_one_sub {φ q : ℝ → ℝ} (hq : ∀ y ∈ Ioo (0 : ℝ) 1, |q y| < 1)
    (hint : ∀ n : ℕ, IntervalIntegrable (fun y ↦ q y ^ n * φ y) volume 0 1)
    (hsum : Summable fun n : ℕ ↦ ∫ y in (0 : ℝ)..1, ‖q y ^ n * φ y‖) :
    HasSum (fun n : ℕ ↦ ∫ y in (0 : ℝ)..1, q y ^ n * φ y) (∫ y in (0 : ℝ)..1, φ y / (1 - q y)) := by
  simp only [intervalIntegral.integral_of_le zero_le_one] at hsum ⊢
  convert hasSum_integral_of_summable_integral_norm (fun n ↦ (hint n).1) hsum using 1
  rw [integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun y hy ↦ ?_
  rw [tsum_mul_right, tsum_geometric_of_abs_lt_one (hq y hy), div_eq_inv_mul]

/-- For `0 ≤ x ≤ 1`: `∫₀¹ x ψ(y)/(1 + xy) dy = ∑ (-x)ⁿ x ∫₀¹ yⁿ ψ(y) dy`, provided the moments
`∫₀¹ ‖yⁿ ψ(y)‖ dy` are summable. -/
public theorem hasSum_integral_mul_div_one_add_mul {ψ : ℝ → ℝ} {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hint : ∀ n : ℕ, IntervalIntegrable (fun y ↦ y ^ n * ψ y) volume 0 1)
    (hsum : Summable fun n : ℕ ↦ ∫ y in (0 : ℝ)..1, ‖y ^ n * ψ y‖) :
    HasSum (fun n : ℕ ↦ (-x) ^ n * x * ∫ y in (0 : ℝ)..1, y ^ n * ψ y)
      (∫ y in (0 : ℝ)..1, x * ψ y / (1 + x * y)) := by
  have hnorm : ∀ n : ℕ, ∫ y in (0 : ℝ)..1, ‖(-x * y) ^ n * (x * ψ y)‖ =
      x ^ (n + 1) * ∫ y in (0 : ℝ)..1, ‖y ^ n * ψ y‖ := by
    intro n
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    ext y
    rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, norm_mul, norm_neg,
      Real.norm_of_nonneg hx0]
    ring
  have h := hasSum_integral_div_one_sub (φ := fun y ↦ x * ψ y) (q := fun y ↦ -x * y)
    (fun y hy ↦ by
      rw [abs_lt]
      constructor <;> nlinarith [hy.1, hy.2])
    (fun n ↦ by
      convert (hint n).const_mul ((-x) ^ n * x) using 1
      ext y
      ring)
    (by
      simp only [hnorm]
      refine Summable.of_nonneg_of_le (fun n ↦ ?_) (fun n ↦ ?_) hsum
      · exact mul_nonneg (pow_nonneg hx0 _)
          (intervalIntegral.integral_nonneg zero_le_one fun y _ ↦ norm_nonneg _)
      · exact mul_le_of_le_one_left
          (intervalIntegral.integral_nonneg zero_le_one fun y _ ↦ norm_nonneg _)
          (pow_le_one₀ hx0 hx1))
  convert h using 1
  · ext n
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    ext y
    ring
  · congr 1
    ext y
    ring_nf

/-- `∫₀¹ ψ(y)/(1 + y²) dy = ∑ (-1)ⁿ ∫₀¹ y²ⁿ ψ(y) dy`, provided the moments `∫₀¹ ‖y²ⁿ ψ(y)‖ dy`
are summable. -/
public theorem hasSum_integral_div_one_add_sq {ψ : ℝ → ℝ}
    (hint : ∀ n : ℕ, IntervalIntegrable (fun y ↦ y ^ (2 * n) * ψ y) volume 0 1)
    (hsum : Summable fun n : ℕ ↦ ∫ y in (0 : ℝ)..1, ‖y ^ (2 * n) * ψ y‖) :
    HasSum (fun n : ℕ ↦ (-1) ^ n * ∫ y in (0 : ℝ)..1, y ^ (2 * n) * ψ y)
      (∫ y in (0 : ℝ)..1, ψ y / (1 + y ^ 2)) := by
  have hq : ∀ (n : ℕ) (y : ℝ), (-y ^ 2) ^ n = (-1) ^ n * y ^ (2 * n) := fun n y ↦ by
    rw [neg_pow, pow_mul]
  have h := hasSum_integral_div_one_sub (φ := ψ) (q := fun y ↦ -y ^ 2)
    (fun y hy ↦ by
      rw [abs_neg, abs_of_nonneg (sq_nonneg y)]
      nlinarith [hy.1, hy.2])
    (fun n ↦ by
      simp only [hq, mul_assoc]
      exact (hint n).const_mul _)
    (by
      simpa only [hq, mul_assoc, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
        using hsum)
  convert h using 1
  · ext n
    rw [← intervalIntegral.integral_const_mul]
    simp only [hq, mul_assoc]
  · simp only [sub_neg_eq_add]

/-! ### The moments `∫₀¹ tᵐ log t dt` -/

/-- `tᵐ log t` is integrable on `[0, 1]`. -/
public theorem intervalIntegrable_pow_mul_log (m : ℕ) :
    IntervalIntegrable (fun t : ℝ ↦ t ^ m * log t) volume 0 1 :=
  intervalIntegral.intervalIntegrable_log'.continuousOn_mul (continuousOn_pow m)

/-- `∫₀¹ tᵐ log t dt = -1/(m+1)²`. -/
public theorem integral_pow_mul_log (m : ℕ) :
    ∫ t in (0 : ℝ)..1, t ^ m * log t = -(1 / ((m : ℝ) + 1) ^ 2) := by
  have h := LogTrig.integral_pow_mul_neg_log m
  simp only [mul_neg, intervalIntegral.integral_neg] at h
  linarith

/-- `∫₀¹ ‖tᵐ log t‖ dt = 1/(m+1)²`. -/
public theorem integral_norm_pow_mul_log (m : ℕ) :
    ∫ t in (0 : ℝ)..1, ‖t ^ m * log t‖ = 1 / ((m : ℝ) + 1) ^ 2 := by
  rw [← LogTrig.integral_pow_mul_neg_log m]
  refine intervalIntegral.integral_congr fun t ht ↦ ?_
  rw [uIcc_of_le zero_le_one] at ht
  rw [norm_mul, Real.norm_of_nonneg (pow_nonneg ht.1 m),
    Real.norm_of_nonpos (log_nonpos ht.1 ht.2)]

/-! ### The dilogarithm as an integral -/

/-- For `0 ≤ x ≤ 1`: `∫₀¹ x log y/(1 + xy) dy = Li₂(-x)`. -/
public theorem integral_mul_log_div_one_add_mul {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∫ y in (0 : ℝ)..1, x * log y / (1 + x * y) = Lir 2 (-x) := by
  have h := hasSum_integral_mul_div_one_add_mul hx0 hx1 intervalIntegrable_pow_mul_log
    (by simpa only [integral_norm_pow_mul_log] using Dilog.summable_one_div_succ_pow le_rfl)
  simp only [integral_pow_mul_log] at h
  refine h.unique ?_
  convert Dilog.hasSum_Lir le_rfl (x := -x) (by rw [abs_neg, abs_of_nonneg hx0]; exact hx1)
    using 1
  ext n
  rw [pow_succ]
  field_simp
  ring

/-! ### The kernel `∫₀¹ x/((1+x²)(1+xy)) dx` and the Fubini swap -/

/-- `x ↦ (1 + x²)⁻¹` is continuous. -/
public theorem continuous_inv_one_add_sq : Continuous fun x : ℝ ↦ (1 + x ^ 2)⁻¹ :=
  (by fun_prop : Continuous fun x : ℝ ↦ 1 + x ^ 2).inv₀ fun x ↦ by positivity

/-- For `y ≥ 0`: `∫₀¹ x/((1+x²)(1+xy)) dx = (log 2/2 + πy/4 - log(1+y))/(1+y²)`. -/
public theorem integral_kernel {y : ℝ} (hy : 0 ≤ y) :
    ∫ x in (0 : ℝ)..1, x / ((1 + x ^ 2) * (1 + x * y)) =
      (log 2 / 2 + π / 4 * y - log (1 + y)) / (1 + y ^ 2) := by
  have hderiv : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt
      (fun x ↦ (log (1 + x ^ 2) / 2 + y * arctan x - log (1 + x * y)) / (1 + y ^ 2))
      (x / ((1 + x ^ 2) * (1 + x * y))) x := by
    intro x hx
    rw [uIcc_of_le zero_le_one] at hx
    have h1 : 0 < 1 + x ^ 2 := by positivity
    have h2 : 0 < 1 + x * y := by nlinarith [hx.1]
    have hA := ((hasDerivAt_pow 2 x).const_add 1).log h1.ne'
    have hC := (((hasDerivAt_id' x).mul_const y).const_add 1).log h2.ne'
    refine ((((hA.div_const 2).add ((hasDerivAt_arctan x).const_mul y)).sub hC).div_const
      (1 + y ^ 2)).congr_deriv ?_
    field_simp
    ring
  have hcont : ContinuousOn (fun x : ℝ ↦ x / ((1 + x ^ 2) * (1 + x * y))) (uIcc 0 1) := by
    refine continuousOn_id.div (by fun_prop) fun x hx ↦ ?_
    rw [uIcc_of_le zero_le_one] at hx
    have h2 : 0 < 1 + x * y := by nlinarith [hx.1]
    positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  simp only [arctan_one, arctan_zero, one_pow, one_mul, zero_mul, add_zero, log_one,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, mul_zero, sub_zero]
  norm_num
  ring

/-- Fubini for the kernel: for `φ` integrable on `[0, 1]`,
`∫₀¹ (1+x²)⁻¹ ∫₀¹ x φ(y)/(1+xy) dy dx = ∫₀¹ φ(y) ∫₀¹ x/((1+x²)(1+xy)) dx dy`. -/
public theorem integral_integral_swap_kernel {φ : ℝ → ℝ} (hφ : IntervalIntegrable φ volume 0 1) :
    ∫ x in (0 : ℝ)..1, (1 + x ^ 2)⁻¹ * ∫ y in (0 : ℝ)..1, x * φ y / (1 + x * y) =
      ∫ y in (0 : ℝ)..1, φ y * ∫ x in (0 : ℝ)..1, x / ((1 + x ^ 2) * (1 + x * y)) := by
  set F : ℝ → ℝ → ℝ := fun x y ↦ x / ((1 + x ^ 2) * (1 + x * y)) * φ y with hF
  have hL : ∀ x : ℝ, (1 + x ^ 2)⁻¹ * ∫ y in (0 : ℝ)..1, x * φ y / (1 + x * y) =
      ∫ y in (0 : ℝ)..1, F x y := by
    intro x
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    ext y
    simp only [hF, div_eq_mul_inv, mul_inv]
    ring
  have hR : ∀ y : ℝ, φ y * ∫ x in (0 : ℝ)..1, x / ((1 + x ^ 2) * (1 + x * y)) =
      ∫ x in (0 : ℝ)..1, F x y := by
    intro y
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    ext x
    simp only [hF]
    ring
  simp only [hL, hR]
  apply intervalIntegral_intervalIntegral_swap
  rw [uIoc_of_le zero_le_one]
  have hφ' : Integrable φ (volume.restrict (Ioc 0 1)) := hφ.1
  have hg : Integrable (fun z : ℝ × ℝ ↦ ‖φ z.2‖)
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc 0 1))) :=
    hφ'.norm.comp_snd _
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
  refine hg.mono' ?_ ?_
  · exact (by fun_prop : Measurable fun z : ℝ × ℝ ↦
      z.1 / ((1 + z.1 ^ 2) * (1 + z.1 * z.2))).aestronglyMeasurable.mul
      hφ'.aestronglyMeasurable.comp_snd
  · rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with z hz
    obtain ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩ := hz
    change ‖F z.1 z.2‖ ≤ ‖φ z.2‖
    simp only [hF, norm_mul]
    refine mul_le_of_le_one_left (norm_nonneg _) ?_
    rw [Real.norm_of_nonneg (by positivity), div_le_one (by positivity)]
    have hxy := mul_pos hx0 hy0
    nlinarith [sq_nonneg z.1, mul_nonneg (sq_nonneg z.1) hxy.le]

/-! ### Two integrals against `1/(1+y²)` -/

/-- `∫₀¹ log y/(1+y²) dy = -G`. -/
public theorem integral_log_div_one_add_sq : ∫ y in (0 : ℝ)..1, log y / (1 + y ^ 2) = -G := by
  rw [← LogTrig.integral_neg_log_div_one_add_sq, ← intervalIntegral.integral_neg]
  simp only [neg_div, neg_neg]

/-- `∫₀¹ y log y/(1+y²) dy = -η(2)/4 = -π²/48`. -/
public theorem integral_mul_log_div_one_add_sq :
    ∫ y in (0 : ℝ)..1, y * log y / (1 + y ^ 2) = -(π ^ 2 / 48) := by
  have hpow : ∀ (n : ℕ) (y : ℝ), y ^ (2 * n) * (y * log y) = y ^ (2 * n + 1) * log y :=
    fun n y ↦ by ring
  have h := hasSum_integral_div_one_add_sq (ψ := fun y ↦ y * log y)
    (fun n ↦ by simpa only [hpow] using intervalIntegrable_pow_mul_log (2 * n + 1))
    (by
      simp only [hpow, integral_norm_pow_mul_log]
      exact (Dilog.summable_one_div_succ_pow le_rfl).comp_injective
        fun a b hab ↦ by simpa using hab)
  simp only [hpow, integral_pow_mul_log] at h
  refine h.unique ?_
  convert Series.hasSum_eta_two.mul_left (-1 / 4) using 1
  · ext n
    push_cast
    field_simp
    ring
  · ring

/-! ### An antiderivative of `log x/(1+x)` -/

/-- `x ↦ log x · log(1+x)` is continuous on `ℝ` (with Lean's `log 0 = 0`). -/
public theorem continuous_log_mul_log_one_add : Continuous fun x : ℝ ↦ log x * log (1 + x) :=
  (Dilog.continuous_log_mul_log_one_sub.comp continuous_neg).congr fun x ↦ by
    simp only [Function.comp, log_neg_eq_log, sub_neg_eq_add]

/-- For `s ≥ 2`, `x ↦ Li_s(-x)` is continuous on `[0, 1]`. -/
public theorem continuousOn_Lir_neg {s : ℕ} (hs : 2 ≤ s) :
    ContinuousOn (fun x ↦ Lir s (-x)) (Icc 0 1) :=
  (Dilog.continuousOn_Lir hs).comp continuousOn_neg fun x hx ↦
    ⟨by linarith [hx.2], by linarith [hx.1]⟩

/-- On `(0, 1)`, `d/dx [Li₂(-x) + log x · log(1+x)] = log x/(1+x)`. -/
public theorem hasDerivAt_Lir_two_neg_add {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun x ↦ Lir 2 (-x) + log x * log (1 + x)) (log x / (1 + x)) x := by
  have h1 := (Dilog.hasDerivAt_Lir_two (x := -x) (by rw [abs_neg, abs_of_pos hx0]; exact hx1)
    (by linarith)).comp x (hasDerivAt_neg x)
  have h2 := (hasDerivAt_log hx0.ne').mul (((hasDerivAt_id' x).const_add 1).log (by linarith))
  refine (h1.add h2).congr_deriv ?_
  rw [sub_neg_eq_add]
  have : 1 + x ≠ 0 := by linarith
  field_simp
  ring

end LeanPolyLog.Arctan
