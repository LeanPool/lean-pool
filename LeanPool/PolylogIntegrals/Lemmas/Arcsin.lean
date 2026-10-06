/-
Copyright (c) 2026 rainrzk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: rainrzk
-/
module

public import LeanPool.PolylogIntegrals.Lemmas.Dilog
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Polylogarithms against the arcsine weight

This file proves the identity behind A011 and A016. Let `s ≥ 2`, and let `w ≥ 0` on `(0, 1]`
have the moments `∫₀¹ yⁿ w(y) dy = 1/(n+1)^s`. Then
`∫₀¹ Li_s(x) / (x √(1 - x²)) dx = ∫₀^{π/2} w(sin φ) (π/2 + φ) dφ`.
The weight `w = -log` (with `s = 2`) gives A011, and `w = log²/2` (with `s = 3`) gives A016.

## Main results

* `LeanPolyLog.Arcsin.hasDerivAt_arcsin_div`: for `|x|, |y| < 1`,
  `d/dx arcsin ((x - y)/(1 - xy)) = √(1 - y²) / ((1 - xy) √(1 - x²))`.
* `LeanPolyLog.Arcsin.integral_one_div_mul_sqrt`: for `|y| < 1`,
  `∫₀¹ dx / ((1 - xy) √(1 - x²)) = (π/2 + arcsin y) / √(1 - y²)`.
* `LeanPolyLog.Arcsin.integral_div_one_sub_mul`: for `0 < x < 1`,
  `∫₀¹ w(y) / (1 - xy) dy = Li_s(x)/x`.
* `LeanPolyLog.Arcsin.integral_Lir_div_mul_sqrt_eq_integral_arcsin`:
  `∫₀¹ Li_s(x) / (x √(1 - x²)) dx = ∫₀¹ w(y) (π/2 + arcsin y) / √(1 - y²) dy`.
* `LeanPolyLog.Arcsin.integral_mul_arcsin_div_sqrt`: the substitution `y = sin φ`, for any `w`.
* `LeanPolyLog.Arcsin.integral_Lir_div_mul_sqrt`:
  `∫₀¹ Li_s(x) / (x √(1 - x²)) dx = ∫₀^{π/2} w(sin φ) (π/2 + φ) dφ`.

## Proof sketch

* `Li_s(x)/x = ∑ xⁿ/(n+1)^s = ∑ xⁿ ∫₀¹ yⁿ w(y) dy = ∫₀¹ w(y)/(1 - xy) dy`. The termwise
  integration is justified because the terms are nonnegative and their integrals are summable.
* So the integral is `∫₀¹ ∫₀¹ w(y) / ((1 - xy) √(1 - x²)) dy dx`. The integrand is nonnegative
  and integrable on the square: for fixed `x` it is at most a multiple of `w(y)`, and its integral
  in `y` is `Li_s(x) / (x √(1 - x²)) ≤ Li_s(1) / √(1 - x²)`. Fubini swaps the two integrals.
* The integral in `x` is elementary: `arcsin ((x - y)/(1 - xy))` is an antiderivative of
  `√(1 - y²) / ((1 - xy) √(1 - x²))`, and it runs from `-arcsin y` at `x = 0` to `π/2` at `x = 1`.
* Finally `y = sin φ` turns `dy / √(1 - y²)` into `dφ` and `arcsin y` into `φ`.

In Lean `√0 = 0` and `a / 0 = 0`, so the integrands are `0` at `x = 1` or `y = 1`. Single points
do not affect the integrals, and the proofs work on the open square `(0, 1)²`.
-/

open Real MeasureTheory Set Function

namespace LeanPolyLog.Arcsin

/-! ### The kernel `1/((1 - xy) √(1 - x²))` -/

/-- `1 - xy > 0` for `x ∈ [0, 1]` and `|y| < 1`. -/
public theorem one_sub_mul_pos {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Ioo (-1 : ℝ) 1) :
    0 < 1 - x * y := by
  nlinarith [mul_nonneg (sub_nonneg.2 hx.2) (by linarith [hy.1] : (0 : ℝ) ≤ 1 + y), hx.1, hy.2]

/-- `1 - ((x - y)/(1 - xy))² = (1 - x²)(1 - y²)/(1 - xy)²`. -/
public theorem one_sub_sq_div_one_sub_mul {x y : ℝ} (h : 1 - x * y ≠ 0) :
    1 - ((x - y) / (1 - x * y)) ^ 2 = (1 - x ^ 2) * (1 - y ^ 2) / (1 - x * y) ^ 2 := by
  field_simp
  ring

/-- For `|x|, |y| < 1`: `d/dx arcsin ((x - y)/(1 - xy)) = √(1 - y²) / ((1 - xy) √(1 - x²))`. -/
public theorem hasDerivAt_arcsin_div {x y : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) (hy : y ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun x ↦ arcsin ((x - y) / (1 - x * y)))
      (√(1 - y ^ 2) / ((1 - x * y) * √(1 - x ^ 2))) x := by
  have hxy : 0 < 1 - x * y := by nlinarith [hx.1, hx.2, hy.1, hy.2]
  have hx2 : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  have hy2 : 0 < 1 - y ^ 2 := by nlinarith [hy.1, hy.2]
  have hu : HasDerivAt (fun x ↦ (x - y) / (1 - x * y))
      ((1 * (1 - x * y) - (x - y) * (0 - 1 * y)) / (1 - x * y) ^ 2) x :=
    ((hasDerivAt_id x).sub_const y).div ((hasDerivAt_const x 1).sub
      ((hasDerivAt_id x).mul_const y)) hxy.ne'
  have hlt : (x - y) / (1 - x * y) < 1 := by
    rw [div_lt_one hxy]
    nlinarith [hx.1, hx.2, hy.1, hy.2]
  have hgt : -1 < (x - y) / (1 - x * y) := by
    rw [lt_div_iff₀ hxy]
    nlinarith [hx.1, hx.2, hy.1, hy.2]
  refine ((hasDerivAt_arcsin hgt.ne' hlt.ne).comp x hu).congr_deriv ?_
  rw [one_sub_sq_div_one_sub_mul hxy.ne', Real.sqrt_div' _ (by positivity), Real.sqrt_mul hx2.le,
    Real.sqrt_sq hxy.le]
  have h1 : 0 < √(1 - x ^ 2) := Real.sqrt_pos.2 hx2
  have h2 : 0 < √(1 - y ^ 2) := Real.sqrt_pos.2 hy2
  have h3 : √(1 - y ^ 2) ^ 2 = 1 - y ^ 2 := Real.sq_sqrt hy2.le
  field_simp
  linear_combination -h3

/-- `x ↦ arcsin ((x - y)/(1 - xy))` is continuous on `[0, 1]` for `|y| < 1`. -/
public theorem continuousOn_arcsin_div {y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) :
    ContinuousOn (fun x ↦ arcsin ((x - y) / (1 - x * y))) (Icc 0 1) :=
  continuous_arcsin.comp_continuousOn <| (continuousOn_id.sub continuousOn_const).div
    (continuousOn_const.sub (continuousOn_id.mul continuousOn_const))
    fun _ hx ↦ (one_sub_mul_pos hx hy).ne'

/-- The derivative in `hasDerivAt_arcsin_div` is nonnegative for `0 < x < 1`. -/
public theorem sqrt_div_mul_sqrt_nonneg {x y :
    ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (-1 : ℝ) 1) :
    0 ≤ √(1 - y ^ 2) / ((1 - x * y) * √(1 - x ^ 2)) :=
  div_nonneg (Real.sqrt_nonneg _)
    (mul_nonneg (one_sub_mul_pos ⟨hx.1.le, hx.2.le⟩ hy).le (Real.sqrt_nonneg _))

/-- `∫₀¹ √(1 - y²) / ((1 - xy) √(1 - x²)) dx = π/2 + arcsin y` for `|y| < 1`. -/
public theorem integral_sqrt_div_mul_sqrt {y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) :
    ∫ x in (0 : ℝ)..1, √(1 - y ^ 2) / ((1 - x * y) * √(1 - x ^ 2)) = π / 2 + arcsin y := by
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun x ↦ arcsin ((x - y) / (1 - x * y)))
      (√(1 - y ^ 2) / ((1 - x * y) * √(1 - x ^ 2))) x :=
    fun x hx ↦ hasDerivAt_arcsin_div ⟨by linarith [hx.1], hx.2⟩ hy
  have hint := intervalIntegral.integrableOn_deriv_of_nonneg (continuousOn_arcsin_div hy)
    hderiv fun x hx ↦ sqrt_div_mul_sqrt_nonneg hx hy
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
    (continuousOn_arcsin_div hy) hderiv
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr hint)]
  have h1 : (1 : ℝ) - y ≠ 0 := by linarith [hy.2]
  simp only [one_mul, zero_mul, sub_zero, zero_sub, div_one, arcsin_neg, div_self h1, arcsin_one]
  ring

/-- The kernel `1/((1 - xy) √(1 - x²))` is integrable on `(0, 1]` for `|y| < 1`. -/
public theorem integrableOn_one_div_mul_sqrt {y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) :
    IntegrableOn (fun x ↦ 1 / ((1 - x * y) * √(1 - x ^ 2))) (Ioc 0 1) := by
  have hy2 : 0 < √(1 - y ^ 2) := Real.sqrt_pos.2 (by nlinarith [hy.1, hy.2])
  have h : IntegrableOn
      (fun x ↦ 1 / √(1 - y ^ 2) * (√(1 - y ^ 2) / ((1 - x * y) * √(1 - x ^ 2)))) (Ioc 0 1) :=
    (intervalIntegral.integrableOn_deriv_of_nonneg (continuousOn_arcsin_div hy)
      (fun x hx ↦ hasDerivAt_arcsin_div ⟨by linarith [hx.1], hx.2⟩ hy)
      fun x hx ↦ sqrt_div_mul_sqrt_nonneg hx hy).const_mul _
  refine h.congr_fun (fun x _ ↦ ?_) measurableSet_Ioc
  field_simp

/-- `1/√(1 - x²)` is integrable on `(0, 1]`. -/
public theorem integrableOn_one_div_sqrt :
    IntegrableOn (fun x : ℝ ↦ 1 / √(1 - x ^ 2)) (Ioc 0 1) := by
  simpa using integrableOn_one_div_mul_sqrt (y := 0) (by norm_num)

/-- `∫₀¹ dx / ((1 - xy) √(1 - x²)) = (π/2 + arcsin y) / √(1 - y²)` for `|y| < 1`. -/
public theorem integral_one_div_mul_sqrt {y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) :
    ∫ x in (0 : ℝ)..1, 1 / ((1 - x * y) * √(1 - x ^ 2)) = (π / 2 + arcsin y) / √(1 - y ^ 2) := by
  have hy2 : 0 < √(1 - y ^ 2) := Real.sqrt_pos.2 (by nlinarith [hy.1, hy.2])
  rw [eq_div_iff hy2.ne', ← integral_sqrt_div_mul_sqrt hy, ← intervalIntegral.integral_mul_const]
  congr 1
  ext x
  ring

/-! ### Generating functions of moments -/

/-- For `0 < |x| ≤ 1` and `s ≥ 2`: `∑_{n ≥ 0} xⁿ/(n+1)^s = Li_s(x)/x`. -/
public theorem hasSum_Lir_div_self {s : ℕ} (hs : 2 ≤ s) {x : ℝ} (hx : |x| ≤ 1) (hx0 : x ≠ 0) :
    HasSum (fun n : ℕ ↦ x ^ n / ((n : ℝ) + 1) ^ s) (Lir s x / x) := by
  have hsum : Summable fun n : ℕ ↦ x ^ n / ((n : ℝ) + 1) ^ s := by
    refine (Dilog.summable_one_div_succ_pow hs).of_norm_bounded fun n ↦ ?_
    rw [norm_div, norm_pow, Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)]
    gcongr
    exact pow_le_one₀ (abs_nonneg x) hx
  convert hsum.hasSum using 1
  unfold Lir
  exact (Dilog.tsum_pow_div_pow_eq_div s hx0).symm

/-- For `0 < x ≤ 1` and `s ≥ 2`: `0 ≤ Li_s(x)/x`. -/
public theorem Lir_div_self_nonneg {s : ℕ} (hs : 2 ≤ s) {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    0 ≤ Lir s x / x :=
  (hasSum_Lir_div_self hs (abs_le.2 ⟨by linarith [hx.1], hx.2⟩) hx.1.ne').nonneg
    fun n ↦ by have := hx.1; positivity

/-- For `0 < x ≤ 1` and `s ≥ 2`: `Li_s(x)/x ≤ Li_s(1)`. -/
public theorem Lir_div_self_le {s : ℕ} (hs : 2 ≤ s) {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    Lir s x / x ≤ Lir s 1 := by
  have h1 := hasSum_Lir_div_self hs (x := 1) (by simp) one_ne_zero
  rw [div_one] at h1
  refine hasSum_le (fun n ↦ ?_)
    (hasSum_Lir_div_self hs (abs_le.2 ⟨by linarith [hx.1], hx.2⟩) hx.1.ne') h1
  gcongr
  · exact hx.1.le
  · exact hx.2

/-- Let `w ≥ 0` on `(0, 1]` have the moments `∫₀¹ yⁿ w(y) dy = 1/(n+1)^s`. Then for `0 < x < 1`,
`∫₀¹ w(y)/(1 - xy) dy = Li_s(x)/x`: expand `1/(1 - xy)` as a geometric series and integrate
term by term. -/
public theorem integral_div_one_sub_mul {s : ℕ} {w : ℝ → ℝ} (hw0 : ∀ y ∈ Ioc (0 : ℝ) 1, 0 ≤ w y)
    (hint : ∀ n : ℕ, IntegrableOn (fun y ↦ y ^ n * w y) (Ioc 0 1))
    (hmom : ∀ n : ℕ, ∫ y in (0 : ℝ)..1, y ^ n * w y = 1 / ((n : ℝ) + 1) ^ s)
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ∫ y in Ioc (0 : ℝ) 1, w y / (1 - x * y) = Lir s x / x := by
  have hmom' : ∀ n : ℕ, ∫ y in Ioc (0 : ℝ) 1, y ^ n * w y = 1 / ((n : ℝ) + 1) ^ s := fun n ↦ by
    rw [← intervalIntegral.integral_of_le zero_le_one, hmom]
  have hsum : ∀ y ∈ Ioc (0 : ℝ) 1,
      HasSum (fun n : ℕ ↦ x ^ n * (y ^ n * w y)) (w y / (1 - x * y)) := by
    intro y hy
    have h0 : 0 ≤ x * y := mul_nonneg hx.1.le hy.1.le
    have h1 : x * y < 1 := by nlinarith [hx.1, hx.2, hy.1, hy.2]
    convert (hasSum_geometric_of_lt_one h0 h1).mul_right (w y) using 1
    · ext n
      rw [mul_pow]
      ring
    · rw [div_eq_mul_inv, mul_comm]
  have hnorm : ∀ n : ℕ, ∫ y in Ioc (0 : ℝ) 1, ‖x ^ n * (y ^ n * w y)‖ =
      x ^ n * (1 / ((n : ℝ) + 1) ^ s) := by
    intro n
    rw [← hmom' n, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun y hy ↦ ?_
    exact Real.norm_of_nonneg
      (mul_nonneg (pow_nonneg hx.1.le n) (mul_nonneg (pow_nonneg hy.1.le n) (hw0 y hy)))
  have hsummable : Summable fun n : ℕ ↦ x ^ n * (1 / ((n : ℝ) + 1) ^ s) := by
    refine Summable.of_nonneg_of_le (fun n ↦ by have := hx.1; positivity) (fun n ↦ ?_)
      (summable_geometric_of_lt_one hx.1.le hx.2)
    have h : 1 / ((n : ℝ) + 1) ^ s ≤ 1 :=
      div_le_one_of_le₀ (one_le_pow₀ (by linarith [n.cast_nonneg (α := ℝ)])) (by positivity)
    calc x ^ n * (1 / ((n : ℝ) + 1) ^ s) ≤ x ^ n * 1 :=
          mul_le_mul_of_nonneg_left h (pow_nonneg hx.1.le n)
      _ = x ^ n := mul_one _
  rw [setIntegral_congr_fun measurableSet_Ioc fun y hy ↦ (hsum y hy).tsum_eq.symm,
    ← integral_tsum_of_summable_integral_norm (fun n ↦ (hint n).const_mul (x ^ n))
      (by simpa only [hnorm] using hsummable)]
  simp_rw [integral_const_mul, hmom']
  unfold Lir
  rw [← Dilog.tsum_pow_div_pow_eq_div s hx.1.ne']
  congr 1
  ext n
  ring

/-! ### Swapping the order of integration -/

/-- Let `s ≥ 2`, and let `w ≥ 0` on `(0, 1]` be measurable with the moments
`∫₀¹ yⁿ w(y) dy = 1/(n+1)^s`. Then
`∫₀¹ Li_s(x) / (x √(1 - x²)) dx = ∫₀¹ w(y) (π/2 + arcsin y) / √(1 - y²) dy`. Both sides equal
`∫₀¹ ∫₀¹ w(y) / ((1 - xy) √(1 - x²)) dx dy`, by Fubini. -/
public theorem integral_Lir_div_mul_sqrt_eq_integral_arcsin {s : ℕ} (hs : 2 ≤ s) {w : ℝ → ℝ}
    (hw : Measurable w) (hw0 : ∀ y ∈ Ioc (0 : ℝ) 1, 0 ≤ w y)
    (hint : ∀ n : ℕ, IntegrableOn (fun y ↦ y ^ n * w y) (Ioc 0 1))
    (hmom : ∀ n : ℕ, ∫ y in (0 : ℝ)..1, y ^ n * w y = 1 / ((n : ℝ) + 1) ^ s) :
    ∫ x in (0 : ℝ)..1, Lir s x / (x * √(1 - x ^ 2)) =
      ∫ y in (0 : ℝ)..1, w y * ((π / 2 + arcsin y) / √(1 - y ^ 2)) := by
  set F : ℝ → ℝ → ℝ := fun x y ↦ w y * (1 / ((1 - x * y) * √(1 - x ^ 2))) with hF
  have hF0 : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ y ∈ Ioo (0 : ℝ) 1, 0 ≤ F x y := fun x hx y hy ↦
    mul_nonneg (hw0 y ⟨hy.1, hy.2.le⟩) (one_div_nonneg.2 (mul_nonneg
      (one_sub_mul_pos ⟨hx.1.le, hx.2.le⟩ ⟨by linarith [hy.1], hy.2⟩).le (Real.sqrt_nonneg _)))
  have hwint : IntegrableOn w (Ioo 0 1) := by
    simpa using (hint 0).mono_set Ioo_subset_Ioc_self
  -- the integral in `y`
  have hinner_y : ∀ x ∈ Ioo (0 : ℝ) 1,
      ∫ y in Ioo (0 : ℝ) 1, F x y = Lir s x / (x * √(1 - x ^ 2)) := by
    intro x hx
    have h := integral_div_one_sub_mul hw0 hint hmom hx
    rw [integral_Ioc_eq_integral_Ioo] at h
    have hx2 : 0 < √(1 - x ^ 2) := Real.sqrt_pos.2 (by nlinarith [hx.1, hx.2])
    calc ∫ y in Ioo (0 : ℝ) 1, F x y
        = ∫ y in Ioo (0 : ℝ) 1, w y / (1 - x * y) * (1 / √(1 - x ^ 2)) := by
          refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
          simp only [hF]
          rw [mul_one_div, mul_one_div, div_div]
      _ = Lir s x / (x * √(1 - x ^ 2)) := by
          rw [integral_mul_const, h]
          field_simp
  -- the integral in `x`
  have hinner_x : ∀ y ∈ Ioo (0 : ℝ) 1,
      ∫ x in Ioo (0 : ℝ) 1, F x y = w y * ((π / 2 + arcsin y) / √(1 - y ^ 2)) := by
    intro y hy
    rw [integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le zero_le_one,
      integral_one_div_mul_sqrt ⟨by linarith [hy.1], hy.2⟩]
  -- integrability on the square
  have hmeas : AEStronglyMeasurable (uncurry F)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
    have : Measurable fun p : ℝ × ℝ ↦ w p.2 * (1 / ((1 - p.1 * p.2) * √(1 - p.1 ^ 2))) := by
      fun_prop
    exact this.aestronglyMeasurable
  have hprod : Integrable (uncurry F)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
    refine (integrable_prod_iff hmeas).2 ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioo, hmeas.prodMk_left] with x hx hxm
      have hx1 : 0 < 1 - x := by linarith [hx.2]
      have hx2 : 0 < √(1 - x ^ 2) := Real.sqrt_pos.2 (by nlinarith [hx.1, hx.2])
      refine (hwint.mul_const (1 / ((1 - x) * √(1 - x ^ 2)))).mono' hxm ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
      have hxy : 1 - x ≤ 1 - x * y := by nlinarith [hx.1, hy.2]
      simp only [uncurry_apply_pair]
      rw [Real.norm_of_nonneg (hF0 x hx y hy)]
      simp only [hF]
      gcongr
      exact hw0 y ⟨hy.1, hy.2.le⟩
    · have hdom : IntegrableOn (fun x : ℝ ↦ Lir s 1 * (1 / √(1 - x ^ 2))) (Ioo 0 1) :=
        (integrableOn_one_div_sqrt.mono_set Ioo_subset_Ioc_self).const_mul _
      refine hdom.mono' hmeas.norm.integral_prod_right' ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      have hx2 : 0 < √(1 - x ^ 2) := Real.sqrt_pos.2 (by nlinarith [hx.1, hx.2])
      have h : ∫ y in Ioo (0 : ℝ) 1, ‖uncurry F (x, y)‖ = ∫ y in Ioo (0 : ℝ) 1, F x y :=
        setIntegral_congr_fun measurableSet_Ioo fun y hy ↦ Real.norm_of_nonneg (hF0 x hx y hy)
      rw [h, hinner_y x hx, ← div_div, mul_one_div,
        Real.norm_of_nonneg (div_nonneg (Lir_div_self_nonneg hs ⟨hx.1, hx.2.le⟩) hx2.le)]
      gcongr
      exact Lir_div_self_le hs ⟨hx.1, hx.2.le⟩
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo,
    ← setIntegral_congr_fun measurableSet_Ioo hinner_y,
    ← setIntegral_congr_fun measurableSet_Ioo hinner_x]
  exact integral_integral_swap hprod

/-! ### The substitution `y = sin φ` -/

/-- The substitution `y = sin φ`:
`∫₀¹ w(y) (π/2 + arcsin y) / √(1 - y²) dy = ∫₀^{π/2} w(sin φ) (π/2 + φ) dφ` for any `w`. -/
public theorem integral_mul_arcsin_div_sqrt (w : ℝ → ℝ) :
    ∫ y in (0 : ℝ)..1, w y * ((π / 2 + arcsin y) / √(1 - y ^ 2)) =
      ∫ φ in (0 : ℝ)..(π / 2), w (sin φ) * (π / 2 + φ) := by
  have hπ : (0 : ℝ) ≤ π / 2 := by positivity
  have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg (a := 0) (b := π / 2)
    (f := sin) (f' := cos) (g := fun y ↦ w y * ((π / 2 + arcsin y) / √(1 - y ^ 2)))
    continuous_sin.continuousOn (fun x _ ↦ hasDerivAt_sin x) fun x hx ↦ by
      rw [min_eq_left hπ, max_eq_right hπ] at hx
      exact cos_nonneg_of_mem_Icc ⟨by linarith [hx.1, pi_pos], hx.2.le⟩
  rw [sin_zero, sin_pi_div_two] at h
  rw [← h, intervalIntegral.integral_of_le hπ, intervalIntegral.integral_of_le hπ,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun φ hφ ↦ ?_
  have hc : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith [hφ.1, pi_pos], hφ.2⟩
  simp only [comp_apply]
  rw [arcsin_sin (by linarith [hφ.1, pi_pos]) hφ.2.le, ← cos_sq', Real.sqrt_sq hc.le]
  field_simp

/-- Let `s ≥ 2`, and let `w ≥ 0` on `(0, 1]` be measurable with the moments
`∫₀¹ yⁿ w(y) dy = 1/(n+1)^s`. Then
`∫₀¹ Li_s(x) / (x √(1 - x²)) dx = ∫₀^{π/2} w(sin φ) (π/2 + φ) dφ`. -/
public theorem integral_Lir_div_mul_sqrt {s : ℕ} (hs : 2 ≤ s) {w : ℝ → ℝ} (hw : Measurable w)
    (hw0 : ∀ y ∈ Ioc (0 : ℝ) 1, 0 ≤ w y)
    (hint : ∀ n : ℕ, IntegrableOn (fun y ↦ y ^ n * w y) (Ioc 0 1))
    (hmom : ∀ n : ℕ, ∫ y in (0 : ℝ)..1, y ^ n * w y = 1 / ((n : ℝ) + 1) ^ s) :
    ∫ x in (0 : ℝ)..1, Lir s x / (x * √(1 - x ^ 2)) =
      ∫ φ in (0 : ℝ)..(π / 2), w (sin φ) * (π / 2 + φ) := by
  rw [integral_Lir_div_mul_sqrt_eq_integral_arcsin hs hw hw0 hint hmom,
    integral_mul_arcsin_div_sqrt]

end LeanPolyLog.Arcsin
