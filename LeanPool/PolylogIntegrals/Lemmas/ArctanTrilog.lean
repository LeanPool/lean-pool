/-
Copyright (c) 2026 rainrzk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: rainrzk
-/
module

public import LeanPool.PolylogIntegrals.Lemmas.Arctan

/-!
# The trilogarithm, `log²` moments and a symmetric double integral

This file collects the lemmas behind A013, one power of `log` higher than
`LeanPool.PolylogIntegrals.Lemmas.Arctan`.

## Main results

* `LeanPolyLog.Arctan.integral_pow_mul_log_sq`: `∫₀¹ tᵐ log² t dt = 2/(m+1)³`.
* `LeanPolyLog.Arctan.integral_mul_log_sq_div_one_add_mul`: for `0 ≤ x ≤ 1`,
  `∫₀¹ x log² y/(1 + xy) dy = -2 Li₃(-x)`.
* `LeanPolyLog.Arctan.Lir_three_one`, `LeanPolyLog.Arctan.Lir_three_neg_one`: `Li₃(1) = ζ(3)` and
  `Li₃(-1) = -(3/4) ζ(3)`.
* `LeanPolyLog.Arctan.hasSum_eta_three`, `LeanPolyLog.Arctan.hasSum_beta_three`:
  `η(3) = ∑ (-1)ⁿ/(n+1)³ = (3/4) ζ(3)` and `β(3) = ∑ (-1)ᵏ/(2k+1)³ = π³/32`.
* `LeanPolyLog.Arctan.integral_log_sq_div_one_add_sq`,
  `LeanPolyLog.Arctan.integral_mul_log_sq_div_one_add_sq`: `∫₀¹ log² y/(1+y²) dy = π³/16` and
  `∫₀¹ y log² y/(1+y²) dy = (3/16) ζ(3)`.
* `LeanPolyLog.Arctan.integral_log_mul_Lir_two_neg_div_one_add_sq`:
  `∫₀¹ log x · Li₂(-x)/(1+x²) dx = π² G/48`.
* `LeanPolyLog.Arctan.hasDerivAt_trilog_primitive`: on `(0, 1)`,
  `-2 Li₃(-x) + 2 log x · Li₂(-x) + log(1+x) log² x` is an antiderivative of `log² x/(1+x)`; it is
  continuous on `[0, 1]` by `LeanPolyLog.Arctan.continuousOn_log_mul_Lir_two_neg` and
  `LeanPolyLog.Arctan.continuousOn_log_one_add_mul_log_sq`.

## Proof sketch

* The `log²` moments come from the antiderivative
  `t^(m+1) (log² t/(m+1) - 2 log t/(m+1)² + 2/(m+1)³)`, which is continuous at `0` because
  `t log² t = 4 (√t log √t)²` for `t ≥ 0`.
* `Li₃(-1)` follows from the duplication formula `Li₃(1) = 4 (Li₃(1) + Li₃(-1))`, and `β(3)` is
  Mathlib's `hasSum_L_function_mod_four_eval_three`, restricted to the odd indices.
* For the double integral, write `Li₂(-x) = ∫₀¹ x log y/(1+xy) dy`. The integrand
  `f(x, y) = x log x log y/((1+x²)(1+xy))` is bounded by `|log x| |log y|` on `(0, 1]²`, and
  `f(x, y) + f(y, x) = (x log x/(1+x²)) (log y/(1+y²)) + (log x/(1+x²)) (y log y/(1+y²))`.
  Swapping the variables gives twice the integral as a sum of two products of single integrals,
  `2 (-π²/48)(-G)`.
* Continuity at `0`: `log x · Li₂(-x) = -(x log x) ∑ (-x)ⁿ/(n+1)²`, and
  `0 ≤ log(1+x) log² x ≤ x log² x` on `[0, 1]`.
-/

open Real MeasureTheory Set Filter Topology

namespace LeanPolyLog.Arctan

/-! ### The moments `∫₀¹ tᵐ log² t dt` -/

/-- `t log² t` is continuous on `[0, ∞)`: there it equals `4 (√t log √t)²`. -/
public theorem continuousOn_mul_log_sq : ContinuousOn (fun t : ℝ ↦ t * log t ^ 2) (Ici 0) := by
  have h : Continuous fun t : ℝ ↦ 4 * (√t * log √t) ^ 2 :=
    continuous_const.mul ((continuous_mul_log.comp continuous_sqrt).pow 2)
  refine h.continuousOn.congr fun t ht ↦ ?_
  dsimp only
  rw [log_sqrt ht, mul_pow, sq_sqrt ht]
  ring

/-- An antiderivative of `tᵐ log² t`, namely
`t^(m+1) log² t/(m+1) - 2 t^(m+1) log t/(m+1)² + 2 t^(m+1)/(m+1)³`. It is continuous on `[0, 1]`
and vanishes at `0`. -/
@[expose] public noncomputable def powMulLogSqPrimitive (m : ℕ) (t : ℝ) : ℝ :=
  t ^ (m + 1) * log t ^ 2 / ((m : ℝ) + 1) - 2 * (t ^ (m + 1) * log t) / ((m : ℝ) + 1) ^ 2 +
    2 * t ^ (m + 1) / ((m : ℝ) + 1) ^ 3

/-- Away from `0`, the derivative of `powMulLogSqPrimitive m` is `tᵐ log² t`. -/
public theorem hasDerivAt_powMulLogSqPrimitive (m : ℕ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (powMulLogSqPrimitive m) (t ^ m * log t ^ 2) t := by
  have hl := hasDerivAt_log ht
  have hp := hasDerivAt_pow (m + 1) t
  have h1 := (hp.mul (hl.pow 2)).div_const ((m : ℝ) + 1)
  have h2 := ((hp.mul hl).const_mul 2).div_const (((m : ℝ) + 1) ^ 2)
  have h3 := (hp.const_mul 2).div_const (((m : ℝ) + 1) ^ 3)
  refine ((h1.sub h2).add h3).congr_deriv ?_
  simp only [Nat.add_sub_cancel, Pi.pow_apply]
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp
  rw [pow_succ]
  field_simp
  ring

/-- `powMulLogSqPrimitive m` is continuous on `[0, 1]`. -/
public theorem continuousOn_powMulLogSqPrimitive (m : ℕ) :
    ContinuousOn (powMulLogSqPrimitive m) (Icc 0 1) := by
  have h1 : ContinuousOn (fun t : ℝ ↦ t ^ (m + 1) * log t ^ 2) (Icc 0 1) :=
    (((continuous_pow m).continuousOn.mul (continuousOn_mul_log_sq.mono Icc_subset_Ici_self))).congr
      fun t _ ↦ by simp only [Pi.mul_apply]; ring
  unfold powMulLogSqPrimitive
  refine ((h1.div_const _).sub ?_).add ?_
  · exact (continuousOn_const.mul (LogTrig.continuous_pow_succ_mul_log m).continuousOn).div_const _
  · exact (continuousOn_const.mul (continuous_pow (m + 1)).continuousOn).div_const _

/-- `tᵐ log² t` is integrable on `[0, 1]`: it is the nonnegative derivative of a continuous
function. -/
public theorem intervalIntegrable_pow_mul_log_sq (m : ℕ) :
    IntervalIntegrable (fun t : ℝ ↦ t ^ m * log t ^ 2) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  exact intervalIntegral.integrableOn_deriv_of_nonneg (continuousOn_powMulLogSqPrimitive m)
    (fun t ht ↦ hasDerivAt_powMulLogSqPrimitive m ht.1.ne')
    (fun t ht ↦ mul_nonneg (pow_nonneg ht.1.le m) (sq_nonneg _))

/-- `∫₀¹ tᵐ log² t dt = 2/(m+1)³`. -/
public theorem integral_pow_mul_log_sq (m : ℕ) :
    ∫ t in (0 : ℝ)..1, t ^ m * log t ^ 2 = 2 / ((m : ℝ) + 1) ^ 3 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
    (continuousOn_powMulLogSqPrimitive m)
    (fun t ht ↦ hasDerivAt_powMulLogSqPrimitive m ht.1.ne')
    (intervalIntegrable_pow_mul_log_sq m)]
  simp [powMulLogSqPrimitive]

/-- `∫₀¹ ‖tᵐ log² t‖ dt = 2/(m+1)³`. -/
public theorem integral_norm_pow_mul_log_sq (m : ℕ) :
    ∫ t in (0 : ℝ)..1, ‖t ^ m * log t ^ 2‖ = 2 / ((m : ℝ) + 1) ^ 3 := by
  rw [← integral_pow_mul_log_sq m]
  refine intervalIntegral.integral_congr fun t ht ↦ ?_
  rw [uIcc_of_le zero_le_one] at ht
  exact Real.norm_of_nonneg (mul_nonneg (pow_nonneg ht.1 m) (sq_nonneg _))

/-! ### The trilogarithm as an integral -/

/-- For `0 ≤ x ≤ 1`: `∫₀¹ x log² y/(1 + xy) dy = -2 Li₃(-x)`. -/
public theorem integral_mul_log_sq_div_one_add_mul {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∫ y in (0 : ℝ)..1, x * log y ^ 2 / (1 + x * y) = -2 * Lir 3 (-x) := by
  have hs : Summable fun n : ℕ ↦ 2 / ((n : ℝ) + 1) ^ 3 :=
    ((Dilog.summable_one_div_succ_pow (by norm_num : 2 ≤ 3)).mul_left 2).congr fun n ↦ by ring
  have h := hasSum_integral_mul_div_one_add_mul hx0 hx1 intervalIntegrable_pow_mul_log_sq
    (by simpa only [integral_norm_pow_mul_log_sq] using hs)
  simp only [integral_pow_mul_log_sq] at h
  refine h.unique ?_
  convert (Dilog.hasSum_Lir (by norm_num : 2 ≤ 3) (x := -x)
    (by rw [abs_neg, abs_of_nonneg hx0]; exact hx1)).mul_left (-2) using 1
  ext n
  rw [pow_succ]
  field_simp
  ring

/-! ### `ζ(3)`-type values -/

/-- `Li₃(1) = ζ(3)`. -/
public theorem Lir_three_one : Lir 3 1 = zeta3 := by
  simp [Lir, zeta3]

/-- `Li₃(-1) = -η(3) = -(3/4) ζ(3)`, from the duplication formula at `x = 1`. -/
public theorem Lir_three_neg_one : Lir 3 (-1) = -(3 / 4 * zeta3) := by
  have h := Dilog.Lir_sq (s := 3) (by norm_num) (x := 1) (by norm_num)
  rw [one_pow, Lir_three_one] at h
  norm_num at h
  linarith

/-- The Dirichlet eta function at `3`: `η(3) = ∑_{n ≥ 0} (-1)ⁿ/(n+1)³ = (3/4) ζ(3)`. -/
public theorem hasSum_eta_three :
    HasSum (fun n : ℕ ↦ (-1 : ℝ) ^ n / ((n : ℝ) + 1) ^ 3) (3 / 4 * zeta3) := by
  have h := (Dilog.hasSum_Lir (by norm_num : 2 ≤ 3) (x := -1) (by norm_num)).neg
  rw [Lir_three_neg_one, neg_neg] at h
  convert h using 1
  ext n
  rw [pow_succ]
  ring

/-- The Dirichlet beta function at `3`: `β(3) = ∑_{k ≥ 0} (-1)ᵏ/(2k+1)³ = π³/32`. -/
public theorem hasSum_beta_three :
    HasSum (fun k : ℕ ↦ (-1 : ℝ) ^ k / (2 * (k : ℝ) + 1) ^ 3) (π ^ 3 / 32) := by
  have h := hasSum_L_function_mod_four_eval_three
  rw [← (show Function.Injective fun k : ℕ ↦ 2 * k + 1 from fun a b hab ↦ by simpa using hab
    ).hasSum_iff] at h
  · convert h using 1
    ext k
    simp only [Function.comp]
    push_cast
    rw [show π * (2 * (k : ℝ) + 1) / 2 = k * π + π / 2 by ring, sin_add_pi_div_two,
      cos_nat_mul_pi]
    ring
  · intro n hn
    obtain ⟨k, rfl⟩ : Even n := by
      rcases Nat.even_or_odd n with he | ⟨k, rfl⟩
      · exact he
      · exact absurd ⟨k, rfl⟩ hn
    push_cast
    rw [show π * ((k : ℝ) + k) / 2 = k * π by ring, sin_nat_mul_pi, mul_zero]

/-! ### Two more integrals against `1/(1+y²)` -/

/-- `∫₀¹ log² y/(1+y²) dy = 2 β(3) = π³/16`. -/
public theorem integral_log_sq_div_one_add_sq :
    ∫ y in (0 : ℝ)..1, log y ^ 2 / (1 + y ^ 2) = π ^ 3 / 16 := by
  have h := hasSum_integral_div_one_add_sq (ψ := fun y ↦ log y ^ 2)
    (fun n ↦ intervalIntegrable_pow_mul_log_sq (2 * n))
    (by
      simp only [integral_norm_pow_mul_log_sq]
      have hi : Function.Injective fun n : ℕ ↦ 2 * n := fun a b hab ↦ by simpa using hab
      exact ((Dilog.summable_one_div_succ_pow (by norm_num : 2 ≤ 3)).mul_left 2).comp_injective hi
        |>.congr fun n ↦ by simp only [Function.comp_apply]; ring)
  simp only [integral_pow_mul_log_sq] at h
  refine h.unique ?_
  convert hasSum_beta_three.mul_left 2 using 1
  · ext n
    push_cast
    ring
  · ring

/-- `∫₀¹ y log² y/(1+y²) dy = η(3)/4 = (3/16) ζ(3)`. -/
public theorem integral_mul_log_sq_div_one_add_sq :
    ∫ y in (0 : ℝ)..1, y * log y ^ 2 / (1 + y ^ 2) = 3 / 16 * zeta3 := by
  have hpow : ∀ (n : ℕ) (y : ℝ), y ^ (2 * n) * (y * log y ^ 2) = y ^ (2 * n + 1) * log y ^ 2 :=
    fun n y ↦ by ring
  have h := hasSum_integral_div_one_add_sq (ψ := fun y ↦ y * log y ^ 2)
    (fun n ↦ by simpa only [hpow] using intervalIntegrable_pow_mul_log_sq (2 * n + 1))
    (by
      simp only [hpow, integral_norm_pow_mul_log_sq]
      have hi : Function.Injective fun n : ℕ ↦ 2 * n + 1 := fun a b hab ↦ by simpa using hab
      exact ((Dilog.summable_one_div_succ_pow (by norm_num : 2 ≤ 3)).mul_left 2).comp_injective hi
        |>.congr fun n ↦ by simp only [Function.comp_apply]; ring)
  simp only [hpow, integral_pow_mul_log_sq] at h
  refine h.unique ?_
  convert hasSum_eta_three.mul_left (1 / 4) using 1
  · ext n
    push_cast
    field_simp
    ring
  · ring

/-! ### The symmetric double integral -/

/-- `∫₀¹ log x · Li₂(-x)/(1+x²) dx = π² G/48`.

With `Li₂(-x) = ∫₀¹ x log y/(1+xy) dy` this is the integral of
`f(x, y) = x log x log y/((1+x²)(1+xy))` over the square, which equals that of `f(y, x)`; and
`f(x, y) + f(y, x) = (x log x/(1+x²)) (log y/(1+y²)) + (log x/(1+x²)) (y log y/(1+y²))`. -/
public theorem integral_log_mul_Lir_two_neg_div_one_add_sq :
    ∫ x in (0 : ℝ)..1, log x * Lir 2 (-x) / (1 + x ^ 2) = π ^ 2 * G / 48 := by
  set μ : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod volume with hμ
  set S : Set (ℝ × ℝ) := Ioc 0 1 ×ˢ Ioc 0 1 with hS
  set f : ℝ × ℝ → ℝ := fun z ↦ z.1 / ((1 + z.1 ^ 2) * (1 + z.1 * z.2)) * (log z.1 * log z.2)
    with hf
  set a : ℝ → ℝ := fun t ↦ t * log t / (1 + t ^ 2) with ha
  set b : ℝ → ℝ := fun t ↦ log t / (1 + t ^ 2) with hb
  have hlog : Integrable (fun t : ℝ ↦ log t) (volume.restrict (Ioc 0 1)) :=
    intervalIntegral.intervalIntegrable_log'.1
  have ia : Integrable a (volume.restrict (Ioc 0 1)) :=
    (continuous_mul_log.div (by fun_prop) fun t ↦ by positivity).integrableOn_Ioc
  have ib : Integrable b (volume.restrict (Ioc 0 1)) := by
    have h := intervalIntegral.intervalIntegrable_log'.mul_continuousOn
      (g := fun y : ℝ ↦ (1 + y ^ 2)⁻¹) (a := 0) (b := 1) continuous_inv_one_add_sq.continuousOn
    have h' : IntegrableOn (fun t : ℝ ↦ log t / (1 + t ^ 2)) (Ioc 0 1) := by
      simpa only [div_eq_mul_inv] using h.1
    exact h'
  -- `f` is integrable on the square, dominated by `|log x| |log y|`
  have hfi : IntegrableOn f S μ := by
    rw [IntegrableOn, hμ, hS, ← Measure.prod_restrict]
    refine (hlog.norm.mul_prod hlog.norm).mono' ?_ ?_
    · exact (by fun_prop : Measurable f).aestronglyMeasurable
    · rw [Measure.prod_restrict]
      filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with z hz
      obtain ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩ := hz
      simp only [hf, norm_mul]
      refine mul_le_of_le_one_left (by positivity) ?_
      rw [Real.norm_of_nonneg (by positivity), div_le_one (by positivity)]
      have hxy := mul_pos hx0 hy0
      nlinarith [sq_nonneg z.1, mul_nonneg (sq_nonneg z.1) hxy.le]
  have h1 : ∫ x in (0 : ℝ)..1, log x * Lir 2 (-x) / (1 + x ^ 2) = ∫ z in S, f z ∂μ := by
    rw [setIntegral_prod f hfi, intervalIntegral.integral_of_le zero_le_one]
    refine setIntegral_congr_fun measurableSet_Ioc fun x hx ↦ ?_
    rw [← integral_mul_log_div_one_add_mul hx.1.le hx.2,
      intervalIntegral.integral_of_le zero_le_one, mul_div_right_comm, ← integral_const_mul]
    congr 1
    ext y
    simp only [hf, div_eq_mul_inv, mul_inv]
    ring
  have h2 : ∫ z in S, f z.swap ∂μ = ∫ z in S, f z ∂μ := setIntegral_prod_swap _ _ f
  have h3 : ∫ z in S, (f z + f z.swap) ∂μ = ∫ z in S, (a z.1 * b z.2 + b z.1 * a z.2) ∂μ := by
    refine setIntegral_congr_fun (measurableSet_Ioc.prod measurableSet_Ioc) fun z hz ↦ ?_
    obtain ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩ := hz
    simp only [hf, ha, hb, Prod.fst_swap, Prod.snd_swap]
    have h1x : 0 < 1 + z.1 * z.2 := by positivity
    have h1y : 0 < 1 + z.2 * z.1 := by positivity
    field_simp
    ring
  have h4 : ∫ z in S, (a z.1 * b z.2 + b z.1 * a z.2) ∂μ =
      2 * ((∫ t in Ioc (0 : ℝ) 1, a t) * ∫ t in Ioc (0 : ℝ) 1, b t) := by
    have iab : IntegrableOn (fun z : ℝ × ℝ ↦ a z.1 * b z.2) S μ := by
      rw [IntegrableOn, hμ, hS, ← Measure.prod_restrict]
      exact ia.mul_prod ib
    have iba : IntegrableOn (fun z : ℝ × ℝ ↦ b z.1 * a z.2) S μ := by
      rw [IntegrableOn, hμ, hS, ← Measure.prod_restrict]
      exact ib.mul_prod ia
    rw [integral_add iab iba, hμ, hS, setIntegral_prod_mul, setIntegral_prod_mul]
    ring
  have hA : ∫ t in Ioc (0 : ℝ) 1, a t = -(π ^ 2 / 48) := by
    rw [← intervalIntegral.integral_of_le zero_le_one]
    exact integral_mul_log_div_one_add_sq
  have hB : ∫ t in Ioc (0 : ℝ) 1, b t = -G := by
    rw [← intervalIntegral.integral_of_le zero_le_one]
    exact integral_log_div_one_add_sq
  have hsum := integral_add hfi hfi.swap
  simp only [Function.comp_def] at hsum
  rw [h3, h4, hA, hB, h2] at hsum
  rw [h1]
  linarith

/-! ### Continuity of the pieces of the antiderivative at `0` -/

/-- `x ↦ ∑ (-x)ⁿ/(n+1)²` is continuous on `[0, 1]` (Weierstrass M-test). -/
public theorem continuousOn_tsum_neg_pow_div_sq :
    ContinuousOn (fun x : ℝ ↦ ∑' n : ℕ, (-x) ^ n / ((n : ℝ) + 1) ^ 2) (Icc 0 1) := by
  refine continuousOn_tsum (fun n ↦ by fun_prop) (Dilog.summable_one_div_succ_pow le_rfl)
    fun n x hx ↦ ?_
  rw [norm_div, norm_pow, norm_neg, Real.norm_of_nonneg hx.1, Real.norm_of_nonneg (by positivity)]
  exact div_le_div_of_nonneg_right (pow_le_one₀ hx.1 hx.2) (by positivity)

/-- `Li₂(-x) = -x ∑ (-x)ⁿ/(n+1)²`. -/
public theorem Lir_two_neg_eq (x :
    ℝ) : Lir 2 (-x) = -x * ∑' n : ℕ, (-x) ^ n / ((n : ℝ) + 1) ^ 2 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [Dilog.tsum_pow_div_pow_eq_div 2 (neg_ne_zero.2 hx)]
    unfold Lir
    field_simp

/-- `x ↦ log x · Li₂(-x)` is continuous on `[0, 1]`: it equals `-(x log x) ∑ (-x)ⁿ/(n+1)²`. -/
public theorem continuousOn_log_mul_Lir_two_neg :
    ContinuousOn (fun x ↦ log x * Lir 2 (-x)) (Icc 0 1) := by
  refine ((continuous_mul_log.continuousOn.mul continuousOn_tsum_neg_pow_div_sq).neg).congr
    fun x _ ↦ ?_
  simp only [Pi.neg_apply, Pi.mul_apply]
  rw [Lir_two_neg_eq]
  ring

/-- `x ↦ log(1+x) log² x` is continuous on `[0, 1]`: at `0` it is squeezed between `0` and
`x log² x`. -/
public theorem continuousOn_log_one_add_mul_log_sq :
    ContinuousOn (fun x : ℝ ↦ log (1 + x) * log x ^ 2) (Icc 0 1) := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with rfl | hx0
  · have hg : Tendsto (fun t : ℝ ↦ t * log t ^ 2) (𝓝[Icc 0 1] 0) (𝓝 0) := by
      have h := ((continuousOn_mul_log_sq 0 self_mem_Ici).mono
        (Icc_subset_Ici_self : Icc (0 : ℝ) 1 ⊆ Ici 0)).tendsto
      simpa using h
    rw [ContinuousWithinAt]
    simp only [add_zero, log_one, zero_mul]
    refine squeeze_zero' ?_ ?_ hg
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact mul_nonneg (log_nonneg (by linarith [ht.1])) (sq_nonneg _)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      linarith [log_le_sub_one_of_pos (by linarith [ht.1] : 0 < 1 + t)]
  · exact (((continuousAt_const.add continuousAt_id).log (by linarith : (0 : ℝ) < 1 + x).ne').mul
      ((continuousAt_log hx0.ne').pow 2)).continuousWithinAt

/-! ### An antiderivative of `log² x/(1+x)` -/

/-- On `(0, 1)`, `d/dx [-2 Li₃(-x) + 2 log x · Li₂(-x) + log(1+x) log² x] = log² x/(1+x)`. -/
public theorem hasDerivAt_trilog_primitive {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun x ↦ -2 * Lir 3 (-x) + 2 * (log x * Lir 2 (-x)) + log (1 + x) * log x ^ 2)
      (log x ^ 2 / (1 + x)) x := by
  have hx : |-x| < 1 := by rw [abs_neg, abs_of_pos hx0]; exact hx1
  have hnx : -x ≠ 0 := neg_ne_zero.2 hx0.ne'
  have h3 := (Dilog.hasDerivAt_Lir_succ 2 hx hnx).comp x (hasDerivAt_neg x)
  have h2 := (Dilog.hasDerivAt_Lir_two hx hnx).comp x (hasDerivAt_neg x)
  have hl := hasDerivAt_log hx0.ne'
  have hl1 := ((hasDerivAt_id' x).const_add 1).log (by linarith)
  refine (((h3.const_mul (-2)).add ((hl.mul h2).const_mul 2)).add
    (hl1.mul (hl.pow 2))).congr_deriv ?_
  simp only [Pi.pow_apply, Function.comp_apply]
  rw [sub_neg_eq_add]
  have : 1 + x ≠ 0 := by linarith
  field_simp
  ring

end LeanPolyLog.Arctan
