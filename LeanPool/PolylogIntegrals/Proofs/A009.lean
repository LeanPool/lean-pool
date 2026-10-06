/-
Copyright (c) 2026 rainrzk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: rainrzk
-/
module

public import LeanPool.PolylogIntegrals.Proofs.A006
public import LeanPool.PolylogIntegrals.Proofs.A007

/-!
# A009: `∫₀^{π/2} x² cot x dx = (π²/4) log 2 - (7/8) ζ(3)`

Let `J = ∫₀^{π/2} x log sin x dx`.

* Split `[0, π/2]` at `π/4`. With `x ↦ π/2 - x` the upper half is
  `∫₀^{π/4} (π/2 - u) log cos u du`.
* On the lower half, `sin x = sin 2x / (2 cos x)`, and `u = 2x` gives
  `∫₀^{π/4} x log sin 2x dx = J/4`.
* Together: `(3/4) J = -(π²/32) log 2 - 2 ∫₀^{π/4} x log cos x + (π/2) ∫₀^{π/4} log cos x`, so
  A006 and A007 give `J = -(π²/8) log 2 + (7/16) ζ(3)`.

Finally `F x = x² log sin x` is continuous on `[0, π/2]` (it tends to `0` at `0`), vanishes at both
ends, and has derivative `2x log sin x + x² cot x` on `(0, π/2)`. Hence `A009 = -2J`.

In Lean `cot 0 = 0` and `log 0 = 0`; single points do not affect the integrals. The helper
lemmas and `integral_mul_log_sin` (the value of `J`) are public, and A011 reuses them.
-/

open Real MeasureTheory Set Filter Topology

namespace LeanPolyLog.Proofs

/-- `x² ≤ (π²/4) sin x` on `[0, π/2]`, from Jordan's inequality `(2/π) x ≤ sin x`. -/
public theorem sq_le_mul_sin {x : ℝ} (hx : x ∈ Icc 0 (π / 2)) : x ^ 2 ≤ π ^ 2 / 4 * sin x := by
  have hj := mul_le_sin hx.1 hx.2
  calc x ^ 2 ≤ π / 2 * x := by nlinarith [hx.1, hx.2]
    _ = π ^ 2 / 4 * (2 / π * x) := by field_simp; ring
    _ ≤ π ^ 2 / 4 * sin x := by gcongr

/-- `x ↦ x² log sin x` is continuous on `[0, π/2]`. At `0` it tends to `0`, because
`|x² log sin x| ≤ (π²/4) |sin x log sin x|` there. -/
public theorem continuousOn_sq_mul_log_sin :
    ContinuousOn (fun x : ℝ ↦ x ^ 2 * log (sin x)) (Icc 0 (π / 2)) := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with rfl | hx0
  · have hg : Tendsto (fun x ↦ π ^ 2 / 4 * ‖sin x * log (sin x)‖) (𝓝[Icc 0 (π / 2)] 0)
        (𝓝 0) := by
      have h := ((continuous_mul_log.comp continuous_sin).tendsto 0).norm.const_mul (π ^ 2 / 4)
      simp only [Function.comp_apply, sin_zero, log_zero, mul_zero, norm_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    rw [ContinuousWithinAt]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
    refine squeeze_zero_norm' ?_ hg
    filter_upwards [self_mem_nhdsWithin] with y hy
    rw [norm_mul, norm_mul, ← mul_assoc]
    gcongr
    rw [Real.norm_of_nonneg (sq_nonneg y),
      Real.norm_of_nonneg (sin_nonneg_of_nonneg_of_le_pi hy.1 (by linarith [hy.2, pi_pos]))]
    exact sq_le_mul_sin hy
  · have hs : sin x ≠ 0 := (sin_pos_of_pos_of_lt_pi hx0 (by linarith [hx.2, pi_pos])).ne'
    exact ((continuousAt_id.pow 2).mul (continuous_sin.continuousAt.log hs)).continuousWithinAt

/-- `x² cot x` is integrable on `[0, π/2]`, since it is bounded by `π²/4` there. -/
public theorem intervalIntegrable_sq_mul_cot :
    IntervalIntegrable (fun x : ℝ ↦ x ^ 2 * cot x) volume 0 (π / 2) := by
  have hπ : (0 : ℝ) ≤ π / 2 := by positivity
  have hcot : (fun x : ℝ ↦ x ^ 2 * cot x) = fun x ↦ x ^ 2 * (cos x / sin x) := by
    ext x
    rw [cot_eq_cos_div_sin]
  rw [hcot]
  refine (intervalIntegrable_const (c := π ^ 2 / 4)).mono_fun' ?_ ?_
  · exact (by fun_prop : Measurable fun x : ℝ ↦ x ^ 2 * (cos x / sin x)).aestronglyMeasurable
  · rw [uIoc_of_le hπ]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hs : 0 < sin x := sin_pos_of_pos_of_lt_pi hx.1 (by linarith [hx.2, pi_pos])
    rw [norm_mul, norm_div, Real.norm_of_nonneg (sq_nonneg x), Real.norm_of_nonneg hs.le]
    calc x ^ 2 * (‖cos x‖ / sin x) ≤ x ^ 2 * (1 / sin x) := by
          gcongr
          exact abs_cos_le_one x
      _ = x ^ 2 / sin x := by ring
      _ ≤ π ^ 2 / 4 := by
          rw [div_le_iff₀ hs]
          exact sq_le_mul_sin ⟨hx.1.le, hx.2⟩

/-- `∫₀^{π/2} x log sin x dx = -(π²/8) log 2 + (7/16) ζ(3)`. -/
public theorem integral_mul_log_sin :
    ∫ x in (0 : ℝ)..(π / 2), x * log (sin x) = -(π ^ 2 / 8 * log 2) + 7 / 16 * zeta3 := by
  set J := ∫ x in (0 : ℝ)..(π / 2), x * log (sin x) with hJ
  have hπ : (0 : ℝ) ≤ π / 4 := by positivity
  have hcos : ∀ x ∈ uIcc (0 : ℝ) (π / 4), 0 < cos x := by
    intro x hx
    rw [uIcc_of_le hπ] at hx
    apply cos_pos_of_mem_Ioo
    constructor <;> linarith [hx.1, hx.2, pi_pos]
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun x ↦ x * log (sin x)) volume a b :=
    fun _ _ ↦ intervalIntegrable_log_sin.continuousOn_mul continuousOn_id
  have hC : IntervalIntegrable (fun x ↦ x * log (cos x)) volume 0 (π / 4) :=
    ContinuousOn.intervalIntegrable fun x hx ↦
      (continuousAt_id.mul (continuous_cos.continuousAt.log (hcos x hx).ne')).continuousWithinAt
  have hD : IntervalIntegrable (fun x ↦ log (cos x)) volume 0 (π / 4) :=
    intervalIntegrable_log_cos
  -- the upper half `[π/4, π/2]`
  have hupper : ∫ x in (π / 4)..(π / 2), x * log (sin x) =
      π / 2 * (∫ x in (0 : ℝ)..(π / 4), log (cos x)) -
        ∫ x in (0 : ℝ)..(π / 4), x * log (cos x) := by
    have h := intervalIntegral.integral_comp_sub_left (a := 0) (b := π / 4)
      (fun x ↦ x * log (sin x)) (π / 2)
    rw [show π / 2 - π / 4 = π / 4 by ring, sub_zero] at h
    rw [← h]
    simp_rw [sin_pi_div_two_sub, sub_mul]
    rw [intervalIntegral.integral_sub (hD.const_mul _) hC, intervalIntegral.integral_const_mul]
  -- the lower half `[0, π/4]`
  have heq : EqOn (fun x ↦ x * log (sin x))
      (fun x ↦ 1 / 2 * (2 * x * log (sin (2 * x))) - log 2 * x - x * log (cos x))
      (uIcc 0 (π / 4)) := by
    intro x hx
    have hc := (hcos x hx).ne'
    rw [uIcc_of_le hπ] at hx
    rcases eq_or_lt_of_le hx.1 with rfl | hx0
    · simp
    have hs : sin x ≠ 0 := (sin_pos_of_pos_of_lt_pi hx0 (by linarith [hx.2, pi_pos])).ne'
    simp only
    rw [sin_two_mul, log_mul (mul_ne_zero two_ne_zero hs) hc, log_mul two_ne_zero hs]
    ring
  have hA : IntervalIntegrable (fun x ↦ 1 / 2 * (2 * x * log (sin (2 * x)))) volume 0
      (π / 4) := by
    have h := (hint 0 (π / 2)).comp_mul_left (c := 2)
    rw [zero_div, show π / 2 / 2 = π / 4 by ring] at h
    exact h.const_mul _
  have hB : IntervalIntegrable (fun x : ℝ ↦ log 2 * x) volume 0 (π / 4) :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  have h2 : ∫ x in (0 : ℝ)..(π / 4), 2 * x * log (sin (2 * x)) = J / 2 := by
    have h := intervalIntegral.integral_comp_mul_left (a := 0) (b := π / 4)
      (fun x ↦ x * log (sin x)) (two_ne_zero (α := ℝ))
    rw [mul_zero, show 2 * (π / 4) = π / 2 by ring, smul_eq_mul] at h
    rw [h, hJ]
    ring
  have hlower : ∫ x in (0 : ℝ)..(π / 4), x * log (sin x) =
      J / 4 - π ^ 2 / 32 * log 2 - ∫ x in (0 : ℝ)..(π / 4), x * log (cos x) := by
    rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_sub (hA.sub hB) hC,
      intervalIntegral.integral_sub hA hB, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, h2, integral_id]
    ring
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hint 0 (π / 4))
    (hint (π / 4) (π / 2))
  rw [hupper, hlower, A006_cos, A007] at hsplit
  linarith

/-- A009: `∫₀^{π/2} x² cot x dx = (π²/4) log 2 - (7/8) ζ(3)`. -/
public theorem A009 :
    ∫ x in (0 : ℝ)..(π / 2), x ^ 2 * Real.cot x = π ^ 2 / 4 * Real.log 2 - 7 / 8 * zeta3 := by
  have hπ : (0 : ℝ) ≤ π / 2 := by positivity
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) (π / 2), HasDerivAt (fun x ↦ x ^ 2 * log (sin x))
      (2 * (x * log (sin x)) + x ^ 2 * cot x) x := by
    intro x hx
    have hs : sin x ≠ 0 := (sin_pos_of_pos_of_lt_pi hx.1 (by linarith [hx.2, pi_pos])).ne'
    convert (hasDerivAt_pow 2 x).mul ((hasDerivAt_sin x).log hs) using 1
    rw [cot_eq_cos_div_sin]
    push_cast
    ring
  have hint1 : IntervalIntegrable (fun x ↦ 2 * (x * log (sin x))) volume 0 (π / 2) :=
    (intervalIntegrable_log_sin.continuousOn_mul continuousOn_id).const_mul 2
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hπ
    continuousOn_sq_mul_log_sin hderiv (hint1.add intervalIntegrable_sq_mul_cot)
  rw [intervalIntegral.integral_add hint1 intervalIntegrable_sq_mul_cot,
    intervalIntegral.integral_const_mul, integral_mul_log_sin, sin_pi_div_two, log_one,
    mul_zero] at hFTC
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, sub_zero]
    at hFTC
  linear_combination hFTC

end LeanPolyLog.Proofs
