/-
Copyright (c) 2026 rainrzk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: rainrzk
-/
module

public import LeanPool.PolylogIntegrals.Lemmas.ArctanTrilog
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The integral `∫₀^{π/2} log² sin x dx`

This file proves `∫₀^{π/2} log² sin x dx = π³/24 + (π/2) log² 2`, which A015 and A016 use.

## Main results

* `LeanPolyLog.LogSinSq.intervalIntegrable_log_sin_sq`,
  `LeanPolyLog.LogSinSq.intervalIntegrable_log_cos_sq`,
  `LeanPolyLog.LogSinSq.intervalIntegrable_log_sin_sq_zero_pi`: `log² sin` is integrable on
  `[0, π/2]` and on `[0, π]`, and `log² cos` is integrable on `[0, π/2]`.
* `LeanPolyLog.LogSinSq.integral_log_cos_sq`: `∫₀^{π/2} log² cos = ∫₀^{π/2} log² sin`.
* `LeanPolyLog.LogSinSq.integral_log_sin_sq_zero_pi`: `∫₀^π log² sin = 2 ∫₀^{π/2} log² sin`.
* `LeanPolyLog.LogSinSq.integral_log_tan_sq`: `∫₀^{π/4} (log sin x - log cos x)² dx = π³/16`.
* `LeanPolyLog.LogSinSq.integral_log_sin_sq`: `∫₀^{π/2} log² sin x dx = π³/24 + (π/2) log² 2`.
* `LeanPolyLog.LogSinSq.integral_log_sin_mul_log_cos`:
  `∫₀^{π/2} log sin x · log cos x dx = (π/2) log² 2 - π³/48`.

## Proof sketch

Write `L = ∫₀^{π/2} log² sin` and `B = ∫₀^{π/2} log sin · log cos`; also `∫₀^{π/2} log² cos = L`
and `∫₀^{π/2} log cos = ∫₀^{π/2} log sin = -(π/2) log 2`.

* Integrability: Jordan's inequality `(2/π) x ≤ sin x ≤ 1` gives `log² sin x ≤ log² (2x/π)` on
  `(0, π/2]`, and `log²` is integrable on `[0, 1]`. The product `log sin · log cos` is bounded by
  `log² sin + log² cos`.
* `sin 2x = 2 sin x cos x`, and `u = 2x` together with `sin (π - u) = sin u` gives
  `∫₀^{π/2} log² sin 2x dx = L`. Expanding the square, `L = 2L - (3π/2) log² 2 + 2B`.
* On `[0, π/4]` the substitution `x = arctan t` turns `log sin x - log cos x` into `log t`, so
  `∫₀^{π/4} (log sin - log cos)² = ∫₀¹ log² t/(1+t²) dt = π³/16`. The reflection `x ↦ π/2 - x`
  doubles this to `∫₀^{π/2} (log sin - log cos)² = 2L - 2B = π³/8`.
* Solving the two linear equations gives `L` and `B`.
-/

open Real MeasureTheory Set

namespace LeanPolyLog.LogSinSq

/-! ### Integrability -/

/-- On `(0, π/2]`, Jordan's inequality gives `log² sin x ≤ log² (2x/π)`. -/
public theorem log_sin_sq_le {x : ℝ} (hx : x ∈ Ioc 0 (π / 2)) :
    log (sin x) ^ 2 ≤ log (2 / π * x) ^ 2 := by
  have hpos : 0 < 2 / π * x := by have := pi_pos; have := hx.1; positivity
  have hj : 2 / π * x ≤ sin x := mul_le_sin hx.1.le hx.2
  have h1 : log (2 / π * x) ≤ log (sin x) := log_le_log hpos hj
  have h2 : log (sin x) ≤ 0 := log_nonpos (hpos.le.trans hj) (sin_le_one x)
  nlinarith

/-- `log² (2x/π)` is integrable on `[0, π/2]`. -/
public theorem intervalIntegrable_log_sq_mul :
    IntervalIntegrable (fun x : ℝ ↦ log (2 / π * x) ^ 2) volume 0 (π / 2) := by
  have h1 : IntervalIntegrable (fun t : ℝ ↦ log t ^ 2) volume 0 1 := by
    simpa using Arctan.intervalIntegrable_pow_mul_log_sq 0
  have h2 := h1.comp_mul_left (c := 2 / π)
  rwa [zero_div, one_div_div] at h2

/-- `log² sin` is integrable on `[0, π/2]`. -/
public theorem intervalIntegrable_log_sin_sq :
    IntervalIntegrable (fun x ↦ log (sin x) ^ 2) volume 0 (π / 2) := by
  have hπ : (0 : ℝ) ≤ π / 2 := by positivity
  refine intervalIntegrable_log_sq_mul.mono_fun' ?_ ?_
  · exact ((measurable_log.comp measurable_sin).pow_const 2).aestronglyMeasurable
  · rw [uIoc_of_le hπ]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact log_sin_sq_le hx

/-- `log² cos` is integrable on `[0, π/2]`. -/
public theorem intervalIntegrable_log_cos_sq :
    IntervalIntegrable (fun x ↦ log (cos x) ^ 2) volume 0 (π / 2) := by
  have h := intervalIntegrable_log_sin_sq.comp_sub_left (π / 2)
  simp only [sin_pi_div_two_sub, sub_zero, sub_self] at h
  exact h.symm

/-- `log² sin` is integrable on `[0, π]`. -/
public theorem intervalIntegrable_log_sin_sq_zero_pi :
    IntervalIntegrable (fun x ↦ log (sin x) ^ 2) volume 0 π := by
  have h := intervalIntegrable_log_sin_sq.comp_sub_left π
  simp only [sin_pi_sub, sub_zero] at h
  rw [show π - π / 2 = π / 2 by ring] at h
  exact intervalIntegrable_log_sin_sq.trans h.symm

/-- `log sin · log cos` is integrable on `[0, π/2]`: it is bounded by `log² sin + log² cos`. -/
public theorem intervalIntegrable_log_sin_mul_log_cos :
    IntervalIntegrable (fun x ↦ log (sin x) * log (cos x)) volume 0 (π / 2) := by
  refine (intervalIntegrable_log_sin_sq.add intervalIntegrable_log_cos_sq).mono_fun' ?_ ?_
  · exact ((measurable_log.comp measurable_sin).mul
      (measurable_log.comp measurable_cos)).aestronglyMeasurable
  · refine ae_of_all _ fun x ↦ ?_
    simp only [norm_mul, Real.norm_eq_abs]
    nlinarith [sq_abs (log (sin x)), sq_abs (log (cos x)),
      sq_nonneg (|log (sin x)| - |log (cos x)|)]

/-! ### Symmetries -/

/-- `∫₀^{π/2} log² cos x dx = ∫₀^{π/2} log² sin x dx`, by `x ↦ π/2 - x`. -/
public theorem integral_log_cos_sq :
    ∫ x in (0 : ℝ)..(π / 2), log (cos x) ^ 2 = ∫ x in (0 : ℝ)..(π / 2), log (sin x) ^ 2 := by
  have h := intervalIntegral.integral_comp_sub_left (fun x ↦ log (sin x) ^ 2) (π / 2)
    (a := 0) (b := π / 2)
  simp only [sin_pi_div_two_sub, sub_zero, sub_self] at h
  exact h

/-- `∫₀^π log² sin x dx = 2 ∫₀^{π/2} log² sin x dx`, by `x ↦ π - x` on `[π/2, π]`. -/
public theorem integral_log_sin_sq_zero_pi :
    ∫ x in (0 : ℝ)..π, log (sin x) ^ 2 = 2 * ∫ x in (0 : ℝ)..(π / 2), log (sin x) ^ 2 := by
  have h := intervalIntegral.integral_comp_sub_left (fun x ↦ log (sin x) ^ 2) π
    (a := 0) (b := π / 2)
  simp only [sin_pi_sub, sub_zero] at h
  rw [show π - π / 2 = π / 2 by ring] at h
  have hi := intervalIntegrable_log_sin_sq
  have hi' : IntervalIntegrable (fun x ↦ log (sin x) ^ 2) volume (π / 2) π := by
    have := hi.comp_sub_left π
    simp only [sin_pi_sub, sub_zero] at this
    rw [show π - π / 2 = π / 2 by ring] at this
    exact this.symm
  rw [← intervalIntegral.integral_add_adjacent_intervals hi hi', ← h]
  ring

/-- `∫₀^{π/2} log sin x dx = ∫₀^{π/2} log cos x dx = -(π/2) log 2`. -/
public theorem integral_log_cos_zero_pi_div_two :
    ∫ x in (0 : ℝ)..(π / 2), log (cos x) = -(π / 2 * log 2) := by
  have h := intervalIntegral.integral_comp_sub_left (fun x ↦ log (sin x)) (π / 2)
    (a := 0) (b := π / 2)
  simp only [sin_pi_div_two_sub, sub_zero, sub_self] at h
  rw [h, integral_log_sin_zero_pi_div_two]
  ring

/-! ### The substitution `x = arctan t` -/

/-- `∫₀^{π/4} (log sin x - log cos x)² dx = ∫₀¹ log² t/(1+t²) dt = π³/16`. -/
public theorem integral_log_tan_sq :
    ∫ x in (0 : ℝ)..(π / 4), (log (sin x) - log (cos x)) ^ 2 = π ^ 3 / 16 := by
  have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg (a := 0) (b := 1)
    (f := arctan) (f' := fun t ↦ 1 / (1 + t ^ 2))
    (g := fun x ↦ (log (sin x) - log (cos x)) ^ 2)
    continuous_arctan.continuousOn (fun x _ ↦ hasDerivAt_arctan x) (fun x _ ↦ by positivity)
  rw [arctan_zero, arctan_one] at h
  rw [← h, ← Arctan.integral_log_sq_div_one_add_sq]
  congr 1
  ext t
  simp only [Function.comp, sin_arctan, cos_arctan]
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  · have hs : √(1 + t ^ 2) ≠ 0 := by positivity
    rw [log_div ht hs, one_div, log_inv]
    ring

/-- `∫₀^{π/2} (log sin x - log cos x)² dx = π³/8`: the reflection `x ↦ π/2 - x` maps
`[π/4, π/2]` onto `[0, π/4]` and swaps `sin` and `cos`. -/
public theorem integral_log_tan_sq_zero_pi_div_two :
    ∫ x in (0 : ℝ)..(π / 2), (log (sin x) - log (cos x)) ^ 2 = π ^ 3 / 8 := by
  have hD : IntervalIntegrable (fun x ↦ (log (sin x) - log (cos x)) ^ 2) volume 0 (π / 2) := by
    have := (intervalIntegrable_log_sin_sq.add intervalIntegrable_log_cos_sq).sub
      (intervalIntegrable_log_sin_mul_log_cos.const_mul 2)
    convert this using 1
    ext x
    ring
  have hπ4 : (0 : ℝ) ≤ π / 4 := by positivity
  have hsub1 : uIcc 0 (π / 4) ⊆ uIcc 0 (π / 2) := by
    rw [uIcc_of_le hπ4, uIcc_of_le (by positivity)]
    exact Icc_subset_Icc le_rfl (by linarith [pi_pos])
  have hsub2 : uIcc (π / 4) (π / 2) ⊆ uIcc 0 (π / 2) := by
    rw [uIcc_of_le (by linarith [pi_pos]), uIcc_of_le (by positivity)]
    exact Icc_subset_Icc hπ4 le_rfl
  have h := intervalIntegral.integral_comp_sub_left
    (fun x ↦ (log (sin x) - log (cos x)) ^ 2) (π / 2) (a := 0) (b := π / 4)
  simp only [sin_pi_div_two_sub, cos_pi_div_two_sub, sub_zero] at h
  rw [show π / 2 - π / 4 = π / 4 by ring] at h
  rw [← intervalIntegral.integral_add_adjacent_intervals (hD.mono_set hsub1)
    (hD.mono_set hsub2), ← h]
  have h2 : ∫ x in (0 : ℝ)..(π / 4), (log (cos x) - log (sin x)) ^ 2 =
      ∫ x in (0 : ℝ)..(π / 4), (log (sin x) - log (cos x)) ^ 2 := by
    congr 1
    ext x
    ring
  rw [h2, integral_log_tan_sq]
  ring

/-! ### The value of `∫₀^{π/2} log² sin` -/

/-- `∫₀^{π/2} log² sin x dx = π³/24 + (π/2) log² 2` and
`∫₀^{π/2} log sin x · log cos x dx = (π/2) log² 2 - π³/48`. -/
public theorem integral_log_sin_sq_and :
    (∫ x in (0 : ℝ)..(π / 2), log (sin x) ^ 2) = π ^ 3 / 24 + π / 2 * log 2 ^ 2 ∧
      (∫ x in (0 : ℝ)..(π / 2), log (sin x) * log (cos x)) = π / 2 * log 2 ^ 2 - π ^ 3 / 48 := by
  set L := ∫ x in (0 : ℝ)..(π / 2), log (sin x) ^ 2 with hL
  set B := ∫ x in (0 : ℝ)..(π / 2), log (sin x) * log (cos x) with hB
  have hπ : (0 : ℝ) ≤ π / 2 := by positivity
  have iS2 := intervalIntegrable_log_sin_sq
  have iK2 := intervalIntegrable_log_cos_sq
  have iS : IntervalIntegrable (fun x ↦ log (sin x)) volume 0 (π / 2) := intervalIntegrable_log_sin
  have iK : IntervalIntegrable (fun x ↦ log (cos x)) volume 0 (π / 2) := intervalIntegrable_log_cos
  have iSK := intervalIntegrable_log_sin_mul_log_cos
  have hS1 : ∫ x in (0 : ℝ)..(π / 2), log (sin x) = -(π / 2 * log 2) := by
    rw [integral_log_sin_zero_pi_div_two]
    ring
  -- `∫₀^{π/2} log² sin 2x dx = L`
  have hdup : ∫ x in (0 : ℝ)..(π / 2), log (sin (2 * x)) ^ 2 = L := by
    have h := intervalIntegral.integral_comp_mul_left (fun x ↦ log (sin x) ^ 2)
      (two_ne_zero (α := ℝ)) (a := 0) (b := π / 2)
    rw [h, mul_zero, show 2 * (π / 2) = π by ring, integral_log_sin_sq_zero_pi, smul_eq_mul]
    ring
  -- expanding `log sin 2x = log 2 + log sin x + log cos x`
  have hexp : ∫ x in (0 : ℝ)..(π / 2), log (sin (2 * x)) ^ 2 =
      ∫ x in (0 : ℝ)..(π / 2), (log 2 ^ 2 + log (sin x) ^ 2 + log (cos x) ^ 2
        + 2 * log 2 * log (sin x) + 2 * log 2 * log (cos x)
        + 2 * (log (sin x) * log (cos x))) := by
    rw [intervalIntegral.integral_of_le hπ, intervalIntegral.integral_of_le hπ,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun x hx ↦ ?_
    have hs : 0 < sin x := sin_pos_of_pos_of_lt_pi hx.1 (by linarith [hx.2, pi_pos])
    have hc : 0 < cos x := cos_pos_of_mem_Ioo ⟨by linarith [hx.1, pi_pos], hx.2⟩
    rw [sin_two_mul, log_mul (by positivity) hc.ne', log_mul two_ne_zero hs.ne']
    ring
  have i0 : IntervalIntegrable (fun _ : ℝ ↦ log 2 ^ 2) volume 0 (π / 2) :=
    intervalIntegrable_const
  have i3 := iS.const_mul (2 * log 2)
  have i4 := iK.const_mul (2 * log 2)
  have i5 := iSK.const_mul 2
  rw [intervalIntegral.integral_add ((((i0.add iS2).add iK2).add i3).add i4) i5,
    intervalIntegral.integral_add (((i0.add iS2).add iK2).add i3) i4,
    intervalIntegral.integral_add ((i0.add iS2).add iK2) i3,
    intervalIntegral.integral_add (i0.add iS2) iK2, intervalIntegral.integral_add i0 iS2,
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hdup,
    integral_log_cos_sq, hS1, integral_log_cos_zero_pi_div_two, smul_eq_mul, sub_zero] at hexp
  -- the reflected equation `∫₀^{π/2} (log sin - log cos)² = 2L - 2B`
  have htan := integral_log_tan_sq_zero_pi_div_two
  have hsq : ∫ x in (0 : ℝ)..(π / 2), (log (sin x) - log (cos x)) ^ 2 =
      ∫ x in (0 : ℝ)..(π / 2), (log (sin x) ^ 2 + log (cos x) ^ 2
        - 2 * (log (sin x) * log (cos x))) := by
    congr 1
    ext x
    ring
  rw [hsq, intervalIntegral.integral_sub (iS2.add iK2) i5,
    intervalIntegral.integral_add iS2 iK2, intervalIntegral.integral_const_mul,
    integral_log_cos_sq] at htan
  rw [← hL, ← hB] at hexp htan
  constructor <;> linarith

/-- `∫₀^{π/2} log² sin x dx = π³/24 + (π/2) log² 2`. -/
public theorem integral_log_sin_sq :
    ∫ x in (0 : ℝ)..(π / 2), log (sin x) ^ 2 = π ^ 3 / 24 + π / 2 * log 2 ^ 2 :=
  integral_log_sin_sq_and.1

/-- `∫₀^{π/2} log sin x · log cos x dx = (π/2) log² 2 - π³/48`. -/
public theorem integral_log_sin_mul_log_cos :
    ∫ x in (0 : ℝ)..(π / 2), log (sin x) * log (cos x) = π / 2 * log 2 ^ 2 - π ^ 3 / 48 :=
  integral_log_sin_sq_and.2

end LeanPolyLog.LogSinSq
