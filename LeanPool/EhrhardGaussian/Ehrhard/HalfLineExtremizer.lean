/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith

/-! Half-lines maximize the first moment among functions bounded between zero and one with
prescribed integral under a finite measure with a finite first moment. -/

public section

open MeasureTheory Set

namespace EhrhardGaussian.Ehrhard

/-- A measurable function taking values in `[0,1]` is integrable for a finite measure. -/
theorem integrable_of_mem_Icc {μ : Measure ℝ} [IsFiniteMeasure μ] {f : ℝ → ℝ}
    (hf : Measurable f) (hbound : ∀ x, f x ∈ Icc (0 : ℝ) 1) : Integrable f μ := by
  refine (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable ?_
  exact ae_of_all _ fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hbound x).1]
    exact (hbound x).2

/-- Multiplying a first moment by a measurable function in `[0,1]` preserves integrability. -/
theorem integrable_mul_of_mem_Icc {μ : Measure ℝ} {f : ℝ → ℝ}
    (hid : Integrable (fun x : ℝ => x) μ) (hf : Measurable f)
    (hbound : ∀ x, f x ∈ Icc (0 : ℝ) 1) : Integrable (fun x => x * f x) μ := by
  refine hid.mul_bdd (c := 1) hf.aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (hbound x).1]
  exact (hbound x).2

/-- The upper half-line maximizes the first moment among functions in `[0,1]`
with its mean. The mean is written as an integral to allow atomic measures. -/
theorem integral_mul_le_integral_Ioi {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hid : Integrable (fun x : ℝ => x) μ) {f : ℝ → ℝ} (hf : Measurable f)
    (hbound : ∀ x, f x ∈ Icc (0 : ℝ) 1) (c : ℝ)
    (hmean : ∫ x, f x ∂μ = ∫ x, (Ioi c).indicator (fun _ : ℝ => (1 : ℝ)) x ∂μ) :
    ∫ x, x * f x ∂μ ≤ ∫ x in Ioi c, x ∂μ := by
  have hfint := integrable_of_mem_Icc (μ := μ) hf hbound
  have hxfint := integrable_mul_of_mem_Icc hid hf hbound
  have hind := (integrable_const (1 : ℝ) (μ := μ)).indicator (measurableSet_Ioi (a := c))
  have hxind := hid.indicator (measurableSet_Ioi (a := c))
  have hleft : Integrable (fun x => x * f x - c * f x) μ :=
    hxfint.sub (hfint.const_mul c)
  have hright : Integrable (fun x =>
      (Ioi c).indicator (fun x : ℝ => x) x -
        c * (Ioi c).indicator (fun _ : ℝ => (1 : ℝ)) x) μ :=
    hxind.sub (hind.const_mul c)
  have hle := integral_mono hleft hright (fun x => ?_)
  · rw [integral_sub hxfint (hfint.const_mul c),
      integral_sub hxind (hind.const_mul c), integral_const_mul, integral_const_mul,
      hmean] at hle
    simp only [integral_indicator measurableSet_Ioi] at hle
    exact (sub_le_sub_iff_right _).mp hle
  · by_cases hx : c < x
    · simp only [mem_Ioi.mpr hx, indicator_of_mem, mul_one]
      have := mul_le_mul_of_nonneg_left (hbound x).2 (sub_nonneg.mpr hx.le)
      linarith only [this]
    · simp only [mem_Ioi, hx, not_false_eq_true, indicator_of_notMem, mul_zero, sub_zero]
      have := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_of_not_gt hx))
        (hbound x).1
      linarith only [this]

end EhrhardGaussian.Ehrhard
