/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Averages of a moving window integral

`prop:lps-smoothing`: the initial-layer control of the time-difference quotients. For a
nonnegative integrable `f`, the mean over `[a,a+δ]` of the window averages
`(1/h) ∫_τ^{τ+h} f` is at most `∫_a^{a+δ+h} f` (Fubini for the sliding window).
-/

public section

open MeasureTheory Set
open scoped Interval


noncomputable section

namespace ESS.LPS

/-- The integral over `[a, a+δ]` of window averages of a nonnegative integrable function is at
most the integral over the enlarged interval (`prop:lps-smoothing`). -/
theorem lps_window_average_integral_le {a δ h : ℝ} (hδ : 0 < δ) (hh : 0 < h) {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume a (a + δ + h))
    (hf0 : ∀ x ∈ Icc a (a + δ + h), 0 ≤ f x) :
    ∫ τ in a..(a + δ), (1 / h) * ∫ σ in τ..(τ + h), f σ ≤ ∫ σ in a..(a + δ + h), f σ := by
  have hδh : a ≤ a + δ + h := by linarith only [hδ, hh]
  set F : ℝ → ℝ := fun x => ∫ σ in a..x, f σ with hF
  have hFcont : ContinuousOn F (Icc a (a + δ + h)) := by
    have := intervalIntegral.continuousOn_primitive_interval' hf left_mem_uIcc
    rwa [uIcc_of_le hδh] at this
  have hsplit : ∀ x y, a ≤ x → x ≤ y → y ≤ a + δ + h → F y - F x = ∫ σ in x..y, f σ := by
    intro x y hax hxy hy
    have h1 : IntervalIntegrable f volume a x := hf.mono_set (by
      rw [uIcc_of_le hax, uIcc_of_le hδh]; exact Icc_subset_Icc le_rfl (hxy.trans hy))
    have h2 : IntervalIntegrable f volume x y := hf.mono_set (by
      rw [uIcc_of_le hxy, uIcc_of_le hδh]; exact Icc_subset_Icc hax hy)
    have := intervalIntegral.integral_add_adjacent_intervals h1 h2
    simp only [F]
    linarith only [this]
  have hF0 : F a = 0 := by simp [F]
  have hFmono : ∀ x y, a ≤ x → x ≤ y → y ≤ a + δ + h → F x ≤ F y := by
    intro x y hax hxy hy
    have hn : 0 ≤ ∫ σ in x..y, f σ :=
      intervalIntegral.integral_nonneg hxy fun u hu => hf0 u ⟨hax.trans hu.1, hu.2.trans hy⟩
    linarith only [hsplit x y hax hxy hy, hn]
  have hFnn : ∀ x, a ≤ x → x ≤ a + δ + h → 0 ≤ F x := fun x hax hx => by
    have := hFmono a x le_rfl hax hx
    linarith only [this, hF0]
  have hFint : ∀ x y, a ≤ x → x ≤ y → y ≤ a + δ + h → IntervalIntegrable F volume x y := by
    intro x y hax hxy hy
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hxy]
    exact hFcont.mono (Icc_subset_Icc hax hy)
  have hwin : ∀ τ ∈ Icc a (a + δ), (1 / h) * (∫ σ in τ..(τ + h), f σ) =
      (1 / h) * (F (τ + h) - F τ) := by
    intro τ hτ
    rw [hsplit τ (τ + h) hτ.1 (by linarith only [hh]) (by linarith only [hτ.2])]
  rw [intervalIntegral.integral_congr (g := fun τ => (1 / h) * (F (τ + h) - F τ))
    (fun τ hτ => hwin τ (by rwa [uIcc_of_le (by linarith only [hδ])] at hτ))]
  have hc1 : IntervalIntegrable (fun τ => F (τ + h)) volume a (a + δ) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le (by linarith only [hδ])]
    exact hFcont.comp (continuousOn_id.add continuousOn_const) fun τ hτ =>
      ⟨by linarith only [hτ.1, hh], by linarith only [hτ.2]⟩
  have hc2 : IntervalIntegrable F volume a (a + δ) :=
    hFint a (a + δ) le_rfl (by linarith only [hδ]) (by linarith only [hh])
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hc1 hc2,
    intervalIntegral.integral_comp_add_right (fun τ => F τ) h]
  have hA := intervalIntegral.integral_add_adjacent_intervals
    (hFint a (a + h) le_rfl (by linarith only [hh]) (by linarith only [hδ]))
    (hFint (a + h) (a + δ + h) (by linarith only [hh]) (by linarith only [hδ]) le_rfl)
  have hB := intervalIntegral.integral_add_adjacent_intervals hc2
    (hFint (a + δ) (a + δ + h) (by linarith only [hδ]) (by linarith only [hh]) le_rfl)
  have hn1 : 0 ≤ ∫ τ in a..(a + h), F τ :=
    intervalIntegral.integral_nonneg (by linarith only [hh]) fun u hu =>
      hFnn u hu.1 (by linarith only [hu.2, hδ])
  have hn2 : (∫ τ in (a + δ)..(a + δ + h), F τ) ≤ ∫ τ in (a + δ)..(a + δ + h), F (a + δ + h) := by
    refine intervalIntegral.integral_mono_on (by linarith only [hh])
      (hFint (a + δ) (a + δ + h) (by linarith only [hδ]) (by linarith only [hh]) le_rfl)
      intervalIntegrable_const fun u hu => ?_
    exact hFmono u (a + δ + h) (by linarith only [hu.1, hδ]) hu.2 le_rfl
  rw [intervalIntegral.integral_const, smul_eq_mul] at hn2
  have hfinal : (∫ τ in a..(a + δ + h), f τ) = F (a + δ + h) := by simp [F]
  rw [hfinal]
  have hh' : a + δ + h - (a + δ) = h := by ring
  rw [hh'] at hn2
  have hsum : (∫ τ in (a + h)..(a + δ + h), F τ) - ∫ τ in a..(a + δ), F τ ≤ h * F (a + δ + h) := by
    linarith only [hA, hB, hn1, hn2]
  calc (1 / h) * ((∫ τ in (a + h)..(a + δ + h), F τ) - ∫ τ in a..(a + δ), F τ)
      ≤ (1 / h) * (h * F (a + δ + h)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = F (a + δ + h) := by field_simp

end ESS.LPS
