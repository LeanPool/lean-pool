/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.H1EstimateGronwall

/-!
# Integral Grönwall inequality with an integrable coefficient

A continuous function bounded by a constant plus the integral of an
integrable nonnegative coefficient times itself is bounded by the
corresponding exponential factor. A variant carries a nonnegative
dissipation term on the left-hand side. Both are used to close the
high-order energy estimates of the smoothing argument (`prop:lps-smoothing`).
-/

public section

open MeasureTheory Set
open scoped Interval


noncomputable section

namespace ESS.LPS

/-- Integral form of Grönwall's inequality with an integrable nonnegative
coefficient: if `Φ r ≤ A + ∫_s^r c Φ` for every `r ∈ [s, t]`, then
`Φ r ≤ A exp (∫_s^r c)` on `[s, t]` (`prop:lps-smoothing`). -/
theorem lps_integral_gronwall {s t : ℝ} (hst : s ≤ t) {Φ c : ℝ → ℝ} {A : ℝ}
    (hΦ : ContinuousOn Φ (Icc s t)) (hc : IntervalIntegrable c volume s t)
    (hc0 : ∀ r ∈ Icc s t, 0 ≤ c r)
    (h : ∀ r ∈ Icc s t, Φ r ≤ A + ∫ τ in s..r, c τ * Φ τ) :
    ∀ r ∈ Icc s t, Φ r ≤ A * Real.exp (∫ τ in s..r, c τ) := by
  have hcΦ : IntervalIntegrable (fun τ => c τ * Φ τ) volume s t :=
    hc.mul_continuousOn (by rw [uIcc_of_le hst]; exact hΦ)
  let f : ℝ → ℝ := fun r => A + ∫ τ in s..r, c τ * Φ τ
  have hs_mem : s ∈ uIcc s t := by rw [uIcc_of_le hst]; exact ⟨le_rfl, hst⟩
  have hGac : AbsolutelyContinuousOnInterval (fun r => ∫ τ in s..r, c τ * Φ τ) s t :=
    hcΦ.absolutelyContinuousOnInterval_intervalIntegral hs_mem
  have hAac : AbsolutelyContinuousOnInterval (fun _ : ℝ => A) s t :=
    (LipschitzWith.const A).lipschitzOnWith.absolutelyContinuousOnInterval
  have hfac : AbsolutelyContinuousOnInterval f s t := hAac.fun_add hGac
  have hcI : IntegrableOn c (Icc s t) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hst).1 hc
  have hcpos : ∀ᵐ r ∂(volume.restrict (Icc s t)), 0 ≤ c r := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact hc0 r hr
  have hderiv : ∀ᵐ r ∂(volume.restrict (Icc s t)), deriv f r ≤ c r * f r := by
    filter_upwards [hcΦ.ae_hasDerivAt_integral.filter_mono ae_restrict_le,
      ae_restrict_mem measurableSet_Icc] with r hG hr
    have hr' : r ∈ uIcc s t := by rw [uIcc_of_le hst]; exact hr
    have hGr : HasDerivAt (fun x => ∫ τ in s..x, c τ * Φ τ) (c r * Φ r) r :=
      hG hr' s hs_mem
    have hfr : deriv f r = c r * Φ r := (hGr.const_add A).deriv
    rw [hfr]
    exact mul_le_mul_of_nonneg_left (h r hr) (hc0 r hr)
  have hgr := lps_ac_gronwall hst hfac hcI hcpos hderiv
  intro r hr
  have hfs : f s = A := by simp [f]
  have hbound := hgr r hr
  rw [hfs] at hbound
  exact (h r hr).trans hbound

/-- Integral Grönwall inequality with a nonnegative dissipation term on the
left: if `Φ r + D r ≤ A + ∫_s^r c Φ` on `[s, t]` with `Φ, D ≥ 0`, then
`D t ≤ A (1 + (∫_s^t c) exp (∫_s^t c))` (`prop:lps-smoothing`). -/
theorem lps_integral_gronwall_dissipation {s t : ℝ} (hst : s ≤ t) {Φ c D : ℝ → ℝ} {A : ℝ}
    (hΦ : ContinuousOn Φ (Icc s t)) (hc : IntervalIntegrable c volume s t)
    (hc0 : ∀ r ∈ Icc s t, 0 ≤ c r) (hΦ0 : ∀ r ∈ Icc s t, 0 ≤ Φ r)
    (hD0 : ∀ r ∈ Icc s t, 0 ≤ D r)
    (h : ∀ r ∈ Icc s t, Φ r + D r ≤ A + ∫ τ in s..r, c τ * Φ τ) :
    D t ≤ A * (1 + (∫ τ in s..t, c τ) * Real.exp (∫ τ in s..t, c τ)) := by
  have hs : s ∈ Icc s t := ⟨le_rfl, hst⟩
  have ht : t ∈ Icc s t := ⟨hst, le_rfl⟩
  have hΦle : ∀ r ∈ Icc s t, Φ r ≤ A + ∫ τ in s..r, c τ * Φ τ := fun r hr =>
    (le_add_of_nonneg_right (hD0 r hr)).trans (h r hr)
  have hbound := lps_integral_gronwall hst hΦ hc hc0 hΦle
  have hA : 0 ≤ A := by
    have h0 := h s hs
    rw [intervalIntegral.integral_same, add_zero] at h0
    linarith only [h0, hΦ0 s hs, hD0 s hs]
  have hCmono : ∀ r ∈ Icc s t, (∫ τ in s..r, c τ) ≤ ∫ τ in s..t, c τ := by
    intro r hr
    have hsr : IntervalIntegrable c volume s r :=
      hc.mono_set (by rw [uIcc_of_le hst, uIcc_of_le hr.1]; exact Icc_subset_Icc le_rfl hr.2)
    have hrt : IntervalIntegrable c volume r t :=
      hc.mono_set (by rw [uIcc_of_le hst, uIcc_of_le hr.2]; exact Icc_subset_Icc hr.1 le_rfl)
    have hsplit := intervalIntegral.integral_add_adjacent_intervals hsr hrt
    have hnn : 0 ≤ ∫ τ in r..t, c τ :=
      intervalIntegral.integral_nonneg hr.2 fun u hu => hc0 u ⟨hr.1.trans hu.1, hu.2⟩
    linarith only [hsplit, hnn]
  set K : ℝ := A * Real.exp (∫ τ in s..t, c τ) with hK
  have hcΦ : IntervalIntegrable (fun τ => c τ * Φ τ) volume s t :=
    hc.mul_continuousOn (by rw [uIcc_of_le hst]; exact hΦ)
  have hint : (∫ τ in s..t, c τ * Φ τ) ≤ ∫ τ in s..t, c τ * K := by
    refine intervalIntegral.integral_mono_on hst hcΦ (hc.mul_const K) ?_
    intro r hr
    refine mul_le_mul_of_nonneg_left ((hbound r hr).trans ?_) (hc0 r hr)
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (hCmono r hr)) hA
  rw [intervalIntegral.integral_mul_const] at hint
  have hDt := h t ht
  have hΦt := hΦ0 t ht
  have hgoal : A * (1 + (∫ τ in s..t, c τ) * Real.exp (∫ τ in s..t, c τ)) =
      A + (∫ τ in s..t, c τ) * K := by
    rw [hK]; ring
  rw [hgoal]
  linarith only [hDt, hΦt, hint]

end ESS.LPS
