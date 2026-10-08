/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingGronwall

/-!
# Uniform bound from a differential energy inequality with an integrable coefficient

`prop:lps-smoothing`: the real-variable step of the time-difference estimate. An energy `E ≥ 0`
with `E' ≤ -D + κ E` (in integral form), whose mean over an initial layer of length `δ` is at most
`Θ` and whose coefficient has integral at most `Λ`, is bounded by `(Θ/δ) e^Λ` after the layer.
-/

public section

open MeasureTheory Set
open scoped Interval


noncomputable section

namespace ESS.LPS

/-- A continuous nonnegative function with integral at most `Θ` over `[a,a+δ]` takes a value at
most `Θ/δ` there. -/
theorem lps_exists_le_average {a δ Θ : ℝ} (hδ : 0 < δ) {E : ℝ → ℝ}
    (hE : ContinuousOn E (Icc a (a + δ)))
    (hΘ : ∫ τ in a..(a + δ), E τ ≤ Θ) : ∃ s ∈ Icc a (a + δ), E s ≤ Θ / δ := by
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  obtain ⟨s₀, hs₀, hmin⟩ := (isCompact_Icc (a := a) (b := a + δ)).exists_isMinOn
    ⟨a, ⟨le_rfl, by linarith only [hδ]⟩⟩ hE
  have hgt : Θ / δ < E s₀ := hcon s₀ hs₀
  have hint : ∫ τ in a..(a + δ), E s₀ ≤ ∫ τ in a..(a + δ), E τ := by
    refine intervalIntegral.integral_mono_on (by linarith only [hδ])
      intervalIntegrable_const (hE.intervalIntegrable_of_Icc (by linarith only [hδ])) ?_
    intro τ hτ
    exact hmin hτ
  rw [intervalIntegral.integral_const, smul_eq_mul] at hint
  have : Θ < E s₀ * δ := by
    rw [div_lt_iff₀ hδ] at hgt
    linarith only [hgt]
  have hdelta : a + δ - a = δ := by ring
  rw [hdelta] at hint
  linarith only [hint, this, hΘ, mul_comm δ (E s₀)]

/-- Uniform bound from an energy inequality with an integrable coefficient. -/
theorem lps_energy_uniform_bound {a T' δ Θ Λ : ℝ} (hδ : 0 < δ) (haδ : a + δ ≤ T')
    {E g Dd κ : ℝ → ℝ}
    (hE : ContinuousOn E (Icc a T')) (hE0 : ∀ r ∈ Icc a T', 0 ≤ E r)
    (hg : IntervalIntegrable g volume a T') (hDd : IntervalIntegrable Dd volume a T')
    (hκ : IntervalIntegrable κ volume a T') (hDd0 : ∀ r ∈ Icc a T', 0 ≤ Dd r)
    (hκ0 : ∀ r ∈ Icc a T', 0 ≤ κ r)
    (hid : ∀ s ∈ Icc a T', ∀ t ∈ Icc a T', s ≤ t → E t - E s = ∫ τ in s..t, g τ)
    (hineq : ∀ᵐ τ ∂(volume : Measure ℝ), τ ∈ Icc a T' → g τ ≤ -Dd τ + κ τ * E τ)
    (hΘ : ∫ τ in a..(a + δ), E τ ≤ Θ) (hΛ : ∫ τ in a..T', κ τ ≤ Λ) :
    ∃ s ∈ Icc a (a + δ), E s ≤ Θ / δ ∧
      (∀ t ∈ Icc (a + δ) T', E t ≤ Θ / δ * Real.exp Λ) ∧
      ∀ t ∈ Icc (a + δ) T', ∫ τ in (a + δ)..t, Dd τ ≤ Θ / δ * (1 + Λ * Real.exp Λ) := by
  obtain ⟨s, hs, hEs⟩ := lps_exists_le_average hδ
    (hE.mono (Icc_subset_Icc le_rfl haδ)) hΘ
  refine ⟨s, hs, hEs, ?_⟩
  have hsT : s ≤ T' := hs.2.trans haδ
  have hsa : a ≤ s := hs.1
  have hsub : Icc s T' ⊆ Icc a T' := Icc_subset_Icc hsa le_rfl
  have hsubI : uIcc s T' ⊆ uIcc a T' := by
    rw [uIcc_of_le hsT, uIcc_of_le (hsa.trans hsT)]; exact hsub
  have hκs : IntervalIntegrable κ volume s T' := hκ.mono_set hsubI
  have hgs : IntervalIntegrable g volume s T' := hg.mono_set hsubI
  have hDds : IntervalIntegrable Dd volume s T' := hDd.mono_set hsubI
  have hEκ : ∀ t ∈ Icc s T', E t + ∫ τ in s..t, Dd τ ≤ E s + ∫ τ in s..t, κ τ * E τ := by
    intro t ht
    have htI : t ∈ Icc a T' := hsub ht
    have hsI : s ∈ Icc a T' := ⟨hsa, hsT⟩
    have hEt := hid s hsI t htI ht.1
    have hsubt : Icc s t ⊆ Icc s T' := Icc_subset_Icc le_rfl ht.2
    have hsubtI : uIcc s t ⊆ uIcc s T' := by
      rw [uIcc_of_le ht.1, uIcc_of_le hsT]; exact hsubt
    have hgt : IntervalIntegrable g volume s t := hgs.mono_set hsubtI
    have hDdt : IntervalIntegrable Dd volume s t := hDds.mono_set hsubtI
    have hκEt : IntervalIntegrable (fun τ => κ τ * E τ) volume s t :=
      (hκs.mono_set hsubtI).mul_continuousOn
        (by rw [uIcc_of_le ht.1]; exact hE.mono (hsubt.trans hsub))
    have hle : ∫ τ in s..t, g τ ≤ ∫ τ in s..t, (-Dd τ + κ τ * E τ) := by
      refine intervalIntegral.integral_mono_ae_restrict ht.1 hgt
        ((hDdt.neg).add hκEt) ?_
      rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
      filter_upwards [hineq] with τ hτ hτm
      exact hτ ⟨hsa.trans hτm.1, hτm.2.trans ht.2⟩
    have hneg : IntervalIntegrable (fun τ => -Dd τ) volume s t := hDdt.neg
    have hsum := intervalIntegral.integral_add hneg hκEt
    have hneg2 : (∫ τ in s..t, -Dd τ) = -∫ τ in s..t, Dd τ := intervalIntegral.integral_neg
    linarith only [hEt, hle, hsum, hneg2]
  have hA0 : 0 ≤ E s := hE0 s ⟨hsa, hsT⟩
  have hDnn : ∀ r ∈ Icc s T', 0 ≤ ∫ τ in s..r, Dd τ := fun r hr =>
    intervalIntegral.integral_nonneg hr.1 fun u hu => hDd0 u ⟨hsa.trans hu.1, hu.2.trans hr.2⟩
  have hκc : ∀ t ∈ Icc s T', (∫ τ in s..t, κ τ) ≤ Λ := by
    intro t ht
    have hsat : IntervalIntegrable κ volume a s := hκ.mono_set (by
      rw [uIcc_of_le hsa, uIcc_of_le (hsa.trans hsT)]; exact Icc_subset_Icc le_rfl hsT)
    have hst : IntervalIntegrable κ volume s t := hκ.mono_set (by
      rw [uIcc_of_le ht.1, uIcc_of_le (hsa.trans hsT)]; exact Icc_subset_Icc hsa ht.2)
    have htT : IntervalIntegrable κ volume t T' := hκ.mono_set (by
      rw [uIcc_of_le ht.2, uIcc_of_le (hsa.trans hsT)]; exact Icc_subset_Icc (hsa.trans ht.1)
        le_rfl)
    have h1 := intervalIntegral.integral_add_adjacent_intervals hsat hst
    have h2 := intervalIntegral.integral_add_adjacent_intervals (hsat.trans hst) htT
    have hn1 : 0 ≤ ∫ τ in a..s, κ τ :=
      intervalIntegral.integral_nonneg hsa fun u hu => hκ0 u ⟨hu.1, hu.2.trans hsT⟩
    have hn2 : 0 ≤ ∫ τ in t..T', κ τ :=
      intervalIntegral.integral_nonneg ht.2 fun u hu => hκ0 u ⟨(hsa.trans ht.1).trans hu.1, hu.2⟩
    linarith only [h1, h2, hn1, hn2, hΛ]
  have hbound := lps_integral_gronwall hsT (Φ := E) (c := κ) (A := E s) (hE.mono hsub) hκs
    (fun r hr => hκ0 r (hsub hr)) (fun r hr => by
      have := hEκ r hr
      linarith only [this, hDnn r hr])
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · have htI : t ∈ Icc s T' := ⟨(hs.2).trans ht.1, ht.2⟩
    calc E t ≤ E s * Real.exp (∫ τ in s..t, κ τ) := hbound t htI
      _ ≤ Θ / δ * Real.exp Λ := by
          refine mul_le_mul hEs (Real.exp_le_exp.2 (hκc t htI)) (Real.exp_pos _).le ?_
          exact hA0.trans hEs
  · have htI : t ∈ Icc s T' := ⟨(hs.2).trans ht.1, ht.2⟩
    have hsubt : Icc s t ⊆ Icc s T' := Icc_subset_Icc le_rfl htI.2
    have hκst : IntervalIntegrable κ volume s t := hκs.mono_set (by
      rw [uIcc_of_le htI.1, uIcc_of_le hsT]; exact hsubt)
    have hdiss := lps_integral_gronwall_dissipation htI.1 (Φ := E) (c := κ)
      (D := fun r => ∫ τ in s..r, Dd τ)
      (A := E s) (hE.mono (hsubt.trans hsub)) hκst (fun r hr => hκ0 r (hsub (hsubt hr)))
      (fun r hr => hE0 r (hsub (hsubt hr))) (fun r hr => hDnn r (hsubt hr))
      (fun r hr => hEκ r (hsubt hr))
    have hδs : (∫ τ in (a + δ)..t, Dd τ) ≤ ∫ τ in s..t, Dd τ := by
      have hs' : IntervalIntegrable Dd volume s (a + δ) := hDds.mono_set (by
        rw [uIcc_of_le hs.2, uIcc_of_le hsT]; exact Icc_subset_Icc le_rfl haδ)
      have hst' : IntervalIntegrable Dd volume (a + δ) t := hDds.mono_set (by
        rw [uIcc_of_le ht.1, uIcc_of_le hsT]; exact Icc_subset_Icc hs.2 ht.2)
      have h := intervalIntegral.integral_add_adjacent_intervals hs' hst'
      have hn : 0 ≤ ∫ τ in s..(a + δ), Dd τ :=
        intervalIntegral.integral_nonneg hs.2 fun u hu => hDd0 u ⟨hsa.trans hu.1, hu.2.trans haδ⟩
      linarith only [h, hn]
    have hK := hκc t htI
    have hnn : 0 ≤ ∫ τ in s..t, κ τ :=
      intervalIntegral.integral_nonneg htI.1 fun u hu => hκ0 u ⟨hsa.trans hu.1, hu.2.trans htI.2⟩
    have hexp : Real.exp (∫ τ in s..t, κ τ) ≤ Real.exp Λ := Real.exp_le_exp.2 hK
    have hfac : (1 + (∫ τ in s..t, κ τ) * Real.exp (∫ τ in s..t, κ τ)) ≤ 1 + Λ * Real.exp Λ := by
      have : (∫ τ in s..t, κ τ) * Real.exp (∫ τ in s..t, κ τ) ≤ Λ * Real.exp Λ :=
        mul_le_mul hK hexp (Real.exp_pos _).le (hnn.trans hK)
      linarith only [this]
    calc (∫ τ in (a + δ)..t, Dd τ) ≤ ∫ τ in s..t, Dd τ := hδs
      _ ≤ E s * (1 + (∫ τ in s..t, κ τ) * Real.exp (∫ τ in s..t, κ τ)) := hdiss
      _ ≤ Θ / δ * (1 + Λ * Real.exp Λ) :=
          mul_le_mul hEs hfac (by positivity) (hA0.trans hEs)

end ESS.LPS
