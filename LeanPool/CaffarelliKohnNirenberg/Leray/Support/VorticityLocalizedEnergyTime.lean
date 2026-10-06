/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.WeakDerivOneDim
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# One-dimensional time calculus for the localized vorticity energy

A function of time with an integrable weak derivative on `(a, τ)`, and with a
continuous version taking the value `c₀` at `a`, is almost everywhere the
primitive `c₀ + ∫ₐᵗ G`. The square of such a primitive satisfies the energy
identity `(c₀ + ∫ₐᵗ G)² = c₀² + ∫ₐᵗ 2 (c₀ + ∫ₐˢ G) G(s) ds`. These are the time
steps of the energy argument in `lem:localized-vorticity-energy` of the Escauriaza–Seregin–Šverák manuscript.
-/

public section

open MeasureTheory Set Filter
open scoped Topology Interval

noncomputable section

namespace CKN

/-- The energy identity for the square of an absolutely continuous primitive. -/
theorem vlTime_sq_primitive {a t c : ℝ} {G : ℝ → ℝ}
    (hG : IntervalIntegrable G volume a t) :
    (c + ∫ s in a..t, G s) ^ 2 =
      c ^ 2 + ∫ s in a..t, 2 * (c + ∫ r in a..s, G r) * G s := by
  let F : ℝ → ℝ := fun s => c + ∫ r in a..s, G r
  have hprim : AbsolutelyContinuousOnInterval (fun s => ∫ r in a..s, G r) a t :=
    hG.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp)
  have hF : AbsolutelyContinuousOnInterval F a t := by
    have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => c) a t :=
      (LipschitzWith.const (α := ℝ) c).lipschitzOnWith.absolutelyContinuousOnInterval
    exact hconst.add hprim
  have hmul := hF.integral_deriv_mul_eq_sub hF
  have hderiv : ∀ᵐ s, s ∈ Ι a t → deriv F s * F s + F s * deriv F s =
      2 * F s * G s := by
    filter_upwards [hG.ae_hasDerivAt_integral] with s hs hsI
    have hsI' : s ∈ uIcc a t := uIoc_subset_uIcc hsI
    have hd : HasDerivAt F (G s) s := by
      have h := hs hsI' a (by simp)
      simpa [F] using h.const_add c
    rw [hd.deriv]
    ring
  have hcongr : (∫ s in a..t, deriv F s * F s + F s * deriv F s) =
      ∫ s in a..t, 2 * F s * G s :=
    intervalIntegral.integral_congr_ae hderiv
  have hFa : F a = c := by simp [F]
  have hFt : F t = c + ∫ s in a..t, G s := rfl
  rw [hcongr, hFa] at hmul
  rw [← hFt]
  change F t ^ 2 = c ^ 2 + ∫ s in a..t, 2 * F s * G s
  rw [hmul]
  ring

/-- A weak time derivative together with a continuous version with value `c₀`
at the initial time determines the function as the primitive from `c₀`. -/
theorem vlTime_eq_primitive_of_trace {a τ : ℝ} (hat : a < τ) {f G c : ℝ → ℝ} {c₀ : ℝ}
    (hf : IntegrableOn f (Ioo a τ) volume) (hG : IntegrableOn G (Ioo a τ) volume)
    (hweak : HasWeakDerivOn (Ioo a τ) f G)
    (hc : ContinuousOn c (Icc a τ)) (hca : c a = c₀)
    (hcf : ∀ᵐ t ∂(volume.restrict (Ioo a τ)), c t = f t) :
    (∀ t ∈ Icc a τ, c t = c₀ + ∫ s in a..t, G s) ∧
      ∀ᵐ t ∂(volume.restrict (Ioo a τ)), f t = c₀ + ∫ s in a..t, G s := by
  set t₀ : ℝ := (a + τ) / 2 with ht₀_def
  have ht₀ : t₀ ∈ Ioo a τ := by
    rw [ht₀_def]
    exact ⟨by linarith only [hat], by linarith only [hat]⟩
  obtain ⟨C, hC⟩ := exists_ae_eq_const_add_intervalIntegral_of_weakDeriv hat ht₀
    (hf.locallyIntegrableOn) (hG.locallyIntegrableOn) hweak
  have hGint : IntervalIntegrable G volume a τ := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hat.le]
    exact hG
  have hGsub : ∀ x ∈ Icc a τ, ∀ y ∈ Icc a τ, IntervalIntegrable G volume x y := by
    intro x hx y hy
    exact hGint.mono_set (uIcc_subset_uIcc (by simpa [uIcc_of_le hat.le] using hx)
      (by simpa [uIcc_of_le hat.le] using hy))
  let P : ℝ → ℝ := fun t => C + ∫ s in t₀..t, G s
  have hIcc : Icc a τ = uIcc a τ := (uIcc_of_le hat.le).symm
  have hPcont : ContinuousOn P (Icc a τ) := by
    rw [hIcc]
    exact continuousOn_const.add
      (intervalIntegral.continuousOn_primitive_interval' hGint
        (by rw [← hIcc]; exact Ioo_subset_Icc_self ht₀))
  have hae : c =ᵐ[volume.restrict (Ioo a τ)] P := by
    filter_upwards [hcf, hC.filter_mono ae_restrict_le,
      ae_restrict_mem measurableSet_Ioo] with t hct hCt ht
    rw [hct]
    exact hCt ht
  have hEqIoo : EqOn c P (Ioo a τ) :=
    Measure.eqOn_open_of_ae_eq hae isOpen_Ioo (hc.mono Ioo_subset_Icc_self)
      (hPcont.mono Ioo_subset_Icc_self)
  have hEqIcc : EqOn c P (Icc a τ) :=
    hEqIoo.of_subset_closure hc hPcont Ioo_subset_Icc_self
      (by rw [closure_Ioo hat.ne])
  have hPa : C + ∫ s in t₀..a, G s = c₀ := by
    rw [← hca]
    exact (hEqIcc (left_mem_Icc.2 hat.le)).symm
  have hPform : ∀ t ∈ Icc a τ, P t = c₀ + ∫ s in a..t, G s := by
    intro t ht
    simp only [P]
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hGsub t₀ (Ioo_subset_Icc_self ht₀) a (left_mem_Icc.2 hat.le))
      (hGsub a (left_mem_Icc.2 hat.le) t ht), ← hPa]
    ring
  refine ⟨fun t ht => (hEqIcc ht).trans (hPform t ht), ?_⟩
  filter_upwards [hC.filter_mono ae_restrict_le,
    ae_restrict_mem measurableSet_Ioo] with t hCt ht
  rw [hCt ht]
  exact hPform t (Ioo_subset_Icc_self ht)

end CKN

end
