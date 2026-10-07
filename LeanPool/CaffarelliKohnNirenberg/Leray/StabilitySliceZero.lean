/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!
# Stability Slice Zero

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
noncomputable section

namespace CKN

/-- A space-time integral limit preserves a zero identity on almost every
time slice, provided it holds for the approximants and every measurable
time restriction. -/
theorem stability_ae_slice_integral_zero_of_setIntegral_tendsto
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (ν : Measure ℝ) [SFinite μ] [SFinite ν]
    (F : ℕ → X × ℝ → ℝ) (G : X × ℝ → ℝ)
    (hF : ∀ n, Integrable (F n) (μ.prod ν))
    (hG : Integrable G (μ.prod ν))
    (hzero : ∀ n, ∀ᵐ t ∂ν, ∫ x, F n (x, t) ∂μ = 0)
    (hconv : ∀ s : Set ℝ, MeasurableSet s → ν s < ⊤ →
      Tendsto (fun n => ∫ z in (univ : Set X) ×ˢ s, F n z ∂μ.prod ν)
        atTop (nhds (∫ z in (univ : Set X) ×ˢ s, G z ∂μ.prod ν))) :
    ∀ᵐ t ∂ν, ∫ x, G (x, t) ∂μ = 0 := by
  have hinner : Integrable (fun t => ∫ x, G (x, t) ∂μ) ν :=
    hG.integral_prod_right
  apply hinner.ae_eq_zero_of_forall_setIntegral_eq_zero
  intro s hs hsfinite
  have hzeroFn (n : ℕ) :
      (∫ z in (univ : Set X) ×ˢ s, F n z ∂μ.prod ν) = 0 := by
    rw [← setIntegral_prod_swap (univ : Set X) s (F n)]
    rw [setIntegral_prod (fun z : ℝ × X => F n z.swap) (hF n).swap.integrableOn]
    simp only [setIntegral_univ]
    apply integral_eq_zero_of_ae
    exact ae_restrict_of_ae (hzero n)
  have hlim := hconv s hs hsfinite
  have hGzero : (∫ z in (univ : Set X) ×ˢ s, G z ∂μ.prod ν) = 0 := by
    have heq : (0 : ℝ) = ∫ z in (univ : Set X) ×ˢ s, G z ∂μ.prod ν :=
      tendsto_const_nhds_iff.mp (by simpa only [hzeroFn] using hlim)
    exact heq.symm
  rw [← setIntegral_prod_swap (univ : Set X) s G] at hGzero
  rw [setIntegral_prod (fun z : ℝ × X => G z.swap) hG.swap.integrableOn] at hGzero
  simpa only [setIntegral_univ, Prod.swap_prod_mk] using hGzero

end CKN
