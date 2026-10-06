/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityBoundedPairing
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Stability Weighted Gradient Scalar

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter
open scoped ENNReal
noncomputable section

namespace CKN

/-- A nonnegative bounded weight converts weak `L²` convergence into
convergence of the mixed energy and a weighted square inequality. -/
theorem stability_weighted_gradient_scalar
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (F : ℕ → α → ℝ) (G ψ : α → ℝ)
    (hF : ∀ n, MemLp (F n) 2 μ) (hG : MemLp G 2 μ)
    (hψ : MemLp ψ ∞ μ) (hψnonneg : ∀ᵐ x ∂μ, 0 ≤ ψ x)
    (hweak : ∀ w : α → ℝ, MemLp w 2 μ →
      Tendsto (fun n => ∫ x, F n x * w x ∂μ) atTop
        (nhds (∫ x, G x * w x ∂μ))) :
    Tendsto (fun n => ∫ x, F n x * G x * ψ x ∂μ) atTop
      (nhds (∫ x, G x * G x * ψ x ∂μ)) ∧
    (∀ n, 2 * (∫ x, F n x * G x * ψ x ∂μ) ≤
      (∫ x, F n x * F n x * ψ x ∂μ) +
      (∫ x, G x * G x * ψ x ∂μ)) := by
  have hw : MemLp (fun x => ψ x * G x) 2 μ := by
    have h : MemLp (ψ • G) 2 μ := hψ.smul hG
    have heq : (ψ • G) = (fun x => ψ x * G x) := by funext x; rfl
    rwa [heq] at h
  have hconvRaw := hweak (fun x => ψ x * G x) hw
  have hconv : Tendsto (fun n => ∫ x, F n x * G x * ψ x ∂μ)
      atTop (nhds (∫ x, G x * G x * ψ x ∂μ)) := by
    have heqFn (n : ℕ) :
        (∫ x, F n x * (ψ x * G x) ∂μ) =
          ∫ x, F n x * G x * ψ x ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    have heqG : (∫ x, G x * (ψ x * G x) ∂μ) =
        ∫ x, G x * G x * ψ x ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    simpa only [heqFn, heqG] using hconvRaw
  refine ⟨hconv, ?_⟩
  intro n
  have hF2 : MemLp (fun x => F n x * F n x) 1 μ := by
    have h : MemLp (F n * F n) 1 μ := (hF n).mul (hF n)
    have heq : F n * F n = (fun x => F n x * F n x) := by funext x; rfl
    rwa [heq] at h
  have hG2 : MemLp (fun x => G x * G x) 1 μ := by
    have h : MemLp (G * G) 1 μ := hG.mul hG
    have heq : G * G = (fun x => G x * G x) := by funext x; rfl
    rwa [heq] at h
  have hFG : MemLp (fun x => F n x * G x) 1 μ := by
    have h : MemLp (F n * G) 1 μ := (hF n).mul hG
    have heq : F n * G = (fun x => F n x * G x) := by funext x; rfl
    rwa [heq] at h
  have hFint : Integrable (fun x => F n x * F n x * ψ x) μ :=
    stability_integrable_mul_bounded_test μ (by norm_num) hF2 hψ
  have hGint : Integrable (fun x => G x * G x * ψ x) μ :=
    stability_integrable_mul_bounded_test μ (by norm_num) hG2 hψ
  have hFGint : Integrable (fun x => F n x * G x * ψ x) μ :=
    stability_integrable_mul_bounded_test μ (by norm_num) hFG hψ
  have hpoint : ∀ᵐ x ∂μ,
      2 * (F n x * G x * ψ x) ≤
        (F n x * F n x * ψ x) + (G x * G x * ψ x) := by
    filter_upwards [hψnonneg] with x hx
    have hsq := mul_nonneg (sq_nonneg (F n x - G x)) hx
    nlinarith only [hsq]
  have hineq := integral_mono_ae (hFGint.const_mul 2)
    (hFint.add hGint) hpoint
  rw [integral_const_mul, integral_add' hFint hGint] at hineq
  exact hineq

end CKN
