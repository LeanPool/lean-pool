/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilitySetIntegralConvergence

/-!
# Stability Weak Set Integral

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
noncomputable section

namespace CKN

/-- Weak `L²` convergence passes a bounded linear pairing through every
measurable restriction of a finite-measure domain. -/
theorem stability_tendsto_setIntegral_mul_test_of_weak_Ltwo
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (F : ℕ → α → ℝ) (G φ : α → ℝ) (S : Set α)
    (hφ : MemLp φ ∞ μ) (hS : MeasurableSet S)
    (hweak : ∀ w : α → ℝ, MemLp w 2 μ →
      Tendsto (fun n => ∫ x, F n x * w x ∂μ) atTop
        (nhds (∫ x, G x * w x ∂μ))) :
    Tendsto (fun n => ∫ x in S, F n x * φ x ∂μ) atTop
      (nhds (∫ x in S, G x * φ x ∂μ)) := by
  let w : α → ℝ := S.indicator φ
  have hw : MemLp w 2 μ := (hφ.indicator hS).mono_exponent (by simp)
  have h := hweak w hw
  have heqF (n : ℕ) :
      (∫ x, F n x * w x ∂μ) = ∫ x in S, F n x * φ x ∂μ := by
    rw [← integral_indicator hS]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ S <;> simp [w, hx]
  have heqG :
      (∫ x, G x * w x ∂μ) = ∫ x in S, G x * φ x ∂μ := by
    rw [← integral_indicator hS]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ S <;> simp [w, hx]
  simpa only [heqF, heqG] using h

end CKN
