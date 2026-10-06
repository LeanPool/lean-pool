/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityFixedMultiplier

/-!
# Stability Set Integral Convergence

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
noncomputable section

namespace CKN

/-- Strong local `L³` convergence passes to a bounded linear pairing on
every measurable subset of a finite-measure domain. -/
theorem stability_tendsto_setIntegral_mul_test_of_Lthree
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (F : ℕ → α → ℝ) (G φ : α → ℝ) (S : Set α)
    (hF : ∀ n, MemLp (F n) 3 μ)
    (hφ : MemLp φ ∞ μ) (hS : MeasurableSet S)
    (hconv : Tendsto (fun n => eLpNorm (F n - G) 3 μ) atTop (nhds 0)) :
    Tendsto (fun n => ∫ x in S, φ x * F n x ∂μ) atTop
      (nhds (∫ x in S, φ x * G x ∂μ)) := by
  let w : α → ℝ := S.indicator φ
  have hw : MemLp w ∞ μ := hφ.indicator hS
  have h := stability_tendsto_integral_mul_test_of_Lthree μ F G w hF hw hconv
  have heqF (n : ℕ) :
      (∫ x, w x • F n x ∂μ) = ∫ x in S, φ x * F n x ∂μ := by
    rw [← integral_indicator hS]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ S <;> simp [w, hx, smul_eq_mul]
  have heqG :
      (∫ x, w x • G x ∂μ) = ∫ x in S, φ x * G x ∂μ := by
    rw [← integral_indicator hS]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ S <;> simp [w, hx, smul_eq_mul]
  simpa only [heqF, heqG] using h

end CKN
