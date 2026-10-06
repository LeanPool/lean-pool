/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityPressureIntegralConvergence

/-!
# Stability Pressure Fixed Multiplier

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter
open scoped ENNReal
noncomputable section

namespace CKN

/-- A bounded scalar test preserves convergence of pressure integrals under
strong local `L^{3/2}` convergence. -/
theorem stability_tendsto_integral_mul_test_of_LthreeHalves
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    (F : ℕ → α → ℝ) (G φ : α → ℝ)
    (hF : ∀ n, MemLp (F n) (3 / 2 : ℝ≥0∞) μ)
    (hφ : MemLp φ ∞ μ)
    (hconv : Tendsto (fun n => eLpNorm (F n - G) (3 / 2 : ℝ≥0∞) μ)
      atTop (nhds 0)) :
    Tendsto (fun n => ∫ x, φ x * F n x ∂μ) atTop
      (nhds (∫ x, φ x * G x ∂μ)) := by
  have hOne : (1 : ℝ≥0∞) ≤ (3 / 2 : ℝ≥0∞) := by
    rw [← CKN.ofReal_threeHalves]
    simpa using ENNReal.ofReal_le_ofReal (by norm_num : (1 : ℝ) ≤ 3 / 2)
  have hG : MemLp G (3 / 2 : ℝ≥0∞) μ :=
    Lp.memLp_of_cauchy_tendsto hOne hF G hconv
  have hscaled (n : ℕ) :
      eLpNorm (fun x => φ x * F n x - φ x * G x) (3 / 2 : ℝ≥0∞) μ ≤
      eLpNorm φ ∞ μ * eLpNorm (F n - G) (3 / 2 : ℝ≥0∞) μ := by
    have h := eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm
      (φ := φ) (f := F n - G) (3 / 2 : ℝ≥0∞) hφ.aestronglyMeasurable
    have heq : (fun x => φ x * F n x - φ x * G x) = φ • (F n - G) := by
      funext x
      change φ x * F n x - φ x * G x = φ x * (F n x - G x)
      ring
    rw [heq]
    exact h
  have hmul : Tendsto
      (fun n => eLpNorm φ ∞ μ * eLpNorm (F n - G) (3 / 2 : ℝ≥0∞) μ)
      atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.const_mul hconv (Or.inr hφ.eLpNorm_ne_top)
  have hconvScaled : Tendsto
      (fun n => eLpNorm (fun x => φ x * F n x - φ x * G x)
        (3 / 2 : ℝ≥0∞) μ) atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmul
      (Filter.Eventually.of_forall fun _ => bot_le)
      (Filter.Eventually.of_forall hscaled)
  have hFscaled (n : ℕ) : MemLp (fun x => φ x * F n x)
      (3 / 2 : ℝ≥0∞) μ := by
    have h : MemLp (φ • F n) (3 / 2 : ℝ≥0∞) μ := hφ.smul (hF n)
    have heq : (φ • F n) = (fun x => φ x * F n x) := by
      funext x
      rfl
    rwa [heq] at h
  exact stability_tendsto_integral_of_LthreeHalves μ
    (fun n x => φ x * F n x) (fun x => φ x * G x)
    hFscaled hconvScaled

end CKN
