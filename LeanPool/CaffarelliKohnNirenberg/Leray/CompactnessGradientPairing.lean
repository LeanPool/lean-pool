/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityWeakGradientProduct
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Compactness Gradient Pairing

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal

namespace CKN.Leray

/-- Strong `L²` convergence on a finite-measure space passes to Bochner
integrals. -/
theorem tendsto_integral_of_strong_l2
    {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure α) [IsFiniteMeasure μ]
    (F : ℕ → α → E) (G : α → E)
    (hF : ∀ n, MemLp (F n) 2 μ)
    (hconv : Tendsto (fun n => eLpNorm (F n - G) 2 μ) atTop (nhds 0)) :
    Tendsto (fun n => ∫ x, F n x ∂μ) atTop (nhds (∫ x, G x ∂μ)) := by
  let C : ℝ≥0∞ := μ univ ^ (1 / 2 : ℝ)
  have hC : C < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by norm_num) (by finiteness)
  have hbound (n : ℕ) : eLpNorm (F n - G) 1 μ ≤
      eLpNorm (F n - G) 2 μ * C := by
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ_of_pos
      (f := F n - G) (μ := μ) (p := (1 : ℝ≥0∞)) (q := (2 : ℝ≥0∞))
      (by norm_num) (by norm_num)
    convert h using 1
    norm_num [C]
  have hmul : Tendsto (fun n => eLpNorm (F n - G) 2 μ * C)
      atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.mul_const hconv (Or.inr hC.ne)
  have hconv1 : Tendsto (fun n => eLpNorm (F n - G) 1 μ)
      atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmul
      (Filter.Eventually.of_forall fun _ => bot_le)
      (Filter.Eventually.of_forall hbound)
  have hF1 (n : ℕ) : MemLp (F n) 1 μ :=
    (hF n).mono_exponent (by norm_num)
  exact tendsto_integral_of_L1' G
    (Filter.Eventually.of_forall fun n => memLp_one_iff_integrable.mp (hF1 n)) hconv1

/-- A bounded scalar multiplier preserves convergence of integrals under
strong `L²` convergence. -/
theorem tendsto_integral_mul_test_of_strong_l2
    {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure α) [IsFiniteMeasure μ]
    (F : ℕ → α → E) (G : α → E) (φ : α → ℝ)
    (hF : ∀ n, MemLp (F n) 2 μ)
    (hφ : MemLp φ ∞ μ)
    (hconv : Tendsto (fun n => eLpNorm (F n - G) 2 μ) atTop (nhds 0)) :
    Tendsto (fun n => ∫ x, φ x • F n x ∂μ) atTop
      (nhds (∫ x, φ x • G x ∂μ)) := by
  have hscaled (n : ℕ) :
      eLpNorm (fun x => φ x • F n x - φ x • G x) 2 μ ≤
        eLpNorm φ ∞ μ * eLpNorm (F n - G) 2 μ := by
    have h := eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm
      (φ := φ) (f := F n - G) 2 hφ.aestronglyMeasurable
    have heq : (fun x => φ x • F n x - φ x • G x) = φ • (F n - G) := by
      funext x
      exact (smul_sub (φ x) (F n x) (G x)).symm
    rw [heq]
    exact h
  have hmul : Tendsto (fun n => eLpNorm φ ∞ μ * eLpNorm (F n - G) 2 μ)
      atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.const_mul hconv (Or.inr hφ.eLpNorm_ne_top)
  have hconvScaled : Tendsto
      (fun n => eLpNorm (fun x => φ x • F n x - φ x • G x) 2 μ)
      atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmul
      (Filter.Eventually.of_forall fun _ => bot_le)
      (Filter.Eventually.of_forall hscaled)
  have hFscaled (n : ℕ) : MemLp (fun x => φ x • F n x) 2 μ :=
    hφ.smul (hF n)
  exact tendsto_integral_of_strong_l2 μ
    (fun n x => φ x • F n x) (fun x => φ x • G x)
    hFscaled hconvScaled

/-- A bounded test on a measurable subset preserves strong `L²` convergence
of scalar pairings. -/
theorem tendsto_setIntegral_mul_test_of_strong_l2
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (F : ℕ → α → ℝ) (G φ : α → ℝ) (S : Set α)
    (hF : ∀ n, MemLp (F n) 2 μ)
    (hφ : MemLp φ ∞ μ) (hS : MeasurableSet S)
    (hconv : Tendsto (fun n => eLpNorm (F n - G) 2 μ) atTop (nhds 0)) :
    Tendsto (fun n => ∫ x in S, φ x * F n x ∂μ) atTop
      (nhds (∫ x in S, φ x * G x ∂μ)) := by
  let w : α → ℝ := S.indicator φ
  have hw : MemLp w ∞ μ := hφ.indicator hS
  have h := tendsto_integral_mul_test_of_strong_l2 μ F G w hF hw hconv
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

end CKN.Leray
